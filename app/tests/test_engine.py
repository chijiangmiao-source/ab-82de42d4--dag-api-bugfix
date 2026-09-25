"""Rule-logic (JTMS) test suite — runs with the plain stdlib unittest."""

import json
import os
import tempfile
import threading
import time
import unittest

from app.tms import Conflict, Engine, NotFound, ValidationFailed


class EngineCase(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.db = os.path.join(self.tmp.name, "tms.db")
        self.engine = Engine(self.db)

    def tearDown(self):
        self.engine.close()
        self.tmp.cleanup()

    # ------------------------------------------------------------- helpers

    def conclusion(self, node):
        for item in self.engine.state()["conclusions"]:
            if item["id"] == node:
                return item
        raise AssertionError(f"no conclusion {node!r}")

    def assert_valid(self, node):
        self.assertTrue(self.conclusion(node)["valid"], f"{node} invalid")

    def assert_invalid(self, node):
        self.assertFalse(self.conclusion(node)["valid"], f"{node} valid")

    def build_two_path_procedure(self):
        """Safety procedure: C supported by two independent paths, D below C."""
        self.engine.add_fact("F1", "sensor A reading")
        self.engine.add_fact("F2", "sensor B reading")
        self.engine.add_rules({"id": "R1", "premises": ["F1"],
                               "conclusion": "C"})
        self.engine.add_rules({"id": "R2", "premises": ["F2"],
                               "conclusion": "C"})
        self.engine.add_rules({"id": "R3", "premises": ["C"],
                               "conclusion": "D"})

    def build_shared_premise_procedure(self, layers=15):
        """F, then `layers` conclusions with two single-premise rules each,
        both rules of a layer sharing the previous layer's conclusion as
        their only premise: 16 business nodes, 2*layers rules, and a
        support DAG whose tree expansion would be exponential."""
        self.engine.add_fact("F", "root fact")
        rules = []
        for i in range(layers):
            prev = "F" if i == 0 else f"C{i - 1}"
            rules.append({"id": f"R{i}a", "premises": [prev],
                          "conclusion": f"C{i}"})
            rules.append({"id": f"R{i}b", "premises": [prev],
                          "conclusion": f"C{i}"})
        self.engine.add_rules(rules)

    # ------------------------------------------------------- core scenarios

    def test_two_independent_supports_keep_conclusion_alive(self):
        self.build_two_path_procedure()
        self.assert_valid("C")
        self.assert_valid("D")

        verdict = self.engine.retract_fact("F1")
        # Conclusion stays valid on the remaining independent support.
        self.assert_valid("C")
        self.assert_valid("D")
        self.assertEqual(verdict["invalidated"], [])
        retained = {r["node"]: r for r in verdict["retained"]}
        self.assertIn("C", retained)
        remaining = retained["C"]["remaining_supports"]
        self.assertEqual(len(remaining), 1)
        self.assertEqual(remaining[0]["rule_id"], "R2")
        self.assertEqual(remaining[0]["premises"], ["F2"])

    def test_last_support_retraction_cascades_downstream(self):
        self.build_two_path_procedure()
        self.engine.retract_fact("F1")
        verdict = self.engine.retract_fact("F2")

        self.assert_invalid("C")
        self.assert_invalid("D")
        invalidated = [item["node"] for item in verdict["invalidated"]]
        self.assertEqual(invalidated, ["C", "D"])
        # Propagation chain: C exhausts its support first, then D.
        chain = [(step["depth"], step["node"], step["cause"])
                 for step in verdict["propagation"]]
        self.assertEqual(chain, [
            (0, "C", "support-exhausted"),
            (1, "D", "support-exhausted"),
        ])

    def test_complete_premise_set_saved_per_firing(self):
        self.engine.add_fact("F1")
        self.engine.add_fact("F2")
        self.engine.add_rules({"id": "R1", "premises": ["F1", "F2"],
                               "conclusion": "C"})
        supports = self.conclusion("C")["supports"]
        self.assertEqual(len(supports), 1)
        self.assertEqual(supports[0]["rule_id"], "R1")
        self.assertEqual(supports[0]["premises"], ["F1", "F2"])
        self.assertEqual(supports[0]["status"], "valid")

    def test_repeated_retraction_replays_same_verdict(self):
        self.build_two_path_procedure()
        first = self.engine.retract_fact("F1")
        second = self.engine.retract_fact("F1")
        self.assertFalse(first["replayed"])
        self.assertTrue(second["replayed"])
        for key in ("fact_id", "verdict", "at", "invalidated", "retained",
                    "propagation"):
            self.assertEqual(first[key], second[key], key)

    def test_unknown_fact_retraction_rejected(self):
        with self.assertRaises(NotFound):
            self.engine.retract_fact("NOPE")

    def test_rule_with_unknown_premise_rejected_without_pollution(self):
        self.engine.add_fact("F1")
        with self.assertRaises(ValidationFailed):
            self.engine.add_rules({"id": "R1", "premises": ["GHOST"],
                                   "conclusion": "C"})
        state = self.engine.state()
        self.assertEqual(state["rules"], [])
        self.assertEqual(state["conclusions"], [])

    def test_self_supporting_loop_rejected(self):
        self.engine.add_fact("F1")
        with self.assertRaises(ValidationFailed):
            self.engine.add_rules({"id": "R1", "premises": ["F1", "C"],
                                   "conclusion": "C"})
        self.assertEqual(self.engine.state()["rules"], [])

    def test_batch_is_atomic(self):
        self.engine.add_fact("F1")
        with self.assertRaises(ValidationFailed):
            self.engine.add_rules([
                {"id": "R1", "premises": ["F1"], "conclusion": "C"},
                {"id": "R2", "premises": ["GHOST"], "conclusion": "E"},
            ])
        state = self.engine.state()
        self.assertEqual(state["rules"], [])
        self.assertEqual(state["conclusions"], [])

    def test_cycle_alone_derives_nothing(self):
        self.engine.add_fact("F1")
        self.engine.add_rules([
            {"id": "R1", "premises": ["X"], "conclusion": "Y"},
            {"id": "R2", "premises": ["Y"], "conclusion": "X"},
        ])
        self.assert_invalid("X")
        self.assert_invalid("Y")

    def test_grounded_cycle_collapses_when_ground_retracted(self):
        self.engine.add_fact("F1")
        self.engine.add_rules({"id": "R0", "premises": ["F1"],
                               "conclusion": "X"})
        self.engine.add_rules([
            {"id": "R1", "premises": ["X"], "conclusion": "Y"},
            {"id": "R2", "premises": ["Y"], "conclusion": "X"},
        ])
        self.assert_valid("X")
        self.assert_valid("Y")

        self.engine.retract_fact("F1")
        # The X<->Y loop must not keep itself alive without ground support.
        self.assert_invalid("X")
        self.assert_invalid("Y")

    def test_reassert_restores_conclusions(self):
        self.build_two_path_procedure()
        self.engine.retract_fact("F1")
        self.engine.retract_fact("F2")
        self.assert_invalid("C")
        verdict = self.engine.assert_fact("F2")
        self.assert_valid("C")
        self.assert_valid("D")
        self.assertEqual(verdict["restored"], ["C", "D"])

    def test_justification_graph_is_complete(self):
        self.build_two_path_procedure()
        self.engine.retract_fact("F1")
        basis = self.engine.justification("D")
        self.assertEqual(basis["root"], "D")
        nodes = basis["nodes"]
        # Every node of the basis appears exactly once, keyed by id.
        self.assertEqual(set(nodes), {"D", "C", "F1", "F2"})
        node_d = nodes["D"]
        self.assertTrue(node_d["valid"])
        self.assertFalse(node_d["cyclic"])
        self.assertEqual([s["rule_id"] for s in node_d["supports"]], ["R3"])
        self.assertEqual(node_d["supports"][0]["premises"], ["C"])
        valid_supports = [s for s in nodes["C"]["supports"]
                          if s["status"] == "valid"]
        self.assertEqual(len(valid_supports), 1)
        self.assertEqual(valid_supports[0]["rule_id"], "R2")
        self.assertEqual(valid_supports[0]["premises"], ["F2"])
        self.assertEqual(nodes["F2"], {"node": "F2", "kind": "fact",
                                       "label": "sensor B reading",
                                       "status": "asserted", "valid": True})
        self.assertEqual(nodes["F1"]["status"], "retracted")
        self.assertFalse(nodes["F1"]["valid"])

    def test_justification_shares_common_premises(self):
        self.build_shared_premise_procedure()
        basis = self.engine.justification("C14")
        self.assertEqual(basis["root"], "C14")
        nodes = basis["nodes"]
        # 16 business nodes, each transmitted exactly once — the shared
        # premise is referenced, not copied per referring rule.
        expected = {"F"} | {f"C{i}" for i in range(15)}
        self.assertEqual(set(nodes), expected)
        self.assertEqual(
            sum(len(n["supports"]) for n in nodes.values()
                if n["kind"] == "conclusion"),
            30,
        )
        # The full support relation is recomputable from the response:
        # every premise reference resolves to the one shared node entry.
        for entry in nodes.values():
            for support in entry.get("supports", []):
                for premise in support["premises"]:
                    self.assertIn(premise, nodes)
        referrers = [s["rule_id"] for s in nodes["C14"]["supports"]
                     if s["premises"] == ["C13"]]
        self.assertEqual(sorted(referrers), ["R14a", "R14b"])
        self.assertTrue(all(nodes[f"C{i}"]["valid"] for i in range(15)))
        self.assertFalse(any(n.get("cyclic") for n in nodes.values()))
        payload = json.dumps(basis, ensure_ascii=False).encode("utf-8")
        self.assertLess(len(payload), 1024 * 1024)

    def test_justification_validity_semantics_preserved(self):
        self.build_shared_premise_procedure()
        self.engine.retract_fact("F")
        nodes = self.engine.justification("C14")["nodes"]
        # The complete relation survives retraction; only the flags flip.
        self.assertEqual(len(nodes), 16)
        self.assertTrue(all(not n["valid"] for n in nodes.values()))
        self.assertTrue(all(s["status"] == "invalid"
                            for n in nodes.values()
                            for s in n.get("supports", [])))
        self.engine.assert_fact("F")
        nodes = self.engine.justification("C14")["nodes"]
        self.assertTrue(all(n["valid"] for n in nodes.values()))
        self.assertTrue(all(s["status"] == "valid"
                            for n in nodes.values()
                            for s in n.get("supports", [])))

    def test_justification_cycle_is_finite_and_complete(self):
        self.engine.add_fact("F1")
        self.engine.add_rules({"id": "R0", "premises": ["F1"],
                               "conclusion": "X"})
        self.engine.add_rules([
            {"id": "R1", "premises": ["X"], "conclusion": "Y"},
            {"id": "R2", "premises": ["Y"], "conclusion": "X"},
        ])
        nodes = self.engine.justification("X")["nodes"]
        # The loop is represented once per node, never infinitely expanded.
        self.assertEqual(set(nodes), {"X", "Y", "F1"})
        self.assertTrue(nodes["X"]["cyclic"])
        self.assertTrue(nodes["Y"]["cyclic"])
        self.assertNotIn("cyclic", nodes["F1"])
        # ... and the cyclic relation itself is fully preserved.
        x_supports = {s["rule_id"]: s["premises"]
                      for s in nodes["X"]["supports"]}
        self.assertEqual(x_supports["R2"], ["Y"])
        self.assertEqual(x_supports["R0"], ["F1"])
        self.assertEqual([s["premises"] for s in nodes["Y"]["supports"]],
                         [["X"]])
        self.assertTrue(nodes["X"]["valid"])
        self.assertTrue(nodes["Y"]["valid"])

    def test_justification_ungrounded_cycle_stays_invalid(self):
        self.engine.add_fact("F1")
        self.engine.add_rules([
            {"id": "R1", "premises": ["X"], "conclusion": "Y"},
            {"id": "R2", "premises": ["Y"], "conclusion": "X"},
        ])
        nodes = self.engine.justification("X")["nodes"]
        self.assertEqual(set(nodes), {"X", "Y"})
        self.assertTrue(nodes["X"]["cyclic"] and nodes["Y"]["cyclic"])
        self.assertFalse(nodes["X"]["valid"] or nodes["Y"]["valid"])

    def test_justification_queries_do_not_block_mutations(self):
        self.build_shared_premise_procedure()
        stop = threading.Event()
        errors = []

        def hammer():
            while not stop.is_set():
                try:
                    self.engine.justification("C14")
                except Exception as exc:  # pragma: no cover - failure path
                    errors.append(exc)

        workers = [threading.Thread(target=hammer) for _ in range(4)]
        for worker in workers:
            worker.start()
        try:
            started = time.monotonic()
            self.engine.add_fact("FZ")
            self.engine.add_rules({"id": "RZ", "premises": ["FZ"],
                                   "conclusion": "CZ"})
            self.engine.retract_fact("FZ")
            self.engine.assert_fact("FZ")
            elapsed = time.monotonic() - started
        finally:
            stop.set()
            for worker in workers:
                worker.join()
        self.assertFalse(errors)
        # Construction happens outside the store lock; a burst of basis
        # queries must not serialise procedure mutations behind it.
        self.assertLess(elapsed, 3.0)
        self.assert_valid("CZ")
        self.assert_valid("C14")

    def test_justification_of_unknown_node_rejected(self):
        with self.assertRaises(NotFound):
            self.engine.justification("NOPE")

    def test_duplicate_ids_rejected(self):
        self.engine.add_fact("F1")
        with self.assertRaises(Conflict):
            self.engine.add_fact("F1")
        self.engine.add_rules({"id": "R1", "premises": ["F1"],
                               "conclusion": "C"})
        with self.assertRaises(Conflict):
            self.engine.add_rules({"id": "R1", "premises": ["F1"],
                                   "conclusion": "C2"})
        with self.assertRaises(Conflict):
            self.engine.add_fact("C")  # collides with a conclusion

    def test_persistence_across_restart(self):
        self.build_two_path_procedure()
        verdict = self.engine.retract_fact("F1")
        self.engine.close()

        reopened = Engine(self.db)
        try:
            state = reopened.state()
            facts = {f["id"]: f for f in state["facts"]}
            self.assertEqual(facts["F1"]["status"], "retracted")
            self.assertEqual(facts["F2"]["status"], "asserted")
            conclusions = {c["id"]: c for c in state["conclusions"]}
            self.assertTrue(conclusions["C"]["valid"])
            self.assertTrue(conclusions["D"]["valid"])
            # Justification state survives the restart as well.
            basis = reopened.justification("C")
            valid_supports = [s for s in basis["nodes"]["C"]["supports"]
                              if s["status"] == "valid"]
            self.assertEqual([s["rule_id"] for s in valid_supports], ["R2"])
            # And the recorded verdict is replayed identically.
            replay = reopened.retract_fact("F1")
            self.assertTrue(replay["replayed"])
            self.assertEqual(replay["at"], verdict["at"])
        finally:
            reopened.close()

    def test_health_reflects_store(self):
        self.assertEqual(self.engine.health()["status"], "ok")


if __name__ == "__main__":
    unittest.main()
