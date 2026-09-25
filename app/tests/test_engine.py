"""Rule-logic (JTMS) test suite — runs with the plain stdlib unittest."""

import json
import os
import tempfile
import threading
import unittest

from app.tms import Conflict, Engine, NotFound, ValidationFailed


ONE_MIB = 1024 * 1024


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

    def build_shared_chain(self, layers=15):
        """F, then `layers` conclusions; each layer has two rules whose only
        premise is the previous layer's conclusion (shared premise)."""
        self.engine.add_fact("F")
        prev = "F"
        for i in range(layers):
            conclusion = f"C{i}"
            self.engine.add_rules([
                {"id": f"R{i}a", "premises": [prev], "conclusion": conclusion},
                {"id": f"R{i}b", "premises": [prev], "conclusion": conclusion},
            ])
            prev = conclusion
        return prev

    def assert_snapshot_consistent(self, graph):
        """Every valid support's premises are valid nodes in the same graph."""
        nodes, supports = graph["nodes"], graph["supports"]
        for support in supports.values():
            for premise in support["premises"]:
                self.assertIn(premise, nodes)
            if support["status"] == "valid":
                for premise in support["premises"]:
                    self.assertTrue(
                        nodes[premise]["valid"],
                        f"{support['rule_id']} valid but premise {premise} not",
                    )

    def test_justification_graph_is_complete_and_recomputable(self):
        self.build_two_path_procedure()
        self.engine.retract_fact("F1")
        graph = self.engine.justification("D")
        self.assertEqual(graph["format"], "shared-graph/v1")
        self.assertEqual(graph["root"], "D")
        nodes, supports = graph["nodes"], graph["supports"]

        self.assertTrue(nodes["D"]["valid"])
        self.assertEqual(nodes["D"]["support_ids"], ["R3"])
        self.assertEqual(supports["R3"]["premises"], ["C"])
        self.assertEqual(supports["R3"]["status"], "valid")

        self.assertTrue(nodes["C"]["valid"])
        self.assertEqual(nodes["C"]["support_ids"], ["R1", "R2"])
        # F1 retracted: R1 broken, R2 remains the single live support.
        self.assertEqual(supports["R1"]["status"], "invalid")
        self.assertEqual(supports["R2"]["status"], "valid")
        self.assertEqual(supports["R2"]["premises"], ["F2"])
        self.assertEqual(nodes["F1"]["status"], "retracted")
        self.assertEqual(nodes["F2"], {
            "id": "F2", "kind": "fact", "label": "sensor B reading",
            "status": "asserted", "valid": True})

        self.assertFalse(any(n.get("cyclic") for n in nodes.values()))
        self.assertEqual(graph["cycles"], [])
        self.assert_snapshot_consistent(graph)

    def test_shared_premises_serialised_once_and_response_under_one_mib(self):
        last = self.build_shared_chain()
        graph = self.engine.justification(last)
        encoded = json.dumps(graph, ensure_ascii=False).encode("utf-8")
        self.assertLess(len(encoded), ONE_MIB)

        # 16 business nodes (1 fact + 15 conclusions), 30 supports.
        self.assertEqual(set(graph["nodes"]),
                         {"F"} | {f"C{i}" for i in range(15)})
        self.assertEqual(len(graph["nodes"]), 16)
        self.assertEqual(set(graph["supports"]),
                         {f"R{i}{v}" for i in range(15) for v in "ab"})
        self.assertEqual(len(graph["supports"]), 30)

        # The shared premise C0 is one node referenced by both layer-1 rules.
        self.assertEqual(graph["supports"]["R1a"]["premises"], ["C0"])
        self.assertEqual(graph["supports"]["R1b"]["premises"], ["C0"])

        # A caller rebuilds the whole support structure from id references;
        # the same premise never appears as two distinct nodes.
        deps = {}
        for support in graph["supports"].values():
            deps.setdefault(support["conclusion"], set()).update(
                support["premises"])
        self.assertEqual(deps["C1"], {"C0"})
        self.assertEqual(deps[last], {"C13"})
        self.assert_snapshot_consistent(graph)

    def test_justification_represents_cycle_fully_without_expansion(self):
        self.engine.add_fact("F1")
        self.engine.add_rules({"id": "R0", "premises": ["F1"],
                               "conclusion": "X"})
        self.engine.add_rules([
            {"id": "R1", "premises": ["X"], "conclusion": "Y"},
            {"id": "R2", "premises": ["Y"], "conclusion": "X"},
        ])
        graph = self.engine.justification("X")
        self.assertTrue(graph["nodes"]["X"]["valid"])
        self.assertTrue(graph["nodes"]["X"]["cyclic"])
        self.assertTrue(graph["nodes"]["Y"]["cyclic"])
        cycle_edges = {(c["node"], c["rule_id"], c["premise"])
                       for c in graph["cycles"]}
        self.assertEqual(cycle_edges,
                         {("X", "R2", "Y"), ("Y", "R1", "X")})
        # Complete: all three supports (incl. the ground path) present once.
        self.assertEqual(set(graph["supports"]), {"R0", "R1", "R2"})
        self.assertLess(len(json.dumps(graph).encode()), ONE_MIB)

        # Ground retraction collapses the loop but keeps the cycle relations.
        self.engine.retract_fact("F1")
        graph2 = self.engine.justification("X")
        self.assertFalse(graph2["nodes"]["X"]["valid"])
        self.assertFalse(graph2["nodes"]["Y"]["valid"])
        self.assertEqual(graph2["supports"]["R0"]["status"], "invalid")
        self.assertEqual({(c["node"], c["rule_id"]) for c in graph2["cycles"]},
                         {("X", "R2"), ("Y", "R1")})
        self.assert_snapshot_consistent(graph2)

    def test_justification_queries_do_not_block_concurrent_mutations(self):
        # A long chain keeps graph construction busy without holding the
        # store lock; mutations must commit while queries are in flight.
        self.build_shared_chain(layers=120)
        stop = threading.Event()
        errors = []

        def query_loop():
            try:
                while not stop.is_set():
                    self.engine.justification("C119")
            except Exception as exc:  # pragma: no cover - diagnostic
                errors.append(exc)

        workers = [threading.Thread(target=query_loop) for _ in range(3)]
        for worker in workers:
            worker.start()
        try:
            # Each mutation must commit promptly even while large justification
            # graphs are being assembled.
            for number in range(5):
                ready = threading.Event()

                def add_one(n=number):
                    ready.set()
                    self.engine.add_fact(f"G{n}")

                op = threading.Thread(target=add_one)
                op.start()
                self.assertTrue(ready.wait(2))
                op.join(timeout=5)
                self.assertFalse(op.is_alive(), "mutation blocked by query")

            verdict = self.engine.retract_fact("F")
            self.assertIn("C0",
                          [item["node"] for item in verdict["invalidated"]])
            restored = self.engine.assert_fact("F")
            self.assertIn("C0", restored["restored"])
        finally:
            stop.set()
            for worker in workers:
                worker.join(timeout=5)
                self.assertFalse(worker.is_alive())
        self.assertEqual(errors, [])
        self.assert_snapshot_consistent(self.engine.justification("C119"))

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
            graph = reopened.justification("C")
            live = [rule_id for rule_id, support in graph["supports"].items()
                    if support["status"] == "valid"]
            self.assertEqual(live, ["R2"])
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
