#!/usr/bin/env python3
"""One-shot verification pipeline (runs inside the `verify` compose service):

  1. run the rule-logic unit tests;
  2. build the procedure page into the shared page volume;
  3. API/HTTP smoke checks against the live app service, covering:
       - conclusion retained (with its remaining complete basis) after one
         of two independent supports is retracted;
       - downstream invalidation with a visible propagation chain after the
         last support is retracted;
       - idempotent replay, rejection of unknown facts / dangling premises /
         self-supporting loops, and inert cyclic rules;
  4. shared-premise basis scenarios: a 15-layer procedure whose support DAG
     expands exponentially as a tree must still answer the full-basis query
     compactly (each node once, premises referenced by id), express cycles
     finitely, keep valid/invalid semantics, and never block concurrent
     procedure mutations while a large basis is being constructed;
  5. exit 0 when everything passed, 1 otherwise.
"""

from __future__ import annotations

import json
import os
import subprocess
import sys
import threading
import time
import urllib.error
import urllib.request
from datetime import datetime, timezone

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
APP_BASE_URL = os.environ.get("APP_BASE_URL", "http://localhost:8000")
PAGE_OUT = os.environ.get("PAGE_OUT", os.path.join(ROOT, "web", "dist"))
STAMP = "verify-" + datetime.now(timezone.utc).strftime("%Y%m%d%H%M%S")

RESULTS = []


def report(name: str, ok: bool, detail: str = "") -> None:
    RESULTS.append((name, ok, detail))
    mark = "PASS" if ok else "FAIL"
    line = f"[{mark}] {name}"
    if detail:
        line += f" — {detail}"
    print(line, flush=True)


def check(name: str, condition: bool, detail: str = "") -> bool:
    report(name, condition, detail)
    return condition


# --------------------------------------------------------------------- http

def http(method: str, path: str, body=None, expect=None):
    url = APP_BASE_URL + path
    data = None
    headers = {"Accept": "application/json"}
    if body is not None:
        data = json.dumps(body).encode("utf-8")
        headers["Content-Type"] = "application/json"
    request = urllib.request.Request(url, data=data, headers=headers,
                                     method=method)
    try:
        with urllib.request.urlopen(request, timeout=10) as resp:
            status = resp.status
            raw = resp.read()
            ctype = resp.headers.get("Content-Type", "")
    except urllib.error.HTTPError as exc:
        status = exc.code
        raw = exc.read()
        ctype = exc.headers.get("Content-Type", "") if exc.headers else ""
    parsed = None
    if "json" in ctype:
        parsed = json.loads(raw.decode("utf-8"))
    if expect is not None and status != expect:
        raise AssertionError(
            f"{method} {path}: expected HTTP {expect}, got {status}: "
            f"{raw[:200]!r}"
        )
    return status, parsed, raw


def wait_for_app(timeout: float = 60.0) -> bool:
    deadline = time.time() + timeout
    while time.time() < deadline:
        try:
            status, payload, _ = http("GET", "/api/healthz")
            if status == 200 and payload.get("status") == "ok":
                return True
        except Exception:
            pass
        time.sleep(1.0)
    return False


# -------------------------------------------------------------------- steps

def step_unit_tests() -> bool:
    proc = subprocess.run(
        [sys.executable, "-m", "unittest", "discover", "-s",
         os.path.join(ROOT, "app", "tests"), "-v"],
        cwd=ROOT, capture_output=True, text=True,
    )
    tail = (proc.stderr or proc.stdout).strip().splitlines()[-3:]
    return check("rule-logic unit tests", proc.returncode == 0,
                 " | ".join(tail))


def step_build_page() -> bool:
    proc = subprocess.run(
        [sys.executable, os.path.join(ROOT, "web", "build.py"),
         "--out", PAGE_OUT, "--stamp", STAMP],
        cwd=ROOT, capture_output=True, text=True,
    )
    ok = proc.returncode == 0 and os.path.isfile(
        os.path.join(PAGE_OUT, "index.html"))
    return check("page build", ok, (proc.stdout or proc.stderr).strip())


def step_smoke() -> bool:
    ok = True

    ok &= check("app healthy", wait_for_app(), APP_BASE_URL)

    # The page served by the app must be the one this run just built.
    try:
        _, _, raw = http("GET", "/", expect=200)
        ok &= check("served page carries this run's build stamp",
                    STAMP.encode() in raw, f"stamp={STAMP}")
    except AssertionError as exc:
        ok &= check("served page carries this run's build stamp", False,
                    str(exc))
        return ok

    try:
        http("POST", "/api/reset", {}, expect=200)
    except AssertionError as exc:
        return check("reset procedure for smoke run", False, str(exc))

    # -- build the safety procedure: two independent supports for C, D below
    http("POST", "/api/facts", {"id": "F1", "label": "sensor A"}, expect=201)
    http("POST", "/api/facts", {"id": "F2", "label": "sensor B"}, expect=201)
    http("POST", "/api/rules",
         {"id": "R1", "premises": ["F1"], "conclusion": "C"}, expect=201)
    http("POST", "/api/rules",
         {"id": "R2", "premises": ["F2"], "conclusion": "C"}, expect=201)
    http("POST", "/api/rules",
         {"id": "R3", "premises": ["C"], "conclusion": "D"}, expect=201)

    _, state, _ = http("GET", "/api/state", expect=200)
    conclusions = {c["id"]: c for c in state["conclusions"]}
    ok &= check("procedure established: C and D valid",
                conclusions["C"]["valid"] and conclusions["D"]["valid"])
    ok &= check("C has two complete supports",
                len([s for s in conclusions["C"]["supports"]
                     if s["status"] == "valid"]) == 2)

    # -- retract one of the two independent supports: C must survive
    _, verdict, _ = http("POST", "/api/facts/F1/retract", expect=200)
    _, state, _ = http("GET", "/api/state", expect=200)
    conclusions = {c["id"]: c for c in state["conclusions"]}
    ok &= check("after retracting F1: C still valid",
                conclusions["C"]["valid"])
    ok &= check("after retracting F1: D still valid",
                conclusions["D"]["valid"])
    ok &= check("verdict lists no invalidations",
                verdict["invalidated"] == [])
    retained = {r["node"]: r for r in verdict["retained"]}
    remaining = retained.get("C", {}).get("remaining_supports", [])
    ok &= check("verdict lists remaining complete basis for C",
                len(remaining) == 1 and remaining[0]["rule_id"] == "R2"
                and remaining[0]["premises"] == ["F2"],
                json.dumps(remaining, ensure_ascii=False))
    _, basis, _ = http("GET", "/api/conclusions/C/justification", expect=200)
    live = [s for s in basis["nodes"]["C"]["supports"]
            if s["status"] == "valid"]
    ok &= check("justification endpoint shows only R2 as live support",
                basis["root"] == "C" and len(live) == 1
                and live[0]["rule_id"] == "R2"
                and live[0]["premises"] == ["F2"]
                and basis["nodes"]["F2"]["kind"] == "fact"
                and basis["nodes"]["F2"]["valid"])

    # -- retract the last support: C and the dependent D must fall
    _, verdict2, _ = http("POST", "/api/facts/F2/retract", expect=200)
    _, state, _ = http("GET", "/api/state", expect=200)
    conclusions = {c["id"]: c for c in state["conclusions"]}
    ok &= check("after retracting F2: C invalid",
                not conclusions["C"]["valid"])
    ok &= check("after retracting F2: downstream D invalid",
                not conclusions["D"]["valid"])
    chain = [(s["node"], s["cause"]) for s in verdict2["propagation"]]
    ok &= check("propagation chain: C exhausted, then D",
                chain == [("C", "support-exhausted"),
                          ("D", "support-exhausted")],
                json.dumps(chain, ensure_ascii=False))
    ok &= check("retracted facts listed",
                sorted(state["retracted_facts"]) == ["F1", "F2"])

    # -- idempotent replay of the same retraction
    _, verdict3, _ = http("POST", "/api/facts/F2/retract", expect=200)
    same = all(verdict3[k] == verdict2[k] for k in
               ("fact_id", "verdict", "at", "invalidated", "retained",
                "propagation"))
    ok &= check("repeated retraction replays the same verdict",
                same and verdict3["replayed"] is True)

    # -- rejections must not pollute the procedure
    status, _, _ = http("POST", "/api/facts/GHOST/retract", expect=404)
    ok &= check("unknown fact retraction rejected (404)", status == 404)

    rules_before = len(state["rules"])
    status, _, _ = http("POST", "/api/rules",
                        {"id": "RBAD", "premises": ["GHOST"],
                         "conclusion": "E"}, expect=400)
    status2, _, _ = http("POST", "/api/rules",
                         {"id": "RSELF", "premises": ["C", "E2"],
                          "conclusion": "E2"}, expect=400)
    _, state, _ = http("GET", "/api/state", expect=200)
    ok &= check("dangling-premise and self-supporting rules rejected",
                status == 400 and status2 == 400)
    ok &= check("rejections did not pollute the procedure",
                len(state["rules"]) == rules_before
                and "E" not in {c["id"] for c in state["conclusions"]}
                and "E2" not in {c["id"] for c in state["conclusions"]})

    # -- cyclic rules exist but derive nothing out of thin air
    http("POST", "/api/rules", [
        {"id": "R4", "premises": ["X"], "conclusion": "Y"},
        {"id": "R5", "premises": ["Y"], "conclusion": "X"},
    ], expect=201)
    _, state, _ = http("GET", "/api/state", expect=200)
    conclusions = {c["id"]: c for c in state["conclusions"]}
    ok &= check("cyclic rules yield no valid conclusions",
                not conclusions["X"]["valid"]
                and not conclusions["Y"]["valid"])

    return ok


def step_shared_basis() -> bool:
    """Acceptance scenarios for the shared-support basis graph.

    Builds F plus 15 layers of conclusions with two single-premise rules
    per layer (both sharing the previous layer's conclusion): 16 business
    nodes, 30 rules — a support DAG whose naive tree expansion would be
    exponential.  The full basis of C14 must stay compact, keep every
    support relation recomputable, express cycles finitely, and its
    construction must not block concurrent procedure mutations.
    """
    ok = True

    try:
        http("POST", "/api/reset", {}, expect=200)
        http("POST", "/api/facts", {"id": "F", "label": "root"}, expect=201)
        rules = []
        for i in range(15):
            prev = "F" if i == 0 else f"C{i - 1}"
            rules.append({"id": f"R{i}a", "premises": [prev],
                          "conclusion": f"C{i}"})
            rules.append({"id": f"R{i}b", "premises": [prev],
                          "conclusion": f"C{i}"})
        http("POST", "/api/rules", rules, expect=201)
    except AssertionError as exc:
        return check("shared-premise procedure established", False, str(exc))

    # -- the complete basis stays compact and shares common premises
    _, basis, raw = http("GET", "/api/conclusions/C14/justification",
                         expect=200)
    ok &= check("shared-premise basis fits in 1 MiB",
                len(raw) <= 1024 * 1024, f"bytes={len(raw)}")
    nodes = basis.get("nodes", {})
    expected = {"F"} | {f"C{i}" for i in range(15)}
    ok &= check("basis carries each of the 16 nodes exactly once",
                basis.get("root") == "C14" and set(nodes) == expected,
                f"nodes={len(nodes)}")
    # Callers can recompute the support relation from the response: every
    # premise reference resolves to the single shared node entry, and the
    # 30 rule firings are all present.
    recomputable = all(
        premise in nodes
        for entry in nodes.values() if entry["kind"] == "conclusion"
        for support in entry["supports"] for premise in support["premises"]
    )
    firings = sum(len(entry["supports"]) for entry in nodes.values()
                  if entry["kind"] == "conclusion")
    refs_c13 = sum(
        1 for entry in nodes.values() if entry["kind"] == "conclusion"
        for support in entry["supports"] if support["premises"] == ["C13"]
    )
    ok &= check("support relation recomputable; C13 shared, not duplicated",
                recomputable and firings == 30 and refs_c13 == 2
                and nodes.get("C13", {}).get("valid") is True,
                f"firings={firings} refs_to_C13={refs_c13}")

    # -- validity semantics survive the graph encoding
    http("POST", "/api/facts/F/retract", expect=200)
    _, basis, _ = http("GET", "/api/conclusions/C14/justification",
                       expect=200)
    nodes = basis["nodes"]
    ok &= check("after retracting F: full basis kept, every node invalid",
                len(nodes) == 16
                and all(not n["valid"] for n in nodes.values())
                and all(s["status"] == "invalid" for n in nodes.values()
                        for s in n.get("supports", [])))
    http("POST", "/api/facts/F/assert", expect=200)
    _, basis, _ = http("GET", "/api/conclusions/C14/justification",
                       expect=200)
    ok &= check("after re-asserting F: every node valid again",
                all(n["valid"] for n in basis["nodes"].values()))

    # -- cyclic support: finite response, loop fully expressed
    http("POST", "/api/rules", [
        {"id": "RCX", "premises": ["CY"], "conclusion": "CX"},
        {"id": "RCY", "premises": ["CX"], "conclusion": "CY"},
    ], expect=201)
    _, basis, raw = http("GET", "/api/conclusions/CX/justification",
                         expect=200)
    nodes = basis.get("nodes", {})
    cx_premises = [p for s in nodes.get("CX", {}).get("supports", [])
                   for p in s["premises"]]
    cy_premises = [p for s in nodes.get("CY", {}).get("supports", [])
                   for p in s["premises"]]
    ok &= check("cyclic basis is finite, complete and keeps the loop",
                set(nodes) == {"CX", "CY"}
                and nodes["CX"]["cyclic"] and nodes["CY"]["cyclic"]
                and not nodes["CX"]["valid"] and not nodes["CY"]["valid"]
                and cx_premises == ["CY"] and cy_premises == ["CX"]
                and len(raw) <= 1024 * 1024,
                f"nodes={sorted(nodes)} bytes={len(raw)}")

    # -- concurrent basis queries must not block procedure mutations
    stop_hammer = threading.Event()

    def hammer():
        while not stop_hammer.is_set():
            try:
                http("GET", "/api/conclusions/C14/justification", expect=200)
            except Exception:  # noqa: BLE001 - keep hammering until told
                pass

    workers = [threading.Thread(target=hammer, daemon=True)
               for _ in range(4)]
    for worker in workers:
        worker.start()
    started = time.time()
    mutations_ok = True
    try:
        http("POST", "/api/facts", {"id": "FCONC"}, expect=201)
        http("POST", "/api/rules",
             {"id": "RCONC", "premises": ["FCONC"], "conclusion": "CCONC"},
             expect=201)
        http("POST", "/api/facts/FCONC/retract", expect=200)
        http("POST", "/api/facts/FCONC/assert", expect=200)
    except AssertionError:
        mutations_ok = False
    elapsed = time.time() - started
    stop_hammer.set()
    for worker in workers:
        worker.join()
    ok &= check("mutations not blocked by concurrent basis queries",
                mutations_ok and elapsed < 5.0, f"elapsed={elapsed:.2f}s")
    _, state, _ = http("GET", "/api/state", expect=200)
    conclusions = {c["id"]: c for c in state["conclusions"]}
    ok &= check("procedure consistent after the concurrent burst",
                conclusions.get("CCONC", {}).get("valid") is True
                and conclusions.get("C14", {}).get("valid") is True)

    return ok


def main() -> int:
    print(f"verify: target={APP_BASE_URL} page_out={PAGE_OUT} "
          f"stamp={STAMP}", flush=True)
    ok = step_unit_tests()
    ok = step_build_page() and ok
    try:
        ok = step_smoke() and ok
        ok = step_shared_basis() and ok
    except Exception as exc:  # noqa: BLE001 - report any smoke failure
        report("smoke run aborted", False, repr(exc))
        ok = False

    passed = sum(1 for _, good, _ in RESULTS if good)
    total = len(RESULTS)
    print(f"verify: {passed}/{total} checks passed", flush=True)
    if ok and passed == total:
        print("verify: OK", flush=True)
        return 0
    print("verify: FAILED", flush=True)
    return 1


if __name__ == "__main__":
    sys.exit(main())
