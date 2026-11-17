#!/usr/bin/env python3
"""Negative control for trace validation: copies of a recorded trace with one edit each.

    python3 tools/tamper_trace.py traces/run.ndjson outdir     writes outdir/<edit>.ndjson

Every copy describes a run that the program did not make and that the specification does not
allow, so spec/validate_trace.sh must REJECT each of them.  A copy that is ACCEPTED would mean
that some part of a recorded step is not compared with the specification.
The names of the files written are printed, one per line.  Python 3.9+, standard library only.
"""
import copy
import json
import sys
from pathlib import Path

if len(sys.argv) != 3:
    sys.exit(__doc__)
src, out = Path(sys.argv[1]), Path(sys.argv[2])
out.mkdir(parents=True, exist_ok=True)
L = [json.loads(line) for line in src.read_text().splitlines() if line.strip()]   # L[0] is the first line, L[k] is step k
N = L[0]["N"]


def write(name: str, recs: list) -> None:
    (out / f"{name}.ndjson").write_text("".join(json.dumps(r, separators=(",", ":")) + "\n" for r in recs))
    print(f"{name}.ndjson")


def first(action: str):
    """The first step of that action, or None."""
    return next((k for k in range(1, len(L)) if L[k]["action"] == action), None)


def edit(name: str, k, change) -> None:
    """Write a copy in which `change` was applied to step k (skipped when the trace has no such step)."""
    if k is None or not 0 <= k < len(L):
        return
    r = copy.deepcopy(L)
    change(r, k)
    write(name, r)


def stale(var: str):
    """The step leaves `var` as it was before the step."""
    def change(r, k):
        r[k]["state"][var] = copy.deepcopy(L[k - 1]["state"][var])
    return change


def other_process(r, k):
    p, q = r[k]["p"], r[k]["q"]
    r[k]["q"] = next(x for x in range(1, N + 1) if x not in (p, q))


def clock_plus_one(r, k):
    r[k]["state"]["clock"][r[k]["p"] - 1] += 1


def ack_timestamp(r, k):
    p, q = r[k]["p"], r[k]["q"]
    r[k]["state"]["chan"][p - 1][q - 1][-1]["ts"] -= 1


def still_waiting(r, k):
    r[k]["state"]["pc"][r[k]["p"] - 1] = "waiting"


def rename(to: str):
    def change(r, k):
        r[k]["action"] = to
    return change


mid = len(L) // 2
edit("clock-off-by-one", mid, clock_plus_one)                       # a clock one tick ahead
edit("pc-not-held", first("Acquire"), still_waiting)                # granted, but pc still "waiting"
edit("lastTs-stale", first("RecvAck"), stale("lastTs"))             # the ack does not update lastTs
edit("queue-stale", first("RecvRelease"), stale("queue"))           # the released request stays queued
edit("reqs-stale", first("Request"), stale("reqs"))                 # the request is not counted
edit("ack-timestamp", first("RecvRequest"), ack_timestamp)          # the ack carries an older timestamp
edit("wrong-action", first("RecvAck"), rename("RecvRelease"))       # an ack recorded as a release
if N >= 3:
    edit("wrong-sender", first("RecvRequest"), other_process)       # the request came from someone else
last_acquire = max((k for k in range(1, len(L)) if L[k]["action"] == "Acquire"), default=None)
edit("lastGranted-stale", last_acquire, stale("lastGranted"))       # the grant is not remembered
if len(L) > 4:
    r = copy.deepcopy(L)
    del r[mid]                                                      # a step is missing
    write("dropped-step", r)
    r = copy.deepcopy(L)
    r[mid - 1], r[mid] = r[mid], r[mid - 1]                         # two steps in the other order
    write("swapped-steps", r)
if N >= 2:
    r = copy.deepcopy(L)
    r[0]["state"]["pc"][0], r[0]["state"]["pc"][1] = r[0]["state"]["pc"][1], r[0]["state"]["pc"][0]
    write("init-other-holder", r)                                   # P2 holds the resource initially
if L[0]["MaxReq"] >= 2 and any(s["state"]["reqs"][p] == 2 for s in L[1:] for p in range(N)):
    r = copy.deepcopy(L)
    r[0]["MaxReq"] = 1                                              # a second request is one too many
    write("maxreq-lowered", r)
