------------------------- MODULE LamportMutexTrace -------------------------
(***************************************************************************)
(* Trace validation: is a recorded execution of ../cpp/lamport_mutex.cpp   *)
(* a behaviour of LamportMutex?                                            *)
(*                                                                         *)
(* The program, run with LM_TRACE=<file>, writes one JSON object per line. *)
(* The first line holds the constants of the run and the initial state:    *)
(*     {"N": 3, "MaxReq": 2, "state": {...}}                               *)
(* Every later line is one step, written while the step's lock is held:    *)
(*     {"action": "RecvRequest", "p": 3, "q": 2, "state": {...}}           *)
(* where "state" holds the seven variables after the step.                 *)
(*                                                                         *)
(* This module extends the specification with one variable, l, the number  *)
(* of steps matched so far.  Its next-state relation allows exactly one    *)
(* thing: the action named by line l + 1, with the recorded parameters,    *)
(* leading to the recorded state.  The actions are those of LamportMutex,  *)
(* unchanged, so a step is allowed here only if the specification allows   *)
(* it.  TLC is run with deadlock checking:                                 *)
(*   - if every line is matched, the last state loops on itself (Done)     *)
(*     and TLC finds no error: the run is a behaviour of the spec;         *)
(*   - if line l + 1 cannot be matched, the state has no successor and     *)
(*     TLC reports a deadlock: the behaviour it prints is the part of the  *)
(*     run that the spec accepts, and line l + 1 is where they part.       *)
(*                                                                         *)
(* The method is the one of Cirstea, Kuppe, Loillier and Merz, "Validating *)
(* Traces of Distributed Programs Against TLA+ Specifications".            *)
(*                                                                         *)
(* Run it with ./validate_trace.sh <file>; the file name reaches this      *)
(* module through the environment variable LM_TRACE.                       *)
(***************************************************************************)
EXTENDS LamportMutex, Json, IOUtils

ASSUME TraceFileGiven == "LM_TRACE" \in DOMAIN IOEnv

TraceLog == TLCEval(ndJsonDeserialize(IOEnv.LM_TRACE))   \* the file, a sequence of records
Header   == TraceLog[1]                                  \* constants and initial state
Events   == SubSeq(TraceLog, 2, Len(TraceLog))           \* the steps

(* The constants of the specification are those of the run (see the .cfg). *)
TraceN      == Header.N
TraceMaxReq == Header.MaxReq

VARIABLE l      \* the number of recorded steps matched so far

Range(s) == {s[i] : i \in DOMAIN s}

(* JSON has arrays and objects only.  An array of length N is a function on
   1..N, which is how clock, lastTs, pc, reqs and the two levels of chan are
   written; an array is also a sequence (a channel) and a tuple (a request);
   an object is a record (a message).  Only the request queues need a
   conversion: they are sets in the spec and arrays in the file. *)
QueueOf(s) == [p \in Proc |-> Range(s.queue[p])]

(* The specification is in the recorded state s. *)
InState(s) ==
    /\ clock = s.clock
    /\ queue = QueueOf(s)
    /\ chan = s.chan
    /\ lastTs = s.lastTs
    /\ pc = s.pc
    /\ reqs = s.reqs
    /\ lastGranted = s.lastGranted

(* The variables whose value after the step is not the recorded one. *)
Mismatch(s) ==
    (IF clock' = s.clock THEN {} ELSE {"clock"})
    \cup (IF queue' = QueueOf(s) THEN {} ELSE {"queue"})
    \cup (IF chan' = s.chan THEN {} ELSE {"chan"})
    \cup (IF lastTs' = s.lastTs THEN {} ELSE {"lastTs"})
    \cup (IF pc' = s.pc THEN {} ELSE {"pc"})
    \cup (IF reqs' = s.reqs THEN {} ELSE {"reqs"})
    \cup (IF lastGranted' = s.lastGranted THEN {} ELSE {"lastGranted"})

(* The first line is the initial state of the specification. *)
TraceInit ==
    /\ l = 0
    /\ Init
    /\ InState(Header.state)

(* The action of the specification that the recorded step e names. *)
Step(e) ==
    \/ e.action = "Request"     /\ Request(e.p)
    \/ e.action = "RecvRequest" /\ RecvRequest(e.p, e.q)
    \/ e.action = "RecvAck"     /\ RecvAck(e.p, e.q)
    \/ e.action = "Release"     /\ Release(e.p)
    \/ e.action = "RecvRelease" /\ RecvRelease(e.p, e.q)
    \/ e.action = "Acquire"     /\ Acquire(e.p)

(* Match line l + 1: the specification takes the named action, and the state
   it reaches is the recorded one.  When the action is enabled but leads to
   another state, the differing variables are printed and the step fails. *)
Replay ==
    /\ l < Len(Events)
    /\ LET e == Events[l + 1] IN
        /\ Step(e)
        /\ \/ Mismatch(e.state) = {}
           \/ /\ Mismatch(e.state) # {}
              /\ PrintT(<<"MISMATCH", l + 1, e.action, Mismatch(e.state)>>)
              /\ FALSE
    /\ l' = l + 1

(* Every line is matched: the behaviour ends here, by stuttering. *)
Done == l = Len(Events) /\ UNCHANGED <<l, vars>>

TraceNext == Replay \/ Done

TraceSpec == TraceInit /\ [][TraceNext]_<<l, vars>>

(* Checked by TLC when it stops: one state for the first line and one for
   every step.  It fails if the first line is not an initial state. *)
TraceAccepted == TLCGet("stats").distinct = Len(Events) + 1
=============================================================================
