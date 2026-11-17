--------------------------- MODULE LamportMutex ---------------------------
(***************************************************************************)
(* Lamport's distributed mutual-exclusion algorithm, from "Time, Clocks,   *)
(* and the Ordering of Events in a Distributed System" (CACM 21(7), 1978, *)
(* pp. 558-565), section "Ordering the Events Totally".                    *)
(*                                                                         *)
(* The paper gives the algorithm as five rules over a system of logical    *)
(* clocks (IR1, IR2) and a total order => on events, and proves that it   *)
(* satisfies three conditions:                                             *)
(*   I.   a process holding the resource releases it before it is granted  *)
(*        to another process;                                              *)
(*   II.  requests are granted in the order (=>) in which they are made;   *)
(*   III. if every holder eventually releases, every request is eventually *)
(*        granted.                                                         *)
(*                                                                         *)
(* Assumptions the paper makes (and this module encodes):                  *)
(*   A1. messages from Pi to Pj are received in the order they are sent    *)
(*       (chan[i][j] is a FIFO sequence; receives take the head);          *)
(*   A2. every message is eventually received (weak fairness on the three  *)
(*       receive actions in FairSpec); no loss, no duplication;            *)
(*   A3. a process can send messages directly to every other process;      *)
(*   A4. the request queues initially contain T0:P0 "requests resource",   *)
(*       P0 holds the resource, and T0 is less than every initial clock    *)
(*       (T0 = 0, clocks start at 1, P0 = 1);                              *)
(*   A5. the actions of each rule form a single event (one spec action     *)
(*       each; the implementation makes them atomic under one lock);       *)
(*   A6. the total order => on events: by timestamp, ties broken by an     *)
(*       arbitrary total order on processes (here: the process number);    *)
(*   A7. no process fails (the paper leaves failure out of scope).         *)
(*                                                                         *)
(* The state machine has one action per rule (Request = rule 1,            *)
(* RecvRequest = rule 2, Release = rule 3, RecvRelease = rule 4,           *)
(* Acquire = rule 5) plus RecvAck, which consumes the acknowledgement that *)
(* rule 2 sends and that rule 5(ii) relies on.  IR1 and IR2 are applied   *)
(* in every action.  Footnote 5 (an ack may be omitted when a later        *)
(* message was already sent) and footnote 6 (>= instead of > for lower    *)
(* processes) are optimisations the module does not take.                  *)
(*                                                                         *)
(* Bound to ../cpp/lamport_mutex.cpp by the TLA+ annotations written       *)
(* there as comments (@TLA_VAR, @TLA_ACTION_LOCKED, @TLA_GUARD, ...).      *)
(***************************************************************************)
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    N,        \* number of processes          @TLA_IMPL{kind:"const", symbol:"n_"}
    MaxReq    \* requests per process (bound)  @TLA_IMPL{kind:"const", symbol:"max_req_"}

ASSUME NAssumption == N \in Nat /\ N >= 1 /\ MaxReq \in Nat

Proc == 1..N          \* the arbitrary total order on processes is the order on 1..N
P0   == 1             \* the process initially granted the resource
T0   == 0             \* timestamp of the initial request, below every clock

VARIABLES
    clock,        \* clock[p]: the logical clock C_p (IR1, IR2)
    queue,        \* queue[p]: p's request queue, a set of <<timestamp, process>>
    chan,         \* chan[p][q]: FIFO of messages in flight from p to q
    lastTs,       \* lastTs[p][q]: timestamp of the last message p received from q
    pc,           \* pc[p] \in {"idle", "waiting", "held"}
    reqs,         \* reqs[p]: requests made so far (bounds the model)
    lastGranted   \* history: the last request granted, for condition II

vars == <<clock, queue, chan, lastTs, pc, reqs, lastGranted>>

Kinds   == {"req", "ack", "rel"}
Msg     == [kind : Kinds, ts : Nat, from : Proc]
Request_ == Nat \X Proc            \* a request is a timestamped process: T_m:P_i

(* The total order => of the paper, restricted to requests (A6). *)
Precedes(a, b) == a[1] < b[1] \/ (a[1] = b[1] /\ a[2] < b[2])

Max(a, b) == IF a >= b THEN a ELSE b

TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ queue \in [Proc -> SUBSET Request_]
    /\ chan \in [Proc -> [Proc -> Seq(Msg)]]
    /\ lastTs \in [Proc -> [Proc -> Nat]]
    /\ pc \in [Proc -> {"idle", "waiting", "held"}]
    /\ reqs \in [Proc -> 0..MaxReq]
    /\ lastGranted \in Request_

(* A4: P0 holds the resource, every queue contains T0:P0, clocks are above T0. *)
Init ==
    /\ clock = [p \in Proc |-> T0 + 1]
    /\ queue = [p \in Proc |-> {<<T0, P0>>}]
    /\ chan = [p \in Proc |-> [q \in Proc |-> <<>>]]
    /\ lastTs = [p \in Proc |-> [q \in Proc |-> T0]]
    /\ pc = [p \in Proc |-> IF p = P0 THEN "held" ELSE "idle"]
    /\ reqs = [p \in Proc |-> 0]
    /\ lastGranted = <<T0, P0>>

(* Append m to the channel from p to every other process (A3). *)
Broadcast(p, m) ==
    [chan EXCEPT ![p] = [q \in Proc |-> IF q = p THEN chan[p][q] ELSE Append(chan[p][q], m)]]

(* Rule 1.  P_i sends T_m:P_i "requests resource" to every other process and
   puts it on its own request queue.  IR1: the event ticks the clock. *)
Request(p) ==
    /\ pc[p] = "idle"
    /\ reqs[p] < MaxReq
    /\ LET t == clock[p] + 1 IN
       /\ clock' = [clock EXCEPT ![p] = t]
       /\ queue' = [queue EXCEPT ![p] = @ \cup {<<t, p>>}]
       /\ chan' = Broadcast(p, [kind |-> "req", ts |-> t, from |-> p])
       /\ pc' = [pc EXCEPT ![p] = "waiting"]
       /\ reqs' = [reqs EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<lastTs, lastGranted>>

(* Rule 2.  P_j receives T_m:P_i "requests resource": it places the request on
   its queue and sends a timestamped acknowledgement to P_i.  IR2(b): the clock
   jumps above T_m.  The ack carries the new clock value (IR2(a)). *)
RecvRequest(p, q) ==
    /\ q # p
    /\ chan[q][p] # <<>>
    /\ Head(chan[q][p]).kind = "req"
    /\ LET m == Head(chan[q][p])
           t == Max(clock[p], m.ts) + 1 IN
       /\ clock' = [clock EXCEPT ![p] = t]
       /\ lastTs' = [lastTs EXCEPT ![p][q] = m.ts]
       /\ queue' = [queue EXCEPT ![p] = @ \cup {<<m.ts, q>>}]
       /\ chan' = [chan EXCEPT ![q][p] = Tail(@),
                               ![p][q] = Append(@, [kind |-> "ack", ts |-> t, from |-> p])]
    /\ UNCHANGED <<pc, reqs, lastGranted>>

(* Receipt of an acknowledgement: only the clock and lastTs move (IR2(b)). *)
RecvAck(p, q) ==
    /\ q # p
    /\ chan[q][p] # <<>>
    /\ Head(chan[q][p]).kind = "ack"
    /\ LET m == Head(chan[q][p]) IN
       /\ clock' = [clock EXCEPT ![p] = Max(clock[p], m.ts) + 1]
       /\ lastTs' = [lastTs EXCEPT ![p][q] = m.ts]
       /\ chan' = [chan EXCEPT ![q][p] = Tail(@)]
    /\ UNCHANGED <<queue, pc, reqs, lastGranted>>

(* Rule 3.  P_i removes its own request from its queue and sends a timestamped
   "releases resource" message to every other process. *)
Release(p) ==
    /\ pc[p] = "held"
    /\ LET t == clock[p] + 1 IN
       /\ clock' = [clock EXCEPT ![p] = t]
       /\ queue' = [queue EXCEPT ![p] = {r \in @ : r[2] # p}]
       /\ chan' = Broadcast(p, [kind |-> "rel", ts |-> t, from |-> p])
       /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<lastTs, reqs, lastGranted>>

(* Rule 4.  P_j receives P_i "releases resource" and removes every
   T_m:P_i "requests resource" from its queue. *)
RecvRelease(p, q) ==
    /\ q # p
    /\ chan[q][p] # <<>>
    /\ Head(chan[q][p]).kind = "rel"
    /\ LET m == Head(chan[q][p]) IN
       /\ clock' = [clock EXCEPT ![p] = Max(clock[p], m.ts) + 1]
       /\ lastTs' = [lastTs EXCEPT ![p][q] = m.ts]
       /\ queue' = [queue EXCEPT ![p] = {r \in @ : r[2] # q}]
       /\ chan' = [chan EXCEPT ![q][p] = Tail(@)]
    /\ UNCHANGED <<pc, reqs, lastGranted>>

(* p's own request, when it has one. *)
MyRequest(p) == CHOOSE r \in queue[p] : r[2] = p
HasRequest(p) == \E r \in queue[p] : r[2] = p

(* Rule 5, both conditions, tested locally by P_i:
   (i)  its request precedes (=>) every other request in its queue;
   (ii) it has received from every other process a message timestamped later
        than its request. *)
CanAcquire(p) ==
    /\ HasRequest(p)
    /\ \A r \in queue[p] : r = MyRequest(p) \/ Precedes(MyRequest(p), r)
    /\ \A q \in Proc \ {p} : lastTs[p][q] > MyRequest(p)[1]

Acquire(p) ==
    /\ pc[p] = "waiting"
    /\ CanAcquire(p)
    /\ clock' = [clock EXCEPT ![p] = @ + 1]          \* IR1: being granted is an event
    /\ pc' = [pc EXCEPT ![p] = "held"]
    /\ lastGranted' = MyRequest(p)
    /\ UNCHANGED <<queue, chan, lastTs, reqs>>

Next ==
    \E p \in Proc :
        \/ Request(p)
        \/ Acquire(p)
        \/ Release(p)
        \/ \E q \in Proc : RecvRequest(p, q) \/ RecvAck(p, q) \/ RecvRelease(p, q)

Spec == Init /\ [][Next]_vars

(* A2 (every message is eventually received), the hypothesis of condition III
   (every holder eventually releases), and a process that may acquire does. *)
FairSpec ==
    /\ Spec
    /\ \A p \in Proc :
        /\ WF_vars(Acquire(p))
        /\ WF_vars(Release(p))
        /\ \A q \in Proc : WF_vars(RecvRequest(p, q)) /\ WF_vars(RecvAck(p, q)) /\ WF_vars(RecvRelease(p, q))

-----------------------------------------------------------------------------

(* With FIFO channels (A1) a queue never holds two requests of one process:
   the release that removes the old one arrives before the new request. *)
OneRequestPerProcess ==
    \A p, q \in Proc : Cardinality({r \in queue[q] : r[2] = p}) <= 1

(* Clock Condition on the wire: IR1 + FIFO make timestamps increase along a channel. *)
ChannelTimestampsIncrease ==
    \A p, q \in Proc : \A i, j \in 1..Len(chan[p][q]) : i < j => chan[p][q][i].ts < chan[p][q][j].ts

(* Condition II: successive grants follow the total order =>. *)
GrantOrder == [][lastGranted' # lastGranted => Precedes(lastGranted, lastGranted')]_vars

(* Condition III: under FairSpec, every request is eventually granted. *)
EveryRequestGranted == \A p \in Proc : (pc[p] = "waiting") ~> (pc[p] = "held")

(* Condition I (and the definition of mutual exclusion). *)
Mutex == \A p, q \in Proc : pc[p] = "held" /\ pc[q] = "held" => p = q

(* A holder's request is still in its own queue (rule 3 is the only way out). *)
HolderHasRequest == \A p \in Proc : pc[p] = "held" => HasRequest(p)

(* checked by TLC on the three models below *)
THEOREM MutualExclusion == Spec => []Mutex

-----------------------------------------------------------------------------
(* Model-checking configuration.  The annotations below describe the three models;
   MC_safety.cfg, MC_live2.cfg and MC_live.cfg next to this module say the same thing
   in the syntax TLC reads (run_tlc.sh runs them).

   @TLA_MODEL{name: "safety", spec_module: "LamportMutex", specification: "Spec"}
   @TLA_MODEL{name: "live",   spec_module: "LamportMutex", specification: "FairSpec"}
   @TLA_MODEL{name: "live2",  spec_module: "LamportMutex", specification: "FairSpec"}
   Timestamps are the mechanism of the algorithm, so every distinct clock value is a
   distinct state: N = 3 with two requests per process exceeds 16 million states
   without finishing.  The models below finish: safety on two processes and two
   requests each (the second request is what OneRequestPerProcess is about), live on
   three processes and one request each (all invariants are checked there too).
   @TLA_CONST_BIND{name: "N", value: "2", model: "safety"}
   @TLA_CONST_BIND{name: "MaxReq", value: "2", model: "safety"}
   @TLA_CONST_BIND{name: "N", value: "3", model: "live"}
   @TLA_CONST_BIND{name: "MaxReq", value: "1", model: "live"}
   @TLA_CONST_BIND{name: "N", value: "2", model: "live2"}
   @TLA_CONST_BIND{name: "MaxReq", value: "2", model: "live2"}
   @TLA_TYPE_OK{name: "TypeOK"}
   @TLA_INVARIANT{name: "Mutex"}
   @TLA_INVARIANT{name: "HolderHasRequest"}
   @TLA_INVARIANT{name: "OneRequestPerProcess"}
   @TLA_INVARIANT{name: "ChannelTimestampsIncrease"}
   @TLA_ACTION_PROPERTY{name: "GrantOrder", formula: `[][lastGranted' # lastGranted => Precedes(lastGranted, lastGranted')]_vars`}
   @TLA_LEADS_TO{name: "EveryRequestGranted", p: `pc[p] = "waiting"`, q: `pc[p] = "held"`, model: "live"}
   @TLA_LEADS_TO{name: "EveryRequestGranted", p: `pc[p] = "waiting"`, q: `pc[p] = "held"`, model: "live2"}
   @TLA_CHECK_DEADLOCK{value: false}
*)
=============================================================================
