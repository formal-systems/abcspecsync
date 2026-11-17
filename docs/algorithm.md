# Lamport's mutual-exclusion algorithm, as a state machine

Source: Leslie Lamport, *Time, Clocks, and the Ordering of Events in a Distributed
System*, Communications of the ACM 21(7), July 1978, pp. 558-565, section "Ordering the
Events Totally" (pp. 561-562).

## 1. The problem (p. 561)

A fixed set of processes share one resource. Only one process may use it at a time. An
algorithm granting the resource must satisfy three conditions:

| | Condition | In the spec |
|---|---|---|
| I | a process that has been granted the resource must release it before it can be granted to another | invariant `Mutex` |
| II | different requests must be granted in the order in which they are made | action property `GrantOrder` |
| III | if every process granted the resource eventually releases it, every request is eventually granted | liveness `EveryRequestGranted` under `FairSpec` |

"The order in which they are made" is the total order of the paper, written here as
`Precedes(a, b)`: by timestamp, ties broken by the process number.

## 2. The clocks the algorithm is built on (pp. 559-561)

Each process `P_i` keeps a logical clock `C_i`, a counter. Two implementation rules make the
clocks satisfy the Clock Condition (if `a` happened before `b` then `C(a) < C(b)`):

| Rule | Text | In the spec | In the code |
|---|---|---|---|
| IR1 | each process increments `C_i` between any two successive events | `clock[p] + 1` in `Request`, `Release`, `Acquire` | `++clock_[p]` in `request` and `release`, `clock_[p] += 1` in `acquire` |
| IR2(a) | a message `m` sent by `P_i` carries the timestamp `T_m = C_i` | `[kind |-> ..., ts |-> t, from |-> p]` | `Msg{kind, t, p}` |
| IR2(b) | on receiving `m`, `P_j` sets `C_j` greater than or equal to its present value and greater than `T_m` | `Max(clock[p], m.ts) + 1` in the three receive actions | `tick_on_receive` |

The total order `=>` on events (p. 561): `a => b` iff `C_i(a) < C_j(b)`, or they are equal
and `P_i < P_j` in an arbitrary fixed total order of the processes. Here the processes are
`1..N` and the fixed order is the order on numbers.

## 3. Assumptions (p. 561)

The paper calls them "not essential, but introduced to avoid distracting implementation
details". They are what the specification encodes and what the implementation must provide.

| | Assumption | Spec | Code |
|---|---|---|---|
| A1 | messages from `P_i` to `P_j` are received in the order sent | `chan[i][j]` is a sequence; receives take `Head` | `std::deque` per pair; only the addressee pops its front |
| A2 | every message is eventually received | `WF_vars(RecvRequest/RecvAck/RecvRelease)` in `FairSpec` | each thread serves its inbox in every phase and after its last round |
| A3 | a process can send directly to every other process | `Broadcast(p, m)` appends to every `chan[p][q]`, `q # p` | `broadcast` |
| A4 | the request queues initially contain `T0:P0`; `P0` holds the resource; `T0` is below every initial clock | `Init`: `queue[p] = {<<0, 1>>}`, `pc[1] = "held"`, `clock[p] = 1` | the `System` constructor; thread 1 starts by holding, then releasing |
| A5 | the actions of each rule form a single event | one action per rule | one method per rule, each one atomic step under `mu_` |
| A6 | an arbitrary total order on processes breaks timestamp ties | `Precedes` | `precedes` |
| A7 | no process fails (out of the paper's scope) | no crash action | none |

Two footnotes are optimisations the module does not take: an acknowledgement may be omitted
when a later-timestamped message was already sent (footnote 5), and a lower-numbered process
only needs a message timestamped `>= T_m` (footnote 6).

## 4. The five rules (p. 561) and their actions

| Rule | Text (abridged) | Action | Changes |
|---|---|---|---|
| 1 | to request the resource, `P_i` sends `T_m:P_i requests resource` to every other process and puts that message on its request queue | `Request(p)` | `clock`, `queue[p]`, `chan[p][*]`, `pc[p]`, `reqs[p]` |
| 2 | when `P_j` receives `T_m:P_i requests resource`, it places it on its request queue and sends a timestamped acknowledgement to `P_i` | `RecvRequest(p, q)` | `clock`, `lastTs[p][q]`, `queue[p]`, `chan[q][p]` (pop), `chan[p][q]` (ack) |
| 3 | to release the resource, `P_i` removes any `T_m:P_i requests resource` from its queue and sends a timestamped `P_i releases resource` to every other process | `Release(p)` | `clock`, `queue[p]`, `chan[p][*]`, `pc[p]` |
| 4 | when `P_j` receives `P_i releases resource`, it removes any `T_m:P_i requests resource` from its request queue | `RecvRelease(p, q)` | `clock`, `lastTs[p][q]`, `queue[p]`, `chan[q][p]` |
| 5 | `P_i` is granted the resource when (i) there is a `T_m:P_i requests resource` in its queue ordered before every other request by `=>`, and (ii) `P_i` has received a message from every other process timestamped later than `T_m` | `Acquire(p)` | `clock`, `pc[p]`, `lastGranted` |
| (ack) | the acknowledgement of rule 2 is itself a message: receiving it is what usually satisfies 5(ii) | `RecvAck(p, q)` | `clock`, `lastTs[p][q]`, `chan[q][p]` |

Both conditions of rule 5 are tested locally by `P_i`: `CanAcquire(p)` reads only
`queue[p]` and `lastTs[p]`.

## 5. The state machine

```
CONSTANTS  N (processes, 1..5 in the implementation), MaxReq (requests per process; bounds the model)

VARIABLES
  clock[p]        the logical clock C_p                                  Nat
  queue[p]        p's request queue: a set of <<timestamp, process>>     SUBSET (Nat \X Proc)
  chan[p][q]      messages in flight from p to q, in order               Seq(Msg)
  lastTs[p][q]    timestamp of the last message p received from q        Nat
  pc[p]           "idle" | "waiting" | "held"
  reqs[p]         requests made so far (history, bounds the model)       0..MaxReq
  lastGranted     the last request granted (history, for condition II)   Nat \X Proc

Msg == [kind : {"req", "ack", "rel"}, ts : Nat, from : Proc]
```

```
                 Request(p)                 Acquire(p)
   idle ───────────────────────▶ waiting ───────────────────────▶ held
    ▲      rule 1: tick, queue,            rule 5: (i) and (ii)       │
    │      broadcast req                   hold on queue[p], lastTs[p]│
    │                                                                 │
    └─────────────────────────────────────────────────────────────────┘
                  Release(p)   rule 3: tick, dequeue own request, broadcast rel

   In every control state, p also runs rules 2 and 4 and consumes acks:
   RecvRequest(p, q), RecvAck(p, q), RecvRelease(p, q)  on  Head(chan[q][p])
```

`Next` is the disjunction of the six actions over `p \in Proc` (and `q \in Proc` for the
receives). `Spec == Init /\ [][Next]_vars`. `FairSpec` adds weak fairness on `Acquire`,
`Release` and the three receives: A2 plus the hypothesis of condition III.

## 6. Properties checked

| Property | Kind | Paper | Model |
|---|---|---|---|
| `TypeOK` | invariant | | all three |
| `Mutex` | invariant | condition I | all three |
| `HolderHasRequest` | invariant | rule 3 is the only way a holder's request leaves its queue | all three |
| `OneRequestPerProcess` | invariant | consequence of A1 (FIFO): the release that removes an old request arrives before the next request | all three |
| `ChannelTimestampsIncrease` | invariant | Clock Condition on the wire: IR1 plus FIFO | all three |
| `GrantOrder` | action property `[][lastGranted' # lastGranted => Precedes(lastGranted, lastGranted')]_vars` | condition II | all three |
| `EveryRequestGranted` | liveness `(pc[p] = "waiting") ~> (pc[p] = "held")` | condition III | live, live2 |

Why timestamps make the model expensive: a model checker distinguishes two states whenever a
variable differs. Here the timestamps are the mechanism (every comparison in rule 5 is between
timestamps), so they cannot be abstracted away, and every distinct clock value is a distinct
state. Three processes with two requests each pass 16 million distinct states without
finishing. The models that finish, and their results, are in the README.
