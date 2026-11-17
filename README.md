# ABCSpecSync example: Lamport's mutual exclusion, code and specification in sync

Lamport's 1978 paper *Time, Clocks, and the Ordering of Events in a Distributed System*
gives a distributed mutual-exclusion algorithm as five rules over logical clocks. This
directory holds the algorithm as a specification and as a program. The model checker verifies
the specification; trace validation and the views check that the program and the specification
say the same thing:

| | Where | What |
|---|---|---|
| The specification | `spec/LamportMutex.tla` | a TLA+ state machine: seven variables, one action per rule, the paper's three conditions as properties, three models for the TLC model checker |
| The implementation | `cpp/lamport_mutex.cpp` | a C++17 program: N threads are the processes, every rule is one method. Comments of the form `@TLA_...{...}` say which variable or action of the spec each piece of code implements |
| Trace validation | `spec/LamportMutexTrace.tla`, `spec/validate_trace.sh` | the program records its run; TLC decides whether the specification can take the same steps through the same states |
| The views | `views/sync-views.html` | code on the left, spec on the right, one view per group of variables and per action, with a table that says what binds them and whether they agree |

`docs/algorithm.md` is the reading of the paper that the others follow: the five rules, the
clock rules IR1 and IR2, the assumptions A1 to A7, the state machine, the properties.

What you need: Java 11 or later (for TLC), a C++17 compiler, Python 3.9 or later (to
regenerate the views and for the negative control; standard library only). Docker is needed
only for the sanitizer runs on macOS. TLC and the
TLA+ community modules are included in `tools/`.

Everything in one command, about one minute:

```sh
./run_all.sh
```

```
== 1. model checking the specification
model safety: no error, 4786 distinct states, depth 27
model live2: no error, 4786 distinct states, depth 27
== 2. build
== 3. record runs (3 processes, 2 rounds) and validate each trace against the specification
lamport_mutex: 3 processes x 2 rounds, seed 1, resource used 7 times: mutual exclusion held
traces/n3-r2-s1.ndjson: ACCEPTED: the 57 recorded steps are steps of the specification, through the same states
...
== 4. negative control: copies of traces/n3-r2-s1.ndjson with one edit each must be REJECTED
tampered copies: REJECTED 13 of 13
RESULT: the models hold, every recorded run is ACCEPTED by the specification, every tampered copy is REJECTED
```

The sections below take the steps one at a time.

## 1. Model-check the specification

```sh
spec/run_tlc.sh              # the two models that finish in seconds: safety, then live2
spec/run_tlc.sh safety       # one model
spec/run_tlc.sh live         # the large one: 7.1 million states, see the table
```

The script runs
`java -cp tools/tla2tools.jar tlc2.TLC -workers 4 -config MC_<model>.cfg LamportMutex` in `spec/`.
`WORKERS=8 spec/run_tlc.sh` changes the number of threads, `JAVA_OPTS=-Xmx6g` passes options to
Java (here a 6 GB heap, for the large model), and `TLA2TOOLS=/path/to/tla2tools.jar` uses another
copy of TLC. In VS Code with the TLA+ extension, open `spec/LamportMutex.tla` and
check the model with one of the three `MC_*.cfg` files as its configuration.

A run that finds no error ends like this:

```
Model checking completed. No error has been found.
7913 states generated, 4786 distinct states found, 0 states left on queue.
The depth of the complete state graph search is 27.
```

The three models:

| Model | Constants | Specification | Checks | Distinct states | Depth | Result |
|---|---|---|---|---|---|---|
| `safety` | N = 2, MaxReq = 2 | `Spec` | TypeOK, Mutex, HolderHasRequest, OneRequestPerProcess, ChannelTimestampsIncrease, GrantOrder | 4,786 | 27 | no error, 2 s |
| `live2` | N = 2, MaxReq = 2 | `FairSpec` | the same plus EveryRequestGranted | 4,786 | 27 | no error, 4 s |
| `live` | N = 3, MaxReq = 1 | `FairSpec` | the same plus EveryRequestGranted | 7,128,781 | 31 | no error, 26 minutes with 8 threads and a 6 GB heap (`WORKERS=8 JAVA_OPTS=-Xmx6g spec/run_tlc.sh live`); 7 of those minutes are the last liveness check, over the complete graph |

`spec/LamportMutex.pdf` is the module as the TLA+ pretty-printer typesets it: mathematical
symbols, comments shaded, and the line numbers of the `.tla` file. To make it again after a change
(needs LaTeX), run this in `spec/`; it also writes `.tex`, `.aux` and `.log` files there:

```sh
java -cp ../tools/tla2tools.jar tla2tex.TLA -shade -number -nops -textwidth 470 -hoffset -64 \
     -textheight 675 -voffset -72 -latexCommand pdflatex -latexOutputExt pdf LamportMutex.tla
```

What the properties say: `Mutex` is condition I of the paper (one holder at a time),
`GrantOrder` is condition II (requests are granted in the order of their timestamps),
`EveryRequestGranted` is condition III (every request is eventually granted, if messages are
delivered and holders release: the fairness in `FairSpec`). The other invariants are facts
the algorithm relies on. The module's own header lists the assumptions it encodes.

Why the models are small: timestamps are the mechanism of the algorithm, so every distinct
clock value is a distinct state. Three processes with two requests each pass 16 million
states without finishing.

## 2. Run the implementation

```sh
cpp/build.sh                        # builds cpp/lamport_mutex
cpp/lamport_mutex                   # 3 processes, 2 rounds each, seed 1: about 5 s
cpp/lamport_mutex 5 3 7             # N = 5, ROUNDS = 3, SEED = 7: about 10 s
LM_LOG=1 cpp/lamport_mutex 3 2 1    # the first run again, with every step printed
```

`N` threads (1 to 5), `P_1` to `P_N`, share one resource through per-pair FIFO message
queues. Each thread repeats `ROUNDS` times: it stays idle for 0 to 2 seconds, asks for the
resource (rule 1), serves its inbox until rule 5 grants it, uses the resource for 0 to 1
second while still answering requests (rules 2 and 4), and releases it (rule 3). `P_1` starts
as the holder, as the paper assumes. The delays come from a generator seeded by `(SEED, p)`.

The last line is the verdict, and the exit status is 1 if mutual exclusion was violated:

```
lamport_mutex: 3 processes x 2 rounds, seed 1, resource used 7 times: mutual exclusion held
```

Two independent checks stand behind that line. A resource oracle (`Resource`) counts the
threads that use the resource at the same time and knows nothing of the algorithm. The
algorithm's own state is checked at every grant (`@TLA_INVARIANT{name: "Mutex"}`).

With `LM_LOG=1`, one line per step, in the order the steps happened, with the request queue
in the paper's notation (here from `LM_LOG=1 cpp/lamport_mutex 2 1 3`):

```
0.261s  P1 C=3  rule 1: send  req  ts=3 to all   (queue {3:P1})
0.261s  P2 C=4  rule 2: recv  req  ts=3 from P1; send ack ts=4 to P1   (queue {3:P1})
0.261s  P1 C=5          recv  ack  ts=4 from P2
0.261s  P1 C=6  rule 5: GRANTED  own request ts=3 is first in {3:P1}, heard from every other process after it
0.535s  P1 C=7  rule 3: send  rel  ts=7 to all   RELEASED   (queue {})
0.535s  P2 C=8  rule 4: recv  rel  ts=7 from P1   (queue {})
```

**Sanitizers.** `cpp/sanitize.sh` builds the program with AddressSanitizer and
UndefinedBehaviorSanitizer, then with ThreadSanitizer, for g++ and clang, and runs each build on
six sizes (N = 1 to 5) and once with `LM_LOG=1`. Every run also records its trace, and the traces
are validated as in the next section.

```sh
cpp/sanitize.sh             # on Linux, with the compilers of the machine
cpp/sanitize.sh --docker    # in a Linux container (ubuntu:24.04; g++ and clang are installed in it)
```

```
ok    g++-thread  N=5 ROUNDS=3 SEED=2  230 steps, no report
...
RESULT: 28 sanitized runs, no report, every run exits with status 0
traces: ACCEPTED 28 of 28
```

Observed with g++ 13.3 and clang 18.1: no report in the 28 runs. A copy in which
`sys_.finished += 1` runs without the lock: ThreadSanitizer reports a data race and the script
fails, while the 14 traces of that copy are still ACCEPTED. `finished` is excluded state: the
specification says nothing about it, so only the sanitizer can see that defect.

## 3. Validate a run against the specification

"Mutual exclusion held" says that one run did nothing visibly wrong. Trace validation asks
more: was that run a behaviour of the specification, step by step?

```sh
LM_TRACE=traces/run.ndjson cpp/lamport_mutex 3 2 1     # record the run
spec/validate_trace.sh traces/run.ndjson               # ask TLC
```

```
traces/run.ndjson: ACCEPTED: the 57 recorded steps are steps of the specification, through the same states
```

**What the program records.** With `LM_TRACE` set, one JSON object per line. The first line
holds the constants of the run and the initial state. Every later line is one step: the name
of the action, its parameters, and the values of the seven variables after the step.

```
{"N":3,"MaxReq":2,"state":{"clock":[1,1,1],"queue":[[[0,1]],[[0,1]],[[0,1]]],"chan":[[[],[],[]],[[],[],[]],[[],[],[]]],"lastTs":[[0,0,0],[0,0,0],[0,0,0]],"pc":["held","idle","idle"],"reqs":[0,0,0],"lastGranted":[0,1]}}
{"action":"Request","p":2,"state":{"clock":[1,2,1],"queue":[[[0,1]],[[0,1],[2,2]],[[0,1]]],"chan":[[[],[],[]],[[{"kind":"req","ts":2,"from":2}],[],[{"kind":"req","ts":2,"from":2}]],[[],[],[]]],"lastTs":[...],"pc":["held","waiting","idle"],"reqs":[0,1,0],"lastGranted":[0,1]}}
```

In the code this is `record("Request", p)`, the last statement of every step, executed while
the step's lock is still held. So the lines are in the order of the steps, and each state is
exactly the one that the step produced. `state_json()` writes the seven fields; the two
functions are about forty lines of plain C++.

**What TLC checks.** `spec/LamportMutexTrace.tla` extends the specification with one variable,
`l`, the number of lines matched so far. Its next-state relation allows one thing only: the
action that line `l + 1` names, with the recorded parameters, leading to the recorded state.

```tla
Step(e) ==
    \/ e.action = "Request"     /\ Request(e.p)
    \/ e.action = "RecvRequest" /\ RecvRequest(e.p, e.q)
    ...
Replay ==
    /\ l < Len(Events)
    /\ LET e == Events[l + 1] IN Step(e) /\ Mismatch(e.state) = {} ...
    /\ l' = l + 1
```

`Request`, `RecvRequest` and the others are the actions of `LamportMutex`, unchanged: a
recorded step is accepted only if the specification allows it. The constants `N` and `MaxReq`
are read from the first line, and the first line must be the `Init` of the specification.
The invariants and `GrantOrder` are checked on the states of the run as well.

**The verdict.** TLC runs with deadlock checking. If every line is matched, the last state
stutters and TLC finds no error: ACCEPTED. If line `k` cannot be matched, the state before it
has no successor, TLC reports a deadlock, and the script says which step it was and why:

```
REJECTED at step 3 of 57, RecvAck(2, 1): the specification can take this step, but reaches a state that differs from the recorded one in {"lastTs"}
REJECTED at step 23 of 57, Acquire(1): the specification cannot take this step from the state reached after step 22 (an enabling condition of the action is false there)
```

TLC's complete output, with the accepted part of the run as a behaviour, is kept in
`$TMPDIR/abcspecsync-tlc/trace/tlc.log`.

**What was observed.**

| Input | Verdict |
|---|---|
| 20 runs: N = 1, 2, 3, 4, 5 with two rounds (7, 26, 57, 100 and 155 steps), thirteen seeds with N = 3, three seeds with N = 5 and three rounds (230 steps) | ACCEPTED, every one |
| 13 copies of one trace with one edit each (`tools/tamper_trace.py`): a clock off by one, a stale `lastTs`, `queue`, `reqs` or `lastGranted`, `pc` not set on a grant, an older timestamp in an acknowledgement, a wrong action, a wrong sender, a dropped step, two steps swapped, another initial holder, `MaxReq` lowered | REJECTED 13 of 13 |
| A prefix of a trace (the first 30 steps) | ACCEPTED: a prefix of a behaviour is a behaviour |
| The program without condition (ii) of rule 5 | prints "mutual exclusion held"; REJECTED at an `Acquire` that the specification does not allow |
| The program that does not update `lastTs` on an acknowledgement | prints "mutual exclusion held"; REJECTED at the first `RecvAck`, in `lastTs` |
| The program without `Max` in the clock on receipt | prints "mutual exclusion held"; REJECTED at the first receive of a message timestamped above the receiver's clock (step 2 in the runs observed: a `RecvRequest`, in `clock` and `chan`, or a `RecvRelease`, in `clock`) |
| The program that sends no acknowledgement | prints "mutual exclusion held"; REJECTED at the first `RecvRequest`, in `chan` |
| The program that keeps its request in its queue on release | reports MUTUAL EXCLUSION VIOLATED, exit status 1 (two runs); REJECTED at the first `Release`, in `queue` |

The tampered copies are the negative control: a copy that TLC accepted would mean that some
part of a recorded step is not compared with the specification. `run_all.sh` repeats it.

**What it proves, and what it does not.** An ACCEPTED trace proves that this run is a
behaviour of the specification, so every property that TLC verified for the specification
holds for this run, and the code took only steps that the algorithm allows. It says nothing
about the runs that were not recorded: a defect that no recorded run exercises stays unseen
(the tie-break on equal timestamps, for example, needs two requests with the same timestamp).
More seeds and more processes give more runs; the model checker covers every behaviour, but
of the specification.

The method is that of Cirstea, Kuppe, Loillier and Merz, *Validating Traces of Distributed
Programs Against TLA+ Specifications*.

## 4. The annotations

The program is plain C++17. The annotations are comments, so they change nothing in the
binary; they are there for the reader, and for any tool that wants to line the two files up.
Each one names a symbol of the spec:

```cpp
// @TLA_VAR{name: "clock", type: `[Proc -> Nat]`}
std::map<int, int> clock_;
```

```cpp
void request(int p) {
    {
        // @TLA_ACTION_LOCKED{name: "Request", lock: "mu_", params: ["p"]}
        std::lock_guard<std::mutex> step(mu_);
        // @TLA_GUARD{name: `pc[p] = "idle"`}
        assert(pc_[p] == "idle");
        ...
        // @TLA_UNCHANGED{vars: ["lastTs", "lastGranted"]}
        record("Request", p);
    }
```

| Annotation | On | Binds |
|---|---|---|
| `@TLA_MODULE` | the file | the module that the file implements |
| `@TLA_CONST` | a field | a CONSTANT of the spec (`N`, `MaxReq`) |
| `@TLA_VAR` | a field | a VARIABLE of the spec, with its type: the set that `TypeOK` gives it |
| `@TLA_EXCLUDED` | a field | state that is deliberately not in the spec, with the reason (the mutex, the condition variable, bookkeeping, the trace output) |
| `@TLA_HISTORY` | a field | a variable kept only so that a property can be stated |
| `@TLA_INIT` | the constructor | the initial state, `Init` |
| `@TLA_ACTION_LOCKED` | a statement | one action: from taking the named lock to the end of the block, the code is one atomic step of the spec |
| `@TLA_GUARD` | a statement | one enabling conjunct of that action, named by its text in the spec; the assert under it is the same condition on the fields |
| `@TLA_UNCHANGED` | a statement | the variables that the action leaves unchanged |
| `@TLA_INVARIANT` | a statement | a property of the spec that the code also evaluates |
| `@TLA_MESSAGE`, `@TLA_CHANNEL` | a struct, a field | the message record and the queues that carry it |
| `@TLA_PROCESS`, `@TLA_WEAK_FAIRNESS` | a method, a class | the threads, and why each action eventually runs |

The spec carries the links in the other direction: `@TLA_IMPL` on the constants, and at the
end of the module `@TLA_MODEL`, `@TLA_CONST_BIND`, `@TLA_INVARIANT` and the others, which
describe the three models that the `MC_*.cfg` files give to TLC.

The type in `@TLA_VAR` is written in TLA+: it is the set that the `TypeOK` invariant of the
spec gives the variable (`clock \in [Proc -> Nat]`), so the annotation and the spec say the
same thing in the same words. Values that contain quotes are written between backticks.

## 5. The views

Open `views/sync-views.html` in a browser (`views/sync-views.pdf` is the same content, one
view per page or two, A4 landscape). Seventeen views:

| View | Teaches |
|---|---|
| Overview | how to read the views, the three checks, the annotations used, the binding summary |
| Module and constants | which module the file implements; what must be fixed for a model and for a run |
| Variables | state: every variable is one field, every other field is excluded on purpose; the type of each is its `TypeOK` set |
| Init | the initial state on both sides |
| Rule 1, Rule 2, Acknowledgement, Rule 3, Rule 4, Rule 5 | one action each: the atomic step, the guards, what changes, what does not, where the step is recorded |
| Rule 5: conditions (i) and (ii) | a guard that is a definition in the spec and a function in the code |
| Clocks, broadcast, FIFO channels | the helpers: operators in the spec, small functions in the code |
| Next, processes and fairness | which thread takes which step; liveness assumptions |
| Properties and the oracle | what must hold, and who checks it: TLC on the model, the code on a run |
| Models | the models in the spec and the configuration files of TLC |
| Trace validation | what the code records, what the trace specification checks, what was observed |
| Exercises | eight changes to make, with the outcome to predict and then observe |

In the last column of each table, ✓ and ✗ are computed from the files when the views are
generated: 179 checks for this copy, all in agreement. A line that starts with · is an
explanation written by hand. To see a check fail, change one side and generate again:

```sh
python3 views/make_views.py            # writes views/sync-views.html, and the PDF if Chrome is installed
python3 views/make_views.py --no-pdf   # the HTML only; prints the checks that fail, exit status 1 if any
```

The script reads the files with regular expressions and is written for this example. What it
compares is names and sets: every variable has a field and the type that `TypeOK` gives it,
every action has a step, the guards carry the text of the enabling conjuncts, the fields that
a step writes are the variables that the action primes, the frame is the same on both sides,
every step is recorded under its action's name, the models match the configuration files. It
does not compare values: that is what trace validation does, on the runs that were recorded.

## 6. The tutorial slides

`slides/code-and-spec-tutorial.pptx` (55 slides) is a tutorial for readers who have never seen
TLA+. It starts with the problem, the five rules and the TLA+ notation that this specification
uses, then walks through the files with the C++ on the left and the TLA+ on the right. Every
line of `cpp/lamport_mutex.cpp`, `spec/LamportMutex.tla` and `spec/LamportMutexTrace.tla` is on
a slide, with its line number in the file; each slide has two or three remarks on what to
notice, and speaker notes.

## 7. Exercises

The last view lists them; each outcome below was observed on this copy.

| Change | Observed |
|---|---|
| Code: remove `"lastGranted"` from `@TLA_UNCHANGED` in `request` | the view on rule 1 fails: the frames differ |
| Code: delete `last_ts_[p][q] = m.ts;` in `recv_ack` | the view on the acknowledgement fails; the program prints "mutual exclusion held"; its trace is REJECTED at the first `RecvAck` |
| Code: rename the guard of `release` to `pc[p] = "waiting"` | the view on rule 3 fails; the program still runs |
| Code: add a field to `System` without annotation | the view on variables asks whether it is a spec variable or excluded |
| Code: remove condition (ii) from `can_acquire` | nine runs, none reported a violation; the trace of such a run is REJECTED at an `Acquire` |
| Spec: remove condition (ii) from `CanAcquire` | `safety`: `Invariant Mutex is violated`, a behaviour of 7 states, about a second |
| Spec: remove the tie-break from `Precedes` | `safety`: no error (4,771 distinct states); `live2`: a temporal property is violated |
| Spec: no acknowledgement in `RecvRequest` | `safety`: no error (880 distinct states); `live2`: a temporal property is violated |
| Spec: no `Max` in the clock of `RecvRequest` | `safety`: no error; `live2`: a temporal property is violated |

The fifth and sixth rows are the same defect on the two sides: the runs pass, trace
validation rejects the run at the step the algorithm does not allow, and the model checker
shows the behaviour in which that step breaks mutual exclusion. The last three keep mutual
exclusion and lose progress, which only a model with fairness shows.

## Layout

```
abcspecsync/
  README.md                     this file
  LICENSE                       the licence of the example (Apache License 2.0)
  run_all.sh                    models, build, record, validate, negative control
  spec/LamportMutex.tla         the specification
  spec/LamportMutex.pdf         the same module typeset by the TLA+ pretty-printer, with the line numbers of the file
  spec/MC_safety.cfg            the three models (MC_live2.cfg, MC_live.cfg)
  spec/run_tlc.sh               runs TLC on them
  spec/LamportMutexTrace.tla    the trace specification (LamportMutexTrace.cfg)
  spec/validate_trace.sh        runs TLC on a recorded trace: ACCEPTED or REJECTED at step k
  cpp/lamport_mutex.cpp         the implementation, annotated in comments; records its run with LM_TRACE
  cpp/build.sh                  builds it
  cpp/sanitize.sh               runs it under the address, undefined-behaviour and thread sanitizers
  traces/                       the runs recorded by run_all.sh
  views/sync-views.html         the views; sync-views.pdf is the same content
  views/make_views.py           generates them from the files
  docs/algorithm.md             the paper's rules, assumptions, state machine and properties
  slides/code-and-spec-tutorial.pptx   a tutorial deck for readers new to TLA+: every line of the code and of the specs
  tools/tamper_trace.py         the negative control of trace validation
  tools/tla2tools.jar           TLC 2.20 (TLA+ tools, build 8fca17f of 2026-02-24)
  tools/CommunityModules-deps.jar   the TLA+ community modules (Json and IOUtils are used to read the trace)
```

The example itself is under the Apache License 2.0, see `LICENSE`.
The two jars are unmodified distributions of the TLA+ project, under their MIT licences:
https://github.com/tlaplus/tlaplus and https://github.com/tlaplus/CommunityModules.
