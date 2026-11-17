// Lamport's distributed mutual exclusion (spec: ../spec/LamportMutex.tla).
//
// N threads (1..5) are the processes P_1..P_N of the paper.  They share one resource and talk
// only through per-pair FIFO message queues (chan[from][to]).  Every rule of the paper is one
// method of System, and every method is one atomic step under the single lock mu_.
//
// The comments of the form @TLA_<NAME>{...} are TLA+ annotations.  Each one names the symbol
// of the specification that the code next to it implements.  They are comments: the program is
// plain C++17, it includes no library for them and runs the same with or without them.
// The names used in this file:
//
//   MODULE           this file implements that module
//   CONST            the field that holds a CONSTANT of the spec
//   VAR              the field that holds a VARIABLE of the spec, with its type: the set
//                    that TypeOK gives it, written in TLA+
//   EXCLUDED         a field that is deliberately not in the spec, with the reason
//   INIT             the code that establishes Init
//   ACTION_LOCKED    the step that implements an action: from taking the named lock to the
//                    end of the block, the code is one atomic step of the spec
//   GUARD            an enabling condition of that action, named by the text of the spec
//                    conjunct; the assert under it is that condition on the fields
//   UNCHANGED        the variables that the action leaves unchanged (its frame)
//   INVARIANT        a property of the spec that the code also evaluates
//   HISTORY          a variable kept only so that a property can be stated
//   MESSAGE, CHANNEL             the message record and the queues that carry it
//   PROCESS, WEAK_FAIRNESS       the threads, and why each action eventually runs
//
// Build: ./build.sh            Run: ./lamport_mutex [N=3] [ROUNDS=2] [SEED=1]
// Log:   LM_LOG=1 ./lamport_mutex 3 2 1   prints every message sent and received, every
//        grant and release, with the sender's clock, in the order the steps happened
// Trace: LM_TRACE=run.ndjson ./lamport_mutex 3 2 1   records the run, one line per step, for
//        trace validation: ../spec/validate_trace.sh run.ndjson asks TLC whether the
//        specification can take the same steps through the same states
#include <atomic>
#include <cassert>
#include <chrono>
#include <condition_variable>
#include <cstdlib>
#include <deque>
#include <fstream>
#include <iostream>
#include <map>
#include <mutex>
#include <random>
#include <set>
#include <string>
#include <thread>
#include <utility>
#include <vector>

// @TLA_MODULE{name: "LamportMutex", file: "../spec/LamportMutex.tla"}

namespace lm {

using Clock = std::chrono::steady_clock;
using Request = std::pair<int, int>;   // <<timestamp, process>>: T_m:P_i

/// LM_LOG=1: one line per event, written while the step's lock is held, so the order printed
/// is the order of the steps.  Format:  <ms since start> P<i> C=<clock>  <what>
static std::mutex log_mu;
static void log_event(int p, int clock, const std::string &what) noexcept {
    static const bool on = std::getenv("LM_LOG") != nullptr;
    static const auto t0 = std::chrono::steady_clock::now();
    if (!on) return;
    auto ms = std::chrono::duration_cast<std::chrono::milliseconds>(std::chrono::steady_clock::now() - t0).count();
    std::lock_guard<std::mutex> g(log_mu);
    std::cout << ms / 1000 << "." << (ms % 1000) / 100 << (ms % 100) / 10 << ms % 10 << "s  P" << p
              << " C=" << clock << "  " << what << "\n";
}

/// A message of the paper: its kind, the timestamp T_m (IR2(a)) and the sender.
// @TLA_MESSAGE{type: "Msg"}
struct Msg {
    std::string kind;   // "req", "ack", "rel"
    int ts;
    int from;
};

/// The total order => of the paper on requests: timestamp first, process number on ties.
static bool precedes(const Request &a, const Request &b) {
    if (a.first != b.first) return a.first < b.first;
    return a.second < b.second;
}

/// The shared resource, used only between Acquire and Release.  It is an oracle independent of
/// the algorithm's state: two concurrent users are a mutual-exclusion violation at run time.
class Resource {
  public:
    void enter(int p) {
        if (++users_ != 1) {
            std::cerr << "MUTUAL EXCLUSION VIOLATED: P" << p << " uses the resource while another process does\n";
            violated_ = true;
        }
    }
    void leave(int) {
        --users_;
        ++uses_;
    }
    bool violated() const { return violated_; }
    int uses() const { return uses_; }

  private:
    std::atomic<int> users_{0};
    std::atomic<int> uses_{0};
    std::atomic<bool> violated_{false};
};

/// The whole system of the specification: the clocks, request queues and channels of every
/// process.  A real deployment would split it per process; the channels would be sockets.
/// Here the processes are threads, so the state is one object and every rule runs under mu_.
///
/// @TLA_WEAK_FAIRNESS{action: "Acquire"}     the waiting thread is woken on every send and re-tests rule 5
/// @TLA_WEAK_FAIRNESS{action: "Release"}     a holder releases after at most one second
/// @TLA_WEAK_FAIRNESS{action: "RecvRequest"} every thread serves its inbox in every phase, until all are done
/// @TLA_WEAK_FAIRNESS{action: "RecvAck"}
/// @TLA_WEAK_FAIRNESS{action: "RecvRelease"}
class System {
  public:
    static constexpr int P0 = 1;   // the process initially granted the resource
    static constexpr int T0 = 0;   // timestamp of its initial request

    /// @TLA_INIT{}  Assumption A4 of the paper: P0 holds the resource, every queue holds T0:P0.
    System(int n, int max_req) : n_(n), max_req_(max_req), last_granted_(T0, P0) {
        for (int p = 1; p <= n; p++) {
            clock_[p] = T0 + 1;
            queue_[p] = {Request(T0, P0)};
            reqs_[p] = 0;
            pc_[p] = p == P0 ? "held" : "idle";
            for (int q = 1; q <= n; q++) {
                chan_[p][q] = {};
                last_ts_[p][q] = T0;
            }
        }
        if (const char *file = std::getenv("LM_TRACE")) trace_.open(file);
        if (std::getenv("LM_TRACE") && !trace_.is_open()) { std::cerr << "LM_TRACE: cannot write the trace file\n"; std::exit(2); }
        if (trace_.is_open())   // first line of the trace: the constants of the run and the initial state
            trace_ << "{\"N\":" << n_ << ",\"MaxReq\":" << max_req_ << ",\"state\":" << state_json() << "}" << std::endl;
    }

    int n() const { return n_; }
    int max_req() const { return max_req_; }
    std::mutex &mu() { return mu_; }
    std::condition_variable &cv() { return cv_; }

    // ---- the five rules, one atomic step each ------------------------------------------------
    // Every @TLA_GUARD is named by the text of the spec conjunct that the assert under it
    // evaluates on the fields: one guard per enabling conjunct of the action.
    // The last statement of every step is record(...): with LM_TRACE set, it writes the action and
    // the state that the step produced, while mu_ is still held.

    /// Rule 1: P_i sends T_m:P_i "requests resource" to every other process and queues it.
    void request(int p) {
        {
            // @TLA_ACTION_LOCKED{name: "Request", lock: "mu_", params: ["p"]}
            std::lock_guard<std::mutex> step(mu_);
            // @TLA_GUARD{name: `pc[p] = "idle"`}
            assert(pc_[p] == "idle");
            // @TLA_GUARD{name: `reqs[p] < MaxReq`}
            assert(reqs_[p] < max_req_);
            int t = ++clock_[p];                        // IR1
            queue_[p].insert(Request(t, p));
            broadcast(p, Msg{"req", t, p});             // IR2(a): the message carries T_m = C_i
            pc_[p] = "waiting";
            reqs_[p] += 1;
            log_event(p, t, "rule 1: send  req  ts=" + std::to_string(t) + " to all   (queue " + queue_str(p) + ")");
            // @TLA_UNCHANGED{vars: ["lastTs", "lastGranted"]}
            record("Request", p);
        }
        cv_.notify_all();
    }

    /// Rule 2: P_j receives T_m:P_i "requests resource", queues it and acknowledges.
    void recv_request(int p, int q) {
        {
            // @TLA_ACTION_LOCKED{name: "RecvRequest", lock: "mu_", params: ["p", "q"]}
            std::lock_guard<std::mutex> step(mu_);
            // @TLA_GUARD{name: `q # p`}
            assert(q != p);
            // @TLA_GUARD{name: `chan[q][p] # <<>>`}
            assert(!chan_[q][p].empty());
            // @TLA_GUARD{name: `Head(chan[q][p]).kind = "req"`}
            assert(chan_[q][p].front().kind == "req");
            Msg m = chan_[q][p].front();
            chan_[q][p].pop_front();
            int t = tick_on_receive(p, m);              // IR2(b)
            last_ts_[p][q] = m.ts;
            queue_[p].insert(Request(m.ts, q));
            chan_[p][q].push_back(Msg{"ack", t, p});    // the timestamped acknowledgement
            log_event(p, t, "rule 2: recv  req  ts=" + std::to_string(m.ts) + " from P" + std::to_string(q) +
                                "; send ack ts=" + std::to_string(t) + " to P" + std::to_string(q) + "   (queue " + queue_str(p) + ")");
            // @TLA_UNCHANGED{vars: ["pc", "reqs", "lastGranted"]}
            record("RecvRequest", p, q);
        }
        cv_.notify_all();
    }

    /// Receipt of an acknowledgement: only the clock and lastTs move.
    void recv_ack(int p, int q) {
        {
            // @TLA_ACTION_LOCKED{name: "RecvAck", lock: "mu_", params: ["p", "q"]}
            std::lock_guard<std::mutex> step(mu_);
            // @TLA_GUARD{name: `q # p`}
            assert(q != p);
            // @TLA_GUARD{name: `chan[q][p] # <<>>`}
            assert(!chan_[q][p].empty());
            // @TLA_GUARD{name: `Head(chan[q][p]).kind = "ack"`}
            assert(chan_[q][p].front().kind == "ack");
            Msg m = chan_[q][p].front();
            chan_[q][p].pop_front();
            int t = tick_on_receive(p, m);              // IR2(b)
            last_ts_[p][q] = m.ts;
            log_event(p, t, "        recv  ack  ts=" + std::to_string(m.ts) + " from P" + std::to_string(q));
            // @TLA_UNCHANGED{vars: ["queue", "pc", "reqs", "lastGranted"]}
            record("RecvAck", p, q);
        }
        cv_.notify_all();
    }

    /// Rule 3: P_i removes its request from its queue and tells every other process.
    void release(int p) {
        {
            // @TLA_ACTION_LOCKED{name: "Release", lock: "mu_", params: ["p"]}
            std::lock_guard<std::mutex> step(mu_);
            // @TLA_GUARD{name: `pc[p] = "held"`}
            assert(pc_[p] == "held");
            int t = ++clock_[p];                        // IR1
            erase_requests_of(p, p);
            broadcast(p, Msg{"rel", t, p});
            pc_[p] = "idle";
            log_event(p, t, "rule 3: send  rel  ts=" + std::to_string(t) + " to all   RELEASED   (queue " + queue_str(p) + ")");
            // @TLA_UNCHANGED{vars: ["lastTs", "reqs", "lastGranted"]}
            record("Release", p);
        }
        cv_.notify_all();
    }

    /// Rule 4: P_j receives P_i "releases resource" and drops P_i's request from its queue.
    void recv_release(int p, int q) {
        {
            // @TLA_ACTION_LOCKED{name: "RecvRelease", lock: "mu_", params: ["p", "q"]}
            std::lock_guard<std::mutex> step(mu_);
            // @TLA_GUARD{name: `q # p`}
            assert(q != p);
            // @TLA_GUARD{name: `chan[q][p] # <<>>`}
            assert(!chan_[q][p].empty());
            // @TLA_GUARD{name: `Head(chan[q][p]).kind = "rel"`}
            assert(chan_[q][p].front().kind == "rel");
            Msg m = chan_[q][p].front();
            chan_[q][p].pop_front();
            int t = tick_on_receive(p, m);              // IR2(b)
            last_ts_[p][q] = m.ts;
            erase_requests_of(p, q);
            log_event(p, t, "rule 4: recv  rel  ts=" + std::to_string(m.ts) + " from P" + std::to_string(q) + "   (queue " + queue_str(p) + ")");
            // @TLA_UNCHANGED{vars: ["pc", "reqs", "lastGranted"]}
            record("RecvRelease", p, q);
        }
        cv_.notify_all();
    }

    /// Rule 5: P_i is granted the resource when (i) its request precedes every other request in
    /// its queue and (ii) it has received a later-timestamped message from every other process.
    void acquire(int p) {
        // @TLA_ACTION_LOCKED{name: "Acquire", lock: "mu_", params: ["p"]}
        std::lock_guard<std::mutex> step(mu_);
        // @TLA_GUARD{name: `pc[p] = "waiting"`}
        assert(pc_[p] == "waiting");
        // @TLA_GUARD{name: `CanAcquire(p)`}
        assert(can_acquire(p));
        clock_[p] += 1;                                 // IR1: being granted is an event
        pc_[p] = "held";
        last_granted_ = my_request(p);
        log_event(p, clock_[p], "rule 5: GRANTED  own request ts=" + std::to_string(last_granted_.first) +
                                    " is first in " + queue_str(p) + ", heard from every other process after it");
        int held = 0;
        for (int q = 1; q <= n_; q++) held += pc_[q] == "held";
        // @TLA_INVARIANT{name: "Mutex"}  evaluated on the algorithm's state at every grant
        if (held > 1) {
            std::cerr << "invariant Mutex violated in the algorithm state (" << held << " holders)\n";
            invariant_failed_ = true;
        }
        // @TLA_UNCHANGED{vars: ["queue", "chan", "lastTs", "reqs"]}
        record("Acquire", p);
    }

    // ---- queries the threads use to decide what to do next (caller holds mu_) --------------

    /// Both conditions of rule 5, tested locally by P_i.
    bool can_acquire(int p) const {
        if (!has_request(p)) return false;
        Request mine = my_request(p);
        for (const Request &r : queue_.at(p))
            if (r != mine && !precedes(mine, r)) return false;              // (i)
        for (int q = 1; q <= n_; q++)
            if (q != p && last_ts_.at(p).at(q) <= mine.first) return false; // (ii)
        return true;
    }
    /// The sender of the next message addressed to p, or 0.
    int next_sender(int p) const {
        for (int q = 1; q <= n_; q++)
            if (q != p && !chan_.at(q).at(p).empty()) return q;
        return 0;
    }
    std::string head_kind(int p, int q) const { return chan_.at(q).at(p).front().kind; }
    bool quiescent() const {
        for (int p = 1; p <= n_; p++)
            for (int q = 1; q <= n_; q++)
                if (!chan_.at(p).at(q).empty()) return false;
        return true;
    }
    bool invariant_failed() const { return invariant_failed_; }

    // @TLA_EXCLUDED{reason: "termination bookkeeping of the threads, not part of the algorithm"}
    int finished = 0;

  private:
    std::string queue_str(int p) const noexcept {   // the request queue as the paper writes it: T_m:P_i
        std::string s = "{";
        for (const Request &r : queue_.at(p)) s += (s.size() > 1 ? ", " : "") + std::to_string(r.first) + ":P" + std::to_string(r.second);
        return s + "}";
    }
    bool has_request(int p) const noexcept {
        for (const Request &r : queue_.at(p))
            if (r.second == p) return true;
        return false;
    }
    // The helpers below run inside an action after its first write; they are noexcept, so a
    // step is never left half done.
    Request my_request(int p) const noexcept {
        for (const Request &r : queue_.at(p))
            if (r.second == p) return r;
        return Request(-1, -1);
    }
    /// IR2(b): on receipt, the clock jumps past the message's timestamp.  Returns the new value.
    int tick_on_receive(int p, const Msg &m) noexcept {
        clock_[p] = (clock_[p] >= m.ts ? clock_[p] : m.ts) + 1;
        return clock_[p];
    }
    void broadcast(int p, const Msg &m) noexcept {
        for (int q = 1; q <= n_; q++)
            if (q != p) chan_[p][q].push_back(m);
    }
    void erase_requests_of(int p, int owner) noexcept {
        for (auto it = queue_[p].begin(); it != queue_[p].end();)
            it = it->second == owner ? queue_[p].erase(it) : std::next(it);
    }

    // ---- trace validation --------------------------------------------------------------------
    // With LM_TRACE=<file> the program records its run, one JSON object per line.  The first line
    // holds the constants and the initial state.  Every later line is one step: the action, its
    // parameters and the values of the seven variables after the step.  A function on 1..N is an
    // array of length N, a set or a sequence is an array, a request is [timestamp, process], a
    // message is an object.  ../spec/LamportMutexTrace.tla reads the file, and TLC decides
    // whether the specification can take the same steps through the same states.

    /// The values of the seven variables of the spec, as JSON (caller holds mu_).
    std::string state_json() const {
        auto num = [](int x) { return std::to_string(x); };
        auto req = [&](const Request &r) { return "[" + num(r.first) + "," + num(r.second) + "]"; };
        std::string clock, queue, chan, last_ts, pc, reqs;
        for (int p = 1; p <= n_; p++) {
            std::string sep = p > 1 ? "," : "", queue_p, chan_p, last_ts_p;
            for (const Request &r : queue_.at(p)) queue_p += (queue_p.empty() ? "" : ",") + req(r);
            for (int q = 1; q <= n_; q++) {
                std::string msgs;
                for (const Msg &m : chan_.at(p).at(q))
                    msgs += (msgs.empty() ? "" : ",") +
                            ("{\"kind\":\"" + m.kind + "\",\"ts\":" + num(m.ts) + ",\"from\":" + num(m.from) + "}");
                chan_p += (q > 1 ? "," : "") + ("[" + msgs + "]");
                last_ts_p += (q > 1 ? "," : "") + num(last_ts_.at(p).at(q));
            }
            clock += sep + num(clock_.at(p));
            queue += sep + "[" + queue_p + "]";
            chan += sep + "[" + chan_p + "]";
            last_ts += sep + "[" + last_ts_p + "]";
            pc += sep + "\"" + pc_.at(p) + "\"";
            reqs += sep + num(reqs_.at(p));
        }
        return "{\"clock\":[" + clock + "],\"queue\":[" + queue + "],\"chan\":[" + chan + "],\"lastTs\":[" + last_ts +
               "],\"pc\":[" + pc + "],\"reqs\":[" + reqs + "],\"lastGranted\":" + req(last_granted_) + "}";
    }
    /// One line of the trace: the step just taken and the state it leads to.  It is the last
    /// statement of a step, so mu_ is still held: the lines are in the order of the steps, and
    /// each state is exactly the one that the step produced.
    void record(const char *action, int p, int q = 0) {
        if (!trace_.is_open()) return;
        trace_ << "{\"action\":\"" << action << "\",\"p\":" << p;
        if (q != 0) trace_ << ",\"q\":" << q;
        trace_ << ",\"state\":" << state_json() << "}" << std::endl;
    }

    // @TLA_CONST{name: "N"}
    int n_;
    // @TLA_CONST{name: "MaxReq"}
    int max_req_;
    // @TLA_EXCLUDED{reason: "synchronisation: makes every rule one atomic step (assumption A5)"}
    std::mutex mu_;
    // @TLA_EXCLUDED{reason: "synchronisation: wakes waiting threads on every send"}
    std::condition_variable cv_;
    // @TLA_VAR{name: "clock", type: `[Proc -> Nat]`}
    std::map<int, int> clock_;
    // @TLA_VAR{name: "queue", type: `[Proc -> SUBSET Request_]`}
    std::map<int, std::set<Request>> queue_;
    // @TLA_CHANNEL{name: "chan", kind: "fifo", msg_type: "Msg"}
    // @TLA_VAR{name: "chan", type: `[Proc -> [Proc -> Seq(Msg)]]`}
    std::map<int, std::map<int, std::deque<Msg>>> chan_;
    // @TLA_VAR{name: "lastTs", type: `[Proc -> [Proc -> Nat]]`}
    std::map<int, std::map<int, int>> last_ts_;
    // @TLA_VAR{name: "pc", type: `[Proc -> {"idle", "waiting", "held"}]`}
    std::map<int, std::string> pc_;
    // @TLA_HISTORY{var: "reqs"}
    // @TLA_VAR{name: "reqs", type: `[Proc -> 0..MaxReq]`}
    std::map<int, int> reqs_;
    // @TLA_HISTORY{var: "lastGranted"}
    // @TLA_VAR{name: "lastGranted", type: `Request_`}
    Request last_granted_;
    // @TLA_EXCLUDED{reason: "diagnostic flag"}
    bool invariant_failed_ = false;
    // @TLA_EXCLUDED{reason: "trace output: it records the steps and is never read by the algorithm"}
    std::ofstream trace_;
};

/// One process of the paper: a thread that, ROUNDS times, waits between 0 and 2 seconds, asks
/// for the resource, uses it for up to 1 second and releases it.  In every phase it keeps
/// serving its inbox (rules 2 and 4 and acknowledgements), because the other processes depend
/// on its messages to make progress.  The delays come from a generator seeded by (seed, p), so
/// a run is reproducible for a given seed up to thread scheduling.
class Process {
  public:
    Process(System &sys, Resource &res, int p, int rounds, unsigned seed)
        : sys_(sys), res_(res), p_(p), rounds_(rounds), rng_(seed * 1000u + (unsigned)p) {}

    /// @TLA_PROCESS{name: "proc", set: "Proc"}  one thread per element of Proc; this is the
    /// order in which it takes the steps of Next.
    void run() {
        if (p_ == lm::System::P0) hold_then_release();     // A4: P0 starts as the holder
        for (int round = 1; round <= rounds_; round++) {
            serve_until(Clock::now() + ms(0, 2000));       // may ask for the resource after 0..2 s
            sys_.request(p_);
            wait_for_grant();
            hold_then_release();
        }
        {
            std::lock_guard<std::mutex> g(sys_.mu());
            sys_.finished += 1;
        }
        sys_.cv().notify_all();
        serve_until_all_done();
    }

  private:
    std::chrono::milliseconds ms(int lo, int hi) {
        return std::chrono::milliseconds(std::uniform_int_distribution<int>(lo, hi)(rng_));
    }
    /// Use the resource for up to 1 s, still serving the inbox, then rule 3.
    void hold_then_release() {
        res_.enter(p_);
        serve_until(Clock::now() + ms(0, 1000));
        res_.leave(p_);
        sys_.release(p_);
    }
    /// Receive one message addressed to p, dispatching to the rule its kind selects.
    void dispatch(int q, const std::string &kind) {
        if (kind == "req") sys_.recv_request(p_, q);
        else if (kind == "ack") sys_.recv_ack(p_, q);
        else sys_.recv_release(p_, q);
    }
    /// Serve the inbox until the deadline (receives are the only events while idle or holding).
    void serve_until(Clock::time_point deadline) {
        for (;;) {
            int q; std::string kind;
            {
                std::unique_lock<std::mutex> g(sys_.mu());
                if (!sys_.cv().wait_until(g, deadline, [&] { return sys_.next_sender(p_) != 0; })) return;
                q = sys_.next_sender(p_);
                kind = sys_.head_kind(p_, q);
            }
            dispatch(q, kind);   // only p_ consumes chan[q][p_], so the head is still there
        }
    }
    /// Serve the inbox until rule 5 holds, then take the resource.
    void wait_for_grant() {
        for (;;) {
            int q = 0; std::string kind;
            {
                std::unique_lock<std::mutex> g(sys_.mu());
                sys_.cv().wait(g, [&] { return sys_.can_acquire(p_) || sys_.next_sender(p_) != 0; });
                q = sys_.next_sender(p_);
                if (q != 0) kind = sys_.head_kind(p_, q);
            }
            if (q != 0) { dispatch(q, kind); continue; }
            sys_.acquire(p_);
            return;
        }
    }
    /// After the last round: keep answering until every process is done and nothing is in flight.
    void serve_until_all_done() {
        for (;;) {
            int q = 0; std::string kind;
            {
                std::unique_lock<std::mutex> g(sys_.mu());
                sys_.cv().wait(g, [&] { return sys_.next_sender(p_) != 0 || (sys_.finished == sys_.n() && sys_.quiescent()); });
                q = sys_.next_sender(p_);
                if (q == 0) return;
                kind = sys_.head_kind(p_, q);
            }
            dispatch(q, kind);
        }
    }

    System &sys_;
    Resource &res_;
    int p_;
    int rounds_;
    std::mt19937 rng_;
};

}  // namespace lm

int main(int argc, char **argv) {
    int n = argc > 1 ? std::atoi(argv[1]) : 3;
    int rounds = argc > 2 ? std::atoi(argv[2]) : 2;
    unsigned seed = argc > 3 ? (unsigned)std::atoi(argv[3]) : 1u;
    if (n < 1 || n > 5 || rounds < 0) { std::cerr << "usage: " << argv[0] << " [N=1..5] [ROUNDS] [SEED]\n"; return 2; }
    lm::System sys(n, rounds);   // the constants of this run: N = n, MaxReq = rounds
    lm::Resource res;
    std::vector<lm::Process> procs;
    for (int p = 1; p <= n; p++) procs.emplace_back(sys, res, p, rounds, seed);
    std::vector<std::thread> threads;
    for (auto &pr : procs) threads.emplace_back([&pr] { pr.run(); });
    for (auto &t : threads) t.join();
    bool ok = !res.violated() && !sys.invariant_failed();
    std::cout << "lamport_mutex: " << n << " processes x " << rounds << " rounds, seed " << seed
              << ", resource used " << res.uses() << " times: "
              << (ok ? "mutual exclusion held" : "MUTUAL EXCLUSION VIOLATED") << "\n";
    return ok ? 0 : 1;
}
