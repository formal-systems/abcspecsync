#!/usr/bin/env bash
# Trace validation: is a recorded run of cpp/lamport_mutex a behaviour of LamportMutex.tla?
#
#   LM_TRACE=traces/run.ndjson cpp/lamport_mutex 3 2 1     record a run
#   spec/validate_trace.sh traces/run.ndjson               ask TLC (several files may be given)
#
# TLC checks LamportMutexTrace.tla, which extends the specification and can only take the
# recorded steps.  One line is printed per file:
#   ACCEPTED   every recorded step is a step of the specification, through the same states
#   REJECTED   at step k: the first recorded step that the specification cannot take
# The exit status is 0 if every file is accepted, 1 if one is rejected, 2 on an error.
# TLC's full output for the last file checked is kept in $TMPDIR/abcspecsync-tlc/trace/tlc.log.
#
# Needs Java 11 or later.  TLA2TOOLS and COMMUNITY_MODULES override the two jars in ../tools.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
JAR="${TLA2TOOLS:-$HERE/../tools/tla2tools.jar}"
CM="${COMMUNITY_MODULES:-$HERE/../tools/CommunityModules-deps.jar}"
[ $# -ge 1 ] || { echo "usage: $0 trace.ndjson [more.ndjson ...]"; exit 2; }
for j in "$JAR" "$CM"; do [ -f "$j" ] || { echo "jar not found: $j"; exit 2; }; done
META="${TMPDIR:-/tmp}/abcspecsync-tlc/trace"
mkdir -p "$META"
LOG="$META/tlc.log"
status=0

step_text() {   # step_text FILE K -> "RecvAck(2, 1)", read from line K + 1 of the trace
  sed -n "$(($2 + 1))p" "$1" | sed -E 's/^\{"action":"([A-Za-z]+)","p":([0-9]+)(,"q":([0-9]+))?.*/\1(\2\3)/; s/,"q":/, /'
}

for f in "$@"; do
  [ -f "$f" ] || { echo "$f: no such file"; status=2; continue; }
  abs="$(cd "$(dirname "$f")" && pwd)/$(basename "$f")"
  steps=$(($(grep -c '' "$abs") - 1))
  (cd "$HERE" && LM_TRACE="$abs" java -XX:+UseParallelGC -cp "$JAR:$CM" tlc2.TLC -workers 1 -noGenerateSpecTE \
      -metadir "$META/states" -config LamportMutexTrace.cfg LamportMutexTrace) > "$LOG" 2>&1
  if grep -q "Model checking completed. No error has been found." "$LOG"; then
    echo "$f: ACCEPTED: the $steps recorded steps are steps of the specification, through the same states"
  elif grep -q "Deadlock reached" "$LOG"; then
    k=$(($(grep -E '^/\\ l = [0-9]+' "$LOG" | tail -1 | sed -E 's/.* = //') + 1))
    what=$(step_text "$abs" "$k")
    diff=$(grep -E '^<<"MISMATCH", '"$k"',' "$LOG" | tail -1 | sed -E 's/.*, (\{.*\})>>$/\1/')
    if [ -n "$diff" ]; then
      echo "$f: REJECTED at step $k of $steps, $what: the specification can take this step, but reaches a state that differs from the recorded one in $diff"
    else
      echo "$f: REJECTED at step $k of $steps, $what: the specification cannot take this step from the state reached after step $((k - 1)) (an enabling condition of the action is false there)"
    fi
    [ $status = 2 ] || status=1
  elif grep -qE "Invariant [A-Za-z]+ is violated|Action property .* is violated" "$LOG"; then
    k=$(grep -E '^/\\ l = [0-9]+' "$LOG" | tail -1 | sed -E 's/.* = //')
    echo "$f: REJECTED: $(grep -E 'Invariant [A-Za-z]+ is violated|Action property .* is violated' "$LOG" | head -1 | sed 's/^Error: //') after step $k of $steps"
    [ $status = 2 ] || status=1
  elif grep -q "Finished computing initial states: 0 distinct states" "$LOG"; then
    echo "$f: REJECTED at the first line: the recorded initial state is not the Init of the specification (with the N and MaxReq of that line)"
    [ $status = 2 ] || status=1
  else
    echo "$f: ERROR: TLC gave no verdict; the end of its output ($LOG):"
    tail -8 "$LOG" | sed 's/^/    /'
    status=2
  fi
done
exit $status
