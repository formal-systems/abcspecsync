#!/usr/bin/env bash
# The whole example in one command: model-check the specification, build the program, record
# runs, and let TLC decide whether the specification allows each recorded run.
#
#   ./run_all.sh                         N=3 ROUNDS=2 SEEDS="1 2 3"   (about one minute)
#   N=5 ROUNDS=3 SEEDS="2 7" ./run_all.sh
#
# 1. TLC on the models safety and live2 (the large model: spec/run_tlc.sh live)
# 2. build cpp/lamport_mutex
# 3. for each seed: run the program with LM_TRACE set, then spec/validate_trace.sh on the trace
# 4. negative control: copies of the first trace with one edit each must all be REJECTED
# Needs Java 11+, a C++17 compiler and Python 3.9+ (step 4 only).  Exit status 0 if all agree.
set -uo pipefail
cd "$(dirname "$0")"
N=${N:-3}; ROUNDS=${ROUNDS:-2}; SEEDS=${SEEDS:-1 2 3}
fail=0
mkdir -p traces

echo "== 1. model checking the specification"
for m in safety live2; do
  out=$(spec/run_tlc.sh "$m" 2>&1)
  if echo "$out" | grep -q "Model checking completed. No error has been found."; then
    echo "model $m: no error, $(echo "$out" | grep -E 'distinct states found' | tail -1 | sed -E 's/.*generated, ([0-9,]+ distinct states) found.*/\1/'), $(echo "$out" | grep -E 'depth of the complete' | sed -E 's/.* is ([0-9]+)\./depth \1/')"
  else
    echo "model $m: ERROR"; echo "$out" | grep -E "^Error" | head -3; fail=1
  fi
done

echo "== 2. build"
cpp/build.sh || exit 1

echo "== 3. record runs ($N processes, $ROUNDS rounds) and validate each trace against the specification"
first=""
for s in $SEEDS; do
  f=traces/n$N-r$ROUNDS-s$s.ndjson
  rm -f "$f"
  LM_TRACE=$f cpp/lamport_mutex "$N" "$ROUNDS" "$s" || fail=1
  spec/validate_trace.sh "$f" || fail=1
  [ -n "$first" ] || first=$f
done

echo "== 4. negative control: copies of $first with one edit each must be REJECTED"
tdir=$(mktemp -d)
total=0; rejected=0
for c in $(python3 tools/tamper_trace.py "$first" "$tdir"); do
  total=$((total + 1))
  v=$(spec/validate_trace.sh "$tdir/$c")
  if [[ $v == *": REJECTED"* ]]; then rejected=$((rejected + 1)); else echo "NOT rejected: ${v#"$tdir/"}"; fail=1; fi
done
rm -rf "$tdir"
echo "tampered copies: REJECTED $rejected of $total"

if [ $fail = 0 ]; then
  echo "RESULT: the models hold, every recorded run is ACCEPTED by the specification, every tampered copy is REJECTED"
else
  echo "RESULT: FAIL (see above)"
fi
exit $fail
