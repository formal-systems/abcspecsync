#!/usr/bin/env bash
# Run lamport_mutex.cpp under the sanitizers: AddressSanitizer with UndefinedBehaviorSanitizer
# (and LeakSanitizer where the platform has it), then ThreadSanitizer.
#
#   cpp/sanitize.sh             here, with the compilers of this machine (Linux)
#   cpp/sanitize.sh --docker    in a Linux container; needs Docker and, with the default image,
#                               network access to install g++ and clang in the container
#
# For every compiler and sanitizer the program is built with -Werror and run on six sizes
# (N = 1 to 5 processes) and once with LM_LOG=1.  A run passes if it exits with status 0 and the
# sanitizer printed no report.  Every run records its trace; when Java is available here, the
# traces are then validated against the specification (../spec/validate_trace.sh).
# The exit status is 0 if every run and every trace passes, 1 otherwise, 2 if nothing could run.
#
#   CXXS="g++ clang++"   the compilers to use (default: those of the two that are installed)
#   OUT=dir              where the traces and the reports go (default: $TMPDIR/abcspecsync-sanitize)
#   IMAGE=ubuntu:24.04   the image of --docker; g++ and clang are installed in the container
#                        when the image does not have them
#
# On macOS use --docker.  Without it only the address run is attempted, and only if a sanitized
# program starts at all; ThreadSanitizer is not started natively (TSAN_ON_MACOS=1 forces it).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
ROOT=$(cd "$HERE/.." && pwd)
OUT=${OUT:-${TMPDIR:-/tmp}/abcspecsync-sanitize}
MODE=${1:-native}
RUNS="3-2-1 3-2-2 5-3-2 1-2-1 2-2-3 4-2-5"     # N-ROUNDS-SEED
REPORT='WARNING: ThreadSanitizer|ERROR: AddressSanitizer|ERROR: LeakSanitizer|runtime error:'

validate() {   # TLC on every trace recorded in $OUT, when Java is here
  command -v java >/dev/null || { echo "== traces not validated: no Java here (spec/validate_trace.sh $OUT/*.ndjson)"; return 0; }
  local total=0 accepted=0 line
  echo "== validating the recorded traces against the specification"
  for t in "$OUT"/*.ndjson; do
    [ -f "$t" ] || continue
    total=$((total + 1))
    line=$("$ROOT/spec/validate_trace.sh" "$t")
    case $line in *": ACCEPTED"*) accepted=$((accepted + 1)) ;; *) echo "${line#"$OUT/"}" ;; esac
  done
  echo "traces: ACCEPTED $accepted of $total"
  [ "$accepted" = "$total" ]
}

if [ "$MODE" = --docker ]; then
  command -v docker >/dev/null || { echo "docker not found"; exit 2; }
  mkdir -p "$OUT"; rm -f "$OUT"/*.ndjson "$OUT"/*.err
  docker run --rm --memory 3g --cpus 4 --pids-limit 512 \
      -v "$ROOT":/src:ro -v "$OUT":/out -e CXXS="${CXXS:-}" "${IMAGE:-ubuntu:24.04}" \
      bash /src/cpp/sanitize.sh --in-container
  status=$?
  [ $status = 2 ] && exit 2
  validate || status=1
  echo "the traces, and the report of every failed run, are in $OUT"
  exit $status
fi

if [ "$MODE" = --in-container ]; then
  OUT=/out
  if ! command -v g++ >/dev/null && ! command -v clang++ >/dev/null; then
    command -v apt-get >/dev/null || { echo "the image has no C++ compiler and no apt-get: choose another IMAGE"; exit 2; }
    echo "== installing g++ and clang in the container"
    (apt-get update -qq && DEBIAN_FRONTEND=noninteractive apt-get install -y -qq --no-install-recommends \
        g++ clang libclang-rt-dev) > /tmp/apt.log 2>&1 || { echo "the installation failed:"; tail -5 /tmp/apt.log; exit 2; }
  fi
elif [ "$MODE" != native ]; then
  echo "usage: $0 [--docker]"; exit 2
fi

mkdir -p "$OUT"
[ "$MODE" = native ] && rm -f "$OUT"/*.ndjson "$OUT"/*.err
BUILD=$(mktemp -d "${TMPDIR:-/tmp}/abcspecsync-build.XXXXXX")
trap 'rm -rf "$BUILD"' EXIT
LIMIT=""; command -v timeout >/dev/null && LIMIT="timeout 180"

starts() {   # starts CXX SANITIZER: a trivial program built with it starts and ends normally
  echo 'int main() { return 0; }' > "$BUILD/probe.cpp"
  "$1" -fsanitize="$2" -o "$BUILD/probe" "$BUILD/probe.cpp" 2>/dev/null || return 1
  ( $LIMIT "$BUILD/probe" ) >/dev/null 2>&1     # in a subshell: a crash of the probe prints nothing
}

fail=0; ran=0
for cxx in ${CXXS:-g++ clang++}; do
  command -v "$cxx" >/dev/null || { echo "skip  $cxx: not installed"; continue; }
  echo "== $("$cxx" --version | head -1)"
  for san in address,undefined thread; do
    tag=$cxx-${san%%,*}
    if [ "$san" = thread ] && [ "$(uname -s)" = Darwin ] && [ "${TSAN_ON_MACOS:-0}" != 1 ]; then
      echo "skip  $tag: ThreadSanitizer is not started natively on macOS; use --docker"; continue
    fi
    if ! starts "$cxx" "$san" 2>/dev/null; then
      echo "skip  $tag: a program built with -fsanitize=$san does not start here; use --docker"; continue
    fi
    flags="-fsanitize=$san -fno-omit-frame-pointer -g -O1"
    [ "$san" = thread ] || flags="$flags -fno-sanitize-recover=undefined"
    if ! "$cxx" -std=c++17 -Wall -Wextra -Werror -pedantic $flags -o "$BUILD/lm-$tag" "$HERE/lamport_mutex.cpp" -lpthread 2> "$OUT/$tag-build.err"; then
      echo "FAIL  $tag: the build fails"; head -8 "$OUT/$tag-build.err"; fail=1; continue
    fi
    rm -f "$OUT/$tag-build.err"
    for run in $RUNS log; do
      if [ "$run" = log ]; then n=3; rounds=2; seed=4; log=1; else
        n=${run%%-*}; rest=${run#*-}; rounds=${rest%%-*}; seed=${rest#*-}; log=""
      fi
      name=$tag-n$n-r$rounds-s$seed
      env TSAN_OPTIONS=exitcode=66 UBSAN_OPTIONS=print_stacktrace=1 LM_TRACE="$OUT/$name.ndjson" ${log:+LM_LOG=1} \
        $LIMIT "$BUILD/lm-$tag" "$n" "$rounds" "$seed" > "$BUILD/run.out" 2> "$OUT/$name.err"
      rc=$?
      reports=$(grep -cE "$REPORT" "$OUT/$name.err")
      ran=$((ran + 1))
      if [ $rc = 0 ] && [ "$reports" = 0 ]; then
        echo "ok    $tag  N=$n ROUNDS=$rounds SEED=$seed${log:+ LM_LOG=1}  $(($(grep -c '' "$OUT/$name.ndjson") - 1)) steps, no report"
        rm -f "$OUT/$name.err"
      else
        echo "FAIL  $tag  N=$n ROUNDS=$rounds SEED=$seed${log:+ LM_LOG=1}  exit status $rc, $reports sanitizer report(s), kept in $name.err"
        head -30 "$OUT/$name.err"; fail=1
      fi
    done
  done
done

if [ $ran = 0 ]; then echo "RESULT: nothing could run here; use --docker"; exit 2; fi
if [ $fail = 0 ]; then echo "RESULT: $ran sanitized runs, no report, every run exits with status 0"
else echo "RESULT: FAIL (see above; the reports are the .err files of the output directory)"; fi
if [ "$MODE" = native ]; then validate || fail=1; else chmod -R a+rwX "$OUT" 2>/dev/null; fi
exit $fail
