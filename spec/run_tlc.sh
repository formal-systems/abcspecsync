#!/usr/bin/env bash
# Model-check LamportMutex.tla with TLC on one of its three models.
#
#   ./run_tlc.sh              the models that finish in seconds: safety, then live2
#   ./run_tlc.sh safety       N = 2, MaxReq = 2, Spec:     the invariants and GrantOrder
#   ./run_tlc.sh live2        N = 2, MaxReq = 2, FairSpec: the same plus EveryRequestGranted
#   ./run_tlc.sh live         N = 3, MaxReq = 1, FairSpec: 7.1 million states, 26 minutes with
#                             WORKERS=8 JAVA_OPTS=-Xmx6g
#
# Needs Java 11 or later.  TLC is ../tools/tla2tools.jar; set TLA2TOOLS to use another copy.
# WORKERS sets the number of TLC worker threads (default 4); JAVA_OPTS is passed to java.
set -euo pipefail
cd "$(dirname "$0")"
JAR="${TLA2TOOLS:-$PWD/../tools/tla2tools.jar}"
[ -f "$JAR" ] || { echo "tla2tools.jar not found at $JAR (set TLA2TOOLS)"; exit 2; }
META="${TMPDIR:-/tmp}/abcspecsync-tlc"     # TLC's working files, kept out of this directory
status=0
for model in ${@:-safety live2}; do
  [ -f "MC_$model.cfg" ] || { echo "no model MC_$model.cfg (safety, live2, live)"; exit 2; }
  echo "== TLC, model $model (MC_$model.cfg)"
  mkdir -p "$META/$model"
  java -XX:+UseParallelGC ${JAVA_OPTS:-} -cp "$JAR" tlc2.TLC -workers "${WORKERS:-4}" -noGenerateSpecTE -metadir "$META/$model" \
       -config "MC_$model.cfg" LamportMutex || status=$?
done
exit $status
