#!/usr/bin/env bash
# Build lamport_mutex.  Usage: [CXX=c++] [CXXSTD=c++17] ./build.sh
# Needs only a C++17 compiler and the standard library.
set -euo pipefail
cd "$(dirname "$0")"
"${CXX:-c++}" -std="${CXXSTD:-c++17}" -Wall -Wextra -Werror -pedantic -O2 \
    -o lamport_mutex lamport_mutex.cpp -lpthread
echo "built $PWD/lamport_mutex"
