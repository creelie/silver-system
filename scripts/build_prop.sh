#!/usr/bin/env bash
# build_prop.sh -- build build/bipprop: CaDiCaL (pinned in get_tools.sh) with the planarity
# propagator prop/bipprop.cpp. Needs the Boost Graph Library headers (Ubuntu: libboost-dev).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
"$ROOT/scripts/get_tools.sh" > /dev/null
C="$ROOT/build/tools/cadical"
g++ -O2 -std=c++17 -I"$C/src" -o "$ROOT/build/bipprop" "$ROOT/prop/bipprop.cpp" "$C/build/libcadical.a"
echo "built $ROOT/build/bipprop"
