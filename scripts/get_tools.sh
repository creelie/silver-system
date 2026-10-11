#!/usr/bin/env bash
# get_tools.sh -- build the pinned SAT solvers into build/tools.
#   Kissat https://github.com/arminbiere/kissat commit 8af8e56f174b778aef3aa45af9f739b2a5f492c2
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
T="$ROOT/build/tools"
mkdir -p "$T"
if [ ! -d "$T/kissat" ]; then
  git clone -q https://github.com/arminbiere/kissat.git "$T/kissat"
  git -C "$T/kissat" checkout -q 8af8e56f174b778aef3aa45af9f739b2a5f492c2
fi
(cd "$T/kissat" && [ -x build/kissat ] || { ./configure > /dev/null && make -j"$(nproc)" > /dev/null; })
"$T/kissat/build/kissat" --version
#   CaDiCaL https://github.com/arminbiere/cadical commit c60730422e758ef1cebe7aeddf2dda31c996bf04
if [ ! -d "$T/cadical" ]; then
  git clone -q https://github.com/arminbiere/cadical.git "$T/cadical"
  git -C "$T/cadical" checkout -q c60730422e758ef1cebe7aeddf2dda31c996bf04
fi
(cd "$T/cadical" && [ -x build/cadical ] || { ./configure > /dev/null && make -j"$(nproc)" > /dev/null; })
"$T/cadical/build/cadical" --version
