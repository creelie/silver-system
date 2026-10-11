#!/usr/bin/env bash
# get_tools.sh -- build the pinned SAT solver into build/tools.
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
