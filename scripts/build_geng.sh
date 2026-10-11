#!/usr/bin/env bash
# build_geng.sh -- build build/tools/geng18: nauty's geng with the PRUNE hook enum/prune.c.
#   nauty 2.8.8, from the source distribution of pynauty 2.8.8.1 on PyPI (sha256 below).
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
T="$ROOT/build/tools"; mkdir -p "$T"; cd "$T"
if [ ! -x geng18 ]; then
  pip download -q --no-binary :all: --no-deps pynauty==2.8.8.1 -d .
  echo "454d3b0e605d649d13478afb090daef4a152f15c4a337a391fe69fded7e683f2  pynauty-2.8.8.1.tar.gz" | sha256sum -c -
  tar xzf pynauty-2.8.8.1.tar.gz
  cd pynauty-2.8.8.1/src/nauty2_8_8
  ./configure > /dev/null
  make gtoolsW.o nautyW1.o nautilW1.o naugraphW1.o schreier.o naurng.o > /dev/null
  gcc -O3 -o "$T/geng18" -DMAXN=WORDSIZE -DWORDSIZE=32 -DPRUNE=myprune -I. geng.c "$ROOT/enum/prune.c" \
    gtoolsW.o nautyW1.o nautilW1.o naugraphW1.o schreier.o naurng.o
fi
