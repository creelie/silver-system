#!/bin/bash
# build_sms.sh DIR: build SAT modulo symmetries (markirch/sat-modulo-symmetries at a fixed commit) with our patch
# uc.patch: a --thickness2 switch for the directed thickness-two propagator, and --underlying-clique k, a propagator
# that forbids small non-biplanar graphs in the union graph (k = 8: K9 and K10 minus a triangle; k = 11 adds
# K11 minus (P3 + 2K2), K11 minus a bowtie and K11 minus two disjoint triangles; each checked by exhaustion over all triangulations on 9-11 vertices).
set -e
D=${1:-build/sms}; here=$(cd "$(dirname "$0")" && pwd)
git clone -q https://github.com/markirch/sat-modulo-symmetries.git "$D"
cd "$D"; git checkout -q 63958bd
git clone -q https://github.com/markirch/cadical_sms.git cadical_sms
git -C cadical_sms checkout -q b023aaf
(cd cadical_sms && CXXFLAGS=-fPIC ./configure > /dev/null && make -j4 > /dev/null)
git apply "$here/uc.patch"
cmake -S . -B build -DCMAKE_BUILD_TYPE=Release > /dev/null && make -C build -j4 smsg > /dev/null
ls -la build/src/smsg
