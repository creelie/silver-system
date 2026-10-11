#!/usr/bin/env bash
# shard.sh QUEUE SHARD NSHARDS TIMEOUT PAR
# Tests the lines "w|edges" of QUEUE whose line number is SHARD mod NSHARDS: writes the CNF of
# "F[w] is biplanar" with encode/DumpF.lean and runs Kissat on it with a time limit, PAR at a time.
# Results go to out/results.txt as "w|edges tag=... rc=... seconds" (rc 10 = biplanar drawing found,
# 20 = not biplanar, 124 = time limit); for rc 10 the solution and the CNF are kept in out/.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
QUEUE=$1; SHARD=$2; N=$3; export TO=$4; PAR=${5:-4}
export ROOT KISSAT="${KISSAT:-$ROOT/build/tools/kissat/build/kissat}"
mkdir -p "$ROOT/out"
awk -v s="$SHARD" -v n="$N" '(NR - 1) % n == s' "$QUEUE" > "$ROOT/out/mine.txt"
one() {
  line="$1"; w=${line%%|*}; fe=${line#*|}
  tag=$(printf '%s' "$line" | md5sum | cut -c1-10)
  cnf=$(mktemp /tmp/f_XXXXXX.cnf)
  (cd "$ROOT" && lean --run encode/DumpF.lean "$w" "$fe" "$cnf" > /dev/null 2>&1)
  s=$(date +%s)
  timeout "$TO" "$KISSAT" -q "$cnf" > "$ROOT/out/$tag.sol" 2>&1; rc=$?
  echo "$line tag=$tag rc=$rc $(( $(date +%s) - s ))s" >> "$ROOT/out/results.txt"
  if [ "$rc" = 10 ]; then cp "$cnf" "$ROOT/out/$tag.cnf"; else rm -f "$ROOT/out/$tag.sol"; fi
  rm -f "$cnf"
}
export -f one
xargs -P "$PAR" -d '\n' -I{} bash -c 'one "$1"' _ {} < "$ROOT/out/mine.txt"
grep -c . "$ROOT/out/results.txt"
