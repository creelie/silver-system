#!/usr/bin/env bash
# race.sh CNF TIMEOUT : run four solver configurations on CNF in parallel; the first definite
# answer (10 = satisfiable, 20 = unsatisfiable) stops the others. Prints "CNF -> rc cfg i seconds".
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
K="$ROOT/build/tools/kissat/build/kissat"; C="$ROOT/build/tools/cadical/build/cadical"
f=$1; TO=$2
pids=(); cfgs=("$K -q" "$K -q --unsat" "$K -q --sat" "$C -q")
for i in 0 1 2 3; do
  ( timeout "$TO" ${cfgs[$i]} "$f" > "$f.$i.sol"; echo $? > "$f.$i.rc" ) &
  pids+=($!)
done
s=$(date +%s); res=""
while [ -z "$res" ]; do
  sleep 20
  for i in 0 1 2 3; do
    [ -f "$f.$i.rc" ] || continue
    r=$(cat "$f.$i.rc")
    if [ "$r" = 10 ] || [ "$r" = 20 ]; then res="$r cfg $i"; fi
  done
  all=1; for i in 0 1 2 3; do [ -f "$f.$i.rc" ] || all=0; done
  [ $all = 1 ] && [ -z "$res" ] && res="timeout"
done
for p in "${pids[@]}"; do pkill -P "$p" 2>/dev/null; kill "$p" 2>/dev/null; done
echo "$(basename "$f") -> $res $(( $(date +%s) - s ))s"
