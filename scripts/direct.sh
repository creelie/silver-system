#!/usr/bin/env bash
# direct.sh LINE TIMEOUT : encode one line of data/direct.txt ("name N options...") and run four
# solver configurations on it in parallel; the first definite answer stops the others.
set -u
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
K="$ROOT/build/tools/kissat/build/kissat"; C="$ROOT/build/tools/cadical/build/cadical"
read -r name n opts < <(sed -n "${1}p" "$ROOT/data/direct.txt")
TO=$2
mkdir -p "$ROOT/out"; cd "$ROOT/out"
python3 "$ROOT/encode/direct.py" "$n" "$name.cnf" $opts
pids=(); cfgs=("$K -q" "$K -q --sat" "$K -q --seed=1" "$C -q --sat")
for i in 0 1 2 3; do
  ( timeout "$TO" ${cfgs[$i]} "$name.cnf" > "$name.$i.sol"; echo $? > "$name.$i.rc" ) &
  pids+=($!)
done
s=$(date +%s); res=""
while [ -z "$res" ]; do
  sleep 20
  for i in 0 1 2 3; do
    [ -f "$name.$i.rc" ] || continue
    r=$(cat "$name.$i.rc")
    if [ "$r" = 10 ] || [ "$r" = 20 ]; then res="$r cfg $i"; fi
  done
  all=1; for i in 0 1 2 3; do [ -f "$name.$i.rc" ] || all=0; done
  [ $all = 1 ] && [ -z "$res" ] && res="timeout"
done
for p in "${pids[@]}"; do pkill -P "$p" 2>/dev/null; kill "$p" 2>/dev/null; done
echo "$name n=$n $opts -> $res $(( $(date +%s) - s ))s" | tee -a results.txt
case "$res" in 10*) i=${res#10 cfg }; python3 "$ROOT/scripts/decode_direct.py" "$name.cnf" "$name.$i.sol" "$name.g6" | tee -a results.txt ;; esac
rm -f "$name.cnf"
