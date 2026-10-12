#!/usr/bin/env bash
# stabcube.sh "n p s1,..,sp dmin" FLAGS DEPTH CUBE_TIMEOUT BUDGET WORKERS
#   Cube and conquer on one Turán-stability model (scripts/stab2.py with the redundant constraints
#   FLAGS). march_cu splits the formula DEPTH levels deep; Kissat solves each cube (the formula plus
#   the cube's literals as unit clauses) within CUBE_TIMEOUT seconds, WORKERS cubes at a time. A cube
#   that is not decided is split 6 levels further by march_cu (its children keep the parent's
#   literals) and queued again, until BUDGET seconds have passed.
#   Output in out/: result.txt ("UNSAT", "SAT" with the decoded graph, or "OPEN k"), cubes.txt (every
#   cube with its result), open.txt (cubes left), model files for a SAT cube.
set -uo pipefail
read -r n p sz dm <<< "$1"; FL=$2; D=$3; CT=$4; BUDGET=$5; W=$6
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
K="$ROOT/build/tools/kissat/build/kissat"; M="$ROOT/build/CnC/march_cu/march_cu"
O="$ROOT/out"; mkdir -p "$O"; T0=$(date +%s)
python3 "$ROOT/scripts/stab2.py" "$n" "$p" "$sz" "$O/m.cnf" "$dm" - "$FL"
"$M" "$O/m.cnf" -d "$D" -o "$O/q.icnf" > "$O/march0.log" 2>&1; mrc=$?
if grep -q 'UNSATISFIABLE' "$O/march0.log"; then
  echo "$1 UNSAT (march_cu at the root) $(( $(date +%s) - T0 ))s" | tee "$O/result.txt"; exit 0
fi
if [ "$mrc" != 0 ] || ! grep -q '^a' "$O/q.icnf" 2>/dev/null; then
  echo "$1 ERROR march_cu exit $mrc" | tee "$O/result.txt"; tail -5 "$O/march0.log"; exit 1
fi
grep '^a' "$O/q.icnf" | sed 's/^a //; s/ 0$//' > "$O/queue.txt"
grep -o 'number of cubes [0-9]*, including [0-9]* refuted leaves' "$O/march0.log" | tee "$O/march0.txt"
: > "$O/cubes.txt"
solve() {  # solve WORKER QUEUEFILE
  local j=$1 q=$2 cube rc s
  while IFS= read -r cube; do
    s=$(date +%s)
    timeout "$CT" "$K" -q --relaxed <(cat "$O/m.cnf"; for l in $cube; do echo "$l 0"; done) > "$O/sol_$j.txt"; rc=$?
    echo "$rc $(( $(date +%s) - s )) $cube" >> "$O/res_$j.txt"
    if [ "$rc" = 10 ]; then cp "$O/sol_$j.txt" "$O/SAT_model.txt"; echo "$cube" > "$O/SAT_cube.txt"; fi
  done < "$q"
}
round=0
while [ -s "$O/queue.txt" ]; do
  rm -f "$O"/res_*.txt "$O"/qs_*.txt
  awk -v w="$W" -v o="$O" '{ print > (o "/qs_" (NR - 1) % w ".txt") }' "$O/queue.txt"
  for j in $(seq 0 $(( W - 1 ))); do [ -f "$O/qs_$j.txt" ] && solve "$j" "$O/qs_$j.txt" & done
  wait
  cat "$O"/res_*.txt | sed "s/^/$round /" >> "$O/cubes.txt"
  if [ -f "$O/SAT_model.txt" ]; then break; fi
  awk '$1 != 20 { $1 = ""; $2 = ""; sub(/^ +/, ""); print }' "$O"/res_*.txt > "$O/open.txt"
  echo "round $round: $(wc -l < "$O/queue.txt") cubes, $(grep -c . "$O/open.txt") open, $(( $(date +%s) - T0 ))s"
  : > "$O/queue.txt"
  [ -s "$O/open.txt" ] || break
  [ $(( $(date +%s) - T0 )) -lt "$BUDGET" ] || break
  while IFS= read -r cube; do
    # march_cu reads only as many clauses as the header declares, so the header must count the units
    "$M" <(awk -v k="$(wc -w <<< "$cube")" 'NR == 1 { $4 += k } { print }' "$O/m.cnf"; for l in $cube; do echo "$l 0"; done) \
      -d 6 -o "$O/sub.icnf" > "$O/sub.log" 2>&1 || true
    if grep -q '^a' "$O/sub.icnf" 2>/dev/null; then
      grep '^a' "$O/sub.icnf" | sed 's/^a //; s/ 0$//' | sed "s/^/$cube /" >> "$O/queue.txt"
    elif grep -q 'UNSATISFIABLE' "$O/sub.log"; then echo "$round 20 0 $cube (march)" >> "$O/cubes.txt"
    else echo "$cube" >> "$O/stuck.txt"; fi
    rm -f "$O/sub.icnf"
  done < "$O/open.txt"
  : > "$O/open.txt"   # every open cube is now split (children queued), closed by march_cu, or stuck
  round=$(( round + 1 ))
done
total=$(grep -c . "$O/cubes.txt")
touch "$O/open.txt" "$O/stuck.txt"; cat "$O/stuck.txt" >> "$O/open.txt"
if [ -f "$O/SAT_model.txt" ]; then
  echo "$1 SAT (cube $(cat "$O/SAT_cube.txt"))" | tee "$O/result.txt"
  python3 "$ROOT/scripts/stab_decode.py" "$O/SAT_model.txt" "$O/m.cnf.map" | tee -a "$O/result.txt"
elif [ -s "$O/open.txt" ] || [ -s "$O/queue.txt" ]; then
  echo "$1 OPEN $(sort -u "$O/open.txt" | grep -c .) open, $(grep -c . "$O/queue.txt") queued, $total cubes tried $(( $(date +%s) - T0 ))s" | tee "$O/result.txt"
elif [ "$total" -gt 0 ]; then
  echo "$1 UNSAT $total cubes $(cat "$O/march0.txt") $(( $(date +%s) - T0 ))s" | tee "$O/result.txt"
else
  echo "$1 ERROR (no verdict)" | tee "$O/result.txt"
fi
rm -f "$O/m.cnf" "$O"/sol_*.txt
