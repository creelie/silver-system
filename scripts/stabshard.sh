#!/usr/bin/env bash
# stabshard.sh "n p s1,..,sp dmin" FLAGS CUBES k/N TAG CUBE_TIMEOUT BUDGET WORKERS [SPLIT_DEPTH]
#   One shard of a Lean-checked cube-and-conquer refutation of Stab.encode n p sizes dmin FLAGS, for
#   cases too large for one job of scripts/stabcert.sh. The shard takes the cubes of the file CUBES
#   (or, for CUBES "march:D", march_cu's cubes D levels deep) numbered k mod N (from 0) and, until
#   BUDGET seconds have passed, with WORKERS solvers:
#   1. CaDiCaL refutes the formula plus each cube's literals as unit clauses and writes an LRAT proof,
#      which lrat-trim checks and trims;
#   2. a cube left open after CUBE_TIMEOUT seconds is split SPLIT_DEPTH (default 6) levels further by
#      march_cu (its children keep its literals) and queued again.
#   Meanwhile a checker gathers the refuted cubes into chunks of about CHUNK_MB of certificates and has
#   Lean check each chunk with the verified LRAT checker of its standard library: module
#   StabCert.<case>.<TAG>.K<j> lists the cubes, module C<j> proves "every cube of cubes<j> is refuted".
#   A checked chunk's certificates are then deleted (with the module's .olean.private, which holds them;
#   modules importing C<j> need only its public part), so the disk holds only the unchecked backlog.
#   Output in build/stabshard/<case>/<TAG>/: result.txt, leaves.txt (the cubes of the checked chunks,
#   "id cube"), open.txt (cubes to give a later run: open, or refuted but not checked in time),
#   chunks.txt, cubes.txt, lean.txt, lrat.sha256. scripts/stabfinal.sh proves the theorem for the whole
#   model once the leaves of all shards cover every assignment.
set -uo pipefail
read -r n p sz dm <<< "$1"; FL=$2; CUBES=$3; SHARD=$4; TAG=$5; CT=$6; BUDGET=$7; W=$8
case "$CUBES" in march:*) ;; *) CUBES=$(realpath "$CUBES") ;; esac
SPLIT=${9:-6}
K=${SHARD%/*}; NSH=${SHARD#*/}
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN="$ROOT/verification/lean"
B="$ROOT/build"
CADICAL="${CADICAL:-$B/tools/cadical/build/cadical}"
LRAT_TRIM="${LRAT_TRIM:-$B/tools/lrat-trim/lrat-trim}"
M="${MARCH:-$B/CnC/march_cu/march_cu}"
CHUNK=$(( ${CHUNK_MB:-300} * 1048576 ))
NS="T${n}_${p}_${sz//,/_}_d${dm}_${FL:-x}"
O="$B/stabshard/$NS/$TAG"; LR="$O/lrat"; mkdir -p "$O" "$LR"
T0=$(date +%s); DEADLINE=$(( T0 + BUDGET ))
cd "$LEAN"
DUMP="$LEAN/.lake/build/bin/stab-dump"
[ -x "$DUMP" ] || lake build stab-dump > /dev/null
lake build BiplanarF.Stab > /dev/null
"$DUMP" "$n" "$p" "$sz" "$dm" "${FL:--}" "$O/m.cnf" > /dev/null
withunits() { awk -v k="$(wc -w <<< "$1")" 'NR == 1 { $4 += k } { print }' "$O/m.cnf"; for l in $1; do echo "$l 0"; done; }
if [ "${CUBES#march:}" != "$CUBES" ]; then   # march:D: march_cu's cubes D levels deep (the same in every shard)
  "$M" "$O/m.cnf" -d "${CUBES#march:}" -o "$O/q.icnf" > "$O/march0.log" 2>&1
  if grep -q 'UNSATISFIABLE' "$O/march0.log" || ! grep -q '^a [^0]' "$O/q.icnf" 2>/dev/null; then
    printf '1\n-1\n' > "$O/all.txt"   # refuted at the root, or no split: the two cubes x1 and -x1
  else
    grep '^a' "$O/q.icnf" | sed -E 's/^a//; s/(^| )0$//; s/^ //' > "$O/all.txt"
  fi
  rm -f "$O/q.icnf"
else cp "$CUBES" "$O/all.txt"; fi
awk -v k="$K" -v m="$NSH" 'NF && (NR - 1) % m == k' "$O/all.txt" > "$O/queue.txt"
echo "shard $SHARD of $CUBES: $(wc -l < "$O/queue.txt") cubes"
for f in leaves refuted stuck cubes chunks lean lrat.sha256; do : > "$O/$f.txt"; done
mv "$O/lrat.sha256.txt" "$O/lrat.sha256"; rm -f "$O/solved.flag" "$O/lean_error"
NEXT=$(( K * 10000000 ))
solve() {  # solve WORKER QUEUEFILE: lines "id cube"; a cube not started before the deadline stays open
  local j=$1 q=$2 id cube rc s left
  while read -r id cube; do
    s=$(date +%s); left=$(( DEADLINE - s ))
    if [ "$left" -le 0 ] || [ -e "$O/lean_error" ]; then echo "125 0 $id $cube" >> "$O/res_$j.txt"; continue; fi
    [ "$left" -lt "$CT" ] || left=$CT
    withunits "$cube" > "$O/w_$j.cnf"
    timeout "$left" "$CADICAL" -q --lrat=true --binary=true "$O/w_$j.cnf" "$O/w_$j.raw" > "$O/sol_$j.txt" 2>&1; rc=$?
    if [ "$rc" = 10 ]; then   # a solution: keep it and stop the shard
      cp "$O/sol_$j.txt" "$O/SAT_model.txt"; echo "$cube" > "$O/SAT_cube.txt"; echo "solution found" > "$O/lean_error"
    fi
    if [ "$rc" = 20 ]; then
      "$LRAT_TRIM" -q -a "$O/w_$j.cnf" "$O/w_$j.raw" "$LR/c$id.lrat" > /dev/null 2>&1; rc=$?
      if [ "$rc" = 20 ]; then echo "$id $cube" >> "$O/refuted.txt"; else rc=99; fi
    fi
    echo "$rc $(( $(date +%s) - s )) $id $cube" >> "$O/res_$j.txt"
    rm -f "$O/w_$j.cnf" "$O/w_$j.raw" "$O/sol_$j.txt"
  done < "$q"
}
chunk() {  # chunk J FILE: check the refuted cubes of FILE in Lean as chunk J, then delete their certificates
  local j=$1 f=$2 mod="StabCert.$NS.$TAG.C$1" out rc a
  python3 "$ROOT/scripts/stabshard_lean.py" "$NS" "$TAG" "$j" "$n" "$p" "$sz" "$dm" "$FL" "$f" "$LR" "$LEAN/StabCert" > /dev/null
  out=$(lake build "$mod" 2>&1); rc=$?
  echo "$out" >> "$O/lean.txt"
  if [ "$rc" != 0 ] || grep -q "error" <<< "$out"; then echo "chunk $j: lake exit $rc" > "$O/lean_error"; return 1; fi
  a=$(tr '\n' ' ' <<< "$out" | sed -n "s/.*'StabCert\.$NS\.$TAG\.chunk$j' depends on axioms: \[\([^]]*\)\].*/\1/p")
  [ -n "$a" ] || { echo "chunk $j: no axiom report" > "$O/lean_error"; return 1; }
  for a in $(tr ',' ' ' <<< "$a"); do
    case "$a" in
      propext|Classical.choice|Quot.sound|*._native.native_decide.ax_*) ;;
      *) echo "chunk $j: unexpected axiom $a" > "$O/lean_error"; return 1 ;;
    esac
  done
  awk '{ print "c" $1 ".lrat" }' "$f" | (cd "$LR" && xargs sha256sum) >> "$O/lrat.sha256"
  awk -v d="$LR" '{ print d "/c" $1 ".lrat" }' "$f" | xargs rm -f
  rm -f "$LEAN/.lake/build/lib/lean/StabCert/$NS/$TAG/C$j.olean.private"*
  cat "$f" >> "$O/leaves.txt"
  echo "$j $(wc -l < "$f") $(( $(date +%s) - T0 ))s" >> "$O/chunks.txt"
}
checker() {  # chunk the refuted cubes as their certificates accumulate, until solving has ended
  local j=0 done_n=0 tot bytes
  while [ ! -e "$O/lean_error" ]; do
    tot=$(wc -l < "$O/refuted.txt")
    if [ "$tot" -gt "$done_n" ]; then
      sed -n "$(( done_n + 1 )),${tot}p" "$O/refuted.txt" > "$O/pend.txt"
      bytes=$(awk -v d="$LR" '{ print d "/c" $1 ".lrat" }' "$O/pend.txt" | xargs stat -c %s | awk '{ s += $1 } END { print s + 0 }')
      if [ "$bytes" -ge "$CHUNK" ] || [ -e "$O/solved.flag" ]; then
        chunk "$j" "$O/pend.txt" || return 1
        done_n=$tot; j=$(( j + 1 )); continue
      fi
    elif [ -e "$O/solved.flag" ]; then return 0
    fi
    sleep 20
  done
}
checker & CHK=$!
round=0
while [ -s "$O/queue.txt" ]; do
  rm -f "$O"/res_*.txt "$O"/qs_*.txt
  awk -v start="$NEXT" '{ print start + NR - 1, $0 }' "$O/queue.txt" > "$O/qid.txt"
  NEXT=$(( NEXT + $(wc -l < "$O/queue.txt") ))
  awk -v w="$W" -v o="$O" '{ print > (o "/qs_" (NR - 1) % w ".txt") }' "$O/qid.txt"
  PIDS=
  for j in $(seq 0 $(( W - 1 ))); do
    if [ -f "$O/qs_$j.txt" ]; then solve "$j" "$O/qs_$j.txt" & PIDS="$PIDS $!"; fi
  done
  [ -z "$PIDS" ] || wait $PIDS
  cat "$O"/res_*.txt | sed "s/^/$round /" >> "$O/cubes.txt"
  if grep -q '^99 ' "$O"/res_*.txt; then echo "lrat-trim rejected a proof" > "$O/lean_error"; break; fi
  awk '$1 != 20 { $1 = ""; $2 = ""; $3 = ""; sub(/^ +/, ""); print }' "$O"/res_*.txt > "$O/open.txt"
  echo "round $round: $(wc -l < "$O/queue.txt") cubes, $(grep -c . "$O/open.txt") open, $(( $(date +%s) - T0 ))s"
  : > "$O/queue.txt"
  [ -s "$O/open.txt" ] || break
  [ "$(date +%s)" -lt "$DEADLINE" ] && [ ! -e "$O/lean_error" ] || break
  : > "$O/open2.txt"
  while IFS= read -r cube; do
    if [ "$(date +%s)" -ge "$DEADLINE" ]; then echo "$cube" >> "$O/open2.txt"; continue; fi
    timeout 1800 "$M" <(withunits "$cube") -d "$SPLIT" -o "$O/sub.icnf" > "$O/sub.log" 2>&1 || true
    # (march_cu writes the single empty cube "a 0" when it refutes the cube itself: left open)
    if grep -q '^a [^0]' "$O/sub.icnf" 2>/dev/null; then
      grep '^a' "$O/sub.icnf" | sed -E 's/^a//; s/(^| )0$//; s/^ //' | sed "s/^/$cube /" >> "$O/queue.txt"
    else echo "$cube" >> "$O/stuck.txt"; fi
    rm -f "$O/sub.icnf"
  done < "$O/open.txt"
  mv "$O/open2.txt" "$O/open.txt"
  round=$(( round + 1 ))
done
touch "$O/solved.flag"; wait "$CHK"
T_SOLVE=$(( $(date +%s) - T0 ))
# open: never refuted, or refuted but not in a checked chunk
cat "$O/stuck.txt" "$O/queue.txt" >> "$O/open.txt"; : > "$O/queue.txt"
awk 'NR == FNR { ok[$1] = 1; next } !($1 in ok) { $1 = ""; sub(/^ +/, ""); print }' "$O/leaves.txt" "$O/refuted.txt" >> "$O/open.txt"
NL=$(grep -c . "$O/leaves.txt"); NO=$(grep -c . "$O/open.txt"); NC=$(grep -c . "$O/chunks.txt")
if [ -f "$O/SAT_model.txt" ]; then
  echo "$1 $SHARD $TAG SAT (cube $(cat "$O/SAT_cube.txt"))" | tee "$O/result.txt"
  python3 "$ROOT/scripts/stab2.py" "$n" "$p" "$sz" "$O/py.cnf" "$dm" - "$FL" > /dev/null 2>&1 &&
    python3 "$ROOT/scripts/stab_decode.py" "$O/SAT_model.txt" "$O/py.cnf.map" | tee -a "$O/result.txt"
  exit 0
fi
if [ -e "$O/lean_error" ]; then
  echo "$1 $SHARD $TAG ERROR $(cat "$O/lean_error") (leaves=$NL open=$NO)" | tee "$O/result.txt"; exit 1
fi
H=$( (cat "$O/leaves.txt" "$O/lrat.sha256") | sha256sum | cut -d' ' -f1)
echo "$1 $SHARD $TAG CHECKED leaves=$NL open=$NO chunks=$NC time=${T_SOLVE}s sha256=$H" | tee "$O/result.txt"
