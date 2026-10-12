#!/usr/bin/env bash
# stabcert.sh "n p s1,..,sp dmin" FLAGS DEPTH CUBE_TIMEOUT BUDGET WORKERS [CUBES]
#   Refute one Turán-stability model by cube and conquer and check the refutation in Lean.
#   1. the Lean encoder (verification/lean, Stab.encode) writes the formula F, the same file as
#      scripts/stab2.py n p sizes F dmin - FLAGS;
#   2. march_cu splits F into cubes DEPTH levels deep (the cubes include its refuted leaves), or the
#      cubes are read from the file CUBES (one per line, for instance the refuted cubes of a run of
#      scripts/stabcube.sh; nothing is assumed about them, since step 4 checks that they cover);
#   3. CaDiCaL refutes F plus each cube's literals as unit clauses and writes an LRAT proof, which
#      lrat-trim checks and trims; a cube left open after CUBE_TIMEOUT seconds is split 6 levels
#      further by march_cu (children keep the parent's literals) and queued again, until BUDGET;
#   4. CaDiCaL and lrat-trim also refute the clauses "not all literals of cube c", one per final cube,
#      which says the cubes cover every assignment;
#   5. Lean checks every certificate with the verified LRAT checker of its standard library and
#      proves (Stab.encode n p sizes dmin FLAGS).Unsat from Stab.unsat_of_cubes.
#   Output in build/stabcert/TAG/: result.txt and the logs; Lean sources in verification/lean/StabCert/.
#   Needs CADICAL, LRAT_TRIM and MARCH (defaults under build/) and elan.
set -uo pipefail
read -r n p sz dm <<< "$1"; FL=$2; D=$3; CT=$4; BUDGET=$5; W=$6; CUBES=${7:+$(realpath "$7")}
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN="$ROOT/verification/lean"
B="$ROOT/build"
CADICAL="${CADICAL:-$B/tools/cadical/build/cadical}"
LRAT_TRIM="${LRAT_TRIM:-$B/tools/lrat-trim/lrat-trim}"
M="${MARCH:-$B/CnC/march_cu/march_cu}"
NS="T${n}_${p}_${sz//,/_}_d${dm}_${FL:-x}"
O="$B/stabcert/$NS"; LR="$O/lrat"; mkdir -p "$O" "$LR"
T0=$(date +%s)
cd "$LEAN"
DUMP="$LEAN/.lake/build/bin/stab-dump"
[ -x "$DUMP" ] || lake build stab-dump > /dev/null
"$DUMP" "$n" "$p" "$sz" "$dm" "${FL:--}" "$O/m.cnf" > /dev/null
NCL=$(head -n 1 "$O/m.cnf" | cut -d' ' -f4)
# withunits CUBE: the formula with the cube's literals appended as unit clauses (header updated)
withunits() { awk -v k="$(wc -w <<< "$1")" 'NR == 1 { $4 += k } { print }' "$O/m.cnf"; for l in $1; do echo "$l 0"; done; }
if [ -n "$CUBES" ]; then
  grep -v '^ *$' "$CUBES" > "$O/queue.txt"
  [ -s "$O/queue.txt" ] || { echo "$1 ERROR no cubes in $CUBES" | tee "$O/result.txt"; exit 1; }
else
  "$M" "$O/m.cnf" -d "$D" -o "$O/q.icnf" > "$O/march0.log" 2>&1; mrc=$?
  if grep -q 'UNSATISFIABLE' "$O/march0.log"; then
    printf '1\n-1\n' > "$O/queue.txt"   # refuted at the root: split on variable 1 (no empty cube)
  elif [ "$mrc" != 0 ] || ! grep -q '^a' "$O/q.icnf" 2>/dev/null; then
    echo "$1 ERROR march_cu exit $mrc" | tee "$O/result.txt"; exit 1
  else
    grep '^a' "$O/q.icnf" | sed -E 's/^a//; s/(^| )0$//; s/^ //' > "$O/queue.txt"
    grep -q . "$O/queue.txt" || printf '1\n-1\n' > "$O/queue.txt"   # the single empty cube: likewise
  fi
fi
: > "$O/leaves.txt"; : > "$O/stuck.txt"; NEXT=0
solve() {  # solve WORKER QUEUEFILE: lines "id cube"
  local j=$1 q=$2 id cube rc s
  while read -r id cube; do
    s=$(date +%s)
    withunits "$cube" > "$O/w_$j.cnf"
    timeout "$CT" "$CADICAL" -q --lrat=true --binary=true "$O/w_$j.cnf" "$O/w_$j.raw" > /dev/null 2>&1; rc=$?
    if [ "$rc" = 20 ]; then
      "$LRAT_TRIM" -q -a "$O/w_$j.cnf" "$O/w_$j.raw" "$LR/c$id.lrat" > /dev/null 2>&1; rc=$?
      [ "$rc" = 20 ] && rc=20 || rc=99
    fi
    echo "$rc $(( $(date +%s) - s )) $id $cube" >> "$O/res_$j.txt"
    rm -f "$O/w_$j.cnf" "$O/w_$j.raw"
  done < "$q"
}
round=0
while [ -s "$O/queue.txt" ]; do   # (a root refutation is the single empty cube)
  rm -f "$O"/res_*.txt "$O"/qs_*.txt
  awk -v start="$NEXT" '{ print start + NR - 1, $0 }' "$O/queue.txt" > "$O/qid.txt"
  NEXT=$(( NEXT + $(wc -l < "$O/queue.txt") ))
  awk -v w="$W" -v o="$O" '{ print > (o "/qs_" (NR - 1) % w ".txt") }' "$O/qid.txt"
  for j in $(seq 0 $(( W - 1 ))); do [ -f "$O/qs_$j.txt" ] && solve "$j" "$O/qs_$j.txt" & done
  wait
  cat "$O"/res_*.txt | sed "s/^/$round /" >> "$O/cubes.txt"
  awk '$1 == 20 { $1 = ""; $2 = ""; sub(/^ +/, ""); print }' "$O"/res_*.txt >> "$O/leaves.txt"
  if grep -q '^99 ' "$O"/res_*.txt; then echo "$1 ERROR lrat-trim rejected a proof" | tee "$O/result.txt"; exit 1; fi
  awk '$1 != 20 { $1 = ""; $2 = ""; $3 = ""; sub(/^ +/, ""); print }' "$O"/res_*.txt > "$O/open.txt"
  echo "round $round: $(wc -l < "$O/queue.txt") cubes, $(grep -c . "$O/open.txt") open, $(( $(date +%s) - T0 ))s"
  : > "$O/queue.txt"
  [ -s "$O/open.txt" ] || break
  [ $(( $(date +%s) - T0 )) -lt "$BUDGET" ] || break
  while IFS= read -r cube; do
    "$M" <(withunits "$cube") -d 6 -o "$O/sub.icnf" > "$O/sub.log" 2>&1 || true
    # (march_cu writes the single empty cube "a 0" when it refutes the cube itself: left open)
    if grep -q '^a [^0]' "$O/sub.icnf" 2>/dev/null; then
      grep '^a' "$O/sub.icnf" | sed -E 's/^a//; s/(^| )0$//; s/^ //' | sed "s/^/$cube /" >> "$O/queue.txt"
    else echo "$cube" >> "$O/stuck.txt"; fi
    rm -f "$O/sub.icnf"
  done < "$O/open.txt"
  : > "$O/open.txt"
  round=$(( round + 1 ))
done
cat "$O/stuck.txt" >> "$O/open.txt"
if [ -s "$O/open.txt" ] || [ -s "$O/queue.txt" ]; then
  echo "$1 OPEN $(grep -c . "$O/open.txt") open, $(grep -c . "$O/queue.txt") queued, $(wc -l < "$O/leaves.txt") refuted $(( $(date +%s) - T0 ))s" | tee "$O/result.txt"
  exit 0
fi
# coverage: the negated cubes are unsatisfiable
NL=$(wc -l < "$O/leaves.txt")
MAXV=$(head -n 1 "$O/m.cnf" | cut -d' ' -f3)
{ echo "p cnf $MAXV $NL"; awk '{ s = ""; for (i = 2; i <= NF; i++) s = s (-$i) " "; print s "0" }' "$O/leaves.txt"; } > "$O/cover.cnf"
"$CADICAL" -q --lrat=true --binary=true "$O/cover.cnf" "$O/cover.raw" > /dev/null 2>&1; rc=$?
[ "$rc" = 20 ] || { echo "$1 ERROR the cubes do not cover (CaDiCaL exit $rc)" | tee "$O/result.txt"; exit 1; }
"$LRAT_TRIM" -q -a "$O/cover.cnf" "$O/cover.raw" "$LR/cover.lrat" > /dev/null 2>&1; rc=$?   # 20: verified
[ "$rc" = 20 ] || { echo "$1 ERROR cover proof (lrat-trim exit $rc)" | tee "$O/result.txt"; exit 1; }
T_SOLVE=$(( $(date +%s) - T0 ))
# Lean sources: chunks of at most CHUNK_MB of certificates, then the final theorem
python3 "$ROOT/scripts/stabcert_lean.py" "$NS" "$n" "$p" "$sz" "$dm" "$FL" "$O/leaves.txt" "$LR" "$LEAN/StabCert" "${CHUNK_MB:-300}"
t0=$(date +%s)
lake build "StabCert.$NS.Final" > "$O/lean.txt" 2>&1; lrc=$?
T_LEAN=$(( $(date +%s) - t0 ))
if [ "$lrc" != 0 ] || grep -q "error" "$O/lean.txt"; then tail -30 "$O/lean.txt"; echo "$1 ERROR Lean rejected the certificates" | tee "$O/result.txt"; exit 1; fi
AX=$(tr '\n' ' ' < "$O/lean.txt" | sed -n "s/.*'StabCert.$NS.unsat' depends on axioms: \[\([^]]*\)\].*/\1/p")
[ -n "$AX" ] || { echo "$1 ERROR no axiom report" | tee "$O/result.txt"; exit 1; }
for a in $(echo "$AX" | tr ',' ' '); do
  case "$a" in
    propext|Classical.choice|Quot.sound|*._native.native_decide.ax_*) ;;
    *) echo "$1 ERROR unexpected axiom $a" | tee "$O/result.txt"; exit 1 ;;
  esac
done
H=$( (cat "$O/leaves.txt"; sha256sum "$LR"/*.lrat | cut -d' ' -f1) | sha256sum | cut -d' ' -f1)
echo "$1 CERTIFIED $NS cubes=$NL clauses=$NCL solve=${T_SOLVE}s lean=${T_LEAN}s lrat_mb=$(du -sm "$LR" | cut -f1) sha256=$H" | tee "$O/result.txt"
