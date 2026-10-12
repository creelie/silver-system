#!/usr/bin/env bash
# stabfinal.sh "n p s1,..,sp dmin" FLAGS SHARDDIR...
#   Combine the shards of a Lean-checked cube-and-conquer refutation (scripts/stabshard.sh) into the
#   theorem StabCert.<case>.unsat: (Stab.encode n p sizes dmin FLAGS).Unsat. Each SHARDDIR holds one
#   shard's leaves.txt, its Lean sources in lean/<TAG>/ and its compiled modules in olean/<TAG>/ (the
#   files lake wrote under .lake/build/lib/lean/StabCert/<case>/<TAG>/, certificates left out: the
#   theorems chunk<k> were checked when the shard compiled them). Then:
#   1. CaDiCaL and lrat-trim refute the clauses "not all literals of cube c", one per refuted cube of
#      all shards, which says the cubes cover every assignment;
#   2. Lean compiles Final.lean (scripts/stabfinal_lean.py), which checks that certificate and proves
#      the theorem from the chunk theorems by Stab.unsat_of_cubes, and reports its axioms.
#   Output: build/stabfinal/<case>/result.txt.
set -uo pipefail
CASE=$1; read -r n p sz dm <<< "$CASE"; FL=$2; shift 2
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN="$ROOT/verification/lean"
B="$ROOT/build"
CADICAL="${CADICAL:-$B/tools/cadical/build/cadical}"
LRAT_TRIM="${LRAT_TRIM:-$B/tools/lrat-trim/lrat-trim}"
NS="T${n}_${p}_${sz//,/_}_d${dm}_${FL:-x}"
O="$B/stabfinal/$NS"; mkdir -p "$O"
SRC="$LEAN/StabCert/$NS"; LIB="$LEAN/.lake/build/lib/lean/StabCert/$NS"; mkdir -p "$SRC/lrat" "$LIB"
: > "$O/leaves.txt"; TAGS=
for d in "$@"; do
  for t in $(ls "$d/lean"); do
    [ -e "$SRC/$t" ] && { echo "$CASE ERROR shard tag $t twice" | tee "$O/result.txt"; exit 1; }
    mkdir -p "$SRC/$t" "$LIB/$t"
    cp "$d/lean/$t"/*.lean "$SRC/$t/"; cp -r "$d/olean/$t/." "$LIB/$t/"
    TAGS="$TAGS $t"
  done
  cat "$d/leaves.txt" >> "$O/leaves.txt"
done
NL=$(grep -c . "$O/leaves.txt")
cd "$LEAN"
DUMP="$LEAN/.lake/build/bin/stab-dump"
[ -x "$DUMP" ] || lake build stab-dump > /dev/null
lake build BiplanarF.Stab > /dev/null
"$DUMP" "$n" "$p" "$sz" "$dm" "${FL:--}" "$O/m.cnf" > /dev/null
MAXV=$(head -n 1 "$O/m.cnf" | cut -d' ' -f3); rm -f "$O/m.cnf"
{ echo "p cnf $MAXV $NL"; awk '{ s = ""; for (i = 2; i <= NF; i++) s = s (-$i) " "; print s "0" }' "$O/leaves.txt"; } > "$O/cover.cnf"
"$CADICAL" -q --lrat=true --binary=true "$O/cover.cnf" "$O/cover.raw" > /dev/null 2>&1; rc=$?
[ "$rc" = 20 ] || { echo "$CASE ERROR the cubes of the shards do not cover (CaDiCaL exit $rc)" | tee "$O/result.txt"; exit 1; }
"$LRAT_TRIM" -q -a "$O/cover.cnf" "$O/cover.raw" "$SRC/lrat/cover.lrat" > /dev/null 2>&1; rc=$?   # 20: verified
[ "$rc" = 20 ] || { echo "$CASE ERROR cover proof (lrat-trim exit $rc)" | tee "$O/result.txt"; exit 1; }
python3 "$ROOT/scripts/stabfinal_lean.py" "$NS" "$n" "$p" "$sz" "$dm" "$FL" "$LEAN/StabCert" $TAGS
t0=$(date +%s)
# plain lean with lake's import list, not lake build: lake would rebuild the shard modules, whose
# certificates (.olean.private) are not here
lake env lean --setup "StabCert/$NS/Final.setup.json" "StabCert/$NS/Final.lean" > "$O/lean.txt" 2>&1; lrc=$?
T_LEAN=$(( $(date +%s) - t0 ))
if [ "$lrc" != 0 ] || grep -q "error" "$O/lean.txt"; then tail -30 "$O/lean.txt"; echo "$CASE ERROR Lean rejected the combination" | tee "$O/result.txt"; exit 1; fi
AX=$(tr '\n' ' ' < "$O/lean.txt" | sed -n "s/.*'StabCert.$NS.unsat' depends on axioms: \[\([^]]*\)\].*/\1/p")
[ -n "$AX" ] || { echo "$CASE ERROR no axiom report" | tee "$O/result.txt"; exit 1; }
for a in $(echo "$AX" | tr ',' ' '); do
  case "$a" in
    propext|Classical.choice|Quot.sound|*._native.native_decide.ax_*) ;;
    *) echo "$CASE ERROR unexpected axiom $a" | tee "$O/result.txt"; exit 1 ;;
  esac
done
H=$( (cat "$O/leaves.txt"; sha256sum "$SRC/lrat/cover.lrat" | cut -d' ' -f1) | sha256sum | cut -d' ' -f1)
echo "$CASE CERTIFIED $NS shards=$(wc -w <<< "$TAGS") cubes=$NL lean=${T_LEAN}s sha256=$H" | tee "$O/result.txt"
