#!/usr/bin/env bash
# certifyF.sh 'w|a-b,c-d,...' -- refute "the clique blow-up F[w] is biplanar" and check the refutation in Lean.
#
#   1. the Lean encoder (verification/lean, Biplanar.encode w edges) writes the formula to build/cnf/TAG.cnf;
#   2. CaDiCaL refutes it and writes a binary LRAT proof;
#   3. lrat-trim checks and trims the proof and writes it as text to build/lrat/TAG.lrat;
#   4. Lean checks the proof with the verified LRAT checker of its standard library
#      (Std.Tactic.BVDecide.Reflect.verifyCert_correct) and proves (Biplanar.encode w edges).Unsat.
# Prints one line "TAG w|edges certified ..." or exits non-zero. Needs CADICAL and LRAT_TRIM and elan.
set -euo pipefail
LINE="$1"; W="${LINE%%|*}"; FE="${LINE#*|}"
TAG="$(echo "${W//,/_}")_$(printf '%s' "$FE" | md5sum | cut -c1-8)"
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
LEAN="$ROOT/verification/lean"
B="$ROOT/build"
mkdir -p "$B/cnf" "$B/lrat" "$B/log"
CADICAL="${CADICAL:-$B/tools/cadical/build/cadical}"
LRAT_TRIM="${LRAT_TRIM:-$B/tools/lrat-trim/lrat-trim}"
cd "$LEAN"
DUMP="$LEAN/.lake/build/bin/biplanarf-dump"
[ -x "$DUMP" ] || lake build biplanarf-dump > /dev/null
"$DUMP" "$W" "$FE" "$B/cnf/$TAG.cnf" > /dev/null
now() { date +%s.%N; }
since() { awk -v a="$1" -v b="$(now)" 'BEGIN { printf "%.1f", b - a }'; }
t0=$(now)
set +e
"$CADICAL" -q --lrat=true --binary=true "$B/cnf/$TAG.cnf" "$B/lrat/$TAG.raw" > "$B/log/$TAG.cadical.txt"
rc=$?
set -e
[ "$rc" = 20 ] || { echo "CaDiCaL exit code $rc on $LINE (expected 20 = unsatisfiable)"; exit 1; }
T_SOLVE=$(since "$t0"); t0=$(now)
set +e
"$LRAT_TRIM" -q -a "$B/cnf/$TAG.cnf" "$B/lrat/$TAG.raw" "$B/lrat/$TAG.lrat"
rc=$?
set -e
[ "$rc" = 20 ] || { echo "lrat-trim exit code $rc on $LINE (expected 20 = proof verified)"; exit 1; }
T_TRIM=$(since "$t0")
rm -f "$B/lrat/$TAG.raw"
LW="[${W//,/, }]"
LFE="[$(echo "$FE" | sed -E 's/([0-9]+)-([0-9]+)/(\1, \2)/g; s/,\(/, (/g')]"
mkdir -p "$LEAN/Certs"
ln -sfn "$B/lrat" "$LEAN/Certs/lrat"
cat > "$LEAN/Certs/Unsat_$TAG.lean" <<LEANEOF
import BiplanarF.Encode
open Std.Tactic.BVDecide

/-- The clique blow-up \`F[w]\`, \`w = $W\`, \`F\` with edges \`$FE\`, is not biplanar: the LRAT proof in
\`Certs/lrat/$TAG.lrat\` refutes its formula and is accepted by the verified checker of the Lean standard library. -/
theorem Biplanar.unsatF_$TAG : (Biplanar.encode $LW $LFE).Unsat :=
  Reflect.verifyCert_correct _ (include_str "lrat/$TAG.lrat") (by native_decide)

#print axioms Biplanar.unsatF_$TAG
LEANEOF
t0=$(now)
lake env lean "Certs/Unsat_$TAG.lean" > "$B/log/$TAG.lean.txt" 2>&1 || true
T_LEAN=$(since "$t0")
if grep -q "error" "$B/log/$TAG.lean.txt"; then cat "$B/log/$TAG.lean.txt"; echo "Lean rejected the certificate for $LINE"; exit 1; fi
AX=$(tr '\n' ' ' < "$B/log/$TAG.lean.txt" | sed -n "s/.*'Biplanar.unsatF_$TAG' depends on axioms: \[\([^]]*\)\].*/\1/p")
[ -n "$AX" ] || { echo "no axiom report"; exit 1; }
for a in $(echo "$AX" | tr ',' ' '); do
  case "$a" in
    propext|Classical.choice|Quot.sound|"Biplanar.unsatF_$TAG._native.native_decide.ax_1_1") ;;
    *) echo "unexpected axiom $a"; exit 1 ;;
  esac
done
H=$(sha256sum "$B/lrat/$TAG.lrat" | cut -d' ' -f1)
echo "$TAG $LINE certified clauses=$(head -n 1 "$B/cnf/$TAG.cnf" | cut -d' ' -f4) solve=${T_SOLVE}s trim=${T_TRIM}s lean=${T_LEAN}s lrat_sha256=$H"
