#!/usr/bin/env bash
# stabcube_leaves.sh CUBES.TXT > LEAVES: the refuted cubes of a stabcube run (lines "round rc time cube"
# with rc 20), one per line, for scripts/stabcert.sh. Runs before commit a0475fb wrote march_cu's
# "refuted" marker "a 0" as a trailing literal 0; it is dropped here (the parent cube is the leaf).
# An empty line means the whole formula was refuted (certify that case with DEPTH 0).
awk '$2 == 20 {
  $1 = ""; $2 = ""; $3 = ""; sub(/ *\(march\)$/, ""); sub(/^ +/, "")
  n = split($0, a, " "); while (n > 0 && a[n] == "0") n--
  s = ""; for (i = 1; i <= n; i++) s = s (i > 1 ? " " : "") a[i]
  print s
}' "$1" | awk '!seen[$0]++'
