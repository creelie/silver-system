#!/bin/bash
# smssurvey.sh SIZES TIMEOUT: run SMS on the Turán-stability case n=28, p=3, parts SIZES, dmin 9, as a portfolio of
# four variants at once (one per core); stop all when one answers. Writes results/<case>.txt.
set -u
c=$1; T=$2; tag=${c//,/_}; set -- ${c//,/ }
SM=build/sms/build/src/smsg; mkdir -p results work
python3 scripts/sms_stab.py 28 3 "$c" 9 work/$tag.enc e 2> /dev/null
python3 scripts/sms_stab.py 28 3 "$c" 9 work/${tag}T.enc eT 2> /dev/null
run() {  # name enc k extra...
  local nm=$1 f=$2 k=$3; shift 3; local s=$(date +%s)
  timeout $T $SM -v 28 --directed --thickness2 5 --underlying-clique $k --initial-partition $1 $2 $3 --dimacs $f "${@:4}" > work/${tag}_$nm.out 2>&1 &
  echo $! > work/${tag}_$nm.pid; wait $!; local rc=$?
  echo "$c $nm rc=$rc $(( $(date +%s) - s ))s $(grep -E '^Result' work/${tag}_$nm.out)" >> results/$tag.txt
}
run k8 work/$tag.enc 8 "$@" & p1=$!
run k11 work/$tag.enc 11 "$@" & p2=$!
run T11 work/${tag}T.enc 11 "$@" & p3=$!
run k11s work/$tag.enc 11 "$@" --cadical-config "seed=17" & p4=$!
while sleep 20; do
  grep -qE 'Result: (10|20)' results/$tag.txt 2> /dev/null && break
  alive=0; for p in $p1 $p2 $p3 $p4; do kill -0 $p 2> /dev/null && alive=1; done
  [ $alive = 1 ] || break
done
for f in work/${tag}_*.pid; do kill $(cat $f) 2> /dev/null || true; done; wait; rm -f work/${tag}_*.pid
cat results/$tag.txt
