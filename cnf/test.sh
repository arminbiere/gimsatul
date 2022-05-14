#!/bin/sh

cd `dirname $0`/..

ron () {
  if [ "$3" = "" ]
  then
    name=$2
    opts=""
  else
    name=$2`echo -- "$3"|sed -e 's,[= ],,g;s,--,-,g'`
    opts=" $3"
  fi
  cnf=cnf/$2.cnf
  log=cnf/$name.log
  err=cnf/$name.err
  rm -f $log $err
  cmd="./gimsatul $cnf$opts"
  echo "$cmd"
  $cmd 1>$log 2>$err
  status=$?
  if [ ! $1 = $status ]
  then
    echo "cnf/test.sh: error: '$cmd' exits with status '$status' but expected '$1'"
    exit 1
  fi
}

run () {
  ron $1 $2
  ron $1 $2 "--threads=2"
  ron $1 $2 "--threads=4"
  ron $1 $2 "--walk-initially"
  ron $1 $2 "--no-simplify"
  ron $1 $2 "--no-simplify --threads=2"
  ron $1 $2 "--no-simplify --threads=4"
}

run 20 false
run 10 true

run 10 trivial

run 10 unit1
run 10 unit2
run 10 unit3
run 10 unit4
run 20 unit5
run 20 unit6
run 10 unit7
run 20 unit8
run 20 unit9

run 20 full1
run 20 full2
run 20 full3
run 20 full4

run 20 ph2
run 20 ph3
run 20 ph4
run 20 ph5
run 20 ph6

run 20 add4
run 20 add8
run 20 add16
run 20 add32
run 20 add64
run 20 add128

run 10 prime4
run 10 prime9
run 10 prime49
run 10 prime121
run 10 prime169
run 10 prime289
run 10 prime361
run 10 prime841
run 10 prime961
run 10 prime529
run 10 prime1369
run 10 prime1681
run 10 prime1849
run 10 prime2209
run 20 prime65537

run 10 sqrt2809
run 10 sqrt3481
run 10 sqrt3721
run 10 sqrt4489
run 10 sqrt5041
run 10 sqrt5329
run 10 sqrt6241
run 10 sqrt6889
run 10 sqrt7921
run 10 sqrt9409
run 10 sqrt10201
run 10 sqrt10609
run 10 sqrt11449
run 10 sqrt11881
run 10 sqrt12769
run 10 sqrt16129
run 10 sqrt63001
run 10 sqrt259081
run 10 sqrt1042441
