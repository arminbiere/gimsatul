#!/bin/sh
cat<<EOF>input.json
{
  "formula_file": "/rundir/$1",
  "worker_node_ips": ["leader"],
  "timeout_seconds": "1000",
  "formula_language": "",
  "solver_argument_list": [""]
}
EOF
exec docker run -i --shm-size=32g --name leader --entrypoint bash --rm -v `pwd`:/rundir satcomp-gimsatul -c "/competition/solver; cat /rundir/stdout.log; cat /rundir/stderr.log 1>&2"
