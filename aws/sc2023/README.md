# Dockerfile for SAT Competition 2023 Parallel Track on AWS

- `Dockerfile` for the 'satcomp-gimsatul' image
- `input.json` generated by `run.sh` (put into `/rundir`)
- `makefile` for building and testing (`make test`)
- `prime2209.cnf` simple satisfiable formula
- `prime4294967297.cnf` slightly harder unsatisfiable formula
- `run.sh` script for local testing
- `solver` script copied to `/competition/solver` in image
- `stderr.log` produced by docker run triggered by `run.sh`
- `stdout.log` produced by docker run triggered by `run.sh`
