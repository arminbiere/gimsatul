# Gimsatul SAT Solver

Use the following to configure, compile and test the solver

> `./configure && make test`

For more information on build options try

> `./configure -h`

The resulting solver `gimsatul` is multi-threaded but you need
to specified the number of threads explicitly to make use of that
feature:

> `./gimsatul cnf/prime4294967297.cnf --threads=16`

Information about other command line options is obtained with

> `./gimsatul -h`

The solver reasos (optionally copmpressed) files in DIMACS format
and also is able to produce DRUP/DRAT proofs.  To generate a
proof trace just specify the path to the output proof file
as an addition argument on the command line:

> `./gimsatul cnf/prime4294967297.cnf --threads=16 /tmp/proof`

Armin Biere
