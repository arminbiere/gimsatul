# Gimsatul SAT Solver

This is an attempt to produce a port-folio style parallel SAT-solver which
actually physically shares clauses between different solving threads.  This
is made possible by using separate watcher data-structures for each solver
thread, while keeping the actual clause data immutable.  This allows to
share large clauses between threads through atomic reference counting,
which in turn allows more aggressive sharing of learned clauses while
keeping the overall memory foot-print small.

Interesting learned clauses are exported rather aggressively and imported
eagerly before making a decision.  Beside exchanging all learned units
between threads, there is a preference given to import low-glue learned
clauses (glue = LBD = glucose level), with binary clauses having highest
priorities, followed by glucose level one clause, then tier 1 clauses (glue
of two), and tier 3 clauses (glue at most 6).

Binary original clauses (after preprocessing) are not allocated but kept
virtual in separate watcher stacks, which the are shared among all threads
(as they are not changed).  Learned binary clauses are thread local but
also virtual in the thread local watcher lists.

As far preprocessing is concerned only bounded variable elimination and
subsumption are currently implemented and simply run before solvers are
cloned to share original irredundant clauses.  Inprocessing is not supported
yet.  It would also be useful to parallelize preprocessing, which currently
is only run in a single thread before cloning.

## Naming

The name of the solver comes from *gimbatul* which is "Black Speech" and
occurs in the inscription of the "One Ring" in "Lord of the Rings" and
literally translates to to "find them" (all).

We use the same terminology in the source code.  The main thread which
organizes everything is the "Ruler" and the actual solver threads are called
"Rings".

## Installation

Use the following to configure, compile and test the solver

> `./configure && make test`

For more information on build options try

> `./configure -h`

## Usage

The resulting solver `gimsatul` is multi-threaded but you need
to specify the number of threads explicitly to make use of that
feature:

> `./gimsatul cnf/prime4294967297.cnf --threads=16`

Information about other command line options can be obtained with

> `./gimsatul -h`

The solver reads (optionally compressed) files in DIMACS format
and if requested is able to produce DRUP/DRAT proofs. To generate a
proof trace just specify the path to the output proof file
as an additional argument on the command line

> `./gimsatul cnf/prime4294967297.cnf --threads=16 /tmp/proof`
