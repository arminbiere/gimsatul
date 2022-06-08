# Version 1.0.2rc1

- added termination checks to simplifiers and local search

- improved scheduling of simplification limits and bounds

- added `-i` / `--id` command line option
  (to get GIT id even for `./configure --quiet`)

- made the pool cache-line-size aligned to maximes cache usage
  and still avoid false sharing (as one pool is cache-line sized).

- removed potential race during logging dereferenced clause

- factored out empty clause tracing into `set_inconsistent`
  (as tracing was missing at two calls to it)

- removed duplicated trace deletion in `compact_ring` during removal
  of root-level falsified literals in saved thread-local learned clauses,
  when the shrunken clause becomes binary (thus virtual)

# Version 1.0.1

- Xcode needs `_Atomic(...) *` instead of `volatile ... *` first arguments in
  `atomic_exchange` etc.

- added `./configure --pedantic` to test for C11 conformance
  (removes `popen` and thus compressed reading)
