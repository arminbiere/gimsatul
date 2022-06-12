# Version 1.0.2rc1

- Separated watchers from opaque watch pointers and allocated
  these watchers on thread local watcher stack instead of using
  allocating thread local objects.  This requires indexing
  (restricts the number of watchers to 2^31-1) instead of
  using pointers in watch lists, but makes rooms for blocking
  literals which speeds up propagation (and was the whole point
  of this change).

- Added termination checks to simplifiers and local search.

- Improved scheduling of simplification limits and bounds.

- Added `-i` / `--id` command line option
  (to get GIT id even for `./configure --quiet`).

- Made the pool cache-line-size aligned to maximes cache usage
  and still avoid false sharing (as one pool is cache-line sized).

- Removed potential race during logging dereferenced clause.

- Factored out empty clause tracing into `set_inconsistent`
  (as tracing was missing at two calls to it).

- Removed duplicated trace deletion in `compact_ring` during removal
  of root-level falsified literals in saved thread-local learned clauses,
  when the shrunken clause becomes binary (thus virtual).

# Version 1.0.1

- Xcode needs `_Atomic(...) *` instead of `volatile ... *` first arguments in
  `atomic_exchange` etc.

- Added `./configure --pedantic` to test for C11 conformance
  (removes `popen` and thus compressed reading).
