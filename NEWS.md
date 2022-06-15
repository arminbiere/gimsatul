# Version 1.0.2rc1

- We further increased the watcher stack size by 8 bytes (from 24 to 32)
  making room for storing the literals of clauses of size 3 and 4 directly
  in the watcher.  This thus avoids another memory dereference to such short
  but non-binary clauses.  For those short clauses the middle reference is
  not needed giving room for one more literal and the previously unused
  padding needed for the 8-byte aligned clause pointer in a watcher gave
  another one.  This explains why increasing the size by 8 bytes gives room
  for 16 bytes (one could in principle stuff in two more literals extending
  the XOR trick, and actually get away with 24 bytes for up to 4 literals,
  but this would make propagation and analysis code much more complex).

- Separated watchers from opaque watch pointers and allocated these watchers
  on thread local watcher stack instead of using allocating thread local
  objects.  This requires indexing (restricts the number of watchers to
  2^31-1) instead of using pointers in watch lists, but makes room for
  blocking literals which seem to speed up propagation substantially also
  for us in this solver (and was the whole point of this change).

- Added termination checks to simplifiers and local search.

- Improved scheduling of simplification limits and bounds.

- Added `-i` / `--id` command line option (to get GIT id even for
  `./configure --quiet`).

- Made the pool cache-line-size aligned to maximizes cache usage and still
  avoid false sharing (as one pool is cache-line sized).

- Removed potential race during logging dereferenced clause.

- Factored out empty clause tracing into `set_inconsistent`
  (as tracing was missing at two calls to it).

- Removed duplicated trace deletion in `compact_ring` during removal of
  root-level falsified literals in saved thread-local learned clauses, when
  the shrunken clause becomes binary (thus virtual).

# Version 1.0.1

- Xcode needs `_Atomic(...) *` instead of `volatile ... *` first arguments in
  `atomic_exchange` etc.

- Added `./configure --pedantic` to test for C11 conformance
  (removes `popen` and thus compressed reading).
