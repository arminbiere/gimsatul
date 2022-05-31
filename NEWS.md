# Version 1.0.2rc1

- removed duplicated trace deletion in `compact_ring` during removal
  of root-level falsified literals in saved thread-local learned clauses,
  when the shrunken clause becomes binary (thus virtual)

# Version 1.0.1

- Xcode needs `_Atomic(...) *` instead of `volatile ... *` first arguments in
  `atomic_exchange` etc.

- added `./configure --pedantic` to test for C11 conformance
  (removes `popen` and thus compressed reading)
