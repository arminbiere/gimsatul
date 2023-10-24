#include "export.h"
#include "message.h"
#include "ruler.h"
#include "utilities.h"

void export_units (struct ring *ring) {
  struct ruler *ruler = ring->ruler;
  struct ring_units *units = &ring->ring_units;
  volatile signed char *values = ruler->values;
  unsigned *end = units->end;
  bool locked = false;
  while (units->export != end) {
    assert (units->export < units->end);
    unsigned unit = *units->export ++;
#ifndef NFASTPATH
    if (values[unit])
      continue;
#endif
    if (ring->pool && !locked) {
      if (pthread_mutex_lock (&ruler->locks.units))
        fatal_error ("failed to acquire unit lock");
      locked = true;
    }

    signed char value = values[unit];
    if (value)
      continue;

    very_verbose (ring, "exporting unit %d",
                  unmap_and_export_literal (ruler->unmap, unit));
    assign_ruler_unit (ruler, unit);
    INC_UNIT_CLAUSE_STATISTICS (exported);
  }

  if (locked && pthread_mutex_unlock (&ruler->locks.units))
    fatal_error ("failed to release unit lock");
}

static uint64_t compute_redundancy (struct ring *ring, unsigned glue,
                                    unsigned size) {
  bool share_by_size = ring->options.share_by_size;
  unsigned high = share_by_size ? size : glue;
  unsigned low = share_by_size ? glue : size;
  return (((uint64_t) high) << 32) + low;
}

static bool exporting (struct ring *ring) {
  unsigned threads = ring->threads;
  if (threads < 2)
    return false;
  if (!ring->options.share_learned)
    return false;
  return true;
}

static void export_clause (struct ring *ring, struct clause *clause) {
  assert (exporting (ring));
  unsigned glue, size;
  if (is_binary_pointer (clause))
    glue = 1, size = 2;
  else
    glue = clause->glue, size = clause->size;
  unsigned redundancy = compute_redundancy (ring, glue, size);
  struct ring *other = random_other_ring (ring);
  struct pool *pool = ring->pool + other->id;
  struct bucket *worst = 0;
  LOG ("exporting to random other target ring %u", other->id);
  unsigned exported = 0;
  for (struct bucket *b = pool->bucket, *end = b + SIZE_POOL; b != end; b++)
    if (!b->shared) {
      worst = b;
      break;
    } else if (!worst || worst->redundancy >= redundancy)
      worst = b;
  if (worst) {
    atomic_uintptr_t *share = &worst->shared;
    if (!is_binary_pointer (clause))
      reference_clause (ring, clause, 1);
    uintptr_t ptr = atomic_exchange (share, (uintptr_t) clause);
    worst->redundancy = redundancy;
    if (ptr) {
      struct clause *previous = (struct clause *) ptr;
      if (!is_binary_pointer (previous))
        dereference_clause (ring, previous);
    } else
      exported++;
  }
  ADD_LARGE_CLAUSE_STATISTICS (exported, exported, glue, size);
  INC_LARGE_CLAUSE_STATISTICS (shared, glue, size);
}

void export_binary_clause (struct ring *ring, struct watch *watch) {
  assert (is_binary_pointer (watch));
  if (!exporting (ring))
    return;
  LOGWATCH (watch, "exporting");
  struct clause *clause = (struct clause *) watch;
  export_clause (ring, clause);
}

void export_large_clause (struct ring *ring, struct clause *clause) {
  assert (!is_binary_pointer (clause));
  if (!exporting (ring))
    return;
  struct averages *a = ring->averages + ring->stable;
  // TODO make this an option.
  {
    unsigned glue = clause->glue;
    double factor = 1.0; // TODO make this an option.
    double average = a->glue.slow.value;
    double limit = factor * average;
    if (glue > limit) {
      LOGCLAUSE (clause, "failed to export (glue %u > limit %g = %g * %g)",
                 glue, limit, factor, average);
      return;
    }
  }
  // TODO make this an option.
  {
    unsigned size = clause->size;
    double factor = 0.5; // TODO make this an option.
    double average = a->size.value;
    double limit = factor * average;
    if (size > limit) {
      LOGCLAUSE (clause, "failed to export (size %u > limit %g = %g * %g)",
                 size, limit, factor, average);
      return;
    }
  }
  LOGCLAUSE (clause, "exporting");
  export_clause (ring, clause);
}

void flush_pool (struct ring *ring) {
#ifndef QUIET
  size_t flushed = 0;
#endif
  for (unsigned i = 0; i != ring->threads; i++) {
    if (i == ring->id)
      continue;
    struct pool *pool = ring->pool + i;
    for (unsigned shared = 0; shared != SIZE_POOL; shared++) {
      struct bucket *b = &pool->bucket[shared];
      atomic_uintptr_t *share = &b->shared;
      uintptr_t ptr = atomic_exchange (share, 0);
      if (!ptr)
        continue;
      struct clause *clause = (struct clause *) ptr;
      if (!is_binary_pointer (clause))
        dereference_clause (ring, clause);
#ifndef QUIET
      flushed++;
#endif
    }
  }
  very_verbose (ring, "flushed %zu clauses to be exported", flushed);
}
