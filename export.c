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

static bool exporting (struct ring *ring) {
  unsigned threads = ring->threads;
  if (threads < 2)
    return false;
  if (!ring->options.share_learned)
    return false;
  return true;
}

static struct rings *export_rings (struct ring *ring) {
  struct rings *exports = &ring->exports;
  CLEAR (*exports);
#if 1
  struct ring * other = random_other_ring (ring);
  PUSH (*exports, other);
#else
  struct ruler *ruler = ring->ruler;
  for (all_rings (other))
    if (other != ring)
      PUSH (*exports, other);
#endif
  return exports;
}

static void export_to_ring (struct ring *ring, struct ring *other,
                            struct clause *clause, unsigned glue,
                            unsigned size, uint64_t redundancy) {
  LOG ("exporting to other target ring %u", other->id);
  assert (ring != other);

  struct pool *pool = ring->pool + other->id;
  struct bucket *start = pool->bucket;
  struct bucket *end = start + SIZE_POOL;
  struct bucket *worst = 0;

  for (struct bucket *b = start; b != end; b++) {
    if (!b->shared) {
      worst = b;
      break;
    }
    if (!worst || worst->redundancy >= redundancy)
      worst = b;
  }

  if (!worst)
    return;

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
    INC_LARGE_CLAUSE_STATISTICS (exported, glue, size);
}

static void export_clause (struct ring *ring, struct clause *clause) {
  assert (exporting (ring));
  bool binary = is_binary_pointer (clause);
  unsigned glue = binary ? 1 : clause->glue;
  unsigned size = binary ? 2 : clause->size;
  bool share_by_size = ring->options.share_by_size;
  uint64_t high = share_by_size ? size : glue;
  uint64_t low = share_by_size ? glue : size;
  uint64_t redundancy = (high << 32) + low;
  struct rings *exports = export_rings (ring);
  for (all_pointers_on_stack (struct ring, other, *exports))
    export_to_ring (ring, other, clause, glue, size, redundancy);
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
  unsigned glue = clause->glue;
  if (glue > TIER1_GLUE_LIMIT) {
    double factor = 0.5;
    double average = a->glue.slow.value;
    double limit = factor * average;
    if (glue > limit) {
      LOGCLAUSE (clause, "failed to export (glue %u > limit %g = %g * %g)",
                 glue, limit, factor, average);
      return;
    }
    unsigned size = clause->size;
    factor = 1.0;
    average = a->size.value;
    limit = factor * average;
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
