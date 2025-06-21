#include "export.h"
#include "message.h"
#include "random.h"
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
    if (ring->import && !locked) {
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

static void export_to_ring (struct ring *ring, struct ring *other,
                            struct clause *clause, unsigned size,
                            uint64_t redundancy) {
  LOG ("trying to export to target ring %u with redundancy [%u:%u]",
       other->id, LOG_REDUNDANCY (redundancy));
  assert (ring != other);

  struct import *import = other->import;

  struct bucket *start = import->bucket;
  struct bucket *end = start + SIZE_IMPORT;
  struct bucket *worst = 0;

  uint64_t worst_redundancy = 0;

  for (struct bucket *b = start; b != end; b++) {
    atomic_uintptr_t b_shared = b->shared;
    compiler_barrier ();
    uint64_t b_redundancy = b->redundancy;
    if (!b_shared) {
      worst_redundancy = b_redundancy;
      worst = b;
      break;
    }
    if (worst_redundancy > b_redundancy)
      continue;
    worst_redundancy = b_redundancy;
    worst = b;
  }

  if (!worst) {
    LOG ("export to ring %u failed "
         "as all its buckets have better redundancy",
         other->id);
    return;
  }

#ifdef LOGGING
  if (worst_redundancy == MAX_REDUNDANCY)
    LOG ("exporting to ring %u bucket %zu (first export)", other->id,
         worst - start);
  else
    LOG ("exporting to ring %u bucket %zu with redundancy [%u:%u]",
         other->id, worst - start, LOG_REDUNDANCY (worst_redundancy));
#endif
  if (!is_binary_pointer (clause))
    reference_clause (ring, clause, 1);

  atomic_uintptr_t *share = &worst->shared;
  worst->redundancy = redundancy;
  uintptr_t ptr = atomic_exchange (share, (uintptr_t) clause);

  if (ptr) {
    LOG ("previous export to ring %u bucket %zu redundancy [%u:%u] failed",
         other->id, worst - start, LOG_REDUNDANCY (worst_redundancy));
    struct clause *previous = (struct clause *) ptr;
    if (!is_binary_pointer (previous))
      dereference_clause (ring, previous);
  } else if (worst_redundancy != MAX_REDUNDANCY) {
    LOG ("previous export to ring %u bucket %zu redundancy [%u:%u] "
         "succeeded",
         other->id, worst - start, LOG_REDUNDANCY (worst_redundancy));
    INC_LARGE_CLAUSE_STATISTICS (exported, size);
  }
}

static void export_clause (struct ring *ring, struct clause *clause) {
  assert (exporting (ring));
  bool binary = is_binary_pointer (clause);
  unsigned size = binary ? 2 : clause->size;
  uint64_t redundancy = size;
#if 0
  struct rings *exports = export_rings (ring);
  for (all_pointers_on_stack (struct ring, other, *exports))
    export_to_ring (ring, other, clause, size, redundancy);
#else
  struct ruler *ruler = ring->ruler;
  struct rings *rings = &ruler->rings;
  for (all_pointers_on_stack (struct ring, other, *rings))
    if (other != ring)
      export_to_ring (ring, other, clause, size, redundancy);
#endif
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
#if 0
  struct averages *a = ring->averages + ring->stable;
  double average, factor, limit;
#if 0
  unsigned glue = clause->glue;
  if (glue > ring->tier1_glue_limit[ring->stable]) {
    factor = 0.5;
    average = a->glue.slow.value;
    limit = factor * average;
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
#else
  unsigned size = clause->size;
  factor = 1.0;
  average = a->size.value;
  limit = factor * average;
  if (size > limit) {
    LOGCLAUSE (clause, "failed to export (size %u > limit %g = %g * %g)",
               size, limit, factor, average);
    return;
  }
#endif
#endif
  LOGCLAUSE (clause, "exporting");
  export_clause (ring, clause);
}
