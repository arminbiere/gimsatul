#include "export.h"
#include "message.h"
#include "ruler.h"
#include "utilities.h"

void
export_units (struct ring *ring)
{
  assert (!ring->level);
  struct ruler *ruler = ring->ruler;
  struct ring_trail *trail = &ring->trail;
  volatile signed char *values = ruler->values;
  unsigned *end = trail->end;
  bool locked = false;
  while (trail->export != end)
    {
      unsigned unit = *trail->export++;
#ifndef NFASTPATH
      if (values[unit])
	continue;
#endif
      if (ring->pool && !locked)
	{
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

void
export_binary_clause (struct ring *ring, struct watch *watch)
{
  assert (is_binary_pointer (watch));
  if (!ring->options.share_learned_clauses)
    return;
  unsigned threads = ring->threads;
  if (threads < 2)
    return;
  LOGWATCH (watch, "exporting");
  unsigned exported = 0;
  for (unsigned i = 0; i != threads; i++)
    {
      if (i == ring->id)
	continue;
      struct pool *pool = ring->pool + i;
      struct clause *clause = (struct clause *) watch;
      atomic_uintptr_t *share = &pool->share[BINARY_SHARED];
      uintptr_t previous = atomic_exchange (share, (uintptr_t) clause);
      exported += !previous;
    }
  INC_BINARY_CLAUSE_STATISTICS (exported);
}

void
export_large_clause (struct ring *ring, struct clause *clause)
{
  assert (!is_binary_pointer (clause));
  if (!ring->options.share_learned_clauses)
    return;
  unsigned glue = clause->glue;
  assert (glue);
  if (glue > ring->options.maximum_shared_glue)
    return;
  assert (glue < SIZE_SHARED);
  LOGCLAUSE (clause, "exporting");
  unsigned threads = ring->threads;
  assert (threads);
  unsigned inc = threads - 1;
  assert (inc);
  reference_clause (ring, clause, inc);
  struct pool *pool = ring->pool;
  assert (pool);
  unsigned exported = 0;
  for (unsigned i = 0; i != threads; i++, pool++)
    {
      if (i == ring->id)
	continue;
      atomic_uintptr_t *share = &pool->share[glue];
      uintptr_t previous = atomic_exchange (share, (uintptr_t) clause);
      if (previous)
	dereference_clause (ring, (struct clause *) previous);
      else
	exported++;
    }
  INC_LARGE_CLAUSE_STATISTICS (exported, glue);
}

void
flush_pool (struct ring *ring)
{
  size_t flushed = 0;
  for (unsigned i = 0; i != ring->threads; i++)
    {
      if (i == ring->id)
       continue;
      struct pool *pool = ring->pool + i;
      for (unsigned shared = 0; shared != SIZE_SHARED; shared++)
       {
         atomic_uintptr_t *share = &pool->share[shared];
         uintptr_t clause = atomic_exchange (share, 0);
         if (!clause)
           continue;
         if (shared != BINARY_SHARED)
           dereference_clause (ring, (struct clause *) clause);
         flushed++;
       }
    }
  very_verbose (ring, "flushed %zu clauses to be exported", flushed);
}

