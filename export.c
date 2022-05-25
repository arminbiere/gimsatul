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
		    export_literal (ruler->map, unit));
      assign_ruler_unit (ruler, unit);
      ring->statistics.exported.clauses++;
      ring->statistics.exported.units++;
    }

  if (locked && pthread_mutex_unlock (&ruler->locks.units))
    fatal_error ("failed to release unit lock");
}

void
export_binary (struct ring *ring, struct watch *watch)
{
  assert (binary_pointer (watch));
  unsigned threads = ring->threads;
  if (threads < 2)
    return;
  LOGWATCH (watch, "exporting");
  for (unsigned i = 0; i != threads; i++)
    {
      if (i == ring->id)
	continue;
      struct pool *pool = ring->pool + i;
      struct clause *clause = (struct clause *) watch;
      struct clause *volatile *share = &pool->share[BINARY_SHARED];
      struct clause *previous = atomic_exchange (share, clause);
      if (previous)
	continue;
      ring->statistics.exported.binary++;
      ring->statistics.exported.clauses++;
    }
}

static unsigned
export_clause (struct ring *ring, struct clause *clause, unsigned shared)
{
  assert (shared < SIZE_SHARED);
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
      struct clause *volatile *share = &pool->share[shared];
      struct clause *previous = atomic_exchange (share, clause);
      if (previous)
	dereference_clause (ring, previous);
      else
	{
	  ring->statistics.exported.clauses++;
	  exported++;
	}
    }
  return exported;
}

void
export_glue1_clause (struct ring *ring, struct clause *clause)
{
  assert (!binary_pointer (clause));
  assert (clause->glue <= 1);
  if (ring->pool)
    ring->statistics.exported.glue1 +=
      export_clause (ring, clause, GLUE1_SHARED);
}

void
export_tier1_clause (struct ring *ring, struct clause *clause)
{
  assert (!binary_pointer (clause));
  assert (1 < clause->glue);
  assert (clause->glue <= TIER2_GLUE_LIMIT);
  if (ring->pool)
    ring->statistics.exported.tier1 +=
      export_clause (ring, clause, TIER1_SHARED);
}

void
export_tier2_clause (struct ring *ring, struct clause *clause)
{
  assert (!binary_pointer (clause));
  assert (TIER1_GLUE_LIMIT < clause->glue);
  assert (clause->glue <= TIER2_GLUE_LIMIT);
  if (ring->pool)
    ring->statistics.exported.tier2 +=
      export_clause (ring, clause, TIER2_SHARED);
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
	  struct clause *volatile *share = &pool->share[shared];
	  struct clause *clause = atomic_exchange (share, 0);
	  if (!clause)
	    continue;
	  if (shared != BINARY_SHARED)
	    dereference_clause (ring, clause);
	  flushed++;
	}
    }
  very_verbose (ring, "flushed %zu clauses to be exported", flushed);
}
