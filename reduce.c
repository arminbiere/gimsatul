#include "macros.h"
#include "reduce.h"
#include "ring.h"

bool
reducing (struct ring *ring)
{
  return ring->limits.reduce < SEARCH_CONFLICTS;
}

#ifndef NDEBUG

static void
check_clause_statistics (struct ring *ring)
{
  size_t redundant = 0;
  size_t irredundant = 0;

  for (all_ring_literals (lit))
    {
      struct references *watches = &REFERENCES (lit);
      for (all_watches (watch, *watches))
	{
	  if (!binary_pointer (watch))
	    continue;
	  assert (lit == lit_pointer (watch));
	  unsigned other = other_pointer (watch);
	  if (lit < other)
	    continue;
	  assert (redundant_pointer (watch));
	  redundant++;
	}

      unsigned *binaries = watches->binaries;
      if (!binaries)
	continue;
      for (unsigned *p = binaries, other; (other = *p) != INVALID; p++)
	if (lit < other)
	  irredundant++;
    }

  for (all_watches (watch, ring->watches))
    {
      assert (!binary_pointer (watch));
      struct clause *clause = watch->clause;
      assert (clause->glue == watch->glue);
      assert (clause->redundant == watch->redundant);
      if (watch->redundant)
	redundant++;
      else
	irredundant++;
    }

  struct ring_statistics *statistics = &ring->statistics;
  assert (statistics->redundant == redundant);
  assert (statistics->irredundant == irredundant);
}

#else
#define check_clause_statistics(...) do { } while (0)
#endif

static void
mark_reasons (struct ring *ring)
{
  for (all_literals_on_trail_with_reason (lit))
    {
      struct watch *watch = VAR (lit)->reason;
      if (!watch)
	continue;
      if (binary_pointer (watch))
	continue;
      assert (!watch->reason);
      watch->reason = true;
    }
}

void
reduce (struct ring *ring)
{
  check_clause_statistics (ring);
  struct ring_statistics *statistics = &ring->statistics;
  struct ring_limits *limits = &ring->limits;
  statistics->reductions++;
  verbose (ring, "reduction %" PRIu64 " at %" PRIu64 " conflicts",
	   statistics->reductions, SEARCH_CONFLICTS);
  mark_reasons (ring);
  struct watches candidates;
  INIT (candidates);
  bool fixed = ring->last.fixed != ring->statistics.fixed;
  if (fixed)
    mark_satisfied_ring_clauses_as_garbage (ring);
  gather_reduce_candidates (ring, &candidates);
  sort_reduce_candidates (&candidates);
  mark_reduce_candidates_as_garbage (ring, &candidates);
  RELEASE (candidates);
  flush_references (ring, fixed);
  flush_watches (ring);
  check_clause_statistics (ring);
  unmark_reasons (ring);
  limits->reduce = SEARCH_CONFLICTS;
  limits->reduce += REDUCE_INTERVAL * sqrt (statistics->reductions + 1);
  verbose (ring, "next reduce limit at %" PRIu64 " conflicts",
	   limits->reduce);
  report (ring, '-');
}

