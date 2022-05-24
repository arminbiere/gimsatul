#include "barrier.h"
#include "macros.h"
#include "message.h"
#include "reduce.h"
#include "report.h"
#include "ring.h"
#include "trace.h"
#include "utilities.h"

#include <inttypes.h>
#include <math.h>

bool
reducing (struct ring *ring)
{
  return ring->limits.reduce < SEARCH_CONFLICTS;
}

void
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
      if (watch->garbage)
	continue;
      assert (!binary_pointer (watch));
      assert (watch->clause->redundant == watch->redundant);
      if (watch->redundant)
	redundant++;
      else
	irredundant++;
    }
#ifndef NDEBUG
  struct ring_statistics *statistics = &ring->statistics;
  assert (statistics->redundant == redundant);
  assert (statistics->irredundant == irredundant);
#endif
}

#define all_literals_on_trail_with_reason(LIT) \
  unsigned * P_ ## LIT = ring->trail.iterate, \
           * END_ ## LIT = ring->trail.end, LIT; \
  P_ ## LIT != END_ ## LIT && (LIT = *P_ ## LIT, true); \
  ++ P_ ## LIT

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

static void
gather_reduce_candidates (struct ring *ring, struct watches *candidates)
{
  for (all_watches (watch, ring->watches))
    {
      if (watch->garbage)
	continue;
      if (watch->reason)
	continue;
      if (!watch->redundant)
	continue;
      if (watch->glue <= TIER1_GLUE_LIMIT)
	continue;
      if (watch->used)
	{
	  watch->used--;
	  continue;
	}
      PUSH (*candidates, watch);
    }
  verbose (ring, "gathered %zu reduce candidates %.0f%%",
	   SIZE (*candidates),
	   percent (SIZE (*candidates), ring->statistics.redundant));
}

static void
mark_reduce_candidates_as_garbage (struct ring *ring,
				   struct watches *candidates)
{
  size_t size = SIZE (*candidates);
  size_t target = REDUCE_FRACTION * size;
  size_t reduced = 0;
  for (all_watches (watch, *candidates))
    {
      mark_garbage_watch (ring, watch);
      if (++reduced == target)
	break;
    }
  verbose (ring, "reduced %zu clauses %.0f%%",
	   reduced, percent (reduced, size));
}

static void
flush_references (struct ring *ring, bool fixed)
{
  size_t flushed = 0;
  signed char *values = ring->values;
  struct variable *variables = ring->variables;
  for (all_ring_literals (lit))
    {
      signed char lit_value = values[lit];
      if (lit_value > 0)
	{
	  if (variables[IDX (lit)].level)
	    lit_value = 0;
	}
      struct references *watches = &REFERENCES (lit);
      struct watch **begin = watches->begin, **q = begin;
      struct watch **end = watches->end;
      for (struct watch ** p = begin; p != end; p++)
	{
	  struct watch *watch = *q++ = *p;
	  if (binary_pointer (watch))
	    {
	      assert (lit == lit_pointer (watch));
	      if (!fixed)
		continue;
	      unsigned other = other_pointer (watch);
	      assert (lit != other);
	      signed char other_value = values[other];
	      if (other_value > 0)
		{
		  if (variables[IDX (other)].level)
		    other_value = 0;
		}
	      if (lit_value > 0 || other_value > 0)
		{
		  if (lit < other)
		    {
		      bool redundant = redundant_pointer (watch);
		      dec_clauses (ring, redundant);
		      trace_delete_binary (&ring->trace, lit, other);
		    }
		  flushed++;
		  q--;
		}
	    }
	  else
	    {
	      if (!watch->garbage)
		continue;
	      if (watch->reason)
		continue;
	      flushed++;
	      q--;
	    }
	}
      watches->end = q;
      SHRINK_STACK (*watches);
    }
  assert (!(flushed & 1));
  verbose (ring, "flushed %zu garbage watches from watch lists", flushed);
}

static void
unmark_reasons (struct ring *ring)
{
  for (all_literals_on_trail_with_reason (lit))
    {
      struct watch *watch = VAR (lit)->reason;
      if (!watch)
	continue;
      if (binary_pointer (watch))
	continue;
      assert (watch->reason);
      watch->reason = false;
    }
}

void
reduce (struct ring *ring)
{
#ifndef NDEBUG
  check_clause_statistics (ring);
#endif
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
  sort_redundant_watches (SIZE (candidates), candidates.begin);
  mark_reduce_candidates_as_garbage (ring, &candidates);
  RELEASE (candidates);
  flush_references (ring, fixed);
  flush_watches (ring);
#ifndef NDEBUG
  check_clause_statistics (ring);
#endif
  unmark_reasons (ring);
  limits->reduce = SEARCH_CONFLICTS;
  unsigned interval = ring->options.reduce_interval;
  assert (interval);
  limits->reduce += interval * sqrt (statistics->reductions + 1);
  verbose (ring, "next reduce limit at %" PRIu64 " conflicts",
	   limits->reduce);
  report (ring, '-');
}
