#include "assign.h"
#include "macros.h"
#include "propagate.h"
#include "ruler.h"
#include "utilities.h"

struct watch *
ring_propagate (struct ring *ring, bool stop_at_conflict, struct watch * ignore)
{
  assert (!ring->inconsistent);
  assert (ignore || !binary_pointer (ignore));
  struct ring_trail *trail = &ring->trail;
  struct watch *conflict = 0;
  signed char *values = ring->values;
  uint64_t ticks = 0, propagations = 0;
  while (trail->propagate != trail->end)
    {
      if (stop_at_conflict && conflict)
	break;
      unsigned lit = *trail->propagate++;
      LOG ("propagating %s", LOGLIT (lit));
      propagations++;
      unsigned not_lit = NOT (lit);
      struct references *watches = &REFERENCES (not_lit);
      unsigned *binaries = watches->binaries;
      if (binaries)
	{
	  unsigned other, *p;
	  for (p = binaries; (other = *p) != INVALID; p++)
	    {
	      struct watch *watch = tag_pointer (false, other, not_lit);
	      signed char other_value = values[other];
	      if (other_value < 0)
		{
		  conflict = watch;
		  if (stop_at_conflict)
		    break;
		}
	      else if (!other_value)
		{
		  struct watch *reason = tag_pointer (false, other, not_lit);
		  assign_with_reason (ring, other, reason);
		  ticks++;
		}
	    }
	  ticks += cache_lines (p, binaries);
	  if (stop_at_conflict && conflict)
	    break;
	}
      struct watch **begin = watches->begin, **q = begin;
      struct watch **end = watches->end, **p = begin;
      ticks++;
      while (p != end)
	{
	  assert (!stop_at_conflict || !conflict);
	  struct watch *watch = *q++ = *p++;
	  if (ignore && watch == ignore)
	    continue;
	  unsigned other;
	  signed char other_value;
	  if (binary_pointer (watch))
	    {
	      assert (lit_pointer (watch) == not_lit);
	      other = other_pointer (watch);
	      other_value = values[other];
	      if (other_value > 0)
		continue;
	      if (other_value < 0)
		{
		  conflict = watch;
		  if (stop_at_conflict)
		    break;
		}
	      else
		{
		  struct watch *reason = tag_pointer (false, other, not_lit);
		  assign_with_reason (ring, other, reason);
		  ticks++;
		}
	    }
	  else
	    {
	      assert (!watch->garbage);
	      other = watch->sum ^ not_lit;
	      assert (other < 2 * ring->size);
	      other_value = values[other];
	      ticks++;
	      if (other_value > 0)
		continue;
	      struct clause *clause = watch->clause;
	      unsigned replacement = INVALID;
	      signed char replacement_value = -1;
	      unsigned *literals = clause->literals;
	      unsigned *end_literals = literals + clause->size;
	      assert (watch->middle <= clause->size);
	      unsigned *middle_literals = literals + watch->middle;
	      unsigned *r = middle_literals;
	      ticks++;
	      while (r != end_literals)
		{
		  replacement = *r;
		  if (replacement != not_lit && replacement != other)
		    {
		      replacement_value = values[replacement];
		      if (replacement_value >= 0)
			break;
		    }
		  r++;
		}
	      if (replacement_value < 0)
		{
		  r = literals;
		  while (r != middle_literals)
		    {
		      replacement = *r;
		      if (replacement != not_lit && replacement != other)
			{
			  replacement_value = values[replacement];
			  if (replacement_value >= 0)
			    break;
			}
		      r++;
		    }
		}
	      watch->middle = r - literals;
	      if (replacement_value >= 0)
		{
		  watch->sum = other ^ replacement;
		  LOGCLAUSE (watch->clause, "unwatching %s in", LOGLIT (lit));
		  watch_literal (ring, replacement, watch);
		  ticks++;
		  q--;
		}
	      else if (other_value)
		{
		  assert (other_value < 0);
		  conflict = watch;
		  if (stop_at_conflict)
		    break;
		}
	      else
		{
		  assign_with_reason (ring, other, watch);
		  ticks++;
		}
	    }
	}
      while (p != end)
	*q++ = *p++;
      ticks += cache_lines (p, begin);
      watches->end = q;
      if (q == watches->begin)
	RELEASE (*watches);
    }

  struct context *context = ring->statistics.contexts + ring->context;

  if (conflict)
    {
      LOGWATCH (conflict, "conflicting");
      context->conflicts++;
    }

  context->propagations += propagations;
  context->ticks += ticks;

  return conflict;
}

