#include "assign.h"
#include "macros.h"
#include "propagate.h"
#include "ruler.h"
#include "utilities.h"

#include "cover.h"

struct watch *
ring_propagate (struct ring *ring, bool stop_at_conflict,
		struct clause *ignore)
{
  assert (!ring->inconsistent);
  assert (!ignore || !is_binary_pointer (ignore));
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
	      struct watch *watch = tag_binary (false, other, not_lit);
	      signed char other_value = values[other];
	      if (other_value < 0)
		{
		  conflict = watch;
		  if (stop_at_conflict)
		    break;
		}
	      else if (!other_value)
		{
		  struct watch *reason = tag_binary (false, other, not_lit);
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
	  unsigned blocking = other_pointer (watch);
	  signed char blocking_value = values[blocking];
	  if (blocking_value > 0)
	    continue;
	  if (is_binary_pointer (watch))
	    {
	      assert (lit_pointer (watch) == not_lit);
	      if (blocking_value < 0)
		{
		  conflict = watch;
		  if (stop_at_conflict)
		    break;
		}
	      else
		{
		  struct watch *reason =
		    tag_binary (false, blocking, not_lit);
		  assign_with_reason (ring, blocking, reason);
		  ticks++;
		}
	    }
	  else
	    {
	      ticks++;
	      unsigned idx = index_pointer (watch);
	      struct watcher *watcher = index_to_watcher (ring, idx);
	      if (watcher->garbage)
		continue;
	      struct clause *clause = watcher->clause;
	      if (ignore && clause == ignore)
		continue;
	      unsigned other = watcher->sum ^ not_lit;
	      signed char other_value;
	      if (other == blocking)
		other_value = blocking_value;
	      else
		{
		  assert (other < 2 * ring->size);
		  other_value = values[other];
		  if (other_value > 0)
		    {
		      bool redundant = redundant_pointer (watch);
		      watch = tag_index (redundant, idx, other);
		      q[-1] = watch;
		      continue;
		    }
		}
	      unsigned replacement = INVALID;
	      signed char replacement_value = -1;
	      unsigned *literals = clause->literals;
	      unsigned *end_literals = literals + clause->size;
#ifndef NMIDDLE
	      assert (watcher->middle <= clause->size);
	      unsigned *middle_literals = literals + watcher->middle;
	      unsigned *r = middle_literals;
#else
	      unsigned *r = literals;
#endif
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
#ifndef NMIDDLE
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
	      watcher->middle = r - literals;
#endif
	      if (replacement_value >= 0)
		{
		  watcher->sum = other ^ replacement;
		  LOGCLAUSE (watcher->clause,
			     "unwatching %s in", LOGLIT (not_lit));
		  watch_literal (ring, replacement, other, watcher);
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
