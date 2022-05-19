#include "analyze.h"
#include "assign.h"
#include "backtrack.h"
#include "export.h"
#include "import.h"
#include "message.h"
#include "propagate.h"
#include "report.h"
#include "ring.h"
#include "search.h"
#include "utilities.h"
#include "vivify.h"

#include "cover.h"

#if 1
#include "random.h"
#endif

#include <inttypes.h>

static size_t
reschedule_vivification_candidates (struct ring * ring,
                                    struct watches * candidates)
{
  assert (EMPTY (*candidates));
  for (all_watches (watch, ring->watches))
    if (watch->vivify && !watch->garbage)
      PUSH (*candidates, watch);
  return SIZE (*candidates);
}

static size_t
schedule_vivification_candidates (struct ring * ring,
                                  struct watches * candidates)
{
  for (all_watches (watch, ring->watches))
    if (!watch->vivify && watched_vivification_candidate (watch))
      PUSH (*candidates, watch);
  return SIZE (*candidates);
}

#define ANALYZE(OTHER) \
do { \
  unsigned idx = IDX (other); \
  struct variable * v = variables + idx; \
  if (v->seen) \
    break; \
  unsigned level = v->level; \
  if (!level) \
    break; \
  assert (ring->values[other] < 0); \
  v->seen = true; \
  PUSH (*analyzed, idx); \
  if (level != ring->level && !used[level]) \
    { \
      used[level] = true; \
      PUSH (*levels, level); \
    } \
  open++; \
  if (!v->reason) \
    PUSH (*clause, other); \
} while (0)

struct watch *
vivify_strengthen (struct ring * ring, struct watch * candidate)
{
  LOGWATCH (candidate, "vivify strengthening");
  assert (!binary_pointer (candidate));
  struct unsigneds * analyzed = &ring->analyzed;
  struct variable * variables = ring->variables;
  struct unsigneds * clause = &ring->clause;
  struct unsigneds * levels = &ring->levels;
  bool * used = ring->used;
  struct ring_trail * trail = &ring->trail;
  assert (EMPTY (*analyzed));
  assert (EMPTY (*clause));
  struct watch * reason = candidate;
  unsigned * t = trail->end;
  unsigned open = 0;
  do
    {
      assert (reason);
      LOGWATCH (reason, "vivify analyzing");
      if (binary_pointer (reason))
	{
	  unsigned other = other_pointer (reason);
	  ANALYZE (other);
	}
      else
	{
	  for (all_literals_in_clause (other, reason->clause))
	    ANALYZE (other);
	}
      assert (open);
      if (!--open)
	break;
      assert (t != trail->begin);
      while (open)
	{
	  unsigned lit;
	  for (;;)
	    {
	      assert (t != trail->begin);
	      lit = *--t;
	      unsigned idx = IDX (lit);
	      struct variable * v = variables + idx;
	      if (v->seen)
		{
		  reason = v->reason;
		  break;
		}
	    }
	  if (reason)
	    break;
	  open--;
	}
    }
  while (open);
  LOGTMP ("vivify strengthened");
  size_t size = SIZE (*clause);
  assert (size);
  assert (size < candidate->clause->size);
  unsigned * literals = clause->begin;
  struct watch * res = 0;
  if (size == 1)
    {
      unsigned unit = literals[0];
      assert (ring->level);
      backtrack (ring, 0);
      trace_add_unit (&ring->trace, unit);
      if (ring_propagate (ring, false, 0))
	set_inconsistent (ring, "propagation of strengthened clause unit fails");
      else
        export_units (ring);
    }
  else if (size == 2)
    {
      unsigned lit = literals[0], other = literals[1];
      res = new_local_binary_clause (ring, true, lit, other);
      trace_add_binary (&ring->trace, lit, other);
      export_binary (ring, res);
    }
  else
    {
      unsigned glue = SIZE (*levels);
      LOG ("computed glue %u", glue);
      if (glue > candidate->glue)
	{
	  glue = candidate->glue;
	  LOG ("but candidate glue %u smaller", glue);
	}
      assert (glue < size);
      struct clause * clause =
        new_large_clause (size, literals, true, glue);
      res = watch_first_two_literals_in_large_clause (ring, clause);
      trace_add_clause (&ring->trace, clause);
      if (glue <= 1)
	export_glue1_clause (ring, clause);
      else if (glue <= TIER1_GLUE_LIMIT)
	export_tier1_clause (ring, clause);
      else if (glue <= TIER2_GLUE_LIMIT)
	export_tier2_clause (ring, clause);
    }
  clear_analyzed (ring);
  CLEAR (*clause);
  return res;
}

void
vivify_clauses (struct ring * ring)
{
  if (ring->inconsistent)
    return;
  struct watches * watches = &ring->watches;
  if (EMPTY (*watches))
    return;
  START (ring, vivify);
  assert (SEARCH_TICKS >= ring->last.probing);
  uint64_t delta_search_ticks = SEARCH_TICKS - ring->last.probing;
  uint64_t delta_probing_ticks = VIVIFY_EFFORT * delta_search_ticks;
  verbose (ring, "vivification effort of %" PRIu64 " = %g * %" PRIu64
           " search ticks", delta_probing_ticks, (double) VIVIFY_EFFORT,
	   delta_search_ticks);
  uint64_t probing_ticks_before = PROBING_TICKS;
  uint64_t limit = probing_ticks_before + delta_probing_ticks;
  size_t implied = 0, strengthened = 0, tried = 0, vivified = 0;
  struct watches candidates;
  INIT (candidates);
  size_t rescheduled = reschedule_vivification_candidates (ring, &candidates);
  very_verbose (ring, "rescheduling %zu vivification candidates",
                rescheduled);
  size_t scheduled = schedule_vivification_candidates (ring, &candidates);
  very_verbose (ring, "scheduled %zu vivification candidates in total",
                scheduled);
  signed char * values = ring->values;
#if 0
  struct watch ** begin = candidates.begin;
  struct watch ** end = candidates.end;
  struct watch ** p = begin;
  while (p != end)
#else
  while (!EMPTY (candidates))
#endif
    {
      if (PROBING_TICKS > limit)
	break;
      if (terminate_ring (ring))
	break;
      if (import_shared (ring))
	{
	  if (ring->inconsistent)
	    break;
	  if (ring_propagate (ring, false, 0))
	    {
	      set_inconsistent (ring,
	                        "propagation of imported clauses "
				"during vivification fails");
	      break;
	    }
	}
      tried++;
      assert (!ring->level);
#if 0
      struct watch * watch = *p++;
#else
      size_t size = SIZE (candidates);
      size_t pos = random_modulo (&ring->random, size);
      if (pos != size - 1)
	SWAP (candidates.begin[size-1], candidates.begin[pos]);
      struct watch * watch = POP (candidates);
#endif
      assert (!binary_pointer (watch));
      assert (watched_vivification_candidate (watch));
      watch->vivify = false;
      struct clause * clause = watch->clause;
      unsigned non_root_level_falsified = 0;
      for (all_literals_in_clause (lit, clause))
	{
	  signed char value = values[lit];
	  if (!value)
	    {
	      ring->level++;
	      ring->statistics.contexts[PROBING_CONTEXT].decisions++;
	      unsigned not_lit = NOT (lit);
	      LOG ("assuming %s", LOGLIT (not_lit));
	      assign_decision (ring, not_lit);
	      if (ring_propagate (ring, false, watch))
		goto IMPLIED;
	    }
	  else
	    {
	      const unsigned idx = IDX (lit);
	      struct variable * v = ring->variables + idx;
	      if (value > 0)
		{
		  if (v->level)
		    {
		 IMPLIED:
		      LOGWATCH (watch, "vivify implied");
		      ring->statistics.vivify.succeeded++;
		      ring->statistics.vivify.implied++;
		      vivified++;
		      implied++;
		    }
		  else
		    LOGWATCH (watch, "root-level satisfied");
		  mark_garbage_watch (ring, watch);
		  break;
		}
	      else if (value < 0)
		{
		  if (v->level)
		    non_root_level_falsified++;
		}
	    }
	}
      if (!watch->garbage && non_root_level_falsified)
	{
	  ring->statistics.vivify.succeeded++;
	  ring->statistics.vivify.strengthened++;
	  struct watch * strengthened = vivify_strengthen (ring, watch);
	  mark_garbage_watch (ring, watch);
	  if (ring->inconsistent)
	    break;
	  if (strengthened && !binary_pointer (strengthened))
	    {
	      assert (watched_vivification_candidate (strengthened));
#if 0
	      size_t pos = p - begin;
#endif
	      PUSH (candidates, strengthened);
#if 0
	      if (candidates.begin != begin)
		{
		  begin = candidates.begin;
		  end = candidates.end;
		  p = begin + pos;
		}
#endif
	    }
	}
      if (ring->level)
	backtrack (ring, 0);
    }
#if 0
  if (p != end && !(*p)->vivify)
    while (p != end)
      (*p++)->vivify = true;
#else
  for (all_pointers_on_stack (struct watch, watch, candidates))
    watch->vivify = true;
#endif
  RELEASE (candidates);
  very_verbose (ring,
                "vivified %zu clauses %.0f%% from %zu tried %.0f%% "
                "after %" PRIu64 " ticks (%s)",
                vivified, percent (vivified, tried),
		tried, percent (tried, scheduled),
		PROBING_TICKS - probing_ticks_before,
		(PROBING_TICKS > limit ? "limit hit" : "completed"));
  very_verbose (ring, "implied %zu clauses %.0f%% of vivified "
                "and strengthened %zu clauses %.0f%%",
		implied, percent (implied, vivified),
		strengthened, percent (strengthened, vivified));
  report (ring, 'v');
  STOP (ring, vivify);
}
