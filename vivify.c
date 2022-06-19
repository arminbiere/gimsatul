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

#include <inttypes.h>

static inline bool
watched_vivification_candidate (struct watcher *watcher)
{
  if (watcher->garbage)
    return false;
  if (!watcher->redundant)
    return false;
  if (watcher->glue > TIER2_GLUE_LIMIT)
    return false;
  return true;
}

static size_t
reschedule_vivification_candidates (struct ring *ring,
				    struct unsigneds *candidates)
{
  assert (EMPTY (*candidates));
  for (all_redundant_watchers (watcher))
    if (watcher->vivify && !watcher->garbage)
      PUSH (*candidates, watcher_to_index (ring, watcher));
  size_t size = SIZE (*candidates);
  sort_redundant_watcher_indices (ring, size, candidates->begin);
  return size;
}

static size_t
schedule_vivification_candidates (struct ring *ring,
				  struct unsigneds *candidates)
{
  size_t before = SIZE (*candidates);
  for (all_redundant_watchers (watcher))
    if (!watcher->vivify && watched_vivification_candidate (watcher))
      PUSH (*candidates, watcher_to_index (ring, watcher));
  size_t after = SIZE (*candidates);
  size_t delta = after - before;
  sort_redundant_watcher_indices (ring, delta, candidates->begin + before);
  return after;
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
    PUSH (*ring_clause, other); \
} while (0)

struct watch *
vivify_strengthen (struct ring *ring, struct watch *candidate)
{
  LOGWATCH (candidate, "vivify strengthening");
  assert (!is_binary_pointer (candidate));
  struct unsigneds *analyzed = &ring->analyzed;
  struct variable *variables = ring->variables;
  struct unsigneds *ring_clause = &ring->clause;
  struct unsigneds *levels = &ring->levels;
  bool *used = ring->used;
  struct ring_trail *trail = &ring->trail;
  assert (EMPTY (*analyzed));
  assert (EMPTY (*ring_clause));
  struct watch *reason = candidate;
  unsigned *t = trail->end;
  unsigned open = 0;
  do
    {
      assert (reason);
      LOGWATCH (reason, "vivify analyzing");
      if (is_binary_pointer (reason))
	{
	  unsigned other = other_pointer (reason);
	  ANALYZE (other);
	}
      else
	{
	  struct watcher *watcher = get_watcher (ring, reason);
	  struct clause *reason_clause = watcher->clause;
	  for (all_literals_in_clause (other, reason_clause))
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
	      struct variable *v = variables + idx;
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
  unsigned size = SIZE (*ring_clause);
  assert (size);
  assert (size < get_clause (ring, candidate)->size);
  unsigned *literals = ring_clause->begin;
  struct watch *res = 0;
  if (size == 1)
    {
      unsigned unit = literals[0];
      assert (ring->level);
      backtrack (ring, 0);
      trace_add_unit (&ring->trace, unit);
      if (ring_propagate (ring, false, 0))
	set_inconsistent (ring,
			  "propagation of strengthened clause unit fails");
      else
	export_units (ring);
    }
  else if (size == 2)
    {
      unsigned lit = literals[0], other = literals[1];
      res = new_local_binary_clause (ring, true, lit, other);
      trace_add_binary (&ring->trace, lit, other);
      export_binary_clause (ring, res);
    }
  else
    {
      struct watcher *watcher = get_watcher (ring, candidate);
      unsigned glue = SIZE (*levels);
      LOG ("computed glue %u", glue);
      if (glue > watcher->glue)
	{
	  glue = watcher->glue;
	  LOG ("but candidate glue %u smaller", glue);
	}
#if 0
      message (ring, "vivification reduced glue to %u (size %u) from %u (size %u)",
               glue, size, watcher->glue, get_clause (ring, candidate)->size);
#endif
      assert (glue < size);
      struct clause *clause = new_large_clause (size, literals, true, glue);
      res = watch_first_two_literals_in_large_clause (ring, clause);
      trace_add_clause (&ring->trace, clause);
      export_large_clause (ring, clause);
    }
  clear_analyzed (ring);
  CLEAR (*ring_clause);
  return res;
}

static unsigned
vivify_watcher (struct ring * ring, unsigned idx)
{
  struct watcher * watcher = index_to_watcher (ring, idx);
  assert (watched_vivification_candidate (watcher));
  watcher->vivify = false;

  signed char *values = ring->values;
  struct clause *clause = watcher->clause;

  unsigned non_root_level_falsified = 0;
  bool clause_implied = false;

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
	  if (ring_propagate (ring, false, clause))
	    goto IMPLIED;
	}
      else
	{
	  const unsigned idx = IDX (lit);
	  struct variable *v = ring->variables + idx;
	  if (value > 0)
	    {
	      if (!v->level)
		{
		  LOGCLAUSE (clause, "root-level satisfied");
		  mark_garbage_watcher (ring, watcher);
		}
	      else
		{
		IMPLIED:
		  LOGCLAUSE (clause, "vivify implied");
#if 0
		  message (ring, "vivification implied glue %u (size %u)",
			   clause->glue, clause->size);
#endif
		  ring->statistics.vivify.succeeded++;
		  ring->statistics.vivify.implied++;

		  mark_garbage_watcher (ring, watcher);
		}
	      clause_implied = true;
	      break;
	    }
	  else if (value < 0)
	    {
	      if (v->level)
		non_root_level_falsified++;
	    }
	}
    }

  unsigned res = 0;

  if (!clause_implied && non_root_level_falsified)
    {
      ring->statistics.vivify.succeeded++;
      ring->statistics.vivify.strengthened++;

      struct watch *watch = tag_index (true, idx, INVALID_LIT);
      struct watch *strengthened = vivify_strengthen (ring, watch);
      watcher = index_to_watcher (ring, idx);
      mark_garbage_watcher (ring, watcher);

      if (ring->inconsistent)
	return 0;

      if (strengthened && !is_binary_pointer (strengthened))
	{
#ifndef NDEBUG
	  struct watcher *swatcher = get_watcher (ring, strengthened);
	  assert (watched_vivification_candidate (swatcher));
#endif
	  res = index_pointer (strengthened);
	}
    }

  if (ring->level)
    backtrack (ring, 0);

  return res;
}

void
vivify_clauses (struct ring *ring)
{
  if (ring->inconsistent)
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

  struct unsigneds candidates;
  INIT (candidates);

  size_t rescheduled = reschedule_vivification_candidates (ring, &candidates);
  very_verbose (ring, "rescheduling %zu vivification candidates",
		rescheduled);
  size_t scheduled = schedule_vivification_candidates (ring, &candidates);
  very_verbose (ring, "scheduled %zu vivification candidates in total",
		scheduled);
#ifdef QUIET
  (void) rescheduled, (void) scheduled;
#endif

  uint64_t implied = ring->statistics.vivify.implied;
  uint64_t strengthened = ring->statistics.vivify.strengthened;
  uint64_t vivified = ring->statistics.vivify.succeeded;
  uint64_t tried = 0;

  size_t i = 0;
  while (i != SIZE (candidates))
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
	      set_inconsistent (ring, "propagation of imported clauses "
				"during vivification fails");
	      break;
	    }
	}
      tried++;
      assert (!ring->level);
      unsigned idx = candidates.begin[i++];
      unsigned sidx = vivify_watcher (ring, idx);
      if (sidx)
	PUSH (candidates, sidx);
      else if (ring->inconsistent)
	break;
    }

  if (i != SIZE (candidates))
    while (i != SIZE (candidates))
      index_to_watcher (ring, candidates.begin[i++])->vivify = true;

  RELEASE (candidates);

  implied = ring->statistics.vivify.implied - implied;
  strengthened = ring->statistics.vivify.strengthened - strengthened;
  vivified = ring->statistics.vivify.succeeded - vivified;

  very_verbose (ring,
		"vivified %" PRIu64 " clauses %.0f%% from %" PRIu64 " tried %.0f%% "
		"after %" PRIu64 " ticks (%s)",
		vivified, percent (vivified, tried),
		tried, percent (tried, scheduled),
		PROBING_TICKS - probing_ticks_before,
		(PROBING_TICKS > limit ? "limit hit" : "completed"));

  very_verbose (ring, "implied %" PRIu64 " clauses %.0f%% of vivified "
		"and strengthened %" PRIu64 " clauses %.0f%%",
		implied, percent (implied, vivified),
		strengthened, percent (strengthened, vivified));

  verbose_report (ring, 'v', !(implied || strengthened));
  STOP (ring, vivify);
}
