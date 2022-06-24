#include "allocate.h"
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

struct vivifier
{
  struct ring * ring;
  struct unsigneds candidates;
  struct unsigneds decisions;
  struct unsigneds sorted;
  unsigned * counts;
};

static void
init_vivifier (struct vivifier * vivifier, struct ring * ring)
{
  vivifier->ring = ring;
  INIT (vivifier->candidates);
  INIT (vivifier->decisions);
  INIT (vivifier->sorted);
  vivifier->counts =
    allocate_and_clear_array (2 * ring->size, sizeof (unsigned));
}

static void
release_vivifier (struct vivifier * vivifier)
{
  RELEASE (vivifier->candidates);
  RELEASE (vivifier->decisions);
  RELEASE (vivifier->sorted);
  free (vivifier->counts);
}

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
reschedule_vivification_candidates (struct vivifier * vivifier)
{
  struct unsigneds * candidates = &vivifier->candidates;
  struct ring * ring = vivifier->ring;
  assert (EMPTY (*candidates));
  for (all_redundant_watchers (watcher))
    if (watcher->vivify && !watcher->garbage)
      PUSH (*candidates, watcher_to_index (ring, watcher));
  size_t size = SIZE (*candidates);
  sort_redundant_watcher_indices (ring, size, candidates->begin);
  return size;
}

static size_t
schedule_vivification_candidates (struct vivifier * vivifier)
{
  struct unsigneds * candidates = &vivifier->candidates;
  struct ring * ring = vivifier->ring;
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
vivify_strengthen (struct ring *ring, struct watch *candidate,
                   struct unsigneds * decisions)
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
	  for (all_watcher_literals (other, watcher))
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
      CLEAR (*decisions);
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

static bool
less_vivification_probe (struct ring *ring, unsigned a, unsigned b)
{
  signed char *values = ring->values;
  signed char a_value = values[a];
  signed char b_value = values[b];
  if (a_value && !b_value)
    return true;
  if (!a_value && b_value)
    return false;
  if (a_value && b_value)
    return a < b;
  assert (!a_value);
  assert (!b_value);
  unsigned a_idx = IDX (a);
  unsigned b_idx = IDX (b);
  assert (a_idx != b_idx);
  if (ring->stable)
    {
      double a_score = ring->heap.nodes[a_idx].score;
      double b_score = ring->heap.nodes[b_idx].score;
      if (a_score > b_score)
	return true;
      if (a_score < b_score)
	return false;
    }
  else
    {
      uint64_t a_stamp = ring->queue.links[a_idx].stamp;
      uint64_t b_stamp = ring->queue.links[b_idx].stamp;
      if (a_stamp > b_stamp)
	return true;
      if (a_stamp < b_stamp)
	return false;
    }
  return a < b;
}

static void
sort_vivification_probes (struct ring *ring, struct unsigneds *sorted)
{
  if (SIZE (*sorted) < 2)
    return;
  unsigned *begin = sorted->begin;
  unsigned *end = sorted->end;
  for (unsigned *p = begin; p + 1 != end; p++)
    for (unsigned *q = p + 1; q != end; q++)
      if (less_vivification_probe (ring, *q, *p))
	SWAP (unsigned, *p, *q);
}

static unsigned
vivify_watcher (struct ring *ring,
		struct unsigneds *decisions, struct unsigneds *sorted,
		unsigned idx)
{
  assert (SIZE (*decisions) == ring->level);

  struct watcher *watcher = index_to_watcher (ring, idx);
  assert (watched_vivification_candidate (watcher));
  watcher->vivify = false;

  signed char *values = ring->values;
  struct clause *clause = watcher->clause;

  if (watcher->glue > TIER1_GLUE_LIMIT &&
      clause->size > VIVIFY_CLAUSE_SIZE_LIMIT)
    return 0;

  for (all_literals_in_clause (lit, clause))
    if (values[lit] > 0 && !VAR (lit)->level)
      {
	LOGCLAUSE (clause, "root-level satisfied");
	mark_garbage_watcher (ring, watcher);
	return 0;
      }

  LOGCLAUSE (clause, "trying to vivify");
  ring->statistics.vivify.tried++;

  for (unsigned level = 0; level != SIZE (*decisions); level++)
    {
      unsigned decision = decisions->begin[level];
      assert (VAR (decision)->level == level + 1);
      assert (!VAR (decision)->reason);
      bool found = false;
      for (all_literals_in_clause (lit, clause))
	if (NOT (lit) == decision)
	  {
	    found = true;
	    break;
	  }
      if (found)
	{
	  assert (VAR (decision)->level == level + 1);
	  assert (!VAR (decision)->reason);
	  signed char value = values[decision];
	  assert (value);
	  if (value > 0)
	    {
	      LOG ("reusing decision %s", LOGLIT (decision));
	      continue;
	    }
	  LOG ("decision %s with opposite phase", LOGLIT (decision));
	}
      else
	LOG ("decision %s not in clause", LOGLIT (decision));
      assert (level < ring->level);
      backtrack (ring, level);
      RESIZE (*decisions, level);
      break;
    }

  if (!EMPTY (*decisions))
    ring->statistics.vivify.reused++;

  CLEAR (*sorted);
  for (all_literals_in_clause (lit, clause))
    {
      signed char value = values[lit];
      struct variable *v = VAR (lit);
      if (value && v->level && !v->reason)
	{
	  LOG ("skipping reused decision %s", LOGLIT (lit));
	  assert (!v->reason);
	  assert (value < 0);
	  assert (v->level);
	  continue;
	}
      PUSH (*sorted, lit);
    }

  sort_vivification_probes (ring, sorted);

  unsigned non_root_level_falsified = 0;
  bool clause_implied = false;

  for (all_elements_on_stack (unsigned, lit, *sorted))
    {
      signed char value = values[lit];

      if (!value)
	{
	  ring->level++;
	  ring->statistics.contexts[PROBING_CONTEXT].decisions++;
	  unsigned not_lit = NOT (lit);
#ifdef LOGGING
	  if (ring->stable)
	    LOG ("assuming %s score %g",
		 LOGLIT (not_lit), ring->heap.nodes[IDX (not_lit)].score);
	  else
	    LOG ("assuming %s stamp %" PRIu64,
		 LOGLIT (not_lit), ring->queue.links[IDX (not_lit)].stamp);
#endif
	  assign_decision (ring, not_lit);
	  PUSH (*decisions, not_lit);
	  if (!ring_propagate (ring, false, clause))
	    continue;

	  LOGCLAUSE (clause, "vivify implied after conflict");
	IMPLIED:
	  ring->statistics.vivify.succeeded++;
	  ring->statistics.vivify.implied++;
	  mark_garbage_watcher (ring, watcher);
	  clause_implied = true;
	  break;
	}

      if (value > 0)
	{
	  LOGCLAUSE (clause,
		     "vivify implied (through literal %s)", LOGLIT (lit));
	  goto IMPLIED;
	}

      assert (value < 0);
      struct variable *v = VAR (lit);
      non_root_level_falsified += !!v->level;
    }

  unsigned res = 0;

  if (!clause_implied && non_root_level_falsified)
    {
      ring->statistics.vivify.succeeded++;
      ring->statistics.vivify.strengthened++;

      struct watch *watch = tag_index (true, idx, INVALID_LIT);
      struct watch *strengthened =
        vivify_strengthen (ring, watch, decisions);
      watcher = index_to_watcher (ring, idx);
      mark_garbage_watcher (ring, watcher);

      if (ring->inconsistent)
	return 0;

      if (strengthened)
	{
	  if (!is_binary_pointer (strengthened))
	    {
#ifndef NDEBUG
	      struct watcher *swatcher = get_watcher (ring, strengthened);
	      assert (watched_vivification_candidate (swatcher));
#endif
	      res = index_pointer (strengthened);
	    }
	}
    }

  if (!clause_implied && !non_root_level_falsified)
    LOGCLAUSE (clause, "vivification failed of");

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

  struct vivifier vivifier;
  init_vivifier (&vivifier, ring);

  size_t rescheduled = reschedule_vivification_candidates (&vivifier);
  very_verbose (ring, "rescheduling %zu vivification candidates",
		rescheduled);
  size_t scheduled = schedule_vivification_candidates (&vivifier);
  very_verbose (ring, "scheduled %zu vivification candidates in total",
		scheduled);
#ifdef QUIET
  (void) rescheduled, (void) scheduled;
#endif

  uint64_t implied = ring->statistics.vivify.implied;
  uint64_t strengthened = ring->statistics.vivify.strengthened;
  uint64_t vivified = ring->statistics.vivify.succeeded;
  uint64_t tried = ring->statistics.vivify.tried;

  struct unsigneds decisions;
  struct unsigneds sorted;
  INIT (decisions);
  INIT (sorted);

  size_t i = 0;
  while (i != SIZE (vivifier.candidates))
    {
      if (PROBING_TICKS > limit)
	break;
      if (terminate_ring (ring))
	break;
      if (import_shared (ring))
	{
	  if (ring->inconsistent)
	    break;
	  if (ring->level)
	    backtrack (ring, ring->level - 1);
	  RESIZE (decisions, ring->level);
	  if (ring_propagate (ring, false, 0))
	    {
	      set_inconsistent (ring, "propagation of imported clauses "
				"during vivification fails");
	      break;
	    }
	}
      unsigned idx = vivifier.candidates.begin[i++];
      unsigned sidx = vivify_watcher (ring, &decisions, &sorted, idx);
      if (sidx)
	PUSH (vivifier.candidates, sidx);
      else if (ring->inconsistent)
	break;
    }

  if (!ring->inconsistent && ring->level)
    backtrack (ring, 0);

  if (i != SIZE (vivifier.candidates))
    while (i != SIZE (vivifier.candidates))
      index_to_watcher (ring, vivifier.candidates.begin[i++])->vivify = true;

  release_vivifier (&vivifier);

  implied = ring->statistics.vivify.implied - implied;
  strengthened = ring->statistics.vivify.strengthened - strengthened;
  vivified = ring->statistics.vivify.succeeded - vivified;
  tried = ring->statistics.vivify.tried - tried;

  very_verbose (ring,
		"vivified %" PRIu64 " clauses %.0f%% from %" PRIu64
		" tried %.0f%% " "after %" PRIu64 " ticks (%s)", vivified,
		percent (vivified, tried), tried, percent (tried, scheduled),
		PROBING_TICKS - probing_ticks_before,
		(PROBING_TICKS > limit ? "limit hit" : "completed"));

  very_verbose (ring, "implied %" PRIu64 " clauses %.0f%% of vivified "
		"and strengthened %" PRIu64 " clauses %.0f%%",
		implied, percent (implied, vivified),
		strengthened, percent (strengthened, vivified));

  verbose_report (ring, 'v', !(implied || strengthened));
  STOP (ring, vivify);
}
