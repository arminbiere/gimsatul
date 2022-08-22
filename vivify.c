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
#include "sort.h"
#include "utilities.h"
#include "vivify.h"

#include <inttypes.h>
#include <string.h>

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
    allocate_and_clear_array (2 * ring->size, sizeof *vivifier->counts);
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
watched_vivification_candidate (struct watcher *watcher, unsigned tier)
{
  assert (tier == 1 || tier == 2);
  if (watcher->garbage)
    return false;
  if (!watcher->redundant)
    return false;
  if (tier == 1)
    {
      if (watcher->glue > TIER1_GLUE_LIMIT)
	return false;
    }
  if (tier == 2)
    {
      if (watcher->glue <= TIER1_GLUE_LIMIT)
	return false;
      if (watcher->glue > TIER2_GLUE_LIMIT)
	return false;
    }
  return true;
}

static void
schedule_vivification_candidate (struct ring * ring, unsigned * counts,
                                 struct unsigneds * candidates,
                                 struct watcher * candidate)
{
  assert (!ring->level);
  signed char * values = ring->values;
  for (all_watcher_literals (lit, candidate))
    if (values[lit] > 0)
      {
	LOGCLAUSE (candidate->clause, "root-level satisfied");
	mark_garbage_watcher (ring, candidate);
	return;
      }
  for (all_watcher_literals (lit, candidate))
    if (!values[lit])
      counts[lit]++;
  PUSH (*candidates, watcher_to_index (ring, candidate));
}

static bool
smaller_vivification_literal (unsigned * counts, unsigned a, unsigned b)
{
  if (a == b)
    return false;
  unsigned c = counts[a];
  unsigned d = counts[b];
  if (c < d)
    return true;
  if (c > d)
    return false;
  return a > b;
}

static bool
better_vivification_candidate (unsigned * counts,
                               struct watcher * a, struct watcher * b)
{
  unsigned asize = a->size ? a->size : SIZE_WATCHER_LITERALS;
  unsigned bsize = b->size ? b->size : SIZE_WATCHER_LITERALS;
  struct clause * aclause = a->size ? 0 : a->clause;
  struct clause * bclause = b->size ? 0 : b->clause;
  unsigned * alits = a->aux, * blits = b->aux;
  unsigned * end_alits = alits + asize;
  unsigned * end_blits = blits + bsize;
  for (unsigned * p = alits, * q = blits;
       p != end_alits && q != end_blits; p++, q++)
    if (smaller_vivification_literal (counts, *p, *q))
      return false;
    else if (smaller_vivification_literal (counts, *q, *p))
      return true;
  if (asize < bsize)
    return false;
  if (asize > bsize)
    return true;
  if (aclause)
    asize = aclause->size;
  if (bclause)
    bsize = bclause->size;
  if (asize < bsize)
    return false;
  if (asize > bsize)
    return true;
  return a < b;
}

#define LESS_VIVIFICATION_CANDIDATE(A,B) \
  better_vivification_candidate(counts, \
                                index_to_watcher (ring, (A)), \
                                index_to_watcher (ring, (B)))

static void
sort_vivivification_candidates (struct ring * ring, unsigned * counts,
                                size_t size, unsigned * candidates)
{
  unsigned * end = candidates + size;
  for (unsigned * c = candidates; c != end; c++)
    {
      unsigned idx = *c;
      struct watcher * watcher = index_to_watcher (ring, idx);
      if (watcher->size)
	{
	  unsigned * lits = watcher->aux;
	  for (unsigned i = 0; i + 1 != watcher->size; i++)
	    for (unsigned j = i + 1; j != watcher->size; j++)
	      if (smaller_vivification_literal (counts, lits[i], lits[j]))
		SWAP (unsigned, lits[i], lits[j]);
	}
      else
	{
	  struct clause * clause = watcher->clause;
	  assert (clause->size > SIZE_WATCHER_LITERALS);
	  unsigned * src = clause->literals;
	  unsigned * end_src = src + clause->size;
	  unsigned * dst = watcher->aux;
	  unsigned * end_dst = dst + SIZE_WATCHER_LITERALS;
	  unsigned last = INVALID;
	  for (unsigned * q = dst; q != end_dst; q++)
	    {
	      unsigned next = INVALID;
	      for (unsigned * p = src; p != end_src; p++)
		{
		  unsigned other = *p;
		  if (last == INVALID ||
		      smaller_vivification_literal (counts, other, last))
		    if (next == INVALID ||
		        smaller_vivification_literal (counts, next, other))
		      next = other;
		}
	      assert (next != INVALID);
	      last = *q = next;
	    }
	}
    }

  SORT (unsigned, size, candidates, LESS_VIVIFICATION_CANDIDATE);

  for (unsigned * c = candidates; c != end; c++)
    {
      unsigned idx = *c;
      struct watcher * watcher = index_to_watcher (ring, idx);
      if (watcher->size)
	{
#ifdef LOGGING
	  do
	    {
	      unsigned size = watcher->size;
	      LOGPREFIX ("sorted glue %u size %u watcher[%u] "
			 "vivification candidate",
			 watcher->glue, size, idx);
	      unsigned * lits = watcher->aux;
	      unsigned * end_lits = lits + size;;
	      for (unsigned * p = lits; p != end_lits; p++)
		{
		  unsigned lit = *p;
		  printf (" %s#%u", LOGLIT (lit), counts[lit]);
		}
	      LOGSUFFIX ();
	    }
	  while (0);
#endif
	}
      else
	{
#ifdef LOGGING
	  do
	    {
	      struct clause * clause = watcher->clause;
	      LOGPREFIX ("sorted glue %u size %u watcher[%u] "
			 "vivification candidate",
			 watcher->glue, clause->size, idx);
	      unsigned * lits = watcher->aux;
	      unsigned * end_lits = lits + SIZE_WATCHER_LITERALS;
	      for (unsigned * p = lits; p != end_lits; p++)
		{
		  unsigned lit = *p;
		  printf (" %s#%u", LOGLIT (lit), counts[lit]);
		}
	      printf (" ... clause[%" PRIu64 "]", clause->id);
	      LOGSUFFIX ();
	    }
	  while (0);
#endif
	  watcher->aux[0] = 0;
	}
    }
}

static size_t
reschedule_vivification_candidates (struct vivifier * vivifier, unsigned tier)
{
  struct unsigneds * candidates = &vivifier->candidates;
  unsigned * counts = vivifier->counts;
  struct ring * ring = vivifier->ring;
  assert (EMPTY (*candidates));
  for (all_redundant_watchers (watcher))
    if (watcher->vivify && watched_vivification_candidate (watcher, tier))
      schedule_vivification_candidate (ring, counts, candidates, watcher);
  size_t size = SIZE (*candidates);
  sort_vivivification_candidates (ring, counts, size, candidates->begin);
  return size;
}

static size_t
schedule_vivification_candidates (struct vivifier * vivifier, unsigned tier)
{
  struct unsigneds * candidates = &vivifier->candidates;
  unsigned * counts = vivifier->counts;
  struct ring * ring = vivifier->ring;
  memset (counts, 0, sizeof (unsigned) * 2 * ring->size);
  size_t before = SIZE (*candidates);
  for (all_redundant_watchers (watcher))
    if (!watcher->vivify && watched_vivification_candidate (watcher, tier))
      schedule_vivification_candidate (ring, counts, candidates, watcher);
  size_t after = SIZE (*candidates);
  size_t delta = after - before;
  sort_vivivification_candidates (ring, counts, delta, candidates->begin + before);
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
      used[level] = 1; \
      PUSH (*levels, level); \
    } \
  open++; \
  if (!v->reason) \
    PUSH (*ring_clause, other); \
} while (0)

struct watch *
vivify_strengthen (struct vivifier * vivifier, struct watch *candidate)
{
  struct ring * ring = vivifier->ring;
  struct unsigneds * decisions = &vivifier->decisions;
  LOGWATCH (candidate, "vivify strengthening");
  assert (!is_binary_pointer (candidate));
  struct unsigneds *analyzed = &ring->analyzed;
  struct variable *variables = ring->variables;
  struct unsigneds *ring_clause = &ring->clause;
  struct unsigneds *levels = &ring->levels;
  unsigned *used = ring->used;
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
	{
	  ring->iterating = -1;
	  iterate (ring);
	}
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

static void
sort_vivification_probes (signed char * values, unsigned * counts,
                          struct unsigneds *sorted)
{
  if (SIZE (*sorted) < 2)
    return;
  unsigned *begin = sorted->begin;
  unsigned *end = sorted->end;
  for (unsigned *p = begin; p + 1 != end; p++)
    for (unsigned *q = p + 1; q != end; q++)
      if (smaller_vivification_literal (counts, *q, *p))
	SWAP (unsigned, *p, *q);
}

static unsigned
vivify_watcher (struct vivifier * vivifier, unsigned tier, unsigned idx)
{
  struct ring * ring = vivifier->ring;
  struct unsigneds * decisions = &vivifier->decisions;
  assert (SIZE (*decisions) == ring->level);

  struct watcher *watcher = index_to_watcher (ring, idx);
  assert (watched_vivification_candidate (watcher, tier));
  watcher->vivify = false;

  signed char *values = ring->values;
  struct clause *clause = watcher->clause;

  for (all_literals_in_clause (lit, clause))
    if (values[lit] > 0 && !VAR (lit)->level)
      {
	LOGCLAUSE (clause, "root-level satisfied");
	mark_garbage_watcher (ring, watcher);
	return 0;
      }

  LOGCLAUSE (clause, "trying to vivify watcher[%u]", idx);
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

  struct unsigneds * sorted = &vivifier->sorted;
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

  sort_vivification_probes (values, vivifier->counts, sorted);

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
	  clause_implied = true;
	  break;

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
      struct watch *strengthened = vivify_strengthen (vivifier, watch);
      watcher = index_to_watcher (ring, idx);
      mark_garbage_watcher (ring, watcher);

      if (ring->inconsistent)
	return 0;

      if (strengthened && !is_binary_pointer (strengthened))
	{
	  struct watcher *swatcher = get_watcher (ring, strengthened);
	  if (watched_vivification_candidate (swatcher, tier))
	    res = index_pointer (strengthened);
	}
    }

  if (!clause_implied && !non_root_level_falsified)
    LOGCLAUSE (clause, "vivification failed on");

  return res;
}

void
vivify_clauses (struct ring *ring)
{
  if (ring->inconsistent)
    return;
  if (!ring->options.vivify)
    return;
  START (ring, vivify);
  assert (SEARCH_TICKS >= ring->last.probing);

  uint64_t delta_search_ticks = SEARCH_TICKS - ring->last.probing;
  uint64_t delta_probing_ticks = VIVIFY_EFFORT * delta_search_ticks;
  verbose (ring, "total vivification effort of %" PRIu64 " = %g * %" PRIu64
	   " search ticks", delta_probing_ticks, (double) VIVIFY_EFFORT,
	   delta_search_ticks);

  double sum =
    RELATIVE_VIVIFY_TIER1_EFFORT + RELATIVE_VIVIFY_TIER2_EFFORT;

  for (unsigned tier = 2; tier >= 1; tier--)
    {
      if (ring->inconsistent)
	break;
      if (terminate_ring (ring))
	break;
      uint64_t probing_ticks_before = PROBING_TICKS;
      double effort;
      if (tier == 2)
	effort = RELATIVE_VIVIFY_TIER2_EFFORT;
      else
	effort = RELATIVE_VIVIFY_TIER1_EFFORT;

      double scale = effort / sum;
      uint64_t scaled_ticks = scale * delta_probing_ticks;

      verbose (ring, "tier%u vivification limit of %"
	       PRIu64 " vivification ticks %.0f%%",
	       tier, scaled_ticks, 100.0 *scale);

      uint64_t limit = probing_ticks_before + scaled_ticks;

      struct vivifier vivifier;
      init_vivifier (&vivifier, ring);

      size_t rescheduled =
        reschedule_vivification_candidates (&vivifier, tier);
      very_verbose (ring, "rescheduled %zu tier%u vivification candidates",
		    rescheduled, tier);
      size_t scheduled =
        schedule_vivification_candidates (&vivifier, tier);
      very_verbose (ring, "scheduled %zu tier%u vivification candidates in total",
		    scheduled, tier);
#ifdef QUIET
      (void) rescheduled, (void) scheduled;
#endif

      uint64_t implied = ring->statistics.vivify.implied;
      uint64_t strengthened = ring->statistics.vivify.strengthened;
      uint64_t vivified = ring->statistics.vivify.succeeded;
      uint64_t tried = ring->statistics.vivify.tried;

      struct unsigneds * decisions = &vivifier.decisions;;

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
	      RESIZE (*decisions, ring->level);
	      assert (ring->level == SIZE (*decisions));
	      if (ring_propagate (ring, false, 0))
		{
		  set_inconsistent (ring, "propagation of imported clauses "
				    "during vivification fails");
		  break;
		}
	    }
	  unsigned idx = vivifier.candidates.begin[i++];
	  unsigned sidx = vivify_watcher (&vivifier, tier, idx);
	  if (sidx)
	    PUSH (vivifier.candidates, sidx);
	  else if (ring->inconsistent)
	    break;
	}

      if (!ring->inconsistent && ring->level)
	backtrack (ring, 0);

      size_t final_scheduled = SIZE (vivifier.candidates);
      size_t remain = final_scheduled - i;
      if (remain)
	very_verbose (ring,
	              "incomplete vivification as %zu tier%u "
	              "candidates remain %.0f%%", remain, tier,
		      percent (remain, final_scheduled));
      else
	very_verbose (ring, "all %zu scheduled tier%u "
		      "vivification candidates tried",
	              final_scheduled, tier);

      while (i != final_scheduled)
	{
	  unsigned idx = vivifier.candidates.begin[i++];
	  struct watcher * watcher = index_to_watcher (ring, idx);
	  watcher->vivify = true;
	}

      release_vivifier (&vivifier);

      implied = ring->statistics.vivify.implied - implied;
      strengthened = ring->statistics.vivify.strengthened - strengthened;
      vivified = ring->statistics.vivify.succeeded - vivified;
      tried = ring->statistics.vivify.tried - tried;

      very_verbose (ring,
		    "vivified %" PRIu64 " tier%u clauses %.0f%% from %"
		    PRIu64 " tried %.0f%% " "after %" PRIu64 " ticks (%s)",
		    vivified, tier, percent (vivified, tried), tried,
		    percent (tried, scheduled),
		    PROBING_TICKS - probing_ticks_before,
		    (PROBING_TICKS > limit ? "limit hit" : "completed"));

      very_verbose (ring,
                    "implied %" PRIu64 " tier%u clauses %.0f%% of vivified "
		    "and strengthened %" PRIu64 " clauses %.0f%%",
		    implied, tier, percent (implied, vivified),
		    strengthened, percent (strengthened, vivified));

      verbose_report (ring, (tier == 1 ? 'v' : 'u'), !(implied || strengthened));
    }
  STOP (ring, vivify);
}
