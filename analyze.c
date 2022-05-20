#include "analyze.h"
#include "assign.h"
#include "backtrack.h"
#include "bump.h"
#include "export.h"
#include "macros.h"
#include "minimize.h"
#include "ring.h"
#include "trace.h"
#include "utilities.h"

static void
bump_reason (struct watch *watch)
{
  if (!watch->redundant)
    return;
  if (watch->clause->glue <= TIER1_GLUE_LIMIT)
    return;
  if (watch->clause->glue <= TIER2_GLUE_LIMIT)
    watch->used = 2;
  else
    watch->used = 1;
}

static void
bump_reason_side_literal (struct ring *ring, unsigned lit)
{
  unsigned idx = IDX (lit);
  struct variable *v = ring->variables + idx;
  if (!v->level)
    return;
  if (v->seen)
    return;
  v->seen = true;
  PUSH (ring->analyzed, idx);
  if (ring->stable)
    bump_variable_on_heap (ring, idx);
}

static void
bump_reason_side_literals (struct ring *ring)
{
  for (all_elements_on_stack (unsigned, lit, ring->clause))
    {
      struct variable *v = VAR (lit);
      if (!v->level)
	continue;
      struct watch *reason = v->reason;
      if (!reason)
	continue;
      assert (v->seen || v->shrinkable);
      if (binary_pointer (reason))
	{
	  assert (NOT (lit) == lit_pointer (reason));
	  bump_reason_side_literal (ring, other_pointer (reason));
	}
      else
	{
	  struct clause *clause = reason->clause;
	  const unsigned not_lit = NOT (lit);
	  for (all_literals_in_clause (other, clause))
	    if (other != not_lit)
	      bump_reason_side_literal (ring, other);
	}
    }
}

void
clear_analyzed (struct ring *ring)
{
  struct unsigneds *analyzed = &ring->analyzed;
  struct variable *variables = ring->variables;
  for (all_elements_on_stack (unsigned, idx, *analyzed))
    {
      struct variable *v = variables + idx;
      assert (v->seen);
      v->seen = false;
    }
  CLEAR (*analyzed);

  struct unsigneds *levels = &ring->levels;
  bool *used = ring->used;
  for (all_elements_on_stack (unsigned, used_level, *levels))
      used[used_level] = false;
  CLEAR (*levels);
}

#define ANALYZE_LITERAL(OTHER) \
do { \
  if (OTHER == uip) \
    break; \
  assert (ring->values[OTHER] < 0); \
  unsigned OTHER_IDX = IDX (OTHER); \
  struct variable *V = variables + OTHER_IDX; \
  unsigned OTHER_LEVEL = V->level; \
  if (!OTHER_LEVEL) \
    break; \
  if (V->seen) \
    break; \
  V->seen = true; \
  PUSH (*analyzed, OTHER_IDX); \
  if (ring->stable) \
    bump_variable_on_heap (ring, OTHER_IDX); \
  if (OTHER_LEVEL == level) \
    { \
      open++; \
      break; \
    } \
  PUSH (*clause, OTHER); \
  if (!used[OTHER_LEVEL]) \
    { \
      glue++; \
      used[OTHER_LEVEL] = true; \
      PUSH (*levels, OTHER_LEVEL); \
      if (OTHER_LEVEL > jump) \
	jump = OTHER_LEVEL; \
    } \
} while (0)

bool
analyze (struct ring *ring, struct watch *reason)
{
  assert (!ring->inconsistent);
#if 0
  for (all_variables (v))
    assert (!v->seen), assert (!v->poison), assert (!v->minimize),
      assert (!v->shrinkable);
#endif
  if (!ring->level)
    {
      set_inconsistent (ring, "conflict on root-level produces empty clause");
      trace_add_empty (&ring->trace);
      return false;
    }
  struct unsigneds *clause = &ring->clause;
  struct unsigneds *analyzed = &ring->analyzed;
  struct unsigneds *levels = &ring->levels;
  assert (EMPTY (*clause));
  assert (EMPTY (*analyzed));
  assert (EMPTY (*levels));
  bool *used = ring->used;
  struct variable *variables = ring->variables;
  struct ring_trail *trail = &ring->trail;
  unsigned *t = trail->end;
  PUSH (*clause, INVALID);
  const unsigned level = ring->level;
  unsigned uip = INVALID, jump = 0, glue = 0, open = 0;
  for (;;)
    {
      LOGWATCH (reason, "analyzing");
      if (binary_pointer (reason))
	{
	  unsigned lit = lit_pointer (reason);
	  unsigned other = other_pointer (reason);
	  ANALYZE_LITERAL (lit);
	  ANALYZE_LITERAL (other);
	}
      else
	{
	  bump_reason (reason);
	  for (all_literals_in_clause (lit, reason->clause))
	    ANALYZE_LITERAL (lit);
	}
      do
	{
	  assert (t > ring->trail.begin);
	  uip = *--t;
	}
      while (!VAR (uip)->seen);
      if (!--open)
	break;
      reason = variables[IDX (uip)].reason;
      assert (reason);
    }
  LOG ("back jump level %u", jump);
  struct averages *averages = ring->averages + ring->stable;
  update_average (&averages->level, SLOW_ALPHA, jump);
  LOG ("glucose level (LBD) %u", glue);
  update_average (&averages->glue.slow, SLOW_ALPHA, glue);
  update_average (&averages->glue.fast, FAST_ALPHA, glue);
  unsigned assigned = SIZE (ring->trail);
  double filled = percent (assigned, ring->size);
  LOG ("assigned %u variables %.0f%% filled", assigned, filled);
  update_average (&averages->trail, SLOW_ALPHA, filled);
  unsigned *literals = clause->begin;
  const unsigned not_uip = NOT (uip);
  literals[0] = not_uip;
  LOGTMP ("first UIP %s", LOGLIT (uip));
  shrink_or_minimize_clause (ring, glue);
  bump_reason_side_literals (ring);
  if (ring->stable)
    bump_score_increment (ring);
  else
    sort_and_bump_analyzed_variables_on_queue (ring);
  backtrack (ring, level - 1);
  update_best_and_target_phases (ring);
  if (jump < level - 1)
    backtrack (ring, jump);
  unsigned size = SIZE (*clause);
  assert (size);
  if (size == 1)
    {
      trace_add_unit (&ring->trace, not_uip);
      assign_ring_unit (ring, not_uip);
      ring->iterating = true;
    }
  else
    {
      unsigned other = literals[1];
      struct watch *learned;
      if (size == 2)
	{
	  assert (VAR (other)->level == jump);
	  learned = new_local_binary_clause (ring, true, not_uip, other);
	  trace_add_binary (&ring->trace, not_uip, other);
	  export_binary (ring, learned);
	}
      else
	{
	  if (VAR (other)->level != jump)
	    {
	      unsigned *p = literals + 2, replacement;
	      while (assert (p != clause->end),
		     VAR (replacement = *p)->level != jump)
		p++;
	      literals[1] = replacement;
	      *p = other;
	    }
	  struct clause *clause =
	    new_large_clause (size, literals, true, glue);
	  LOGCLAUSE (clause, "new");
	  learned = watch_first_two_literals_in_large_clause (ring, clause);
	  assert (!binary_pointer (learned));
	  trace_add_clause (&ring->trace, clause);
	  if (glue == 1)
	    export_glue1_clause (ring, clause);
	  else if (glue <= TIER1_GLUE_LIMIT)
	    export_tier1_clause (ring, clause);
	  else if (glue <= TIER2_GLUE_LIMIT)
	    export_tier2_clause (ring, clause);
	}
      assign_with_reason (ring, not_uip, learned);
    }
  CLEAR (*clause);

  clear_analyzed (ring);

  return true;
}
