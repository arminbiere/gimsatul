#include "definition.h"
#include "eliminate.h"
#include "macros.h"
#include "message.h"
#include "profile.h"
#include "simplify.h"
#include "trace.h"
#include "utilities.h"

#include <string.h>
#include <inttypes.h>

static bool
literal_with_too_many_occurrences (struct ruler *ruler, unsigned lit)
{
  ruler->statistics.ticks.elimination++;
  struct clauses *clauses = &OCCURRENCES (lit);
  size_t size = SIZE (*clauses);
  size_t occurrence_limit = ruler->options.occurrence_limit;
  bool res = size > occurrence_limit;
  if (res)
    ROG ("literal %s occurs %zu times (limit %zu)",
	 ROGLIT (lit), size, occurrence_limit);
  return res;
}

static bool
clause_with_too_many_occurrences (struct ruler *ruler,
				  struct clause *clause, unsigned except)
{
  if (binary_pointer (clause))
    {
      unsigned other = other_pointer (clause);
      return literal_with_too_many_occurrences (ruler, other);
    }

  size_t clause_size_limit = ruler->options.clause_size_limit;
  if (clause->size > clause_size_limit)
    {
      ROGCLAUSE (clause, "antecedent size %zu exceeded by",
                 clause_size_limit);
      return true;
    }

  for (all_literals_in_clause (other, clause))
    if (other != except && literal_with_too_many_occurrences (ruler, other))
      return true;

  return false;
}

static size_t
actual_occurrences (struct clauses *clauses)
{
  struct clause **begin = clauses->begin, **q = begin;
  struct clause **end = clauses->end, **p = q;
  uint64_t ticks = 1 + cache_lines (end, begin);
  while (p != end)
    {
      struct clause *clause = *q++ = *p++;
      if (binary_pointer (clause))
	continue;
      ticks++;
      if (clause->garbage)
	q--;
    }

  clauses->end = q;
  return q - begin;
}

static bool
can_resolve_clause (struct simplifier *simplifier,
		    struct clause *clause, unsigned except)
{
  signed char *marks = simplifier->marks;
  struct ruler *ruler = simplifier->ruler;
  signed char *values = (signed char *) ruler->values;
  if (binary_pointer (clause))
    {
      unsigned other = other_pointer (clause);
      signed char value = values[other];
      if (value > 0)
	return false;
      if (value < 0)
	return true;
      signed char mark = marked_literal (marks, other);
      if (mark < 0)
	return false;
      return true;
    }
  else
    {
      assert (!clause->garbage);
      assert (clause->size <= ruler->options.clause_size_limit);
      ruler->statistics.ticks.elimination++;
      for (all_literals_in_clause (lit, clause))
	{
	  if (lit == except)
	    continue;
	  signed char value = values[lit];
	  if (value > 0)
	    return false;
	  if (value < 0)
	    continue;
	  signed char mark = marked_literal (marks, lit);
	  if (mark < 0)
	    return false;
	}
      return true;
    }
}

static bool
is_elimination_candidate (struct simplifier *simplifier, unsigned idx)
{
  if (simplifier->eliminated[idx])
    return false;

  struct ruler *ruler = simplifier->ruler;
  if (!ruler->eliminate[idx])
    return false;

  unsigned pivot = LIT (idx);
  if (ruler->values[pivot])
    return false;

  return true;
}

static bool
can_eliminate_variable (struct simplifier *simplifier, unsigned idx)
{
  if (!is_elimination_candidate (simplifier, idx))
    return false;

  struct ruler *ruler = simplifier->ruler;
  ROG ("trying next elimination candidate %s", ROGVAR (idx));
  ruler->eliminate[idx] = false;

  size_t occurrence_limit = ruler->options.occurrence_limit;

  unsigned pivot = LIT (idx);
  struct clauses *pos_clauses = &OCCURRENCES (pivot);
  ROG ("flushing garbage clauses of %s", ROGLIT (pivot));
  size_t pos_size = actual_occurrences (pos_clauses);
  if (pos_size > occurrence_limit)
    {
      ROG ("pivot literal %s occurs %zu times (limit %zu)",
	   ROGLIT (pivot), pos_size, occurrence_limit);
      return false;
    }

  unsigned not_pivot = NOT (pivot);
  struct clauses *neg_clauses = &OCCURRENCES (not_pivot);
  ROG ("flushing garbage clauses of %s", ROGLIT (not_pivot));
  size_t neg_size = actual_occurrences (neg_clauses);
  if (neg_size > occurrence_limit)
    {
      ROG ("negative pivot literal %s occurs %zu times (limit %zu)",
	   ROGLIT (not_pivot), neg_size, occurrence_limit);
      return false;
    }

  size_t occurrences = pos_size + neg_size;
  ROG ("candidate %s has %zu = %zu + %zu occurrences",
       ROGVAR (idx), occurrences, pos_size, neg_size);

  for (all_clauses (clause, *pos_clauses))
    if (clause_with_too_many_occurrences (ruler, clause, pivot))
      return false;

  for (all_clauses (clause, *neg_clauses))
    if (clause_with_too_many_occurrences (ruler, clause, not_pivot))
      return false;

  size_t resolvents = 0;
  size_t resolutions = 0;
  unsigned bound = ruler->limits.bound;
  size_t limit = occurrences + bound;
  ROG ("actual limit %zu = occurrences %zu + bound %u",
       limit, occurrences, bound);

#ifdef LOGGING
  uint64_t ticks_before = ruler->statistics.ticks.elimination;
#endif

  if (find_definition (simplifier, pivot))
    {
      struct clauses *gate = simplifier->gate;
      struct clauses *nogate = simplifier->nogate;

      for (unsigned i = 0; i != 2; i++)
	{
	  for (all_clauses (pos_clause, gate[i]))
	    {
	      ruler->statistics.ticks.elimination++;
	      mark_clause (simplifier->marks, pos_clause, pivot);
	      for (all_clauses (neg_clause, nogate[!i]))
		{
		  if (elimination_ticks_limit_hit (simplifier))
		    break;
		  resolutions++;
		  if (can_resolve_clause (simplifier, neg_clause, not_pivot))
		    if (resolvents++ == limit)
		      break;
		}
	      unmark_clause (simplifier->marks, pos_clause, pivot);
	      if (elimination_ticks_limit_hit (simplifier))
		break;
	    }
	  SWAP (unsigned, pivot, not_pivot);
	  if (resolvents > limit)
	    break;
	  if (elimination_ticks_limit_hit (simplifier))
	    break;
	}
    }
  else
    {
      for (all_clauses (pos_clause, *pos_clauses))
	{
	  ruler->statistics.ticks.elimination++;
	  mark_clause (simplifier->marks, pos_clause, pivot);
	  for (all_clauses (neg_clause, *neg_clauses))
	    {
	      if (elimination_ticks_limit_hit (simplifier))
		break;
	      resolutions++;
	      if (can_resolve_clause (simplifier, neg_clause, not_pivot))
		if (resolvents++ == limit)
		  break;
	    }
	  unmark_clause (simplifier->marks, pos_clause, pivot);
	  if (elimination_ticks_limit_hit (simplifier))
	    break;
	}

      CLEAR (*simplifier->gate);
    }

  ROG ("candidate %s has %zu = %zu + %zu occurrences "
       "took %zu resolutions %" PRIu64 " ticks total %" PRIu64,
       ROGLIT (pivot), limit, pos_size, neg_size,
       resolutions, ruler->statistics.ticks.elimination - ticks_before,
       ruler->statistics.ticks.elimination);

  if (elimination_ticks_limit_hit (simplifier))
    return false;

  if (resolvents == limit)
    ROG ("number of resolvents %zu matches limit %zu", resolvents, limit);
  else if (resolvents < limit)
    ROG ("number of resolvents %zu stays below limit %zu", resolvents, limit);
  else
    ROG ("number of resolvents exceeds limit %zu", limit);

  return resolvents <= limit;
}

static bool
add_first_antecedent_literals (struct simplifier *simplifier,
			       struct clause *clause, unsigned pivot)
{
  struct ruler *ruler = simplifier->ruler;
  ROGCLAUSE (clause, "1st %s antecedent", ROGLIT (pivot));
  signed char *values = (signed char *) ruler->values;
  struct unsigneds *resolvent = &simplifier->resolvent;
  if (binary_pointer (clause))
    {
      unsigned other = other_pointer (clause);
      signed char value = values[other];
      if (value > 0)
	{
	  ROG ("1st antecedent %s satisfied", ROGLIT (other));
	  return false;
	}
      if (value < 0)
	return true;
      PUSH (*resolvent, other);
    }
  else
    {
      assert (!clause->garbage);
      bool found_pivot = false;
      for (all_literals_in_clause (lit, clause))
	{
	  if (lit == pivot)
	    {
	      found_pivot = true;
	      continue;
	    }
	  signed char value = values[lit];
	  if (value > 0)
	    {
	      ROG ("1st antecedent %s satisfied", ROGLIT (lit));
	      return false;
	    }
	  if (value < 0)
	    continue;
	  PUSH (*resolvent, lit);
	}
      assert (found_pivot), (void) found_pivot;
    }
  return true;
}

static bool
add_second_antecedent_literals (struct simplifier *simplifier,
				struct clause *clause, unsigned not_pivot)
{
  struct ruler *ruler = simplifier->ruler;
  ROGCLAUSE (clause, "2nd %s antecedent", ROGLIT (not_pivot));
  signed char *values = (signed char *) ruler->values;
  signed char *marks = simplifier->marks;
  struct unsigneds *resolvent = &simplifier->resolvent;
  if (binary_pointer (clause))
    {
      unsigned other = other_pointer (clause);
      signed char value = values[other];
      if (value > 0)
	{
	  ROG ("2nd antecedent %s satisfied", ROGLIT (other));
	  return false;
	}
      if (value < 0)
	return true;
      signed char mark = marked_literal (marks, other);
      if (mark < 0)
	{
	  ROG ("2nd antecedent tautological through %s", ROGLIT (other));
	  return false;
	}
      if (mark > 0)
	return true;
      PUSH (*resolvent, other);
      return true;
    }
  else
    {
      assert (!clause->garbage);
      bool found_not_pivot = false;
      for (all_literals_in_clause (lit, clause))
	{
	  if (lit == not_pivot)
	    {
	      found_not_pivot = true;
	      continue;
	    }
	  signed char value = values[lit];
	  if (value > 0)
	    {
	      ROG ("2nd antecedent %s satisfied", ROGLIT (lit));
	      return false;
	    }
	  if (value < 0)
	    continue;
	  signed char mark = marked_literal (marks, lit);
	  if (mark < 0)
	    {
	      ROG ("2nd antecedent tautological through %s", ROGLIT (lit));
	      return false;
	    }
	  if (mark > 0)
	    continue;
	  PUSH (*resolvent, lit);
	}
      assert (found_not_pivot), (void) found_not_pivot;
      return true;
    }
}

static void
eliminate_variable (struct simplifier *simplifier, unsigned idx)
{
  struct ruler *ruler = simplifier->ruler;
  unsigned pivot = LIT (idx);
  if (ruler->values[pivot])
    return;
  ROG ("eliminating %s", ROGVAR (idx));
  assert (!simplifier->eliminated[idx]);
  simplifier->eliminated[idx] = true;
  ruler->statistics.eliminated++;
  assert (ruler->statistics.active);
  ruler->statistics.active--;
  ROG ("adding resolvents on %s", ROGVAR (idx));
  unsigned not_pivot = NOT (pivot);
  struct clauses *pos_clauses = &OCCURRENCES (pivot);
  struct clauses *neg_clauses = &OCCURRENCES (not_pivot);
  size_t resolvents = 0;
  signed char *marks = simplifier->marks;
  struct clauses *gate = simplifier->gate;
  if (EMPTY (*gate))
    {
      for (all_clauses (pos_clause, *pos_clauses))
	{
	  mark_clause (marks, pos_clause, pivot);
	  for (all_clauses (neg_clause, *neg_clauses))
	    {
	      assert (EMPTY (simplifier->resolvent));
	      if (add_first_antecedent_literals (simplifier,
						 pos_clause, pivot) &&
		  add_second_antecedent_literals (simplifier,
						  neg_clause, not_pivot))
		{
		  add_resolvent (simplifier);
		  resolvents++;
		}
	      CLEAR (simplifier->resolvent);
	      if (ruler->inconsistent)
		break;
	    }
	  unmark_clause (marks, pos_clause, pivot);
	  if (ruler->inconsistent)
	    break;
	}
    }
  else
    {
      ruler->statistics.definitions++;

      struct clauses *gate = simplifier->gate;
      struct clauses *nogate = simplifier->nogate;

      for (unsigned i = 0; i != 2; i++)
	{
	  for (all_clauses (pos_clause, gate[i]))
	    {
	      mark_clause (marks, pos_clause, pivot);
	      for (all_clauses (neg_clause, nogate[!i]))
		{
		  assert (EMPTY (simplifier->resolvent));
		  if (add_first_antecedent_literals (simplifier,
						     pos_clause, pivot) &&
		      add_second_antecedent_literals (simplifier,
						      neg_clause, not_pivot))
		    {
		      add_resolvent (simplifier);
		      resolvents++;
		    }
		  CLEAR (simplifier->resolvent);
		  if (ruler->inconsistent)
		    break;
		}
	      unmark_clause (marks, pos_clause, pivot);
	      if (ruler->inconsistent)
		break;
	    }
	  SWAP (unsigned, pivot, not_pivot);
	  if (ruler->inconsistent)
	    break;
	}
    }

  ROG ("added %zu resolvents on %s", resolvents, ROGVAR (idx));
  if (ruler->inconsistent)
    return;
  size_t pos_size = SIZE (*pos_clauses);
  size_t neg_size = SIZE (*neg_clauses);
  if (pos_size > neg_size)
    {
      SWAP (unsigned, pivot, not_pivot);
      SWAP (size_t, pos_size, neg_size);
      SWAP (struct clauses *, pos_clauses, neg_clauses);
    }
  ROG ("adding %zu clauses with %s to extension stack",
       pos_size, ROGLIT (pivot));
  struct unsigneds *extension = &ruler->extension[0];
  unsigned *unmap = ruler->unmap;
  for (all_clauses (clause, *pos_clauses))
    {
      ruler->statistics.weakened++;
      ROGCLAUSE (clause, "pushing weakened[%zu] witness literal %s",
		 ruler->statistics.weakened, ROGLIT (pivot));
      PUSH (*extension, INVALID);
      PUSH (*extension, unmap_literal (unmap, pivot));
      if (binary_pointer (clause))
	{
	  unsigned other = other_pointer (clause);
	  PUSH (*extension, unmap_literal (unmap, other));
	}
      else
	{
	  for (all_literals_in_clause (lit, clause))
	    if (lit != pivot)
	      PUSH (*extension, unmap_literal (unmap, lit));
	}
    }
  ruler->statistics.weakened++;
  ROG ("pushing weakened[%zu] unit %s",
       ruler->statistics.weakened, ROGLIT (not_pivot));
  PUSH (*extension, INVALID);
  PUSH (*extension, unmap_literal (unmap, not_pivot));
  recycle_clauses (simplifier, pos_clauses, pivot);
  recycle_clauses (simplifier, neg_clauses, not_pivot);
}

static void
gather_elimination_candidates (struct simplifier *simplifier,
			       struct unsigneds *candidates)
{
  struct ruler *ruler = simplifier->ruler;
  unsigned idx = ruler->compact;
  while (idx)
    if (is_elimination_candidate (simplifier, --idx))
      PUSH (*candidates, idx);
}

bool
eliminate_variables (struct simplifier *simplifier, unsigned round)
{
  struct ruler *ruler = simplifier->ruler;
  if (!ruler->options.eliminate)
    return false;
  if (elimination_ticks_limit_hit (simplifier))
    return false;
#ifndef QUIET
  double start_round = START (ruler, eliminate);
#endif
  assert (!ruler->eliminating);
  ruler->eliminating = true;

  struct unsigneds candidates;
  INIT (candidates);
  gather_elimination_candidates (simplifier, &candidates);
#ifndef QUIET
  unsigned variables = ruler->compact;
  unsigned scheduled = SIZE (candidates);
  verbose (0, "[%u] gathered %u elimination candidates %.0f%%",
	   round, scheduled, percent (scheduled, variables));
#endif
  unsigned eliminated = 0;

  while (!EMPTY (candidates))
    {
      if (ruler->inconsistent)
	break;
      if (elimination_ticks_limit_hit (simplifier))
	break;
      unsigned idx = POP (candidates);
      if (can_eliminate_variable (simplifier, idx))
	{
	  eliminate_variable (simplifier, idx);
	  eliminated++;
	}
      idx++;
    }

  unsigned remaining = SIZE (candidates);
  RELEASE (candidates);

  RELEASE (simplifier->resolvent);
  RELEASE (simplifier->gate[0]);
  RELEASE (simplifier->gate[1]);
  RELEASE (simplifier->nogate[0]);
  RELEASE (simplifier->nogate[1]);

  unsigned old_bound = ruler->limits.bound;
#ifndef QUIET
  double end_round = STOP (ruler, eliminate);
  message (0, "[%u] eliminated %u variables %.0f%% "
	   "with bound %u in %.2f seconds", round,
	   eliminated, percent (eliminated, ruler->compact),
	   old_bound, end_round - start_round);
#endif

  if (remaining)
    {
#ifndef QUIET
      unsigned completed = scheduled - remaining;
      message (0, "[%u] tried %u candidate variables %.0f%% "
	       "(%u remain %.0f%%)", round, completed,
	       percent (completed, variables),
	       remaining, percent (remaining, variables));
#endif
    }
  else
    {
      message (0, "[%u] all candidate variables 100%% tried", round);
      unsigned max_bound = ruler->options.eliminate_bound;
      unsigned new_bound;
      if (eliminated)
	new_bound = old_bound;
      else
	{
	  new_bound = old_bound ? 2 * old_bound : 1;
	  if (new_bound > max_bound)
	    new_bound = max_bound;
	}
      assert (old_bound <= new_bound);
#ifndef QUIET
      const char *reached_max_bound =
	new_bound == max_bound ? "maximum " : "";
#endif
      if (old_bound == new_bound)
	message (0, "[%u] keeping elimination bound at %s%u",
		 round, reached_max_bound, old_bound);
      else
	{
	  message (0, "[%u] increasing elimination bound to %s%u",
		   round, reached_max_bound, new_bound);
	  memset (ruler->eliminate, 1, ruler->compact);
	  ruler->limits.bound = new_bound;
	}
    }

  assert (ruler->eliminating);
  ruler->eliminating = false;

  return eliminated;
}
