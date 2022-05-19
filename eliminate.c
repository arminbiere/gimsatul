#include "definition.h"
#include "eliminate.h"
#include "message.h"
#include "profile.h"
#include "simplify.h"
#include "trace.h"
#include "utilities.h"

#include <string.h>

static bool
literal_with_too_many_occurrences (struct ruler * ruler, unsigned lit)
{
  ruler->statistics.ticks.elimination++;
  struct clauses * clauses = &OCCURRENCES (lit);
  size_t size = SIZE (*clauses);
  bool res = size > OCCURRENCE_LIMIT;
  if (res)
    ROG ("literal %s occurs %zu times (limit %zu)",
         ROGLIT (lit), size, (size_t) OCCURRENCE_LIMIT);
  return res;
}

static bool
clause_with_too_many_occurrences (struct ruler * ruler,
                                  struct clause * clause,
				  unsigned except)
{
  if (binary_pointer (clause))
    {
      unsigned other = other_pointer (clause);
      return literal_with_too_many_occurrences (ruler, other);
    }

  if (clause->size > CLAUSE_SIZE_LIMIT)
    {
      ROGCLAUSE (clause, "antecedent size %zu exceeded by",
                 (size_t) CLAUSE_SIZE_LIMIT);
      return true;
    }

  for (all_literals_in_clause (other, clause))
      if (other != except &&
	  literal_with_too_many_occurrences (ruler, other))
	return true;

  return false;
}

static size_t
actual_occurrences (struct clauses * clauses)
{
  struct clause ** begin = clauses->begin, ** q = begin;
  struct clause ** end = clauses->end, ** p = q;
  uint64_t ticks = 1 + cache_lines (end, begin);
  while (p != end)
    {
      struct clause * clause = *q++ = *p++;
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
can_resolve_clause (struct ruler * ruler,
                    struct clause * clause, unsigned except)
{
  signed char * values = (signed char*) ruler->values;
  signed char * marks = ruler->marks;
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
      assert (clause->size <= CLAUSE_SIZE_LIMIT);
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
can_eliminate_variable (struct ruler * ruler, unsigned idx, unsigned margin)
{
  if (ruler->eliminated[idx])
    return false;
  if (!ruler->eliminate[idx])
    return false;
  unsigned pivot = LIT (idx);
  if (ruler->values[pivot])
    return false;

  ROG ("trying next elimination candidate %s", ROGVAR (idx));
  ruler->eliminate[idx] = false;

  struct clauses * pos_clauses = &OCCURRENCES (pivot);
  ROG ("flushing garbage clauses of %s", ROGLIT (pivot));
  size_t pos_size = actual_occurrences (pos_clauses);
  if (pos_size > OCCURRENCE_LIMIT)
    {
      ROG ("pivot literal %s occurs %zu times (limit %zu)",
           ROGLIT (pivot), pos_size,
	   (size_t) OCCURRENCE_LIMIT);
      return false;
    }

  unsigned not_pivot = NOT (pivot);
  struct clauses * neg_clauses = &OCCURRENCES (not_pivot);
  ROG ("flushing garbage clauses of %s", ROGLIT (not_pivot));
  size_t neg_size = actual_occurrences (neg_clauses);
  if (neg_size > OCCURRENCE_LIMIT)
    {
      ROG ("negative pivot literal %s occurs %zu times (limit %zu)",
           ROGLIT (not_pivot),neg_size,
	   (size_t) OCCURRENCE_LIMIT);
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
  size_t limit = occurrences + margin;
  ROG ("actual limit %zu = occurrences %zu + margin %u",
       limit, occurrences, margin);
#if 0
  uint64_t ticks = ruler->statistics.ticks.elimination;
#endif

  if (find_definition (ruler, pivot))
    {
      struct clauses * gate = ruler->gate;
      struct clauses * nogate = ruler->nogate;

      for (unsigned i = 0; i != 2; i++)
	{
	  for (all_clauses (pos_clause, gate[i]))
	    {
	      ruler->statistics.ticks.elimination++;
	      mark_clause (ruler->marks, pos_clause, pivot);
	      for (all_clauses (neg_clause, nogate[!i]))
		{
		  if (elimination_ticks_limit_hit (ruler))
		    break;
		  resolutions++;
		  if (can_resolve_clause (ruler, neg_clause, not_pivot))
		    if (resolvents++ == limit)
		      break;
		}
	      unmark_clause (ruler->marks, pos_clause, pivot);
	      if (elimination_ticks_limit_hit (ruler))
		break;
	    }
	  SWAP (pivot, not_pivot);
	  if (resolvents > limit)
	    break;
	  if (elimination_ticks_limit_hit (ruler))
	    break;
	}
    }
  else
    {
      for (all_clauses (pos_clause, *pos_clauses))
	{
	  ruler->statistics.ticks.elimination++;
	  mark_clause (ruler->marks, pos_clause, pivot);
	  for (all_clauses (neg_clause, *neg_clauses))
	    {
	      if (elimination_ticks_limit_hit (ruler))
		break;
	      resolutions++;
	      if (can_resolve_clause (ruler, neg_clause, not_pivot))
		if (resolvents++ == limit)
		  break;
	    }
	  unmark_clause (ruler->marks, pos_clause, pivot);
	  if (elimination_ticks_limit_hit (ruler))
	    break;
	}

      CLEAR (*ruler->gate);
    }

#if 0
  message (0, "candidate %d has %zu = %zu + %zu occurrences took %zu resolutions %" PRIu64 " ticks total %" PRIu64,
        export_literal (pivot), limit, pos_size, neg_size, resolutions,
	ruler->statistics.ticks.elimination - ticks,
	ruler->statistics.ticks.elimination);
#endif

  if (elimination_ticks_limit_hit (ruler))
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
add_first_antecedent_literals (struct ruler * ruler,
                               struct clause * clause, unsigned pivot)
{
  ROGCLAUSE (clause, "1st %s antecedent", ROGLIT (pivot));
  signed char * values = (signed char*) ruler->values;
  struct unsigneds * resolvent = &ruler->resolvent;
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
add_second_antecedent_literals (struct ruler * ruler,
                                struct clause * clause, unsigned not_pivot)
{
  ROGCLAUSE (clause, "2nd %s antecedent", ROGLIT (not_pivot));
  signed char * values = (signed char*) ruler->values;
  signed char * marks = ruler->marks;
  struct unsigneds * resolvent = &ruler->resolvent;
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
eliminate_variable (struct ruler * ruler, unsigned idx)
{
  unsigned pivot = LIT (idx);
  if (ruler->values[pivot])
    return;
  ROG ("eliminating %s", ROGVAR (idx));
  assert (!ruler->eliminated[idx]);
  ruler->eliminated[idx] = true;
  ruler->statistics.eliminated++;
  assert (ruler->statistics.active);
  ruler->statistics.active--;
  ROG ("adding resolvents on %s", ROGVAR (idx));
  unsigned not_pivot = NOT (pivot);
  struct clauses * pos_clauses = &OCCURRENCES (pivot);
  struct clauses * neg_clauses = &OCCURRENCES (not_pivot);
  size_t resolvents = 0;
  signed char * marks = ruler->marks;
  struct clauses * gate = ruler->gate;
  if (EMPTY (*gate))
    {
      for (all_clauses (pos_clause, *pos_clauses))
	{
	  mark_clause (marks, pos_clause, pivot);
	  for (all_clauses (neg_clause, *neg_clauses))
	    {
	      assert (EMPTY (ruler->resolvent));
	      if (add_first_antecedent_literals (ruler,
		                                 pos_clause, pivot) &&
		  add_second_antecedent_literals (ruler,
		                                  neg_clause, not_pivot))
		{
		  add_resolvent (ruler);
		  resolvents++;
		}
	      CLEAR (ruler->resolvent);
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

      struct clauses * gate = ruler->gate;
      struct clauses * nogate = ruler->nogate;

      for (unsigned i = 0; i != 2; i++)
	{
	  for (all_clauses (pos_clause, gate[i]))
	    {
	      mark_clause (marks, pos_clause, pivot);
	      for (all_clauses (neg_clause, nogate[!i]))
		{
		  assert (EMPTY (ruler->resolvent));
		  if (add_first_antecedent_literals (ruler,
						     pos_clause, pivot) &&
		      add_second_antecedent_literals (ruler,
						      neg_clause, not_pivot))
		    {
		      add_resolvent (ruler);
		      resolvents++;
		    }
		  CLEAR (ruler->resolvent);
		  if (ruler->inconsistent)
		    break;
		}
	      unmark_clause (marks, pos_clause, pivot);
	      if (ruler->inconsistent)
		break;
	    }
	  SWAP (pivot, not_pivot);
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
      SWAP (pivot, not_pivot);
      SWAP (pos_size, neg_size);
      SWAP (pos_clauses, neg_clauses);
    }
  ROG ("adding %zu clauses with %s to extension stack",
       pos_size, ROGLIT (pivot));
  struct unsigneds * extension = ruler->extension;
  for (all_clauses (clause, *pos_clauses))
    {
      ROGCLAUSE (clause,
        "pushing with witness literal %s on extension stack",
	ROGLIT (pivot));
      PUSH (*extension, INVALID);
      PUSH (*extension, pivot);
      if (binary_pointer (clause))
	{
	  unsigned other = other_pointer (clause);
	  PUSH (*extension, other);
	}
      else
	{
	  for (all_literals_in_clause (lit, clause))
	    if (lit != pivot)
	      PUSH (*extension, lit);
	}
    }
  ROG ("pushing unit %s to extension stack", ROGLIT (not_pivot));
  PUSH (*extension, INVALID);
  PUSH (*extension, not_pivot);
  recycle_clauses (ruler, pos_clauses, pivot);
  recycle_clauses (ruler, neg_clauses, not_pivot);
}

bool
eliminate_variables (struct ruler * ruler, unsigned round)
{
  if (!ruler->options.eliminate)
    return false;
  if (elimination_ticks_limit_hit (ruler))
    return false;
  double start_round = START (ruler, eliminate);
  assert (!ruler->eliminating);
  ruler->eliminating = true;
  unsigned eliminated = 0;
  unsigned margin;
  if (round < 2)
    margin = 0;
  else
    {
      unsigned shift = (round - 1)/2;
      if (shift > LD_MAX_ELIMINATE_MARGIN)
	shift = LD_MAX_ELIMINATE_MARGIN;
      margin = 1u << shift;
      if (shift != LD_MAX_ELIMINATE_MARGIN && (round & 1))
	memset (ruler->eliminate, 1, ruler->size);
    }
  for (all_ruler_indices (idx))
    {
      if (ruler->inconsistent)
	break;
      if (elimination_ticks_limit_hit (ruler))
	break;
      if (can_eliminate_variable (ruler, idx, margin))
	{
	  eliminate_variable (ruler, idx);
	  eliminated++;
	}
    }
  RELEASE (ruler->resolvent);
  RELEASE (ruler->gate[0]);
  RELEASE (ruler->gate[1]);
  RELEASE (ruler->nogate[0]);
  RELEASE (ruler->nogate[1]);
  assert (ruler->eliminating);
  ruler->eliminating = false;
  double end_round = STOP (ruler, eliminate);
  message (0, "[%u] eliminated %u variables %.0f%% "
           "margin %u in %.2f seconds", round,
	   eliminated, percent (eliminated, ruler->size),
	   margin, end_round - start_round);
  return eliminated;
}
