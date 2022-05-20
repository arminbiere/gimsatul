#include "clause.h"
#include "macros.h"
#include "message.h"
#include "ruler.h"
#include "simplify.h"
#include "subsume.h"
#include "trace.h"
#include "utilities.h"

#include <string.h>

static bool
is_subsumption_candidate (struct simplifier * simplifier,
                          struct clause * clause)
{
  bool subsume = false;
  struct ruler * ruler = simplifier->ruler;
  ruler->statistics.ticks.subsumption++;
  if (clause->size <= CLAUSE_SIZE_LIMIT && !clause->garbage)
    {
      unsigned count = 0;
      for (all_literals_in_clause (lit, clause))
	if (simplifier->subsume[IDX (lit)])
	  if (count++)
	    break;
      subsume = (count > 1);
    }
  clause->subsume = subsume;
  return subsume;
}

static size_t
get_subsumption_candidates (struct simplifier * simplifier,
                            struct clause *** candidates_ptr)
{
  struct ruler * ruler = simplifier->ruler;
  struct clauses * clauses = &ruler->clauses;
  ruler->statistics.ticks.subsumption += SIZE (*clauses);
  const size_t size_count = CLAUSE_SIZE_LIMIT + 1;
  size_t count[size_count];
  memset (count, 0, sizeof count);
  for (all_clauses (clause, *clauses))
    if (is_subsumption_candidate (simplifier, clause))
      count[clause->size]++;
  size_t * c = count, * end = c + size_count;
  size_t pos = 0, size;
  while (c != end)
    size = *c, *c++ = pos, pos += size;
  size_t bytes = pos * sizeof (struct clause *);
  struct clause **candidates = allocate_block (bytes);
  for (all_clauses (clause, *clauses))
    if (clause->subsume)
      candidates[count[clause->size]++] = clause;
  memset (simplifier->subsume, 0, ruler->size);
  *candidates_ptr = candidates;
  return pos;
}

static struct clause *
find_subsuming_clause (struct simplifier * simplifier, unsigned lit,
                       bool strengthen_only, unsigned * remove_ptr)
{
  assert (!strengthen_only || marked_literal (simplifier->marks, lit) < 0);
  assert (strengthen_only || marked_literal (simplifier->marks, lit) > 0);
  struct ruler * ruler = simplifier->ruler;
  struct clauses * clauses = &OCCURRENCES (lit);
  unsigned resolved;
  size_t size_clauses = SIZE (*clauses);
  struct clause * res = 0;
  uint64_t ticks = 1;
  if (size_clauses <= OCCURRENCE_LIMIT)
    {
      signed char * marks = simplifier->marks;
      ticks += cache_lines (clauses->end, clauses->begin);
      for (all_clauses (clause, *clauses))
	{
	  resolved = strengthen_only ? lit : INVALID;
	  if (binary_pointer (clause))
	    {
	      unsigned other = other_pointer (clause);
	      signed char mark = marked_literal (marks, other);
	      if (mark > 0)
		{
		  res = clause;
		  break;
		}
	      if (mark < 0 && !strengthen_only)
		{
		  res = clause;
		  assert (resolved == INVALID);
		  resolved = other;
		  break;
		}
	    }
	  else
	    {
	      ticks++;
	      res = clause;
	      assert (!clause->garbage);
	      for (all_literals_in_clause (other, clause))
		{
		  signed char mark = marked_literal (marks, other);
		  if (!mark)
		    {
		      res = 0;
		      break;
		    }
		  if (mark < 0)
		    {
		      if (resolved == INVALID)
			resolved = other;
		      else
			{
			  res = 0;
			  break;
			}
		    }
		}
	      if (res)
		break;
	    }
	}
    }
  ruler->statistics.ticks.subsumption += ticks;
  if (res && resolved != INVALID)
    *remove_ptr = NOT (resolved);
  return res;
}

static struct clause *
strengthen_ternary_clause (struct simplifier * simplifier,
			   struct clause * clause, unsigned remove)
{
  assert (!binary_pointer (clause));
  assert (clause->size == 3);
  assert (remove != INVALID);
  unsigned lit = INVALID, other = INVALID;
  unsigned * literals = clause->literals;
  for (unsigned i = 0; i != 3; i++)
    {
      unsigned tmp = literals[i];
      if (tmp == remove)
	continue;
      if (lit == INVALID)
	lit = tmp;
      else 
	{
	  assert (other == INVALID);
	  other = tmp;
	  break;
	}
    }
  assert (lit != INVALID);
  assert (other != INVALID);
  mark_subsume_literal (simplifier, lit);
  mark_subsume_literal (simplifier, other);
  struct ruler * ruler = simplifier->ruler;
  ruler->statistics.strengthened++;
  new_ruler_binary_clause (ruler, lit, other);
  trace_add_binary (&ruler->trace, lit, other);
  ROGCLAUSE (clause, "marking garbage");
  trace_delete_clause (&ruler->trace, clause);
  ruler->statistics.garbage++;
  clause->garbage = true;
  return tag_pointer (false, lit, other);
}

static void
strengthen_very_large_clause (struct simplifier * simplifier,
                              struct clause * clause, unsigned remove)
{
  struct ruler * ruler = simplifier->ruler;
  ROGCLAUSE (clause, "strengthening by removing %s in", ROGLIT (remove));
  assert (!binary_pointer (clause));
  assert (remove != INVALID);
  unsigned old_size = clause->size;
  assert (old_size > 3);
  unsigned * literals = clause->literals, * q = literals;
  trace_add_literals (&ruler->trace, old_size, literals, remove);
  trace_delete_literals (&ruler->trace, old_size, literals);
  unsigned * end = literals + old_size;
  for (unsigned *p = literals, lit; p != end; p++)
    if ((lit = *p) != remove)
      *q++ = lit;
  unsigned new_size = q - literals;
  assert (new_size + 1 == old_size);
  clause->size = new_size;
  assert (new_size > 2);
  ruler->statistics.strengthened++;
  mark_subsume_clause (simplifier, clause);
}

static void
forward_subsume_large_clause (struct simplifier * simplifier,
                              struct clause * clause)
{
  struct ruler * ruler = simplifier->ruler;
  ROGCLAUSE (clause, "subsumption candidate");
  assert (!binary_pointer (clause));
  assert (!clause->garbage);
  assert (clause->size <= CLAUSE_SIZE_LIMIT);
  mark_clause (simplifier->marks, clause, INVALID);
  unsigned remove = INVALID, other = INVALID;
  struct clause * subsuming = 0;
  for (all_literals_in_clause (lit, clause))
    {
      subsuming = find_subsuming_clause (simplifier, lit, false, &remove);
      if (subsuming)
	{
	  other = lit;
	  break;
	}
      unsigned not_lit = NOT (lit);
      subsuming = find_subsuming_clause (simplifier, not_lit, true, &remove);
      if (subsuming)
	{
	  other = not_lit;
	  break;
	}
    }
  if (subsuming && remove == INVALID)
    {
      ROGCLAUSE (subsuming, "subsuming");
      ruler->statistics.subsumed++;
      ROGCLAUSE (clause, "marking garbage subsumed");
      mark_eliminate_clause (simplifier, clause);
      trace_delete_clause (&ruler->trace, clause);
      ruler->statistics.garbage++;
      clause->garbage = true;
    }
  else
    {
      if (subsuming)
	{
	  assert (remove != INVALID);
	  bool selfsubsuming = !binary_pointer (subsuming) &&
	                        (clause->size == subsuming->size);
	  if (selfsubsuming)
	    ROGCLAUSE (subsuming,
		       "self-subsuming resolution on %s with",
		       ROGLIT (NOT (remove)));
	  else
	    ROGCLAUSE (subsuming, "resolution on %s with",
	               ROGLIT (NOT (remove)));
	  mark_eliminate_literal (simplifier, remove);
	  if (clause->size == 3)
	    {
	      clause = strengthen_ternary_clause (simplifier, clause, remove);
	      assert (binary_pointer (clause));
	    }
	  else
	    strengthen_very_large_clause (simplifier, clause, remove);
	  ROGCLAUSE (clause, "strengthened");
	  mark_eliminate_literal (simplifier, remove);
	  unmark_literal (simplifier->marks, remove);
	  if (selfsubsuming)
	    {
	      ruler->statistics.subsumed++;
	      ruler->statistics.selfsubsumed++;
	      ROGCLAUSE (subsuming,
	                "disconnecting and marking garbage subsumed");
	      disconnect_literal (ruler, other, subsuming);
	      mark_eliminate_clause (simplifier, subsuming);
	      trace_delete_clause (&ruler->trace, subsuming);
	      ruler->statistics.garbage++;
	      subsuming->garbage = true;
	    }
	}
      if (!binary_pointer (clause))
	{
	  unsigned min_lit = INVALID;
	  unsigned min_size = UINT_MAX;
	  for (all_literals_in_clause (lit, clause))
	    {
	      unsigned lit_size = SIZE (OCCURRENCES (lit));
	      if (min_lit != INVALID && min_size <= lit_size)
		continue;
	      min_lit = lit;
	      min_size = lit_size;
	    }
	  assert (min_lit != INVALID);
	  assert (min_size != INVALID);
	  ROGCLAUSE (clause, "connecting least occurring literal %s "
			     "with %u occurrences in",
			     ROGLIT (min_lit), min_size);
	  connect_literal (ruler, min_lit, clause);
	}
    }
  if (binary_pointer (clause))
    {
      unsigned lit = lit_pointer (clause);
      unsigned other = other_pointer (clause);
      unmark_literal (simplifier->marks, lit);
      unmark_literal (simplifier->marks, other);
    }
  else
    unmark_clause (simplifier->marks, clause, INVALID);
}

static void
flush_large_clause_occurrences (struct ruler * ruler)
{
  ROG ("flushing large clauses occurrences");
  size_t flushed = 0;
  for (all_ruler_literals (lit))
    {
      struct clauses * clauses = &OCCURRENCES (lit);
      struct clause ** begin = clauses->begin, ** q = begin;
      struct clause ** end = clauses->end, ** p = q;
      while (p != end)
	{
	  struct clause * clause = *p++;
	  if (binary_pointer (clause))
	    *q++ = clause;
	  else
	    flushed++;
	}
      clauses->end = q;
    }
  very_verbose (0, "flushed %zu large clause occurrences", flushed);
}

static void
flush_large_garbage_clauses_and_reconnect (struct ruler * ruler)
{
  ROG ("flushing large garbage clauses");
  struct clauses * clauses = &ruler->clauses;
  struct clause ** begin = clauses->begin, ** q = begin;
  struct clause ** end = clauses->end, ** p = q;
  size_t flushed = 0, reconnected = 0;
  while (p != end)
    {
      struct clause * clause = *q++ = *p++;
      if (clause->garbage)
	{
	  ROGCLAUSE (clause, "finally deleting");
	  free (clause);
	  flushed++;
	  q--;
	}
      else
	{
	  connect_large_clause (ruler, clause);
	  reconnected++;
	}
    }
  clauses->end = q;
  very_verbose (0, "flushed %zu garbage clauses", flushed);
  very_verbose (0, "reconnected %zu large clauses", reconnected);
}

bool
subsume_clauses (struct simplifier * simplifier, unsigned round)
{
  if (subsumption_ticks_limit_hit (simplifier))
    return false;
  struct ruler * ruler = simplifier->ruler;
  double start_subsumption = START (ruler, subsume);
  flush_large_clause_occurrences (ruler);
  assert (!ruler->subsuming);
  ruler->subsuming = true;
  struct clause ** candidates;
  size_t size_candidates = get_subsumption_candidates (ruler, &candidates);
  verbose (0, "[%u] found %zu large forward subsumption candidates",
           round, size_candidates);
  struct { uint64_t before, after, delta; } subsumed, strengthened;
  struct ruler_statistics * statistics = &ruler->statistics;
  subsumed.before = statistics->subsumed;
  strengthened.before = statistics->strengthened;
  struct clause ** end_candidates = candidates + size_candidates;
  for (struct clause ** p = candidates; p != end_candidates; p++)
    {
      forward_subsume_large_clause (simplifier, *p);
      if (subsumption_ticks_limit_hit (simplifier))
	break;
    }
  free (candidates);
  flush_large_clause_occurrences (ruler);
  flush_large_garbage_clauses_and_reconnect (ruler);
  assert (ruler->subsuming);
  ruler->subsuming = false;
  subsumed.after = statistics->subsumed;
  strengthened.after = statistics->strengthened;
  subsumed.delta = subsumed.after - subsumed.before;
  strengthened.delta = strengthened.after - strengthened.before;
  double end_subsumption = STOP (ruler, subsume);
  message (0, "[%u] subsumed %zu clauses %.0f%% and "
           "strengthened %zu clauses %.0f%% in %.2f seconds", round,
	   subsumed.delta, percent (subsumed.delta, statistics->original),
	   strengthened.delta, percent (strengthened.delta, statistics->original),
	   end_subsumption - start_subsumption);
  return subsumed.delta || strengthened.delta;
}

