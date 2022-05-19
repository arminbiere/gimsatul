#include "compact.h"
#include "deduplicate.h"
#include "eliminate.h"
#include "message.h"
#include "simplify.h"
#include "substitute.h"
#include "subsume.h"
#include "trace.h"
#include "utilities.h"

#include <inttypes.h>

void
add_resolvent (struct ruler * ruler)
{
  assert (!ruler->inconsistent);
  struct unsigneds * resolvent = &ruler->resolvent;
  unsigned * literals = resolvent->begin;
  size_t size = SIZE (*resolvent);
  trace_add_literals (&ruler->trace, size, literals, INVALID);
  if (!size)
    {
      very_verbose (0, "%s", "empty resolvent");
      ruler->inconsistent = true;
    }
  else if (size == 1)
    {
      const unsigned unit = literals[0];
      ROG ("unit resolvent %s", ROGLIT (unit));
      assign_ruler_unit (ruler, unit);
    }
  else if (size == 2)
    {
      unsigned lit = literals[0];
      unsigned other = literals[1];
      new_ruler_binary_clause (ruler, lit, other);
      mark_subsume_literal (ruler, other);
      mark_subsume_literal (ruler, lit);
    }
  else
    {
      assert (size > 2);
      if (ruler->eliminating)
	ruler->statistics.ticks.elimination += size;
      struct clause *clause = new_large_clause (size, literals, false, 0);
      connect_large_clause (ruler, clause);
      mark_subsume_clause (ruler, clause);
      PUSH (ruler->clauses, clause);
      ROGCLAUSE (clause, "new");
    }
}

/*------------------------------------------------------------------------*/

static bool
ruler_propagate (struct ruler * ruler)
{
  signed char * values = (signed char*) ruler->values;
  struct ruler_trail * units = &ruler->units;
  size_t garbage = 0;
  while (!ruler->inconsistent && units->propagate != units->end)
    {
      unsigned lit = *units->propagate++;
      ROG ("propagating unit %s", ROGLIT (lit));
      unsigned not_lit = NOT (lit);
      struct clauses * clauses = &OCCURRENCES (not_lit);
      for (all_clauses (clause, *clauses))
	{
	  bool satisfied = false;
	  unsigned unit = INVALID;
	  unsigned non_false = 0;
	  if (binary_pointer (clause))
	    {
	      assert (lit_pointer (clause) == not_lit);
	      unsigned other = other_pointer (clause);
	      signed char value = values[other];
	      if (value > 0)
		continue;
	      if (value < 0)
		{
	          ROGBINARY (not_lit, other, "conflict");
		  goto CONFLICT;
		}
	      ROGBINARY (not_lit, other, "unit %s forcing", ROGLIT (other));
	      trace_add_unit (&ruler->trace, other);
	      assign_ruler_unit (ruler, other);
	      continue;
	    }
	  if (clause->garbage)
	    continue;
	  for (all_literals_in_clause (other, clause))
	    {
	      signed char value = values[other];
	      if (value > 0)
		{
		  satisfied = true;
		  break;
		}
	      if (value < 0)
		continue;
	      if (non_false++)
		break;
	      unit = other;
	    }
	  if (!satisfied && !non_false)
	    {
	      ROGCLAUSE (clause, "conflict");
	    CONFLICT:
	      assert (!ruler->inconsistent);
	      verbose (0, "%s", "propagation yields inconsistency");
	      ruler->inconsistent = true;
	      trace_add_empty (&ruler->trace);
	      break;
	    }
	  if (!satisfied && non_false == 1)
	    {
	      ROGCLAUSE (clause, "unit %s forcing", ROGLIT (unit));
	      assert (unit != INVALID);
	      trace_add_unit (&ruler->trace, unit);
	      assign_ruler_unit (ruler, unit);
	      satisfied = true;
	    }
	  if (satisfied)
	    {
	      ROGCLAUSE (clause, "marking satisfied garbage");
	      trace_delete_clause (&ruler->trace, clause);
	      mark_eliminate_clause (ruler, clause);
	      ruler->statistics.garbage++;
	      clause->garbage = true;
	      garbage++;
	    }
	}
    }
  very_verbose (0, "marked %zu garbage clause during propagation", garbage);
  return !ruler->inconsistent;
}

static void
mark_satisfied_ruler_clauses (struct ruler * ruler)
{
  signed char * values = (signed char*) ruler->values;
  size_t marked_satisfied = 0, marked_dirty = 0;
  for (all_clauses (clause, ruler->clauses))
    {
      if (clause->garbage)
	continue;
      bool satisfied = false, dirty = false;
      for (all_literals_in_clause (lit, clause))
	{
	  signed char value = values[lit];
	  if (value > 0)
	    {
	      satisfied = true;
	      break;
	    }
	  if (!dirty && value < 0)
	    dirty = true;
	}
      if (satisfied)
	{
	  ROGCLAUSE (clause, "marking satisfied garbage");
	  trace_delete_clause (&ruler->trace, clause);
	  mark_eliminate_clause (ruler, clause);
	  ruler->statistics.garbage++;
	  clause->garbage = true;
	  marked_satisfied++;
	}
      else if (dirty)
	{
	  ROGCLAUSE (clause, "marking dirty");
	  assert (!clause->dirty);
	  clause->dirty = true;
	  marked_dirty++;
	}
    }
  very_verbose (0,
     "found %zu additional large satisfied clauses and marked %zu dirty",
     marked_satisfied, marked_dirty);
}

static void
flush_ruler_occurrences (struct ruler * ruler)
{
  signed char * values = (signed char*) ruler->values;
  size_t flushed = 0;
  size_t deleted = 0;
  for (all_ruler_literals (lit))
    {
      signed char lit_value = values[lit];
      struct clauses * clauses = &OCCURRENCES (lit);
      struct clause ** begin = clauses->begin, ** q = begin;
      struct clause ** end = clauses->end, ** p = q;
      while (p != end)
	{
	  struct clause * clause = *q++ = *p++;
	  if (binary_pointer (clause))
	    {
	      assert (lit_pointer (clause) == lit);
	      unsigned other = other_pointer (clause);
	      signed char other_value = values[other];
	      if (other_value > 0 || lit_value > 0)
		{
		  if (other < lit)
		    {
		      ROGBINARY (lit, other, "deleting satisfied");
		      trace_delete_binary (&ruler->trace, lit, other);
		      if (!lit_value)
			mark_eliminate_literal ( ruler, lit);
		      if (!other_value)
			mark_eliminate_literal ( ruler, other);
		      deleted++;
		    }
		  flushed++;
		  q--;
		}
	      else
		{
		  assert (!lit_value);
		  assert (!other_value);
		}
	    }
	  else if (clause->garbage)
	    {
	      flushed++;
	      q--;
	    }
	}
      if (lit_value)
	{
	  flushed += q - begin;
	  RELEASE (*clauses);
	}
      else
	clauses->end = q;
    }
  very_verbose (0, "flushed %zu garbage watches", flushed);
  very_verbose (0, "deleted %zu satisfied binary clauses", deleted);
  assert (deleted <= ruler->statistics.binaries);
  ruler->statistics.binaries -= deleted;
}

static void
delete_large_garbage_ruler_clauses (struct ruler * ruler)
{
  struct clauses * clauses = &ruler->clauses;
  struct clause ** begin_clauses = clauses->begin, ** q = begin_clauses;
  struct clause ** end_clauses = clauses->end, ** p = q;
  size_t deleted = 0, shrunken = 0;
  signed char * values = (signed char*) ruler->values;
  bool trace = ruler->options.proof.file;
  struct unsigneds remove;
  INIT (remove);
  while (p != end_clauses)
    {
      struct clause * clause = *q++ = *p++;
      if (clause->garbage)
	{
	  ROGCLAUSE (clause, "finally deleting");
	  free (clause);
	  deleted++;
	  q--;
	}
      else if (clause->dirty)
	{
	  assert (EMPTY (remove));
	  shrunken++;
	  ROGCLAUSE (clause, "shrinking dirty");
	  unsigned * literals = clause->literals;
	  unsigned old_size = clause->size;
	  assert (old_size > 2);
	  unsigned * end_literals = literals + old_size;
	  unsigned * l = literals, * k = l;
	  while (l != end_literals)
	    {
	      unsigned lit = *k++ = *l++;
	      signed char value = values[lit];
	      assert (value <= 0);
	      if (trace)
		PUSH (remove, lit);
	      if (value < 0)
		k--;
	    }
	  size_t new_size = k - literals;
	  assert (1 < new_size);
	  assert (new_size < old_size);
	  clause->size = new_size;
	  clause->dirty = false;
	  ROGCLAUSE (clause, "shrunken dirty");
	  if (trace)
	    {
	      assert (old_size == SIZE (remove));
	      trace_add_clause (&ruler->trace, clause);
	      trace_delete_literals (&ruler->trace, old_size, remove.begin);
	      CLEAR (remove);
	    }
	  if (2 < new_size)
	    continue;
	  unsigned lit = literals[0];
	  unsigned other = literals[1];
	  disconnect_literal (ruler, lit, clause);
	  disconnect_literal (ruler, other, clause);
	  ROGCLAUSE (clause, "deleting shrunken dirty");
	  new_ruler_binary_clause (ruler, lit, other);
	  mark_subsume_literal (ruler, other);
	  mark_subsume_literal (ruler, lit);
	  free (clause);
	  q--;
	}
    }
  clauses->end = q;
  if (trace)
    RELEASE (remove);
  very_verbose (0, "finally deleted %zu large garbage clauses", deleted);
  very_verbose (0, "shrunken %zu dirty clauses", shrunken);
}

static bool
propagate_and_flush_ruler_units (struct ruler * ruler)
{
  if (!ruler_propagate (ruler))
    return false;
  struct ruler_last * last = &ruler->last;
  if (last->fixed != ruler->statistics.fixed.total)
      mark_satisfied_ruler_clauses (ruler);
  if (last->fixed != ruler->statistics.fixed.total ||
      last->garbage != ruler->statistics.garbage)
    {
      flush_ruler_occurrences (ruler);
      delete_large_garbage_ruler_clauses (ruler);
    }
  last->fixed = ruler->statistics.fixed.total;
  last->garbage = ruler->statistics.garbage;
  assert (!ruler->inconsistent);
  return true;
}

static void
connect_all_large_clauses (struct ruler * ruler)
{
  ROG ("connecting all large clauses");
  for (all_clauses (clause, ruler->clauses))
    connect_large_clause (ruler, clause);
}

static uint64_t
scale_ticks_limit (unsigned optimized, unsigned base)
{
  uint64_t res = base;
  res *= 1e6;
  for (unsigned i = 0; i != optimized; i++)
    {
      if (UINT64_MAX/10 > res)
	res *= 10;
      else
	{
	  res = UINT64_MAX;
	  break;
	}
    }
  return res;
}

static void
set_ruler_limits (struct ruler * ruler, unsigned optimize)
{
  message (0, "simplification optimization level %u", optimize);
  if (optimize)
    {
      unsigned scale = 1;
      for (unsigned i = 0; i != optimize; i++)
	scale *= 10;
      message (0, "scaling simplification ticks limits by %u", scale);
    }
  else
    message (0, "keeping simplification ticks limits at their default");

  ruler->limits.elimination =
    scale_ticks_limit (optimize, ELIMINATION_TICKS_LIMIT);
  message (0, "setting elimination limit to %" PRIu64 " ticks",
           ruler->limits.elimination);

  ruler->limits.subsumption =
    scale_ticks_limit (optimize, SUBSUMPTION_TICKS_LIMIT);
  message (0, "setting subsumption limit to %" PRIu64 " ticks",
           ruler->limits.subsumption);
}

static unsigned
set_max_rounds (unsigned optimize)
{
  unsigned res = SIMPLIFICATION_ROUNDS;
  if (optimize)
    {
      unsigned scale = optimize + 1;
      if ((UINT_MAX - 1)/scale >= SIMPLIFICATION_ROUNDS)
	res *= scale;
      else
	res = UINT_MAX - 1;
      message (0, "running at most %u simplification rounds (scaled by %u)",
	       res, optimize);
    }
  else
    message (0, "running at most %u simplification rounds (default)", res);
  return res;
}

static size_t
current_ruler_clauses (struct ruler * ruler)
{
  return SIZE (ruler->clauses) + ruler->statistics.binaries;
}

static void
push_ruler_units_to_extension_stack (struct ruler * ruler)
{
#if 0
  SHRINK_STACK (ruler->extension[0]);
  struct unsigneds * extension = ruler->extension + 1;
  for (all_elements_on_stack (unsigned, lit, ruler->units))
    PUSH (*extension, lit);
  SHRINK_STACK (*extension);
#else
  struct unsigneds * extension = ruler->extension + 0;
  for (all_elements_on_stack (unsigned, lit, ruler->units))
    {
      PUSH (*extension, INVALID);
      PUSH (*extension, lit);
    }
#endif
  verbose (0, "pushed %zu units on extension stack", SIZE (*extension));
  ruler->units.end = ruler->units.propagate = ruler->units.begin;
}

void
simplify_ruler (struct ruler * ruler)
{
  if (ruler->inconsistent)
    return;

  double start_simplification = START (ruler, simplify);
  assert (!ruler->simplifying);
  ruler->simplifying = true;

  if (!ruler->options.preprocessing)
    {
      if (verbosity >= 0)
	{
	  printf ("c\nc simplifying by root-level propagation only\n");
	  fflush (stdout);
	}
      connect_all_large_clauses (ruler);
      propagate_and_flush_ruler_units (ruler);
      goto DONE;
    }

  if (verbosity >= 0)
    {
      printf ("c\nc simplifying formula before cloning\n");
      fflush (stdout);
    }

  connect_all_large_clauses (ruler);

  unsigned optimize = ruler->options.optimize;
  set_ruler_limits (ruler, optimize);
  struct
  {
    size_t before, after, delta;
  } clauses, variables;

  clauses.before = current_ruler_clauses (ruler);
  variables.before = ruler->statistics.active;

  unsigned max_rounds = set_max_rounds (optimize);

  bool done = false;

  for (unsigned round = 1; !done && round <= max_rounds; round++)
    {
      done = true;
      if (!propagate_and_flush_ruler_units (ruler))
	break;

      if (equivalent_literal_substitution (ruler, round))
	done = false;
      if (!propagate_and_flush_ruler_units (ruler))
	break;

      if (remove_duplicated_binaries (ruler, round))
	done = false;
      if (!propagate_and_flush_ruler_units (ruler))
	break;

      if (subsume_clauses (ruler, round))
	done = false;
      if (!propagate_and_flush_ruler_units (ruler))
	break;

      if (eliminate_variables (ruler, round))
	done = false;
      if (!propagate_and_flush_ruler_units (ruler))
	break;
      if (elimination_ticks_limit_hit (ruler))
	break;
    }
  if (verbosity >= 0)
    fputs ("c\n", stdout);

  variables.after = ruler->statistics.active;
  assert (variables.after <= variables.before);
  variables.delta = variables.before - variables.after;

  message (0, "simplification removed %zu variables %.0f%% "
           "with %zu remaining %.0f%%",
	   variables.delta,
	   percent (variables.delta, variables.before),
	   variables.after,
	   percent (variables.after, ruler->size));
           

  clauses.after = current_ruler_clauses (ruler);
  size_t original = ruler->statistics.original;

  if (clauses.after <= clauses.before)
    {
      clauses.delta = clauses.before - clauses.after;
      message (0, "simplification removed %zu clauses %.0f%% "
               "with %zu remaining %.0f%%",
	       clauses.delta,
	       percent (clauses.delta, clauses.before),
	       clauses.after,
	       percent (clauses.after, original));
    }
  else
    {
      clauses.delta = clauses.after - clauses.before;
      message (0, "simplification ADDED %zu clauses %.0f%% "
               "with %zu remaining %.0f%%",
	       clauses.delta,
	       percent (clauses.delta, clauses.before),
	       clauses.after,
	       percent (clauses.after, original));
    }

  if (ruler->inconsistent)
    message (0, "simplification produced empty clause");

  message (0, "subsumption used %" PRIu64 " ticks%s",
           ruler->statistics.ticks.subsumption,
	   subsumption_ticks_limit_hit (ruler) ? " (limit hit)" : "");
  message (0, "elimination used %" PRIu64 " ticks%s",
           ruler->statistics.ticks.elimination,
	   elimination_ticks_limit_hit (ruler) ? " (limit hit)" : "");
DONE:
  push_ruler_units_to_extension_stack (ruler);
  compact_ruler (ruler);
  assert (ruler->simplifying);
  ruler->simplifying = false;
  double end_simplification = STOP (ruler, simplify);
  message (0, "simplification took %.2f seconds",
           end_simplification - start_simplification);
}
