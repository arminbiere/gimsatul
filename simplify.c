#include "backtrack.h"
#include "compact.h"
#include "deduplicate.h"
#include "eliminate.h"
#include "message.h"
#include "report.h"
#include "simplify.h"
#include "substitute.h"
#include "subsume.h"
#include "trace.h"
#include "utilities.h"

#include <inttypes.h>
#include <string.h>

struct simplifier *
new_simplifier (struct ruler *ruler)
{
  size_t size = ruler->compact;
  struct simplifier *simplifier =
    allocate_and_clear_block (sizeof *simplifier);
  simplifier->ruler = ruler;
  simplifier->marks = allocate_and_clear_block (2 * size);
  simplifier->eliminated = allocate_and_clear_block (size);
  simplifier->eliminate = allocate_and_clear_block (size);
  simplifier->subsume = allocate_and_clear_block (size);
  memset (simplifier->eliminate, 1, size);
  memset (simplifier->subsume, 1, size);
  return simplifier;
}

void
delete_simplifier (struct simplifier *simplifier)
{
  free (simplifier->marks);
  free (simplifier->eliminated);
  free (simplifier->eliminate);
  free (simplifier->subsume);
  free (simplifier);
}

void
add_resolvent (struct simplifier *simplifier)
{
  struct ruler *ruler = simplifier->ruler;
  assert (!ruler->inconsistent);
  struct unsigneds *resolvent = &simplifier->resolvent;
  unsigned *literals = resolvent->begin;
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
      mark_subsume_literal (simplifier, other);
      mark_subsume_literal (simplifier, lit);
    }
  else
    {
      assert (size > 2);
      if (ruler->eliminating)
	ruler->statistics.ticks.elimination += size;
      struct clause *clause = new_large_clause (size, literals, false, 0);
      connect_large_clause (ruler, clause);
      mark_subsume_clause (simplifier, clause);
      PUSH (ruler->clauses, clause);
      ROGCLAUSE (clause, "new");
    }
}

/*------------------------------------------------------------------------*/

static bool
ruler_propagate (struct simplifier *simplifier)
{
  struct ruler *ruler = simplifier->ruler;
  signed char *values = (signed char *) ruler->values;
  struct ruler_trail *units = &ruler->units;
  size_t garbage = 0;
  while (!ruler->inconsistent && units->propagate != units->end)
    {
      unsigned lit = *units->propagate++;
      ROG ("propagating unit %s", ROGLIT (lit));
      unsigned not_lit = NOT (lit);
      struct clauses *clauses = &OCCURRENCES (not_lit);
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
	      mark_eliminate_clause (simplifier, clause);
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
mark_satisfied_ruler_clauses (struct simplifier *simplifier)
{
  struct ruler *ruler = simplifier->ruler;
  signed char *values = (signed char *) ruler->values;
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
	  mark_eliminate_clause (simplifier, clause);
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
flush_ruler_occurrences (struct simplifier *simplifier)
{
  struct ruler *ruler = simplifier->ruler;
  signed char *values = (signed char *) ruler->values;
  size_t flushed = 0;
  size_t deleted = 0;
  for (all_ruler_literals (lit))
    {
      signed char lit_value = values[lit];
      struct clauses *clauses = &OCCURRENCES (lit);
      struct clause **begin = clauses->begin, **q = begin;
      struct clause **end = clauses->end, **p = q;
      while (p != end)
	{
	  struct clause *clause = *q++ = *p++;
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
			mark_eliminate_literal (simplifier, lit);
		      if (!other_value)
			mark_eliminate_literal (simplifier, other);
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
delete_large_garbage_ruler_clauses (struct simplifier *simplifier)
{
  struct ruler *ruler = simplifier->ruler;
  struct clauses *clauses = &ruler->clauses;
  struct clause **begin_clauses = clauses->begin, **q = begin_clauses;
  struct clause **end_clauses = clauses->end, **p = q;
  size_t deleted = 0, shrunken = 0;
  signed char *values = (signed char *) ruler->values;
  bool trace = ruler->options.proof.file;
  struct unsigneds remove;
  INIT (remove);
  while (p != end_clauses)
    {
      struct clause *clause = *q++ = *p++;
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
	  unsigned *literals = clause->literals;
	  unsigned old_size = clause->size;
	  assert (old_size > 2);
	  unsigned *end_literals = literals + old_size;
	  unsigned *l = literals, *k = l;
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
	  mark_subsume_literal (simplifier, other);
	  mark_subsume_literal (simplifier, lit);
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
propagate_and_flush_ruler_units (struct simplifier *simplifier)
{
  if (!ruler_propagate (simplifier))
    return false;
  struct ruler *ruler = simplifier->ruler;
  struct ruler_last *last = &ruler->last;
  if (last->fixed != ruler->statistics.fixed.total)
    mark_satisfied_ruler_clauses (simplifier);
  if (last->fixed != ruler->statistics.fixed.total ||
      last->garbage != ruler->statistics.garbage)
    {
      flush_ruler_occurrences (simplifier);
      delete_large_garbage_ruler_clauses (simplifier);
    }
  last->fixed = ruler->statistics.fixed.total;
  last->garbage = ruler->statistics.garbage;
  assert (!ruler->inconsistent);
  return true;
}

static void
connect_all_large_clauses (struct ruler *ruler)
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
      if (UINT64_MAX / 10 > res)
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
set_ruler_limits (struct ruler *ruler, unsigned optimize)
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
      if ((UINT_MAX - 1) / scale >= SIMPLIFICATION_ROUNDS)
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
current_ruler_clauses (struct ruler *ruler)
{
  return SIZE (ruler->clauses) + ruler->statistics.binaries;
}

static void
push_ruler_units_to_extension_stack (struct ruler *ruler)
{
  struct unsigneds *extension = &ruler->extension;
  for (all_elements_on_stack (unsigned, lit, ruler->units))
    {
      PUSH (*extension, INVALID);
      PUSH (*extension, lit);
    }
  verbose (0, "pushed %zu units on extension stack", SIZE (*extension));
  ruler->units.end = ruler->units.propagate = ruler->units.begin;
}

static void
run_only_root_level_propagation (struct simplifier *simplifier)
{
  if (verbosity >= 0)
    {
      printf ("c\nc simplifying by root-level propagation only\n");
      fflush (stdout);
    }
  connect_all_large_clauses (simplifier->ruler);
  propagate_and_flush_ruler_units (simplifier);
}

static void
run_full_blown_simplification (struct simplifier *simplifier)
{
  if (verbosity >= 0)
    {
      printf ("c\nc simplifying formula before cloning\n");
      fflush (stdout);
    }

  struct ruler *ruler = simplifier->ruler;
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
      if (!propagate_and_flush_ruler_units (simplifier))
	break;

      if (equivalent_literal_substitution (simplifier, round))
	done = false;
      if (!propagate_and_flush_ruler_units (simplifier))
	break;

      if (remove_duplicated_binaries (simplifier, round))
	done = false;
      if (!propagate_and_flush_ruler_units (simplifier))
	break;

      if (subsume_clauses (simplifier, round))
	done = false;
      if (!propagate_and_flush_ruler_units (simplifier))
	break;

      if (eliminate_variables (simplifier, round))
	done = false;
      if (!propagate_and_flush_ruler_units (simplifier))
	break;
      if (elimination_ticks_limit_hit (simplifier))
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
	   variables.after, percent (variables.after, ruler->size));


  clauses.after = current_ruler_clauses (ruler);
  size_t original = ruler->statistics.original;

  if (clauses.after <= clauses.before)
    {
      clauses.delta = clauses.before - clauses.after;
      message (0, "simplification removed %zu clauses %.0f%% "
	       "with %zu remaining %.0f%%",
	       clauses.delta,
	       percent (clauses.delta, clauses.before),
	       clauses.after, percent (clauses.after, original));
    }
  else
    {
      clauses.delta = clauses.after - clauses.before;
      message (0, "simplification ADDED %zu clauses %.0f%% "
	       "with %zu remaining %.0f%%",
	       clauses.delta,
	       percent (clauses.delta, clauses.before),
	       clauses.after, percent (clauses.after, original));
    }

  if (ruler->inconsistent)
    message (0, "simplification produced empty clause");

  message (0, "subsumption used %" PRIu64 " ticks%s",
	   ruler->statistics.ticks.subsumption,
	   subsumption_ticks_limit_hit (simplifier) ? " (limit hit)" : "");
  message (0, "elimination used %" PRIu64 " ticks%s",
	   ruler->statistics.ticks.elimination,
	   elimination_ticks_limit_hit (simplifier) ? " (limit hit)" : "");
}

void
simplify_ruler (struct ruler *ruler)
{
  if (ruler->inconsistent)
    return;

  double start_simplification = START (ruler, simplify);

  assert (!ruler->simplifying);
  ruler->simplifying = true;

  struct simplifier *simplifier = new_simplifier (ruler);
  if (ruler->options.preprocessing)
    run_full_blown_simplification (simplifier);
  else
    run_only_root_level_propagation (simplifier);

  push_ruler_units_to_extension_stack (ruler);
  compact_ruler (simplifier);
  delete_simplifier (simplifier);

  assert (ruler->simplifying);
  ruler->simplifying = false;

  double end_simplification = STOP (ruler, simplify);
  message (0, "simplification took %.2f seconds",
	   end_simplification - start_simplification);
}

static void
finish_other_ring_simplification (struct ring * ring)
{
}

static void
finish_first_ring_simplication (struct ring * ring)
{
  assert (!ring->id);
  struct ruler * ruler = ring->ruler;
  if (pthread_mutex_lock (&ruler->locks.simplify))
    fatal_error ("failed to acquire simplify lock during preparation");

  ruler->simplify = false;

  if (pthread_mutex_unlock (&ruler->locks.simplify))
    fatal_error ("failed to release simplify lock during preparation");

  struct ring_limits * limits = &ring->limits;
  struct ring_statistics * statistics = &ring->statistics;
  limits->simplify = SEARCH_CONFLICTS;
  unsigned interval = ring->options.simplify_interval;
  assert (interval);
  limits->simplify += interval * nlogn (statistics->simplifications);
  very_verbose (ring, "new simplify limit of %" PRIu64 " conflicts",
		limits->simplify);
}

static void
finish_ring_simplification (struct ring * ring)
{
  if (ring->id)
    finish_other_ring_simplification (ring);
  else
    finish_first_ring_simplication (ring);
}

static void
run_first_ring_simplification (struct ring * ring)
{
  assert (!ring->id);
  struct ruler * ruler = ring->ruler;
  (void) ruler;
}

static void
run_ring_simplification (struct ring * ring)
{
  if (!ring->id)
    run_first_ring_simplification (ring);
}

static void
prepare_first_ring_simplification (struct ring * ring)
{
  assert (!ring->id);
}

static void
prepare_other_ring_simplification (struct ring * ring)
{
  assert (ring->id);
}

static void
prepare_ring_simplification (struct ring * ring)
{
  if (ring->level)
    backtrack (ring, 0);
  assert (ring->trail.propagate == ring->trail.end);
  STOP_SEARCH ();
  ring->statistics.simplifications++;
  if (ring->id)
    prepare_other_ring_simplification (ring);
  else
    prepare_first_ring_simplification (ring);
  rendezvous (ring, run_ring_simplification, "running simplification");
  run_ring_simplification (ring);
  rendezvous (ring, finish_ring_simplification, "finish simplification");
  finish_ring_simplification (ring);
  report (ring, 's');
  START_SEARCH ();
}

void
simplify_ring (struct ring * ring)
{
  struct ruler * ruler = ring->ruler;

  if (ring->id)
    assert (ruler->simplify);
  else
    {
      if (pthread_mutex_lock (&ruler->locks.simplify))
	fatal_error ("failed to acquire simplify lock during starting");

      assert (!ruler->simplify);
      ruler->simplify = true;

      if (pthread_mutex_unlock (&ruler->locks.simplify))
	fatal_error ("failed to release simplify lock during starting");
    }

  rendezvous (ring, prepare_ring_simplification, "preparing simplification");
  prepare_ring_simplification (ring);
}

bool
simplifying (struct ring * ring)
{
  if (ring->options.simplify < 2)
    return false;
  if (!ring->id)
    return ring->limits.simplify <= SEARCH_CONFLICTS;
    
  struct ruler * ruler = ring->ruler;
#ifndef NFASTPATH
  if (!ruler->simplify)
    return false;
#endif
  if (pthread_mutex_lock (&ruler->locks.simplify))
    fatal_error ("failed to acquire simplify lock during checking");

  bool res = ruler->simplify;

  if (pthread_mutex_unlock (&ruler->locks.simplify))
    fatal_error ("failed to release simplify lock during checking");

  return res;
}
