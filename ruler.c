#include "ruler.h"
#include "simplify.h"
#include "trace.h"
#include "utilities.h"

#include <string.h>

static void
init_ruler_profiles (struct ruler *ruler)
{
  INIT_PROFILE (ruler, cloning);
  INIT_PROFILE (ruler, deduplicating);
  INIT_PROFILE (ruler, eliminating);
  INIT_PROFILE (ruler, parsing);
  INIT_PROFILE (ruler, solving);
  INIT_PROFILE (ruler, simplifying);
  INIT_PROFILE (ruler, subsuming);
  INIT_PROFILE (ruler, substituting);
  INIT_PROFILE (ruler, total);
  START (ruler, total);
}

struct ruler *
new_ruler (size_t size, struct options * opts)
{
  assert (0 < opts->threads);
  assert (opts->threads <= MAX_THREADS);
  struct ruler *ruler = allocate_and_clear_block (sizeof *ruler);
  memcpy (&ruler->options, opts, sizeof *opts);
  pthread_mutex_init (&ruler->locks.units, 0);
  pthread_mutex_init (&ruler->locks.rings, 0);
#ifdef NFASTPATH
  pthread_mutex_init (&ruler->locks.terminate, 0);
  pthread_mutex_init (&ruler->locks.winner, 0);
#endif
  ruler->size = size;
  ruler->statistics.active = size;
  ruler->values = allocate_and_clear_block (2 * size);
  ruler->marks = allocate_and_clear_block (2 * size);
  assert (sizeof (bool) == 1);
  ruler->eliminated = allocate_and_clear_block (size);
  ruler->eliminate = allocate_and_clear_block (size);
  ruler->subsume = allocate_and_clear_block (size);
  memset (ruler->eliminate, 1, size);
  memset (ruler->subsume, 1, size);
  ruler->occurrences =
    allocate_and_clear_array (2 * size, sizeof *ruler->occurrences);
  ruler->units.begin = allocate_array (size, sizeof (unsigned));
  ruler->units.propagate = ruler->units.end = ruler->units.begin;
  init_ruler_profiles (ruler);
  return ruler;
}

static void
release_occurrences (struct ruler *ruler)
{
  if (!ruler->occurrences)
    return;
  for (all_ruler_literals (lit))
    RELEASE (OCCURRENCES (lit));
  free (ruler->occurrences);
}

static void
release_clauses (struct ruler * ruler)
{
  for (all_clauses (clause, ruler->clauses))
    if (!binary_pointer (clause))
      free (clause);
  RELEASE (ruler->clauses);
}

void
delete_ruler (struct ruler *ruler)
{
#ifndef NDEBUG
  for (all_rings (ring))
    assert (!ring);
#endif
  RELEASE (ruler->rings);
  RELEASE (ruler->buffer);
  RELEASE (ruler->extension);
  release_occurrences (ruler);
  release_clauses (ruler);
  free ((void *) ruler->values);
  free (ruler->marks);
  free (ruler->eliminated);
  free (ruler->eliminate);
  free (ruler->subsume);
  free (ruler->units.begin);
  free (ruler->threads);
  free (ruler);
}

static void
connect_ruler_binary (struct ruler *ruler, unsigned lit, unsigned other)
{
  struct clauses *clauses = &OCCURRENCES (lit);
  struct clause *watch_lit = tag_pointer (false, lit, other);
  PUSH (*clauses, watch_lit);
}

void
new_ruler_binary_clause (struct ruler *ruler, unsigned lit, unsigned other)
{
  ROGBINARY (lit, other, "new");
  connect_ruler_binary (ruler, lit, other);
  connect_ruler_binary (ruler, other, lit);
  ruler->statistics.binaries++;
}

void
disconnect_literal (struct ruler * ruler,
                    unsigned lit, struct clause * clause)
{
  ROGCLAUSE (clause, "disconnecting %s from", ROGLIT (lit));
  struct clauses * clauses = &OCCURRENCES (lit);
  struct clause ** begin = clauses->begin, ** q = begin;
  struct clause ** end = clauses->end, ** p = q;
  uint64_t ticks = 1 + cache_lines (end, begin);
  if (ruler->eliminating)
    ruler->statistics.ticks.elimination += ticks;
  if (ruler->subsuming)
    ruler->statistics.ticks.subsumption += ticks;
  while (p != end)
    {
      struct clause * other_clause = *q++ = *p++;
      if (other_clause == clause)
	{
	  q--;
	  break;
	}
    }
  while (p != end)
    *q++ = *p++;
  assert (q + 1 == p);
  clauses->end = q;
  if (EMPTY (*clauses))
    RELEASE (*clauses);
}

void
connect_large_clause (struct ruler * ruler, struct clause * clause)
{
  assert (!binary_pointer (clause));
  for (all_literals_in_clause (lit, clause))
    connect_literal (ruler, lit, clause);
}

void
assign_ruler_unit (struct ruler * ruler, unsigned unit)
{
  signed char * values = (signed char*) ruler->values;
  unsigned not_unit = NOT (unit);
  assert (!values[unit]);
  assert (!values[not_unit]);
  values[unit] = 1;
  values[not_unit] = -1;
  assert (ruler->units.end < ruler->units.begin + ruler->size);
  *ruler->units.end++ = unit;
  ROG ("assign %s unit", ROGLIT (unit));
  if (ruler->simplifying)
    ruler->statistics.fixed.simplifying++;
  if (ruler->solving)
    ruler->statistics.fixed.solving++;
  ruler->statistics.fixed.total++;
  assert (ruler->statistics.active);
  ruler->statistics.active--;
}

void
disconnect_and_delete_clause (struct ruler * ruler,
                              struct clause * clause, unsigned lit)
{
  if (binary_pointer (clause))
    {
      assert (lit == lit_pointer (clause));
      assert (!redundant_pointer (clause));
      unsigned other = other_pointer (clause);
      struct clause * other_clause = tag_pointer (false, other, lit);
      disconnect_literal (ruler, other, other_clause);
      ROGBINARY (lit, other, "disconnected and deleted");
      assert (ruler->statistics.binaries);
      ruler->statistics.binaries--;
      trace_delete_binary (&ruler->buffer, lit, other);
      mark_eliminate_literal (ruler, other);
    }
  else
    {
      ROGCLAUSE (clause, "disconnecting and marking garbage");
      trace_delete_clause (&ruler->buffer, clause);
      ruler->statistics.garbage++;
      clause->garbage = true;
      for (all_literals_in_clause (other, clause))
	{
	  if (other == lit)
	    continue;
	  disconnect_literal (ruler, other, clause);
	  mark_eliminate_literal (ruler, other);
	}
    }
}

void
disconnect_and_delete_clauses (struct ruler * ruler,
                               struct clauses * clauses, unsigned except)
{
  ROG ("disconnecting and deleting clauses with %s", ROGLIT (except));
  for (all_clauses (clause, *clauses))
      disconnect_and_delete_clause (ruler, clause, except);
  RELEASE (*clauses);
}

