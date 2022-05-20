#include "message.h"
#include "ruler.h"
#include "trace.h"
#include "simplify.h"
#include "utilities.h"

#include <string.h>

void
init_ruler_profiles (struct ruler *ruler)
{
  INIT_PROFILE (ruler, clone);
  INIT_PROFILE (ruler, deduplicate);
  INIT_PROFILE (ruler, eliminate);
  INIT_PROFILE (ruler, parse);
  INIT_PROFILE (ruler, solve);
  INIT_PROFILE (ruler, simplify);
  INIT_PROFILE (ruler, subsume);
  INIT_PROFILE (ruler, substitute);
  INIT_PROFILE (ruler, total);
  START (ruler, total);
}

struct ruler *
new_ruler (size_t size, struct options *opts)
{
  assert (0 < opts->threads);
  assert (opts->threads <= MAX_THREADS);
  struct ruler *ruler = allocate_and_clear_block (sizeof *ruler);
  ruler->size = ruler->compact = size;
  ruler->statistics.active = size;
  memcpy (&ruler->options, opts, sizeof *opts);
  ruler->trace.binary = opts->binary;
  ruler->trace.file = opts->proof.file ? &opts->proof : 0;
#ifndef NDEBUG
  ruler->original = allocate_and_clear_block (sizeof *ruler->original);
#endif
  pthread_mutex_init (&ruler->locks.units, 0);
  pthread_mutex_init (&ruler->locks.rings, 0);
  pthread_mutex_init (&ruler->locks.terminate, 0);
  pthread_mutex_init (&ruler->locks.winner, 0);
  init_synchronization (&ruler->synchronize);
  ruler->values = allocate_and_clear_block (2 * size);

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
release_clauses (struct ruler *ruler)
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
  RELEASE (ruler->trace.buffer);
  RELEASE (ruler->extension);
  if (ruler->original)
    {
      RELEASE (*ruler->original);
      free (ruler->original);
    }
  release_occurrences (ruler);
  release_clauses (ruler);
  free ((void *) ruler->values);
  free (ruler->map);
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
disconnect_literal (struct ruler *ruler, unsigned lit, struct clause *clause)
{
  ROGCLAUSE (clause, "disconnecting %s from", ROGLIT (lit));
  struct clauses *clauses = &OCCURRENCES (lit);
  struct clause **begin = clauses->begin, **q = begin;
  struct clause **end = clauses->end, **p = q;
  uint64_t ticks = 1 + cache_lines (end, begin);
  if (ruler->eliminating)
    ruler->statistics.ticks.elimination += ticks;
  if (ruler->subsuming)
    ruler->statistics.ticks.subsumption += ticks;
  while (p != end)
    {
      struct clause *other_clause = *q++ = *p++;
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
connect_large_clause (struct ruler *ruler, struct clause *clause)
{
  assert (!binary_pointer (clause));
  for (all_literals_in_clause (lit, clause))
    connect_literal (ruler, lit, clause);
}

void
assign_ruler_unit (struct ruler *ruler, unsigned unit)
{
  signed char *values = (signed char *) ruler->values;
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
recycle_clause (struct simplifier *simplifier,
		struct clause *clause, unsigned lit)
{
  struct ruler *ruler = simplifier->ruler;
  if (binary_pointer (clause))
    {
      assert (lit == lit_pointer (clause));
      assert (!redundant_pointer (clause));
      unsigned other = other_pointer (clause);
      struct clause *other_clause = tag_pointer (false, other, lit);
      disconnect_literal (ruler, other, other_clause);
      ROGBINARY (lit, other, "disconnected and deleted");
      assert (ruler->statistics.binaries);
      ruler->statistics.binaries--;
      trace_delete_binary (&ruler->trace, lit, other);
      mark_eliminate_literal (simplifier, other);
    }
  else
    {
      ROGCLAUSE (clause, "disconnecting and marking garbage");
      trace_delete_clause (&ruler->trace, clause);
      ruler->statistics.garbage++;
      clause->garbage = true;
      for (all_literals_in_clause (other, clause))
	if (other != lit)
	  mark_eliminate_literal (simplifier, other);
    }
}

void
recycle_clauses (struct simplifier *simplifier,
		 struct clauses *clauses, unsigned except)
{
#ifdef LOGGING
  struct ruler *ruler = simplifier->ruler;
  ROG ("disconnecting and deleting clauses with %s", ROGLIT (except));
#endif
  for (all_clauses (clause, *clauses))
    recycle_clause (simplifier, clause, except);
  RELEASE (*clauses);
}

/*------------------------------------------------------------------------*/

void
push_ring (struct ruler *ruler, struct ring *ring)
{
  if (pthread_mutex_lock (&ruler->locks.rings))
    fatal_error ("failed to acquire rings lock while pushing ring");
  size_t id = SIZE (ruler->rings);
  PUSH (ruler->rings, ring);
  if (pthread_mutex_unlock (&ruler->locks.rings))
    fatal_error ("failed to release rings lock while pushing ring");
  assert (id < MAX_THREADS);
  ring->id = id;
  ring->random = ring->id;
  ring->ruler = ruler;
  ring->units = ruler->units.end;
}

void
detach_ring (struct ring *ring)
{
  struct ruler *ruler = ring->ruler;
  if (pthread_mutex_lock (&ruler->locks.rings))
    fatal_error ("failed to acquire rings lock while detaching ring");
  assert (ring->id < SIZE (ruler->rings));
  assert (ruler->rings.begin[ring->id] == ring);
  ruler->rings.begin[ring->id] = 0;
  if (pthread_mutex_unlock (&ruler->locks.rings))
    fatal_error ("failed to release ringfs lock while detaching ring");
}

/*------------------------------------------------------------------------*/

void
set_terminate (struct ruler *ruler)
{
  if (pthread_mutex_lock (&ruler->locks.terminate))
    fatal_error ("failed to acquire terminate lock");
  ruler->terminate = true;
  if (pthread_mutex_unlock (&ruler->locks.terminate))
    fatal_error ("failed to release terminate lock");
  disable_synchronization (&ruler->synchronize);
}

void
set_winner (struct ring *ring)
{
  volatile struct ring *winner;
  struct ruler *ruler = ring->ruler;
  bool winning;
  if (pthread_mutex_lock (&ruler->locks.winner))
    fatal_error ("failed to acquire winner lock");
  winner = ruler->winner;
  assert (winner != ring);
  winning = !winner;
  if (winning)
    ruler->winner = ring;
  if (pthread_mutex_unlock (&ruler->locks.winner))
    fatal_error ("failed to release winner lock");
  if (!winning)
    {
      assert (winner);
      assert (winner->status == ring->status);
      return;
    }
  set_terminate (ruler);
  verbose (ring, "winning ring[%u] with status %d", ring->id, ring->status);
}
