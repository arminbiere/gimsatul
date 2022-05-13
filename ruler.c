#include "ruler.h"
#include "simplify.h"
#include "trace.h"
#include "utilities.h"

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

