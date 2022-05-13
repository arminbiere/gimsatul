#include "ruler.h"
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

