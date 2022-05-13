#include "message.h"
#include "simplify.h"
#include "trace.h"

void
add_resolvent (struct ruler * ruler)
{
  assert (!ruler->inconsistent);
  struct unsigneds * resolvent = &ruler->resolvent;
  unsigned * literals = resolvent->begin;
  size_t size = SIZE (*resolvent);
  trace_add_literals (&ruler->buffer, size, literals, INVALID);
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

