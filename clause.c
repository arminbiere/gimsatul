#include "clause.h"
#include "stack.h"
#include "tagging.h"
#include "trace.h"
#include "utilities.h"

#ifdef LOGGING
#include "logging.h"
#endif

#include <string.h>

struct clause *
new_large_clause (size_t size, unsigned *literals,
		  bool redundant, unsigned glue)
{
  assert (2 <= size);
  size_t bytes = size * sizeof (unsigned);
  struct clause *clause = allocate_block (sizeof *clause + bytes);
#ifdef LOGGING
  clause->id = atomic_fetch_add (&clause_ids, 1);
#endif
  if (glue > MAX_GLUE)
    glue = MAX_GLUE;
  clause->glue = glue;
  clause->garbage = false;
  clause->dirty = false;
  clause->redundant = redundant;
  clause->subsume = false;
  clause->shared = 0;
  clause->size = size;
  memcpy (clause->literals, literals, bytes);
  return clause;
}

void
mark_clause (signed char * marks, struct clause * clause, unsigned except)
{
  if (binary_pointer (clause))
    mark_literal (marks, other_pointer (clause));
  else
    for (all_literals_in_clause (other, clause))
      if (other != except)
	mark_literal (marks, other);
}

void
unmark_clause (signed char * marks, struct clause * clause, unsigned except)
{
  if (binary_pointer (clause))
    unmark_literal (marks, other_pointer (clause));
  else
    for (all_literals_in_clause (other, clause))
      if (other != except)
	unmark_literal (marks, other);
}

void
really_trace_add_clause (struct buffer *buffer, struct clause *clause)
{
  really_trace_add_literals (buffer, clause->size, clause->literals, INVALID);
}

void
really_trace_delete_clause (struct buffer *buffer, struct clause *clause)
{
  if (!clause->garbage)
    really_trace_delete_literals (buffer, clause->size, clause->literals);
}
