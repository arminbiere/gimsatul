#include "promote.h"
#include "ring.h"

#include <stdatomic.h>

void
promote_clause (struct ring * ring, struct watch * watch)
{
  struct clause * clause = watch->clause;
  assert (!binary_pointer (clause));
  unsigned char old_glue = clause->glue;
  if (!old_glue)
    return;
  struct unsigneds * levels = &ring->levels[1];
  assert (EMPTY (*levels));
  signed char * values = ring->values;
  bool * used = ring->used[1];
  struct variable * variables = ring->variables;
  unsigned level = ring->level;
  unsigned char new_glue = 0;
  for (all_literals_in_clause (lit, clause))
    {
      signed char value = values[lit];
      assert (value);
      if (value > 0)
	continue;
      unsigned idx = IDX (lit);
      struct variable * v = variables + idx;
      unsigned lit_level = v->level;
      if (!lit_level)
	continue;
      if (lit_level == level)
	continue;
      if (used[lit_level])
	continue;
      used[lit_level] = true;
      PUSH (*levels, lit_level);
      assert (new_glue < MAX_GLUE);
      if (++new_glue == old_glue)
	break;
    }
  assert (!binary_pointer (clause));
  for (all_elements_on_stack (unsigned, lit_level, *levels))
    used[lit_level] = false;
  CLEAR (*levels);
  assert (new_glue <= old_glue);
  if (old_glue == new_glue)
    return;
  unsigned char expected_glue = old_glue;
  while (!atomic_compare_exchange_strong (&clause->glue,
                                          &expected_glue, new_glue))
    if (expected_glue < new_glue)
      new_glue = expected_glue;
  watch->glue = new_glue;
  struct ring_statistics * statistics = &ring->statistics;
  if (expected_glue == old_glue)
    {
      LOGCLAUSE (clause,
                 "promoted resolved old glue %u", (unsigned) old_glue);
      statistics->promoted.resolved++;
    }
  else
    {
      LOGCLAUSE (clause,
                 "promoted imported old glue %u", (unsigned) old_glue);
      statistics->promoted.imported++;
    }
  statistics->promoted.clauses++;
}
