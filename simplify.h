#ifndef _simplify_h_INCLUDED

#include "ruler.h"

static inline void
mark_eliminate_literal (struct ruler * ruler, unsigned lit)
{
  unsigned idx = IDX (lit);
  if (ruler->eliminate[idx])
    return;
  ROG ("marking %s to be eliminated", ROGVAR (idx));
  ruler->eliminate[idx] = 1;
}

static inline void
mark_eliminate_clause (struct ruler * ruler, struct clause * clause)
{
  for (all_literals_in_clause (lit, clause))
    mark_eliminate_literal (ruler, lit);
}

static inline void
mark_subsume_literal (struct ruler * ruler, unsigned lit)
{
  unsigned idx = IDX (lit);
  if (ruler->subsume[idx])
    return;
  ROG ("marking %s to be subsumed", ROGVAR (idx));
  ruler->subsume[idx] = 1;
}

static inline void
mark_subsume_clause (struct ruler * ruler, struct clause * clause)
{
  for (all_literals_in_clause (lit, clause))
    mark_subsume_literal (ruler, lit);
}

static inline bool
subsumption_ticks_limit_hit (struct ruler * ruler)
{
  struct ruler_statistics * statistics = &ruler->statistics;
  struct ruler_limits * limits = &ruler->limits;
  return statistics->ticks.subsumption > limits->subsumption;
}

static inline bool
elimination_ticks_limit_hit (struct ruler * ruler)
{
  struct ruler_statistics * statistics = &ruler->statistics;
  struct ruler_limits * limits = &ruler->limits;
  return statistics->ticks.elimination > limits->elimination;
}

#endif
