#ifndef _vivify_h_INCLUDED
#define _vivify_h_INCLUDED

#include <stdbool.h>

#include "options.h"
#include "watches.h"

struct ring;
struct watch;

void vivify_clauses (struct ring *);

static inline bool
watched_vivification_candidate (struct watch * watch)
{
  if (watch->garbage)
    return false;
  if (!watch->redundant)
    return false;
  if (watch->glue > TIER2_GLUE_LIMIT)
    return false;
  return true;
}

#endif
