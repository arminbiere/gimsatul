#include "ring.h"
#include "vivify.h"

void
vivify_clauses (string ring * ring)
{
  if (ring->inconsistent)
    return;
  struct clauses * clauses = &ring->clauses;
  if (EMPTY (*clauses))
    return;
}
