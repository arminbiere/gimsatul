#include "promote.h"
#include "clause.h"
#include "ring.h"

void promote_clause (struct ring *ring, struct clause *clause,
                     unsigned new_glue) {
  ring->statistics.promoted.total++;
}
