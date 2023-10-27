#include "promote.h"
#include "clause.h"
#include "ring.h"
#include "watches.h"

#include "cover.h" // TODO remove

unsigned recompute_glue (struct ring *ring, struct watcher *watcher) {
  unsigned limit = watcher->glue;
  struct unsigneds *promote = &ring->promote;
  struct variable *variables = ring->variables;
  unsigned char *used = ring->used;
  assert (EMPTY (*promote));
  unsigned new_glue = 0;
  for (all_watcher_literals (lit, watcher)) {
    assert (ring->values[lit]);
    unsigned idx = IDX (lit);
    struct variable *v = variables + idx;
    unsigned level = v->level;
    if (!level)
      continue;
    if (used[level] & 2u)
      continue;
    used[level] |= 2u;
    PUSH (*promote, level);
    if (++new_glue == limit)
      break;
  }
  while (!EMPTY (*promote)) {
    unsigned level = POP (*promote);
    assert (used[level] & 2);
    used[level] &= ~2u;
  }
  return new_glue;
}

void promote_watcher (struct ring *ring, struct watcher *watcher,
                      unsigned new_glue) {
  unsigned watcher_glue = watcher->glue;
  assert (new_glue < watcher_glue);
  struct clause *clause = watcher->clause;
  for (;;) {
    unsigned old_glue = clause->glue;
    if (old_glue == new_glue)
      break;
    if (old_glue < new_glue) {
      new_glue = old_glue;
      break;
    }
    unsigned tmp_glue = atomic_exchange (&clause->glue, new_glue);
    if (tmp_glue < new_glue)
      new_glue = tmp_glue;
  }
  ring->statistics.promoted++;
  watcher->glue = new_glue;
  if (new_glue <= TIER1_GLUE_LIMIT) {
    if (watcher_glue > TIER1_GLUE_LIMIT) {
      ring->statistics.promoted1++;
      LOGCLAUSE (clause, "promoted to tier1 from glue %u", watcher_glue);
    }
  } else if (new_glue <= TIER2_GLUE_LIMIT) {
    if (watcher_glue > TIER2_GLUE_LIMIT) {
      ring->statistics.promoted2++;
      LOGCLAUSE (clause, "promoted to tier2 from glue %u", watcher_glue);
    }
  }
}
