#include "promote.h"
#include "clause.h"
#include "ring.h"
#include "watches.h"

unsigned recompute_glue (struct ring * ring, struct watcher * watcher) {
  unsigned limit = watcher->glue;
  struct unsigneds * promote = &ring->promote;
  struct variable * variables = ring->variables;
  unsigned char * used = ring->used;
  assert (EMPTY (*promote));
  unsigned new_glue = 0;
  for (all_watcher_literals (lit, watcher)) {
    assert (ring->values[lit]);
    unsigned idx = IDX (lit);
    struct variable * v = variables + idx;
    unsigned level = v->level;
    if (!level)
      continue;
    if (used[level] & 2)
      continue;
    used[level] |= 2;
    PUSH (*promote, level);
    if (++new_glue == limit)
      break;
  }
  for (all_elements_on_stack (unsigned, level, *promote))
    used[level] &= ~2;
  CLEAR (*promote);
  return new_glue;
}

void promote_watcher (struct ring *ring, struct watcher *watcher,
		       unsigned new_glue) {
  unsigned watcher_glue = watcher->glue;
  assert (new_glue < watcher_glue);
  struct clause * clause = watcher->clause;
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
}
