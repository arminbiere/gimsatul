#include "clause.h"
#include "ring.h"
#include "message.h"
#include "tagging.h"
#include "trace.h"
#include "watches.h"
#include "utilities.h"
#include "vivify.h"

#include <string.h>

void
release_references (struct ring *ring)
{
  if (ring->references)
    for (all_ring_literals (lit))
      RELEASE (REFERENCES (lit));
}

void
disconnect_references (struct ring *ring, struct watches *saved)
{
  size_t disconnected = 0;
  for (all_ring_literals (lit))
    {
      struct references *watches = &REFERENCES (lit);
      for (all_watches (watch, *watches))
	if (is_binary_pointer (watch))
	  {
	    assert (redundant_pointer (watch));
	    assert (lit_pointer (watch) == lit);
	    unsigned other = other_pointer (watch);
	    if (other < lit)
	      PUSH (*saved, watch);
	  }
      disconnected += SIZE (*watches);
      RELEASE (*watches);
    }
}

void
reconnect_watches (struct ring *ring, struct watches *saved)
{
  size_t reconnected = 0;
  for (all_watchers (watcher))
    {
      unsigned *literals = watcher->clause->literals;
      watcher->sum = literals[0] ^ literals[1];
      watch_literal (ring, literals[0], literals[1], watcher);
      watch_literal (ring, literals[1], literals[0], watcher);
      reconnected++;
    }
  for (all_watches (lit_watch, *saved))
    {
      assert (is_binary_pointer (lit_watch));
      assert (redundant_pointer (lit_watch));
      unsigned lit = lit_pointer (lit_watch);
      unsigned other = other_pointer (lit_watch);
      struct watch *other_watch = tag_binary (true, other, lit);
      push_watch (ring, lit, lit_watch);
      push_watch (ring, other, other_watch);
    }
  very_verbose (ring, "reconnected %zu clauses", reconnected);
  ring->trail.propagate = ring->trail.begin;
}

struct watch *
watch_literals_in_large_clause (struct ring *ring,
				struct clause *clause,
				unsigned first, unsigned second)
{
  assert (clause->size > 2);
  assert (!clause->garbage);
  assert (!clause->dirty);
#ifndef NDEBUG
  assert (first != second);
  bool found_first = false;
  for (all_literals_in_clause (lit, clause))
    found_first |= (lit == first);
  assert (found_first);
  bool found_second = false;
  for (all_literals_in_clause (lit, clause))
    found_second |= (lit == second);
  assert (found_second);
#endif
  size_t size_watchers = SIZE (ring->watchers);
  if (size_watchers >= MAX_WATCHER_INDEX)
    fatal_error ("more than %zu watched clauses in ring[%u]",
		 (size_t) MAX_WATCHER_INDEX, ring->id);
  unsigned idx = size_watchers;

  if (FULL (ring->watchers))
    ENLARGE (ring->watchers);
  struct watcher *watcher = ring->watchers.end++;
  assert (ring->watchers.end <= ring->watchers.allocated);

  unsigned size = clause->size;
  unsigned glue = clause->glue;
  bool redundant = clause->redundant;

  if (size > 4)			// TODO was 4
    size = 0;

  unsigned used;
  if (redundant && TIER1_GLUE_LIMIT < glue && glue <= TIER2_GLUE_LIMIT)
    used = 2;
  else if (redundant && glue >= TIER2_GLUE_LIMIT)
    used = 1;
  else
    used = 0;

  assert (size < (1 << (8 * sizeof watcher->size)));
  assert (glue < (1 << (8 * sizeof watcher->glue)));
  assert (used < (1 << (8 * sizeof watcher->used)));

  watcher->size = size;
  watcher->glue = glue;
  watcher->used = used;

  watcher->garbage = false;
  watcher->reason = false;
  watcher->redundant = redundant;
  watcher->vivify = false;

  watcher->sum = first ^ second;
  watcher->clause = clause;

  if (size)
    memcpy (watcher->aux, clause->literals, size * sizeof (unsigned));
#ifndef NMIDDLE
  else
    watcher->aux[0] = 2;
#endif

  inc_clauses (ring, redundant);

  struct watch *first_watch = tag_index (redundant, idx, second);
  struct watch *second_watch = tag_index (redundant, idx, first);
  push_watch (ring, first, first_watch);
  push_watch (ring, second, second_watch);

  return tag_index (true, idx, INVALID_LIT);
}

struct watch *
watch_first_two_literals_in_large_clause (struct ring *ring,
					  struct clause *clause)
{
  unsigned *lits = clause->literals;
  return watch_literals_in_large_clause (ring, clause, lits[0], lits[1]);
}

struct watch *
new_local_binary_clause (struct ring *ring, bool redundant,
			 unsigned lit, unsigned other)
{
  inc_clauses (ring, redundant);
  struct watch *watch_lit = tag_binary (redundant, lit, other);
  struct watch *watch_other = tag_binary (redundant, other, lit);
  push_watch (ring, lit, watch_lit);
  push_watch (ring, other, watch_other);
  LOGBINARY (redundant, lit, other, "new");
  return watch_lit;
}

unsigned *
map_watchers (struct ring *ring)
{
  struct watchers *watchers = &ring->watchers;
  assert (!EMPTY (*watchers));
  assert (!watchers->begin[0].sum);
  struct watcher *begin = watchers->begin + 1;
  struct watcher *end = watchers->end;

  size_t size = end - begin;
  unsigned *map = allocate_and_clear_array (size + 1, sizeof *map);

  size_t mapped = 0;
  size_t idx = 1;

  for (struct watcher * p = begin; p != end; p++, idx++)
    if (!p->garbage || p->reason)
      {
	assert (idx <= size);
	assert (mapped < MAX_WATCHER_INDEX);
	map[idx] = ++mapped;
      }

  verbose (ring, "mapped %zu non-garbage watchers %.0f%%",
	   mapped, percent (mapped, size));
#ifdef QUIET
  (void) mapped;
#endif
  return map;
}

void
flush_watchers (struct ring *ring)
{
  struct watchers *watchers = &ring->watchers;
  assert (!EMPTY (*watchers));
  assert (!watchers->begin[0].sum);
  struct watcher *begin = watchers->begin + 1;
  struct watcher *end = watchers->end;
  struct watcher *q = begin;
  size_t flushed = 0;
  size_t deleted = 0;

  for (struct watcher * p = begin; p != end; p++)
    {
      if (!p->garbage || p->reason)
	*q++ = *p;
      else
	{
	  struct clause *clause = p->clause;
	  deleted += dereference_clause (ring, clause);
	  flushed++;
	}
    }
  watchers->end = q;
  verbose (ring,
	   "flushed %zu garbage watched and deleted %zu clauses %.0f%%",
	   flushed, deleted, percent (deleted, flushed));
#ifdef QUIET
  (void) deleted;
  (void) flushed;
#endif
}

void
mark_garbage_watcher (struct ring *ring, struct watcher *watcher)
{
  LOGCLAUSE (watcher->clause, "marking garbage watcher to");
  assert (!watcher->garbage);
  watcher->garbage = true;
  dec_clauses (ring, watcher->redundant);
}

void
sort_redundant_watcher_indices (struct ring *ring,
				size_t size_indices, unsigned *indices)
{
  if (size_indices < 2)
    return;
  size_t size_count = MAX_GLUE + 1, count[size_count];
  memset (count, 0, sizeof count);
  unsigned *end = indices + size_indices;
  for (unsigned *p = indices; p != end; p++)
    {
      unsigned idx = *p;
      struct watcher *watcher = index_to_watcher (ring, idx);
      assert (watcher->glue <= MAX_GLUE);
      assert (watcher->redundant);
      count[watcher->glue]++;
    }
  size_t pos = 0, *c = count + size_count, size;
  while (c-- != count)
    size = *c, *c = pos, pos += size;
  size_t bytes = size_indices * sizeof *indices;
  unsigned *tmp = allocate_block (bytes);
  for (unsigned *p = indices; p != end; p++)
    {
      unsigned idx = *p;
      struct watcher *watcher = index_to_watcher (ring, idx);
      tmp[count[watcher->glue]++] = idx;
    }
  memcpy (indices, tmp, bytes);
  free (tmp);
}
