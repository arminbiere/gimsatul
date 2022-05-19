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
	if (binary_pointer (watch))
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
  for (all_watches (watch, ring->watches))
    {
      assert (!binary_pointer (watch));
      unsigned *literals = watch->clause->literals;
      watch->sum = literals[0] ^ literals[1];
      watch_literal (ring, literals[0], watch);
      watch_literal (ring, literals[1], watch);
      reconnected++;
    }
  for (all_watches (lit_watch, *saved))
    {
      assert (binary_pointer (lit_watch));
      assert (redundant_pointer (lit_watch));
      unsigned lit = lit_pointer (lit_watch);
      unsigned other = other_pointer (lit_watch);
      struct watch *other_watch = tag_pointer (true, other, lit);
      watch_literal (ring, lit, lit_watch);
      watch_literal (ring, other, other_watch);
    }
  very_verbose (ring, "reconnected %zu clauses", reconnected);
  ring->trail.propagate = ring->trail.begin;
}

static struct watch *
watch_large_clause (struct ring *ring, struct clause *clause)
{
  assert (clause->size > 2);
  assert (!clause->garbage);
  assert (!clause->dirty);
  bool redundant = clause->redundant;
  unsigned glue = clause->glue;
  struct watch *watch = allocate_block (sizeof *watch);
  watch->garbage = false;
  watch->reason = false;
  watch->redundant = redundant;
  watch->vivify = false;
  if (redundant && TIER1_GLUE_LIMIT < glue && glue <= TIER2_GLUE_LIMIT)
    watch->used = 2;
  else if (redundant && glue >= TIER2_GLUE_LIMIT)
    watch->used = 1;
  else
    watch->used = 0;
  watch->glue = glue;
  watch->middle = 2;
  watch->clause = clause;
  PUSH (ring->watches, watch);
  inc_clauses (ring, redundant);
  return watch;
}

struct watch *
watch_literals_in_large_clause (struct ring *ring,
				struct clause *clause,
				unsigned first, unsigned second)
{
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
  struct watch *watch = watch_large_clause (ring, clause);
  watch->sum = first ^ second;
  watch_literal (ring, first, watch);
  watch_literal (ring, second, watch);
  return watch;
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
  struct watch *watch_lit = tag_pointer (redundant, lit, other);
  struct watch *watch_other = tag_pointer (redundant, other, lit);
  watch_literal (ring, lit, watch_lit);
  watch_literal (ring, other, watch_other);
  LOGBINARY (redundant, lit, other, "new");
  return watch_lit;
}

static void
delete_watch (struct ring *ring, struct watch *watch)
{
  struct clause *clause = watch->clause;
  dereference_clause (ring, clause);
  free (watch);
}

void
flush_watches (struct ring *ring)
{
  struct watches *watches = &ring->watches;
  struct watch **begin = watches->begin, **q = begin;
  struct watch **end = watches->end;
  size_t flushed = 0, deleted = 0;

  for (struct watch ** p = begin; p != end; p++)
    {
      struct watch *watch = *q++ = *p;
      assert (!binary_pointer (watch));
      if (!watch->garbage)
	continue;
      if (watch->reason)
	continue;
      delete_watch (ring, watch);
      flushed++;
      q--;
    }
  watches->end = q;
  verbose (ring,
	   "flushed %zu garbage watched and deleted %zu clauses %.0f%%",
	   flushed, deleted, percent (deleted, flushed));
}

void
mark_garbage_watch (struct ring * ring, struct watch * watch)
{
  LOGWATCH (watch, "marking garbage");
  assert (!binary_pointer (watch));
  assert (!watch->garbage);
  watch->garbage = true;
  dec_clauses (ring, watch->redundant);
}

void
sort_redundant_watches (size_t size_candidates,
                        struct watch **candidates)
{
  if (size_candidates < 2)
    return;
  size_t size_count = MAX_GLUE + 1, count[size_count];
  memset (count, 0, sizeof count);
  struct watch ** end = candidates + size_candidates;
  for (struct watch ** p = candidates; p != end; p++)
    {
      struct watch * watch = *p;
      assert (watch->redundant), assert (watch->glue <= MAX_GLUE);
      count[watch->glue]++;
    }
  size_t pos = 0, *c = count + size_count, size;
  while (c-- != count)
    size = *c, *c = pos, pos += size;
  size_t bytes = size_candidates * sizeof (struct watch *);
  struct watch **tmp = allocate_block (bytes);
  for (struct watch ** p = candidates; p != end; p++)
    {
      struct watch * watch = *p;
      tmp[count[watch->glue]++] = watch;
    }
  memcpy (candidates, tmp, bytes);
  free (tmp);
}

