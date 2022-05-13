#include "clause.h"
#include "ring.h"
#include "message.h"
#include "tagging.h"
#include "watches.h"

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

