#include "message.h"
#include "ruler.h"
#include "unclone.h"

static void
save_ring_binaries (struct ring * ring)
{
  struct ruler * ruler = ring->ruler;
  if (!ring->id)
    {
      assert (!ruler->occurrences);
      assert (ruler->compact == ring->size);
      ruler->occurrences =
        allocate_and_clear_array (2*ring->size, sizeof *ruler->occurrences);
    }

  struct clauses * saved = &ring->saved;
  assert (EMPTY (*saved));
  size_t irredundant = 0;

  for (all_ring_literals (lit))
    {
      struct references * references = &REFERENCES (lit);
      for (all_watches (watch, *references))
	{
	  if (!binary_pointer (watch))
	    continue;
	  assert (redundant_pointer (watch));
	  unsigned other = other_pointer (watch);
	  if (other >= lit)
	    continue;
	  struct clause * clause = (struct clause*) watch;
	  PUSH (*saved, clause);
	}
      RELEASE (*references);
      if (ring->id)
	continue;
      unsigned * binaries = references->binaries;
      if (!binaries)
	continue;
      struct clauses * occurrenes = &OCCURRENCES (lit);
      for (unsigned * p = binaries, other; (other = *p) != INVALID; p++)
	{
	  struct clause * clause = tag_pointer (false, lit, other);
	  PUSH (*occurrenes, clause);
	  if (lit < other)
	    irredundant++;
	}
      free (binaries);
    }
  free (ring->references);

  size_t redundant = SIZE (*saved);

  if (ring->id)
    irredundant = ruler->statistics.binaries;
  else
    assert (irredundant == ruler->statistics.binaries);

  very_verbose (ring, "saved %zu binary redundant watches", redundant);
  very_verbose (ring, "flushed %zu binary irredundant watches", irredundant);

  assert (ring->statistics.irredundant >= irredundant);
  ring->statistics.irredundant -= irredundant;

  assert (ring->statistics.redundant >= redundant);
  ring->statistics.redundant -= redundant;

}

static void
save_large_watches (struct ring * ring)
{
  struct ruler * ruler = ring->ruler;
  struct clauses * clauses = &ruler->clauses;
  assert (ring->id || EMPTY (*clauses));
  struct watches * watches = &ring->watches;
  struct clauses * saved = &ring->saved;
  for (all_watches (watch, *watches))
    {
      struct clause * clause = watch->clause;
      if (watch->garbage)
	dereference_clause (ring, clause);
      else
	{
	  if (watch->redundant)
	    PUSH (*saved, watch->clause);
	  else if (ring->id)
	    {
	      assert (clause->shared);
	      dereference_clause (ring, clause);
	    }
	  else
	    PUSH (*clauses, clause);
	  dec_clauses (ring, watch->redundant);
	}
      free (watch);
    }
  size_t flushed = SIZE (*watches) - SIZE (*saved);
  RELEASE (*watches);
  very_verbose (ring, "saved %zu redundant large watches", SIZE (*saved));
  very_verbose (ring, "flushed %zu irredundant large watches", flushed);
}

void
unclone_ring (struct ring * ring)
{
  assert (ring->ruler->compact == ring->size);
  save_ring_binaries (ring);
  save_large_watches (ring);
}