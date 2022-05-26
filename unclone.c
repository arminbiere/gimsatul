#include "message.h"
#include "ruler.h"
#include "unclone.h"

static void
save_ring_binaries (struct ring *ring)
{
  struct ruler *ruler = ring->ruler;
  if (!ring->id)
    {
      assert (!ruler->occurrences);
      assert (ruler->compact == ring->size);
      ruler->occurrences =
	allocate_and_clear_array (2 * ring->size, sizeof *ruler->occurrences);
    }

  struct clauses *saved = &ring->saved;
  assert (EMPTY (*saved));
  size_t irredundant = 0;

  for (all_ring_literals (lit))
    {
      struct references *references = &REFERENCES (lit);
      for (all_watches (watch, *references))
	{
	  if (!binary_pointer (watch))
	    continue;
	  assert (redundant_pointer (watch));
	  unsigned other = other_pointer (watch);
	  if (other >= lit)
	    continue;
	  struct clause *clause = (struct clause *) watch;
	  PUSH (*saved, clause);
	}
      RELEASE (*references);
      if (ring->id)
	continue;
      unsigned *binaries = references->binaries;
      if (!binaries)
	continue;
      struct clauses *occurrenes = &OCCURRENCES (lit);
      for (unsigned *p = binaries, other; (other = *p) != INVALID; p++)
	{
	  struct clause *clause = tag_pointer (false, lit, other);
	  PUSH (*occurrenes, clause);
	  if (lit < other)
	    irredundant++;
	}
      free (binaries);
    }

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
save_large_watches (struct ring *ring)
{
  struct ruler *ruler = ring->ruler;
  struct clauses *clauses = &ruler->clauses;
  assert (ring->id || EMPTY (*clauses));
  struct watches *watches = &ring->watches;
  struct clauses *save = &ring->saved;
  size_t transferred = 0, collected = 0, saved = 0, flushed = 0;
  for (all_watches (watch, *watches))
    {
      struct clause *clause = watch->clause;
      if (watch->garbage)
	{
	  dereference_clause (ring, clause);
	  collected++;
	}
      else
	{
	  if (watch->redundant)
	    {
	      PUSH (*save, watch->clause);
	      saved++;
	    }
	  else if (ring->id)
	    {
	      dereference_clause (ring, clause);
	      flushed++;
	    }
	  else
	    {
	      PUSH (*clauses, clause);
	      transferred++;
	    }
	  dec_clauses (ring, watch->redundant);
	}
      free (watch);
    }
  RELEASE (*watches);
  very_verbose (ring, "saved %zu redundant large watches", saved);
  if (ring->id)
    {
      assert (!transferred);
      very_verbose (ring, "flushed %zu irredundant large watches", flushed);
    }
  else
    {
      assert (!flushed);
      very_verbose (ring,
		    "transferred %zu irredundant large clauses", transferred);
    }
}

void
unclone_ring (struct ring *ring)
{
  save_ring_binaries (ring);
  save_large_watches (ring);
  assert (EMPTY (ring->watches));
  release_ring (ring, true);
  assert (EMPTY (ring->watches));
}
