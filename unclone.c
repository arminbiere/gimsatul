#include "message.h"
#include "ruler.h"
#include "unclone.h"

static void
save_ring_binaries (struct ring * ring)
{
  assert (ring->id);
  struct watches * redundant = &ring->redundant;
  assert (EMPTY (*redundant));
  size_t saved = 0;
  for (all_ring_literals (lit))
    {
      struct references * references = &REFERENCES (lit);
      for (all_watches (watch, *references))
	{
	  if (binary_pointer (watch))
	    {
	      assert (redundant_pointer (watch));
	      unsigned other = other_pointer (watch);
	      if (other < lit)
		{
		  PUSH (*redundant, watch);
		  saved++;
		}
	    }
	}
      RELEASE (*references);
    }
  LOG ("saved %zu binary redundant watches", saved);
  free (ring->references);

  struct ruler * ruler = ring->ruler;
  assert (ring->statistics.irredundant >= ruler->statistics.binaries);
  ring->statistics.irredundant -= ruler->statistics.binaries;
}

static void
save_large_redundant_watches (struct ring * ring)
{
  assert (ring->id);
  struct watches * watches = &ring->watches;
  struct watches * redundant = &ring->redundant;
  size_t saved = 0, flushed = 0;
  for (all_watches (watch, *watches))
    if (watch->redundant)
      {
	PUSH (*redundant, watch);
	saved++;
      }
    else
      flushed++;
  RELEASE (*watches);
  LOG ("flushed %zu irredundant large watches", flushed);
  LOG ("saved %zu redundant large watches", saved);
  assert (ring->statistics.irredundant >= flushed);
  ring->statistics.irredundant -= flushed;
}

void
unclone_ring (struct ring * ring)
{
  assert (ring->ruler->compact == ring->size);
  save_ring_binaries (ring);
  save_large_redundant_watches (ring);
}
