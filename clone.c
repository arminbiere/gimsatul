#include "assign.h"
#include "clone.h"
#include "message.h"
#include "ruler.h"
#include "utilities.h"

#include <stdio.h>

static void
copy_ruler_binaries (struct ring *ring)
{
  struct ruler *ruler = ring->ruler;
  assert (first_ring (ruler) == ring);
  assert (!ring->id);
  size_t copied = 0;

  for (all_ruler_literals (lit))
    {
      struct clauses *occurrences = &OCCURRENCES (lit);
      struct references *references = &REFERENCES (lit);
      size_t size = 0;
      for (all_clauses (clause, *occurrences))
	if (binary_pointer (clause))
	  size++;
      unsigned *binaries = allocate_array (size + 1, sizeof *binaries);
      unsigned *b = references->binaries = binaries;
      for (all_clauses (clause, *occurrences))
	if (binary_pointer (clause))
	  {
	    assert (lit_pointer (clause) == lit);
	    assert (!redundant_pointer (clause));
	    unsigned other = other_pointer (clause);
	    if (other < lit)
	      {
		LOGBINARY (false, lit, other , "copying");
		copied++;
	      }
	    *b++ = other;
	  }
      assert (binaries + size == b);
      *b = INVALID;
      RELEASE (*occurrences);
    }
  ring->statistics.irredundant += copied;
  very_verbose (ring, "copied %zu binary clauses", copied);
  assert (copied == ruler->statistics.binaries);
}

static void
share_ring_binaries (struct ring *dst, struct ring *src)
{
  struct ring *ring = dst;
  assert (!src->id);

  for (all_ring_literals (lit))
    {
      struct references *src_references = src->references + lit;
      struct references *dst_references = dst->references + lit;
      dst_references->binaries = src_references->binaries;
    }

  size_t shared = src->ruler->statistics.binaries;
  ring->statistics.irredundant += shared;
  very_verbose (ring, "shared %zu binary clauses", shared);
}

static void
transfer_and_own_ruler_clauses (struct ring *ring)
{
  struct ruler *ruler = ring->ruler;
  assert (first_ring (ruler) == ring);
  assert (!ring->id);
  size_t transferred = 0;
  for (all_clauses (clause, ruler->clauses))
    {
      LOGCLAUSE (clause, "transferring");
      assert (!clause->garbage);
      (void) watch_first_two_literals_in_large_clause (ring, clause);
      transferred++;
    }
  RELEASE (ruler->clauses);
  very_verbose (ring, "transferred %zu large clauses", transferred);
}

static void
clone_ruler (struct ruler *ruler)
{
  if (verbosity >= 0)
    {
      printf ("c\nc cloning first ring solver\n");
      fflush (stdout);
    }
  struct ring *ring = new_ring (ruler);
  if (ruler->inconsistent)
    set_inconsistent (ring, "copied empty clause");
  else
    {
      copy_ruler_binaries (ring);
      transfer_and_own_ruler_clauses (ring);
    }
}

/*------------------------------------------------------------------------*/

static void
clone_clauses (struct ring *dst, struct ring *src)
{
  struct ring *ring = dst;
  verbose (ring, "cloning clauses from ring[%u] to ring[%u]",
	   src->id, dst->id);
  assert (!src->level);
  assert (src->trail.propagate == src->trail.begin);
  if (src->inconsistent)
    {
      set_inconsistent (ring, "cloning inconsistent empty clause");
      return;
    }
  unsigned units = 0;
  for (all_elements_on_stack (unsigned, lit, src->trail))
    {
      LOG ("cloning unit %s", LOGLIT (lit));
      assign_ring_unit (ring, lit);
      units++;
    }
  very_verbose (ring, "cloned %u units", units);

  size_t shared = 0;
  for (all_watches (src_watch, src->watches))
    {
      struct clause *clause = src_watch->clause;
      assert (!clause->redundant);
      reference_clause (ring, clause, 1);
      (void) watch_first_two_literals_in_large_clause (ring, clause);
      shared++;
    }
  very_verbose (ring, "sharing %zu large clauses", shared);
}

static void *
clone_ring (void *ptr)
{
  struct ring *src = ptr;
  struct ring *ring = new_ring (src->ruler);
  share_ring_binaries (ring, src);
  clone_clauses (ring, src);
  init_pool (ring, src->threads);
  return ring;
}

static void
start_cloning_ring (struct ring *first, unsigned clone)
{
  struct ruler *ruler = first->ruler;
  assert (ruler->threads);
  pthread_t *thread = ruler->threads + clone;
  if (pthread_create (thread, 0, clone_ring, first))
    fatal_error ("failed to create cloning thread %u", clone);
}

static void
stop_cloning_ring (struct ring *first, unsigned clone)
{
  struct ruler *ruler = first->ruler;
  pthread_t *thread = ruler->threads + clone;
  if (pthread_join (*thread, 0))
    fatal_error ("failed to join cloning thread %u", clone);
}

void
clone_rings (struct ruler *ruler)
{
  unsigned threads = ruler->options.threads;
  assert (0 < threads);
  assert (threads <= MAX_THREADS);
  START (ruler, clone);
  double before = 0;
  if (verbosity >= 0)
      before = current_resident_set_size () / (double) (1 << 20);
  clone_ruler (ruler);
  if (threads > 1)
    {
      message (0, "cloning %u rings from first to support %u threads",
		  threads - 1, threads);
      ruler->threads = allocate_array (threads, sizeof *ruler->threads);
      struct ring *first = first_ring (ruler);
      init_pool (first, threads);
      for (unsigned i = 1; i != threads; i++)
	start_cloning_ring (first, i);
      for (unsigned i = 1; i != threads; i++)
	stop_cloning_ring (first, i);
    }
  assert (SIZE (ruler->rings) == threads);
  if (verbosity >= 0)
    {
      double after = current_resident_set_size () / (double) (1 << 20);
      printf ("c memory increased by %.2f from %.2f MB to %.2f MB\n",
	      average (after, before), before, after);
      fflush (stdout);
    }
  STOP (ruler, clone);
}
