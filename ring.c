#include "ring.h"
#include "ruler.h"
#include "macros.h"
#include "message.h"
#include "utilities.h"

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#ifndef QUIET

void
print_line_without_acquiring_lock (struct ring *ring, const char *fmt, ...)
{
  va_list ap;
  char line[256];
  if (ring)
    sprintf (line, prefix_format, ring->id);
  else
    strcpy (line, "c ");
  va_start (ap, fmt);
  vsprintf (line + strlen (line), fmt, ap);
  va_end (ap);
  strcat (line, "\n");
  assert (strlen (line) + 1 < sizeof line);
  fputs (line, stdout);
}

void
message (struct ring *ring, const char *fmt, ...)
{
  if (verbosity < 0)
    return;
  acquire_message_lock ();
  va_list ap;
  va_start (ap, fmt);
  if (!fmt || *fmt == '\n')
    {
      if (ring)
	printf ("c%u\n", ring->id);
      else
	printf ("c\n");
      fmt++;
    }
  if (fmt)
    {
      if (ring)
	printf (prefix_format, ring->id);
      else
	fputs ("c ", stdout);
      vprintf (fmt, ap);
      va_end (ap);
      fputc ('\n', stdout);
    }
  fflush (stdout);
  release_message_lock ();
}

static void
init_ring_profiles (struct ring *ring)
{
#define RING_PROFILE(NAME) \
  INIT_PROFILE (ring, NAME);
  RING_PROFILES
#undef RING_PROFILE
    START (ring, solve);
}

#endif

void
init_ring (struct ring * ring)
{
  size_t size = ring->size;
  very_verbose (ring, "initializing 'ring[%u]' of size %zu",
                ring->id, size);

  assert (!ring->marks);
  assert (!ring->values);
  assert (!ring->inactive);
  assert (!ring->used);

  ring->marks = allocate_and_clear_block (2 * size);
  ring->values = allocate_and_clear_block (2 * size);
  ring->inactive = allocate_and_clear_block (size);
  ring->used = allocate_and_clear_block (size);

  assert (!ring->references);
  ring->references =
    allocate_and_clear_array (sizeof (struct references), 2 * size);

  struct ring_trail *trail = &ring->trail;
  assert (!trail->begin);
  assert (!trail->pos);
  trail->end = trail->begin = allocate_array (size, sizeof *trail->begin);
  trail->export = trail->propagate = trail->iterate = trail->begin;
  trail->pos = allocate_array (size, sizeof *trail->pos);

  assert (!ring->variables);
  ring->variables = allocate_and_clear_array (size, sizeof *ring->variables);
}

void
release_ring (struct ring * ring)
{
  very_verbose (ring, "releasing 'ring[%u]' of size %u",
                ring->id, ring->size);

  FREE (ring->marks);
  FREE (ring->values);
  FREE (ring->inactive);
  FREE (ring->used);

  RELEASE (ring->analyzed);
  RELEASE (ring->clause);
  RELEASE (ring->levels);
  RELEASE (ring->minimize);

  FREE (ring->references);
  struct ring_trail * trail = &ring->trail;
  free (trail->begin);
  free (trail->pos);
  memset (trail, 0, sizeof *trail);
  FREE (ring->variables);
}

struct ring *
new_ring (struct ruler *ruler)
{
  unsigned size = ruler->compact;
  assert (size < (1u << 30));

  struct ring *ring = allocate_and_clear_block (sizeof *ring);
#ifndef QUIET
  init_ring_profiles (ring);
#endif
  push_ring (ruler, ring);
  ring->size = size;
  verbose (ring, "new ring[%u] of size %u", ring->id, size);

  init_ring (ring);

  struct heap *heap = &ring->heap;
  heap->nodes = allocate_and_clear_array (size, sizeof *heap->nodes);
  heap->increment = 1;

  ring->phases = allocate_and_clear_array (size, sizeof *ring->phases);

  struct queue *queue = &ring->queue;
  queue->links = allocate_and_clear_array (size, sizeof *queue->links);

  struct node *n = heap->nodes;
  struct link *l = queue->links;
  for (all_ring_indices (idx))
    {
      struct node *node = n++;
      struct link *link = l++;
      LOG ("pushing active %s", LOGVAR (idx));
      push_heap (heap, node);
      enqueue (queue, link, true);
    }
  ring->statistics.active = ring->unassigned = size;

  if ((ring->trace.file = ruler->trace.file))
    ring->trace.binary = ruler->trace.binary;

  for (all_averages (a))
    a->exp = 1.0;
  ring->limits.conflicts = -1;
  ring->options = ruler->options;

  return ring;
}

static void
release_watches (struct ring *ring)
{
  for (all_watches (watch, ring->watches))
    {
      assert (!binary_pointer (watch));
      struct clause *clause = watch->clause;
      LOGCLAUSE (clause, "trying to final delete");
      unsigned shared = atomic_fetch_sub (&clause->shared, 1);
      assert (shared + 1);
      if (!shared)
	{
	  LOGCLAUSE (clause, "final deleting shared %u", shared);
	  free (clause);
	}
      free (watch);
    }
  RELEASE (ring->watches);
}

void
init_pool (struct ring *ring, unsigned threads)
{
  ring->threads = threads;
  ring->pool = allocate_and_clear_array (threads, sizeof *ring->pool);
}

static void
release_pool (struct ring *ring)
{
  struct pool *pool = ring->pool;
  if (!pool)
    return;
  for (unsigned i = 0; i != ring->threads; i++, pool++)
    {
      if (i == ring->id)
	continue;
      for (unsigned i = GLUE1_SHARED; i != SIZE_SHARED; i++)
	{
	  struct clause *clause = pool->share[i];
	  if (!clause)
	    continue;
	  if (binary_pointer (clause))
	    continue;
	  unsigned shared = atomic_fetch_sub (&clause->shared, 1);
	  assert (shared + 1);
	  if (!shared)
	    {
	      LOGCLAUSE (clause, "final deleting shared %u", shared);
	      free (clause);
	    }
	}
    }
  free (ring->pool);
}

static void
release_binaries (struct ring *ring)
{
  for (all_ring_literals (lit))
    free (REFERENCES (lit).binaries);
}

void
delete_ring (struct ring *ring)
{
  verbose (ring, "delete ring[%u]", ring->id);
  release_pool (ring);

  release_references (ring);
  if (!ring->id)
    release_binaries (ring);

  release_ring (ring);

  free (ring->heap.nodes);
  free (ring->phases);
  free (ring->queue.links);

  release_watches (ring);
  RELEASE (ring->saved);

  RELEASE (ring->trace.buffer);

  free (ring);
}

void
dec_clauses (struct ring *ring, bool redundant)
{
  if (redundant)
    {
      assert (ring->statistics.redundant > 0);
      ring->statistics.redundant--;
    }
  else
    {
      assert (ring->statistics.irredundant > 0);
      ring->statistics.irredundant--;
    }
}

void
inc_clauses (struct ring *ring, bool redundant)
{
  if (redundant)
    ring->statistics.redundant++;
  else
    ring->statistics.irredundant++;
}

void
set_inconsistent (struct ring *ring, const char *msg)
{
  assert (!ring->inconsistent);
  very_verbose (ring, "%s", msg);
  ring->inconsistent = true;
  assert (!ring->status);
  ring->status = 20;
  set_winner (ring);
}

void
set_satisfied (struct ring *ring)
{
  assert (!ring->inconsistent);
  assert (!ring->unassigned);
  assert (ring->trail.propagate == ring->trail.end);
  ring->status = 10;
  set_winner (ring);
}

void
mark_satisfied_ring_clauses_as_garbage (struct ring *ring)
{
  size_t marked = 0;
  signed char *values = ring->values;
  struct variable *variables = ring->variables;
  for (all_watches (watch, ring->watches))
    {
      if (watch->garbage)
	continue;
      bool satisfied = false;
      struct clause *clause = watch->clause;
      for (all_literals_in_clause (lit, clause))
	{
	  if (values[lit] <= 0)
	    continue;
	  unsigned idx = IDX (lit);
	  if (variables[idx].level)
	    continue;
	  satisfied = true;
	  break;
	}
      if (!satisfied)
	continue;
      mark_garbage_watch (ring, watch);
      marked++;
    }
  ring->last.fixed = ring->statistics.fixed;
  verbose (ring, "marked %zu satisfied clauses as garbage %.0f%%",
	   marked, percent (marked, SIZE (ring->watches)));
}
