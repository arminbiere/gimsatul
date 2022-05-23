#include "ring.h"
#include "ruler.h"
#include "macros.h"
#include "message.h"
#include "utilities.h"

#include <assert.h>
#include <stdarg.h>
#include <stdio.h>
#include <string.h>

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
  if (ring)
    printf (prefix_format, ring->id);
  else
    fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
  release_message_lock ();
}

static void
init_ring_profiles (struct ring *ring)
{
  INIT_PROFILE (ring, fail);
  INIT_PROFILE (ring, focus);
  INIT_PROFILE (ring, probe);
  INIT_PROFILE (ring, search);
  INIT_PROFILE (ring, stable);
  INIT_PROFILE (ring, vivify);
  INIT_PROFILE (ring, walk);
  INIT_PROFILE (ring, solve);
  START (ring, solve);
}

struct ring *
new_ring (struct ruler *ruler)
{
  unsigned size = ruler->compact;
  assert (size < (1u << 30));
  struct ring *ring = allocate_and_clear_block (sizeof *ring);
  init_ring_profiles (ring);
  push_ring (ruler, ring);
  ring->size = size;
  ring->options = ruler->options;
  if ((ring->trace.file = ruler->trace.file))
    ring->trace.binary = ruler->trace.binary;
  verbose (ring, "new ring[%u] of size %u", ring->id, size);
  ring->values = allocate_and_clear_block (2 * size);
  ring->marks = allocate_and_clear_block (2 * size);
  ring->references =
    allocate_and_clear_array (sizeof (struct references), 2 * size);
  assert (sizeof (bool) == 1);
  ring->active = allocate_and_clear_block (size);
  ring->used[0] = allocate_and_clear_block (size);
  ring->used[1] = allocate_and_clear_block (size);
  ring->variables = allocate_and_clear_array (size, sizeof *ring->variables);
  struct ring_trail *trail = &ring->trail;
  trail->end = trail->begin = allocate_array (size, sizeof *trail->begin);
  trail->export = trail->propagate = trail->iterate = trail->begin;
  trail->pos = allocate_array (size, sizeof *trail->pos);
  struct heap *heap = &ring->heap;
  heap->nodes = allocate_and_clear_array (size, sizeof *heap->nodes);
  heap->increment[0] = heap->increment[1] = 1;
  struct queue *queue = &ring->queue;
  queue->links = allocate_and_clear_array (size, sizeof *heap->nodes);
  unsigned active = 0;
  struct node *n = heap->nodes;
  struct link *l = queue->links;
  for (all_ring_indices (idx))
    {
      struct node *node = n++;
      struct link *link = l++;
      LOG ("pushing active %s", LOGVAR (idx));
      ring->active[idx] = true;
      push_heap (heap, node);
      enqueue (queue, link, true);
      active++;
    }
  ring->statistics.active = ring->unassigned = active;
  LOG ("found %u active variables", active);
  assert (active == ring->size);
  for (all_averages (a))
    a->exp = 1.0;
  ring->limits.conflicts = -1;
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
  RELEASE (ring->clause);
  RELEASE (ring->analyzed);
  RELEASE (ring->minimize);
  free (ring->trail.begin);
  free (ring->trail.pos);
  RELEASE (ring->levels[0]);
  RELEASE (ring->levels[1]);
  RELEASE (ring->trace.buffer);
  release_references (ring);
  if (!ring->id)
    release_binaries (ring);
  free (ring->references);
  release_watches (ring);
  RELEASE (ring->saved);
  free (ring->heap.nodes);
  free (ring->queue.links);
  free (ring->variables);
  free (ring->values);
  free (ring->marks);
  free (ring->active);
  free (ring->used[0]);
  free (ring->used[1]);
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
