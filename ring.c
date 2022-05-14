#include "ring.h"
#include "ruler.h"
#include "macros.h"
#include "message.h"

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
  INIT_PROFILE (ring, focused);
  INIT_PROFILE (ring, search);
  INIT_PROFILE (ring, stable);
  INIT_PROFILE (ring, walk);
  INIT_PROFILE (ring, solving);
  START (ring, solving);
}

struct ring *
new_ring (struct ruler *ruler)
{
  unsigned size = ruler->size;
  assert (size < (1u << 30));
  struct ring *ring = allocate_and_clear_block (sizeof *ring);
  init_ring_profiles (ring);
  push_ring (ruler, ring);
  ring->size = size;
  verbose (ring, "new ring[%u] of size %u", ring->id, size);
  ring->values = allocate_and_clear_block (2 * size);
  ring->marks = allocate_and_clear_block (2 * size);
  ring->references =
    allocate_and_clear_array (sizeof (struct references), 2 * size);
  assert (sizeof (bool) == 1);
  ring->active = allocate_and_clear_block (size);
  ring->used = allocate_and_clear_block (size);
  ring->variables = allocate_and_clear_array (size, sizeof *ring->variables);
  struct ring_trail *trail = &ring->trail;
  trail->end = trail->begin = allocate_array (size, sizeof *trail->begin);
  trail->export = trail->propagate = trail->iterate = trail->begin;
  trail->pos = allocate_array (size, sizeof *trail->pos);
  struct queue *queue = &ring->queue;
  queue->nodes = allocate_and_clear_array (size, sizeof *queue->nodes);
  queue->scores = allocate_and_clear_array (size, sizeof *queue->scores);
  queue->increment[0] = queue->increment[1] = 1;
  bool * eliminated = ruler->eliminated;
  unsigned active = 0;
  signed char * ruler_values = (signed char*) ruler->values;
  for (all_active_and_inactive_nodes (node))
    {
      size_t idx = node - queue->nodes;
      assert (idx < size);
      if (eliminated[idx])
	{
	  LOG ("skipping eliminated %s", LOGVAR (idx));
	  continue;
	}
      unsigned lit = LIT (idx);
      if (ruler_values[lit])
	{
	  LOG ("skipping simplification-fixed %s", LOGVAR (idx));
	  continue;
	}
      LOG ("enqueuing active %s", LOGVAR (idx));
      ring->active[idx] = true;
      push_queue (queue, node);
      active++;
    }
  ring->statistics.active = ring->unassigned = active;
  LOG ("enqueued in total %u active variables", active);
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
release_binaries (struct ring * ring)
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
  free (ring->trail.begin);
  free (ring->trail.pos);
  RELEASE (ring->levels);
  RELEASE (ring->buffer);
  release_references (ring);
  if (!ring->id)
    release_binaries (ring);
  free (ring->references);
  release_watches (ring);
  free (ring->queue.nodes);
  free (ring->queue.scores);
  free (ring->variables);
  free (ring->values);
  free (ring->marks);
  free (ring->active);
  free (ring->used);
  free (ring);
}

