#include "random.h"
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
  if (fmt)
    va_start (ap, fmt);
  if (!fmt || *fmt == '\n')
    {
      if (ring)
	printf ("c%u\n", ring->id);
      else
	printf ("c\n");
      if (fmt)
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
init_ring (struct ring *ring)
{
  size_t size = ring->size;
  very_verbose (ring, "initializing 'ring[%u]' of size %zu", ring->id, size);

  assert (!ring->marks);
  if (ring->values)
    free (ring->values);
  assert (!ring->inactive);
  assert (!ring->used);

  ring->marks = allocate_and_clear_block (2 * size);
  ring->values = allocate_and_clear_block (2 * size);
  ring->inactive = allocate_and_clear_block (size);
  ring->used = allocate_and_clear_array (size, sizeof *ring->used);

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

static void
init_watchers (struct ring *ring)
{
  assert (EMPTY (ring->watchers));
  ENLARGE (ring->watchers);
  memset (ring->watchers.begin, 0, sizeof *ring->watchers.begin);
  ring->watchers.end++;
}

void
release_ring (struct ring *ring, bool keep_values)
{
  very_verbose (ring, "releasing 'ring[%u]' of size %u",
		ring->id, ring->size);

  FREE (ring->marks);
  if (!keep_values)
    FREE (ring->values);
  FREE (ring->inactive);
  FREE (ring->used);

  RELEASE (ring->analyzed);
  RELEASE (ring->clause);
  RELEASE (ring->levels);
  RELEASE (ring->minimize);

  FREE (ring->references);
  struct ring_trail *trail = &ring->trail;
  free (trail->begin);
  free (trail->pos);
  memset (trail, 0, sizeof *trail);
  FREE (ring->variables);
}

static void
activate_variables (struct ring * ring, unsigned size)
{
  if (!size)
    return;

  unsigned start, delta;
  if (size > 1 && ring->id && ring->options.random_order)
    {
      start = random_modulo (&ring->random, size);
      delta = 1 + random_modulo (&ring->random, size - 1);
      while (gcd (delta, size) != 1)
	if (++delta == size)
	  delta = 1;
      LOG ("random activation start %u delta %u", start, delta);
    }
  else
    {
      start = 0, delta = 1;
      LOG ("linear activation order");
    }

  assert (delta);
  assert (start < size);
  assert (size == 1 || delta < size);
  assert (gcd (delta, size) == 1);

  struct heap *heap = &ring->heap;
  struct queue *queue = &ring->queue;
  struct node * nodes = heap->nodes;
  struct link * links = queue->links;

  unsigned idx = start;
  unsigned activated = 0;
  do {
    assert (idx < size);

    struct node * node = nodes + idx;
    node->score = 1.0 - 1.0 / ++activated;
    push_heap (heap, node);
    LOG ("activating %s on heap", LOGVAR (idx));

    struct link * link = links + idx;
    enqueue (queue, link, true);
    LOG ("activating %s on queue", LOGVAR (idx));

    idx += delta;
    if (idx >= size)
      idx -= size;

  } while (idx != start);
  LOG ("activated %u variables", activated);
}

struct ring *
new_ring (struct ruler *ruler)
{
  unsigned size = ruler->compact;
  assert (size < (1u << 30));

  struct ring *ring = allocate_and_clear_block (sizeof *ring);
  ring->options = ruler->options;
#ifndef QUIET
  init_ring_profiles (ring);
#endif
  push_ring (ruler, ring);
  ring->size = size;
  verbose (ring, "new ring[%u] of size %u", ring->id, size);

  init_watchers (ring);
  init_ring (ring);

  struct heap *heap = &ring->heap;
  heap->nodes = allocate_and_clear_array (size, sizeof *heap->nodes);
  heap->increment = 1;

  ring->phases = allocate_and_clear_array (size, sizeof *ring->phases);

  struct queue *queue = &ring->queue;
  queue->links = allocate_and_clear_array (size, sizeof *queue->links);

  activate_variables (ring, size);

  ring->statistics.active = ring->unassigned = size;

  if ((ring->trace.file = ruler->trace.file))
    ring->trace.binary = ruler->trace.binary;

  for (all_averages (a))
    a->exp = 1.0;
  ring->limits.conflicts = -1;

  return ring;
}

static void
release_watchers (struct ring *ring)
{
  for (all_watchers (watcher))
    {
      assert (!is_binary_pointer (watcher));
      struct clause *clause = watcher->clause;
      unsigned shared = atomic_fetch_sub (&clause->shared, 1);
      assert (shared + 1);
      if (!shared)
	free (clause);
    }
  RELEASE (ring->watchers);
}

static void
release_saved (struct ring *ring)
{
  for (all_clauses (clause, ring->saved))
    {
      if (is_binary_pointer (clause))
	continue;
      unsigned shared = atomic_fetch_sub (&clause->shared, 1);
      assert (shared + 1);
      if (shared)
	continue;
      free (clause);
    }
  RELEASE (ring->saved);
}

void
init_pool (struct ring *ring, unsigned threads)
{
  ring->threads = threads;
  ring->pool = allocate_aligned_and_clear_array (CACHE_LINE_SIZE,
						 threads, sizeof *ring->pool);
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
      for (unsigned i = 1; i != SIZE_SHARED; i++)
	{
	  struct clause *clause = (struct clause *) pool->share[i];
	  if (!clause)
	    continue;
	  if (is_binary_pointer (clause))
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
  deallocate_aligned (CACHE_LINE_SIZE, ring->pool);
}

static void
release_binaries (struct ring *ring)
{
  if (ring->references)
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

  release_ring (ring, false);

  free (ring->heap.nodes);
  free (ring->phases);
  free (ring->queue.links);

  release_watchers (ring);
  release_saved (ring);

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
  trace_add_empty (&ring->trace);
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
mark_satisfied_watchers_as_garbage (struct ring *ring)
{
  size_t marked = 0;
  signed char *values = ring->values;
  struct variable *variables = ring->variables;
  size_t size = 0;
  for (all_watchers (watcher))
    {
      size++;
      if (watcher->garbage)
	continue;
      bool satisfied = false;
      for (all_watcher_literals (lit, watcher))
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
      mark_garbage_watcher (ring, watcher);
      marked++;
    }
  ring->last.fixed = ring->statistics.fixed;
  verbose (ring, "marked %zu satisfied clauses as garbage %.0f%%",
	   marked, percent (marked, size));
}
