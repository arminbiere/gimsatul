#include "compact.h"
#include "message.h"
#include "ruler.h"
#include "simplify.h"

static unsigned
map_literal (unsigned *map, unsigned original_lit)
{
  unsigned original_idx = IDX (original_lit);
  unsigned mapped_idx = map[original_idx];
  if (mapped_idx == INVALID)
    return INVALID;
  unsigned mapped_lit = LIT (mapped_idx);
  if (SGN (original_lit))
    mapped_lit = NOT (mapped_lit);
  return mapped_lit;
}

static void
map_occurrences (struct ruler *ruler, unsigned *map, unsigned src)
{
  unsigned dst = map_literal (map, src);
  struct clauses *src_occurrences = &OCCURRENCES (src);
  struct clauses *dst_occurrences = &OCCURRENCES (dst);
  *dst_occurrences = *src_occurrences;
  struct clause **begin = dst_occurrences->begin;
  struct clause **end = dst_occurrences->end;
  struct clause **q = begin;
  for (struct clause ** p = begin; p != end; p++)
    {
      struct clause *src_clause = *p;
      if (!binary_pointer (src_clause))
	continue;
      assert (lit_pointer (src_clause) == src);
      unsigned src_other = other_pointer (src_clause);
      unsigned dst_other = map_literal (map, src_other);
      assert (!redundant_pointer (src_clause));
      struct clause *dst_clause = tag_pointer (false, dst, dst_other);
      *q++ = dst_clause;
    }
  dst_occurrences->end = q;
}

static void
map_large_clause (unsigned *map, struct clause *clause)
{
  assert (!binary_pointer (clause));
  assert (!clause->redundant);
  unsigned *literals = clause->literals;
  unsigned *end = literals + clause->size;
  for (unsigned *p = literals; p != end; p++)
    *p = map_literal (map, *p);
}

static void
map_clauses (struct ruler *ruler, unsigned *map)
{
  struct clauses *clauses = &ruler->clauses;
  struct clause **begin = clauses->begin;
  struct clause **end = clauses->end;
  for (struct clause ** p = begin; p != end; p++)
    map_large_clause (map, *p);
}

static void
compact_phases (struct ring * ring,
                unsigned old_size, unsigned new_size,
		unsigned * map)
{
  struct phases * old_phases = ring->phases;
  struct phases * new_phases = ring->phases =
     allocate_array (new_size, sizeof *new_phases);
  struct phases * old_phase = old_phases;
  struct phases * new_phase = new_phases;
  unsigned * end = map + old_size;
  for (unsigned * mapped = map; mapped != end; mapped++, old_phase++)
    {
      unsigned new_idx = *mapped;
      if (new_idx == INVALID)
	continue;
      assert (new_phases + new_idx == new_phase);
      *new_phase++ = *old_phase;
    }
  assert (old_phase == old_phases + old_size);
  assert (new_phase == new_phases + new_size);
  free (old_phases);
}

static void
compact_heap (struct ring * ring, struct heap * heap,
              unsigned old_size, unsigned new_size, unsigned * map)
{
  struct node * old_nodes = heap->nodes;
  struct node * new_nodes = heap->nodes =
    allocate_and_clear_array (new_size, sizeof *new_nodes);
  heap->root = 0;
  struct node * new_node = new_nodes, *old_node = old_nodes;
  unsigned * end = map + old_size;
  for (unsigned * mapped = map; mapped != end; mapped++, old_node++)
    {
      unsigned new_idx = *mapped;
      if (new_idx == INVALID)
	continue;
      assert (new_nodes + new_idx == new_node);
      new_node->score = old_node->score;
      push_heap (heap, new_node);
      new_node++;
    }
  assert (old_node == old_nodes + old_size);
  assert (new_node == new_nodes + new_size);
  free (old_nodes);
}

static void
compact_queue (struct ring * ring, struct queue * queue,
               unsigned old_size, unsigned new_size, unsigned * map)
{
  struct link * old_links = queue->links;
  struct link * new_links = queue->links =
    allocate_and_clear_array (new_size, sizeof *new_links);
  struct link * first = queue->first;
  queue->first = queue->last = 0;
  queue->stamp = 0;
  for (struct link * old_link = first; old_link; old_link = old_link->next)
    {
      unsigned old_idx = old_link - old_links;
      unsigned new_idx = map[old_idx];
      if (new_idx == INVALID)
	continue;
      struct link * new_link = new_links + new_idx;
      enqueue (queue, new_link, false);
    }
  assert (queue->stamp == new_size);
  reset_queue_search (queue);
  free (old_links);
}

static void
compact_clauses (struct ring * ring,
                 struct clauses * clauses, unsigned * map)
{
  struct clause ** begin = clauses->begin;
  struct clause ** end = clauses->end;
  struct clause ** q = begin;
  struct clause ** p = q;
  while (p != end)
    {
      struct clause * src_clause = *p++;
      struct clause * dst_clause = 0;
      if (binary_pointer (src_clause))
	{
	  assert (redundant_pointer (src_clause));
	  unsigned src_lit = lit_pointer (src_clause);
	  unsigned src_other = other_pointer (src_clause);
	  unsigned dst_lit = map_literal (map, src_lit);
	  unsigned dst_other = map_literal (map, src_other);
	  if (dst_lit != INVALID && dst_other != INVALID)
	    {
	      LOGCLAUSE (src_clause, "original");
	      if (dst_lit < dst_other)
		dst_clause = tag_pointer (true, dst_lit, dst_other);
	      else
		dst_clause = tag_pointer (true, dst_other, dst_lit);
	      assert (dst_clause);
	    }
	}
      else
	{
	  dst_clause = src_clause;
	  for (all_literals_in_clause (src_lit, src_clause))
	    if (map_literal (map, src_lit) == INVALID)
	      {
		dst_clause = 0;
		break;
	      }
	  LOGCLAUSE (src_clause, "original");
	  if (dst_clause)
	    {
	      unsigned * literals = dst_clause->literals;
	      unsigned * end = literals + dst_clause->size;
	      for (unsigned * p = literals; p != end; p++)
		*p = map_literal (map, *p);
	    }
	}
      if (dst_clause)
	{
	  LOGCLAUSE (dst_clause, "mapped");
	  *q++ = dst_clause;
	}
      else
	{
	  LOGCLAUSE (src_clause, "flushing");
	  assert (ring->statistics.redundant);
	  ring->statistics.redundant--;
	}
    }
#ifndef QUIET
  size_t flushed = end - q;
  size_t kept = q - begin;
  verbose (ring, "flushed %zu clauses during compaction", flushed);
  verbose (ring, "kept %zu clauses during compaction", kept);
#endif
  clauses->end = q;
}

static void
compact_ring (struct ring * ring, unsigned * map)
{
  struct ruler * ruler = ring->ruler;
  unsigned old_size = ring->size;
  unsigned new_size = ruler->compact;
  assert (new_size <= old_size);
  (void) old_size, (void) new_size;

  ring->best = 0;
  assert (ring->context == SEARCH_CONTEXT);
  assert (!ring->level);
  ring->probe = ring->id * (new_size / SIZE (ruler->rings));
  ring->size = new_size;
  ring->target = 0;
  ring->unassigned = new_size;;

  init_ring (ring);

  compact_phases (ring, old_size, new_size, map);
  compact_heap (ring, &ring->heap, old_size, new_size, map);
  compact_queue (ring, &ring->queue, old_size, new_size, map);

  assert (EMPTY (ring->watches));
  compact_clauses (ring, &ring->saved, map);
}

void
compact_ruler (struct simplifier *simplifier, bool preprocessing)
{
  struct ruler *ruler = simplifier->ruler;
  if (ruler->inconsistent)
    return;
  bool *eliminated = simplifier->eliminated;
  signed char *values = (signed char *) ruler->values;
  unsigned compact = 0;
  for (all_ruler_indices (idx))
    {
      if (eliminated[idx])
	continue;
      unsigned lit = LIT (idx);
      if (values[lit])
	continue;
      compact++;
    }
  unsigned *unmap = allocate_array (compact, sizeof *unmap);
  unsigned *old_map = ruler->map;
  ruler->map = unmap;
  for (all_rings (ring))
    ring->trace.map = unmap;
  unsigned old_compact = ruler->compact;
  unsigned *map = allocate_array (old_compact, sizeof *map);
  unsigned mapped = 0;
  for (all_ruler_indices (idx))
    {
      unsigned lit = LIT (idx);
      if (eliminated[idx])
	{
	  map[idx] = INVALID;
#ifdef LOGGING
	  if (old_map)
	    ROG ("skipping eliminated variable %u (literal %u) "
	         "which was original variable %u (literal %u)",
		 idx, lit, old_map[idx], LIT (old_map[idx]));
	  else
	    ROG ("skipping eliminated original variable %u (literal %u)",
	         idx, lit);
#endif
	  continue;
	}
      if (values[lit])
	{
	  map[idx] = INVALID;
#ifdef LOGGING
	  if (old_map)
	    ROG ("skipping assigned variable %u (literal %u) "
	         "which was original variable %u (literal %u)",
		 idx, lit, old_map[idx], LIT (old_map[idx]));
	  else
	    ROG ("skipping assigned original variable %u (literal %u)",
	         idx, lit);
#endif
	  continue;
	}
      unsigned old_idx = old_map ? old_map[idx] : idx;
      unmap[mapped] = old_idx;
      map[idx] = mapped;
#ifdef LOGGING
      if (old_map)
	ROG ("mapping variable %u (literal %u) which was originally "
	     "variable %u (literal %u) to variable %u (literal %u)",
	     idx, lit, old_idx, LIT (old_idx), mapped, LIT (mapped));
      else
	ROG ("mapping original variable %u (literal %u) "
	     "to variable %u (literal %u)",
	     idx, lit, mapped, LIT (mapped));
#endif
      mapped++;
    }
  if (old_map)
    free (old_map);
  SHRINK_STACK (ruler->extension);
  for (all_ruler_indices (idx))
    {
      unsigned lit = LIT (idx);
      unsigned not_lit = NOT (lit);
      if (!eliminated[idx] && !values[lit])
	{
	  assert (map[idx] <= idx);
	  map_occurrences (ruler, map, lit);
	  map_occurrences (ruler, map, not_lit);
	}
      else
	{
	  assert (map[idx] == INVALID);
	  RELEASE (OCCURRENCES (lit));
	  RELEASE (OCCURRENCES (not_lit));
	}
    }
  assert (compact == mapped);
  ruler->compact = compact;

  map_clauses (ruler, map);

  if (!preprocessing)
    for (all_rings (ring))
      compact_ring (ring, map);

  free (map);

  free ((void *) ruler->values);
  ruler->values = allocate_and_clear_block (2 * compact);

  free (ruler->units.begin);
  ruler->units.begin = allocate_array (compact, sizeof (unsigned));
  ruler->units.propagate = ruler->units.end = ruler->units.begin;

  message (0, "mapped %u variables to %u variables", ruler->size, mapped);
}
