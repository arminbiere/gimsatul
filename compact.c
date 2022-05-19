#include "compact.h"
#include "message.h"
#include "ruler.h"

static unsigned
map_literal (unsigned * map, unsigned original_lit)
{
  unsigned original_idx = IDX (original_lit);
  unsigned mapped_idx = map[original_idx];
  unsigned mapped_lit = LIT (mapped_idx);
  if (SGN (original_lit))
    mapped_lit = NOT (mapped_lit);
  return mapped_lit;
}

static void
map_occurrences (struct ruler * ruler, unsigned * map, unsigned src)
{
  unsigned dst = map_literal (map, src);
  struct clauses * src_occurrences = &OCCURRENCES (src);
  struct clauses * dst_occurrences = &OCCURRENCES (dst);
  *dst_occurrences = *src_occurrences;
  struct clause ** begin = dst_occurrences->begin;
  struct clause ** end = dst_occurrences->end;
  struct clause ** q = begin;
  for (struct clause ** p = begin; p != end; p++)
    {
      struct clause * src_clause = *p;
      if (!binary_pointer (src_clause))
	continue;
      assert (lit_pointer (src_clause) == src);
      unsigned src_other = other_pointer (src_clause);
      unsigned dst_other = map_literal (map, src_other);
      assert (!redundant_pointer (src_clause));
      struct clause * dst_clause = tag_pointer (false, dst, dst_other);
      *q++ = dst_clause;
    }
  dst_occurrences->end = q;
}

static void
map_large_clause (unsigned * map, struct clause * clause)
{
  assert (!binary_pointer (clause));
  assert (!clause->redundant);
  unsigned * literals = clause->literals;
  unsigned * end = literals + clause->size;
  for (unsigned * p = literals; p != end; p++)
    *p = map_literal (map, *p);
}

static void
map_clauses (struct ruler * ruler, unsigned * map)
{
  struct clauses * clauses = &ruler->clauses;
  struct clause ** begin = clauses->begin;
  struct clause ** end = clauses->end;
  for (struct clause ** p = begin; p != end; p++)
    map_large_clause (map, *p);
}

void
compact_ruler (struct ruler * ruler)
{
  if (ruler->inconsistent)
    return;
  bool * eliminated = ruler->eliminated;
  signed char * values = (signed char*) ruler->values;
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
  unsigned * unmap = allocate_array (compact, sizeof *unmap);
  ruler->map = unmap;
  unsigned * map = allocate_array (ruler->size, sizeof *map);
  unsigned mapped = 0;
  struct unsigneds * extension = ruler->extension + 2;
  for (all_ruler_indices (idx))
    {
      if (eliminated[idx])
	continue;
      unsigned lit = LIT (idx);
      if (values[lit])
	continue;
      unmap[mapped] = idx;
      map[idx] = mapped;
      PUSH (*extension, LIT (idx));
      PUSH (*extension, LIT (mapped));
      mapped++;
    }
  SHRINK_STACK (ruler->extension[2]);
  for (all_ruler_indices (idx))
    {
      unsigned lit = LIT (idx);
      unsigned not_lit = NOT (lit);
      if (!eliminated[idx] && !values[lit])
	{
	  map_occurrences (ruler, map, lit);
	  map_occurrences (ruler, map, not_lit);
	}
      else
	{
	  RELEASE (OCCURRENCES (lit));
	  RELEASE (OCCURRENCES (not_lit));
	}
    }
  assert (compact == mapped);
  ruler->compact = compact;
  map_clauses (ruler, map);
  message (0, "mapped %u variables to %u variables", ruler->size, mapped);
  free (ruler->eliminated);
  ruler->eliminated = 0;
  free (map);
}
