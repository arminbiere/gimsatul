#include "assign.h"
#include "backtrack.h"
#include "import.h"
#include "message.h"
#include "random.h"
#include "ruler.h"
#include "trace.h"
#include "utilities.h"

#include "cover.h"

bool
import_units (struct ring *ring)
{
  assert (ring->pool);
  struct ruler *ruler = ring->ruler;
#ifndef NFASTPATH
  if (ring->units == ruler->units.end)
    return false;
#endif
  struct variable *variables = ring->variables;
  signed char *values = ring->values;
  unsigned level = ring->level;
  unsigned imported = 0;
  if (pthread_mutex_lock (&ruler->locks.units))
    fatal_error ("failed to acquire unit lock");
  while (ring->units != ruler->units.end)
    {
      unsigned unit = *ring->units++;
      LOG ("trying to import unit %s", LOGLIT (unit));
      signed char value = values[unit];
      if (level && value)
	{
	  unsigned idx = IDX (unit);
	  if (variables[idx].level)
	    value = 0;
	}
      if (value > 0)
	continue;
      very_verbose (ring, "importing unit %d",
		    unmap_and_export_literal (ruler->unmap, unit));
      INC_UNIT_CLAUSE_STATISTICS (imported);
      imported++;
      if (value < 0)
	{
	  set_inconsistent (ring, "imported falsified unit");
	  imported = INVALID;
	  break;
	}
      if (level)
	{
	  backtrack (ring, 0);
	  level = 0;
	}
      assert (!ring->level);
      assign_ring_unit (ring, unit);
    }
  if (pthread_mutex_unlock (&ruler->locks.units))
    fatal_error ("failed to release unit lock");
  if (!imported)
    return false;
  ring->iterating = -1;
  return true;
}

static void
really_import_binary_clause (struct ring *ring, unsigned lit, unsigned other)
{
  (void) new_local_binary_clause (ring, true, lit, other);
  trace_add_binary (&ring->trace, lit, other);
  INC_BINARY_CLAUSE_STATISTICS (imported);
}

static void
force_to_repropagate (struct ring *ring, unsigned lit)
{
  LOG ("forcing to repropagate %s", LOGLIT (lit));
  assert (ring->values[lit] < 0);
  unsigned idx = IDX (lit);
  struct variable *v = ring->variables + idx;
  if (ring->level > v->level)
    backtrack (ring, v->level);
  size_t pos = ring->trail.pos[idx];
  assert (pos < SIZE (ring->trail));
  LOG ("setting end of trail to %zu", pos);
  unsigned *propagate = ring->trail.begin + pos;
  assert (propagate < ring->trail.end);
  assert (*propagate == NOT (lit));
  ring->trail.propagate = propagate;
  if (!ring->level)
    ring->iterating = -1;
}

static bool
subsumed_binary (struct ring *ring, unsigned lit, unsigned other)
{
  if (!ring->options.subsume_imported)
    return false;
  ring->statistics.subsumed.binary.checked++;
  if (SIZE (REFERENCES (lit)) > SIZE (REFERENCES (other)))
    SWAP (unsigned, lit, other);
  bool res = false;
  for (all_watches (watch, REFERENCES (lit)))
    if (is_binary_pointer (watch) && other_pointer (watch) == other)
      {
	res = true;
	ring->statistics.subsumed.binary.succeeded++;
	break;
      }
  return res;
}

static bool
import_binary (struct ring *ring, struct clause *clause)
{
  assert (is_binary_pointer (clause));
  assert (redundant_pointer (clause));
  signed char *values = ring->values;
  unsigned lit = lit_pointer (clause);
  signed char lit_value = values[lit];
  unsigned lit_level = 0;
  if (lit_value)
    {
      lit_level = VAR (lit)->level;
      if (lit_value > 0 && !lit_level)
	return false;
    }
  unsigned other = other_pointer (clause);
  signed char other_value = values[other];
  unsigned other_level = 0;
  if (other_value)
    {
      other_level = VAR (other)->level;
      if (other_value > 0 && !other_level)
	return false;
    }

  if (lit_value < other_value ||
      (lit_value == other_value &&
       ((lit_value > 0 && lit_level > other_level) ||
        (lit_value < 0 && lit_level < other_level))))
    {
      SWAP (unsigned, lit, other);
      SWAP (signed char, lit_value, other_value);
      SWAP (unsigned, lit_level, other_level);
    }

#define SUBSUME_BINARY(LIT, OTHER) \
do { \
  if (subsumed_binary (ring, LIT, OTHER)) \
    { \
      LOGBINARY (true, LIT, OTHER, "subsumed imported"); \
      return false; \
    } \
} while (0)

  assert (lit_value >= other_value);

  if (lit_value >= 0 && other_value >= 0)
    {
      SUBSUME_BINARY (lit, other);
      LOGBINARY (true, lit, other, "importing (no propagation)");
      really_import_binary_clause (ring, lit, other);
      return false;
    }

  if (lit_value > 0 && other_value < 0 && lit_level <= other_level)
    {
      SUBSUME_BINARY (lit, other);
      LOGBINARY (true, lit, other, "importing (no propagation)");
      really_import_binary_clause (ring, lit, other);
      if (ring->context == PROBING_CONTEXT)
	{
	  ring->statistics.diverged++;
	  return true;
	}
      return false;
    }

  if (lit_value < 0 && lit_level < other_level)
    {
      fprintf (stderr, "lit %u@%u=%d\n", lit, lit_level, lit_value);
      fprintf (stderr, "other %u@%u=%d\n", other, other_level, other_value);
      fflush (stderr);
    }

  unsigned *pos = ring->trail.pos;
  unsigned lit_pos = pos[IDX (lit)];
  unsigned other_pos = pos[IDX (other)];

  COVER (lit_value < 0 && other_value >= 0);
  COVER (lit_value < 0 && lit_level < other_level);

  if (lit_value < 0 &&
      (other_value >= 0 ||
       lit_level < other_level ||
       (lit_level == other_level && lit_pos < other_pos)))
    {
      assert (other_value < 0);
      assert (lit_level >= other_level);
      SUBSUME_BINARY (lit, other);
      LOGBINARY (true, lit, other,
		 "importing (repropagate first literal %s)", LOGLIT (lit));
      force_to_repropagate (ring, lit);
      really_import_binary_clause (ring, lit, other);
      ring->statistics.diverged++;
      return true;
    }

  assert (other_value < 0 &&
	  (lit_value >= 0 ||
	   other_level < lit_level ||
	   (other_level == lit_level && other_pos < lit_pos)));

  SUBSUME_BINARY (lit, other);
  LOGBINARY (true, lit, other,
	     "importing (repropagate second literal %s))", LOGLIT (other));
  force_to_repropagate (ring, other);
  really_import_binary_clause (ring, lit, other);
  ring->statistics.diverged++;
  return true;
}

static bool
subsumed_large_clause (struct ring *ring, struct clause *clause)
{
  if (!ring->options.subsume_imported)
    return false;
  ring->statistics.subsumed.large.checked++;
  signed char *values = ring->values;
  struct variable *variables = ring->variables;
  signed char *marks = ring->marks;
  unsigned max_occurrences_lit = INVALID;
  size_t max_occurrences = 0;
  for (all_literals_in_clause (lit, clause))
    {
      signed char value = values[lit];
      unsigned idx = IDX (lit);
      struct variable *v = variables + idx;
      if (value < 0 && !v->level)
	continue;
      assert (!value || v->level);
      marks[lit] = 1;
      if (value < 0)
	continue;
      struct references *watches = &REFERENCES (lit);
      size_t tmp_occurrences = SIZE (*watches);
      if (tmp_occurrences <= max_occurrences)
	continue;
      max_occurrences = tmp_occurrences;
      max_occurrences_lit = lit;
    }
  bool res = false;
  for (all_literals_in_clause (lit, clause))
    {
      if (lit == max_occurrences_lit)
	continue;
      signed char lit_value = values[lit];
      if (lit_value < 0)
	continue;
      struct references *watches = &REFERENCES (lit);
      for (all_watches (watch, *watches))
	{
	  if (!redundant_pointer (watch))
	    continue;
	  unsigned blocking = other_pointer (watch);
	  assert (lit != blocking);
	  signed char blocking_mark = marks[blocking];
	  if (!blocking_mark)
	    {
	      signed char blocking_value = values[blocking];
	      if (blocking_value >= 0)
		continue;
	      unsigned blocking_idx = IDX (blocking);
	      struct variable *v = variables + blocking_idx;
	      if (v->level)
		continue;
	    }
	  if (is_binary_pointer (watch))
	    {
	      res = true;
	      LOGWATCH (watch, "subsuming");
	      break;
	    }
	  struct watcher *watcher = get_watcher (ring, watch);
	  res = true;
	  for (all_watcher_literals (other, watcher))
	    {
	      if (other == lit)
		continue;
	      if (other == blocking)
		continue;
	      signed char other_mark = marks[other];
	      if (other_mark)
		continue;
	      signed char other_value = values[other];
	      if (other_value < 0)
		{
		  unsigned other_idx = IDX (other);
		  struct variable *other_variable = variables + other_idx;
		  if (!other_variable->level)
		    continue;
		}
	      res = false;
	      break;
	    }
	  if (!res)
	    continue;
	  LOGWATCH (watch, "subsuming");
	  break;
	}
      if (res)
	break;
    }
  for (all_literals_in_clause (lit, clause))
    marks[lit] = 0;
  if (res)
    ring->statistics.subsumed.large.succeeded++;
  return res;
}

static void
really_import_large_clause (struct ring *ring, struct clause *clause,
			    unsigned first, unsigned second)
{
  watch_literals_in_large_clause (ring, clause, first, second);
  assert (clause->redundant);
  unsigned glue = clause->glue;
  assert (0 < glue);
  assert (glue <= ring->options.maximum_shared_glue);
  INC_LARGE_CLAUSE_STATISTICS (imported, glue);
}

static unsigned
find_literal_to_watch (struct ring *ring, struct clause *clause,
		       unsigned ignore, signed char *res_value_ptr,
		       unsigned *res_level_ptr)
{
  signed char *values = ring->values;
  unsigned res = INVALID, res_level = 0;
  signed char res_value = 0;
  for (all_literals_in_clause (lit, clause))
    {
      if (lit == ignore)
	continue;
      signed char lit_value = values[lit];
      unsigned lit_level = VAR (lit)->level;
      if (res != INVALID)
	{
	  if (lit_value < 0)
	    {
	      if (res_value >= 0)
		continue;
	      if (lit_level <= res_level)
		continue;
	    }
	  else if (lit_value > 0)
	    {
	      if (res_value > 0 && lit_level >= res_level)
		continue;
	    }
	  else
	    {
	      assert (!lit_value);
	      if (res_value >= 0)
		continue;
	    }
	}
      res = lit;
      res_level = lit_level;
      res_value = lit_value;
    }
  *res_value_ptr = res_value;
  *res_level_ptr = res_level;
  return res;
}

static bool
import_large_clause (struct ring *ring, struct clause *clause)
{
  signed char *values = ring->values;
  for (all_literals_in_clause (lit, clause))
    {
      if (values[lit] <= 0)
	continue;
      if (VAR (lit)->level)
	continue;
      LOGCLAUSE (clause, "not importing %s satisfied", LOGLIT (lit));
      dereference_clause (ring, clause);
      return false;
    }

  unsigned lit_level = 0;
  signed char lit_value = 0;
  unsigned lit = find_literal_to_watch (ring, clause, INVALID,
					&lit_value, &lit_level);
  unsigned other_level = 0;
  signed char other_value = 0;
  unsigned other = find_literal_to_watch (ring, clause, lit,
					  &other_value, &other_level);
  assert (lit_value >= other_value);

#define SUBSUME_LARGE_CLAUSE(CLAUSE) \
do { \
  if (subsumed_large_clause (ring, clause)) \
    { \
      dereference_clause (ring, clause); \
      return false; \
    } \
} while (0)

  if (lit_value >= 0 && other_value >= 0)
    {
      SUBSUME_LARGE_CLAUSE (clause);
      LOGCLAUSE (clause, "importing (no propagation)");
      really_import_large_clause (ring, clause, lit, other);
      return false;
    }

  if (lit_value > 0 && other_value < 0 && lit_level <= other_level)
    {
      SUBSUME_LARGE_CLAUSE (clause);
      LOGCLAUSE (clause, "importing (no propagation)");
      really_import_large_clause (ring, clause, lit, other);
      if (ring->context == PROBING_CONTEXT)
	{
	  ring->statistics.diverged++;
	  return true;
	}
      return false;
    }

  unsigned *pos = ring->trail.pos;
  unsigned lit_pos = pos[IDX (lit)];
  unsigned other_pos = pos[IDX (other)];

  if (lit_value < 0 &&
      lit_level == other_level && lit_pos < other_pos)
    {
      assert (other_value < 0);
      assert (lit_level >= other_level);
      SUBSUME_LARGE_CLAUSE (clause);
      LOGCLAUSE (clause, "importing (repropagate first watch %s)",
		 LOGLIT (lit));
      force_to_repropagate (ring, lit);
      really_import_large_clause (ring, clause, lit, other);
      ring->statistics.diverged++;
      return true;
    }

  assert (other_value < 0 &&
	  (lit_value >= 0 ||
	   other_level < lit_level ||
	   (other_level == lit_level && other_pos < lit_pos)));

  SUBSUME_LARGE_CLAUSE (clause);
  LOGCLAUSE (clause, "importing (repropagate second watch %s)",
	     LOGLIT (other));
  force_to_repropagate (ring, other);
  really_import_large_clause (ring, clause, lit, other);
  ring->statistics.diverged++;
  return true;
}

bool
import_shared (struct ring *ring)
{
  if (!ring->pool)
    return false;
  if (import_units (ring))
    return true;
  if (!ring->import_after_propagation_and_conflict)
    return 
  ring->import_after_propagation_and_conflict = false;
  struct ruler *ruler = ring->ruler;
  size_t rings = SIZE (ruler->rings);
  assert (rings <= UINT_MAX);
  assert (rings > 1);
  unsigned id = random_modulo (&ring->random, rings - 1) + ring->id + 1;
  if (id >= rings)
    id -= rings;
  assert (id < rings);
  assert (id != ring->id);
  struct ring *src = ruler->rings.begin[id];
  assert (src->pool);
  struct pool *pool = src->pool + ring->id;
  atomic_uintptr_t *end = pool->share + SIZE_SHARED;
  struct clause *clause = 0;
  for (atomic_uintptr_t * p = pool->share; !clause && p != end; p++)
#ifndef NFASTPATH
    if (*p)
#endif
      clause = (struct clause *) atomic_exchange (p, 0);
  if (!clause)
    return false;
  if (is_binary_pointer (clause))
    return import_binary (ring, clause);
  if (clause->glue > TIER1_GLUE_LIMIT && !ring->stable)
    {
      dereference_clause (ring, clause);
      return false;
    }
  return import_large_clause (ring, clause);
}
