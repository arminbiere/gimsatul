#include "ruler.h"
#include "message.h"
#include "utilities.h"
#include "witness.h"

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

void
extend_witness (struct ring * ring)
{
  LOG ("extending witness");
  struct ruler * ruler = ring->ruler;
#ifndef NDEBUG
  bool * eliminated = ruler->eliminated;
#endif
  signed char * ring_values = ring->values;
  signed char * ruler_values = (signed char*) ruler->values;
  unsigned initialized = 0;
  for (all_ring_indices (idx))
    {
      unsigned lit = LIT (idx);
      if (ring_values[lit])
	continue;
      signed char value = ruler_values[lit];
      if (!value)
	{
	  assert (eliminated[idx]);
	  value = INITIAL_PHASE;
	}
      else
	assert (!eliminated[idx]);
      unsigned not_lit = NOT (lit);
      ring_values[lit] = value;
      ring_values[not_lit] = -value;
      initialized++;
    }
  LOG ("initialized %u unassigned/eliminated variables", initialized);
  struct unsigneds * extension = &ruler->extension;
  unsigned * begin = extension->begin;
  unsigned * p = extension->end;
  unsigned pivot = INVALID;
  bool satisfied = false;
  size_t flipped = 0;
  LOG ("going through extension stack of size %zu", (size_t)(p - begin));
#ifdef LOGGING
  if (verbosity == INT_MAX)
    {
      LOG ("extension stack in reverse order:");
      unsigned * q = p;
      while (q != begin)
	{
	  unsigned * next = q;
	  while (*--next != INVALID)
	    ;
	  LOGPREFIX ("extension clause");
	  for (unsigned * c = next + 1; c != q; c++)
	    printf (" %s", LOGLIT (*c));
	  LOGSUFFIX ();
	  q = next;
	}
    }
#endif
  while (p != begin)
    {
      unsigned lit = *--p;
      if (lit == INVALID)
	{
	  if (!satisfied)
	    {
	      LOG ("flipping %s", LOGLIT (pivot));
	      assert (pivot != INVALID);
	      unsigned not_pivot = NOT (pivot);
	      assert (ring_values[pivot] < 0);
	      assert (ring_values[not_pivot] > 0);
	      ring_values[pivot] = 1;
	      ring_values[not_pivot] = -1;
	      flipped++;
	    }
	  satisfied = false;
	}
      else if (!satisfied)
	{
	  signed char value = ring_values[lit];
	  if (value > 0)
	    satisfied = true;
	}
      pivot = lit;
    }
  verbose (ring, "flipped %zu literals", flipped);
}

#ifndef NDEBUG

void
check_witness (struct ring *ring, struct unsigneds * original)
{
  signed char *values = ring->values;
  size_t clauses = 0;
  for (unsigned *c = original->begin, *p; c != original->end; c = p + 1)
    {
      bool satisfied = false;
      for (p = c; assert (p != original->end), *p != INVALID; p++)
	if (values[*p] > 0)
	  satisfied = true;
      clauses++;
      if (satisfied)
	continue;
      acquire_message_lock ();
      fprintf (stderr, "gimsatul: error: unsatisfied clause[%zu]", clauses);
      for (unsigned *q = c; q != p; q++)
	fprintf (stderr, " %d", export_literal (*q));
      fputs (" 0\n", stderr);
      release_message_lock ();
      abort ();
    }
}

#endif

struct line
{
  char buffer[80];
  size_t size;
};

static void
flush_line (struct line * line)
{
  fwrite (line->buffer, 1, line->size, stdout);
  fputc ('\n', stdout);
  line->size = 0;
}

static void
print_signed_literal (struct line * line, int lit)
{
  char buffer[32];
  sprintf (buffer, " %d", lit);
  size_t len = strlen (buffer);
  if (line->size + len >= sizeof line->buffer)
    flush_line (line);
  if (!line->size)
    line->buffer[line->size++] = 'v';
  memcpy (line->buffer + line->size, buffer, len);
  line->size += len;
}

static void
print_unsigned_literal (struct line * line,
                        signed char *values, unsigned unsigned_lit)
{
  assert (unsigned_lit < (unsigned) INT_MAX);
  int signed_lit = IDX (unsigned_lit) + 1;
  signed_lit *= values[unsigned_lit];
  print_signed_literal (line, signed_lit);
}

void
print_witness (struct ring *ring)
{
  signed char *values = ring->values;
  struct line line;
  line.size = 0;
  for (all_ring_indices (idx))
    print_unsigned_literal (&line, values, LIT (idx));
  print_signed_literal (&line, 0);
  if (line.size)
    flush_line (&line);
}

