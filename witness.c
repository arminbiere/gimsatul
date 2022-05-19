#include "ruler.h"
#include "message.h"
#include "utilities.h"
#include "witness.h"

#include <assert.h>
#include <stdlib.h>
#include <stdio.h>
#include <string.h>

signed char *
extend_witness (struct ring * ring)
{
  struct ruler * ruler = ring->ruler;
  LOG ("extending witness from %u to %u variables",
       ring->size, ruler->size);
  signed char * values = allocate_array (2*ruler->size, sizeof *values);
  memcpy (values, ring->values, 2*ring->size);
#if 1
  for (unsigned idx = 0; idx != ruler->size; idx++)
    {
      unsigned lit = LIT (idx);
      if (values[lit])
	continue;
      unsigned not_lit = NOT (lit);
      values[lit] = 1;
      values[not_lit] = -1;
    }
#else
  for (unsigned idx = ring->size; idx != ruler->size; idx++)
    {
      unsigned lit = LIT (idx);
      unsigned not_lit = NOT (lit);
      values[lit] = 1;
      values[not_lit] = -1;
    }
#endif
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
	      assert (values[pivot] < 0);
	      assert (values[not_pivot] > 0);
	      values[pivot] = 1;
	      values[not_pivot] = -1;
	      flipped++;
	    }
	  satisfied = false;
	}
      else if (!satisfied)
	{
	  signed char value = values[lit];
	  if (value > 0)
	    satisfied = true;
	}
      pivot = lit;
    }
  verbose (ring, "flipped %zu literals", flipped);
  return values;
}

#ifndef NDEBUG

void
check_witness (unsigned * map, signed char * values, struct unsigneds * original)
{
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
	fprintf (stderr, " %d", export_literal (map, *q));
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
print_witness (unsigned size, signed char * values)
{
  struct line line;
  line.size = 0;
  for (unsigned idx = 0; idx != size; idx++)
    print_unsigned_literal (&line, values, LIT (idx));
  print_signed_literal (&line, 0);
  if (line.size)
    flush_line (&line);
}

