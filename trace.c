#include "stack.h"
#include "trace.h"
#include "message.h"
#include "utilities.h"

#include <inttypes.h>

struct file proof;
bool binary_proof_format;

static void
binary_proof_line (struct buffer *buffer,
                   size_t size, unsigned *literals, unsigned except)
{
  const unsigned *end = literals + size;
  for (const unsigned *p = literals; p != end; p++)
    {
      unsigned lit = *p;
      if (lit == except)
	continue;
      unsigned tmp = lit + 2;
      while (tmp & ~127u)
	{
	  unsigned char ch = (tmp & 0x7f) | 128;
	  PUSH (*buffer, ch);
	  tmp >>= 7;
	}
      PUSH (*buffer, (unsigned char) tmp);
    }
  PUSH (*buffer, 0);
}

static void
ascii_proof_line (struct buffer *buffer,
                  size_t size, unsigned *literals, unsigned except)
{
  const unsigned *end = literals + size;
  char tmp[32];
  for (const unsigned *p = literals; p != end; p++)
    {
      unsigned lit = *p;
      if (lit == except)
	continue;
      sprintf (tmp, "%d", export_literal (lit));
      for (char *q = tmp, ch; (ch = *q); q++)
	PUSH (*buffer, ch);
      PUSH (*buffer, ' ');
    }
  PUSH (*buffer, '0');
  PUSH (*buffer, '\n');
}

void
trace_add_literals (struct buffer *buffer,
                    size_t size, unsigned *literals, unsigned except)
{
  if (!proof.file)
    return;
  assert (EMPTY (*buffer));
  if (binary_proof_format)
    {
      PUSH (*buffer, 'a');
      binary_proof_line (buffer, size, literals, except);
    }
  else
    ascii_proof_line (buffer, size, literals, except);
  write_buffer (buffer, &proof);
}

void
trace_add_empty (struct buffer *buffer)
{
  if (proof.file)
    trace_add_literals (buffer, 0, 0, INVALID);
}

void
trace_add_unit (struct buffer *buffer, unsigned unit)
{
  if (proof.file)
    trace_add_literals (buffer, 1, &unit, INVALID);
}

void
trace_add_binary (struct buffer *buffer, unsigned lit, unsigned other)
{
  if (!proof.file)
    return;
  unsigned literals[2] = { lit, other };
  trace_add_literals (buffer, 2, literals, INVALID);
}

void
trace_delete_literals (struct buffer *buffer, size_t size, unsigned *literals)
{
  if (!proof.file)
    return;
  assert (EMPTY (*buffer));
  PUSH (*buffer, 'd');
  if (binary_proof_format)
    binary_proof_line (buffer, size, literals, INVALID);
  else
    {
      PUSH (*buffer, ' ');
      ascii_proof_line (buffer, size, literals, INVALID);
    }
  write_buffer (buffer, &proof);
}

void
trace_delete_binary (struct buffer *buffer, unsigned lit, unsigned other)
{
  if (!proof.file)
    return;
  unsigned literals[2] = { lit, other };
  trace_delete_literals (buffer, 2, literals);
}

void
close_proof (void)
{
  if (!proof.file)
    return;
  if (proof.close)
    fclose (proof.file);

  if (verbosity >= 0)
    {
      printf ("c\nc closed '%s' after writing %" PRIu64 " proof lines\n",
	      proof.path, proof.lines);
      fflush (stdout);
    }
}

