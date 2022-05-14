#include "message.h"
#include "stack.h"
#include "file.h"

#include <assert.h>
#include <inttypes.h>
#include <stdatomic.h>
#include <stdio.h>

void
write_buffer (struct buffer *buffer, struct file * file)
{
  assert (file);
  size_t size = SIZE (*buffer);
  fwrite (buffer->begin, size, 1, file->file);
  CLEAR (*buffer);
  atomic_fetch_add (&file->lines, 1);
}

void
close_proof (struct file * proof)
{
  if (!proof->file)
    return;
  if (proof->close)
    fclose (proof->file);

  if (verbosity >= 0)
    {
      printf ("c\nc closed '%s' after writing %" PRIu64 " proof lines\n",
	      proof->path, proof->lines);
      fflush (stdout);
    }
}
