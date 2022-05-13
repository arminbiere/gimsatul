#include "stack.h"
#include "file.h"

#include <assert.h>
#include <stdatomic.h>

void
write_buffer (struct buffer *buffer, struct file * file)
{
  assert (file);
  size_t size = SIZE (*buffer);
  fwrite (buffer->begin, size, 1, file->file);
  CLEAR (*buffer);
  atomic_fetch_add (&file->lines, 1);
}
