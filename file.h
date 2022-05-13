#ifndef _file_h_INCLUDED
#define _file_h_INCLUDED

#include <stdio.h>
#include <stdint.h>

struct file
{
  FILE *file;
  const char *path;
  uint64_t lines;
  int close;
};

struct buffer;

void write_buffer (struct buffer *, struct file *);

#endif
