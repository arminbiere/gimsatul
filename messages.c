#include "messages.h"

#include <assert.h>
#include <pthread.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

static pthread_mutex_t message_mutex = PTHREAD_MUTEX_INITIALIZER;

void
message_lock_failure (const char *str)
{
  char buffer[128];
  sprintf (buffer, "gimsatul: fatal message locking error: %s\n", str);
  size_t len = strlen (buffer);
  assert (len < sizeof buffer);
  if (write (1, buffer, len) != len)
    abort ();
  abort ();
}

void
acquire_message_lock (void)
{
  if (pthread_mutex_lock (&message_mutex))
    message_lock_failure ("failed to acquire message lock");
}

void
release_message_lock (void)
{
  if (pthread_mutex_unlock (&message_mutex))
    message_lock_failure ("failed to release message lock");
}

void
die (const char *fmt, ...)
{
  acquire_message_lock ();
  fputs ("gimsatul: error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  release_message_lock ();
  exit (1);
}

void
fatal_error (const char *fmt, ...)
{
  acquire_message_lock ();
  fputs ("gimsatul: fatal error: ", stderr);
  va_list ap;
  va_start (ap, fmt);
  vfprintf (stderr, fmt, ap);
  va_end (ap);
  fputc ('\n', stderr);
  fflush (stderr);
  release_message_lock ();
  abort ();
}

int verbosity;
const char *prefix_format = "c%-2u ";

#ifdef LOGGING
volatile uint64_t clause_ids;
#endif

#if 0

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
  if (ring)
    printf (prefix_format, ring->id);
  else
    fputs ("c ", stdout);
  va_list ap;
  va_start (ap, fmt);
  vprintf (fmt, ap);
  va_end (ap);
  fputc ('\n', stdout);
  fflush (stdout);
  release_message_lock ();
}

#endif
