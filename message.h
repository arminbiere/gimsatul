#ifndef _messages_h_INCLUDED
#define _messages_h_INCLUDED

#include <stdint.h>

extern const char *prefix_format;
extern int verbosity;

#ifdef LOGGING
extern volatile uint64_t clause_ids;
#endif

void message_lock_failure (const char *str);
void acquire_message_lock (void);
void release_message_lock (void);

void die (const char *, ...) __attribute__((format (printf, 1, 2)));
void fatal_error (const char *, ...) __attribute__((format (printf, 1, 2)));

struct ring;

void print_line_without_acquiring_lock (struct ring *, const char *, ...)
__attribute__((format (printf, 2, 3)));

void message (struct ring *ring, const char *, ...)
  __attribute__((format (printf, 2, 3)));

#define PRINTLN(...) \
  print_line_without_acquiring_lock (ring, __VA_ARGS__)

#define verbose(...) \
do { \
  if (verbosity > 0) \
    message (__VA_ARGS__); \
} while (0)

#define very_verbose(...) \
do { \
  if (verbosity > 1) \
    message (__VA_ARGS__); \
} while (0)

#endif
