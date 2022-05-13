#ifndef _trace_h_INCLUDED
#define _trace_h_INCLUDED

#include "file.h"

#include <stdbool.h>

extern struct file proof;
extern bool binary_proof_format;

void close_proof (void);

void really_trace_add_empty (struct buffer *);
void really_trace_add_unit (struct buffer *, unsigned unit);
void really_trace_add_binary (struct buffer *, unsigned , unsigned);
void really_trace_add_literals (struct buffer *,
                                size_t, unsigned *, unsigned except);

void really_trace_delete_literals (struct buffer *, size_t, unsigned *);
void really_trace_delete_binary (struct buffer *, unsigned, unsigned);

struct clause;
void really_trace_add_clause (struct buffer *, struct clause *);
void really_trace_delete_clause (struct buffer *, struct clause *);

/*------------------------------------------------------------------------*/

#define trace_add_empty(...) \
do { \
  if (proof.file) \
    really_trace_add_empty (__VA_ARGS__); \
} while (0)

#define trace_add_unit(...) \
do { \
  if (proof.file) \
    really_trace_add_unit (__VA_ARGS__); \
} while (0)

#define trace_add_binary(...) \
do { \
  if (proof.file) \
    really_trace_add_binary (__VA_ARGS__); \
} while (0)

#define trace_add_literals(...) \
do { \
  if (proof.file) \
    really_trace_add_literals (__VA_ARGS__); \
} while (0)

#define trace_add_clause(...) \
do { \
  if (proof.file) \
    really_trace_add_clause (__VA_ARGS__); \
} while (0)

#define trace_delete_literals(...) \
do { \
  if (proof.file) \
    really_trace_delete_literals (__VA_ARGS__); \
} while (0)

#define trace_delete_binary(...) \
do { \
  if (proof.file) \
    really_trace_delete_binary (__VA_ARGS__); \
} while (0)

#define trace_delete_clause(...) \
do { \
  if (proof.file) \
    really_trace_delete_clause (__VA_ARGS__); \
} while (0)

#endif
