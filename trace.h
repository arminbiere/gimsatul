#ifndef _trace_h_INCLUDED
#define _trace_h_INCLUDED

#include "file.h"

#include <stdbool.h>

extern struct file proof;
extern bool binary_proof_format;

struct clause;

void trace_add_empty (struct buffer *);
void trace_add_unit (struct buffer *, unsigned unit);
void trace_add_binary (struct buffer *, unsigned , unsigned);
void trace_add_literals (struct buffer *, size_t, unsigned *, unsigned except);
void trace_add_clause (struct buffer *, struct clause *);

void trace_delete_literals (struct buffer *, size_t, unsigned *);
void trace_delete_binary (struct buffer *, unsigned, unsigned);
void trace_delete_clause (struct buffer *, struct clause *);

void close_proof (void);

#endif
