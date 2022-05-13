#ifndef _tagging_h_INCLUDED
#define _tagging_h_INCLUDED

#include <assert.h>
#include <stdlib.h>
#include <stdbool.h>

static inline bool
tagged_literal (unsigned lit)
{
  return lit & 1;
}

static inline unsigned
untag_literal (unsigned lit)
{
  return lit >> 1;
}

static inline unsigned
tag_literal (bool tag, unsigned lit)
{
  assert (lit < (1u << 31));
  unsigned res = tag | (lit << 1);
  assert (untag_literal (res) == lit);
  assert (tagged_literal (res) == tag);
  return res;
}

static inline unsigned
lower_pointer (void *watch)
{
  return (size_t) watch;
}

static inline unsigned
upper_pointer (void *watch)
{
  return (size_t) watch >> 32;
}

static inline bool
binary_pointer (void *watch)
{
  unsigned lower = lower_pointer (watch);
  return tagged_literal (lower);
}

static inline bool
redundant_pointer (void *watch)
{
  assert (binary_pointer (watch));
  unsigned upper = upper_pointer (watch);
  return tagged_literal (upper);
}

static inline unsigned
lit_pointer (void *watch)
{
  assert (binary_pointer (watch));
  unsigned lower = lower_pointer (watch);
  return untag_literal (lower);
}

static inline unsigned
other_pointer (void *watch)
{
  assert (binary_pointer (watch));
  unsigned upper = upper_pointer (watch);
  return untag_literal (upper);
}

static inline void *
tag_pointer (bool redundant, unsigned lit, unsigned other)
{
  unsigned lower = tag_literal (true, lit);
  unsigned upper = tag_literal (redundant, other);
  size_t word = lower | (size_t) upper << 32;
  void *res = (void *) word;
  assert (binary_pointer (res));
  assert (lit_pointer (res) == lit);
  assert (other_pointer (res) == other);
  assert (redundant_pointer (res) == redundant);
  return res;
}

#endif
