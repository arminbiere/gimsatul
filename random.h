#ifndef _random_h_INCLUDED
#define _random_h_INCLUDED

#include <assert.h>
#include <stdint.h>
#include <stdlib.h>

static inline uint64_t
random64 (struct ring *ring)
{
  uint64_t res = ring->random, next = res;
  next *= 6364136223846793005ul;
  next += 1442695040888963407ul;
  ring->random = next;
  return res;
}

static inline unsigned
random32 (struct ring *ring)
{
  return random64 (ring) >> 32;
}

static inline size_t
random_modulo (struct ring *ring, size_t mod)
{
  assert (mod);
  size_t tmp = random64 (ring);
  size_t res = tmp % mod;
  assert (res < mod);
  return res;
}

static inline double
random_double (struct ring *ring)
{
  return random32 (ring) / 4294967296.0;
}

#endif
