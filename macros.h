#ifndef _macros_h_INCLUDED
#define _macros_h_INCLUDED

#define INVALID UINT_MAX
#define MAX_SIZE_T (~(size_t)0)

#define IDX(LIT) ((LIT) >> 1)
#define LIT(IDX) ((IDX) << 1)
#define NOT(LIT) ((LIT) ^ 1u)
#define SGN(LIT) ((LIT) & 1)

#define MIN(A,B) ((A) < (B) ? (A) : (B))
#define MAX(A,B) ((A) > (B) ? (A) : (B))

#define SWAP(TYPE,A,B) \
do { \
  TYPE TMP = (A); \
  (A) = (B); \
  (B) = TMP; \
} while (0)

#define GUARDED(FROM,TO,IDX,...) \
do { \
  if ((FROM) <= (IDX) && (IDX) <= TO) \
    MACRO (IDX, __VA_ARGS__); \
} while (0)

#define INSTANTIATE(FROM,TO,...) \
do { \
  assert (0 <= (FROM));  \
  assert ((TO) <= 31); \
  GUARDED(FROM,TO,0,__VA_ARGS__); \
  GUARDED(FROM,TO,1,__VA_ARGS__); \
  GUARDED(FROM,TO,2,__VA_ARGS__); \
  GUARDED(FROM,TO,3,__VA_ARGS__); \
  GUARDED(FROM,TO,4,__VA_ARGS__); \
  GUARDED(FROM,TO,5,__VA_ARGS__); \
  GUARDED(FROM,TO,6,__VA_ARGS__); \
  GUARDED(FROM,TO,7,__VA_ARGS__); \
  GUARDED(FROM,TO,8,__VA_ARGS__); \
  GUARDED(FROM,TO,9,__VA_ARGS__); \
  GUARDED(FROM,TO,10,__VA_ARGS__); \
  GUARDED(FROM,TO,11,__VA_ARGS__); \
  GUARDED(FROM,TO,12,__VA_ARGS__); \
  GUARDED(FROM,TO,13,__VA_ARGS__); \
  GUARDED(FROM,TO,14,__VA_ARGS__); \
  GUARDED(FROM,TO,15,__VA_ARGS__); \
  GUARDED(FROM,TO,16,__VA_ARGS__); \
  GUARDED(FROM,TO,17,__VA_ARGS__); \
  GUARDED(FROM,TO,18,__VA_ARGS__); \
  GUARDED(FROM,TO,19,__VA_ARGS__); \
  GUARDED(FROM,TO,20,__VA_ARGS__); \
  GUARDED(FROM,TO,21,__VA_ARGS__); \
  GUARDED(FROM,TO,22,__VA_ARGS__); \
  GUARDED(FROM,TO,23,__VA_ARGS__); \
  GUARDED(FROM,TO,24,__VA_ARGS__); \
  GUARDED(FROM,TO,25,__VA_ARGS__); \
  GUARDED(FROM,TO,26,__VA_ARGS__); \
  GUARDED(FROM,TO,27,__VA_ARGS__); \
  GUARDED(FROM,TO,28,__VA_ARGS__); \
  GUARDED(FROM,TO,29,__VA_ARGS__); \
  GUARDED(FROM,TO,30,__VA_ARGS__); \
  GUARDED(FROM,TO,31,__VA_ARGS__); \
} while (0)
#endif
