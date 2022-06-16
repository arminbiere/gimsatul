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

#define GUARDED(FROM,TO,IDX) \
do { \
  if ((FROM) <= (IDX) && (IDX) <= TO) \
    MACRO (IDX) \
} while (0)

#define INSTANTIATE(FROM,TO) \
do { \
  assert (0 <= (FROM));  \
  assert ((TO) <= 15); \
  GUARDED(FROM,TO,0); \
  GUARDED(FROM,TO,1); \
  GUARDED(FROM,TO,2); \
  GUARDED(FROM,TO,3); \
  GUARDED(FROM,TO,4); \
  GUARDED(FROM,TO,5); \
  GUARDED(FROM,TO,6); \
  GUARDED(FROM,TO,7); \
  GUARDED(FROM,TO,8); \
  GUARDED(FROM,TO,9); \
  GUARDED(FROM,TO,10); \
  GUARDED(FROM,TO,11); \
  GUARDED(FROM,TO,12); \
  GUARDED(FROM,TO,13); \
  GUARDED(FROM,TO,14); \
  GUARDED(FROM,TO,15); \
} while (0)
#endif
