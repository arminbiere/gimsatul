#ifndef _macros_h_INCLUDED
#define _macros_h_INCLUDED

#define INVALID UINT_MAX

#define IDX(LIT) ((LIT) >> 1)
#define LIT(IDX) ((IDX) << 1)
#define NOT(LIT) ((LIT) ^ 1u)
#define SGN(LIT) ((LIT) & 1)

#define MIN(A,B) ((A) < (B) ? (A) : (B))

#define SWAP(A,B) \
do { \
  typeof(A) TMP = (A); \
  (A) = (B); \
  (B) = TMP; \
} while (0)

#endif
