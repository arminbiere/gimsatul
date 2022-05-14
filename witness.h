#ifndef _witness_h_INCLUDED
#define _witness_h_INCLUDED

struct ring;

void extend_witness (struct ring *); 
void print_witness (struct ring *);

#ifndef NDEBUG

struct unsigneds;
void check_witness (struct ring *, struct unsigneds *);

#else

#define check_witness(...) do { } while (0)

#endif

#endif
