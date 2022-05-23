#ifndef _clone_h_INCLUDED
#define _clone_h_INCLUDED

struct ring;
struct ruler;
void copy_ring (struct ring * dst, struct ring * src);
void copy_ruler (struct ring * dst, struct ruler * src);
void clone_rings (struct ruler *);

#endif
