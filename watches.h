#ifndef _watches_h_INCLUDED
#define _watches_h_INCLUDED

#include <stdbool.h>

struct clause;
struct ring;
struct unsigneds;

struct watcher
{
  unsigned short used;
  unsigned char glue;
  bool garbage:1;
  bool reason:1;
  bool redundant:1;
  bool vivify:1;
#ifndef NMIDDLE
  unsigned middle;
#endif
  unsigned sum;
  struct clause *clause;
};

struct watchers
{
  struct watcher *begin, *end, *allocated;
};

/*------------------------------------------------------------------------*/

struct watch;

struct watches
{
  struct watch **begin, **end, **allocated;
};

struct references
{
  struct watch **begin, **end, **allocated;
  unsigned *binaries;
};

/*------------------------------------------------------------------------*/

#define all_watches(ELEM,WATCHES) \
  all_pointers_on_stack (struct watch, ELEM, WATCHES)

/*------------------------------------------------------------------------*/

struct watch *new_local_binary_clause (struct ring *ring, bool redundant,
				       unsigned lit, unsigned other);

struct watch *watch_literals_in_large_clause (struct ring *,
					      struct clause *,
					      unsigned first,
					      unsigned second);

struct watch *watch_first_two_literals_in_large_clause (struct ring *,
							struct clause *);

void mark_garbage_watch (struct ring *, struct watch *);
void mark_garbage_watcher (struct ring *, struct watcher *);

unsigned *map_watchers (struct ring *);
void flush_watchers (struct ring *);
void reconnect_watches (struct ring *, struct watches *saved);

void release_references (struct ring *);
void disconnect_references (struct ring *, struct watches *);
void sort_redundant_watcher_indices (struct ring *, size_t, unsigned *);

/*------------------------------------------------------------------------*/

#endif
