#include "message.h"
#include "ruler.h"

#include <string.h>

void
init_barrier (struct barrier *barrier, const char * name, unsigned size)
{
  barrier->name = name;
  barrier->size = size;
  assert (!barrier->abort);
  if (size < 2)
    return;
  pthread_mutex_init (&barrier->mutex, 0);
  pthread_cond_init (&barrier->condition, 0);
}

void
abort_waiting (struct barrier * barrier)
{
  if (barrier->size < 2)
    return;
  if (pthread_mutex_lock (&barrier->mutex))
    fatal_error ("failed to acquire barrier lock to abort waiting");
  barrier->abort = true;
  if (pthread_mutex_unlock (&barrier->mutex))
    fatal_error ("failed to release barrier lock to abort waiting");
}

void
rendezvous (struct barrier * barrier, struct ring *ring)
{
  if (barrier->size < 2)
    return;
  if (pthread_mutex_lock (&barrier->mutex))
    fatal_error ("failed to acquire barrier lock during rendezvous");

  assert (barrier->waiting < barrier->size);
  barrier->waiting++;
  very_verbose (ring, "entered synchronization on '%s' (%u waiting)",
		barrier->name, barrier->waiting);

  while (!barrier->abort && barrier->waiting < barrier->size)
    pthread_cond_broadcast (&barrier->condition);

  very_verbose (ring, "leaving synchronization on '%s' (%u waiting)",
                barrier->name, barrier->waiting);
  assert (barrier->waiting);
  barrier->waiting--;

  while (barrier->waiting)
    pthread_cond_broadcast (&barrier->condition);

  if (pthread_mutex_unlock (&barrier->mutex))
    fatal_error ("failed to release barrier lock during rendezvous");
}
