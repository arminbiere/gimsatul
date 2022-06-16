#ifndef QUIET

#include "message.h"
#include "ruler.h"
#include "statistics.h"
#include "utilities.h"

#include <inttypes.h>

void
print_ring_statistics (struct ring *ring)
{
  print_ring_profiles (ring);
  double search = ring->profiles.search.time;
  double walk = ring->profiles.solve.time;
  struct ring_statistics *s = &ring->statistics;
  struct context *c = s->contexts + SEARCH_CONTEXT;
  uint64_t conflicts = c->conflicts;
  uint64_t decisions = c->decisions;
  uint64_t propagations = c->propagations;
#ifdef METRICS
  uint64_t visits = 0;
  for (unsigned i = 0; i != SIZE_VISITS; i++)
    visits += c->visits[i];
#endif
  unsigned variables = ring->ruler->size;
  PRINTLN ("%-22s %17" PRIu64 " %13.2f per second", "conflicts:",
	   conflicts, average (conflicts, search));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f per second", "decisions:",
	   decisions, average (decisions, search));
  PRINTLN ("%-22s %17u %13.2f %% variables", "solving-fixed:",
	   s->fixed, percent (s->fixed, variables));
  PRINTLN ("%-22s %17u %13.2f %% variables", "failed-literals:",
	   s->failed, percent (s->failed, variables));
  PRINTLN ("%-22s %17u %13.2f %% variables", "lifted-literals:",
	   s->lifted, percent (s->lifted, variables));
  PRINTLN ("%-22s %17u %13.2f %% variables", "fixed-variables:",
	   s->fixed, percent (s->fixed, variables));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% fixed",
	   "  learned-units:", s->learned.units,
	   percent (s->learned.units, s->fixed));
  if (ring->pool)
    {
      PRINTLN ("%-22s %17" PRIu64 " %13.2f %% fixed",
	       "  imported-units:", s->imported.units,
	       percent (s->imported.units, s->fixed));
      PRINTLN ("%-22s %17" PRIu64 " %13.2f %% fixed",
	       "  exported-units:", s->exported.units,
	       percent (s->exported.units, s->fixed));
    }

  PRINTLN ("%-22s %17" PRIu64 " %13.2f thousands per second",
	   "flips:", s->flips, average (s->flips, 1e3 * walk));

  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% per learned clause",
	   "vivified-clauses:", s->vivify.succeeded,
	   percent (s->vivify.succeeded, s->learned.clauses));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% per vivified clause",
	   "vivify-implied:", s->vivify.implied,
	   percent (s->vivify.implied, s->vivify.succeeded));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% per vivified clause",
	   "vivify-strengthened:", s->vivify.strengthened,
	   percent (s->vivify.strengthened, s->vivify.succeeded));

  PRINTLN ("%-22s %17" PRIu64 " %13.2f per learned clause",
	   "learned-literals:", s->literals.learned,
	   average (s->literals.learned, s->learned.clauses));
#ifdef METRICS
  PRINTLN ("%-22s %17" PRIu64 " %13.2f times learned literals",
	   "  deduced-literals:", s->literals.deduced,
	   average (s->literals.deduced, s->literals.learned));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% per deduced literal",
	   "  minimized-literals:", s->literals.minimized,
	   percent (s->literals.minimized, s->literals.deduced));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% per deduced literal",
	   "  shrunken-literals:", s->literals.shrunken,
	   percent (s->literals.shrunken, s->literals.deduced));
#endif

#define PRINT_CLAUSE_METRICS(NAME) \
do { \
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% " #NAME " clauses", \
	   "  " #NAME "-binaries:", s->NAME.binaries, \
	   percent (s->NAME.binaries, s->NAME.clauses)); \
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% " #NAME " clauses", \
	   "  " #NAME "-tier1:", s->NAME.tier1, \
	   percent (s->NAME.tier1, s->NAME.clauses)); \
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% " #NAME " clauses", \
	   "  " #NAME "-tier2:", s->NAME.tier2, \
	   percent (s->NAME.tier2, s->NAME.clauses)); \
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% " #NAME " clauses", \
	   "  " #NAME "-tier3:", s->NAME.tier3, \
	   percent (s->NAME.tier3, s->NAME.clauses)); \
  INSTANTIATE(1,SIZE_GLUE_STATISTICS-1,NAME); \
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% learned", \
	   "  " #NAME "-glue-large:", s->NAME.glue[0], \
	   percent (s->NAME.glue[0], s->NAME.clauses)); \
} while (0)

#define MACRO(SIZE,NAME) \
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% " #NAME " clauses", \
	   "  " #NAME "-glue" #SIZE ":", s->NAME.glue[SIZE], \
	   percent (s->NAME.glue[SIZE], s->NAME.clauses))

  PRINTLN ("%-22s %17" PRIu64 " %13.2f per second",
	   "learned-clauses:", s->learned.clauses,
	   average (s->learned.clauses, search));
  PRINT_CLAUSE_METRICS (learned);

  if (ring->pool)
    {
      PRINTLN ("%-22s %17" PRIu64 " %13.2f %% learned clauses",
	       "imported-clauses:", s->imported.clauses,
	       percent (s->imported.clauses, s->learned.clauses));
      PRINT_CLAUSE_METRICS (imported);

      PRINTLN ("%-22s %17" PRIu64 " %13.2f %% learned clauses",
	       "exported-clauses:", s->exported.clauses,
	       percent (s->exported.clauses, s->learned.clauses));
      PRINT_CLAUSE_METRICS (exported);
    }

#undef MACRO

  PRINTLN ("%-22s %17" PRIu64 " %13.2f millions per second",
	   "propagations:", propagations, average (propagations,
						   1e6 * search));
#ifdef METRICS
  PRINTLN ("%-22s %17" PRIu64 " %13.2f per propagation",
	   "visits:", visits, average (visits, propagations));
#define MACRO(SIZE,DUMMY) \
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% visits", \
	   "  visits" #SIZE ":", c->visits[SIZE], percent (c->visits[SIZE], visits))
  INSTANTIATE(SIZE_WATCHER_LITERALS + 1, SIZE_VISITS-1);
#undef MACRO
  PRINTLN ("%-22s %17" PRIu64 " %13.2f %% visits", \
	   "  visits-large:", c->visits[0], percent (c->visits[0], visits));
#endif

  PRINTLN ("%-22s %17" PRIu64 " %13.2f conflict interval",
	   "probings:", s->probings, average (conflicts, s->probings));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f conflict interval",
	   "reductions:", s->reductions, average (conflicts, s->reductions));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f conflict interval",
	   "rephased:", s->rephased, average (conflicts, s->rephased));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f conflict interval",
	   "restarts:", s->restarts, average (conflicts, s->restarts));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f conflict interval",
	   "simplifications:", s->simplifications,
	   average (conflicts, s->simplifications));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f conflict interval",
	   "switched:", s->switched, average (conflicts, s->switched));
  PRINTLN ("%-22s %17" PRIu64 " %13.2f flips per walkinterval",
	   "walked:", s->walked, average (s->flips, s->walked));
  fflush (stdout);
}

void
print_ruler_statistics (struct ruler *ruler)
{
  if (verbosity < 0)
    return;

  for (all_rings (ring))
    {
      print_ring_statistics (ring);
      printf ("c\n");
    }

  print_ruler_profiles (ruler);

  double process = process_time ();
  double total = current_time () - start_time;
  double memory = maximum_resident_set_size () / (double) (1 << 20);

  struct ruler_statistics *s = &ruler->statistics;

  unsigned variables = ruler->size;

  printf ("c %-22s %17u %13.2f %% variables\n", "eliminated:",
	  s->eliminated, percent (s->eliminated, variables));
  printf ("c %-22s %17u %13.2f %% eliminated variables\n", "definitions:",
	  s->definitions, percent (s->definitions, s->eliminated));
  printf ("c %-22s %17" PRIu64 " %13.2f %% variables\n", "substituted:",
	  s->substituted, percent (s->substituted, variables));
  printf ("c %-22s %17" PRIu64 " %13.2f %% subsumed clauses\n",
	  "deduplicated:", s->deduplicated, percent (s->deduplicated,
						     s->subsumed));
  printf ("c %-22s %17" PRIu64 " %13.2f %% subsumed clauses\n",
	  "self-subsumed::", s->selfsubsumed, percent (s->selfsubsumed,
						       s->subsumed));
  printf ("c %-22s %17" PRIu64 " %13.2f %% original clauses\n",
	  "strengthened:", s->strengthened, percent (s->strengthened,
						     s->original));
  printf ("c %-22s %17" PRIu64 " %13.2f %% original clauses\n", "subsumed:",
	  s->subsumed, percent (s->subsumed, s->original));
  printf ("c %-22s %17zu %13.2f %% original clauses\n", "weakened:",
	  s->weakened, percent (s->weakened, s->original));
  printf ("c %-22s %17u %13.2f %% total-fixed\n", "simplifying-fixed:",
	  s->fixed.simplifying, percent (s->fixed.simplifying,
					 s->fixed.total));
  printf ("c %-22s %17u %13.2f %% total-fixed\n", "solving-fixed:",
	  s->fixed.solving, percent (s->fixed.solving, s->fixed.total));
  printf ("c %-22s %17u %13.2f %% variables\n", "total-fixed:",
	  s->fixed.total, percent (s->fixed.total, variables));

  printf ("c\n");

  printf ("c %-30s %23.2f %%\n", "utilization:",
	  percent (process / ruler->options.threads, total));
  printf ("c %-30s %23.2f seconds\n", "process-time:", process);
  printf ("c %-30s %23.2f seconds\n", "wall-clock-time:", total);
  printf ("c %-30s %23.2f MB\n", "maximum-resident-set-size:", memory);

  fflush (stdout);
}

#endif
