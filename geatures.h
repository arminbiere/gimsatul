#ifndef _features_h_INCLUDED
#define _features_h_INCLUDED

#if defined(_POSIX_C_SOURCE) || defined(__APPLE__)
#define GIMSATUL_HAS_COMPRESSION
#endif

#if defined(_POSIX_C_SOURCE)
#define GIMSATUL_HAS_POSIX_MEMALIGN
// Could not get 'posix_memalign' working for '__APPLE__',
// i.e., tests fail with 'object ... not allocated'.
#endif

#endif
