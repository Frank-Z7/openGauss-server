/*-------------------------------------------------------------------------
 *
 * pg_bitutils.h
 *	  Miscellaneous functions for bit-wise operations.
 *
 *
 * Copyright (c) 2019-2021, PostgreSQL Global Development Group
 *
 * src/include/port/pg_bitutils.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef PG_BITUTILS_H
#define PG_BITUTILS_H

#ifndef FRONTEND
extern PGDLLIMPORT const uint8 pg_leftmost_one_pos[256];
extern PGDLLIMPORT const uint8 pg_rightmost_one_pos[256];
extern PGDLLIMPORT const uint8 pg_number_of_ones[256];
#else
extern const uint8 pg_leftmost_one_pos[256];
extern const uint8 pg_rightmost_one_pos[256];
extern const uint8 pg_number_of_ones[256];
#endif

#endif							/* PG_BITUTILS_H */
