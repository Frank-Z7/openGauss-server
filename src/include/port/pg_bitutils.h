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

/*
 * Rotate the bits of "word" to the right by n bits.
 */
static inline uint32 pg_rotate_right32(uint32 word, int n)
{
    return (word >> n) | (word << (sizeof(word) * BITS_PER_BYTE - n));
}

#endif							/* PG_BITUTILS_H */
