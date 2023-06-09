/* -------------------------------------------------------------------------
 *
 * timestamp.h
 *	  Timestamp and Interval typedefs and related macros.
 *
 * Note: this file must be includable in both frontend and backend contexts.
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/include/datatype/timestamp.h
 *
 * -------------------------------------------------------------------------
 */
#ifndef DATATYPE_TIMESTAMP_H
#define DATATYPE_TIMESTAMP_H

#include <math.h>
#include <limits.h>
#include <float.h>

/*
 * Timestamp represents absolute time.
 *
 * Interval represents delta time. Keep track of months (and years), days,
 * and hours/minutes/seconds separately since the elapsed time spanned is
 * unknown until instantiated relative to an absolute time.
 *
 * Note that openGauss uses "time interval" to mean a bounded interval,
 * consisting of a beginning and ending time, not a time span - thomas 97/03/20
 *
 * We have two implementations, one that uses int64 values with units of
 * microseconds, and one that uses double values with units of seconds.
 *
 * TimeOffset and fsec_t are convenience typedefs for temporary variables
 * that are of different types in the two cases.  Do not use fsec_t in values
 * stored on-disk, since it is not the same size in both implementations.
 * Also, fsec_t is only meant for *fractional* seconds; beware of overflow
 * if the value you need to store could be many seconds.
 */

#ifdef HAVE_INT64_TIMESTAMP

typedef int64 Timestamp;
typedef int64 TimestampTz;
typedef int64 TimeOffset;
typedef int32 fsec_t; /* fractional seconds (in microseconds) */
#else

typedef double Timestamp;
typedef double TimestampTz;
typedef double TimeOffset;
typedef double fsec_t; /* fractional seconds (in seconds) */
#endif

typedef struct {
    TimeOffset time; /* all time units other than days, months and
                      * years */
    int32 day;       /* days, after time for alignment */
    int32 month;     /* months and years, after time for alignment */
} Interval;

/*
 * Convert an Interval to an approximate equivalent number of usec
 */
#define INTERVAL_TO_USEC(ivp) \
	((ivp->month * DAYS_PER_MONTH * USECS_PER_DAY) + (ivp->day * USECS_PER_DAY) + ivp->time)

#define MAX_TIMESTAMP_PRECISION 6
#define MAX_INTERVAL_PRECISION 6

/*
 *	Round off to MAX_TIMESTAMP_PRECISION decimal places.
 *	Note: this is also used for rounding off intervals.
 */
#define TS_PREC_INV 1000000.0
#define TSROUND(j) (rint(((double)(j)) * TS_PREC_INV) / TS_PREC_INV)

/*
 * Assorted constants for datetime-related calculations
 */

#define DAYS_PER_YEAR 365.25 /* assumes leap year every four years */
#define DAYS_PER_NYEAR 365
#define MONTHS_PER_YEAR 12
/*
 *	DAYS_PER_MONTH is very imprecise.  The more accurate value is
 *	365.2425/12 = 30.436875, or '30 days 10:29:06'.  Right now we only
 *	return an integral number of days, but someday perhaps we should
 *	also return a 'time' value to be used as well.	ISO 8601 suggests
 *	30 days.
 */
#define DAYS_PER_MONTH 30 /* assumes exactly 30 days per month */
#define HOURS_PER_DAY 24  /* assume no daylight savings time changes */

/*
 *	This doesn't adjust for uneven daylight savings time intervals or leap
 *	seconds, and it crudely estimates leap years.  A more accurate value
 *	for days per years is 365.2422.
 */
#define SECS_PER_YEAR (36525 * 864) /* avoid floating-point computation */
#define SECS_PER_DAY 86400
#define SECS_PER_HOUR 3600
#define SECS_PER_MINUTE 60
#define MINS_PER_HOUR 60
#define MINS_PER_DAY (HOURS_PER_DAY * MINS_PER_HOUR)

#define USECS_PER_DAY INT64CONST(86400000000)
#define USECS_PER_HOUR INT64CONST(3600000000)
#define USECS_PER_MINUTE INT64CONST(60000000)
#define USECS_PER_SEC INT64CONST(1000000)

#define USECS_PER_MSEC 1000
#define MSECS_PER_SEC 1000
#define MSECS_PER_MIN (SECS_PER_MINUTE * MSECS_PER_SEC)

/*
 * We allow numeric timezone offsets up to 15:59:59 either way from Greenwich.
 * Currently, the record holders for wackiest offsets in actual use are zones
 * Asia/Manila, at -15:56:00 until 1844, and America/Metlakatla, at +15:13:42
 * until 1867.	If we were to reject such values we would fail to dump and
 * restore old timestamptz values with these zone settings.
 */
#define MAX_TZDISP_HOUR 15 /* maximum allowed hour part */
#define TZDISP_LIMIT ((MAX_TZDISP_HOUR + 1) * SECS_PER_HOUR)

/*
 * DT_NOBEGIN represents timestamp -infinity; DT_NOEND represents +infinity
 */
#ifdef HAVE_INT64_TIMESTAMP
#define DT_NOBEGIN (-INT64CONST(0x7fffffffffffffff) - 1)
#define DT_NOEND (INT64CONST(0x7fffffffffffffff))
#else /* !HAVE_INT64_TIMESTAMP */
#ifdef HUGE_VAL
#define DT_NOBEGIN (-HUGE_VAL)
#define DT_NOEND (HUGE_VAL)
#else
#define DT_NOBEGIN (-DBL_MAX)
#define DT_NOEND (DBL_MAX)
#endif
#endif /* HAVE_INT64_TIMESTAMP */

#define TIMESTAMP_NOBEGIN(j) \
    do {                     \
        (j) = DT_NOBEGIN;    \
    } while (0)

#define TIMESTAMP_IS_NOBEGIN(j) ((j) == DT_NOBEGIN)

#define TIMESTAMP_NOEND(j) \
    do {                   \
        (j) = DT_NOEND;    \
    } while (0)

#define TIMESTAMP_IS_NOEND(j) ((j) == DT_NOEND)

#define TIMESTAMP_NOT_FINITE(j) (TIMESTAMP_IS_NOBEGIN(j) || TIMESTAMP_IS_NOEND(j))

/* Timestamp limits */
#define MIN_TIMESTAMP	INT64CONST(-211813488000000000)
#define END_TIMESTAMP	INT64CONST(9223371331200000000)

/* First allowed date, and first disallowed date, in Julian-date form */
#define DATETIME_MIN_JULIAN (0)
#define DATE_END_JULIAN (2147483494)	/* == date2j(JULIAN_MAXYEAR, 1, 1) */
#define TIMESTAMP_END_JULIAN (109203528)	/* == date2j(294277, 1, 1) */

/* Range-check a timestamp */
#define IS_VALID_TIMESTAMP(t)  (MIN_TIMESTAMP <= (t) && (t) < END_TIMESTAMP)

/*
 * Julian date support.
 *
 * IS_VALID_JULIAN checks the minimum date exactly, but is a bit sloppy
 * about the maximum, since it's far enough out to not be especially
 * interesting.
 */

#define JULIAN_MINYEAR (-4713)
#define JULIAN_MINMONTH (11)
#define JULIAN_MINDAY (24)
#define JULIAN_MAXYEAR (5874898)

#define IS_VALID_JULIAN(y, m, d)                                                                                    \
    (((y) > JULIAN_MINYEAR ||                                                                                       \
         ((y) == JULIAN_MINYEAR && ((m) > JULIAN_MINMONTH || ((m) == JULIAN_MINMONTH && (d) >= JULIAN_MINDAY)))) && \
        (y) < JULIAN_MAXYEAR)

#define JULIAN_MAX (2147483494) /* == date2j(JULIAN_MAXYEAR, 1, 1) */

/* Julian-date equivalents of Day 0 in Unix and openGauss reckoning */
#define UNIX_EPOCH_JDATE 2440588     /* == date2j(1970, 1, 1) */
#define POSTGRES_EPOCH_JDATE 2451545 /* == date2j(2000, 1, 1) */

#define MAX_VALUE_12_CLOCK (HOURS_PER_DAY / 2)
#define MIN_VALUE_12_CLOCK 1

#define MAX_VALUE_24_CLOCK (HOURS_PER_DAY)
#define MIN_VALUE_24_CLOCK 0

#define MAX_VALUE_MI (MINS_PER_HOUR)
#define MIN_VALUE_MI 0

#define MAX_VALUE_SS (SECS_PER_MINUTE)
#define MIN_VALUE_SS 0

#define MAX_VALUE_SSSSS 86400
#define MIN_VALUE_SSSSS 0

#define MAX_VALUE_D 7
#define MIN_VALUE_D 1

#define MAX_VALUE_DD 31
#define MIN_VALUE_DD 1

#define MAX_VALUE_DDD 366
#define MIN_VALUE_DDD 1

#define MAX_VALUE_MM 12
#define MIN_VALUE_MM 1

#define MAX_VALUE_MS 999
#define MIN_VALUE_MS 0

#define MIN_VALUE_YEAR -4712
#define MAX_VALUE_YEAR 9999

#define MAX_VALUE_WW 53
#define MIN_VALUE_WW 1

#define MAX_VALUE_W 5
#define MIN_VALUE_W 1

/* to meet MAX_VALUE_YEAR */
#define MAX_VALUE_J 5373484
#define MIN_VALUE_J 1

#define MAX_VALUE_US 999999
#define MIN_VALUE_US 0

#define MIN_VALUE_RR 0
#define MID_VALUE_RR 49
#define MAX_VALUE_RR 99

#endif /* DATATYPE_TIMESTAMP_H */
