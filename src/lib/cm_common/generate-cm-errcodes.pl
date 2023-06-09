#!/usr/bin/perl
#
# Generate the cm_errcodes.h header from cm_errcodes.txt
# Copyright (c) 2000-2012, PostgreSQL Global Development Group

use warnings;
use strict;

print
  "/* autogenerated from src/backend/utils/cm_errcodes.txt, do not edit */\n";
print "/* there is deliberately not an #ifndef ERRCODES_H here */\n";

open my $cm_errcodes, $ARGV[0] or die;

while (<$cm_errcodes>)
{
	chomp;

	# Skip comments
	next if /^#/;
	next if /^\s*$/;

	# Emit a comment for each section header
	if (/^Section:(.*)/)
	{
		my $header = $1;
		$header =~ s/^\s+//;
		print "\n/* $header */\n";
		next;
	}

	die "unable to parse cm_errcodes.txt"
	  unless /^([^\s]{5})\s+[EWS]\s+([^\s]+)/;

	(my $sqlstate, my $errcode_macro) = ($1, $2);

	# Split the sqlstate letters
	$sqlstate = join ",", split "", $sqlstate;

	# And quote them
	$sqlstate =~ s/([^,])/'$1'/g;

	print "#define $errcode_macro MAKE_SQLSTATE($sqlstate)\n";
}

close $cm_errcodes;
