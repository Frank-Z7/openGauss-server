/* -------------------------------------------------------------------------
 *
 * createas.h
 *	  prototypes for createas.c.
 *
 *
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 * src/include/commands/createas.h
 *
 * -------------------------------------------------------------------------
 */
#ifndef CREATEAS_H
#define CREATEAS_H

#include "catalog/objectaddress.h"
#include "nodes/params.h"
#include "nodes/parsenodes.h"
#include "tcop/dest.h"

extern ObjectAddress ExecCreateTableAs(
    CreateTableAsStmt* stmt, const char* queryString, ParamListInfo params, char* completionTag);

extern int GetIntoRelEFlags(IntoClause* intoClause);

extern DestReceiver* CreateIntoRelDestReceiver(IntoClause* intoClause);

extern Query *SetupForCreateTableAs(Query *query, IntoClause *into,
                                    const char *queryString,
                                    ParamListInfo params, DestReceiver *dest);

#endif /* CREATEAS_H */
