/*-------------------------------------------------------------------------
 *
 *
 *
 *
 * IDENTIFICATION
 *	  src/include/parser/query_split.h
 *
 *-------------------------------------------------------------------------
 */
#ifndef QUERY_SPLIT_H
#define QUERY_SPLIT_H

#include "postgres.h"

#include <fcntl.h>
#include <limits.h>
#include <signal.h>
#include <unistd.h>
#include <sys/socket.h>
#ifdef HAVE_SYS_SELECT_H
#include <sys/select.h>
#endif
#ifdef HAVE_SYS_RESOURCE_H
#include <sys/time.h>
#include <sys/resource.h>
#endif
#ifndef HAVE_GETRUSAGE
#include "rusagestub.h"
#endif
#include "access/parallel.h"
#include "access/printtup.h"
#include "access/table.h"
#include "access/xact.h"
#include "catalog/pg_type.h"
#include "catalog/namespace.h"
#include "commands/async.h"
#include "commands/createas.h"
#include "commands/matview.h"
#include "commands/prepare.h"
#include "executor/spi.h"
#include "jit/jit.h"
#include "libpq/libpq.h"
#include "libpq/pqformat.h"
#include "libpq/pqsignal.h"
#include "miscadmin.h"
#include "nodes/parsenodes.h"
#include "nodes/pathnodes.h"
#include "nodes/pg_list.h"
#include "nodes/print.h"
#include "nodes/makefuncs.h"
#include "optimizer/optimizer.h"
#include "pgstat.h"
#include "pg_trace.h"
#include "parser/analyze.h"
#include "parser/parser.h"
#include "pg_getopt.h"
#include "postmaster/autovacuum.h"
#include "postmaster/postmaster.h"
#include "replication/logicallauncher.h"
#include "replication/logicalworker.h"
#include "replication/slot.h"
#include "replication/walsender.h"
#include "rewrite/rewriteHandler.h"
#include "storage/bufmgr.h"
#include "storage/ipc.h"
#include "storage/proc.h"
#include "storage/procsignal.h"
#include "storage/sinval.h"
#include "tcop/fastpath.h"
#include "tcop/pquery.h"
#include "tcop/tcopprot.h"
#include "tcop/utility.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/ps_status.h"
#include "utils/rel.h"
#include "utils/snapmgr.h"
#include "utils/timeout.h"
#include "utils/timestamp.h"
#include "mb/pg_wchar.h"

void doQSparse(const char* query_string, const char* commandTag, Node* pstmt, Query* querytree, char* completionTag);

#endif
