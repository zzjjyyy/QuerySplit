/*-------------------------------------------------------------------------
 *
 *
 *
 *
 * IDENTIFICATION
 *	  src/backend/parser/query_split.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"
#include "utils/datum.h"
#include "parser/query_split.h"
#include "fe_utils/simple_list.h"
#include "commands/event_trigger.h"
#include "commands/portalcmds.h"
#include "utils/relmapper.h"
#include "commands/vacuum.h"
#include "utils/rel.h"
#include "storage/buf_internals.h"
#include "utils/builtins.h"
#include "portability/instr_time.h"
#include "time.h"

#define NEWBETTER 1
#define OLDBETTER 2

//double total_size = 0.0;
//long long optimize_time = 0;
//long long execution_time = 0;
//long long materialization_time = 0;

#define half_rounded(x) (((x) + ((x) < 0 ? 0 : 1)) / 2)

List* rel2relids = NIL;

Datum pg_relation_size(PG_FUNCTION_ARGS);

static double getMatSize(Oid relid);
//Create a local query
static Query* createQuery(const Query* global_query, int endLoop, List* rtable, Index* transfer_array, int length);
//change the RangeTblEntry relid to the new one
static void dochange(RangeTblEntry* rte, char* relname, Relation relation, Oid relid);
//change the NullTest clause args to the new one
static bool doNullTestTransfor(NullTest* expr, Index* transfer_array);
//change the OpExpr clause args to the new one
static bool doOpExprTransfor(OpExpr* expr, Index* transfer_array);
//change the ScalarArrayOpExpr clause args to the new one
static bool doScalarArrayOpExprTransfor(ScalarArrayOpExpr* expr, Index* transfer_array);
//Get the var will link to unlocal table
static List* findvarlist(List* joinlist, Index* transfer_array, int length);
//from postgres.c
extern void finish_xact_command();
//Get local rtable
static List* getRT_1(List* global_rtable, bool* graph, int length, int i, int j, Index* transfer_array);
static List* getRT_2(List* global_rtable, bool* graph, int length, int i, Index* transfer_array);
//Get local rtables' foreign keys
static List* grFK(List* rtable);
//is this subquery is the last ?
static int hasNext(bool* graph, int length);
// Is this expr refer to two relationship table ?
static bool is_2relationship(OpExpr * opexpr, bool* is_relationship, int length);
//Is this a Entity-to-Relationship Join ?
static bool is_ER(OpExpr* opexpr, bool* is_relationship, int length);
//Is a foreign key join ?
static bool is_FK(OpExpr* opexpr, List* fklist);
//Is a restrict clause ?
static bool is_RC(Expr* expr);
//Transefer jointree to graph
static bool* List2Graph(bool* is_relationship, List* joinlist, List* FKlist, int length);
//Make a aggregation function as result
static List* removeAggref(List* targetList);
//give the new value to some var, prepare for the next subquery
static List* Prepare4Next(Query* global_query, Index* transfer_array, DR_intorel* receiver, PlannedStmt* plannedstmt,char* relname, List* FKlist);
static void Recon(char* query_string, char* commandTag, Query* ori_query, char* completionTag, CommandDest whereDest, char* rel_name);
//remove redundant join
static void rRj(Query* querytree);
//Transfer fromlist to the local
static List* setfromlist(List* fromlist, Index* transfer_array, int length);
//Transfer global var to local
static List* setjoinlist(List* rclist,Index* transfer_array, int length);
//Make a local target list
static List* settargetlist(const List* global_rtable, List* local_rtable, int endLoop, List* varlist, List* targetlist, Index* transfer_array, int length);
//Remove used jointree
static List* simplifyjoinlist(List* list, Index* transfer_array, bool* graph, int length);
//Split Query by Foreign Key
static List* spq(char* query_string, char* commandTag, Query* querytree, char* completionTag);
//from postgres.c
extern void start_xact_command();
static int tarfunc(Index* rels, PlannedStmt* new, PlannedStmt* old);
//Execute the local query
static List* QSExecutor(char* query_string, const char* commandTag, PlannedStmt* plannedstmt, CommandDest dest, char* relname, char* completionTag, Query* querytree, Index* transfer_array, List* FKlist, int endLoop);
//find the subquery with lowest cost to be executed
static PlannedStmt* QSOptimizer(Query* global_query, bool* graph, Index* transfer_array, int length, int* endLoop);
static Plan* find_node_with_nleaf_recursive(Plan* plan, int nleaf, int* leaf_has, int* depth);
static void walk_plantree(Plan* plan, Index* rel);

bool* is_relationship;
//the number of subquery
static int queryId = 0;
//where to send the result, to the client end or temporary table
Index* transfer_array = NULL;

//The interface
void doQSparse(const char* query_string, const char* commandTag, Query* querytree, char* completionTag, CommandDest whereDest)
{
	start_xact_command();
	//srand((unsigned) time(NULL));
	List* FKlist = NIL;
	if (querytree->commandType != CMD_UTILITY && query_splitting_algorithm != Minsubquery)
	{
		MemoryContext oldcontext = MemoryContextSwitchTo(MessageContext);
		//remove Redundant Join
		rRj(querytree);
		MemoryContextSwitchTo(oldcontext);
	}
	PlannedStmt* plannedstmt = NULL;
	if (querytree->commandType == CMD_UTILITY)
	{
		MemoryContext oldcontext = MemoryContextSwitchTo(MessageContext);
		/* Utility commands require no planning. */
		plannedstmt = makeNode(PlannedStmt);
		plannedstmt->commandType = CMD_UTILITY;
		plannedstmt->canSetTag = querytree->canSetTag;
		plannedstmt->utilityStmt = querytree->utilityStmt;
		plannedstmt->stmt_location = querytree->stmt_location;
		plannedstmt->stmt_len = querytree->stmt_len;
		oldcontext = MemoryContextSwitchTo(MessageContext);
		char* rel_name = palloc(10 * sizeof(char));
		sprintf(rel_name, "temp%d", queryId++);
		MemoryContextSwitchTo(oldcontext);
		QSExecutor(query_string, commandTag, plannedstmt, DestRemote, rel_name, completionTag, querytree, NULL, NIL, 1);
		finish_xact_command();
		return;
	}
	ListCell* lc;
	int length = 0;
	foreach(lc, querytree->rtable)
	{
		RangeTblEntry* rte = (RangeTblEntry*)lfirst(lc);
		if (rte->rtekind == RTE_SUBQUERY)
		{
			if (rte->subquery->rtable->length > 1 || rte->subquery->jointree->quals)
			{
				doQSparse(query_string, commandTag, rte->subquery, completionTag, DestIntoRel);
				if (rte->subquery->setOperations)
				{
					rte->subquery->setOperations = NULL;
					if (rte->subquery->jointree->fromlist == NULL)
					{
						RangeTblRef* ref = makeNode(RangeTblRef);
						ref->rtindex = 1;
						rte->subquery->jointree->fromlist = lappend(rte->subquery->jointree->fromlist, ref);
					}
				}
				if (rte->subquery->distinctClause)
				{
					rte->subquery->distinctClause = NIL;
				}
			}
			// If current query is not a set operation. pull up the subquery
			if (querytree->setOperations == NULL)
			{
				if (rte->subquery->rtable->length == 1)
				{
					RangeTblEntry* child_rte = lfirst(list_head(rte->subquery->rtable));
					if (child_rte->relid > 0)
					{
						rte->requiredPerms = 0;
						rte->rtekind = RTE_RELATION;
						rte->relkind = RELKIND_RELATION;
						rte->subquery = NULL;
						rte->relid = child_rte->relid;
						rte->rellockmode = AccessShareLock;
					}
					
				}
			}
		}
		else if (rte->rtekind == RTE_RELATION)
		{
			length++;
		}
		else
		{
			MemoryContext oldcontext = MemoryContextSwitchTo(MessageContext);
			char* rel_name = palloc(10 * sizeof(char));
			sprintf(rel_name, "temp%d", queryId++);
			MemoryContextSwitchTo(oldcontext);
			plannedstmt = planner(querytree, CURSOR_OPT_PARALLEL_OK, NULL);
			QSExecutor(query_string, commandTag, plannedstmt, whereDest, rel_name, completionTag, querytree, NULL, NIL, 1);
			finish_xact_command();
			return;
		}
	}
	//total_size = 0.0;
	//optimize_time = 0;
	//execution_time = 0;
	//materialization_time = 0;
	//split parent query by foreign key
	MemoryContext oldcontext = MemoryContextSwitchTo(MessageContext);
	char* rel_name = palloc(10 * sizeof(char));
	sprintf(rel_name, "temp%d", queryId++);
	MemoryContextSwitchTo(oldcontext);
	Recon(query_string, commandTag, querytree, completionTag, whereDest, rel_name);
	return;
}

//remove Redundant Join
static void rRj(Query* querytree)
{
	//get all the foreign key
	List* FKlist = grFK(querytree->rtable);
	int length = querytree->rtable->length;
	is_relationship = (bool*)palloc(length * sizeof(bool));
	memset(is_relationship, true, length * sizeof(bool));
	ListCell* lc;
	//referenced relation is entity
	foreach(lc, FKlist)
	{
		ForeignKeyOptInfo* fkOptInfo = (ForeignKeyOptInfo*)lc->data.ptr_value;
		int x = fkOptInfo->ref_relid - 1;
		is_relationship[x] = false;
	}
	if (querytree->jointree->quals == NULL)
		return;
	//SQL where clause
	switch (querytree->jointree->quals->type)
	{
		case T_BoolExpr:
		{	
			BoolExpr* expr = (BoolExpr*)querytree->jointree->quals;
			if (expr == NULL)
				return;
			//expression list in the SQL where clause
			List* where = expr->args;
			//remove the redundant expression in expression list
			foreach(lc, where)
			{
				//is this expression a filter clause ?
				if (is_RC(lc->data.ptr_value))
				{
					continue;
				}
				//is this expression contian two relationship table ?
				if (is_2relationship(lc->data.ptr_value, is_relationship, length))
				{
					//if yes, remove it from expression list
					where = list_delete(where, lfirst(lc));
					continue;
				}
			}
			break;
		}
		case T_OpExpr:
			break;
	}
	return;
}

static void Recon(char* query_string, char* commandTag, Query* ori_query, char* completionTag, CommandDest whereDest, char* rel_name)
{
	start_xact_command();
	MemoryContext oldcontext = MemoryContextSwitchTo(MessageContext);
	Query* global_query = ori_query;
	//Query* global_query = copyObjectImpl(ori_query);
	//List* ori_rtable = copyObjectImpl(ori_query->rtable);
	PlannedStmt* plannedstmt = NULL;
	if (global_query->commandType == CMD_UTILITY)
	{
		MemoryContextSwitchTo(oldcontext);
		plannedstmt = QSOptimizer(global_query, NULL, NULL, 0, NULL);
		QSExecutor(query_string, commandTag, plannedstmt, whereDest, NULL, completionTag, NULL, NULL, NIL, 1);
		finish_xact_command();
		return;
	}
	int length = global_query->rtable->length;
	if (global_query->jointree->quals == NULL)
	{
		plannedstmt = planner(global_query, CURSOR_OPT_PARALLEL_OK, NULL);
		MemoryContext oldcontext = MemoryContextSwitchTo(MessageContext);
		transfer_array = (Index*)palloc(length * sizeof(Index));
		for (int j = 0; j < length; j++)
			transfer_array[j] = j + 1;
		MemoryContextSwitchTo(oldcontext);
		QSExecutor(query_string, commandTag, plannedstmt, whereDest, rel_name, completionTag, global_query, transfer_array, NIL, 1);
		finish_xact_command();
		return;
	}
	if (length == 1)
	{
		MemoryContext oldcontext = MemoryContextSwitchTo(MessageContext);
		transfer_array = (Index*)palloc(length * sizeof(Index));
		for (int j = 0; j < length; j++)
			transfer_array[j] = 0;
		int* endLoop = (int*)palloc(sizeof(int));
		MemoryContextSwitchTo(oldcontext);
		plannedstmt = QSOptimizer(global_query, NULL, transfer_array, length, endLoop);
		QSExecutor(query_string, commandTag, plannedstmt, whereDest, NULL, completionTag, global_query, transfer_array, NIL, 1);
		finish_xact_command();
		return;
	}
	List* RClist = NIL;
	List* Joinlist = NIL;
	List* WhereClause = NIL;
	switch (global_query->jointree->quals->type)
	{
		case T_BoolExpr:
		{
			BoolExpr* expr = (BoolExpr*)global_query->jointree->quals;
			WhereClause = expr->args;
			break;
		}
		case T_OpExpr:
		{
			WhereClause = lappend(WhereClause, global_query->jointree->quals);
			break;
		}
	}
	ListCell* lc;
	foreach(lc, WhereClause)
	{
		Node* node = lfirst(lc);
		switch (node->type)
		{
		//case T_SubLink:
		//	doQSparse(query_string, commandTag, ((SubLink*)node)->subselect, completionTag, DestIntoRel);
		//	break;
		default:
			if (is_RC(lc->data.ptr_value))
				RClist = lappend(RClist, lc->data.ptr_value);
			else
				Joinlist = lappend(Joinlist, lc->data.ptr_value);
		}
	}
	List* FKlist = grFK(global_query->rtable);
	//transfer join list to join graph
	bool* graph = List2Graph(is_relationship, Joinlist, FKlist, length);
	//value start from 1, index start from 0
	transfer_array = (Index*)palloc(length * sizeof(Index));
	/*
	int i = 1;
	foreach(lc, ori_rtable)
	{
		RangeTblEntry* rte = (RangeTblEntry*)lfirst(lc);
		My* my = (My*)palloc(sizeof(My));
		my->bms = bms_add_member(NULL, i);
		my->relname = (char*)palloc((strlen(rte->alias->aliasname) + 1) * sizeof(char));
		strcpy(my->relname, rte->alias->aliasname);
		rel2relids = lappend(rel2relids, my);
		i++;
	}
	*/
	int* endLoop = (int*) palloc(sizeof(int));
	MemoryContextSwitchTo(oldcontext);
	while (plannedstmt = QSOptimizer(global_query, graph, transfer_array, length, endLoop))
	{
		/*
		char* thename = ((RangeTblEntry*)lfirst(list_head(plannedstmt->rtable)))->alias->aliasname;
		foreach(lc, rel2relids)
		{
			My* my = (My*)lfirst(lc);
			if (strcmp(my->relname, thename) == 0)
			{
				ListCell* lc1;
				Bitmapset* bms = my->bms;
				foreach(lc1, plannedstmt->rtable)
				{
					RangeTblEntry* rte1 = (RangeTblEntry*)lfirst(lc1);
					ListCell* lc2;
					foreach(lc2, rel2relids)
					{
						My* rte2 = (My*)lfirst(lc2);
						if (strcmp(rte1->alias->aliasname, rte2->relname) == 0)
						{
							oldcontext = MemoryContextSwitchTo(MessageContext);
							bms = bms_union(bms, rte2->bms);
							MemoryContextSwitchTo(oldcontext);
							break;
						}
					}
				}
				my->bms = bms;
				break;
			}	
		}
		*/
		char* relname = NULL;
		//Should we output the result or save it as a temporary table
		if ((*endLoop == 0) || whereDest == DestIntoRel)
		{
			oldcontext = MemoryContextSwitchTo(MessageContext);
			relname = palloc(7 * sizeof(char));
			sprintf(relname, "temp%d", queryId++);
			MemoryContextSwitchTo(oldcontext);
		}
		//Execute the subquery and do some change for next subquery creation
		//instr_time start_time, end_time;
		//INSTR_TIME_SET_CURRENT(start_time);
		if(*endLoop == 1)
			FKlist = QSExecutor(query_string, commandTag, plannedstmt, whereDest, relname, completionTag, global_query, transfer_array, FKlist, *endLoop);
		else
			FKlist = QSExecutor(query_string, commandTag, plannedstmt, DestIntoRel, relname, completionTag, global_query, transfer_array, FKlist, *endLoop);
		//INSTR_TIME_SET_CURRENT(end_time);
		//execution_time += end_time.QuadPart - start_time.QuadPart;
		finish_xact_command();
		if (*endLoop == 1)
		{
			//FILE* fp = fopen("D:\\Database\\Qsplit.txt", "a+");
			//fprintf(fp, "%d\t%lf\n", queryId - 1, total_size);
			//fprintf(fp, "\n");
			//fprintf(fp, "%lf\t%lf\t%lf\n", optimize_time / 10000000.0, materialization_time / 10000000.0, (execution_time - materialization_time) / 10000000.0);
			//fclose(fp);
			break;
		}
		switch (global_query->jointree->quals->type)
		{
			case T_BoolExpr:
			{
				BoolExpr* expr = (BoolExpr*)global_query->jointree->quals;
				WhereClause = expr->args;
				break;
			}
			case T_OpExpr:
			{
				WhereClause = lappend(WhereClause, global_query->jointree->quals);
				break;
			}
		}
		Joinlist = NIL;
		ListCell* lc;
		foreach(lc, WhereClause)
		{
			if (!is_RC(lc->data.ptr_value))
				Joinlist = lappend(Joinlist, lc->data.ptr_value);
		}
		length = global_query->rtable->length;
		graph = List2Graph(is_relationship, Joinlist, FKlist, length);
	}
	pfree(transfer_array);
	pfree(graph);
	transfer_array = NULL;
	graph = NULL;
	return;
}

//Planner
static PlannedStmt* QSOptimizer(Query* global_query, bool* graph, Index* transfer_array, int length, int* endLoop)
{
	//instr_time start_time, end_time;
	//INSTR_TIME_SET_CURRENT(start_time);
	start_xact_command();
	PlannedStmt* result = NULL;
	int remain = hasNext(graph, length);
	int X = 0, Y = 0;
	Index rels[2] = { 0, 0 };
	if(query_splitting_algorithm == RelationshipCenter || query_splitting_algorithm == EntityCenter)
	{
		if (order_decision == global_view)
		{
			PlannedStmt* temp = planner(copyObjectImpl(global_query), CURSOR_OPT_PARALLEL_OK, NULL);
			int leaf_has = 0, depth = 0;
			Plan* temp_plan = find_node_with_nleaf_recursive(temp->planTree, 2, &leaf_has, &depth);
			walk_plantree(temp_plan, rels);
			rels[0] = ((RangeTblEntry*)list_nth(global_query->rtable, rels[0] - 1))->relid;
			rels[1] = ((RangeTblEntry*)list_nth(global_query->rtable, rels[1] - 1))->relid;
		}
		for (int i = 0; i < length; i++)
		{
			if (remain > 1)
				*endLoop = 0;
			else if (remain == 1)
				*endLoop = 1;
			else if (remain == 0)
				return NULL;
			for (int j = 0; j < length; j++)
				transfer_array[j] = 0;
			//Get the rang table list for this subgraph
			List* rtable = getRT_2(global_query->rtable, graph, length, i, transfer_array);
			//Can this subgraph make a join ?
			if (rtable->length < 2)
			{
				if (length != 1)
				{
					continue;
				}
			}
			char* relname = NULL;
			//If so, create a subquery
			Query* local_query = createQuery(global_query, *endLoop, rtable, transfer_array, length);
			PlannedStmt* candidate_result = planner(local_query, CURSOR_OPT_PARALLEL_OK, NULL);
			if (tarfunc(rels, candidate_result, result) == NEWBETTER)
			{
				if(result)
					pfree(result);
				result = candidate_result;
				X = i;
			}
			else
			{
				pfree(candidate_result);
			}
			candidate_result = NULL;
		}
	}
	else if (query_splitting_algorithm == Minsubquery)
	{
		if (order_decision == global_view)
		{
			PlannedStmt* temp = planner(copyObjectImpl(global_query), CURSOR_OPT_PARALLEL_OK, NULL);
			int leaf_has = 0, depth = 0;
			Plan* temp_plan = find_node_with_nleaf_recursive(temp->planTree, 2, &leaf_has, &depth);
			walk_plantree(temp_plan, rels);
			rels[0] = ((RangeTblEntry*)list_nth(global_query->rtable, rels[0] - 1))->relid;
			rels[1] = ((RangeTblEntry*)list_nth(global_query->rtable, rels[1] - 1))->relid;
		}
		for (int i = 0; i < length; i++)
		{
			for (int j = i + 1; j < length; j++)
			{
				if (remain > 1)
					*endLoop = 0;
				else if (remain == 1)
					*endLoop = 1;
				else if (remain == 0)
					return NULL;
				for (int j = 0; j < length; j++)
					transfer_array[j] = 0;
				//Get the rang table list for this subgraph
				List* rtable = getRT_1(global_query->rtable, graph, length, i, j, transfer_array);
				//Can this subgraph make a join ?
				if (rtable == NIL)
				{
					continue;
				}
				char* relname = NULL;
				//If so, create a subquery
				Query* local_query = createQuery(global_query, *endLoop, rtable, transfer_array, length);
				PlannedStmt* candidate_result = planner(local_query, CURSOR_OPT_PARALLEL_OK, NULL);
				if (tarfunc(rels, candidate_result, result) == NEWBETTER)
				{
					if(result)
						pfree(result);
					result = candidate_result;
					X = i;
					Y = j;
				}
				else
				{
					pfree(candidate_result);
				}
				candidate_result = NULL;
			}
		}
	}
	for (int j = 0; j < length; j++)
		transfer_array[j] = 0;
	if (query_splitting_algorithm == RelationshipCenter || query_splitting_algorithm == EntityCenter)
	{
		Index index = 1;
		for (int j = 0; j < length; j++)
		{
			if (graph[X * length + j] == true)
			{
				transfer_array[j] = index++;
			}
			else if (X == j)
			{
				transfer_array[j] = index++;
			}
			else
			{
				transfer_array[j] = 0;
			}
		}
		for (int j = 0; j < length; j++)
		{
			if (graph[X * length + j] == true)
			{
				graph[X * length + j] = false;
				graph[j * length + X] = false;
			}
		}
	}
	else if (query_splitting_algorithm == Minsubquery)
	{	
		for (int j = 0; j < length; j++)
			transfer_array[j] = 0;
		transfer_array[X] = 1;
		transfer_array[Y] = 2;
		graph[X * length + Y] = false;
		for (int i = 0; i < length; i++)
		{
			if (i < X)
			{
				if (graph[i * length + X] == true && graph[i * length + Y] == true)
				{
					graph[i * length + X] = false;
				}
			}
			else if (i > X && i < Y)
			{
				if (graph[X * length + i] == true && graph[i * length + Y] == true)
				{
					graph[X * length + i] = false;
				}
			}
			else if (i > Y)
			{
				if (graph[X * length + i] == true && graph[Y * length + i] == true)
				{
					graph[X * length + i] = false;
				}
			}
		}
	}
	switch (global_query->jointree->quals->type)
	{
		case T_BoolExpr:
		{
			((BoolExpr*)global_query->jointree->quals)->args = simplifyjoinlist(((BoolExpr*)global_query->jointree->quals)->args, transfer_array, graph, length);
			break;
		}
		case T_OpExpr:
		{
			global_query->jointree->quals = NULL;
			break;
		}
	}
	//INSTR_TIME_SET_CURRENT(end_time);
	//optimize_time += end_time.QuadPart - start_time.QuadPart;
	return result;
}

//Executor
static List* QSExecutor(char* query_string, const char* commandTag, PlannedStmt* plannedstmt, CommandDest dest, char* relname, char* completionTag, Query* querytree, Index* transfer_array, List* FKlist, int endLoop)
{
	int16 format;
	Portal portal;
	List* plantree_list;
	DestReceiver* receiver = NULL;
	bool is_parallel_worker = false;
	BeginCommand(commandTag, dest);
	plantree_list = lappend(NIL, plannedstmt);
	CHECK_FOR_INTERRUPTS();
	portal = CreatePortal("", true, true);
	portal->visible = false;
	PortalDefineQuery(portal, NULL, query_string, commandTag, plantree_list, NULL);
	PortalStart(portal, NULL, 0, InvalidSnapshot);
	format = 0;
	PortalSetResultFormat(portal, 1, &format);
	if (dest == DestRemote)
	{
		receiver = CreateDestReceiver(dest);
		SetRemoteDestReceiverParams(receiver, portal);
	}
	if (dest == DestIntoRel)
	{
		IntoClause* into = makeNode(IntoClause);
		into->rel = makeRangeVar(NULL, relname, plannedstmt->stmt_location);
		into->rel->relpersistence = RELPERSISTENCE_TEMP;
		into->onCommit = ONCOMMIT_NOOP;
		into->rel->inh = false;
		into->skipData = false;
		into->viewQuery = NULL;
		receiver = CreateIntoRelDestReceiver(into);
	}
	//Executor
	(void)PortalRun(portal, FETCH_ALL, true, true, receiver, receiver, completionTag);
	if (dest == DestIntoRel)
	{
		VacuumParams params;
		params.index_cleanup = VACOPT_TERNARY_DEFAULT;
		params.truncate = VACOPT_TERNARY_DEFAULT;
		params.options = VACOPT_ANALYZE;
		params.freeze_min_age = -1;
		params.freeze_table_age = -1;
		params.multixact_freeze_min_age = -1;
		params.multixact_freeze_table_age = -1;
		params.is_wraparound = false;
		params.log_min_duration = -1;
		Oid relid = RangeVarGetRelid(((DR_intorel*)receiver)->into->rel, NoLock, true);
		//analyze_rel(relid, ((DR_intorel*)receiver)->into->rel, &params, NIL, false, NULL);
		MemoryContext context = MemoryContextSwitchTo(MessageContext);
		FKlist = Prepare4Next(querytree, transfer_array, (DR_intorel*)receiver, plannedstmt, relname, FKlist);
		//double s = getMatSize(relid);
		//total_size += s;
		MemoryContextSwitchTo(context);
	}
	//if (portal->queryDesc != NULL)
	//	writeFile("D://Database//Qsplit.txt", portal->queryDesc);
	receiver->rDestroy(receiver);
	PortalDrop(portal, false);
	EndCommand(completionTag, dest);
	return FKlist;
}

static RangeTblEntry* fetchRteRelation(RangeTblEntry* rte)
{
	RangeTblEntry* res = rte;
	if (rte->rtekind == RTE_SUBQUERY)
	{
		res = fetchRteRelation(lfirst(list_head(rte->subquery->rtable)));
	}
	else if (rte->rtekind == RTE_RELATION)
	{
		res = rte;
	}
	return res;
}

static List* Prepare4Next(Query* global_query, Index* transfer_array, DR_intorel* receiver, PlannedStmt* plannedstmt, char* relname, List* FKlist)
{
	int length = global_query->rtable->length;
	int X = -1;
	int before = 0;
	for (int i = 0; i < length; i++)
	{
		if (X == -1 && transfer_array[i] == 0)
		{
			continue;
		}
		else if (X == -1 && transfer_array[i] != 0)
		{
			X = i;
			before = 0;
			if (query_splitting_algorithm == RelationshipCenter)
				is_relationship[i - before] = false;
			else if (query_splitting_algorithm == EntityCenter)
				is_relationship[i - before] = true;
		}
		else if (transfer_array[i] != 0)
		{
			before++;
		}
		else if (transfer_array[i] == 0)
		{
			if (query_splitting_algorithm == RelationshipCenter || query_splitting_algorithm == EntityCenter)
				is_relationship[i - before] = is_relationship[i];
		}
	}
	ListCell* lc;
	ListCell* prev = NULL;
	foreach(lc, FKlist)
	{
		bool flag = false;
		ForeignKeyOptInfo* fkOptInfo = (ForeignKeyOptInfo*)lfirst(lc);
		int x = fkOptInfo->con_relid - 1;
		int y = fkOptInfo->ref_relid - 1;
		if (transfer_array[x] != 0 && transfer_array[y] != 0)
		{
			FKlist = list_delete_cell(FKlist, lc, prev);
		}
		else if (transfer_array[x] != 0)
		{
			fkOptInfo->con_relid = X + 1;
			prev = lc;
		}
		else if (transfer_array[y] != 0)
		{
			fkOptInfo->ref_relid = X + 1;
			prev = lc;
		}
		else
		{
			prev = lc;
		}
	}
	Oid relid = RangeVarGetRelid(receiver->into->rel, NoLock, true);
	Relation relation = table_open(relid, NoLock);
	List* varlist = pull_var_clause((Node*)global_query->jointree, 0);
	foreach(lc, varlist)
	{
		Var* var = (Var*)lfirst(lc);
		if (transfer_array[var->varnoold - 1] != 0)
		{
			RangeTblEntry* rte = (RangeTblEntry*)list_nth(global_query->rtable, var->varnoold - 1);
			int len = strlen(rte->eref->aliasname) + strlen(strVal(list_nth(rte->eref->colnames, var->varoattno - 1))) + 2;
			char* attrname = (char*)palloc(len * sizeof(char));
			sprintf(attrname, "%s_%s", rte->eref->aliasname, strVal(list_nth(rte->eref->colnames, var->varoattno - 1)));
			var->varno = X + 1;
			var->varnoold = var->varno;
			for (int i = 0; i < relation->rd_att->natts; i++)
			{
				if (strcmp(attrname, relation->rd_att->attrs[i].attname.data) == 0)
				{
					var->varattno = i + 1;
					var->varoattno = var->varattno;
					break;
				}
			}
			pfree(attrname);
			attrname = NULL;
		}
		else
		{
			int before = 0;
			for (int i = X + 1; i < var->varno - 1; i++)
			{
				if (transfer_array[i] != 0)
				{
					before++;
				}
			}
			var->varno -= before;
			var->varnoold = var->varno;
		}
	}
	foreach(lc, FKlist)
	{
		ForeignKeyOptInfo* fkOptInfo = (ForeignKeyOptInfo*)lfirst(lc);
		int before = 0;
		for (int i = X + 1; i < fkOptInfo->con_relid - 1; i++)
		{
			if (transfer_array[i] != 0)
			{
				before++;
			}
		}
		fkOptInfo->con_relid -= before;
		before = 0;
		for (int i = X + 1; i < fkOptInfo->ref_relid - 1; i++)
		{
			if (transfer_array[i] != 0)
			{
				before++;
			}
		}
		fkOptInfo->ref_relid -= before;
	}
	//子查询涉及的全局relation
	for (int i = length - 1; i > X; i--)
	{
		if (transfer_array[i] != 0)
		{
			RangeTblEntry* rte = list_nth(global_query->rtable, i);
			global_query->rtable = list_delete(global_query->rtable, list_nth(global_query->rtable, i));
			if(global_query->jointree->fromlist)
				global_query->jointree->fromlist = list_delete(global_query->jointree->fromlist, list_nth(global_query->jointree->fromlist, i));
		}
	}
	RangeTblEntry* rte = (RangeTblEntry*)list_nth(global_query->rtable, X);
	dochange(rte, relname, relation, relid);
	//RangeTblEntry* rte2 = fetchRteRelation(rte);
	//if(rte != rte2)
	//	dochange(rte2, NULL, relation, relid);
	Index index = 1;
	foreach(lc, global_query->jointree->fromlist)
	{
		RangeTblRef* rtr = (RangeTblRef*)lfirst(lc);
		rtr->rtindex = index++;
	}
	foreach(lc, global_query->targetList)
	{
		TargetEntry* tar = (TargetEntry*)lfirst(lc);
		Var* vtar = NULL;
		if (tar->expr->type == T_Aggref)
		{
			TargetEntry* te = lfirst(((Aggref*)tar->expr)->args->head);
			if (te->expr->type == T_Var)
				vtar = (Var*)te->expr;
			else if (te->expr->type == T_RelabelType)
				vtar = (Var*)((RelabelType*)te->expr)->arg;
		}
		else if (tar->expr->type == T_RelabelType)
		{
			vtar = (Var*)((RelabelType*)tar->expr)->arg;
		}
		else if(tar->expr->type == T_Var)
		{
			vtar = (Var*)tar->expr;
		}
		if (vtar == NULL)
			continue;
		if (transfer_array[vtar->varnoold - 1] != 0)
		{
			tar->resorigtbl = relid;
			for (int i = 0; i < relation->rd_att->natts; i++)
			{
				if (strcmp(tar->resname, relation->rd_att->attrs[i].attname.data) == 0)
				{
					tar->resorigcol = i + 1;
					vtar->varattno = i + 1;
					vtar->varno = X + 1;
					vtar->varoattno = vtar->varattno;
					vtar->varnoold = vtar->varno;
					break;
				}
			}
		}
		else
		{
			int before = 0;
			for (int i = X + 1; i < vtar->varno; i++)
			{
				if (transfer_array[i] != 0)
				{
					before++;
				}
			}
			vtar->varno = vtar->varno - before;
			vtar->varnoold = vtar->varno;
		}
	}
	table_close(relation, NoLock);
	return FKlist;
}

//transfer joinlist to join graph
static bool* List2Graph(bool* is_relationship, List* joinlist, List* FKlist, int length)
{
	bool* graph = (bool*)palloc((uint64)length * length * sizeof(bool));
	memset(graph, false, (uint64)length * length * sizeof(bool));
	ListCell* lc1;
	if (query_splitting_algorithm == RelationshipCenter || query_splitting_algorithm == EntityCenter)
	{
		foreach(lc1, FKlist)
		{
			bool flag = false;
			ForeignKeyOptInfo* fkOptInfo = (ForeignKeyOptInfo*)lc1->data.ptr_value;
			int x = fkOptInfo->con_relid - 1;
			int y = fkOptInfo->ref_relid - 1;
			ListCell* lc2;
			foreach(lc2, joinlist)
			{
				Var* var1 = (Var*)lfirst(((OpExpr*)lfirst(lc2))->args->head);
				Var* var2 = (Var*)lfirst(((OpExpr*)lfirst(lc2))->args->head->next);
				if (var1->varno - 1 == x && var2->varno - 1 == y)
				{
					flag = true;
					joinlist = list_delete(joinlist, lfirst(lc2));
				}
				else if (var1->varno - 1 == y && var2->varno - 1 == x)
				{
					flag = true;
					joinlist = list_delete(joinlist, lfirst(lc2));
				}
			}
			if (!flag)
				continue;
			if (query_splitting_algorithm == RelationshipCenter)
			{
				graph[x * length + y] = true;
			}
			else if (query_splitting_algorithm == EntityCenter)
			{
				graph[y * length + x] = true;
			}
		}
	}
	foreach(lc1, joinlist)
	{
		Var* var1 = (Var*)lfirst(((OpExpr*)lfirst(lc1))->args->head);
		Var* var2 = (Var*)lfirst(((OpExpr*)lfirst(lc1))->args->head->next);
		if (query_splitting_algorithm == Minsubquery)
		{
			if (var1->varno > var2->varno)
			{
				graph[(var2->varno - 1) * length + var1->varno - 1] = true;
			}
			else if (var1->varno < var2->varno)
			{
				graph[(var1->varno - 1) * length + var2->varno - 1] = true;
			}
		}
		else if (query_splitting_algorithm == RelationshipCenter)
		{
			if ((is_relationship[var1->varno - 1] == true) && (is_relationship[var2->varno - 1] == false))
			{
				graph[(var1->varno - 1) * length + var2->varno - 1] = true;
			}
			else if ((is_relationship[var1->varno - 1] == false) && (is_relationship[var2->varno - 1] == true))
			{
				graph[(var2->varno - 1) * length + var1->varno - 1] = true;
			}
			else if ((is_relationship[var1->varno - 1] == false) && (is_relationship[var2->varno - 1] == false))
			{
				graph[(var1->varno - 1) * length + var2->varno - 1] = true;
				graph[(var2->varno - 1) * length + var1->varno - 1] = true;
			}
			else
			{
				graph[(var1->varno - 1) * length + var2->varno - 1] = true;
				graph[(var2->varno - 1) * length + var1->varno - 1] = true;
			}
		}
		else if(query_splitting_algorithm == EntityCenter)
		{
			if ((is_relationship[var1->varno - 1] == false) && (is_relationship[var2->varno - 1] == true))
			{
				graph[(var1->varno - 1) * length + var2->varno - 1] = true;
			}
			else if ((is_relationship[var1->varno - 1] == true) && (is_relationship[var2->varno - 1] == false))
			{
				graph[(var2->varno - 1) * length + var1->varno - 1] = true;
			}
			else if ((is_relationship[var1->varno - 1] == false) && (is_relationship[var2->varno - 1] == false))
			{
				graph[(var1->varno - 1) * length + var2->varno - 1] = true;
				graph[(var2->varno - 1) * length + var1->varno - 1] = true;
			}
			else
			{
				graph[(var1->varno - 1) * length + var2->varno - 1] = true;
				graph[(var2->varno - 1) * length + var1->varno - 1] = true;
			}
		}
	}
	return graph;
}

static bool is_ER(OpExpr* opexpr, bool* is_relationship, int length)
{
	Var* var1 = (Var*)lfirst(opexpr->args->head);
	Var* var2 = (Var*)lfirst(opexpr->args->head->next);
	if (is_relationship[var1->varno - 1] && is_relationship[var2->varno - 1])
		return false;
	else if (is_relationship[var1->varno - 1] || is_relationship[var2->varno - 1])
		return true;
	else
		return false;
}

static bool is_FK(OpExpr* opexpr, List* fklist)
{
	ListCell* lc = NULL;
	Var* var1 = (Var*)lfirst(opexpr->args->head);
	Var* var2 = (Var*)lfirst(opexpr->args->head->next);
	foreach(lc, fklist)
	{
		ForeignKeyOptInfo* fkOptInfo = (ForeignKeyOptInfo*)lfirst(lc);
		if (var1->varno == fkOptInfo->con_relid && var2->varno == fkOptInfo->ref_relid)
			return true;
		else if (var2->varno == fkOptInfo->con_relid && var1->varno == fkOptInfo->ref_relid)
			return true;
	}
	return false;
}

static bool is_2relationship(OpExpr* opexpr, bool* is_relationship, int length)
{
	Var* var1 = (Var*)lfirst(opexpr->args->head);
	Var* var2 = (Var*)lfirst(opexpr->args->head->next);
	if (is_relationship[var1->varno - 1] && is_relationship[var2->varno - 1])
		return true;
	return false;
}

//Expr is a filter clause?
static bool is_RC(Expr* expr)
{
	if (expr->type != T_OpExpr)
		return true;
	OpExpr* opexpr = (OpExpr*)expr;
	List* left_vars = pull_var_clause((Node*)lfirst(opexpr->args->head), 0);
	List* right_vars = pull_var_clause((Node*)lfirst(opexpr->args->head->next), 0);
	if (left_vars != NIL && right_vars != NIL)
		return false;
	return  true;
}

//get rtable
static List* getRT_1(List* prtable, bool* graph, int length, int i, int j, Index* transfer_array)
{
	if (graph[i * length + j] == true)
	{
		List* rtable = NIL;
		RangeTblEntry* rte_i = copyObjectImpl(list_nth(prtable, i));
		RangeTblEntry* rte_j = copyObjectImpl(list_nth(prtable, j));
		rtable = lappend(rtable, rte_i);
		rtable = lappend(rtable, rte_j);
		transfer_array[i] = 1;
		transfer_array[j] = 2;
		return rtable;
	}
	return NIL;
}

static List* getRT_2(List* prtable, bool* graph, int length, int i, Index* transfer_array)
{
	Index index = 1;
	List* rtable = NIL;
	if (graph == NULL)
	{
		for (int j = 0; j < length; j++)
		{
			RangeTblEntry* rte = copyObjectImpl(list_nth(prtable, j));
			rtable = lappend(rtable, rte);
			transfer_array[j] = index++;
		}
	}
	else
	{
		for (int j = 0; j < length; j++)
		{
			//graph[x][y]
			if (graph[i * length + j] == true)
			{
				RangeTblEntry* rte = copyObjectImpl(list_nth(prtable, j));
				rtable = lappend(rtable, rte);
				transfer_array[j] = index++;
			}
			else if (i == j)
			{
				RangeTblEntry* rte = copyObjectImpl(list_nth(prtable, i));
				rtable = lappend(rtable, rte);
				transfer_array[j] = index++;
			}
		}
	}
	return rtable;
}

//找到global出口
static List* findvarlist(List* joinlist, Index* transfer_array, int length)
{
	ListCell* lc;
	List* reslist = NIL;
	foreach(lc, joinlist)
	{
		Expr* expr = (Expr*)lfirst(lc);
		if (!is_RC(expr))
		{
			List* vars = pull_var_clause((Node*)expr, 0);
			Var* var1 = lfirst(vars->head);
			Var* var2 = (Var*)lfirst(vars->head->next);
			//当前query到外围
			if (transfer_array[var1->varno - 1] != 0 && transfer_array[var2->varno - 1] == 0)
			{
				ListCell* lc1;
				bool append = true;
				foreach(lc1, reslist)
				{
					Var* var = (Var*)lfirst(lc1);
					if (var->varattno == var1->varattno && var->varno == var1->varno)
					{
						append = false;
						break;
					}
				}
				if (append)
				{
					Var* var = copyObjectImpl(var1);
					reslist = lappend(reslist, var);
				}
			}
			else if (transfer_array[var1->varno - 1] == 0 && transfer_array[var2->varno - 1] != 0)
			{
				ListCell* lc1;
				bool append = true;
				foreach(lc1, reslist)
				{
					Var* var = (Var*)lfirst(lc1);
					if (var->varattno == var2->varattno && var->varno == var2->varno)
					{
						append = false;
						break;
					}
				}
				if (append)
				{
					Var* var = copyObjectImpl(var2);
					reslist = lappend(reslist, var);
				}
			}
		}
	}
	return reslist;
}

static Query* createQuery(const Query* global_query, int endLoop, List* rtable, Index* transfer_array, int length)
{
	Query* query;
	query = makeNode(Query);
	query = copyObjectImpl(global_query);
	query->rtable = copyObjectImpl(rtable);
	query->jointree->fromlist = setfromlist(query->jointree->fromlist, transfer_array, length);
	List* varlist = NIL;
	switch (query->jointree->quals->type)
	{
		case T_BoolExpr:
		{
			varlist = findvarlist(((BoolExpr*)query->jointree->quals)->args, transfer_array, length);
			break;
		}
		case T_OpExpr:
		{
			List* temp = lappend(NIL, query->jointree->quals);
			varlist = findvarlist(temp, transfer_array, length);
			break;
		}
	}
	query->targetList = settargetlist(global_query->rtable, rtable, endLoop, varlist, query->targetList, transfer_array, length);
	switch (query->jointree->quals->type)
	{
		case T_BoolExpr:
		{
			((BoolExpr*)query->jointree->quals)->args = setjoinlist(((BoolExpr*)query->jointree->quals)->args, transfer_array, length);
			break;
		}
		case T_OpExpr:
			break;
	}
	if (endLoop == 1)
	{
		query->hasAggs = global_query->hasAggs;
	}
	else
	{
		query->hasAggs = false;
	}
	return query;
}

static bool doNullTestTransfor(NullTest* expr, Index* transfer_array)
{
	List* varlist = pull_var_clause((Node*)expr, 0);
	ListCell* lc;
	foreach(lc, varlist)
	{
		Var* var = (Var*)lfirst(lc);
		if(transfer_array[var->varno - 1] == 0)
			return false;
		var->varno = transfer_array[var->varno - 1];
		var->varnoold = var->varno;
	}
	return true;
}

static bool doOpExprTransfor(OpExpr* expr, Index* transfer_array)
{
	bool flag = true;
	List* varlist = pull_var_clause((Node*)expr, 0);
	ListCell* lc;
	foreach(lc, varlist)
	{
		Var* var = (Var*)lfirst(lc);
		if (transfer_array[var->varno - 1] == 0)
			flag = false;
		var->varno = transfer_array[var->varno - 1];
		var->varnoold = var->varno;
	}
	return flag;
}

static bool doScalarArrayOpExprTransfor(ScalarArrayOpExpr* expr, Index* transfer_array)
{
	List* varlist = pull_var_clause((Node*)expr, 0);
	ListCell* lc;
	foreach(lc, varlist)
	{
		Var* var = (Var*)lfirst(lc);
		if (transfer_array[var->varno - 1] == 0)
			return false;
		var->varno = transfer_array[var->varno - 1];
		var->varnoold = var->varno;
	}
	return true;
}

static List* setjoinlist(List* qualslist, Index* transfer_array, int length)
{
	ListCell* lc;
	foreach(lc, qualslist)
	{
		Expr* expr = (Expr*)lfirst(lc);
		bool flag = true;
		switch (expr->type)
		{
			case T_NullTest:
			{
				NullTest* nulltest = (NullTest*)expr;
				flag = doNullTestTransfor(nulltest, transfer_array);
				break;
			}
			case T_OpExpr:
			{
				OpExpr* opexpr = (OpExpr*)expr;
				flag = doOpExprTransfor(opexpr, transfer_array);
				break;
			}
			case T_ScalarArrayOpExpr:
			{
				ScalarArrayOpExpr* scalararrayopexpr = (ScalarArrayOpExpr*)expr;
				flag = doScalarArrayOpExprTransfor(scalararrayopexpr, transfer_array);
				break;
			}
			case T_BoolExpr:
			{
				BoolExpr* boolexpr = (BoolExpr*)expr;
				boolexpr->args = setjoinlist(boolexpr->args, transfer_array, length);
				if (boolexpr->args == NULL)
					flag = false;
				break;
			}
		}
		if (!flag)
		{
			qualslist = list_delete(qualslist, lfirst(lc));
		}
	}
	return qualslist;
}

static List* simplifyjoinlist(List* list, Index* transfer_array, bool* graph, int length)
{
	ListCell* lc;
	foreach(lc, list)
	{
		Expr* expr = (Expr*)lfirst(lc);
		if (is_RC(expr))
		{
			List* varlist = pull_var_clause((Node*)expr, 0);
			if (varlist)
			{
				Var* var = (Var*)lfirst(varlist->head);
				if (transfer_array[var->varno - 1] != 0)
					list = list_delete(list, lfirst(lc));
			}
		}
		else
		{
			bool flag = false;
			Index X = 0, Y = 0;
			OpExpr* opexpr = (OpExpr*)expr;
			Var* var1 = (Var*)lfirst(opexpr->args->head);
			Var* var2 = (Var*)lfirst(opexpr->args->head->next);
			Assert(var1->varno != var2->varno);
			X = var1->varno - 1;
			Y = var2->varno - 1;
			if (graph[X * length + Y] == false && graph[Y * length + X] == false)
			{
				list = list_delete(list, lfirst(lc));
			}
		}
	}
	return list;
}

static List* setfromlist(List* fromlist, Index* transfer_array, int length)
{
	ListCell* lc;
	foreach(lc, fromlist)
	{
		RangeTblRef* ref = (RangeTblRef*)lfirst(lc);
		if (transfer_array[ref->rtindex - 1] == 0)
		{
			fromlist = list_delete(fromlist, lfirst(lc));
			continue;
		}
		ref->rtindex = transfer_array[ref->rtindex - 1];
	}
	return fromlist;
}

//varlist - global, targetlist - global
static List* settargetlist(const List* global_rtable, List* local_rtable, int endLoop, List* varlist, List* targetlist, Index* transfer_array, int length)
{
	ListCell* lc;
	if (endLoop == 0)
	{
		targetlist = removeAggref(targetlist);
	}
	foreach(lc, targetlist)
	{
		bool reserved = false;
		TargetEntry* tar = (TargetEntry*)lfirst(lc);
		ListCell* lc1;
		if (tar->expr->type == T_Aggref)
		{
			continue;
		}
		foreach(lc1, local_rtable)
		{
			RangeTblEntry* rte = (RangeTblEntry*)lfirst(lc1);
			Var* vtar = NULL;
			if(tar->expr->type == T_Var)
				vtar = (Var*)tar->expr;
			else if (tar->expr->type == T_RelabelType)
				vtar = (Var*)((RelabelType*)tar->expr)->arg;
			if (vtar == NULL)
				continue;
			RangeTblEntry* rte_1 = list_nth(global_rtable, vtar->varno - 1);
			if (strcmp(rte->eref->aliasname, rte_1->eref->aliasname) == 0)
			{
				vtar->varno = transfer_array[vtar->varno - 1];
				vtar->varnoold = vtar->varno;
				reserved = true;
				break;
			}
		}
		if (reserved)
			continue;
		targetlist = list_delete(targetlist, lfirst(lc));
	}
	foreach(lc, varlist)
	{
		Var* var = (Var*)lfirst(lc);
		if (var != NULL)
		{
			TargetEntry* tar = makeNode(TargetEntry);
			RangeTblEntry* rte = (RangeTblEntry*)list_nth(global_rtable, var->varno - 1);
			tar->resorigtbl = rte->relid;
			int len = strlen(rte->eref->aliasname) + strlen(strVal(list_nth(rte->eref->colnames, var->varattno - 1))) + 2;
			tar->resname = (char*)palloc(len * sizeof(char));
			sprintf(tar->resname, "%s_%s", rte->eref->aliasname, strVal(list_nth(rte->eref->colnames, var->varattno - 1)));
			tar->resorigcol = var->varattno;
			if(targetlist)
				tar->resno = targetlist->length + 1;
			else
				tar->resno = 1;
			//该变量所在的表直接参与此次join
			if (transfer_array[var->varno - 1] != 0)
			{
				var->varno = transfer_array[var->varno - 1];
				var->varnoold = var->varno;
			}
			//该变量所在的表间接参与此次join
			else
			{
				for (int i = 0; i < length; i++)
				{
					if (transfer_array[i] != 0)
					{
						var->varno = transfer_array[i];
						var->varnoold = var->varno;
						break;
					}
				}
			}
			tar->expr = copyObjectImpl(var);
			targetlist = lappend(targetlist, tar);
		}
	}
	return targetlist;
}

//get relation foreign key
static List* grFK(List* rtable)
{
	ListCell* lc;
	List* fkey_list = NIL;
	Index relid = 0;
	foreach(lc, rtable)
	{
		relid++;
		RangeTblEntry* rte = (RangeTblEntry*)lfirst(lc);
		if (rte->relid == 0)
			continue;
		Relation relation;
		relation = table_open(rte->relid, NoLock);
		List* cachedfkeys;
		ListCell* lc1;
		cachedfkeys = RelationGetFKeyList(relation);
		foreach(lc1, cachedfkeys)
		{
			ForeignKeyCacheInfo* cachedfk = (ForeignKeyCacheInfo*)lfirst(lc1);
			Index rti;
			ListCell* lc2;
			Assert(cachedfk->conrelid == RelationGetRelid(relation));
			rti = 0;
			foreach(lc2, rtable)
			{
				RangeTblEntry* rte = (RangeTblEntry*)lfirst(lc2);
				ForeignKeyOptInfo* info;
				rti++;
				if (rte->rtekind != RTE_RELATION || rte->relid != cachedfk->confrelid)
					continue;
				if (rti == relid)
					continue;
				/* OK, let's make an entry */
				info = makeNode(ForeignKeyOptInfo);
				info->con_relid = relid;
				info->ref_relid = rti;
				info->nkeys = cachedfk->nkeys;
				memcpy(info->conkey, cachedfk->conkey, sizeof(info->conkey));
				memcpy(info->confkey, cachedfk->confkey, sizeof(info->confkey));
				memcpy(info->conpfeqop, cachedfk->conpfeqop, sizeof(info->conpfeqop));
				/* zero out fields to be filled by match_foreign_keys_to_quals */
				info->nmatched_ec = 0;
				info->nmatched_rcols = 0;
				info->nmatched_ri = 0;
				memset(info->eclass, 0, sizeof(info->eclass));
				memset(info->rinfos, 0, sizeof(info->rinfos));
				fkey_list = lappend(fkey_list, info);
			}
		}
		table_close(relation, NoLock);
	}
	return fkey_list;
}

//Is this local query the last one ?
int hasNext(bool* graph, int length)
{
	if (graph == NULL)
		return 1;
	bool* temp_graph = (bool*)palloc(length * length * sizeof(bool));
	for (int i = 0; i < length * length; i++)
	{
		temp_graph[i] = graph[i];
	}
	int total_cnt = 0;
	if (query_splitting_algorithm == Minsubquery)
	{
		for (int i = 0; i < length; i++)
		{
			for (int j = i + 1; j < length; j++)
			{
				if (temp_graph[i * length + j] == true)
				{
					temp_graph[i * length + j] = false;
					temp_graph[j * length + i] = false;
					total_cnt++;
				}
			}
		}
	}
	else if (query_splitting_algorithm == RelationshipCenter || query_splitting_algorithm == EntityCenter)
	{
		for (int i = 0; i < length; i++)
		{
			int cnt = 0;
			for (int j = 0; j < length; j++)
			{
				if (i == j)
					cnt++;
				if (temp_graph[i * length + j] == true)
				{
					temp_graph[i * length + j] = false;
					temp_graph[j * length + i] = false;
					cnt++;
				}
			}
			if (cnt > 1)
				total_cnt++;
		}
	}
	pfree(temp_graph);
	temp_graph = NULL;
	return total_cnt;
}

//Change the rte's relid and name
void dochange(RangeTblEntry* rte, char* relname, Relation relation, Oid relid)
{
	rte->relid = relid;
	if (relname)
	{
		pfree(rte->eref->aliasname);
		rte->eref->aliasname = relname;
	}
	if (relation)
	{
		list_free(rte->eref->colnames);
		rte->eref->colnames = NIL;
		for (int i = 0; i < relation->rd_att->natts; i++)
		{
			char* str = (char*)palloc((strlen(relation->rd_att->attrs[i].attname.data) + 1) * sizeof(char));
			strcpy(str, relation->rd_att->attrs[i].attname.data);
			rte->eref->colnames = lappend(rte->eref->colnames, makeString(str));
		}
	}
	return;
}
/*
List* makeAggref(List* targetList)
{
	List* resList = NIL;
	ListCell* lc;
	foreach(lc, targetList)
	{
		TargetEntry* old_tar = (TargetEntry*)lfirst(lc);
		Oid old_vartype = ((Var*)old_tar->expr)->vartype;
		TargetEntry* tar = makeNode(TargetEntry);
		tar->resjunk = false;
		tar->resname = old_tar->resname;
		old_tar->resname = NULL;
		tar->resno = old_tar->resno;
		tar->resorigcol = 0;
		tar->resorigtbl = 0;
		tar->ressortgroupref = 0;
		Aggref* aggref = makeNode(Aggref);
		aggref->aggargtypes = lappend_oid(NIL, old_vartype);
		aggref->aggdirectargs = NULL;
		aggref->aggdistinct = NULL;
		aggref->aggfilter = NULL;
		switch (old_vartype)
		{
			case 23:
			{
				aggref->aggfnoid = 2132;
				aggref->inputcollid = 0;
				aggref->aggcollid = 0;
				aggref->aggtype = 23;
				break;
			}
			case 25:
			{
				aggref->aggfnoid = 2145;
				aggref->inputcollid = 100;
				aggref->aggcollid = 100;
				aggref->aggtype = 25;
				break;
			}
			default:
			{
				aggref->aggfnoid = 2145;
				aggref->inputcollid = 100;
				aggref->aggcollid = 100;
				aggref->aggtype = 25;
			}
		}
		aggref->aggkind = 'n';
		aggref->agglevelsup = 0;
		aggref->aggorder = NULL;
		aggref->aggsplit = AGGSPLIT_SIMPLE;
		aggref->aggstar = false;
		aggref->aggtranstype = 0;
		aggref->aggvariadic = false;
		aggref->args = lappend(NIL, old_tar);
		aggref->location = -1;
		tar->expr = (Expr*)aggref;
		resList = lappend(resList, tar);
	}
	return resList;
}
*/
List* removeAggref(List* targetList)
{
	List* resList = NIL;
	ListCell* lc;
	foreach(lc, targetList)
	{
		TargetEntry* old_tar = (TargetEntry*)lfirst(lc);
		if (old_tar->expr->type == T_Aggref)
		{
			TargetEntry* tar = lfirst(((Aggref*)old_tar->expr)->args->head);
			if (tar->expr->type == T_RelabelType)
			{
				if (((RelabelType*)tar->expr)->relabelformat == COERCE_IMPLICIT_CAST)
					tar->expr = ((RelabelType*)tar->expr)->arg;
			}
			tar->resname = old_tar->resname;
			resList = lappend(resList, tar);
		}
		else
		{
			resList = lappend(resList, old_tar);
		}
	}
	return resList;
}

static Plan* find_node_with_nleaf_recursive(Plan* plan, int nleaf, int* leaf_has, int* depth)
{
	if (plan->lefttree == NULL)
	{
		*depth = *depth + 1;
		*leaf_has = 1;
		return NULL;
	}
	*depth = *depth + 1;
	int left_leaf = 0, right_leaf = 0, left_depth = *depth, right_depth = *depth;
	Plan* left_res = NULL;
	left_res = find_node_with_nleaf_recursive(plan->lefttree, nleaf, &left_leaf, &left_depth);
	Plan* right_res = NULL;
	if (plan->righttree)
		right_res = find_node_with_nleaf_recursive(plan->righttree, nleaf, &right_leaf, &right_depth);
	*leaf_has = left_leaf + right_leaf;
	if (left_res && right_res)
	{
		if (left_depth > right_depth)
		{
			*depth = left_depth;
			return left_res;
		}
		else
		{
			*depth = right_depth;
			return right_res;
		}
	}
	else if (left_res)
	{
		*depth = left_depth;;
		return left_res;
	}
	else if (right_res)
	{
		*depth = right_depth;
		return right_res;
	}
	else if (*leaf_has == nleaf)
	{
		*depth = (left_depth > right_depth) ? left_depth : right_depth;
		return plan;
	}
	else
	{
		*depth = (left_depth > right_depth) ? left_depth : right_depth;
		return NULL;
	}
}

static void walk_plantree(Plan* plan, Index* rel)
{
	Index res = 0;
	if (plan->lefttree == NULL)
	{
		res = ((Scan*)plan)->scanrelid;
		if (rel[0] == 0)
			rel[0] = res;
		else
			rel[1] = res;
	}
	if (plan->lefttree != NULL)
		walk_plantree(plan->lefttree, rel);
	if (plan->righttree != NULL)
		walk_plantree(plan->righttree, rel);
	return;
}

int tarfunc(Index* rels, PlannedStmt* new, PlannedStmt* old)
{
	if(old == NULL)
		return NEWBETTER;
	if (new->planTree->plan_rows > 10000000)
	{
		return OLDBETTER;
	}
	if (order_decision == only_cost)
	{
		if (old->planTree->total_cost < new->planTree->total_cost)
		{
			return OLDBETTER;
		}
		else
		{
			return NEWBETTER;
		}
	}
	if (order_decision == only_row)
	{
		if (old->planTree->plan_rows < new->planTree->plan_rows)
		{
			return OLDBETTER;
		}
		else
		{
			return NEWBETTER;
		}
	}
	double fac_old, fac_new;
	if (order_decision == hybrid_row)
	{
		if (new->planTree->plan_rows > 1)
			fac_new = new->planTree->plan_rows;
		else
			fac_new = 1;
		if (old->planTree->plan_rows > 1)
			fac_old = old->planTree->plan_rows;
		else
			fac_old = 1;
		if (fac_new / fac_old > old->planTree->total_cost / new->planTree->total_cost)
		{
			return OLDBETTER;
		}
		else
		{
			return NEWBETTER;
		}
	}
	else if (order_decision == hybrid_sqrt)
	{
		double fac_old, fac_new;
		if (new->planTree->plan_rows > 1)
			fac_new = sqrt(new->planTree->plan_rows);
		else
			fac_new = 1;
		if (old->planTree->plan_rows > 1)
			fac_old = sqrt(old->planTree->plan_rows);
		else
			fac_old = 1;
		if (fac_new / fac_old > old->planTree->total_cost / new->planTree->total_cost)
		{
			return OLDBETTER;
		}
		else
		{
			return NEWBETTER;
		}
	}
	else if (order_decision == hybrid_log)
	{
		if (new->planTree->plan_rows > 1)
			fac_new = log(new->planTree->plan_rows) / log(2);
		else
			fac_new = 1;
		if (old->planTree->plan_rows > 1)
			fac_old = log(old->planTree->plan_rows) / log(2);
		else
			fac_old = 1;
		if (fac_new / fac_old > old->planTree->total_cost / new->planTree->total_cost)
		{
			return OLDBETTER;
		}
		else
		{
			return NEWBETTER;
		}
	}
	else if (order_decision == global_view)
	{
		ListCell* lc;
		bool flag = false;
		foreach(lc, new->rtable)
		{
			RangeTblEntry* rte = (RangeTblEntry*)lfirst(lc);
			if (rte->relid == rels[0])
			{
				flag = true;
				break;
			}
		}
		if (!flag)
			return OLDBETTER;
		flag = false;
		foreach(lc, new->rtable)
		{
			RangeTblEntry* rte = (RangeTblEntry*)lfirst(lc);
			if (rte->relid == rels[1])
			{
				flag = true;
				break;
			}
		}
		if (!flag)
			return OLDBETTER;
		return NEWBETTER;
	}
	return NEWBETTER;
}

static double getMatSize(Oid relid)
{
	int64 size = DatumGetInt64(DirectFunctionCall2Coll(pg_relation_size, 0, relid, (Datum)cstring_to_text("main")));
	if (Abs(size) < 10 * 1024)
		return (double)size / 1000000.0;
	else
	{
		size >>= 9;
		if (Abs(size) < 20 * 1024 - 1)
			return (double)half_rounded(size) / 1000.0;
		else
		{
			size >>= 10;
			if (Abs(size) < 20 * 1024 - 1)
				return (double)half_rounded(size);
			else
			{
				size >>= 10;
				if (Abs(size) < 20 * 1024 - 1)
					return (double)half_rounded(size) * 1000.0;
				else
				{
					size >>= 10;
					return (double)half_rounded(size) * 1000000.0;
				}
			}
		}
	}
}

#define PI 3.141592654

double Gaussian(double mu, double sigma)
{
	static double U, V;
	static int phase = 0;
	double z;
	
	if (phase == 0)
	{
		U = rand() / (RAND_MAX + 1.0);
		V = rand() / (RAND_MAX + 1.0);
		z = sqrt(-2.0 * log(U)) * sin(2.0 * PI * V);
	}
	else
	{
		z = sqrt(-2.0 * log(U)) * cos(2.0 * PI * V);
	}
	
	phase = 1 - phase;

	return z * sigma + mu;
}

int writePlanNode(FILE* fp, PlanState* planstate)
{
	if (planstate->lefttree == NULL)
		return 1;
	if (planstate->type == T_BitmapHeapScanState)
		return 1;
	int left = 0;
	int right = 0;
	left = writePlanNode(fp, planstate->lefttree);
	if (planstate->righttree != NULL)
	{
		right = writePlanNode(fp, planstate->righttree);
		int64 input_size = 0;
		if (planstate->righttree->instrument->ntuples == 0)
		{
			input_size += planstate->righttree->instrument->tuplecount;
		}
		else
		{
			input_size += planstate->righttree->instrument->ntuples;
		}
		if(planstate->lefttree->instrument->ntuples == 0)
		{
			input_size += planstate->lefttree->instrument->tuplecount;
		}
		else
		{
			input_size += planstate->lefttree->instrument->ntuples;
		}
		fprintf(fp, "(%d, %d, %d, %lld, %lld) ", left + right, 0, 0, (int64)planstate->instrument->tuplecount, planstate->instrument->counter.QuadPart);
	}
	return left + right;
}

void writeFile(char* file, QueryDesc* queryDesc)
{
	FILE* fp = fopen(file, "a+");
	writePlanNode(fp, queryDesc->planstate);
	fprintf(fp, "\n");
	fclose(fp);
}