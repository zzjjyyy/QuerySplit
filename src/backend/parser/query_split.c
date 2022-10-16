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
#include "parser/query_split.h"
#include "fe_utils/simple_list.h"
#include "commands/event_trigger.h"
#include "commands/portalcmds.h"
#include "utils/relmapper.h"
#include "commands/vacuum.h"
#include "utils/rel.h"
#include "storage/buf_internals.h"

#define NEWBETTER 1
#define OLDBETTER 2

//Create a local query
static Query* createQuery(const Query* querytree, CommandDest dest, List* rtable, Index* transfer_array, int length);
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
static void Recon(char* query_string, char* commandTag, Node* pstmt, Query* ori_query, char* completionTag);
//remove redundant join
static void rRj(Query* querytree);
//Transfer fromlist to the local
static List* setfromlist(List* fromlist, Index* transfer_array, int length);
//Transfer global var to local
static List* setjoinlist(List* rclist, CommandDest dest, Index* transfer_array, int length);
//Make a local target list
static List* settargetlist(const List* global_rtable, List* local_rtable, CommandDest dest, List* varlist, List* targetlist, Index* transfer_array, int length);
//Remove used jointree
static List* simplifyjoinlist(List* list, CommandDest dest, Index* transfer_array, bool* graph, int length);
//Split Query by Foreign Key
static List* spq(char* query_string, char* commandTag, Node* pstmt, Query* querytree, char* completionTag);
//from postgres.c
extern void start_xact_command();
static int tarfunc(Index* rels, PlannedStmt* new, PlannedStmt* old);
//Execute the local query
static List* QSExecutor(char* query_string, const char* commandTag, Node* pstmt, PlannedStmt* plannedstmt, CommandDest dest, char* relname, char* completionTag, Query* querytree, Index* transfer_array, List* FKlist, MemoryContext oldcontext);
//find the subquery with lowest cost to be executed
static PlannedStmt* QSOptimizer(Query* global_query, bool* graph, Index* transfer_array, int length);
static Plan* find_node_with_nleaf_recursive(Plan* plan, int nleaf, int* leaf_has, int* depth);
static void walk_plantree(Plan* plan, Index* rel);

bool* is_relationship;
//the number of subquery
static int queryId = 0;
//where to send the result, to the client end or temporary table
CommandDest mydest;
Index* transfer_array = NULL;

//The interface
void doQSparse(const char* query_string, const char* commandTag, Node* pstmt, Query* querytree, char* completionTag)
{
	List* FKlist = NIL;
	if (querytree->commandType != CMD_UTILITY && query_splitting_algorithm != Minsubquery)
	{
		//remove Redundant Join
		rRj(querytree);
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
		QSExecutor(query_string, commandTag, pstmt, plannedstmt, DestRemote, NULL, completionTag, querytree, NULL, NIL, oldcontext);
		return;
	}
	ListCell* lc;
	int length = 0;
	foreach(lc, querytree->rtable)
	{
		RangeTblEntry* rte = (RangeTblEntry*)lfirst(lc);
		if (rte->relkind != RELKIND_RELATION)
		{
			MemoryContext oldcontext = MemoryContextSwitchTo(MessageContext);
			plannedstmt = planner(querytree, CURSOR_OPT_PARALLEL_OK, NULL);
			QSExecutor(query_string, commandTag, pstmt, plannedstmt, DestRemote, NULL, completionTag, querytree, NULL, NIL, oldcontext);
			return;
		}
		length++;
	}
	if (length <= 2)
	{
		MemoryContext oldcontext = MemoryContextSwitchTo(MessageContext);
		plannedstmt = planner(querytree, CURSOR_OPT_PARALLEL_OK, NULL);
		QSExecutor(query_string, commandTag, pstmt, plannedstmt, DestRemote, NULL, completionTag, querytree, NULL, NIL, oldcontext);
		return;
	}
	//split parent query by foreign key
	Recon(query_string, commandTag, pstmt, querytree, completionTag);

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

static void Recon(char* query_string, char* commandTag, Node* pstmt, Query* ori_query, char* completionTag)
{
	MemoryContext oldcontext = MemoryContextSwitchTo(MessageContext);
	Query* global_query = copyObjectImpl(ori_query);
	PlannedStmt* plannedstmt = NULL;
	if (global_query->commandType == CMD_UTILITY)
	{
		plannedstmt = QSOptimizer(global_query, NULL, NULL, 0);
		QSExecutor(query_string, commandTag, pstmt, plannedstmt, DestRemote, NULL, completionTag, NULL, NULL, NIL, oldcontext);
		return;
	}
	int length = global_query->rtable->length;
	if (length == 1)
	{
		plannedstmt = QSOptimizer(global_query, NULL, NULL, length);
		QSExecutor(query_string, commandTag, pstmt, plannedstmt, DestRemote, NULL, completionTag, NULL, NULL, NIL, oldcontext);
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
		if (is_RC(lc->data.ptr_value))
			RClist = lappend(RClist, lc->data.ptr_value);
		else
			Joinlist = lappend(Joinlist, lc->data.ptr_value);
	}
	List* FKlist = grFK(global_query->rtable);
	//transfer join list to join graph
	bool* graph = List2Graph(is_relationship, Joinlist, FKlist, length);
	//value start from 1, index start from 0
	transfer_array = (Index*)palloc(length * sizeof(Index));
	while (plannedstmt = QSOptimizer(global_query, graph, transfer_array, length))
	{
		queryId++;
		char* relname = NULL;
		//Should we output the result or save it as a temporary table
		if (mydest == DestIntoRel)
		{
			relname = palloc(7 * sizeof(char));
			sprintf(relname, "temp%d", queryId);
		}
		//Execute the subquery and do some change for next subquery creation
		FKlist = QSExecutor(query_string, commandTag, pstmt, plannedstmt, mydest, relname, completionTag, global_query, transfer_array, FKlist, oldcontext);
		//finish_xact_command();
		if (mydest == DestRemote)
		{
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
static PlannedStmt* QSOptimizer(Query* global_query, bool* graph, Index* transfer_array, int length)
{
	PlannedStmt* result = NULL;
	//start_xact_command();
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
				mydest = DestIntoRel;
			else if (remain == 1)
				mydest = DestRemote;
			else if (remain == 0)
				return NULL;
			for (int j = 0; j < length; j++)
				transfer_array[j] = 0;
			//Get the rang table list for this subgraph
			List* rtable = getRT_2(global_query->rtable, graph, length, i, transfer_array);
			//Can this subgraph make a join ?
			if (rtable->length < 2)
			{
				continue;
			}
			char* relname = NULL;
			//If so, create a subquery
			Query* local_query = createQuery(global_query, mydest, rtable, transfer_array, length);
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
					mydest = DestIntoRel;
				else if (remain == 1)
					mydest = DestRemote;
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
				Query* local_query = createQuery(global_query, mydest, rtable, transfer_array, length);
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
			((BoolExpr*)global_query->jointree->quals)->args = simplifyjoinlist(((BoolExpr*)global_query->jointree->quals)->args, mydest, transfer_array, graph, length);
			break;
		}
		case T_OpExpr:
		{
			global_query->jointree->quals = NULL;
			break;
		}
	}
	return result;
}

//Executor
static List* QSExecutor(char* query_string, const char* commandTag, Node* pstmt, PlannedStmt* plannedstmt, CommandDest dest, char* relname, char* completionTag, Query* querytree, Index* transfer_array, List* FKlist, MemoryContext oldcontext)
{
	Oid relid;
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
	PortalStart(portal, NULL, 0, SnapshotAny);
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
		//into->onCommit = ONCOMMIT_DROP;
		into->rel->inh = false;
		into->skipData = false;
		into->viewQuery = NULL;
		receiver = CreateIntoRelDestReceiver(into);
	}
	MemoryContextSwitchTo(oldcontext);
	//Executor
	(void)PortalRun(portal, FETCH_ALL, true, true, receiver, receiver, completionTag);
	if (dest == DestIntoRel)
		FKlist = Prepare4Next(querytree, transfer_array, (DR_intorel*)receiver, plannedstmt, relname, FKlist);
	receiver->rDestroy(receiver);
	PortalDrop(portal, false);
	EndCommand(completionTag, dest);
	return FKlist;
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
			global_query->jointree->fromlist = list_delete(global_query->jointree->fromlist, list_nth(global_query->jointree->fromlist, i));
		}
	}
	RangeTblEntry* rte = (RangeTblEntry*)list_nth(global_query->rtable, X);
	dochange(rte, relname, relation, relid);
	Index index = 1;
	foreach(lc, global_query->jointree->fromlist)
	{
		RangeTblRef* rtr = (RangeTblRef*)lfirst(lc);
		rtr->rtindex = index++;
	}
	foreach(lc, global_query->targetList)
	{
		TargetEntry* tar = (TargetEntry*)lfirst(lc);
		Var* vtar;
		if (tar->expr->type == T_Aggref)
		{
			TargetEntry* te = lfirst(((Aggref*)tar->expr)->args->head);
			vtar = te->expr;
		}
		else
		{
			vtar = (Var*)tar->expr;
		}
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
	bool* graph = (bool*)palloc(length * length * sizeof(bool));
	memset(graph, false, length * length * sizeof(bool));
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
	return (((Node*)lfirst(opexpr->args->head->next))->type == T_Const);
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
			OpExpr* opexpr = (OpExpr*)expr;
			NodeTag type = ((Node*)lfirst(opexpr->args->head))->type;
			Var* var1 = lfirst(opexpr->args->head);
			Var* var2 = (Var*)lfirst(opexpr->args->head->next);
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

static Query* createQuery(const Query* global_query, CommandDest dest, List* rtable, Index* transfer_array, int length)
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
	query->targetList = settargetlist(global_query->rtable, rtable, dest, varlist, query->targetList, transfer_array, length);
	switch (query->jointree->quals->type)
	{
		case T_BoolExpr:
		{
			((BoolExpr*)query->jointree->quals)->args = setjoinlist(((BoolExpr*)query->jointree->quals)->args, dest, transfer_array, length);
			break;
		}
		case T_OpExpr:
			break;
	}
	if (dest == DestRemote)
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
	NodeTag type = nodeTag(expr->arg);
	Var* var = NULL;
	if (type == T_Var)
		var = (Var*)expr->arg;
	else if (type == T_RelabelType)
		var = (Var*)((RelabelType*)expr->arg)->arg;
	if (transfer_array[var->varno - 1] == 0)
		return false;
	var->varno = transfer_array[var->varno - 1];
	var->varnoold = var->varno;
	return true;
}

static bool doOpExprTransfor(OpExpr* expr, Index* transfer_array)
{
	bool flag = true;
	NodeTag type1 = ((Node*)lfirst(expr->args->head))->type;
	Var* var1 = NULL;
	Var* var2 = NULL;
	if (type1 == T_Var)
	{
		var1 = (Var*)lfirst(expr->args->head);
	}
	else if (type1 == T_RelabelType)
	{
		var1 = (Var*)((RelabelType*)lfirst(expr->args->head))->arg;
	}
	NodeTag type2 = ((Node*)lfirst(expr->args->head->next))->type;
	if (type2 == T_Var)
	{
		var2 = (Var*)lfirst(expr->args->head->next);
	}
	else if (type2 == T_RelabelType)
	{
		var2 = (Var*)((RelabelType*)lfirst(expr->args->head->next))->arg;
	}
	if (var1 && transfer_array[var1->varno - 1] == 0)
	{
		flag = false;
	}
	else if (var1)
	{
		var1->varno = transfer_array[var1->varno - 1];
		var1->varnoold = var1->varno;
	}
	if (var2 && transfer_array[var2->varno - 1] == 0)
	{
		flag = false;
	}
	else if (var2)
	{
		var2->varno = transfer_array[var2->varno - 1];
		var2->varnoold = var2->varno;
	}
	return flag;
}

static bool doScalarArrayOpExprTransfor(ScalarArrayOpExpr* expr, Index* transfer_array)
{
	NodeTag type = nodeTag(lfirst(expr->args->head));
	Var* var = NULL;
	if (type == T_Var)
		var = (Var*)lfirst(expr->args->head);
	else if (type == T_RelabelType)
		var = (Var*)((RelabelType*)lfirst(expr->args->head))->arg;
	if (transfer_array[var->varno - 1] == 0)
		return false;
	var->varno = transfer_array[var->varno - 1];
	var->varnoold = var->varno;
	return true;
}

static List* setjoinlist(List* qualslist, CommandDest dest, Index* transfer_array, int length)
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
				boolexpr->args = setjoinlist(boolexpr->args, dest, transfer_array, length);
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

static List* simplifyjoinlist(List* list, CommandDest dest, Index* transfer_array, bool* graph, int length)
{
	ListCell* lc;
	foreach(lc, list)
	{
		Expr* expr = (Expr*)lfirst(lc);
		if (is_RC(expr))
		{
			List* varlist = pull_var_clause(expr, 0);
			Var* var = (Var*)lfirst(varlist->head);
			if (transfer_array[var->varno - 1] != 0)
				list = list_delete(list, lfirst(lc));
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
static List* settargetlist(const List* global_rtable, List* local_rtable, CommandDest dest, List* varlist, List* targetlist, Index* transfer_array, int length)
{
	ListCell* lc;
	if (dest != DestRemote)
	{
		targetlist = removeAggref(targetlist);
	}
	foreach(lc, targetlist)
	{
		bool reserved = false;
		TargetEntry* tar = (TargetEntry*)lfirst(lc);
		ListCell* lc1;
		if (tar->expr->type != T_Var)
		{
			continue;
		}
		foreach(lc1, local_rtable)
		{
			RangeTblEntry* rte = (RangeTblEntry*)lfirst(lc1);
			RangeTblEntry* rte_1 = list_nth(global_rtable, ((Var*)tar->expr)->varno - 1);
			if (rte->relid == rte_1->relid)
			{
				Var* vtar = (Var*)tar->expr;
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
	pfree(rte->eref->aliasname);
	rte->eref->aliasname = relname;
	list_free(rte->eref->colnames);
	rte->eref->colnames = NIL;
	for (int i = 0; i < relation->rd_att->natts; i++)
	{
		char* str = (char*)palloc((strlen(relation->rd_att->attrs[i].attname.data) + 1) * sizeof(char));
		strcpy(str, relation->rd_att->attrs[i].attname.data);
		rte->eref->colnames = lappend(rte->eref->colnames, makeString(str));
	}
	return;
}

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
		tar->expr = aggref;
		resList = lappend(resList, tar);
	}
	return resList;
}

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
}