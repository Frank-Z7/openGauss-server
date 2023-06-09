/* -------------------------------------------------------------------------
 *
 * nodeMergeAppend.cpp
 *	  routines to handle MergeAppend nodes.
 *
 * Portions Copyright (c) 2020 Huawei Technologies Co.,Ltd.
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/gausskernel/runtime/executor/nodeMergeAppend.cpp
 *
 * -------------------------------------------------------------------------
 *
 * INTERFACE ROUTINES
 *		ExecInitMergeAppend		- initialize the MergeAppend node
 *		ExecMergeAppend			- retrieve the next tuple from the node
 *		ExecEndMergeAppend		- shut down the MergeAppend node
 *		ExecReScanMergeAppend	- rescan the MergeAppend node
 *
 *	 NOTES
 *		A MergeAppend node contains a list of one or more subplans.
 *		These are each expected to deliver tuples that are sorted according
 *		to a common sort key.  The MergeAppend node merges these streams
 *		to produce output sorted the same way.
 *
 *		MergeAppend nodes don't make use of their left and right
 *		subtrees, rather they maintain a list of subplans so
 *		a typical MergeAppend node looks like this in the plan tree:
 *
 *				   ...
 *				   /
 *				MergeAppend---+------+------+--- nil
 *				/	\		  |		 |		|
 *			  nil	nil		 ...	...    ...
 *								 subplans
 */
#include "postgres.h"
#include "knl/knl_variable.h"

#include "access/tableam.h"
#include "executor/exec/execdebug.h"
#include "executor/node/nodeMergeAppend.h"

/*
 * It gets quite confusing having a heap array (indexed by integers) which
 * contains integers which index into the slots array. These typedefs try to
 * clear it up, but they're only documentation.
 */
typedef int SlotNumber;
typedef int HeapPosition;

static TupleTableSlot* ExecMergeAppend(PlanState* state);
static void heap_insert_slot(MergeAppendState* node, SlotNumber new_slot);
static void heap_siftup_slot(MergeAppendState* node);
static int32 heap_compare_slots(MergeAppendState* node, SlotNumber slot1, SlotNumber slot2);

/* ----------------------------------------------------------------
 *		ExecInitMergeAppend
 *
 *		Begin all of the subscans of the MergeAppend node.
 * ----------------------------------------------------------------
 */
MergeAppendState* ExecInitMergeAppend(MergeAppend* node, EState* estate, int eflags)
{
    MergeAppendState* merge_state = makeNode(MergeAppendState);
    PlanState** merge_plan_states;
    int nplans;
    int i;
    ListCell* lc = NULL;

    /* check for unsupported flags */
    Assert(!(eflags & (EXEC_FLAG_BACKWARD | EXEC_FLAG_MARK)));

    /*
     * Set up empty vector of subplan states
     */
    nplans = list_length(node->mergeplans);

    merge_plan_states = (PlanState**)palloc0(nplans * sizeof(PlanState*));

    /*
     * create new MergeAppendState for our node
     */
    merge_state->ps.plan = (Plan*)node;
    merge_state->ps.state = estate;
    merge_state->mergeplans = merge_plan_states;
    merge_state->ms_nplans = nplans;
    merge_state->ps.ExecProcNode = ExecMergeAppend;

    merge_state->ms_slots = (TupleTableSlot**)palloc0(sizeof(TupleTableSlot*) * nplans);
    merge_state->ms_heap = (int*)palloc0(sizeof(int) * nplans);

    /*
     * Miscellaneous initialization
     *
     * MergeAppend plans don't have expression contexts because they never
     * call ExecQual or ExecProject.
     */
    /*
     * MergeAppend nodes do have Result slots, which hold pointers to tuples,
     * so we have to initialize them.
     */
    ExecInitResultTupleSlot(estate, &merge_state->ps);

    /*
     * call ExecInitNode on each of the plans to be executed and save the
     * results into the array "merge_plans".
     */
    i = 0;
    foreach (lc, node->mergeplans) {
        Plan* initNode = (Plan*)lfirst(lc);

        merge_plan_states[i] = ExecInitNode(initNode, estate, eflags);
        i++;
    }

    /*
     * initialize output tuple type
     * src/gausskernel/runtime/executor/nodeMergeAppend.cpp
     * set to default value HEAP
     */
    ExecAssignResultTypeFromTL(&merge_state->ps);
    merge_state->ps.ps_ProjInfo = NULL;

    /*
     * initialize sort-key information
     */
    merge_state->ms_nkeys = node->numCols;
    merge_state->ms_sortkeys = (SortSupportData*)palloc0(sizeof(SortSupportData) * node->numCols);

    for (i = 0; i < node->numCols; i++) {
        SortSupport sortKey = merge_state->ms_sortkeys + i;

        sortKey->ssup_cxt = CurrentMemoryContext;
        sortKey->ssup_collation = node->collations[i];
        sortKey->ssup_nulls_first = node->nullsFirst[i];
        sortKey->ssup_attno = node->sortColIdx[i];
        /*
         * It isn't feasible to perform abbreviated key conversion, since
         * tuples are pulled into merge_state's binary heap as needed.  It would
         * likely be counter-productive to convert tuples into an abbreviated
         * representation as they're pulled up, so opt out of that additional
         * optimization entirely.
         */
        sortKey->abbreviate = false;

        PrepareSortSupportFromOrderingOp(node->sortOperators[i], sortKey);
    }

    /*
     * initialize to show we have not run the subplans yet
     */
    merge_state->ms_heap_size = 0;
    merge_state->ms_initialized = false;
    merge_state->ms_last_slot = -1;

    return merge_state;
}

/* ----------------------------------------------------------------
 *	   ExecMergeAppend
 *
 *		Handles iteration over multiple subplans.
 * ----------------------------------------------------------------
 */
static TupleTableSlot* ExecMergeAppend(PlanState* state)
{
    MergeAppendState* node = castNode(MergeAppendState, state);
    TupleTableSlot* result = NULL;
    SlotNumber i;

    CHECK_FOR_INTERRUPTS();

    if (!node->ms_initialized) {
        /*
         * First time through: pull the first tuple from each subplan, and set
         * up the heap.
         */
        for (i = 0; i < node->ms_nplans; i++) {
            node->ms_slots[i] = ExecProcNode(node->mergeplans[i]);
            if (!TupIsNull(node->ms_slots[i]))
                heap_insert_slot(node, i);
        }
        node->ms_initialized = true;
    } else {
        /*
         * Otherwise, pull the next tuple from whichever subplan we returned
         * from last time, and insert it into the heap.  (We could simplify
         * the logic a bit by doing this before returning from the prior call,
         * but it's better to not pull tuples until necessary.)
         */
        i = node->ms_last_slot;
        node->ms_slots[i] = ExecProcNode(node->mergeplans[i]);
        if (!TupIsNull(node->ms_slots[i]))
            heap_insert_slot(node, i);
    }

    if (node->ms_heap_size > 0) {
        /* Return the topmost heap node, and sift up the remaining nodes */
        i = node->ms_heap[0];
        result = node->ms_slots[i];
        node->ms_last_slot = i;
        heap_siftup_slot(node);
    } else {
        /* All the subplans are exhausted, and so is the heap */
        result = ExecClearTuple(node->ps.ps_ResultTupleSlot);
    }

    return result;
}

/*
 * Insert a new slot into the heap.  The slot must contain a valid tuple.
 */
static void heap_insert_slot(MergeAppendState* node, SlotNumber new_slot)
{
    SlotNumber* heap = node->ms_heap;
    HeapPosition j;

    Assert(!TupIsNull(node->ms_slots[new_slot]));

    j = node->ms_heap_size++; /* j is where the "hole" is */
    while (j > 0) {
        int i = (j - 1) / 2;

        if (heap_compare_slots(node, new_slot, node->ms_heap[i]) >= 0)
            break;
        heap[j] = heap[i];
        j = i;
    }
    heap[j] = new_slot;
}

/*
 * Delete the heap top (the slot in heap[0]), and sift up.
 */
static void heap_siftup_slot(MergeAppendState* node)
{
    SlotNumber* heap = node->ms_heap;
    HeapPosition i, n;

    if (--node->ms_heap_size <= 0)
        return;
    n = node->ms_heap_size; /* heap[n] needs to be reinserted */
    i = 0;                  /* i is where the "hole" is */
    for (;;) {
        int j = 2 * i + 1;

        if (j >= n) {
            break;
        }
        if (j + 1 < n && heap_compare_slots(node, heap[j], heap[j + 1]) > 0) {
            j++;
        }
        if (heap_compare_slots(node, heap[n], heap[j]) <= 0) {
            break;
        }
        heap[i] = heap[j];
        i = j;
    }
    heap[i] = heap[n];
}

/*
 * Compare the tuples in the two given slots.
 */
static int32 heap_compare_slots(MergeAppendState* node, SlotNumber slot1, SlotNumber slot2)
{
    TupleTableSlot* s1 = node->ms_slots[slot1];
    TupleTableSlot* s2 = node->ms_slots[slot2];

    Assert(s1 != NULL);
    Assert(s2 != NULL);

    int nkey;

    Assert(!TupIsNull(s1));
    Assert(!TupIsNull(s2));

    for (nkey = 0; nkey < node->ms_nkeys; nkey++) {
        SortSupport sortKey = node->ms_sortkeys + nkey;
        AttrNumber attno = sortKey->ssup_attno;
        Datum datum1, datum2;
        bool isNull1 = false;
        bool isNull2 = false;
        int compare;

        datum1 = tableam_tslot_getattr(s1, attno, &isNull1);
        datum2 = tableam_tslot_getattr(s2, attno, &isNull2);

        compare = ApplySortComparator(datum1, isNull1, datum2, isNull2, sortKey);
        if (compare != 0)
            return compare;
    }
    return 0;
}

/* ----------------------------------------------------------------
 *		ExecEndMergeAppend
 *
 *		Shuts down the subscans of the MergeAppend node.
 *
 *		Returns nothing of interest.
 * ----------------------------------------------------------------
 */
void ExecEndMergeAppend(MergeAppendState* node)
{
    PlanState** merge_plans;
    int nplans;
    int i;

    /*
     * get information from the node
     */
    merge_plans = node->mergeplans;
    nplans = node->ms_nplans;

    /*
     * shut down each of the subscans
     */
    for (i = 0; i < nplans; i++)
        ExecEndNode(merge_plans[i]);
}

void ExecReScanMergeAppend(MergeAppendState* node)
{
    int i;

    for (i = 0; i < node->ms_nplans; i++) {
        PlanState* subnode = node->mergeplans[i];

        /*
         * ExecReScan doesn't know about my subplans, so I have to do
         * changed-parameter signaling myself.
         */
        if (node->ps.chgParam != NULL)
            UpdateChangedParamSet(subnode, node->ps.chgParam);

        /*
         * If chgParam of subnode is not null then plan will be re-scanned by
         * first ExecProcNode.
         */
        if (subnode->chgParam == NULL)
            ExecReScan(subnode);
    }
    node->ms_heap_size = 0;
    node->ms_initialized = false;
    node->ms_last_slot = -1;
}
