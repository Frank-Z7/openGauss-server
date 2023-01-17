/*
 * Copyright (c) 2020 Huawei Technologies Co.,Ltd.
 *
 * openGauss is licensed under Mulan PSL v2.
 * You can use this software according to the terms and conditions of the Mulan PSL v2.
 * You may obtain a copy of Mulan PSL v2 at:
 *
 *          http://license.coscl.org.cn/MulanPSL2
 *
 * THIS SOFTWARE IS PROVIDED ON AN "AS IS" BASIS, WITHOUT WARRANTIES OF ANY KIND,
 * EITHER EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO NON-INFRINGEMENT,
 * MERCHANTABILITY OR FIT FOR A PARTICULAR PURPOSE.
 * See the Mulan PSL v2 for more details.
 * -------------------------------------------------------------------------
 *
 * vecrowtovector.cpp
 *    Convert underlying iterator row output to vector batch
 *
 *
 * IDENTIFICATION
 *        Code/src/gausskernel/runtime/vecexecutor/vecnode/vecrowtovector.cpp
 *
 * -------------------------------------------------------------------------
 */
#include "postgres.h"
#include "knl/knl_variable.h"

#include "access/tableam.h"
#include "access/tuptoaster.h"
#include "executor/executor.h"
#include "vecexecutor/vecnoderowtovector.h"
#include "utils/memutils.h"
#include "catalog/pg_type.h"
#include "parser/parse_type.h"
#include "utils/builtins.h"
#include "utils/numeric.h"
#include "utils/numeric_gs.h"
#include "storage/item/itemptr.h"
#include "vecexecutor/vecexecutor.h"
#include "vecexecutor/vectorbatch.h"

#define MAX_LOOPS_FOR_RESET 50

/*
 * @Description: Pack one tuple into vectorbatch.
 *
 * @IN pBatch: Target vectorized data.
 * @IN slot:   source data of one slot.
 * @IN transformContext: switch to this context to avoid memory leak.
 * @return: Return true if pBatch is full, else return false.
 */
bool VectorizeOneTuple(_in_ VectorBatch* pBatch, _in_ TupleTableSlot* slot, _in_ MemoryContext transformContext)
{
    bool may_more = false;
    int i, j;

    /* Switch to Current Transfform Context */
    MemoryContext old_context = MemoryContextSwitchTo(transformContext);

    /*
     * Extract all the values of the old tuple.
     */
    Assert(slot != NULL && slot->tts_tupleDescriptor != NULL);

    tableam_tslot_getallattrs(slot);

    j = pBatch->m_rows;
    for (i = 0; i < slot->tts_nvalid; i++) {
        int type_len;
        Form_pg_attribute attr = &slot->tts_tupleDescriptor->attrs[i];

        if (slot->tts_isnull[i] == false) {
            type_len = attr->attlen;
            switch (type_len) {
                case sizeof(char):
                case sizeof(int16):
                case sizeof(int32):
                case sizeof(Datum):
                    pBatch->m_arr[i].m_vals[j] = slot->tts_values[i];
                    break;
                case 12:
                case 16:
                case 64:
                case -2:
                    pBatch->m_arr[i].AddVar(slot->tts_values[i], j);
                    break;
                case -1: {
                    Datum v = PointerGetDatum(PG_DETOAST_DATUM(slot->tts_values[i]));
                    /* if numeric cloumn, try to convert numeric to big integer */
                    if (attr->atttypid == NUMERICOID) {
                        v = try_convert_numeric_normal_to_fast(v);
                    }
                    pBatch->m_arr[i].AddVar(v, j);
                    /* because new memory may be created, so we have to check and free in time. */
                    if (DatumGetPointer(slot->tts_values[i]) != DatumGetPointer(v)) {
                        pfree(DatumGetPointer(v));
                    }
                    break;
                }
                case 6:
                    if (attr->atttypid == TIDOID && attr->attbyval == false) {
                        pBatch->m_arr[i].m_vals[j] = 0;
                        ItemPointer dest_tid = (ItemPointer)(pBatch->m_arr[i].m_vals + j);
                        ItemPointer src_tid = (ItemPointer)DatumGetPointer(slot->tts_values[i]);
                        *dest_tid = *src_tid;
                    } else {
                        pBatch->m_arr[i].AddVar(slot->tts_values[i], j);
                    }
                    break;
                default:
                    ereport(ERROR, (errcode(ERRCODE_INDETERMINATE_DATATYPE), errmsg("unsupported datatype branch")));
            }

            SET_NOTNULL(pBatch->m_arr[i].m_flag[j]);
        } else {
            SET_NULL(pBatch->m_arr[i].m_flag[j]);
        }
    }

    pBatch->m_rows++;
    if (pBatch->m_rows == BatchMaxSize) {
        may_more = true;
    }

    /* Switch to OldContext */
    (void)MemoryContextSwitchTo(old_context);

    return may_more;
}

inline struct varlena* DetoastDatumBatch(struct varlena* datum, ScalarVector* arr)
{
    if (VARATT_IS_EXTENDED(datum)) {
        return heap_tuple_untoast_attr(datum, arr);
    } else {
        return datum;
    }
}

template<bool hasNull>
static inline void FillVector(ScalarVector* ipVector, int rows, ScalarVector* opVector = NULL)
{
    ScalarVector* pVector = opVector ? opVector : ipVector;

    for (int i = 0; i < rows; i++) {
        if (hasNull && unlikely(IS_NULL(ipVector->m_flag[i]))) {
            continue;
        }

        pVector->AddVar(ipVector->m_vals[i], i);
    }
}

template<bool hasNull>
static inline void FillTidVector(ScalarVector* ipVector, int rows, ScalarVector* opVector = NULL)
{
    ScalarVector* pVector = opVector ? opVector : ipVector;

    for (int i = 0; i < rows; i++) {
        if (hasNull && unlikely(IS_NULL(ipVector->m_flag[i]))) {
            continue;
        }

        ItemPointer srcTid = (ItemPointer)DatumGetPointer(ipVector->m_vals[i]);
        ItemPointer destTid = (ItemPointer)(&pVector->m_vals[i]);
        *destTid = *srcTid;
    }
}

template<bool hasNull>
static inline void FillVarlenaVector(Form_pg_attribute attr, ScalarVector* ipVector, int rows, ScalarVector* opVector = NULL)
{
    ScalarVector* pVector = opVector ? opVector : ipVector;
    Datum v, v0;
    int i, off;

    if (opVector) {
        pVector = opVector;
        off = opVector->m_rows;
    }
    else {
        pVector = ipVector;
        off = 0;
    }

    if (attr->atttypid == NUMERICOID) {
        for (i = 0; i < rows; i++) {
            if (hasNull && unlikely(IS_NULL(ipVector->m_flag[i]))) {
                continue;
            }
            
            v = ipVector->m_vals[i];
            /* if numeric cloumn, try to convert numeric to big integer */
            pVector->m_vals[i + off] = try_direct_convert_numeric_normal_to_fast(v, pVector);
        }
    }
    else {
        for (i = 0; i < rows; i++) {
            if (hasNull && unlikely(IS_NULL(ipVector->m_flag[i]))) {
                continue;
            }
            
            v0 = ipVector->m_vals[i];
            v = PointerGetDatum(DetoastDatumBatch((struct varlena *)DatumGetPointer(v0), pVector));
            if (v == v0) {
                pVector->AddVar(v0, i + off);
            } else {
                pVector->m_vals[i + off] = v;
            }
        }
    }
}

template<bool hasNull>
static void TransformScalarVector(Form_pg_attribute attr, ScalarVector* ipVector, int rows, ScalarVector* opVector = NULL)
{
    switch (attr->attlen) {
        case sizeof(char):
        case sizeof(int16):
        case sizeof(int32):
        case sizeof(Datum):
            if (opVector) {
                for (int i = 0; i < rows; i++) {
                    if (hasNull && unlikely(IS_NULL(ipVector->m_flag[i]))) {
                        continue;
                    }
                    opVector->m_vals[opVector->m_rows + i] = ipVector->m_vals[i];     
                }
            }
            break;
        /* See ScalarVector::DatumToScalar to get the define */
        case 12:  /* TIMETZOID, TINTERVALOID */
        case 16:  /* INTERVALOID, UUIDOID */
        case 64:  /* NAMEOID */
        case -2:
            FillVector<hasNull>(ipVector, rows, opVector);
            break;
        case -1:
            FillVarlenaVector<hasNull>(attr, ipVector, rows, opVector);
            break;
        case 6:
            if (attr->atttypid == TIDOID && !attr->attbyval) {
                FillTidVector<hasNull>(ipVector, rows, opVector);
            } else {
                FillVector<hasNull>(ipVector, rows, opVector);
            }
            break;
        default:
            ereport(ERROR,
                (errcode(ERRCODE_INDETERMINATE_DATATYPE), errmsg("unsupported datatype branch")));
    }
}

void VectorizeTupleBatchMode(VectorBatch *ipBatch, VectorBatch *opBatch, TupleTableSlot **slots,
    ExprContext *econtext, SeqScanState *node, int rows)
{
    int i, colidx = 0;
    MemoryContext transformContext = econtext->ecxt_per_tuple_memory;
    ProjectionInfo *proj = node->ps.ps_ProjInfo;
    AttrNumber att;
    Form_pg_attribute attr;
    ScanBatchState *scanstate = node->scanBatchState;

    /* Extract all the values of the old tuple */
    MemoryContext oldContext = MemoryContextSwitchTo(transformContext);

    for (i = 0; i < scanstate->colNum; i++) {
        if (scanstate->colAttr[i].isProject) {
            att = proj->pi_varNumbers[i];
            if (scanstate->colAttr[i].lateRead) {
                colidx = scanstate->colAttr[i].colId;
                attr = &slots[0]->tts_tupleDescriptor->attrs[colidx];
                if (scanstate->nullflag[colidx]) {
                    TransformScalarVector<true>(attr, &ipBatch->m_arr[att - 1], rows, &opBatch->m_arr[i]);
                } else {
                    TransformScalarVector<false>(attr, &ipBatch->m_arr[att - 1], rows, &opBatch->m_arr[i]);
                }

                memcpy_s(&opBatch->m_arr[i].m_flag[opBatch->m_rows], BatchMaxSize, &ipBatch->m_arr[att - 1].m_flag[0], rows);
            }
            else {
                /* Process columns that have been transformed, if there is overlap */
                opBatch->m_arr[i].copyDeep(&(ipBatch->m_arr[att - 1]), 0, rows);
            }
        }
    }

    MemoryContextSwitchTo(oldContext);
}

template <bool lateRead>
void VectorizeTupleBatchModeInPlace(VectorBatch *pBatch, TupleTableSlot **slots,
    ExprContext *econtext, ScanBatchState *scanstate, int rows)
{
    int i, colidx = 0;
    MemoryContext transformContext = econtext->ecxt_per_tuple_memory;
    Form_pg_attribute attr;

    /* Extract all the values of the old tuple */
    MemoryContext oldContext = MemoryContextSwitchTo(transformContext);

    /* for not late read, deform all the column into batch */
    if (!lateRead) {
        for (i = 0; i < rows; i++) {
            tableam_tslot_formbatch(slots[i], pBatch, i, scanstate->maxcolId);
        }

        for (i = 0; i < scanstate->maxcolId; i++) {
            scanstate->nullflag[i] =  pBatch->m_arr[i].m_const;
            pBatch->m_arr[i].m_const = false;
        }
    }

    for (i = 0; i < scanstate->colNum; i++) {
        if ((lateRead && scanstate->colAttr[i].lateRead) || (!lateRead && !scanstate->colAttr[i].lateRead)) {
            colidx = scanstate->colAttr[i].colId;
            attr = &slots[0]->tts_tupleDescriptor->attrs[colidx];
            if (scanstate->nullflag[colidx]) {
                TransformScalarVector<true>(attr, &pBatch->m_arr[colidx], rows);
            } else {
                TransformScalarVector<false>(attr, &pBatch->m_arr[colidx], rows);
            }
        }
    }

    MemoryContextSwitchTo(oldContext);
}

/*
 * @Description: Vectorized Operator--Convert row data to vector batch.
 *
 * @IN state: Row To Vector State.
 * @return: Return the batch of row table data, return NULL otherwise.
 */
static VectorBatch* ExecRowToVecTupleMode(RowToVecState* state)
{
    int i;
    PlanState* outer_plan = NULL;
    TupleTableSlot* outer_slot = NULL;
    VectorBatch* batch = state->m_pCurrentBatch;

    /* Reset Current ecxt_per_tuple_memory Context */
    ExprContext* econtext = state->ps.ps_ExprContext;
    ResetExprContext(econtext);

    /* Get state info from node */
    outer_plan = outerPlanState(state);
    batch->Reset();

    /*
     * ExecProcNode() may restart if we invoke it after it return NULL
     * so we have to guard it ourselves.
     */
    if (state->m_fNoMoreRows) {
        goto done;
    }

    /*
     * Process each outer-plan tuple, and then fetch the next one, until we
     * exhaust the outer plan.
     */
    for (;;) {
        outer_slot = ExecProcNode(outer_plan);
        if (TupIsNull(outer_slot)) {
            state->m_fNoMoreRows = true;
            break;
        }

        /*
         * Vectorize one tuple and switch to ecxt_per_tuple_memory of
         * exprcontext.
         */
        if (VectorizeOneTuple(batch, outer_slot, econtext->ecxt_per_tuple_memory)) {
            /* It is full now, now return current batch */
            break;
        }
    }

done:
    for (i = 0; i < batch->m_cols; i++) {
        batch->m_arr[i].m_rows = batch->m_rows;
    }

    return batch;
}

/*
 * @Description: Process Qual and Project, The vectorization of tuples 
 * if fSimpleMap is true, vectorize tuple in pScanBatch, else output pFinalBatch.
 * @IN pScanBatch: Scan Batch
 * @IN pFinalBatch: Final Batch
 * @return: if pOutBatch = NULL                              : Batch filters all tuples
 *          if pOutBatch = pFinalBatch                       : Has been output directly to pFinalBatch
 *          if pOutBatch != pFinalBatch && pOutBatch != NULL : Output toprojInfo->pi_batch in ExecVecProject
 */
static VectorBatch *ApplyProjectionAndFilterBatch(VectorBatch *pScanBatch, VectorBatch *pFinalBatch,
    SeqScanState *node, TupleTableSlot **outerslot)
{
    ExprContext *econtext = NULL;
    ProjectionInfo *proj = node->ps.ps_ProjInfo;
    VectorBatch *pOutBatch = NULL;
    bool fSimpleMap = false;
    uint64 inputRows = pScanBatch->m_rows;
    uint64 outputRows = pFinalBatch->m_rows;
    List* qual = (List*)node->ps.qual;

    econtext = node->ps.ps_ExprContext;
    fSimpleMap = node->ps.ps_ProjInfo->pi_directMap;
    if (pScanBatch->m_rows != 0) {
        initEcontextBatch(pScanBatch, NULL, NULL, NULL);
        /* Evaluate the qualification clause if any. */
        if (qual != NULL) {
            ScalarVector *pVector = NULL;
            pVector = ExecVecQual(qual, econtext, false);
            /* If no matched rows, fetch again. */
            if (pVector == NULL) {
                /* collect information of removed rows */
                InstrCountFiltered1(node, inputRows);
                return NULL;
            }

            /* Call optimized PackT function when batch mode is turned on. */
            if (econtext->ecxt_scanbatch->m_sel) {
                pScanBatch->Pack(econtext->ecxt_scanbatch->m_sel);
            }
        }

        if (!fSimpleMap) { 
            /*
            * Late read these columns
            * reset m_rows to the value before VecQual
            */
            VectorizeTupleBatchModeInPlace<true>(pScanBatch, outerslot, econtext, node->scanBatchState, pScanBatch->m_rows);

            /* Project the final result */
            pOutBatch = ExecVecProject(proj, true, NULL);

            if (!proj->pi_exprContext->have_vec_set_fun) {
                pOutBatch->m_rows = Min(pOutBatch->m_rows, pScanBatch->m_rows);
                pOutBatch->FixRowCount();
            }

            /* collect information of removed rows */
            InstrCountFiltered1(node, inputRows - pOutBatch->m_rows);
        }
        else {
            /* stored directly to pFinalBatch */
            VectorizeTupleBatchMode(pScanBatch, pFinalBatch, outerslot, econtext, node, pScanBatch->m_rows);
                  
            pOutBatch = pFinalBatch;

            if (!proj->pi_exprContext->have_vec_set_fun) {
                pOutBatch->m_rows = outputRows + pScanBatch->m_rows;
                pOutBatch->FixRowCount();
            }

            /* collect information of removed rows */
            InstrCountFiltered1(node, inputRows - pScanBatch->m_rows);
        }
    }

    /* Check fullness of return batch and refill it does not contain enough? */
    return pOutBatch;
}

static VectorBatch *ExecRowToVecBatchMode(RowToVecState *state)
{
    VectorBatch *pFinalBatch = state->m_pCurrentBatch;
    SeqScanState *seqScanState = (SeqScanState *)outerPlanState(state);
    ScanBatchState *scanBatchState = seqScanState->scanBatchState;
    ExprContext *econtext = state->ps.ps_ExprContext;
    VectorBatch *pBatch = scanBatchState->pScanBatch;
    seqScanState->ps.ps_ProjInfo->pi_exprContext->ecxt_scanbatch = pBatch;
    VectorBatch *pOutBatch = NULL;
    const int BatchModeMaxTuples = 900;
    const int MaxLoopsForReset = 50;

    pFinalBatch->Reset();
    ResetExprContext(seqScanState->ps.ps_ExprContext);
    ResetExprContext(econtext);

    /* last time return with rows, but last partition is read out */
    if (scanBatchState->scanfinished || state->m_fNoMoreRows) {
        scanBatchState->scanfinished = false;
        /* scan next partition for partition iterator */
        return pFinalBatch;
    }

    pBatch->Reset();
    scanBatchState->scanTupleSlotMaxNum = BatchMaxSize;

    int loops = 0;
    while (true) {
        loops++;

        /* Reset MemoryContext to avoid using too much memory if scan times more than MAX_LOOPS_FOR_RESET */
        if (loops == MaxLoopsForReset) {
            if (pFinalBatch->m_rows != 0) {
                return pFinalBatch;
            }
            loops  = 0;
            ResetExprContext(seqScanState->ps.ps_ExprContext);
            ResetExprContext(econtext);
        }
        ScanBatchResult *scanSlotBatch = (ScanBatchResult *)ExecProcNode((PlanState*)seqScanState);

        /* scanSlotBatch is NULL means early free */
        if (scanSlotBatch == NULL || scanBatchState->scanfinished) {
            /* scan next partition for partition iterator */
            scanBatchState->scanfinished = false;
            state->m_fNoMoreRows = true;
            return pFinalBatch;
        }

        /* Vectorize tuples for filter columns. */
        VectorizeTupleBatchModeInPlace<false>(pBatch, scanSlotBatch->scanTupleSlotInBatch,
            econtext, scanBatchState, scanSlotBatch->rows);

        pBatch->FixRowCount(scanSlotBatch->rows);

        /* apply filter conditions and vectorize tuples for late read columns. */
        pOutBatch = ApplyProjectionAndFilterBatch(pBatch, pFinalBatch, seqScanState, scanSlotBatch->scanTupleSlotInBatch);

        /* prepare pBatch for next time read */
        for (int i = 0 ; i < pBatch->m_cols; i++) {
            scanBatchState->nullflag[i] = false;
        }
        pBatch->FixRowCount(0);

        /* Copy pOutBatch to pFinalBatch */
        if (pOutBatch != pFinalBatch) {
            if (BatchIsNull(pOutBatch)) {
                if (!scanBatchState->scanfinished) {
                    continue;
                }
                scanBatchState->scanfinished = false;
                state->m_fNoMoreRows = true;
                return pFinalBatch;
            }

            for (int i = 0; i < pOutBatch->m_cols; i++) {
                pFinalBatch->m_arr[i].copyDeep(&(pOutBatch->m_arr[i]), 0, pOutBatch->m_rows);
            }

            pFinalBatch->m_rows += pOutBatch->m_rows;
        }
        /* else Already stored directly to pFinalBatch */
        
        scanBatchState->scanTupleSlotMaxNum = BatchMaxSize - pFinalBatch->m_rows;

        /*
         * use BatchModeMaxTuples to avoid that pFinalBatch->m_rows be BatchMaxSize - 1 may
         * cause scanBatchState->scanTupleSlotMaxNum = 1, and each SeqNextBatchMode only read
         * one tuple.
         */
        if (scanBatchState->scanfinished || pFinalBatch->m_rows >= BatchModeMaxTuples) {
            /* scaned tuples of this time may not equals to null, next time must be null */
            return pFinalBatch;
        }
    }

    return pFinalBatch;
}


VectorBatch *ExecRowToVec(RowToVecState *state)
{
    if (state->m_batchMode) {
        return ExecRowToVecBatchMode(state);
    } else {
        return ExecRowToVecTupleMode(state);
    }
}

RowToVecState* ExecInitRowToVec(RowToVec* node, EState* estate, int eflags)
{
    RowToVecState* state = NULL;
    ScanState* scanstate = NULL;

    /*
     * create state structure
     */
    state = makeNode(RowToVecState);
    state->ps.plan = (Plan*)node;
    state->ps.state = estate;
    state->ps.vectorized = true;

    if (!CheckTypeSupportRowToVec(node->plan.targetlist, ERROR)) {
        return NULL;
    }

    /*
     * tuple table initialization
     *
     * sort nodes only return scan tuples from their sorted relation.
     */
    ExecInitResultTupleSlot(estate, &state->ps);

    /* Allocate vector buffers */
    state->m_fNoMoreRows = false;

    /*
     * initialize child nodes
     *
     * We shield the child node from the need to support REWIND, BACKWARD, or
     * MARK/RESTORE.
     */
    if (IsA(((Plan *)node)->lefttree, SeqScan)) {
        ((SeqScan*)((Plan *)node)->lefttree)->scanBatchMode = true;
    }
    outerPlanState(state) = ExecInitNode(outerPlan(node), estate, eflags);

    /*
     * Miscellaneous initialization
     *
     * create expression context for node
     */
    ExecAssignExprContext(estate, &state->ps);

    scanstate = (ScanState *)outerPlanState(state);
    if (IsA(scanstate, SeqScanState) && ((SeqScan *)scanstate->ps.plan)->scanBatchMode) {
        state->m_batchMode = true;
    } else {
        state->m_batchMode = false;
    }

    /*
     * initialize tuple type.  no need to initialize projection info because
     * this node doesn't do projections.
     */
    ExecAssignResultTypeFromTL(
            &state->ps,
            ExecGetResultType(outerPlanState(state))->td_tam_ops);

    TupleDesc res_desc = state->ps.ps_ResultTupleSlot->tts_tupleDescriptor;
    state->m_pCurrentBatch = New(CurrentMemoryContext) VectorBatch(CurrentMemoryContext, res_desc);
    state->ps.ps_ProjInfo = NULL;

    return state;
}

void ExecEndRowToVec(RowToVecState* node)
{
    node->m_pCurrentBatch = NULL;

    /*
     * We don't actually free any ExprContexts here (see comment in
     * ExecFreeExprContext), just unlinking the output one from the plan node
     * suffices.
     */
    ExecFreeExprContext(&node->ps);

    /*
     * clean out the tuple table
     */
    (void)ExecClearTuple(node->ps.ps_ResultTupleSlot);

    /*
     * shut down subplans
     */
    ExecEndNode(outerPlanState(node));
}

void ExecReScanRowToVec(RowToVecState* node)
{
    node->m_fNoMoreRows = false;
    node->m_pCurrentBatch->m_rows = 0;
    ExecReScan(node->ps.lefttree);
}

