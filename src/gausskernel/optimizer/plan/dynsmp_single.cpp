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
 * dynsmp_single.cpp
 *	  functions related to dynamic smp.
 *
 * IDENTIFICATION
 *     src/gausskernel/optimizer/plan/dynsmp_single.cpp
 *
 * -------------------------------------------------------------------------
 */
#include "postgres.h"
#include "knl/knl_variable.h"
#include "optimizer/streamplan.h"

#include "nodes/print.h"

static int stream_dop_walker(Plan* plan);
static int dop_join_degree_walker(Query* parse);


void InitDynamicSmp()
{
    u_sess->opt_cxt.query_dop = u_sess->opt_cxt.saved_dop;
    return;
}

void ChooseStartQueryDop(Query* parse, int hashTableCount)
{
    int n_sess, n_free_procs = 0, n_other_procs = 0;
    int n_dop;

    if (u_sess->opt_cxt.auto_dop_join_th > 0 &&
            dop_join_degree_walker(parse) >= u_sess->opt_cxt.auto_dop_join_th)
        u_sess->opt_cxt.query_dop = 2;

    if (!u_sess->opt_cxt.auto_dop_freeprocs)
        return;

    /* Current number of available threads */
#ifdef USE_ASSERT_CHECKING
    GetNFreeProcs(&n_free_procs, &n_other_procs);
#endif

    n_free_procs = g_instance.proc_base->nFreeProcs;
    n_other_procs = g_instance.proc_base->nFreeUtilProcs;

    /* When the number of free procs is less than the threshold */
    if (n_free_procs < u_sess->opt_cxt.auto_dop_freeprocs_th) {
        u_sess->opt_cxt.query_dop = 1;
        return;
    }

    /* Current sessions */
    n_sess = MAX_BACKEND_SLOT - n_free_procs - n_other_procs;

    if (n_sess <= 0)
        return;

    /* available DOP = free_procs / sessions */
    n_dop = n_free_procs / n_sess;

    /* available DOP >= query_dop */
    if (n_dop >= u_sess->opt_cxt.query_dop) {
        return;
    }

    if (n_dop < 1) {
        n_dop = 1;
    }

    u_sess->opt_cxt.query_dop = n_dop;

    return;
}

void OptimizePlanDop(PlannedStmt* plannedStmt)
{
    int stream_level = 0;
elog(WARNING, "stream_level %d",stream_dop_walker(plannedStmt->planTree));
    if (u_sess->opt_cxt.query_dop <= 2)
        return;

    if (plannedStmt->num_streams <= 0)
        return;

    stream_level = stream_dop_walker(plannedStmt->planTree);

    if (stream_level <= 1)
        return;
    else {
        int dop = (int)pow(u_sess->opt_cxt.query_dop, 1.0/stream_level);

        if (dop < 2)
            dop = 2;

        plannedStmt->plan_dop = dop;

        return;
    }
}

bool IsDynamicSmpEnabled()
{
    if (IS_STREAM_PLAN && u_sess->opt_cxt.auto_dop && u_sess->opt_cxt.query_dop > 1) {
        return true;
    }

    return false;
}

static int stream_dop_walker(Plan* plan)
{
    if (plan == NULL)
        return 0;

    switch (nodeTag(plan)) {
        /* Add Row Adapter */
        case T_CStoreScan:
        case T_DfsScan:
        case T_DfsIndexScan:
        case T_CStoreIndexScan:
        case T_CStoreIndexHeapScan:
        case T_CStoreIndexCtidScan:
#ifdef ENABLE_MULTIPLE_NODES
        case T_TsStoreScan:
#endif   /* ENABLE_MULTIPLE_NODES */
        case T_ForeignScan:
            return 0;

        case T_ExtensiblePlan: {
            int e_ret = 0, t_ret;
            ListCell* lc = NULL;
            ExtensiblePlan* ext_plans = (ExtensiblePlan*) plan;

            foreach (lc, ext_plans->extensible_plans) {
                Plan* plan = (Plan*)lfirst(lc);
                t_ret = stream_dop_walker(plan);
                if (t_ret > e_ret)
                    e_ret = t_ret;
            }

            return e_ret;
        } break;

        case T_RemoteQuery:
        case T_Limit:
        case T_PartIterator:
        case T_SetOp:
        case T_Group:
        case T_Unique:
        case T_BaseResult:
        case T_ProjectSet:
        case T_Sort:
        case T_Material:
        case T_StartWithOp:
        case T_WindowAgg:
        case T_Hash:
        case T_Agg:
        case T_RowToVec:
        case T_VecRemoteQuery:
            return stream_dop_walker(plan->lefttree);

        case T_MergeJoin:
        case T_NestLoop:
        case T_HashJoin:
        case T_RecursiveUnion: {
            int l_ret, r_ret;

            l_ret = stream_dop_walker(plan->lefttree);
            r_ret = stream_dop_walker(plan->righttree);

            return l_ret > r_ret ? l_ret : r_ret;
        } break;

        case T_Append: {
            int a_ret = 0, t_ret;
            Append* append = (Append*)plan;
            ListCell* lc = NULL;

            foreach (lc, append->appendplans) {
                Plan* plan = (Plan*)lfirst(lc);
                t_ret = stream_dop_walker(plan);
                if (t_ret > a_ret)
                    a_ret = t_ret;
            }

            return a_ret;
        } break;

        case T_ModifyTable: {
            int m_ret = 0, t_ret;
            ModifyTable* mt = (ModifyTable*)plan;
            ListCell* lc = NULL;

            foreach (lc, mt->plans) {
                Plan* plan = (Plan*)lfirst(lc);
                t_ret = stream_dop_walker(plan);
                if (t_ret > m_ret)
                    m_ret = t_ret;
            }

            return m_ret;
        } break;

        case T_SubqueryScan: {
            SubqueryScan* ss = (SubqueryScan*)plan;

            if (ss->subplan)
                return stream_dop_walker(ss->subplan);
        } break;

        case T_MergeAppend: {
            int m_ret = 0, t_ret;
            MergeAppend* ma = (MergeAppend*)plan;
            ListCell* lc = NULL;

            foreach (lc, ma->mergeplans) {
                Plan* plan = (Plan*)lfirst(lc);
                t_ret = stream_dop_walker(plan);
                if (t_ret > m_ret)
                    m_ret = t_ret;
            }

            return m_ret;
        } break;

        case T_Stream: {
            return stream_dop_walker(plan->lefttree) + 1;
        } break;

        default:
            break;
    }

    return 0;
}

static int
dop_range_table_walker(RangeTblEntry* rte)
{
    switch (rte->rtekind) {
        case RTE_RELATION:
        case RTE_CTE:
        case RTE_RESULT:
            /* nothing to do */
            return 0;
        case RTE_SUBQUERY:
            return dop_join_degree_walker(rte->subquery);
        case RTE_JOIN:
            return 0;
        case RTE_FUNCTION:
            return 0;
        case RTE_VALUES:
            return 0;
#ifdef PGXC
        case RTE_REMOTE_DUMMY:
            return 0;
#endif /* PGXC */
        default:
            break;
    }

    return 0;
}

static int dop_join_degree_walker(Query* parse)
{
    int d_rt, m_rt = 0;
    ListCell* lc = NULL;

    foreach (lc, parse->rtable) {
        d_rt = dop_range_table_walker((RangeTblEntry*)lfirst(lc));

        if (d_rt > m_rt)
            m_rt = d_rt;
    }

    d_rt = list_length(parse->jointree->fromlist);

    return d_rt + m_rt;
}
