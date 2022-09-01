/*-------------------------------------------------------------------------
 *
 * execSRF.c
 *	  Routines implementing the API for set-returning functions
 *
 * This file serves nodeFunctionscan.c and nodeProjectSet.c, providing
 * common code for calling set-returning functions according to the
 * ReturnSetInfo API.
 *
 * Portions Copyright (c) 1996-2017, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 *	  src/backend/executor/execSRF.c
 *
 *-------------------------------------------------------------------------
 */
#include "postgres.h"

#include "catalog/objectaccess.h"
#include "executor/exec/execdebug.h"
#include "executor/executor.h"
#include "funcapi.h"
#include "miscadmin.h"
#include "nodes/nodeFuncs.h"
#include "parser/parse_coerce.h"
#include "pgstat.h"
#include "utils/acl.h"
#include "utils/builtins.h"
#include "utils/lsyscache.h"
#include "utils/memutils.h"
#include "utils/typcache.h"
#include "catalog/pg_proc.h"
#include "catalog/pg_proc_fn.h"
#include "access/tableam.h"

/* static function decls */
static void init_sexpr(Oid foid, Oid input_collation, SetExprState *sexpr, MemoryContext sexprCxt, bool allowSRF,
                       bool needDescForSRF);
static void ShutdownSetExpr(Datum arg);
template <bool has_refcursor>
static ExprDoneCond ExecEvalFuncArgs(
    FunctionCallInfo fcinfo, List* argList, ExprContext* econtext, int* plpgsql_var_dno = NULL);
static void tupledesc_match(TupleDesc dst_tupdesc, TupleDesc src_tupdesc);

extern bool func_has_refcursor_args(Oid Funcid, FunctionCallInfoData* fcinfo);
extern void check_huge_clob_paramter(FunctionCallInfoData* fcinfo, bool is_have_huge_clob);

THR_LOCAL PLpgSQL_execstate* plpgsql_estate = NULL;

/*
 * Prepare function call in FROM (ROWS FROM) for execution.
 *
 * This is used by nodeFunctionscan.c.
 */
SetExprState *
ExecInitTableFunctionResult(Expr *expr,
							ExprContext *econtext, PlanState *parent)
{
	SetExprState *state = makeNode(SetExprState);

	state->funcReturnsSet = false;
	state->expr = expr;
	state->func.fn_oid = InvalidOid;

	/*
	 * Normally the passed expression tree will be a FuncExpr, since the
	 * grammar only allows a function call at the top level of a table
	 * function reference.  However, if the function doesn't return set then
	 * the planner might have replaced the function call via constant-folding
	 * or inlining.  So if we see any other kind of expression node, execute
	 * it via the general ExecEvalExpr() code.  That code path will not
	 * support set-returning functions buried in the expression, though.
	 */
	if (IsA(expr, FuncExpr))
	{
		FuncExpr   *func = (FuncExpr *) expr;

		state->funcReturnsSet = func->funcretset;
		state->args = ExecInitExprList(func->args, parent);

		init_sexpr(func->funcid, func->inputcollid, state,
				   econtext->ecxt_per_query_memory, func->funcretset, false);
	}
	else
	{
		state->elidedFuncState = ExecInitExpr(expr, parent);
	}

	return state;
}

/*
 * Find the real function return type based on the actual func args' types.
 * @inPara arg_num: the number of func's args.
 * @inPara actual_arg_types: the type array of actual func args'.
 * @inPara fcache: the FuncExprState of this functin.
 * @return Oid: the real func return type.
 */
static Oid getRealFuncRetype(int arg_num, Oid* actual_arg_types, FuncExprState* fcache)
{
    Oid funcid = fcache->func.fn_oid;
    Oid rettype = fcache->func.fn_rettype;

    /* Find the declared arg types in PROCOID by funcid. */
    HeapTuple proctup = SearchSysCache1(PROCOID, ObjectIdGetDatum(funcid));
    if (!HeapTupleIsValid(proctup))
        ereport(ERROR,
            (errcode(ERRCODE_CACHE_LOOKUP_FAILED),
                errmodule(MOD_EXECUTOR),
                errmsg("cache lookup failed for function %u", funcid)));

    oidvector* proargs = ProcedureGetArgTypes(proctup);
    Oid* declared_arg_types = proargs->values;

    /* Find the real return type based on the declared arg types and actual arg types.*/
    rettype = enforce_generic_type_consistency(actual_arg_types, declared_arg_types, arg_num, rettype, false);

    ReleaseSysCache(proctup);
    return rettype;
}

/*
 * Check whether the function is a set function supported by the vector engine.
 */
static bool isVectorEngineSupportSetFunc(Oid funcid)
{
    switch (funcid) {
        case OID_REGEXP_SPLIT_TO_TABLE:                // regexp_split_to_table
        case OID_REGEXP_SPLIT_TO_TABLE_NO_FLAG:        // regexp_split_to_table
        case OID_ARRAY_UNNEST:                         // unnest
            return true;
            break;
        default:
            return false;
            break;
    }
}

/*
 * init_fcache - initialize a FuncExprState node during first use
 */
template <bool vectorized>
static void init_fcache(
    Oid foid, Oid input_collation, FuncExprState* fcache, MemoryContext fcacheCxt, bool needDescForSets)
{
    AclResult aclresult;
    MemoryContext oldcontext;

    /* Check permission to call function */
    aclresult = pg_proc_aclcheck(foid, GetUserId(), ACL_EXECUTE);
    if (aclresult != ACLCHECK_OK)
        aclcheck_error(aclresult, ACL_KIND_PROC, get_func_name(foid));

    /*
     * Safety check on nargs.  Under normal circumstances this should never
     * fail, as parser should check sooner.  But possibly it might fail if
     * server has been compiled with FUNC_MAX_ARGS smaller than some functions
     * declared in pg_proc?
     */
    if (list_length(fcache->args) > FUNC_MAX_ARGS)
        ereport(ERROR,
            (errcode(ERRCODE_TOO_MANY_ARGUMENTS),
                errmsg_plural("cannot pass more than %d argument to a function",
                    "cannot pass more than %d arguments to a function",
                    FUNC_MAX_ARGS,
                    FUNC_MAX_ARGS)));

    /* Set up the primary fmgr lookup information */
    fmgr_info_cxt(foid, &(fcache->func), fcacheCxt);
    fmgr_info_set_expr((Node*)fcache->xprstate.expr, &(fcache->func));

    /* palloc args in fcache's context  */
    oldcontext = MemoryContextSwitchTo(fcacheCxt);
    /* Initialize the function call parameter struct as well */
    if (vectorized)
        InitVecFunctionCallInfoData(
            &fcache->fcinfo_data, &(fcache->func), list_length(fcache->args), input_collation, NULL, NULL);
    else
        InitFunctionCallInfoData(
            fcache->fcinfo_data, &(fcache->func), list_length(fcache->args), input_collation, NULL, NULL);

    if (vectorized) {
        int nargs = list_length(fcache->args);
        ListCell* cell = NULL;
        GenericFunRuntime* genericRuntime = NULL;
        errno_t rc;

        if (fcache->fcinfo_data.flinfo->genericRuntime == NULL) {
            genericRuntime = (GenericFunRuntime*)palloc0(sizeof(GenericFunRuntime));
            InitGenericFunRuntimeInfo(*genericRuntime, nargs);
            fcache->fcinfo_data.flinfo->genericRuntime = genericRuntime;
        } else {
            genericRuntime = fcache->fcinfo_data.flinfo->genericRuntime;

            /* if internalFinfo is not null, release the internalFinfo's memory and set the pointer to null */
            if (genericRuntime->internalFinfo != NULL) {
                FreeFunctionCallInfoData(*(genericRuntime->internalFinfo));
                genericRuntime->internalFinfo = NULL;
            }

            /* reset the memory for reuse */
            rc = memset_s(genericRuntime->args,
                sizeof(GenericFunRuntimeArg) * genericRuntime->compacity,
                0,
                sizeof(GenericFunRuntimeArg) * genericRuntime->compacity);
            securec_check(rc, "\0", "\0");

            rc = memset_s(genericRuntime->inputargs,
                sizeof(Datum) * genericRuntime->compacity,
                0,
                sizeof(Datum) * genericRuntime->compacity);
            securec_check(rc, "\0", "\0");

            rc = memset_s(genericRuntime->nulls,
                sizeof(bool) * genericRuntime->compacity,
                0,
                sizeof(bool) * genericRuntime->compacity);
            securec_check(rc, "\0", "\0");

            /* we have to adjust the GenericFunRuntimeArg when
             * a) nargs is larger than genericRuntime->compacity, which means the allocated memory is not enough to hold
             *    all the argumnets here, we should enlarge the memory.
             * b) nargs is less than VECTOR_GENERIC_FUNCTION_PREALLOCED_ARGS while the allocated memory is much more
             * than that. As VECTOR_GENERIC_FUNCTION_PREALLOCED_ARGS is already enough in most senerios, we should
             * reduce the memory.
             *
             * NOTE: To avoid memory wasting and memory fragments, we free and initilized a new GenericFunRuntimeArg.
             */
            if (unlikely(nargs > genericRuntime->compacity) ||
                (unlikely(genericRuntime->compacity > VECTOR_GENERIC_FUNCTION_PREALLOCED_ARGS) &&
                    nargs <= VECTOR_GENERIC_FUNCTION_PREALLOCED_ARGS)) {
                FreeGenericFunRuntimeInfo(*genericRuntime);
                InitGenericFunRuntimeInfo(*genericRuntime, nargs);
            }
        }

        ScalarVector* pVector = New(CurrentMemoryContext) ScalarVector[nargs];

        int i = 0;
        if (fcache->args && fcache->args->length > 0) {
            Oid* actual_arg_types = (Oid*)palloc0(fcache->args->length * sizeof(Oid));

            foreach (cell, fcache->args) {
                ExprState* argstate = (ExprState*)lfirst(cell);
                Oid funcrettype;
                TupleDesc tupdesc;
                ScalarDesc desc;

                (void)get_expr_result_type((Node*)argstate->expr, &funcrettype, &tupdesc);

                desc.typeId = funcrettype;
                desc.encoded = COL_IS_ENCODE(funcrettype);
                fcache->fcinfo_data.flinfo->genericRuntime->args[i].argType = funcrettype;

                pVector[i].init(CurrentMemoryContext, desc);
                /* Record the real arg types from sub functions. */
                actual_arg_types[i] = funcrettype;
                i++;
            }

            /* Find the real return type for func with return type like ANYELEMENT. */
            fcache->fcinfo_data.flinfo->fn_rettype = getRealFuncRetype(i, actual_arg_types, fcache);
            pfree_ext(actual_arg_types);
        }
        fcache->fcinfo_data.argVector = pVector;
    }
    (void)MemoryContextSwitchTo(oldcontext);

    if (vectorized) {
        if (fcache->func.fn_retset == true) {
            if (!isVectorEngineSupportSetFunc(fcache->func.fn_oid)) {
                ereport(ERROR,
                    (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmodule(MOD_EXECUTOR),
                        errmsg("set-return function not supported in vector eninge")));
            }
        }
        fcache->funcResultDesc = NULL;
    } else {
        /* If function returns set, prepare expected tuple descriptor */
        if (fcache->func.fn_retset && needDescForSets) {
            TypeFuncClass functypclass;
            Oid funcrettype;
            TupleDesc tupdesc;
            MemoryContext oldmemcontext;

            functypclass = get_expr_result_type(fcache->func.fn_expr, &funcrettype, &tupdesc);

            /* Must save tupdesc in fcache's context */
            oldmemcontext = MemoryContextSwitchTo(fcacheCxt);

            if (functypclass == TYPEFUNC_COMPOSITE) {
                /* Composite data type, e.g. a table's row type */
                Assert(tupdesc);
                /* Must copy it out of typcache for safety */
                fcache->funcResultDesc = CreateTupleDescCopy(tupdesc);
                fcache->funcReturnsTuple = true;
            } else if (functypclass == TYPEFUNC_SCALAR) {
                /* Base data type, i.e. scalar */
                tupdesc = CreateTemplateTupleDesc(1, false, TAM_HEAP);
                TupleDescInitEntry(tupdesc, (AttrNumber)1, NULL, funcrettype, -1, 0);
                fcache->funcResultDesc = tupdesc;
                fcache->funcReturnsTuple = false;
            } else if (functypclass == TYPEFUNC_RECORD) {
                /* This will work if function doesn't need an expectedDesc */
                fcache->funcResultDesc = NULL;
                fcache->funcReturnsTuple = true;
            } else {
                /* Else, we will fail if function needs an expectedDesc */
                fcache->funcResultDesc = NULL;
            }

            MemoryContextSwitchTo(oldmemcontext);
        } else
            fcache->funcResultDesc = NULL;
    }

    /* Initialize additional state */
    fcache->funcResultStore = NULL;
    fcache->funcResultSlot = NULL;
    fcache->setArgsValid = false;
    fcache->shutdown_reg = false;
}

void initVectorFcache(Oid foid, Oid input_collation, FuncExprState* fcache, MemoryContext fcacheCxt)
{
    init_fcache<true>(foid, input_collation, fcache, fcacheCxt, false);
}

/*
 *		ExecMakeTableFunctionResult
 *
 * Evaluate a table function, producing a materialized result in a Tuplestore
 * object.
 */
Tuplestorestate* ExecMakeTableFunctionResult(
    SetExprState* setexpr, ExprContext* econtext, TupleDesc expectedDesc, bool randomAccess, FunctionScanState* node)
{
    Tuplestorestate* tupstore = NULL;
    TupleDesc tupdesc = NULL;
    Oid funcrettype;
    bool returnsTuple = false;
    bool returnsSet = false;
    FunctionCallInfoData fcinfo;
    PgStat_FunctionCallUsage fcusage;
    ReturnSetInfo rsinfo;
    HeapTupleData tmptup;
    MemoryContext callerContext;
    MemoryContext oldcontext;
    bool direct_function_call = false;
    bool first_time = true;
    int* var_dno = NULL;
    bool has_refcursor = false;
    bool has_out_param = false;

    FuncExpr *fexpr = NULL;
    bool savedIsSTP = u_sess->SPI_cxt.is_stp;
    bool savedProConfigIsSet = u_sess->SPI_cxt.is_proconfig_set;
    bool proIsProcedure = false;
    bool supportTranaction = false;
#ifdef ENABLE_MULTIPLE_NODES
    if (IS_PGXC_COORDINATOR && (t_thrd.proc->workingVersionNum  >= STP_SUPPORT_COMMIT_ROLLBACK)) {
        supportTranaction = true;
    }
#else
    supportTranaction = true;
#endif
    bool needResetErrMsg = (u_sess->SPI_cxt.forbidden_commit_rollback_err_msg[0] == '\0');

    if (unlikely(setexpr == NULL)) {
        ereport(ERROR, (errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED), errmsg("The input function expression is NULL.")));
    }

    /* Only allow commit at CN, therefore only need to set atomic and relevant check at CN level. */
    if (supportTranaction && IsA(setexpr->expr, FuncExpr)) {
        fexpr = (FuncExpr*)setexpr->expr;
        char prokind = (reinterpret_cast<FuncExprState*>(setexpr))->prokind;
        if (!u_sess->SPI_cxt.is_allow_commit_rollback) {
            node->atomic = true;
        }
        else if (IsAfterTriggerBegin()) {
            node->atomic = true;
            stp_set_commit_rollback_err_msg(STP_XACT_AFTER_TRIGGER_BEGIN);
        }
        /*
         * If proconfig is set we can't allow transaction commands because of the
         * way the GUC stacking works: The transaction boundary would have to pop
         * the proconfig setting off the stack.  That restriction could be lifted
         * by redesigning the GUC nesting mechanism a bit.
         */
        if (!prokind) {
            HeapTuple tp = SearchSysCache1(PROCOID, ObjectIdGetDatum(fexpr->funcid));
            bool isNull = false;
            if (!HeapTupleIsValid(tp)) {
                elog(ERROR, "cache lookup failed for function %u", fexpr->funcid);
            }

            /* immutable or stable function do not support commit/rollback */
            bool isNullVolatile = false;
            Datum provolatile = SysCacheGetAttr(PROCOID, tp, Anum_pg_proc_provolatile, &isNullVolatile);
            if (!isNullVolatile && CharGetDatum(provolatile) != PROVOLATILE_VOLATILE) {
                node->atomic = true;
                stp_set_commit_rollback_err_msg(STP_XACT_IMMUTABLE);
            }

            Datum datum = SysCacheGetAttr(PROCOID, tp, Anum_pg_proc_prokind, &isNull);
            proIsProcedure = PROC_IS_PRO(CharGetDatum(datum));
            if (proIsProcedure) {
                (reinterpret_cast<FuncExprState*>(setexpr))->prokind = 'p';
            } else {
                (reinterpret_cast<FuncExprState*>(setexpr))->prokind = 'f';
            }
            /* if proIsProcedure means it was a stored procedure */
            u_sess->SPI_cxt.is_stp = savedIsSTP;
            if (!heap_attisnull(tp, Anum_pg_proc_proconfig, NULL) || u_sess->SPI_cxt.is_proconfig_set) {
                u_sess->SPI_cxt.is_proconfig_set = true;
                node->atomic = true;
                stp_set_commit_rollback_err_msg(STP_XACT_GUC_IN_OPT_CLAUSE);
            }
            ReleaseSysCache(tp);
        } else {
            proIsProcedure = PROC_IS_PRO(prokind);
            u_sess->SPI_cxt.is_stp = savedIsSTP;
        }
    }

    callerContext = CurrentMemoryContext;

    funcrettype = exprType((Node*)setexpr->expr);

    returnsTuple = type_is_rowtype(funcrettype);
    econtext->plpgsql_estate = plpgsql_estate;
    plpgsql_estate = NULL;

    /*
     * Prepare a resultinfo node for communication.  We always do this even if
     * not expecting a set result, so that we can pass expectedDesc.  In the
     * generic-expression case, the expression doesn't actually get to see the
     * resultinfo, but set it up anyway because we use some of the fields as
     * our own state variables.
     */
    rsinfo.type = T_ReturnSetInfo;
    rsinfo.econtext = econtext;
    rsinfo.expectedDesc = expectedDesc;
    rsinfo.allowedModes = (int)(SFRM_ValuePerCall | SFRM_Materialize | SFRM_Materialize_Preferred);
    if (randomAccess)
        rsinfo.allowedModes |= (int)SFRM_Materialize_Random;
    rsinfo.returnMode = SFRM_ValuePerCall;
    /* isDone is filled below */
    rsinfo.setResult = NULL;
    rsinfo.setDesc = NULL;

    /*
     * Normally the passed expression tree will be a FuncExprState, since the
     * grammar only allows a function call at the top level of a table
     * function reference.	However, if the function doesn't return set then
     * the planner might have replaced the function call via constant-folding
     * or inlining.  So if we see any other kind of expression node, execute
     * it via the general ExecEvalExpr() code; the only difference is that we
     * don't get a chance to pass a special ReturnSetInfo to any functions
     * buried in the expression.
     */
    if (!setexpr->elidedFuncState) {
        ExprDoneCond argDone;

        /*
         * This path is similar to ExecMakeFunctionResult.
         */
        direct_function_call = true;

        /*
         * Initialize function cache if first time through
         */
        if (setexpr->func.fn_oid == InvalidOid) {
            FuncExpr* func = (FuncExpr*)setexpr->expr;
            
            init_sexpr(func->funcid, func->inputcollid, setexpr, econtext->ecxt_per_query_memory, false, false);
        }
        returnsSet = setexpr->func.fn_retset;
        InitFunctionCallInfoData(fcinfo,
            &(setexpr->func),
            list_length(setexpr->args),
            setexpr->fcinfo_data.fncollation,
            (Node*)node,
            (Node*)&rsinfo);

        has_refcursor = func_has_refcursor_args(fcinfo.flinfo->fn_oid, &fcinfo);

        has_out_param = (is_function_with_plpgsql_language_and_outparam(fcinfo.flinfo->fn_oid) != InvalidOid);
        if (u_sess->attr.attr_sql.sql_compatibility == A_FORMAT && has_out_param) {
            returnsTuple = type_is_rowtype(RECORDOID);
        }

        int cursor_return_number = fcinfo.refcursor_data.return_number;
        if (cursor_return_number > 0) {
            /* init returnCursor to store out-args cursor info on FunctionScan context*/
            fcinfo.refcursor_data.returnCursor = (Cursor_Data*)palloc0(sizeof(Cursor_Data) * cursor_return_number);
        } else {
            fcinfo.refcursor_data.returnCursor = NULL;
        }

        if (has_refcursor) {
            /* init argCursor to store in-args cursor info on FunctionScan context*/
            fcinfo.refcursor_data.argCursor = (Cursor_Data*)palloc0(sizeof(Cursor_Data) * fcinfo.nargs);
            var_dno = (int*)palloc0(sizeof(int) * fcinfo.nargs);
            int rc = memset_s(var_dno, sizeof(int) * fcinfo.nargs, -1, sizeof(int) * fcinfo.nargs);
            securec_check(rc, "\0", "\0");
        }

        /*
         * Evaluate the function's argument list.
         *
         * Note: ideally, we'd do this in the per-tuple context, but then the
         * argument values would disappear when we reset the context in the
         * inner loop.	So do it in caller context.  Perhaps we should make a
         * separate context just to hold the evaluated arguments?
         */
        if (has_refcursor)
            argDone = ExecEvalFuncArgs<true>(&fcinfo, setexpr->args, econtext, var_dno);
        else
            argDone = ExecEvalFuncArgs<false>(&fcinfo, setexpr->args, econtext);
        /* We don't allow sets in the arguments of the table function */
        if (argDone != ExprSingleResult)
            ereport(ERROR,
                (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                    errmsg("set-valued function called in context that cannot accept a set")));

        /*
         * If function is strict, and there are any NULL arguments, skip
         * calling the function and act like it returned NULL (or an empty
         * set, in the returns-set case).
         */
        if (setexpr->func.fn_strict) {
            int i;

            for (i = 0; i < fcinfo.nargs; i++) {
                if (fcinfo.argnull[i])
                    goto no_function_result;
            }
        }
    } else {
        /* Treat funcexpr as a generic expression */
        direct_function_call = false;
        InitFunctionCallInfoData(fcinfo, NULL, 0, InvalidOid, (Node*)node, NULL);
    }

    /*
     * Switch to short-lived context for calling the function or expression.
     */
    MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);

    /*
     * Loop to handle the ValuePerCall protocol (which is also the same
     * behavior needed in the generic ExecEvalExpr path).
     */
    for (;;) {
        Datum result;

        CHECK_FOR_INTERRUPTS();

        /*
         * reset per-tuple memory context before each call of the function or
         * expression. This cleans up any local memory the function may leak
         * when called.
         */
        ResetExprContext(econtext);

        /* Call the function or expression one time */
        if (direct_function_call) {
            pgstat_init_function_usage(&fcinfo, &fcusage);

            fcinfo.isnull = false;
            rsinfo.isDone = ExprSingleResult;
            result = FunctionCallInvoke(&fcinfo);

            if (econtext->plpgsql_estate != NULL) {
                PLpgSQL_execstate* estate = econtext->plpgsql_estate;
                bool isVaildReturn = (fcinfo.refcursor_data.return_number > 0 &&
                    estate->cursor_return_data != NULL && fcinfo.refcursor_data.returnCursor != NULL);
                if (isVaildReturn) {
                    bool isVaildReturnNum = (fcinfo.refcursor_data.return_number > estate->cursor_return_numbers);
                    if (isVaildReturnNum) {
                        pgstat_end_function_usage(&fcusage, rsinfo.isDone != ExprMultipleResult);
                        ereport(ERROR, (errcode(ERRCODE_INVALID_PARAMETER_VALUE), errmodule(MOD_PLSQL),
                            errmsg("The expected output of the cursor:%d and function:%d does not match",
                            estate->cursor_return_numbers, fcinfo.refcursor_data.return_number)));
                    }
                    for (int i = 0; i < fcinfo.refcursor_data.return_number; i++) {
                        CopyCursorInfoData(&estate->cursor_return_data[i], &fcinfo.refcursor_data.returnCursor[i]);
                    }
                }

                if (var_dno != NULL) {
                    for (int i = 0; i < fcinfo.nargs; i++) {
                        if (var_dno[i] >= 0) {
                            int dno = var_dno[i];
                            Cursor_Data* cursor_data = &fcinfo.refcursor_data.argCursor[i];
                            PLpgSQL_execstate* execstate = econtext->plpgsql_estate;
#ifdef USE_ASSERT_CHECKING
                            PLpgSQL_datum* datum = execstate->datums[dno];
#endif
                            Assert(datum->dtype == PLPGSQL_DTYPE_VAR);
                            Assert(((PLpgSQL_var*)datum)->datatype->typoid == REFCURSOROID);

                            ExecCopyDataToDatum(execstate->datums, dno, cursor_data);
                        }
                    }
                }
            }

            pgstat_end_function_usage(&fcusage, rsinfo.isDone != ExprMultipleResult);
        } else {
            result = ExecEvalExpr(setexpr->elidedFuncState, econtext, &fcinfo.isnull);
        }

        /* Which protocol does function want to use? */
        if (rsinfo.returnMode == SFRM_ValuePerCall) {
            /*
             * Check for end of result set.
             */
            if (rsinfo.isDone == ExprEndResult) {
                break;
            }

            /*
             * Can't do anything very useful with NULL rowtype values. For a
             * function returning set, we consider this a protocol violation
             * (but another alternative would be to just ignore the result and
             * "continue" to get another row).	For a function not returning
             * set, we fall out of the loop; we'll cons up an all-nulls result
             * row below.
             */
            if (returnsTuple && fcinfo.isnull && !has_out_param) {
                if (!returnsSet) {
                    break;
                }
                ereport(ERROR,
                    (errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED),
                        errmsg("function returning set of rows cannot return null value")));
            }

            /*
             * If first time through, build tupdesc and tuplestore for result
             */
            if (first_time) {
                oldcontext = MemoryContextSwitchTo(econtext->ecxt_per_query_memory);
                if (returnsTuple) {
                    /*
                     * Use the type info embedded in the rowtype Datum to look
                     * up the needed tupdesc.  Make a copy for the query.
                     */
                    HeapTupleHeader td;

                    td = DatumGetHeapTupleHeader(result);
                    if (IsA(setexpr->expr, Const)) {
                        tupdesc = lookup_rowtype_tupdesc_copy(
                            ((Const*)setexpr->expr)->consttype, HeapTupleHeaderGetTypMod(td));
                    } else {
                        tupdesc =
                            lookup_rowtype_tupdesc_copy(HeapTupleHeaderGetTypeId(td), HeapTupleHeaderGetTypMod(td));
                    }
                } else {
                    /*
                     * Scalar type, so make a single-column descriptor
                     */
                    tupdesc = CreateTemplateTupleDesc(1, false, TAM_HEAP);
                    TupleDescInitEntry(tupdesc, (AttrNumber)1, "column", funcrettype, -1, 0);
                }
                tupstore = tuplestore_begin_heap(randomAccess, false, u_sess->attr.attr_memory.work_mem);
                MemoryContextSwitchTo(oldcontext);
                rsinfo.setResult = tupstore;
                rsinfo.setDesc = tupdesc;
            }

            /*
             * Store current resultset item.
             */
            if (returnsTuple) {
                HeapTupleHeader td;

                td = DatumGetHeapTupleHeader(result);

                /*
                 * Verify all returned rows have same subtype; necessary in
                 * case the type is RECORD.
                 */
                if ((HeapTupleHeaderGetTypeId(td) != tupdesc->tdtypeid ||
                        HeapTupleHeaderGetTypMod(td) != tupdesc->tdtypmod) &&
                    nodeTag(setexpr->expr) != T_Const) {
                        ereport(ERROR,
                            (errcode(ERRCODE_DATATYPE_MISMATCH),
                                errmsg("rows returned by function are not all of the same row type"),
                                errdetail("return type id %u, tuple decription id %u, return typmod %d  "
                                          "tuple decription, typmod %d",
                                    HeapTupleHeaderGetTypeId(td),
                                    tupdesc->tdtypeid,
                                    HeapTupleHeaderGetTypMod(td),
                                    tupdesc->tdtypmod)));
                    }

                /*
                 * tuplestore_puttuple needs a HeapTuple not a bare
                 * HeapTupleHeader, but it doesn't need all the fields.
                 */
                tmptup.t_len = HeapTupleHeaderGetDatumLength(td);
                tmptup.t_data = td;

                tuplestore_puttuple(tupstore, &tmptup);
            } else {
                tuplestore_putvalues(tupstore, tupdesc, &result, &fcinfo.isnull);
            }

            /*
             * Are we done?
             */
            if (rsinfo.isDone != ExprMultipleResult) {
                break;
            }
        } else if (rsinfo.returnMode == SFRM_Materialize) {
            /* check we're on the same page as the function author */
            if (!first_time || rsinfo.isDone != ExprSingleResult) {
                ereport(ERROR,
                    (errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
                        errmsg("table-function protocol for materialize mode was not followed")));
            }
            /* Done evaluating the set result */
            break;
        } else {
            ereport(ERROR,
                (errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
                    errmsg("unrecognized table-function returnMode: %d", (int)rsinfo.returnMode)));
        }

        first_time = false;
    }

no_function_result:

    /*
     * If we got nothing from the function (ie, an empty-set or NULL result),
     * we have to create the tuplestore to return, and if it's a
     * non-set-returning function then insert a single all-nulls row.
     */
    if (rsinfo.setResult == NULL) {
        MemoryContextSwitchTo(econtext->ecxt_per_query_memory);
        tupstore = tuplestore_begin_heap(randomAccess, false, u_sess->attr.attr_memory.work_mem);
        rsinfo.setResult = tupstore;
        if (!returnsSet) {
            int natts = expectedDesc->natts;
            Datum* nulldatums = NULL;
            bool* nullflags = NULL;
            errno_t rc = EOK;

            MemoryContextSwitchTo(econtext->ecxt_per_tuple_memory);
            nulldatums = (Datum*)palloc0(natts * sizeof(Datum));
            nullflags = (bool*)palloc(natts * sizeof(bool));
            rc = memset_s(nullflags, natts * sizeof(bool), true, natts * sizeof(bool));
            securec_check(rc, "\0", "\0");
            MemoryContextSwitchTo(econtext->ecxt_per_query_memory);
            tuplestore_putvalues(tupstore, expectedDesc, nulldatums, nullflags);
        }
    }

    /*
     * If function provided a tupdesc, cross-check it.	We only really need to
     * do this for functions returning RECORD, but might as well do it always.
     */
    if (rsinfo.setDesc) {
        tupledesc_match(expectedDesc, rsinfo.setDesc);

        /*
         * If it is a dynamically-allocated TupleDesc, free it: it is
         * typically allocated in a per-query context, so we must avoid
         * leaking it across multiple usages.
         */
        if (rsinfo.setDesc->tdrefcount == -1)
            FreeTupleDesc(rsinfo.setDesc);
    }

    MemoryContextSwitchTo(callerContext);
    econtext->plpgsql_estate = NULL;

    if (has_refcursor) {
        if (fcinfo.refcursor_data.argCursor != NULL)
            pfree_ext(fcinfo.refcursor_data.argCursor);
        if (fcinfo.refcursor_data.returnCursor != NULL)
            pfree_ext(fcinfo.refcursor_data.returnCursor);
        if (var_dno != NULL)
            pfree_ext(var_dno);
    }

    /* reset the u_sess->SPI_cxt.is_stp, u_sess->SPI_cxt.is_proconfig_set 
       and error message value */
    u_sess->SPI_cxt.is_stp = savedIsSTP;
    u_sess->SPI_cxt.is_proconfig_set = savedProConfigIsSet;
    if (needResetErrMsg) {
        stp_reset_commit_rolback_err_msg();
    }

    /* All done, pass back the tuplestore */
    return rsinfo.setResult;
}

/*
 * Check that function result tuple type (src_tupdesc) matches or can
 * be considered to match what the query expects (dst_tupdesc). If
 * they don't match, ereport.
 *
 * We really only care about number of attributes and data type.
 * Also, we can ignore type mismatch on columns that are dropped in the
 * destination type, so long as the physical storage matches.  This is
 * helpful in some cases involving out-of-date cached plans.
 */
static void tupledesc_match(TupleDesc dst_tupdesc, TupleDesc src_tupdesc)
{
    int i;

    if (dst_tupdesc->natts != src_tupdesc->natts)
        ereport(ERROR,
            (errcode(ERRCODE_DATATYPE_MISMATCH),
                errmsg("function return row and query-specified return row do not match"),
                errdetail_plural("Returned row contains %d attribute, but query expects %d.",
                    "Returned row contains %d attributes, but query expects %d.",
                    src_tupdesc->natts,
                    src_tupdesc->natts,
                    dst_tupdesc->natts)));

    for (i = 0; i < dst_tupdesc->natts; i++) {
        Form_pg_attribute dattr = dst_tupdesc->attrs[i];
        Form_pg_attribute sattr = src_tupdesc->attrs[i];

        if (IsBinaryCoercible(sattr->atttypid, dattr->atttypid))
            continue; /* no worries */
        if (!dattr->attisdropped)
            ereport(ERROR,
                (errcode(ERRCODE_DATATYPE_MISMATCH),
                    errmsg("function return row and query-specified return row do not match"),
                    errdetail("Returned type %s at ordinal position %d, but query expects %s.",
                        format_type_be(sattr->atttypid),
                        i + 1,
                        format_type_be(dattr->atttypid))));

        if (dattr->attlen != sattr->attlen || dattr->attalign != sattr->attalign)
            ereport(ERROR,
                (errcode(ERRCODE_DATATYPE_MISMATCH),
                    errmsg("function return row and query-specified return row do not match"),
                    errdetail("Physical storage mismatch on dropped attribute at ordinal position %d.", i + 1)));
    }
}

void initExecTableOfIndexInfo(ExecTableOfIndexInfo* execTableOfIndexInfo, ExprContext* econtext)
{
    execTableOfIndexInfo->econtext = econtext;
    execTableOfIndexInfo->tableOfIndex = NULL;
    execTableOfIndexInfo->tableOfIndexType = InvalidOid;
    execTableOfIndexInfo->isnestedtable = false;
    execTableOfIndexInfo->tableOfLayers = 0;
    execTableOfIndexInfo->paramid = -1;
    execTableOfIndexInfo->paramtype = InvalidOid;
}

/*
 * Evaluate arguments for a function.
 */
template <bool has_refcursor>
static ExprDoneCond ExecEvalFuncArgs(
    FunctionCallInfo fcinfo, List* argList, ExprContext* econtext, int* plpgsql_var_dno)
{
    ExprDoneCond argIsDone;
    int i;
    ListCell *arg;

    argIsDone = ExprSingleResult; /* default assumption */

    i = 0;
    econtext->is_cursor = false;
    u_sess->plsql_cxt.func_tableof_index = NIL;
    bool is_have_huge_clob = false;

    foreach (arg, argList) {
        ExprState *argstate = (ExprState *)lfirst(arg);

        if (has_refcursor && argstate->resultType == REFCURSOROID)
            econtext->is_cursor = true;

        fcinfo->arg[i] = ExecEvalExpr(argstate, econtext, &fcinfo->argnull[i]);
        ExecTableOfIndexInfo execTableOfIndexInfo;
        initExecTableOfIndexInfo(&execTableOfIndexInfo, econtext);
        ExecEvalParamExternTableOfIndex((Node*)argstate->expr, &execTableOfIndexInfo);
        if (execTableOfIndexInfo.tableOfIndex != NULL) {
            MemoryContext oldCxt = MemoryContextSwitchTo(SESS_GET_MEM_CXT_GROUP(MEMORY_CONTEXT_OPTIMIZER));
            PLpgSQL_func_tableof_index* func_tableof =
                (PLpgSQL_func_tableof_index*)palloc0(sizeof(PLpgSQL_func_tableof_index));
            func_tableof->varno = i;
            func_tableof->tableOfIndexType = execTableOfIndexInfo.tableOfIndexType;
            func_tableof->tableOfIndex = copyTableOfIndex(execTableOfIndexInfo.tableOfIndex);
            u_sess->plsql_cxt.func_tableof_index = lappend(u_sess->plsql_cxt.func_tableof_index, func_tableof);
            MemoryContextSwitchTo(oldCxt);
        }

        if (has_refcursor && econtext->is_cursor && plpgsql_var_dno != NULL) {
            plpgsql_var_dno[i] = econtext->dno;
            CopyCursorInfoData(&fcinfo->refcursor_data.argCursor[i], &econtext->cursor_data);
        }
        fcinfo->argTypes[i] = argstate->resultType;
        econtext->is_cursor = false;
        if (is_huge_clob(fcinfo->argTypes[i], fcinfo->argnull[i], fcinfo->arg[i])) {
            is_have_huge_clob = true;
        }
        i++;
    }
    check_huge_clob_paramter(fcinfo, is_have_huge_clob);

    Assert(i == fcinfo->nargs);

    return argIsDone;
}

/*
 * init_sexpr - initialize a SetExprState node during first use
 */
static void init_sexpr(Oid foid, Oid input_collation, SetExprState *sexpr, MemoryContext sexprCxt, bool allowSRF,
                       bool needDescForSRF)
{
    AclResult aclresult;

    /* Check permission to call function */
    aclresult = pg_proc_aclcheck(foid, GetUserId(), ACL_EXECUTE);
    if (aclresult != ACLCHECK_OK)
        aclcheck_error(aclresult, ACL_KIND_PROC, get_func_name(foid));
    InvokeFunctionExecuteHook(foid);

    /*
     * Safety check on nargs.  Under normal circumstances this should never
     * fail, as parser should check sooner.  But possibly it might fail if
     * server has been compiled with FUNC_MAX_ARGS smaller than some functions
     * declared in pg_proc?
     */
    if (list_length(sexpr->args) > FUNC_MAX_ARGS)
        ereport(ERROR,
                (errcode(ERRCODE_TOO_MANY_ARGUMENTS),
                 errmsg_plural("cannot pass more than %d argument to a function",
                               "cannot pass more than %d arguments to a function", FUNC_MAX_ARGS, FUNC_MAX_ARGS)));

    /* Set up the primary fmgr lookup information */
    fmgr_info_cxt(foid, &(sexpr->func), sexprCxt);
    fmgr_info_set_expr((Node *)sexpr->expr, &(sexpr->func));

    /* Initialize the function call parameter struct as well */
    InitFunctionCallInfoData(sexpr->fcinfo_data, &(sexpr->func), list_length(sexpr->args), input_collation, NULL, NULL);

    /* If function returns set, check if that's allowed by caller */
    if (sexpr->func.fn_retset && !allowSRF)
        ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED),
                        errmsg("set-valued function called in context that cannot accept a set")));

    /* Otherwise, caller should have marked the sexpr correctly */
    Assert(sexpr->func.fn_retset == sexpr->funcReturnsSet);

    /* If function returns set, prepare expected tuple descriptor */
    if (sexpr->func.fn_retset && needDescForSRF) {
        TypeFuncClass functypclass;
        Oid funcrettype;
        TupleDesc tupdesc;
        MemoryContext oldcontext;

        functypclass = get_expr_result_type(sexpr->func.fn_expr, &funcrettype, &tupdesc);

        /* Must save tupdesc in sexpr's context */
        oldcontext = MemoryContextSwitchTo(sexprCxt);

        if (functypclass == TYPEFUNC_COMPOSITE) {
            /* Composite data type, e.g. a table's row type */
            Assert(tupdesc);
            /* Must copy it out of typcache for safety */
            sexpr->funcResultDesc = CreateTupleDescCopy(tupdesc);
            sexpr->funcReturnsTuple = true;
        } else if (functypclass == TYPEFUNC_SCALAR) {
            /* Base data type, i.e. scalar */
            tupdesc = CreateTemplateTupleDesc(1, false);
            TupleDescInitEntry(tupdesc, (AttrNumber)1, NULL, funcrettype, -1, 0);
            sexpr->funcResultDesc = tupdesc;
            sexpr->funcReturnsTuple = false;
        } else if (functypclass == TYPEFUNC_RECORD) {
            /* This will work if function doesn't need an expectedDesc */
            sexpr->funcResultDesc = NULL;
            sexpr->funcReturnsTuple = true;
        } else {
            /* Else, we will fail if function needs an expectedDesc */
            sexpr->funcResultDesc = NULL;
        }

        MemoryContextSwitchTo(oldcontext);
    } else
        sexpr->funcResultDesc = NULL;

    /* Initialize additional state */
    sexpr->funcResultStore = NULL;
    sexpr->funcResultSlot = NULL;
    sexpr->shutdown_reg = false;
}

/*
 * callback function in case a SetExprState needs to be shut down before it
 * has been run to completion
 */
static void ShutdownSetExpr(Datum arg)
{
    SetExprState *sexpr = castNode(SetExprState, DatumGetPointer(arg));

    /* If we have a slot, make sure it's let go of any tuplestore pointer */
    if (sexpr->funcResultSlot)
        ExecClearTuple(sexpr->funcResultSlot);

    /* Release any open tuplestore */
    if (sexpr->funcResultStore)
        tuplestore_end(sexpr->funcResultStore);
    sexpr->funcResultStore = NULL;

    /* Clear any active set-argument state */
    sexpr->setArgsValid = false;

    /* execUtils will deregister the callback... */
    sexpr->shutdown_reg = false;
}

/*
 *		ExecPrepareTuplestoreResult
 *
 * Subroutine for ExecMakeFunctionResultSet: prepare to extract rows from a
 * tuplestore function result.  We must set up a funcResultSlot (unless
 * already done in a previous call cycle) and verify that the function
 * returned the expected tuple descriptor.
 */
static void ExecPrepareTuplestoreResult(SetExprState *sexpr, ExprContext *econtext, Tuplestorestate *resultStore,
                                        TupleDesc resultDesc)
{
    sexpr->funcResultStore = resultStore;

    if (sexpr->funcResultSlot == NULL) {
        /* Create a slot so we can read data out of the tuplestore */
        TupleDesc slotDesc;
        MemoryContext oldcontext;

        oldcontext = MemoryContextSwitchTo(sexpr->func.fn_mcxt);

        /*
         * If we were not able to determine the result rowtype from context,
         * and the function didn't return a tupdesc, we have to fail.
         */
        if (sexpr->funcResultDesc)
            slotDesc = sexpr->funcResultDesc;
        else if (resultDesc) {
            /* don't assume resultDesc is long-lived */
            slotDesc = CreateTupleDescCopy(resultDesc);
        } else {
            ereport(ERROR, (errcode(ERRCODE_FEATURE_NOT_SUPPORTED), errmsg("function returning setof record called in "
                                                                           "context that cannot accept type record")));
            slotDesc = NULL; /* keep compiler quiet */
        }

        sexpr->funcResultSlot = MakeSingleTupleTableSlot(slotDesc);
        MemoryContextSwitchTo(oldcontext);
    }

    /*
     * If function provided a tupdesc, cross-check it.  We only really need to
     * do this for functions returning RECORD, but might as well do it always.
     */
    if (resultDesc) {
        if (sexpr->funcResultDesc)
            tupledesc_match(sexpr->funcResultDesc, resultDesc);

        /*
         * If it is a dynamically-allocated TupleDesc, free it: it is
         * typically allocated in a per-query context, so we must avoid
         * leaking it across multiple usages.
         */
        if (resultDesc->tdrefcount == -1)
            FreeTupleDesc(resultDesc);
    }

    /* Register cleanup callback if we didn't already */
    if (!sexpr->shutdown_reg) {
        RegisterExprContextCallback(econtext, ShutdownSetExpr, PointerGetDatum(sexpr));
        sexpr->shutdown_reg = true;
    }
}

/*
 *		ExecMakeFunctionResultSet
 *
 * Evaluate the arguments to a set-returning function and then call the
 * function itself.  The argument expressions may not contain set-returning
 * functions (the planner is supposed to have separated evaluation for those).
 *
 * This should be called in a short-lived (per-tuple) context, argContext
 * needs to live until all rows have been returned (i.e. *isDone set to
 * ExprEndResult or ExprSingleResult).
 *
 * This is used by nodeProjectSet.c.
 */
Datum ExecMakeFunctionResultSet(SetExprState *fcache, ExprContext *econtext, MemoryContext argContext, 
                                bool *isNull, ExprDoneCond *isDone)
{
	List	   *arguments;
	Datum		result;
	FunctionCallInfo fcinfo;
	PgStat_FunctionCallUsage fcusage;
	ReturnSetInfo rsinfo;
	bool		callit;
	int			i;
    int* var_dno = NULL;
    bool has_refcursor = fcache->has_refcursor;
    int has_cursor_return = !!fcache->fcinfo_data.refcursor_data.return_number;

restart:

	/* Guard against stack overflow due to overly complex expressions */
	check_stack_depth();

	/*
	 * If a previous call of the function returned a set result in the form of
	 * a tuplestore, continue reading rows from the tuplestore until it's
	 * empty.
	 */
	if (fcache->funcResultStore)
	{
        TupleTableSlot *slot = fcache->funcResultSlot;
        MemoryContext oldContext;
        bool foundTup;
        /* it was provided before ... */
        if (unlikely(isDone == NULL)) {
            ereport(ERROR, (errcode(ERRCODE_NULL_VALUE_NOT_ALLOWED),
                    errmsg("set-valued function called in context that cannot accept a set")));
        }

        /*
         * Have to make sure tuple in slot lives long enough, otherwise
         * clearing the slot could end up trying to free something already
         * freed.
         */
        oldContext = MemoryContextSwitchTo(slot->tts_mcxt);
        foundTup = tuplestore_gettupleslot(fcache->funcResultStore, true, false, fcache->funcResultSlot);
        MemoryContextSwitchTo(oldContext);

        if (foundTup) {
            *isDone = ExprMultipleResult;
            if (fcache->funcReturnsTuple) {
                /* We must return the whole tuple as a Datum. */
                *isNull = false;
                return ExecFetchSlotTupleDatum(fcache->funcResultSlot);
            } else {
                /* Extract the first column and return it as a scalar. */
                Assert(fcache->funcResultSlot != NULL);
                /* Get the Table Accessor Method*/
                return tableam_tslot_getattr(fcache->funcResultSlot, 1, isNull);
            }
        }

        /* Exhausted the tuplestore, so clean up */
		tuplestore_end(fcache->funcResultStore);
		fcache->funcResultStore = NULL;
		*isDone = ExprEndResult;
		*isNull = true;
		return (Datum) 0;
	}

    /*
     * arguments is a list of expressions to evaluate before passing to the
     * function manager.  We skip the evaluation if it was already done in the
     * previous call (ie, we are continuing the evaluation of a set-valued
     * function).  Otherwise, collect the current argument values into fcinfo.
     */
    fcinfo = &fcache->fcinfo_data;

    if (has_cursor_return) {
        /* init returnCursor to store out-args cursor info on ExprContext*/
        fcinfo->refcursor_data.returnCursor =
            (Cursor_Data*)palloc0(sizeof(Cursor_Data) * fcinfo->refcursor_data.return_number);
    } else {
        fcinfo->refcursor_data.returnCursor = NULL;
    }

    if (has_refcursor) {
        /* init argCursor to store in-args cursor info on ExprContext*/
        fcinfo->refcursor_data.argCursor = (Cursor_Data*)palloc0(sizeof(Cursor_Data) * fcinfo->nargs);
        var_dno = (int*)palloc0(sizeof(int) * fcinfo->nargs);
        for (i = 0; i < fcinfo->nargs; i++) {
            var_dno[i] = -1;
        }
    }

	arguments = fcache->args;
    /*
     * The arguments have to live in a context that lives at least until all
     * rows from this SRF have been returned, otherwise ValuePerCall SRFs
     * would reference freed memory after the first returned row.
     */
    if (!fcache->setArgsValid) { 
        MemoryContext oldContext = MemoryContextSwitchTo(argContext);
        if (has_refcursor)
            ExecEvalFuncArgs<true>(fcinfo, arguments, econtext, var_dno);
        else
            ExecEvalFuncArgs<false>(fcinfo, arguments, econtext);
        MemoryContextSwitchTo(oldContext);
    }
	else
	{
		/* Reset flag (we may set it again below) */
		fcache->setArgsValid = false;
	}

	/*
	 * Now call the function, passing the evaluated parameter values.
	 */

	/* Prepare a resultinfo node for communication. */
	fcinfo->resultinfo = (Node *) &rsinfo;
	rsinfo.type = T_ReturnSetInfo;
	rsinfo.econtext = econtext;
	rsinfo.expectedDesc = fcache->funcResultDesc;
	rsinfo.allowedModes = (int) (SFRM_ValuePerCall | SFRM_Materialize);
	/* note we do not set SFRM_Materialize_Random or _Preferred */
	rsinfo.returnMode = SFRM_ValuePerCall;
	/* isDone is filled below */
	rsinfo.setResult = NULL;
	rsinfo.setDesc = NULL;

	/*
	 * If function is strict, and there are any NULL arguments, skip calling
	 * the function.
	 */
	callit = true;
	if (fcache->func.fn_strict) {
		for (i = 0; i < fcinfo->nargs; i++) {
			if (fcinfo->argnull[i]) {
				callit = false;
				break;
			}
		}
	}

	if (callit)
	{
		pgstat_init_function_usage(fcinfo, &fcusage);

		fcinfo->isnull = false;
		rsinfo.isDone = ExprSingleResult;
		result = FunctionCallInvoke(fcinfo);
		*isNull = fcinfo->isnull;
		*isDone = rsinfo.isDone;

		pgstat_end_function_usage(&fcusage, rsinfo.isDone != ExprMultipleResult);
	}
	else
	{
		/* for a strict SRF, result for NULL is an empty set */
		result = (Datum) 0;
		*isNull = true;
		*isDone = ExprEndResult;
	}

    if (has_refcursor && econtext->plpgsql_estate != NULL) {
        PLpgSQL_execstate* estate = econtext->plpgsql_estate;
        /* copy in-args cursor option info */
        for (i = 0; i < fcinfo->nargs; i++) {
            if (var_dno[i] >= 0) {
                int dno = var_dno[i];
                Cursor_Data* cursor_data = &fcinfo->refcursor_data.argCursor[i];
#ifdef USE_ASSERT_CHECKING
                PLpgSQL_datum* datum = estate->datums[dno];
#endif
                Assert(datum->dtype == PLPGSQL_DTYPE_VAR);
                Assert(((PLpgSQL_var*)datum)->datatype->typoid == REFCURSOROID);

                ExecCopyDataToDatum(estate->datums, dno, cursor_data);
            }
        }

        if (fcinfo->refcursor_data.return_number > 0) {
            /* copy function returns cursor option info.
             * for simple expr in exec_eval_expr, we can not get the result type,
             * so cursor_return_data mallocs here.
             */
            if (estate->cursor_return_data == NULL && estate->tuple_store_cxt != NULL) {
                MemoryContext oldcontext = MemoryContextSwitchTo(estate->tuple_store_cxt);
                estate->cursor_return_data =
                    (Cursor_Data*)palloc0(sizeof(Cursor_Data) * fcinfo->refcursor_data.return_number);
                estate->cursor_return_numbers = fcinfo->refcursor_data.return_number;
                (void)MemoryContextSwitchTo(oldcontext);
            }

            if (estate->cursor_return_data != NULL) {
                for (i = 0; i < fcinfo->refcursor_data.return_number; i++) {
                    int rc = memcpy_s(&estate->cursor_return_data[i], sizeof(Cursor_Data),
                        &fcinfo->refcursor_data.returnCursor[i], sizeof(Cursor_Data));
                    securec_check(rc, "\0", "\0");
                }
            }
        }
    }

	/* Which protocol does function want to use? */
	if (rsinfo.returnMode == SFRM_ValuePerCall)
	{
		if (*isDone != ExprEndResult)
		{
			/*
			 * Save the current argument values to re-use on the next call.
			 */
			if (*isDone == ExprMultipleResult)
			{
				fcache->setArgsValid = true;
				/* Register cleanup callback if we didn't already */
				if (!fcache->shutdown_reg)
				{
					RegisterExprContextCallback(econtext,
												ShutdownSetExpr,
												PointerGetDatum(fcache));
					fcache->shutdown_reg = true;
				}
			}
		}
	}
	else if (rsinfo.returnMode == SFRM_Materialize)
	{
		/* check we're on the same page as the function author */
		if (rsinfo.isDone != ExprSingleResult)
			ereport(ERROR,
					(errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
					 errmsg("table-function protocol for materialize mode was not followed")));
		if (rsinfo.setResult != NULL)
		{
			/* prepare to return values from the tuplestore */
			ExecPrepareTuplestoreResult(fcache, econtext,
										rsinfo.setResult,
										rsinfo.setDesc);
			/* loop back to top to start returning from tuplestore */
			goto restart;
		}
		/* if setResult was left null, treat it as empty set */
		*isDone = ExprEndResult;
		*isNull = true;
		result = (Datum) 0;
	}
	else
		ereport(ERROR,
				(errcode(ERRCODE_E_R_I_E_SRF_PROTOCOL_VIOLATED),
				 errmsg("unrecognized table-function returnMode: %d",
						(int) rsinfo.returnMode)));

    if (has_refcursor) {
        pfree_ext(fcinfo->refcursor_data.argCursor);
        pfree_ext(var_dno);
    }

    set_result_for_plpgsql_language_function_with_outparam(fcinfo->flinfo->fn_oid, &result, isNull);

	return result;
}

/*
 * Prepare targetlist SRF function call for execution.
 *
 * This is used by nodeProjectSet.c.
 */
SetExprState *ExecInitFunctionResultSet(Expr *expr, ExprContext *econtext, PlanState *parent)
{
    SetExprState *state = makeNode(SetExprState);

    state->funcReturnsSet = true;
    state->expr = expr;
    state->func.fn_oid = InvalidOid;

    /*
     * Initialize metadata.  The expression node could be either a FuncExpr or
     * an OpExpr.
     */
    if (IsA(expr, FuncExpr)) {
        FuncExpr *func = (FuncExpr *)expr;

        state->args = ExecInitExprList(func->args, parent);
        init_sexpr(func->funcid, func->inputcollid, state, econtext->ecxt_per_query_memory, true, true);
    } else if (IsA(expr, OpExpr)) {
        OpExpr *op = (OpExpr *)expr;

        state->args = ExecInitExprList(op->args, parent);
        init_sexpr(op->opfuncid, op->inputcollid, state, econtext->ecxt_per_query_memory, true, true);
    } else
        elog(ERROR, "unrecognized node type: %d", (int)nodeTag(expr));

    /* shouldn't get here unless the selected function returns set */
    Assert(state->func.fn_retset);

    state->has_refcursor = func_has_refcursor_args(state->func.fn_oid, &state->fcinfo_data);
    return state;
}