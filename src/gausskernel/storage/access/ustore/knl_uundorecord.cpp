/* -------------------------------------------------------------------------
 *
 * knl_uundorecord.cpp
 *     c++ code
 *
 * Portions Copyright (c) 2020 Huawei Technologies Co.,Ltd.
 * Portions Copyright (c) 1996-2012, PostgreSQL Global Development Group
 * Portions Copyright (c) 1994, Regents of the University of California
 *
 *
 * IDENTIFICATION
 * src/gausskernel/storage/access/ustore/knl_uundorecord.cpp
 *
 * -------------------------------------------------------------------------
 */

#include "access/ustore/knl_uundorecord.h"

#include "access/ustore/undo/knl_uundoapi.h"
#include "access/heapam.h"
#include "pgstat.h"
#include "storage/buf/bufmgr.h"

namespace {
const UndoRecordSize UNDO_RECORD_FIX_SIZE = SIZE_OF_UNDO_RECORD_HEADER + SIZE_OF_UNDO_RECORD_BLOCK;

bool InsertUndoBytes(_in_ const char *srcptr, _in_ int srclen, __inout char **writeptr, _in_ const char *endptr,
    __inout int *myBytesWritten, __inout int *alreadyWritten)
{
    if (*myBytesWritten >= srclen) {
        *myBytesWritten -= srclen;
        return true;
    }

    int remaining = srclen - *myBytesWritten;
    int maxWriteOnCurrPage = endptr - *writeptr;
    int canWrite = Min(remaining, maxWriteOnCurrPage);

    if (canWrite == 0) {
        return false;
    }

    errno_t rc = memcpy_s(*writeptr, maxWriteOnCurrPage, srcptr + *myBytesWritten, canWrite);
    securec_check(rc, "\0", "\0");

    *writeptr += canWrite;
    *alreadyWritten += canWrite;
    *myBytesWritten = 0;

    return (canWrite == remaining);
}

bool ReadUndoBytes(_in_ char *destptr, _in_ int destlen, __inout char **readeptr, _in_ const char *endptr,
    __inout int *myBytesRead, __inout int *alreadyRead)
{
    if (*myBytesRead >= destlen) {
        *myBytesRead -= destlen;
        return true;
    }

    int remaining = destlen - *myBytesRead;
    int maxReadOnCurrPage = endptr - *readeptr;
    int canRead = Min(remaining, maxReadOnCurrPage);

    if (canRead == 0) {
        return false;
    }

    errno_t rc = memcpy_s(destptr + *myBytesRead, remaining, *readeptr, canRead);
    securec_check(rc, "\0", "\0");

    *readeptr += canRead;
    *alreadyRead += canRead;
    *myBytesRead = 0;

    return (canRead == remaining);
}
} // namespace

UndoRecord::UndoRecord()
{
    whdr_.Init2DefVal();
    wblk_.Init2DefVal();
    wtxn_.Init2DefVal();
    wpay_.Init2DefVal();
    wtd_.Init2DefVal();
    wpart_.Init2DefVal();
    wtspc_.Init2DefVal();
    rawdata_.data = NULL;
    rawdata_.len = 0;
    SetUrp(INVALID_UNDO_REC_PTR);
    SetBuff(InvalidBuffer);
    SetBufidx(-1);
    SetNeedInsert(false);
    SetCopy(true);
    SetMemoryContext(NULL);
}

UndoRecord::~UndoRecord()
{
    Reset(INVALID_UNDO_REC_PTR);
    SetMemoryContext(NULL);
}

void UndoRecord::Destroy()
{
    Reset(INVALID_UNDO_REC_PTR);
    SetMemoryContext(NULL);
}

void UndoRecord::Reset(UndoRecPtr urp)
{
    whdr_.Init2DefVal();
    wblk_.Init2DefVal();
    wtxn_.Init2DefVal();
    wpay_.Init2DefVal();
    wtd_.Init2DefVal();
    wpart_.Init2DefVal();
    wtspc_.Init2DefVal();

    if (BufferIsValid(buff_)) {
        if (!IS_VALID_UNDO_REC_PTR(urp) || (UNDO_PTR_GET_ZONE_ID(urp) != UNDO_PTR_GET_ZONE_ID(urp_)) ||
            (UNDO_PTR_GET_BLOCK_NUM(urp) != BufferGetBlockNumber(buff_))) {
            BufferDesc *buf_desc = GetBufferDescriptor(buff_ - 1);
            if (LWLockHeldByMe(buf_desc->content_lock)) {
                ereport(LOG, (errmodule(MOD_UNDO),
                    errmsg("Release Buffer %d when Reset UndoRecord from %lu to %lu.", buff_, urp_, urp)));
                LockBuffer(buff_, BUFFER_LOCK_UNLOCK);
            }
            ReleaseBuffer(buff_);
            buff_ = InvalidBuffer;
        }
    }

    if (IsCopy() && rawdata_.data != NULL) {
        pfree(rawdata_.data);
    }

    rawdata_.data = NULL;
    rawdata_.len = 0;
    SetUrp(urp);
    SetBufidx(-1);
    SetNeedInsert(false);
    SetCopy(true);
}

void UndoRecord::Reset2Blkprev()
{
    Reset(Blkprev());
}

UndoRecordSize UndoRecord::MemoryRecordSize()
{
    return sizeof(UndoRecord) + rawdata_.len;
}

UndoRecordSize UndoRecord::RecordSize()
{
    UndoRecordSize size = UNDO_RECORD_FIX_SIZE + sizeof(UndoRecordSize);
    if ((whdr_.uinfo & UNDO_UREC_INFO_PAYLOAD) != 0) {
        size += SIZE_OF_UNDO_RECORD_PAYLOAD;
        size += rawdata_.len;
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_TRANSAC) != 0) {
        size += SIZE_OF_UNDO_RECORD_TRANSACTION;
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_OLDTD) != 0) {
        size += SIZE_OF_UNDO_RECORD_OLDTD;
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_HAS_PARTOID) != 0) {
        size += SIZE_OF_UNDO_RECORD_PARTITION;
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_HAS_TABLESPACEOID) != 0) {
        size += SIZE_OF_UNDO_RECORD_TABLESPACE;
    }

    return size;
}
UndoRecPtr UndoRecord::Prevurp(UndoRecPtr currUrp, Buffer *buffer)
{
    if (IS_VALID_UNDO_REC_PTR(wtxn_.prevurp)) {
        return wtxn_.prevurp;
    }

    int zoneId = UNDO_PTR_GET_ZONE_ID(currUrp);
    UndoLogOffset offset = UNDO_PTR_GET_OFFSET(currUrp);
    UndoRecordSize prevLen = GetPrevRecordLen(currUrp, buffer);

    ereport(DEBUG5, (errmsg(UNDOFORMAT("Prevurp zid=%d, offset=%lu, prevLen=%u"), zoneId, offset, prevLen)));

    return MAKE_UNDO_PTR(zoneId, offset - prevLen);
}

UndoRecordSize UndoRecord::GetPrevRecordLen(UndoRecPtr currUrp, Buffer *inputBuffer)
{
    Buffer buffer = InvalidBuffer;
    bool releaseBuffer = false;
    BlockNumber blk = UNDO_PTR_GET_BLOCK_NUM(currUrp);
    RelFileNode rnode;
    UNDO_PTR_ASSIGN_REL_FILE_NODE(rnode, currUrp, UNDO_DB_OID);
    UndoRecordSize precRecLen = 0;
    UndoLogOffset pageOffset = UNDO_PTR_GET_PAGE_OFFSET(currUrp);
    Assert(pageOffset != 0);

    if (inputBuffer == NULL || !BufferIsValid(*inputBuffer)) {
        buffer =
            ReadUndoBufferWithoutRelcache(rnode, UNDO_FORKNUM, blk, RBM_NORMAL, NULL, RELPERSISTENCE_PERMANENT);
        releaseBuffer = true;
        LockBuffer(buffer, BUFFER_LOCK_SHARE);
    } else {
        buffer = *inputBuffer;
    }

    char *page = (char *)BufferGetPage(buffer);
    UndoRecordSize byteToRead = sizeof(UndoRecordSize);
    char prevLen[2];

    while (byteToRead > 0) {
        pageOffset -= 1;
        if (pageOffset >= UNDO_LOG_BLOCK_HEADER_SIZE) {
            prevLen[byteToRead - 1] = page[pageOffset];
            byteToRead -= 1;
        } else {
            if (releaseBuffer) {
                if (LWLockHeldByMeInMode(BufferDescriptorGetContentLock(GetBufferDescriptor(buffer - 1)), LW_SHARED)) {
                    LockBuffer(buffer, BUFFER_LOCK_UNLOCK);
                }
                ReleaseBuffer(buffer);
            }
            releaseBuffer = true;
            blk -= 1;
            buffer = ReadUndoBufferWithoutRelcache(rnode, UNDO_FORKNUM, blk, RBM_NORMAL, NULL,
                RELPERSISTENCE_PERMANENT);
            LockBuffer(buffer, BUFFER_LOCK_SHARE);
            pageOffset = BLCKSZ;
            page = (char *)BufferGetPage(buffer);
        }
    }

    precRecLen = *(UndoRecordSize *)(prevLen);

    if (UNDO_PTR_GET_PAGE_OFFSET(currUrp) - UNDO_LOG_BLOCK_HEADER_SIZE < precRecLen) {
        precRecLen += UNDO_LOG_BLOCK_HEADER_SIZE;
    }
    if (releaseBuffer) {
        if (LWLockHeldByMeInMode(BufferDescriptorGetContentLock(GetBufferDescriptor(buffer - 1)), LW_SHARED)) {
            LockBuffer(buffer, BUFFER_LOCK_UNLOCK);
        }
        ReleaseBuffer(buffer);
    }
    if (precRecLen == 0) {
        ereport(PANIC, (errmsg(UNDOFORMAT("Currurp %lu, prevLen=%u"), currUrp, precRecLen)));
    }
    return precRecLen;
}

UndoRecPtr UndoRecord::Prepare(UndoPersistence upersistence, UndoRecPtr *undoPtr)
{
    UndoRecordSize undoSize = RecordSize();
    urp_ = *undoPtr;
    *undoPtr = undo::AdvanceUndoPtr(*undoPtr, undoSize);
    return urp_;
}

bool UndoRecord::Append(_in_ Page page, _in_ int startingByte, __inout int *alreadyWritten, UndoRecordSize undoLen)
{
    Assert(page);

    char *writeptr = (char *)page + startingByte;
    char *endptr = (char *)page + BLCKSZ;
    int myBytesWritten = *alreadyWritten;

    if (!InsertUndoBytes((char *)&whdr_, SIZE_OF_UNDO_RECORD_HEADER, &writeptr, endptr, &myBytesWritten,
        alreadyWritten)) {
        return false;
    }
    if (!InsertUndoBytes((char *)&wblk_, SIZE_OF_UNDO_RECORD_BLOCK, &writeptr, endptr, &myBytesWritten,
        alreadyWritten)) {
        return false;
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_TRANSAC) != 0) {
        if (!InsertUndoBytes((char *)&wtxn_, SIZE_OF_UNDO_RECORD_TRANSACTION, &writeptr, endptr, &myBytesWritten,
            alreadyWritten)) {
            return false;
        }
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_OLDTD) != 0) {
        if (!InsertUndoBytes((char *)&wtd_, SIZE_OF_UNDO_RECORD_OLDTD, &writeptr, endptr, &myBytesWritten,
            alreadyWritten)) {
            return false;
        }
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_HAS_PARTOID) != 0) {
        if (!InsertUndoBytes((char *)&wpart_, SIZE_OF_UNDO_RECORD_PARTITION, &writeptr, endptr, &myBytesWritten,
            alreadyWritten)) {
            return false;
        }
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_HAS_TABLESPACEOID) != 0) {
        if (!InsertUndoBytes((char *)&wtspc_, SIZE_OF_UNDO_RECORD_TABLESPACE, &writeptr, endptr, &myBytesWritten,
            alreadyWritten)) {
            return false;
        }
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_PAYLOAD) != 0) {
        wpay_.payloadlen = rawdata_.len;
        if (!InsertUndoBytes((char *)&wpay_, SIZE_OF_UNDO_RECORD_PAYLOAD, &writeptr, endptr, &myBytesWritten,
            alreadyWritten)) {
            return false;
        }
        if (wpay_.payloadlen > 0 &&
            !InsertUndoBytes((char *)rawdata_.data, rawdata_.len, &writeptr, endptr, &myBytesWritten, alreadyWritten)) {
            return false;
        }
    }
    if (!InsertUndoBytes((char *)&undoLen, sizeof(UndoRecordSize), &writeptr, endptr, &myBytesWritten,
        alreadyWritten)) {
        return false;
    }

    return true;
}

void UndoRecord::CheckBeforAppend()
{
    Assert((wpay_.payloadlen == 0) || (wpay_.payloadlen > 0 && rawdata_.data != NULL));
}

void UndoRecord::Load(bool keepBuffer)
{
    Assert(urp_ != INVALID_UNDO_REC_PTR);

    BlockNumber blk = UNDO_PTR_GET_BLOCK_NUM(urp_);
    Buffer buffer = buff_;
    int startingByte = UNDO_PTR_GET_PAGE_OFFSET(urp_);
    RelFileNode rnode;
    UNDO_PTR_ASSIGN_REL_FILE_NODE(rnode, urp_, UNDO_DB_OID);
    bool isUndoRecSplit = false;
    bool copyData = keepBuffer;

    /* Get Undo Persistence. Stored in the variable upersistence */
    int zoneId = UNDO_PTR_GET_ZONE_ID(urp_);
    if (!BufferIsValid(buffer)) {
#ifdef DEBUG_UHEAP
        UHEAPSTAT_COUNT_UNDO_PAGE_VISITS();
#endif
        buffer =
            ReadUndoBufferWithoutRelcache(rnode, UNDO_FORKNUM, blk, RBM_NORMAL, NULL, RELPERSISTENCE_PERMANENT);
        LockBuffer(buffer, BUFFER_LOCK_SHARE);
        buff_ = buffer;
    } else if (!keepBuffer) {
        LockBuffer(buffer, BUFFER_LOCK_SHARE);
    }

    int alreadyRead = 0;
    do {
        Page page = BufferGetPage(buffer);
        BufferDesc *bufDesc = GetBufferDescriptor(buffer - 1);
        if (bufDesc->tag.blockNum != blk || bufDesc->tag.rnode.dbNode != UNDO_DB_OID ||
            bufDesc->tag.rnode.relNode != (Oid)zoneId) {
            ereport(PANIC,
                (errmsg(UNDOFORMAT("undo buffer desc invalid, bufdesc: dbid=%u, relid=%u, blockno=%u. "
                "expect: dbid=%u, zoneid=%u, blockno=%u."),
                bufDesc->tag.rnode.dbNode, bufDesc->tag.rnode.relNode, bufDesc->tag.blockNum,
                (Oid)UNDO_DB_OID, (Oid)zoneId, blk)));
        }
        if (alreadyRead > BLCKSZ) {
            ereport(PANIC, (errmsg(UNDOFORMAT("undo record exceeds max size, readSize %d."), alreadyRead)));
        }
        if (ReadUndoRecord(page, startingByte, &alreadyRead, copyData)) {
            break;
        }

        startingByte = UNDO_LOG_BLOCK_HEADER_SIZE;
        blk++;
        isUndoRecSplit = true;

        if (!keepBuffer) {
            if (LWLockHeldByMeInMode(BufferDescriptorGetContentLock(GetBufferDescriptor(buffer - 1)), LW_SHARED)) {
                LockBuffer(buffer, BUFFER_LOCK_UNLOCK);
            }
            ReleaseBuffer(buffer);

            buff_ = InvalidBuffer;
        }
#ifdef DEBUG_UHEAP
        UHEAPSTAT_COUNT_UNDO_PAGE_VISITS();
#endif
        buffer =
            ReadUndoBufferWithoutRelcache(rnode, UNDO_FORKNUM, blk, RBM_NORMAL, NULL, RELPERSISTENCE_PERMANENT);
        LockBuffer(buffer, BUFFER_LOCK_SHARE);
    } while (true);

    if (isUndoRecSplit) {
        if (LWLockHeldByMeInMode(BufferDescriptorGetContentLock(GetBufferDescriptor(buffer - 1)), LW_SHARED)) {
            LockBuffer(buffer, BUFFER_LOCK_UNLOCK);
        }
        ReleaseBuffer(buffer);
    } else if (!keepBuffer) {
        if (LWLockHeldByMeInMode(BufferDescriptorGetContentLock(GetBufferDescriptor(buffer - 1)), LW_SHARED)) {
            LockBuffer(buffer, BUFFER_LOCK_UNLOCK);
        }
    }
}

bool UndoRecord::ReadUndoRecord(_in_ Page page, _in_ int startingByte, __inout int *alreadyRead, _in_ bool copyData)
{
    Assert(page);

    char *readptr = (char *)page + startingByte;
    char *endptr = (char *)page + BLCKSZ;
    int myBytesRead = *alreadyRead;
    bool isUndoSplited = myBytesRead > 0 ? true : false;

    if (!ReadUndoBytes((char *)&whdr_, SIZE_OF_UNDO_RECORD_HEADER, &readptr, endptr, &myBytesRead, alreadyRead)) {
        return false;
    }
    if (!ReadUndoBytes((char *)&wblk_, SIZE_OF_UNDO_RECORD_BLOCK, &readptr, endptr, &myBytesRead, alreadyRead)) {
        return false;
    }

    if ((whdr_.uinfo & UNDO_UREC_INFO_TRANSAC) != 0) {
        if (!ReadUndoBytes((char *)&wtxn_, SIZE_OF_UNDO_RECORD_TRANSACTION, &readptr, endptr, &myBytesRead,
            alreadyRead)) {
            return false;
        }
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_OLDTD) != 0) {
        if (!ReadUndoBytes((char *)&wtd_, SIZE_OF_UNDO_RECORD_OLDTD, &readptr, endptr, &myBytesRead, alreadyRead)) {
            return false;
        }
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_HAS_PARTOID) != 0) {
        if (!ReadUndoBytes((char *)&wpart_, SIZE_OF_UNDO_RECORD_PARTITION, &readptr, endptr, &myBytesRead,
            alreadyRead)) {
            return false;
        }
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_HAS_TABLESPACEOID) != 0) {
        if (!ReadUndoBytes((char *)&wtspc_, SIZE_OF_UNDO_RECORD_TABLESPACE, &readptr, endptr, &myBytesRead,
            alreadyRead)) {
            return false;
        }
    }
    if ((whdr_.uinfo & UNDO_UREC_INFO_PAYLOAD) != 0) {
        if (!ReadUndoBytes((char *)&wpay_, SIZE_OF_UNDO_RECORD_PAYLOAD, &readptr, endptr, &myBytesRead, alreadyRead)) {
            return false;
        }

        rawdata_.len = wpay_.payloadlen;
        if (rawdata_.len > 0) {
            if (!copyData && !isUndoSplited && rawdata_.len <= (endptr - readptr)) {
                rawdata_.data = readptr;
                SetCopy(false);
            } else {
                if (rawdata_.len > 0 && rawdata_.data == NULL) {
                    rawdata_.data = (char *)MemoryContextAllocZero(
                        CurrentMemoryContext, rawdata_.len);
                }
                if (!ReadUndoBytes((char *)rawdata_.data, rawdata_.len, &readptr, endptr, &myBytesRead, alreadyRead)) {
                    return false;
                }
            }
        }
    }
    return true;
}

static UndoRecordState LoadUndoRecord(UndoRecord *urec, TransactionId *lastXid)
{
    UndoRecordState state = undo::CheckUndoRecordValid(urec->Urp(), true, lastXid);
    if (state != UNDO_RECORD_NORMAL) {
        return state;
    }

    int saveInterruptHoldoffCount = t_thrd.int_cxt.InterruptHoldoffCount;
    MemoryContext currentContext = CurrentMemoryContext;
    PG_TRY();
    {
        t_thrd.undo_cxt.fetchRecord = true;
        urec->Load(false);
        state = undo::CheckUndoRecordValid(urec->Urp(), true, NULL);
        if (state == UNDO_RECORD_NORMAL) {
            VerifyUndoRecordValid(urec, true);
        }
    }
    PG_CATCH();
    {
        MemoryContext oldContext = MemoryContextSwitchTo(currentContext);
        state = undo::CheckUndoRecordValid(urec->Urp(), true, lastXid);
        t_thrd.undo_cxt.fetchRecord = false;
        if (state == UNDO_RECORD_DISCARD || state == UNDO_RECORD_FORCE_DISCARD) {
            t_thrd.int_cxt.InterruptHoldoffCount = saveInterruptHoldoffCount;
            if (BufferIsValid(urec->Buff())) {
                if (LWLockHeldByMeInMode(BufferDescriptorGetContentLock(
                    GetBufferDescriptor(urec->Buff() - 1)), LW_SHARED)) {
                    LockBuffer(urec->Buff(), BUFFER_LOCK_UNLOCK);
                }
                ReleaseBuffer(urec->Buff());
                urec->SetBuff(InvalidBuffer);
            }
            FlushErrorState();
            return state;
        } else {
            (void)MemoryContextSwitchTo(oldContext);
            PG_RE_THROW();
        }
    }
    PG_END_TRY();
    t_thrd.undo_cxt.fetchRecord = false;
    return state;
}

UndoTraversalState FetchUndoRecord(__inout UndoRecord *urec, _in_ SatisfyUndoRecordCallback callback,
    _in_ BlockNumber blkno, _in_ OffsetNumber offset, _in_ TransactionId xid, bool isNeedBypass,
    TransactionId *lastXid)
{
    int64 undo_chain_len = 0; /* len of undo chain for one tuple */

    Assert(urec);

    if (RecoveryInProgress()) {
        uint64 blockcnt = 0;
        while (undo::CheckUndoRecordValid(urec->Urp(), false, NULL) == UNDO_RECORD_NOT_INSERT) {
            ereport(LOG,
                (errmsg(UNDOFORMAT("urp: %ld is not replayed yet. ROS waiting for UndoRecord replay."),
                urec->Urp())));

            pg_usleep(1000L); /* 1ms */
            if (blockcnt % 1000 == 0) {
                CHECK_FOR_INTERRUPTS();
            }
        }
        if (undo::CheckUndoRecordValid(urec->Urp(), false, NULL) == UNDO_RECORD_DISCARD) {
            return UNDO_TRAVERSAL_END;
        }
    }

    do {
        UndoRecordState state = LoadUndoRecord(urec, lastXid);
        if (state == UNDO_RECORD_DISCARD) {
            return UNDO_TRAVERSAL_END;
        } else if (state == UNDO_RECORD_INVALID) {
            return UNDO_TRAVERSAL_ENDCHAIN;
        } else if (state == UNDO_RECORD_FORCE_DISCARD) {
            return UNDO_TRAVERSAL_ABORT;
        }

        if (isNeedBypass && TransactionIdPrecedes(urec->Xid(), g_instance.undo_cxt.globalFrozenXid)) {
            ereport(DEBUG1, (errmsg(UNDOFORMAT("Check visibility by globalFrozenXid"))));
            return UNDO_TRAVERSAL_STOP;
        }

        ++undo_chain_len;

        if (blkno == InvalidBlockNumber) {
            break;
        }

        if (callback(urec, blkno, offset, xid)) {
            break;
        }

        ereport(DEBUG3, (errmsg(UNDOFORMAT("fetch blkprev undo :%lu, curr undo: %lu"), urec->Blkprev(), urec->Urp())));

        urec->Reset2Blkprev();
    } while (true);

#ifdef DEBUG_UHEAP
    UHEAPSTAT_COUNT_UNDO_CHAIN_VISTIED(undo_chain_len)
#endif
    g_instance.undo_cxt.undoChainTotalSize += undo_chain_len;
    g_instance.undo_cxt.undo_chain_visited_count += 1;
    g_instance.undo_cxt.maxChainSize =
        g_instance.undo_cxt.maxChainSize > undo_chain_len ? g_instance.undo_cxt.maxChainSize : undo_chain_len;
    return UNDO_TRAVERSAL_COMPLETE;
}

bool InplaceSatisfyUndoRecord(_in_ UndoRecord *urec, _in_ BlockNumber blkno, _in_ OffsetNumber offset,
    _in_ TransactionId xid)
{
    Assert(urec != NULL);
    Assert(urec->Blkno() != InvalidBlockNumber);

    if (urec->Blkno() != blkno || (TransactionIdIsValid(xid) && !TransactionIdEquals(xid, urec->Xid()))) {
        return false;
    }

    switch (urec->Utype()) {
        case UNDO_MULTI_INSERT: {
            OffsetNumber start_offset;
            OffsetNumber end_offset;

            Assert(urec->Rawdata() != NULL);
            start_offset = ((OffsetNumber *)urec->Rawdata()->data)[0];
            end_offset = ((OffsetNumber *)urec->Rawdata()->data)[1];

            if (offset >= start_offset && offset <= end_offset) {
                return true;
            }
        } break;
        default: {
            Assert(offset != InvalidOffsetNumber);
            if (urec->Offset() == offset) {
                return true;
            }
        } break;
    }

    return false;
}

void PrevDumpUndoRecord(UndoRecord *urec)
{
    if (urec == NULL) {
        return;
    }

    char strOutput[MAX_UNDORECORD_DUMPSIZE] = {0};
    errno_t rc = snprintf_s(strOutput + (int)strlen(strOutput),
        MAX_UNDORECORD_DUMPSIZE, MAX_UNDORECORD_DUMPSIZE - 1,
        "[UndoRecord] UndoRecPtr(%lu): xid(%lu), cid(%u), reloid(%u), relfilenode(%u), utype(%u), "
        "uinfo(%u), blkprev(%lu), blockno(%u), offset(%u), prevurp(%lu), payloadlen(%u), oldxactid(%lu), "
        "partitionoid(%u), tablespace(%u).",
        urec->Urp(), urec->Xid(), urec->Cid(), urec->Reloid(), urec->Relfilenode(),
        urec->Utype(), urec->Uinfo(), urec->Blkprev(), urec->Blkno(), urec->Offset(),
        urec->Prevurp2(), urec->PayLoadLen(), urec->OldXactId(), urec->Partitionoid(),
        urec->Tablespace());
    securec_check_ss(rc, "\0", "\0");

    if (urec->Utype() != UNDO_INSERT && urec->Utype() != UNDO_MULTI_INSERT &&
        urec->rawdata_.len > 0 && urec->rawdata_.data != NULL) {
        UHeapDiskTupleData diskTuple;
        if (urec->Utype() == UNDO_INPLACE_UPDATE) {
            Assert(urec->rawdata_.len >= (int)SizeOfUHeapDiskTupleData);
            uint8 *t_hoff_ptr = (uint8 *)(urec->rawdata_.data);
            uint8 t_hoff = *t_hoff_ptr;
            uint16 prefixlen = 0;
            uint16 suffixlen = 0;
            char *cur_undodata_ptr = NULL;
            rc = memcpy_s((char *)&diskTuple + OffsetTdId, SizeOfUHeapDiskTupleHeaderExceptXid,
                urec->rawdata_.data + sizeof(uint8), SizeOfUHeapDiskTupleHeaderExceptXid);
            securec_check(rc, "", "");
            cur_undodata_ptr = urec->rawdata_.data + sizeof(uint8) + t_hoff - OffsetTdId;
            uint8* flags_ptr = (uint8 *)cur_undodata_ptr;
            uint8 flags = *flags_ptr;
            cur_undodata_ptr += sizeof(uint8);
            if (flags & UREC_INPLACE_UPDATE_XOR_PREFIX) {
                uint16* prefixlen_ptr = (uint16 *)(cur_undodata_ptr);
                cur_undodata_ptr += sizeof(uint16);
                prefixlen = *prefixlen_ptr;
            }

            if (flags & UREC_INPLACE_UPDATE_XOR_SUFFIX) {
                uint16* suffixlen_ptr = (uint16 *)(cur_undodata_ptr);
                cur_undodata_ptr += sizeof(uint16);
                suffixlen = *suffixlen_ptr;
            }
            rc = snprintf_s(strOutput + (int)strlen(strOutput),
                MAX_UNDORECORD_DUMPSIZE, MAX_UNDORECORD_DUMPSIZE - 1,
                " inplace update flag(%u), prefixlen(%u), suffixlen(%u).",
                flags, prefixlen, suffixlen);
            securec_check_ss(rc, "\0", "\0");
        } else {
            Assert(urec->rawdata_.len >= (int)SizeOfUHeapDiskTupleHeaderExceptXid);
            rc = memcpy_s(((char *)&diskTuple + OffsetTdId), SizeOfUHeapDiskTupleHeaderExceptXid,
                urec->rawdata_.data, SizeOfUHeapDiskTupleHeaderExceptXid);
            securec_check(rc, "", "");
        }
        rc = snprintf_s(strOutput + (int)strlen(strOutput),
            MAX_UNDORECORD_DUMPSIZE, MAX_UNDORECORD_DUMPSIZE - 1,
            " diskTuple: tdid(%u), reserved(%u), flag(%u), flag2(%u), t_hoff(%u).",
            diskTuple.td_id, diskTuple.reserved, diskTuple.flag, diskTuple.flag2, diskTuple.t_hoff);
        securec_check_ss(rc, "\0", "\0");
    }

    ereport(LOG, (errmodule(MOD_UPAGE), errmsg("%s", strOutput)));

    return;
}
