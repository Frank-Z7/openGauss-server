#This is the main CMAKE for build bin.
AUX_SOURCE_DIRECTORY(${CMAKE_CURRENT_SOURCE_DIR} TGT_job_SRC)

set(TGT_job_INC 
    ${PROJECT_SRC_DIR}/gausskernel/cbb/communication
    ${PROJECT_SRC_DIR}/include/libcomm
    ${PROJECT_SRC_DIR}/include
    ${PROJECT_SRC_DIR}/lib/gstrace
    ${LIBCGROUP_INCLUDE_PATH}
    ${ZLIB_INCLUDE_PATH}
)

set(job_DEF_OPTIONS ${MACRO_OPTIONS})
set(job_COMPILE_OPTIONS ${OPTIMIZE_OPTIONS} ${OS_OPTIONS} ${PROTECT_OPTIONS} ${WARNING_OPTIONS} ${BIN_SECURE_OPTIONS} ${CHECK_OPTIONS})
set(job_LINK_OPTIONS ${BIN_LINK_OPTIONS})
add_static_objtarget(gausskernel_process_job TGT_job_SRC TGT_job_INC "${job_DEF_OPTIONS}" "${job_COMPILE_OPTIONS}" "${job_LINK_OPTIONS}")

