#This is the main CMAKE for build bin.
AUX_SOURCE_DIRECTORY(${CMAKE_CURRENT_SOURCE_DIR} TGT_buffer_SRC)

set(TGT_buffer_INC 
    ${PROJECT_OPENGS_DIR}/contrib/log_fdw
    ${PROJECT_TRUNK_DIR}/distribute/bin/gds
    ${PROJECT_SRC_DIR}/include/libcomm
    ${PROJECT_SRC_DIR}/include
    ${PROJECT_SRC_DIR}/lib/gstrace
    ${LZ4_INCLUDE_PATH}
    ${LIBCGROUP_INCLUDE_PATH}
    ${EVENT_INCLUDE_PATH}
    ${ZLIB_INCLUDE_PATH}
)

set(buffer_DEF_OPTIONS ${MACRO_OPTIONS} -DOPENGAUSS)
set(buffer_COMPILE_OPTIONS ${OPTIMIZE_OPTIONS} ${OS_OPTIONS} ${PROTECT_OPTIONS} ${WARNING_OPTIONS} ${BIN_SECURE_OPTIONS} ${CHECK_OPTIONS})
set(buffer_LINK_OPTIONS ${BIN_LINK_OPTIONS})
add_static_objtarget(gausskernel_storage_buffer TGT_buffer_SRC TGT_buffer_INC "${buffer_DEF_OPTIONS}" "${buffer_COMPILE_OPTIONS}" "${buffer_LINK_OPTIONS}")

