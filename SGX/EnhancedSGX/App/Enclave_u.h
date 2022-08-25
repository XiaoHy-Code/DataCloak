#ifndef ENCLAVE_U_H__
#define ENCLAVE_U_H__

#include <stdint.h>
#include <wchar.h>
#include <stddef.h>
#include <string.h>
#include "sgx_edger8r.h" /* for sgx_satus_t etc. */

#include "user_types.h"
#include "hot_calls.h"
#include "common.h"

#include <stdlib.h> /* for size_t */

#define SGX_CAST(type, item) ((type)(item))

#ifdef __cplusplus
extern "C" {
#endif

void SGX_UBRIDGE(SGX_NOCONVENTION, ocall_print_string, (const char* str));
void SGX_UBRIDGE(SGX_NOCONVENTION, ocall_print_int, (int str));
void SGX_UBRIDGE(SGX_NOCONVENTION, ocall_print_long, (long int str));
void SGX_UBRIDGE(SGX_NOCONVENTION, ocall_file_write, (char* file, char* buf, int len));
void SGX_UBRIDGE(SGX_NOCONVENTION, ocall_file_add, (char* file, char* buf, int len));
void SGX_UBRIDGE(SGX_NOCONVENTION, ocall_file_read, (char* file, int* buf, long int* start));
void SGX_UBRIDGE(SGX_NOCONVENTION, ocall_file_getline, (char* file, char* buf, long int* line_num));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_open, (const char* filename, int flags, mode_t mode));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_fallocate, (int fd, int mode, off_t offset, off_t len));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_fcntl_flock, (int fd, int cmd, struct flock* p));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_fcntl_int, (int fd, int cmd, int pa));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_fcntl_void, (int fd, int cmd));
char* SGX_UBRIDGE(SGX_NOCONVENTION, ocall_getenv, (const char* name));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_stat, (const char* pathname, struct stat* buf));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_fstat, (int fd, struct stat* buf));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_fchmod, (int fd, unsigned int mode));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_mkdir, (const char* pathname, mode_t mode));
time_t SGX_UBRIDGE(SGX_NOCONVENTION, ocall_time, (time_t* t));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_utimes, (const char* filename, const struct timeval* times));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_gettimeofday, (struct timeval* tv));
ssize_t SGX_UBRIDGE(SGX_NOCONVENTION, ocall_read, (int file, void* buf, size_t count));
ssize_t SGX_UBRIDGE(SGX_NOCONVENTION, ocall_write, (int file, const void* buf, size_t count));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_close, (int fd));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_fchown, (int fd, uid_t owner, gid_t group));
char* SGX_UBRIDGE(SGX_NOCONVENTION, ocall_getcwd, (char* buf, size_t size));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_truncate, (const char* path, off_t length));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_ftruncate, (int fd, off_t length));
ssize_t SGX_UBRIDGE(SGX_NOCONVENTION, ocall_pread, (int fd, void* buf, size_t count, off_t offset));
ssize_t SGX_UBRIDGE(SGX_NOCONVENTION, ocall_pwrite, (int fd, const void* buf, size_t count, off_t offset));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_access, (const char* pathname, int mode));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_unlink, (const char* pathname));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_rmdir, (const char* pathname));
uid_t SGX_UBRIDGE(SGX_NOCONVENTION, ocall_geteuid, ());
off_t SGX_UBRIDGE(SGX_NOCONVENTION, ocall_lseek, (int fd, off_t offset, int whence));
int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_fsync, (int fd));
pid_t SGX_UBRIDGE(SGX_NOCONVENTION, ocall_getpid, ());
unsigned int SGX_UBRIDGE(SGX_NOCONVENTION, ocall_sleep, (unsigned int seconds));

sgx_status_t encall_switch_type_get_i(sgx_enclave_id_t eid, void* data, void* rei, int* int_array, int intTail, double* double_array, int doubleTail, float* float_array, int floatTail, char* char_array, int charTail, long int* long_array, int longTail, char* byte_array, int byteTail, char* uuid, char* cuuid);
sgx_status_t encall_switch_type_branch(sgx_enclave_id_t eid, void* data, void* rei, int* int_array, int intTail, double* double_array, int doubleTail, float* float_array, int floatTail, char* char_array, int charTail, long int* long_array, int longTail, char* byte_array, int byteTail, char* uuid, char* cuuid);
sgx_status_t encall_switch_type_update(sgx_enclave_id_t eid, void* data, void* rei, int* int_array, int intTail, double* double_array, int doubleTail, float* float_array, int floatTail, char* char_array, int charTail, long int* long_array, int longTail, char* byte_array, int byteTail, char* uuid, char* cuuid);
sgx_status_t encall_switch_get_d(sgx_enclave_id_t eid, double* retval, long int Line, int* int_array, int lenint, double* double_array, int lendouble, float* float_array, int lenfloat, char* char_array, int lenchar, long int* long_array, int lenlong, char* byte_array, int lenbyte, char* uuid);
sgx_status_t encall_switch_get_l(sgx_enclave_id_t eid, long int* retval, long int Line, int* int_array, int lenint, double* double_array, int lendouble, float* float_array, int lenfloat, char* char_array, int lenchar, long int* long_array, int lenlong, char* byte_array, int lenbyte, char* uuid);
sgx_status_t print_int(sgx_enclave_id_t eid, int* retval, long int line, int* int_array, char* uuid, char* cuuid);
sgx_status_t print_double(sgx_enclave_id_t eid, double* retval, long int line, double* double_array, int* int_array, char* uuid, char* cuuid);
sgx_status_t print_float(sgx_enclave_id_t eid, float* retval, long int line, float* float_array, char* uuid);
sgx_status_t print_char(sgx_enclave_id_t eid, int* retval, long int line, char* char_array, char* uuid);
sgx_status_t print_long(sgx_enclave_id_t eid, long int* retval, long int line, long int* long_array, int* int_array, char* uuid);
sgx_status_t print_byte(sgx_enclave_id_t eid, int* retval, long int line, char* byte_array, int* int_array, char* uuid);
sgx_status_t print_array_i(sgx_enclave_id_t eid, int* retval, long int line, int* int_array, int int_tail, char* uuid, char* cuuid);
sgx_status_t print_array_d(sgx_enclave_id_t eid, int* retval, long int line, double* double_array, int double_tail, char* uuid, char* cuuid);
sgx_status_t encall_table_load(sgx_enclave_id_t eid, int* retval);
sgx_status_t encall_hash_readin(sgx_enclave_id_t eid, int* retval, char* buf, long int line);
sgx_status_t encall_read_line(sgx_enclave_id_t eid, int* retval, char* in_buf, int buf_len, long int line, int isIndex);
sgx_status_t encall_varible(sgx_enclave_id_t eid, void* data, char* uuid, char* calluuid);
sgx_status_t encall_deleteValue(sgx_enclave_id_t eid, void* data, char* uuid, char* cuuid);
sgx_status_t encall_initArray(sgx_enclave_id_t eid, char* uuid, int index, int size, int isSens);
sgx_status_t encall_initNode(sgx_enclave_id_t eid, char* uuid, int type, int size);
sgx_status_t encall_getArraySize(sgx_enclave_id_t eid, int* retval, long int line, char* uuid);
sgx_status_t encall_getIntArray(sgx_enclave_id_t eid, int* re, int size, long int line, char* uuid);
sgx_status_t encall_getDoubleArray(sgx_enclave_id_t eid, double* re, int size, long int line, char* uuid);
sgx_status_t encall_initmultiArray(sgx_enclave_id_t eid, long int line, char* uuid, char* cuuid);
sgx_status_t EcallStartResponder(sgx_enclave_id_t eid, HotCall* fastEcall);
sgx_status_t EcallStartResponder3(sgx_enclave_id_t eid, HotCall* fastEcall);

#ifdef __cplusplus
}
#endif /* __cplusplus */

#endif
