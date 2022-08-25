/* DO NOT EDIT THIS FILE - it is machine generated */
#include <jni.h>
/* Header for class invoker_sgx_invoker */

#ifndef _Included_invoker_sgx_invoker
#define _Included_invoker_sgx_invoker
#ifdef __cplusplus
extern "C" {
#endif
#undef invoker_sgx_invoker_N
#define invoker_sgx_invoker_N 20L
#undef invoker_sgx_invoker_Temp
#define invoker_sgx_invoker_Temp 100L
/*
 * Class:     invoker_sgx_invoker
 * Method:    print_ms
 * Signature: ()I
 */
JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_print_1ms
  (JNIEnv *, jclass);

/*
 * Class:     invoker_sgx_invoker
 * Method:    init
 * Signature: ()I
 */
JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_init
  (JNIEnv *, jclass);

/*
 * Class:     invoker_sgx_invoker
 * Method:    destroy
 * Signature: ()I
 */
JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_destroy
  (JNIEnv *, jclass);

/*
 * Class:     invoker_sgx_invoker
 * Method:    commitInt
 * Signature: (J[II[DI[FI[JI[CI[BILjava/lang/String;)I
 */
JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_commitInt
  (JNIEnv *, jclass, jlong, jintArray, jint, jdoubleArray, jint, jfloatArray, jint, jlongArray, jint, jcharArray, jint, jbyteArray, jint, jstring);

/*
 * Class:     invoker_sgx_invoker
 * Method:    commitFloat
 * Signature: (J[II[DI[FI[JI[CI[BILjava/lang/String;)F
 */
JNIEXPORT jfloat JNICALL Java_invoker_sgx_1invoker_commitFloat
  (JNIEnv *, jclass, jlong, jintArray, jint, jdoubleArray, jint, jfloatArray, jint, jlongArray, jint, jcharArray, jint, jbyteArray, jint, jstring);

/*
 * Class:     invoker_sgx_invoker
 * Method:    commitDouble
 * Signature: (J[II[DI[FI[JI[CI[BILjava/lang/String;)D
 */
JNIEXPORT jdouble JNICALL Java_invoker_sgx_1invoker_commitDouble
  (JNIEnv *, jclass, jlong, jintArray, jint, jdoubleArray, jint, jfloatArray, jint, jlongArray, jint, jcharArray, jint, jbyteArray, jint, jstring);

/*
 * Class:     invoker_sgx_invoker
 * Method:    commitChar
 * Signature: (J[II[DI[FI[JI[CI[BILjava/lang/String;)C
 */
JNIEXPORT jchar JNICALL Java_invoker_sgx_1invoker_commitChar
  (JNIEnv *, jclass, jlong, jintArray, jint, jdoubleArray, jint, jfloatArray, jint, jlongArray, jint, jcharArray, jint, jbyteArray, jint, jstring);

/*
 * Class:     invoker_sgx_invoker
 * Method:    commitByte
 * Signature: (J[II[DI[FI[JI[CI[BILjava/lang/String;)B
 */
JNIEXPORT jbyte JNICALL Java_invoker_sgx_1invoker_commitByte
  (JNIEnv *, jclass, jlong, jintArray, jint, jdoubleArray, jint, jfloatArray, jint, jlongArray, jint, jcharArray, jint, jbyteArray, jint, jstring);

/*
 * Class:     invoker_sgx_invoker
 * Method:    commitLong
 * Signature: (J[II[DI[FI[JI[CI[BILjava/lang/String;)J
 */
JNIEXPORT jlong JNICALL Java_invoker_sgx_1invoker_commitLong
  (JNIEnv *, jclass, jlong, jintArray, jint, jdoubleArray, jint, jfloatArray, jint, jlongArray, jint, jcharArray, jint, jbyteArray, jint, jstring);

/*
 * Class:     invoker_sgx_invoker
 * Method:    commitBranch
 * Signature: (J[II[DI[FI[JI[CI[BILjava/lang/String;)I
 */
JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_commitBranch
  (JNIEnv *, jclass, jlong, jintArray, jint, jdoubleArray, jint, jfloatArray, jint, jlongArray, jint, jcharArray, jint, jbyteArray, jint, jstring);

/*
 * Class:     invoker_sgx_invoker
 * Method:    commitUpdate
 * Signature: (J[II[DI[FI[JI[CI[BILjava/lang/String;)I
 */
JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_commitUpdate
  (JNIEnv *, jclass, jlong, jintArray, jint, jdoubleArray, jint, jfloatArray, jint, jlongArray, jint, jcharArray, jint, jbyteArray, jint, jstring);

/*
 * Class:     invoker_sgx_invoker
 * Method:    initValue
 * Signature: (Ljava/lang/String;)I
 */
JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_initValue
  (JNIEnv *, jclass, jstring);

/*
 * Class:     invoker_sgx_invoker
 * Method:    deleteValue
 * Signature: (Ljava/lang/String;)I
 */
JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_deleteValue
  (JNIEnv *, jclass, jstring);

#ifdef __cplusplus
}
#endif
#endif
