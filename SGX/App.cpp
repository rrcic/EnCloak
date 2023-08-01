#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <time.h>
# include <unistd.h>
# include <pwd.h>
#define MAX_PATH FILENAME_MAX

#include "sgx_urts.h"
#include "App.h"
#include "Enclave_u.h"
#include<fstream>
#include<iomanip>
#include <iostream>
#include <fstream>
#include <vector>
#include<time.h>
#include<ctime>
#include <sys/types.h>
#include <sys/stat.h>
#include <sys/ioctl.h>
using namespace std;
#include <cstdarg>
#include "invoker_sgx_invoker.h"

typedef unsigned char byte;
#define ArrayLen 10//10000
//-------------------------------------------------

int sgx_use_flag=0;
/* Global EID shared by multiple threads */
sgx_enclave_id_t global_eid = 1;
sgx_enclave_id_t globalEnclaveID;
clock_t t1,t2;

int rei = -99;
int reu = -99;
int reb = -99;
int re_get = -99;

clock_t t3,t4;

int gnum = 0;
int inum = 0;
int dnum = 0;
int unum = 0;
int bnum = 0;

long temp = 0;
int tem=0;

ofstream outfile;

//------------------------------------------hotcalls-------------------------------------------
#include "common.h"
#include "hot_calls.h"
//#include "hot_calls1.h"
typedef sgx_status_t (*EcallFunction)(sgx_enclave_id_t, void* );

#define PERFORMANCE_MEASUREMENT_NUM_REPEATS 10000
#define MEASUREMENTS_ROOT_DIR               "measurments"

inline __attribute__((always_inline))  uint64_t rdtscp(void)
{
        unsigned int low, high;

        asm volatile("rdtscp" : "=a" (low), "=d" (high));

        return low | ((uint64_t)high) << 32;
}

void* EnclaveResponderThread( void* hotEcallAsVoidP )    //branch
{
    //To be started in a new thread
    HotCall *hotEcall = (HotCall*)hotEcallAsVoidP;
    EcallStartResponder( globalEnclaveID, hotEcall );

    return NULL;
}

/*void* EnclaveResponderThread1( void* hotEcall1AsVoidP )  //update
{
    //To be started in a new thread
    HotCall *hotEcall1 = (HotCall*)hotEcall1AsVoidP;
    EcallStartResponder1( globalEnclaveID, hotEcall1 );

    return NULL;
}

void* EnclaveResponderThread2( void* hotEcall2AsVoidP )  //get_i
{
    //To be started in a new thread
    HotCall *hotEcall2 = (HotCall*)hotEcall2AsVoidP;
    EcallStartResponder2( globalEnclaveID, hotEcall2 );

    return NULL;
}
*/
void* EnclaveResponderThread3( void* hotEcall3AsVoidP ) //init_delete
{
    //To be started in a new thread
    HotCall *hotEcall3 = (HotCall*)hotEcall3AsVoidP;
    EcallStartResponder3( globalEnclaveID, hotEcall3 );

    return NULL;
}

/*void* EnclaveResponderThread_initvalue( void* hotEcallAsVoidP )
{
    //To be started in a new thread
    HotCall_init_delete *hotEcall_initvalue = (HotCall_init_delete*)hotEcallAsVoidP;
    EcallStartResponder_initvalue( globalEnclaveID, hotEcall_initvalue );

    return NULL;
}
*/
	int         data            = 0;
	int intArray[ArrayLen]={0};
	double doubleArray[ArrayLen]={0};
	float floatArray[ArrayLen]={0};
	char charArray[ArrayLen]={NULL};
	long longArray[ArrayLen]={0};
	char byteArray[ArrayLen]={NULL};
	char uuid[33]={NULL};
	HotCall     hotEcall        = HOTCALL_INITIALIZER;
/*
        long        data1       =0;
	int intArray1[ArrayLen]={0};
	double doubleArray1[ArrayLen]={0};
	float floatArray1[ArrayLen]={0};
	char charArray1[ArrayLen]={NULL};
	long longArray1[ArrayLen]={0};
	char byteArray1[ArrayLen]={NULL};
	char uuid1[33]={NULL};
	HotCall     hotEcall1        = HOTCALL_INITIALIZER;

	int         data2            = 0;
	int intArray2[ArrayLen]={0};
	double doubleArray2[ArrayLen]={0};
	float floatArray2[ArrayLen]={0};
	char charArray2[ArrayLen]={NULL};
	long longArray2[ArrayLen]={0};
	char byteArray2[ArrayLen]={NULL};
	char uuid2[33]={NULL};
	HotCall     hotEcall2        = HOTCALL_INITIALIZER;
*/
	//int         data3            = 0;
	//int intArray3[ArrayLen]={0};
	//double doubleArray3[ArrayLen]={0};
	//float floatArray3[ArrayLen]={0};
	//char charArray3[ArrayLen]={NULL};
	//long longArray3[ArrayLen]={0};
	//char byteArray3[ArrayLen]={NULL};
	char uuid3[33]={NULL};
	char uuid3c[33]={NULL};
	HotCall     hotEcall3        = HOTCALL_INITIALIZER;
/*	int intArray_initvalue[8]={0};
	char uuid_initvalue[33]={NULL};
	HotCall_init_delete hotEcall_initvalue       = HOTCALL_INITIALIZER_init_delete;

	//char uuid_deletevalue[33]={NULL};
	//HotCall_init_delete hotEcall_deletevalue       = HOTCALL_INITIALIZER_init_delete;
*/
        const uint16_t requestedCallID = 0;
	const uint16_t requestedCallID1 = 1;
	const uint16_t requestedCallID2 = 2;
        const uint16_t requestedCallID3 = 3;
        const uint16_t requestedCallID4 = 4;
//---------------------------------------------------------------------------------------------------



JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_init(JNIEnv *env, jclass obj)
//int init_enclave(void)
{
	if(sgx_use_flag){
		return 0;
	}
	clock_t t1,t2;
	t1=clock();

	printf("----enter Java_invoker_sgx_1invoker_init()-----\n");
	// TODO initialize_enclave()这个函数的定义在哪？
    if(initialize_enclave() < 0){
        printf("init Failed ...\n");
        getchar();
        return -1; 
    }
	printf("init ok\n");
	//------------load-----------------------
	int load_flag=-111;
	//printf("loading");
	//encall_invoketable_load(global_eid,&load_flag);
	encall_table_load(global_eid,&load_flag);
	
	sgx_use_flag=1;
	printf("load matrix ok load_flag=%d\n",load_flag);
   
	//hotcall
	hotEcall.data               = &data;
	hotEcall.intArray               = intArray; 
	hotEcall.doubleArray               = doubleArray;
	hotEcall.floatArray               = floatArray;
	hotEcall.charArray               = charArray;
	hotEcall.longArray               = longArray;
	hotEcall.byteArray               = byteArray;	
	hotEcall.uuid               = uuid;
/*
        hotEcall1.data               = &data1; 
	hotEcall1.intArray               = intArray1; 
	hotEcall1.doubleArray               = doubleArray1;
	hotEcall1.floatArray               = floatArray1;
	hotEcall1.charArray               = charArray1;
	hotEcall1.longArray               = longArray1;
	hotEcall1.byteArray               = byteArray1;	
	hotEcall1.uuid               = uuid1;

	hotEcall2.data               = &data2;
	hotEcall2.intArray               = intArray2; 
	hotEcall2.doubleArray               = doubleArray2;
	hotEcall2.floatArray               = floatArray2;
	hotEcall2.charArray               = charArray2;
	hotEcall2.longArray               = longArray2;
	hotEcall2.byteArray               = byteArray2;	
	hotEcall2.uuid               = uuid2;
*/	
	//hotEcall3.data               = &data3;
	//hotEcall3.intArray               = intArray3; 
	//hotEcall3.doubleArray               = doubleArray3;
	//hotEcall3.floatArray               = floatArray3;
	//hotEcall3.charArray               = charArray3;
	//hotEcall3.longArray               = longArray3;
	//hotEcall3.byteArray               = byteArray3;	
	hotEcall3.uuid               = uuid3;
//	hotEcall_initvalue.intArray               = intArray_initvalue; 	
//	hotEcall_initvalue.uuid               = uuid_initvalue;

	//hotEcall_deletevalue.uuid               = uuid_deletevalue;

        globalEnclaveID = global_eid;
        pthread_create(&hotEcall.responderThread, NULL, EnclaveResponderThread, (void*)&hotEcall);
        //pthread_create(&hotEcall1.responderThread, NULL, EnclaveResponderThread1, (void*)&hotEcall1);
	//pthread_create(&hotEcall2.responderThread, NULL, EnclaveResponderThread2, (void*)&hotEcall2);	
 	pthread_create(&hotEcall3.responderThread, NULL, EnclaveResponderThread3, (void*)&hotEcall3);
///pthread_create(&hotEcall_deletevalue.responderThread, NULL, EnclaveResponderThread_deletevalue, (void*)&hotEcall_deletevalue);

	t2=clock();
	printf("initialize_enclave()_time: %lfs\n", ((double)(t2 - t1)/CLOCKS_PER_SEC));
	printf("sgx update 22\n");
	printf("hotcall init ok\n");

	return load_flag;
}

JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_destroy(JNIEnv *env, jclass obj)
{

   // printf("ready to destroy\n");
    //------------------------------destroy------------
    StopResponder( &hotEcall );
   // StopResponder( &hotEcall1);
    //StopResponder( &hotEcall2);
    StopResponder( &hotEcall3);
   
    if(SGX_SUCCESS==sgx_destroy_enclave(global_eid)){
	sgx_use_flag=0;
	printf("total_ecall=%d\n",gnum+unum+bnum+inum+dnum);
	printf("getint_ecall=%d\n",gnum);
	printf("update_ecall=%d\n",unum);
	printf("branch_ecall=%d\n",bnum);
	printf("init_ecall=%d\n",inum);
	printf("delete_ecall=%d\n",dnum);
    	printf("Enclave destroy success\n");
	return 0;
    }else{
	printf("Enclave destroy failure\n");
	return -1;
    }
}
JNIEXPORT void JNICALL Java_invoker_sgx_1invoker_initNode
  (JNIEnv *env, jclass obj, jstring uuidstring, jint type, jint size){

  	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("initArray enter wrong \n");

	const char* buf = env->GetStringUTFChars(uuidstring,false);
	strcpy(uuid,buf);
	env->ReleaseStringUTFChars(uuidstring, buf);

	encall_initNode(global_eid,uuid,type,size);

//printf("initarray over\n");
	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("initArray exit wrong \n");
	return;

  }


JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_commitInt
  (JNIEnv *env, jclass obj, jlong counter, jintArray jintArray, jint intTail, jdoubleArray jdoubleArray, jint doubleTail, jfloatArray jfloatArray, jint floatTail,jlongArray jlongArray, jint longTail, jcharArray jcharArray, jint charTail,jbyteArray jbyteArray, jint byteTail, jstring uuidstring){


	
	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("Java_invoker_sgx_1invoker_commitInt enter wrong \n");
//printf("go to get int line=%ld\n",counter);
gnum++;
//printf("gettnum=%ld\n",num);

	/*int intArray[ArrayLen];
	double doubleArray[ArrayLen];
	float floatArray[ArrayLen];
	char charArray[ArrayLen];
	long longArray[ArrayLen];
	char byteArray[ArrayLen];*/
		jint *body_i = env->GetIntArrayElements(jintArray, 0);
			for (int i=0; i<intTail; i++)
			{
				intArray[i] = body_i[i];
			}
			env->ReleaseIntArrayElements(jintArray, body_i, 0);
	//	}
	//if(doubleTail > 0){
		jdouble *body_d = env->GetDoubleArrayElements(jdoubleArray, 0);
		for (int i=0; i<doubleTail; i++)
		{
			doubleArray[i] = body_d[i];
		}
		env->ReleaseDoubleArrayElements(jdoubleArray, body_d, 0);
	//}
	//if(floatTail > 0){
		jfloat *body_f = env->GetFloatArrayElements(jfloatArray, 0);
		for (int i=0; i<floatTail; i++)
		{
			floatArray[i] = body_f[i];
		}
		env->ReleaseFloatArrayElements(jfloatArray,body_f, 0);
	//}
	//if(longTail > 0){
		jlong *body_l = env->GetLongArrayElements(jlongArray, 0);
		for (int i=0; i<longTail; i++)
		{
			longArray[i] = body_l[i];
		}
		env->ReleaseLongArrayElements(jlongArray,body_l, 0);

	//}
	//if(charTail > 0){
		jchar *body_c = env->GetCharArrayElements(jcharArray, 0);
		for (int i=0; i<charTail; i++)
		{
			charArray[i] = body_c[i];
		}
		env->ReleaseCharArrayElements(jcharArray,body_c , 0);
	//}
	//if(byteTail > 0){
		jbyte *body_b = env->GetByteArrayElements(jbyteArray, 0);
		for (int i=0; i<byteTail; i++)
		{
			byteArray[i] = body_b[i];
		}
		env->ReleaseByteArrayElements(jbyteArray,body_b, 0);
	//}

	int re=-99;
	const char* buf = env->GetStringUTFChars(uuidstring, false);
	char uuid[33] = {0};
	char cuuid[33] = {0};
	strcpy(uuid,buf);
	env->ReleaseStringUTFChars(uuidstring,buf);

//printf("get Line=%ld ,uuid=%s\n",counter,uuid);
	//sgx_status_t ret=encall_switch_type_i(global_eid,&re,counter,intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,charArray,charTail,longArray,longTail,byteArray,byteTail,uuid);
	HotCall_requestCall( &hotEcall,requestedCallID4, &counter,intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,charArray,charTail,longArray,longTail,byteArray,byteTail,uuid,cuuid,&re_get);
	//printf("after HotCall_requestCall get over\n");
//printf("get Line=%ld ,uuid=%s\n",counter,uuid);
	
//	if(env -> ExceptionOccurred()){
//		printf(" commInt ExceptionOccurred\n");
//		if(env -> MonitorExit(obj)!= JNI_OK);
//		return 0;
//	}
	//getint_ecall++;
	re = re_get;

//if(counter == 48L){
//	printf("[APP] get Line 48 re=%d\n",re);
//}
	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("Java_invoker_sgx_1invoker_commitInt exit wrong \n");	
	
	return re;

	
	//return rei;
}
/**
	commitDouble
*/
JNIEXPORT jdouble JNICALL Java_invoker_sgx_1invoker_commitDouble
   (JNIEnv *env, jclass obj, jlong counter, jintArray jintArray, jint intTail, jdoubleArray jdoubleArray, jint doubleTail, jfloatArray jfloatArray, jint floatTail,jlongArray jlongArray, jint longTail, jcharArray jcharArray, jint charTail,jbyteArray jbyteArray, jint byteTail, jstring uuidstring){
	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("double enter wrong \n");		
	printf("go to get double line=%ld\n",counter);	
	const char* buf = env->GetStringUTFChars(uuidstring, false);
	//char uuid[33] = {0};
	strcpy(uuid,buf);
	env->ReleaseStringUTFChars(uuidstring, buf);

	
	double red=0.0;
	
	sgx_status_t ret=encall_switch_get_d(global_eid,&red,counter,intArray,intTail,
			doubleArray,doubleTail,
			floatArray,floatTail,
			charArray,charTail,
			longArray,longTail,
			byteArray,byteTail,uuid);
	if(ret != SGX_SUCCESS){
		print_error_message(ret);
	}
//printf("get over \n");
	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("Java_invoker_sgx_1invoker_commitdouble exit wrong \n");	
	return red;
}
/**
	commitFloat
*/
JNIEXPORT jfloat JNICALL Java_invoker_sgx_1invoker_commitFloat
  (JNIEnv *env, jclass obj, jlong counter, jintArray jintArray, jint intTail, jdoubleArray jdoubleArray, jint doubleTail, jfloatArray jfloatArray, jint floatTail,jlongArray jlongArray, jint longTail, jcharArray jcharArray, jint charTail,jbyteArray jbyteArray, jint byteTail, jstring uuidstring){
	float ref=999;
	//printf("go to get float line=%ld\n",counter);	
	/*int intArray[ArrayLen];
	double doubleArray[ArrayLen];
	float floatArray[ArrayLen];
	char charArray[ArrayLen];
	long longArray[ArrayLen];
	char byteArray[ArrayLen];
	
	jint *body_i = env->GetIntArrayElements(jintArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		intArray[i] = body_i[i];
	}
	env->ReleaseIntArrayElements(jintArray, body_i, 0);

	jdouble *body_d = env->GetDoubleArrayElements(jdoubleArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		doubleArray[i] = body_d[i];
	}
	env->ReleaseDoubleArrayElements(jdoubleArray, body_d, 0);

	jfloat *body_f = env->GetFloatArrayElements(jfloatArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		floatArray[i] = body_f[i];
	}
	env->ReleaseFloatArrayElements(jfloatArray, body_f, 0);

	jlong *body_l = env->GetLongArrayElements(jlongArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		longArray[i] = body_l[i];
	}
	env->ReleaseLongArrayElements(jlongArray, body_l, 0);
	
	jchar *body_c = env->GetCharArrayElements(jcharArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		charArray[i] = body_c[i];
	}
	env->ReleaseCharArrayElements(jcharArray, body_c, 0);
	
	jbyte *body_b = env->GetByteArrayElements(jbyteArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		byteArray[i] = body_b[i];
	}
	env->ReleaseByteArrayElements(jbyteArray, body_b, 0);	

	if(sgx_use_flag!=1){printf("not init yet");return -12;}

	float ref=999;
	/*
	sgx_status_t ret=encall_switch_type_f(global_eid,&ref,counter,intArray,intTail,
			doubleArray,doubleTail,
			floatArray,floatTail,
			charArray,charTail,
			longArray,longTail,
			byteArray,byteTail);
	if(ret != SGX_SUCCESS){
		print_error_message(ret);
	}
	*/
	return ref;
}
/**
	commitChar
*/
JNIEXPORT jchar JNICALL Java_invoker_sgx_1invoker_commitChar
  (JNIEnv *env, jclass obj, jlong counter, jintArray jintArray, jint intTail, jdoubleArray jdoubleArray, jint doubleTail, jfloatArray jfloatArray, jint floatTail,jlongArray jlongArray, jint longTail, jcharArray jcharArray, jint charTail,jbyteArray jbyteArray, jint byteTail, jstring uuidstring){
	char rec=NULL;	
	//printf("go to get Char line=%ld\n",counter);
	/*int intArray[ArrayLen];
	double doubleArray[ArrayLen];
	float floatArray[ArrayLen];
	char charArray[ArrayLen];
	long longArray[ArrayLen];
	char byteArray[ArrayLen];
	
	jint *body_i = env->GetIntArrayElements(jintArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		intArray[i] = body_i[i];
	}
	env->ReleaseIntArrayElements(jintArray, body_i, 0);

	jdouble *body_d = env->GetDoubleArrayElements(jdoubleArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		doubleArray[i] = body_d[i];
	}
	env->ReleaseDoubleArrayElements(jdoubleArray, body_d, 0);

	jfloat *body_f = env->GetFloatArrayElements(jfloatArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		floatArray[i] = body_f[i];
	}
	env->ReleaseFloatArrayElements(jfloatArray, body_f, 0);

	jlong *body_l = env->GetLongArrayElements(jlongArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		longArray[i] = body_l[i];
	}
	env->ReleaseLongArrayElements(jlongArray, body_l, 0);
	
	jchar *body_c = env->GetCharArrayElements(jcharArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		charArray[i] = body_c[i];
	}
	env->ReleaseCharArrayElements(jcharArray, body_c, 0);
	
	jbyte *body_b = env->GetByteArrayElements(jbyteArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		byteArray[i] = body_b[i];
	}
	env->ReleaseByteArrayElements(jbyteArray, body_b, 0);	

	if(sgx_use_flag!=1){printf("not init yet");return -12;}

	char rec=NULL;
	/*
	sgx_status_t ret=encall_switch_type_c(global_eid,&rec,counter,intArray,intTail,
			doubleArray,doubleTail,
			floatArray,floatTail,
			charArray,charTail,
			longArray,longTail,
			byteArray,byteTail);
	if(ret != SGX_SUCCESS){
		print_error_message(ret);
	}
	*/
	return rec;
}

/**
	commitByte
*/
JNIEXPORT jbyte JNICALL Java_invoker_sgx_1invoker_commitByte
  (JNIEnv *env, jclass obj, jlong counter, jintArray jintArray, jint intTail, jdoubleArray jdoubleArray, jint doubleTail, jfloatArray jfloatArray, jint floatTail,jlongArray jlongArray, jint longTail, jcharArray jcharArray, jint charTail,jbyteArray jbyteArray, jint byteTail, jstring uuidstring){
	char reb=NULL;	
	/*int intArray[ArrayLen];
	double doubleArray[ArrayLen];
	float floatArray[ArrayLen];
	char charArray[ArrayLen];
	long longArray[ArrayLen];
	char byteArray[ArrayLen];
	
	jint *body_i = env->GetIntArrayElements(jintArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		intArray[i] = body_i[i];
	}
	env->ReleaseIntArrayElements(jintArray, body_i, 0);

	jdouble *body_d = env->GetDoubleArrayElements(jdoubleArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		doubleArray[i] = body_d[i];
	}
	env->ReleaseDoubleArrayElements(jdoubleArray, body_d, 0);

	jfloat *body_f = env->GetFloatArrayElements(jfloatArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		floatArray[i] = body_f[i];
	}
	env->ReleaseFloatArrayElements(jfloatArray, body_f, 0);

	jlong *body_l = env->GetLongArrayElements(jlongArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		longArray[i] = body_l[i];
	}
	env->ReleaseLongArrayElements(jlongArray, body_l, 0);
	
	jchar *body_c = env->GetCharArrayElements(jcharArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		charArray[i] = body_c[i];
	}
	env->ReleaseCharArrayElements(jcharArray, body_c, 0);
	
	jbyte *body_b = env->GetByteArrayElements(jbyteArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		byteArray[i] = body_b[i];
	}
	env->ReleaseByteArrayElements(jbyteArray, body_b, 0);	

	if(sgx_use_flag!=1){printf("not init yet");return -12;}

	char reb=NULL;
	/*
	sgx_status_t ret=encall_switch_type_b(global_eid,&reb,counter,intArray,intTail,
			doubleArray,doubleTail,
			floatArray,floatTail,
			charArray,charTail,
			longArray,longTail,
			byteArray,byteTail);
	if(ret != SGX_SUCCESS){
		print_error_message(ret);
	}
	*/
	return reb;
}
/**
	commitLong
*/
JNIEXPORT jlong JNICALL Java_invoker_sgx_1invoker_commitLong
  (JNIEnv *env, jclass obj, jlong counter, jintArray jintArray, jint intTail, jdoubleArray jdoubleArray, jint doubleTail, jfloatArray jfloatArray, jint floatTail,jlongArray jlongArray, jint longTail, jcharArray jcharArray, jint charTail,jbyteArray jbyteArray, jint byteTail, jstring uuidstring){
	
	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("Long enter wrong \n");	
	long rel=999;	
	//printf("go to get l line=%ld\n",counter);
	/*int intArray[ArrayLen];
	double doubleArray[ArrayLen];
	float floatArray[ArrayLen];
	char charArray[ArrayLen];
	long longArray[ArrayLen];
	char byteArray[ArrayLen];
	
	jint *body_i = env->GetIntArrayElements(jintArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		intArray[i] = body_i[i];
	}
	env->ReleaseIntArrayElements(jintArray, body_i, 0);

	jdouble *body_d = env->GetDoubleArrayElements(jdoubleArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		doubleArray[i] = body_d[i];
	}
	env->ReleaseDoubleArrayElements(jdoubleArray, body_d, 0);

	jfloat *body_f = env->GetFloatArrayElements(jfloatArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		floatArray[i] = body_f[i];
	}
	env->ReleaseFloatArrayElements(jfloatArray, body_f, 0);

	jlong *body_l = env->GetLongArrayElements(jlongArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		longArray[i] = body_l[i];
	}
	env->ReleaseLongArrayElements(jlongArray, body_l, 0);
	
	jchar *body_c = env->GetCharArrayElements(jcharArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		charArray[i] = body_c[i];
	}
	env->ReleaseCharArrayElements(jcharArray, body_c, 0);
	
	jbyte *body_b = env->GetByteArrayElements(jbyteArray, 0);
	for (int i=0; i<ArrayLen; i++)
	{
		byteArray[i] = body_b[i];
	}
	env->ReleaseByteArrayElements(jbyteArray, body_b, 0);	

	if(sgx_use_flag!=1){printf("not init yet");return -12;}

	long rel=999;
	*/
	const char* buf = env->GetStringUTFChars(uuidstring, false);
	//char uuid[33] = {0};
	strcpy(uuid,buf);
	env->ReleaseStringUTFChars(uuidstring, buf);

	sgx_status_t ret=encall_switch_get_l(global_eid,&rel,counter,intArray,intTail,
			doubleArray,doubleTail,
			floatArray,floatTail,
			charArray,charTail,
			longArray,longTail,
			byteArray,byteTail,uuid);
	if(ret != SGX_SUCCESS){
		print_error_message(ret);
	}
//printf("get over %ld\n",rel);

	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("branch exit wrong \n");	
	return rel;
}

JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_commitBranch
 (JNIEnv *env, jclass obj, jlong counter, jintArray jintArray, jint intTail, jdoubleArray jdoubleArray, jint doubleTail, jfloatArray jfloatArray, jint floatTail,jlongArray jlongArray, jint longTail, jcharArray jcharArray, jint charTail,jbyteArray jbyteArray, jint byteTail, jstring uuidstring){
	
	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("branch enter wrong \n");
	//printf("go to branch line=%ld\n",counter);
bnum++;
//printf("evalnum=%ld\n",num);

	/*int intArray[ArrayLen];
	double doubleArray[ArrayLen];
	float floatArray[ArrayLen];
	char charArray[ArrayLen];
	long longArray[ArrayLen];
	char byteArray[ArrayLen];
	if(intTail > 0){
		jint *body_i = env->GetIntArrayElements(jintArray, 0);
		for (int i=0; i<intTail; i++)
		{
			intArray[i] = body_i[i];
		}
		env->ReleaseIntArrayElements(jintArray, body_i, 0);
	}
	if(doubleTail > 0){
		jdouble *body_d = env->GetDoubleArrayElements(jdoubleArray, 0);
		for (int i=0; i<doubleTail; i++)
		{
			doubleArray[i] = body_d[i];
		}
		env->ReleaseDoubleArrayElements(jdoubleArray, body_d, 0);
	}
	if(floatTail > 0){
		jfloat *body_f = env->GetFloatArrayElements(jfloatArray, 0);
		for (int i=0; i<floatTail; i++)
		{
			floatArray[i] = body_f[i];
		}
		env->ReleaseFloatArrayElements(jfloatArray,body_f, 0);
	}
	if(longTail > 0){
		jlong *body_l = env->GetLongArrayElements(jlongArray, 0);
		for (int i=0; i<longTail; i++)
		{
			longArray[i] = body_l[i];
		}
		env->ReleaseLongArrayElements(jlongArray,body_l, 0);

	}
	if(charTail > 0){
		jchar *body_c = env->GetCharArrayElements(jcharArray, 0);
		for (int i=0; i<charTail; i++)
		{
			charArray[i] = body_c[i];
		}
		env->ReleaseCharArrayElements(jcharArray,body_c , 0);
	}
	if(byteTail > 0){
		jbyte *body_b = env->GetByteArrayElements(jbyteArray, 0);
		for (int i=0; i<byteTail; i++)
		{
			byteArray[i] = body_b[i];
		}
		env->ReleaseByteArrayElements(jbyteArray,body_b, 0);
	}*/

	int re = -98;
	const char* buf = env->GetStringUTFChars(uuidstring, false);
	char uuid[33] = {0};
	strncpy(uuid,buf,32);
	env->ReleaseStringUTFChars(uuidstring, buf);
//printf("branch Line=%ld ,uuid=%s\n",counter,uuid);
	//printf("go to branch\n");
	//sgx_status_t ret=encall_switch_type_i(global_eid,&re,counter,intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,charArray,charTail,longArray,longTail,byteArray,byteTail,uuid);
	HotCall_requestCall( &hotEcall,requestedCallID, &counter,NULL,0,NULL,0,NULL,0,NULL,0,NULL,0,NULL,0,uuid,NULL,&reb);	
	//HotCall_requestCall( &hotEcall,requestedCallID, &counter,intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,charArray,charTail,longArray,longTail,byteArray,byteTail,uuid,NULL,&reb);
	//printf("branch over\n");
	
	//env->ReleaseIntArrayElements(jintArray,body_i, 0);
	
	
		

	
//printf("branch over reb=%d\n",reb);
//	if(env -> ExceptionOccurred()){
//		printf(" branch ExceptionOccurred\n");
//		if(env -> MonitorExit(obj)!= JNI_OK);
//		return 0;
//	}
	//branch_ecall++;
	re = reb;

	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("branch exit wrong \n");	
	return re;

}

JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_commitUpdate
  (JNIEnv *env, jclass obj, jlong counter, jintArray jintArray, jint intTail, jdoubleArray jdoubleArray, jint doubleTail, jfloatArray jfloatArray, jint floatTail,jlongArray jlongArray, jint longTail, jcharArray jcharArray, jint charTail,jbyteArray jbyteArray, jint byteTail, jstring uuidstring, jstring ouuidstring, jstring cuuidstring){


	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("update enter wrong \n");

//printf("go to update line=%ld\n",counter);
unum++;
//printf("updanum=%ld\n",unum);


//printf("%d %d\n",intTail,doubleTail);
	int* intArray = NULL;
	double* doubleArray = NULL;
	float* floatArray = NULL;
	long* longArray = NULL;
	char* charArray = NULL;
	char* byteArray = NULL;

	if(intTail > 0){
		intArray = new int[intTail];
	}
	if(doubleTail > 0){
		doubleArray = new double[doubleTail];
	}
	if(floatTail > 0){
		floatArray = new float[floatTail];
	}			
	if(longTail > 0){
		longArray = new long[longTail];
	}
	if(charTail > 0){
		charArray = new char[charTail];
	}
	if(byteTail > 0){
		byteArray = new char[byteTail];
	}
	if(intTail > 0){
		intArray = new int[intTail];
		jint *body_i = env->GetIntArrayElements(jintArray, 0);
		for (int i=0; i<intTail; i++)
		{
			intArray[i] = body_i[i];
		}
		env->ReleaseIntArrayElements(jintArray, body_i, 0);
	}
	if(doubleTail > 0){
		doubleArray = new double[doubleTail];
		jdouble *body_d = env->GetDoubleArrayElements(jdoubleArray, 0);
		for (int i=0; i<doubleTail; i++)
		{
			doubleArray[i] = body_d[i];
		}
		env->ReleaseDoubleArrayElements(jdoubleArray, body_d, 0);
	}
	if(floatTail > 0){
		floatArray = new float[floatTail];
		jfloat *body_f = env->GetFloatArrayElements(jfloatArray, 0);
		for (int i=0; i<floatTail; i++)
		{
			floatArray[i] = body_f[i];
		}
		env->ReleaseFloatArrayElements(jfloatArray,body_f, 0);
	}
	if(longTail > 0){
		longArray = new long[longTail];
		jlong *body_l = env->GetLongArrayElements(jlongArray, 0);
		for (int i=0; i<longTail; i++)
		{
			longArray[i] = body_l[i];
		}
		env->ReleaseLongArrayElements(jlongArray,body_l, 0);

	}
	if(charTail > 0){
		charArray = new char[charTail];
		jchar *body_c = env->GetCharArrayElements(jcharArray, 0);
		for (int i=0; i<charTail; i++)
		{
			charArray[i] = body_c[i];
		}
		env->ReleaseCharArrayElements(jcharArray,body_c , 0);
	}
	if(byteTail > 0){
		byteArray = new char[byteTail];
		jbyte *body_b = env->GetByteArrayElements(jbyteArray, 0);
		for (int i=0; i<byteTail; i++)
		{
			byteArray[i] = body_b[i];
		}
		env->ReleaseByteArrayElements(jbyteArray,body_b, 0);
	}

	int re=-97;

	const char* uuidBuf = env->GetStringUTFChars(uuidstring, false);
	char uuid[33] = {0};
	strncpy(uuid,uuidBuf,32);
	env->ReleaseStringUTFChars(uuidstring,uuidBuf);

	const char* ouuidBuf = env->GetStringUTFChars(ouuidstring, false);
	char ouuid[33] = {0};
	strncpy(uuid,ouuidBuf,32);
	env->ReleaseStringUTFChars(ouuidstring,ouuidBuf);


	const char* cuuidBuf = env->GetStringUTFChars(cuuidstring, false);
	char cuuid[33] = {0};
	strncpy(cuuid,cuuidBuf,32);
	env->ReleaseStringUTFChars(cuuidstring,cuuidBuf);


	// char cuuid[33] = {0};
	// strncpy(cuuid,buf+32,32);
//printf("uuid=%s cuuid=%s\n",uuid,cuuid);

  
	//sgx_status_t ret=encall_switch_type_i(global_eid,&reu,counter,intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,charArray,charTail,longArray,longTail,byteArray,byteTail,uuid);
	HotCall_requestCall( &hotEcall,requestedCallID3,&counter,intArray,intTail,doubleArray,doubleTail,floatArray,floatTail,charArray,charTail,longArray,longTail,byteArray,byteTail,uuid,ouuid,cuuid,&reu);
//printf("update over\n");
	
	if(intTail > 0){
		delete[] intArray;
	}

	if(doubleTail > 0){
		delete[] doubleArray;
	}
	if(floatTail > 0){
		delete[] floatArray;
	}			
	if(longTail > 0){
		delete[] longArray;
	}
	if(charTail > 0){
		delete[] charArray;
	}
	if(byteTail > 0){
		delete[] byteArray;
	}

	//int rei=-977;
	//if(reu == 1000){
	//	rei = 1;
	//}else{
	//	printf("update error!!! in app.cpp rei=%d\n",rei);
	//	rei = 0;
	//}

	
//	if(env -> ExceptionOccurred()){
//		printf(" update ExceptionOccurred\n");
//		if(env -> MonitorExit(obj)!= JNI_OK);
//		return 0;
//	}
	//update_ecall++;
	
	re = reu;
//printf("out update\n");	
	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("update exit wrong \n");

	return re;
	
}

JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_initValue
  (JNIEnv *env, jclass obj,jstring uuidstring,jstring calluuidstring, jlong lineno){
	//hashmap insert

	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("initvalue enter wrong \n");

//printf("go to init\n");
inum++;
//printf("initnum=%ld\n",num);
//printf("11112\n");
	const char* buf = env->GetStringUTFChars(uuidstring, false);
	strcpy(uuid3,buf);
	env->ReleaseStringUTFChars(uuidstring, buf);
//printf("11113\n");
	if(calluuidstring == NULL){
		//printf("11116\n");
		//encall_varible(global_eid,uuid3,NULL,lineno);
		HotCall_requestCall( &hotEcall3,requestedCallID1,&lineno,NULL,0,NULL,0,NULL,0,NULL,0,NULL,0,NULL,0,uuid3,NULL,&tem);
	}else{
		const char* callbuf = env->GetStringUTFChars(calluuidstring, false);
//printf("11114\n");
	//char uuid[33] = {0};
	
		strcpy(uuid3c,callbuf);
		env->ReleaseStringUTFChars(calluuidstring, callbuf);
	//int intArray[ArrayLen];
	//jint *body_i = env->GetIntArrayElements(jintArray, 0);
	//memcpy(intArray,body_i,8);
	//int reinitvalue;
//printf("2222\n");
		//encall_varible(global_eid,uuid3,uuid3c,lineno);
		HotCall_requestCall( &hotEcall3,requestedCallID1,&lineno,NULL,0,NULL,0,NULL,0,uuid3c,32,NULL,0,NULL,0,uuid3,NULL,&tem);

	//env->ReleaseIntArrayElements(jintArray, body_i, 0); 
	}
//printf("init over\n");	
	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("initvalue exit wrong \n");
	return 1;
}

JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_deleteValue
  (JNIEnv *env, jclass obj, jstring uuidstring,jstring deletecuuid,jlong status){


	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("deletevalue enter wrong \n");
//printf("go to delete\n");
dnum++;
	const char* buf = env->GetStringUTFChars(uuidstring, false);
	//char uuid[33] = {0};
	strcpy(uuid3,buf);
	//deletevalue_ecall++;
	//printf("[delete]status=%ld\n",status);
	if(status == 0){
	//encall_deleteValue(global_eid,uuid);
		HotCall_requestCall( &hotEcall3,requestedCallID2, &status,NULL,0,NULL,0,NULL,0,NULL,0,NULL,0,NULL,0,uuid3,NULL,&tem);
	}else if(status == 1){
		//printf("[delete]status=%ld",status);
		const char* callbuf = env->GetStringUTFChars(deletecuuid, false);
		strcpy(uuid3c,callbuf);
		env->ReleaseStringUTFChars(deletecuuid, callbuf);
		HotCall_requestCall( &hotEcall3,requestedCallID2, &status,NULL,0,NULL,0,NULL,0,uuid3c,32,NULL,0,NULL,0,uuid3,NULL,&tem);
	}
//printf("delete over\n");
	env->ReleaseStringUTFChars(uuidstring, buf);

//---------------------------------------------------------------------	
	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("deletevalue exit wrong \n");
	return 1;
}

// 原方案
JNIEXPORT void JNICALL Java_invoker_sgx_1invoker_initArray
  (JNIEnv *env, jclass obj, jstring uuidstring, jint index, jint size,jint isSens){
//printf("got to initarray\n");
	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("initArray enter wrong \n");

	const char* buf = env->GetStringUTFChars(uuidstring, false);
	strcpy(uuid,buf);
	env->ReleaseStringUTFChars(uuidstring, buf);

	encall_initArray(global_eid,uuid,index,size,isSens);

//printf("initarray over\n");
	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("initArray exit wrong \n");
	return;
}



JNIEXPORT jintArray JNICALL Java_invoker_sgx_1invoker_commitIntArray
  (JNIEnv *env, jclass obj, jlong counter, jstring uuidstring){
	

	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("initArray enter wrong \n");
//printf("get int[] counter=%ld\n",counter);
	const char* buf = env->GetStringUTFChars(uuidstring, false);
	strcpy(uuid,buf);
	env->ReleaseStringUTFChars(uuidstring, buf);

	int size = 0;
	
	//first return array size
	encall_getArraySize(global_eid,&size,counter,uuid);
//printf("int[] size=%d \n",size);
	//printf("size=%d\n",size);
	int *re = new int[size];
	//second return the array
	encall_getIntArray(global_eid,re,size,counter,uuid);
	
/*	if(counter == 22L){
		for(int i=0;i<size;i++){
			printf("[App get int array]re[%d]=%d\n",i,re[i]);
		}
	}
*/

 	jintArray result = env->NewIntArray(size);
 	if (result == NULL) {
	    printf("APP.CPP OUT OF MEMORY!!!!!!!!\n");
 	    return NULL; /* out of memory error thrown */
 	}
	jint *get_i = env->GetIntArrayElements(result, 0);
	for(int i=0;i<size;i++){
			get_i[i] = re[i];
	}
	env->ReleaseIntArrayElements(result, get_i, 0);
	// move from the temp structure to the java structure
 	//env->SetIntArrayRegion(result, 0, size, re);
	delete[] re;
//printf("out int[] \n");
	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("initArray exit wrong \n");

 	return result;
}

JNIEXPORT jdoubleArray JNICALL Java_invoker_sgx_1invoker_commitDoubleArray
  (JNIEnv *env, jclass obj, jlong counter, jstring uuidstring){
	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("initArray enter wrong \n");
//printf("get double[] counter=%ld\n",counter);
	const char* buf = env->GetStringUTFChars(uuidstring, false);
	strcpy(uuid,buf);
	env->ReleaseStringUTFChars(uuidstring, buf);
	int size = 0;
	
	//first return array size
	encall_getArraySize(global_eid,&size,counter,uuid);

	//printf("d size=%d\n",size);
	double *re = new double[size];
	//second return the array
	encall_getDoubleArray(global_eid,re,size,counter,uuid);
	
	//printf("%ld out %lf %lf\n",counter,re[0],re[1]);

 	jdoubleArray result = env->NewDoubleArray(size);
 	if (result == NULL) {
	    printf("APP.CPP OUT OF MEMORY!!!!!!!!\n");
 	    return NULL; /* out of memory error thrown */
 	}

	// move from the temp structure to the java structure
	jdouble *get_d = env->GetDoubleArrayElements(result, 0);
	for(int i=0;i<size;i++){
			get_d[i] = re[i];
	}
	env->ReleaseDoubleArrayElements(result, get_d, 0);
 	//env->SetDoubleArrayRegion(result, 0, size, re);
	delete[] re;
//printf("out double[] \n");
	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("initArray exit wrong \n");
 	return result;
}

// 原方案
JNIEXPORT jint JNICALL Java_invoker_sgx_1invoker_commitUpdateMutliArray
  (JNIEnv *env, jclass obj, jlong counter, jstring uuidstring, jstring cuuid){

	if(env -> MonitorEnter(obj)!= JNI_OK)
		printf("initArray enter wrong \n");
//printf("go to update mutli array \n");
	const char* buf = env->GetStringUTFChars(uuidstring, false);
	strcpy(uuid3,buf);
	env->ReleaseStringUTFChars(uuidstring, buf);

	const char* callbuf = env->GetStringUTFChars(cuuid, false);
	strcpy(uuid3c,callbuf);
	env->ReleaseStringUTFChars(cuuid, callbuf);

	encall_initmultiArray(global_eid,counter,uuid3,uuid3c);
//printf("out update mutli array \n");
	if(env -> MonitorExit(obj)!= JNI_OK)
		printf("initArray exit wrong \n");
 	return 1;

}

int SGX_CDECL main(int argc, char *argv[])
{
	clock_t t1,t2,t3,t4;
	t1=clock();
	initialize_enclave();
	t2=clock();
	printf("init time: %lf\n", ((double)(t2 - t1)/CLOCKS_PER_SEC));
	int re = 0;
	int red =99;
	t3=clock();
	t4=clock();
	printf("destory time: %lf\n", ((double)(t4 - t3)/CLOCKS_PER_SEC));
	return 0;
//
//
/*
//encall_invoketable_load(global_eid,&re);
encall_table_load(global_eid,&re);
printf("----------------------------------------------------\n");
encall_varible(global_eid,"xcvbnmjhgfdsaqwertyuioplkjhgfdsa",NULL,0);
encall_initArray(global_eid,"xcvbnmjhgfdsaqwertyuioplkjhgfdsa",60,100);

encall_switch_type_i(global_eid,&re,0,NULL,NULL,NULL,NULL,NULL,NULL,"xcvbnmjhgfdsaqwertyuioplkjhgfdsa");
encall_switch_type_i(global_eid,&re,1,NULL,NULL,NULL,NULL,NULL,NULL,"xcvbnmjhgfdsaqwertyuioplkjhgfdsa");
encall_switch_type_i(global_eid,&re,2,NULL,NULL,NULL,NULL,NULL,NULL,"xcvbnmjhgfdsaqwertyuioplkjhgfdsa");
encall_switch_type_i(global_eid,&re,3,NULL,NULL,NULL,NULL,NULL,NULL,"xcvbnmjhgfdsaqwertyuioplkjhgfdsa");
printf("re3:%d\n",re);
//encall_switch_type_i(global_eid,&re,4,NULL,NULL,NULL,NULL,NULL,NULL,"xcvbnmjhgfdsaqwertyuioplkjhgfdsa");
//printf("re4:%d\n",re);


printf("----------------------------------------------------\n");
encall_varible(global_eid,"qwertyuioplkjhgfdsazxcvbnmnbvcx","xcvbnmjhgfdsaqwertyuioplkjhgfdsa",1);

encall_switch_type_i(global_eid,&re,5,NULL,NULL,NULL,NULL,NULL,NULL,"qwertyuioplkjhgfdsazxcvbnmnbvcx");
encall_switch_type_i(global_eid,&re,6,NULL,NULL,NULL,NULL,NULL,NULL,"qwertyuioplkjhgfdsazxcvbnmnbvcx");
encall_switch_type_i(global_eid,&re,7,NULL,NULL,NULL,NULL,NULL,NULL,"qwertyuioplkjhgfdsazxcvbnmnbvcx");
encall_switch_type_i(global_eid,&re,8,NULL,NULL,NULL,NULL,NULL,NULL,"qwertyuioplkjhgfdsazxcvbnmnbvcx");
encall_switch_type_i(global_eid,&re,9,NULL,NULL,NULL,NULL,NULL,NULL,"qwertyuioplkjhgfdsazxcvbnmnbvcx");//105
encall_switch_type_i(global_eid,&re,10,NULL,NULL,NULL,NULL,NULL,NULL,"qwertyuioplkjhgfdsazxcvbnmnbvcx");
encall_switch_type_i(global_eid,&re,11,NULL,NULL,NULL,NULL,NULL,NULL,"qwertyuioplkjhgfdsazxcvbnmnbvcx");
printf("re 107:%d\n",re);
encall_deleteValue(global_eid,"qwertyuioplkjhgfdsazxcvbnmnbvcx");
encall_deleteValue(global_eid,"xcvbnmjhgfdsaqwertyuioplkjhgfdsa");

hotEcall.data               = &data;
	hotEcall.intArray               = intArray; 
	hotEcall.doubleArray               = doubleArray;
	hotEcall.floatArray               = floatArray;
	hotEcall.charArray               = charArray;
	hotEcall.longArray               = longArray;
	hotEcall.byteArray               = byteArray;
        globalEnclaveID = global_eid;
        pthread_create(&hotEcall.responderThread, NULL, EnclaveResponderThread, (void*)&hotEcall);


    int intArray[100] = {0,1,2,3,4,5,6,7,8};
    long longArray[100] = {0,1,2,3,4,5,6,7,8};
    double doubleArray[100] = { 0.1,1.1,2.1,3.1,4.1,5.1,6.1,7.1,8.1,9.1 };
    float floatArray[100] = { 0.1,1.1,2.1,3.1,4.1,5.1,6.1,7.1,8.1,9.1 };
    char charArray[100] = {'a','a','c','d','e','f','g','h','i','j'};
    char byteArray[100] = {'0','1','2','3','4','5','6','7','8','9'}; 
int counter = 1;
HotCall_requestCall( &hotEcall,requestedCallID, &counter,intArray,doubleArray,floatArray,charArray,longArray,byteArray);
//void* s = hotEcall.re;
//int *x = (int*)s;
printf("rei=%d\n",rei);
StopResponder( &hotEcall );
*/

//int k[] = {1,0,0,0,0,0,0};
/*
int re;
encall_table_load(global_eid,&re);

int re_i=999;
double re_d=0.0;
char re_c=' ';

int red;

encall_switch_type_c(global_eid,&re_c,0,int_array,10,double_array,10,float_array,10,char_array,10,long_array,10,byte_array,10);
//printf("re_c=%c\n",re_c);
encall_switch_type_i(global_eid,&re_i,1,int_array,10,double_array,10,float_array,10,char_array,10,long_array,10,byte_array,10);
//printf("re_i1=%d\n",re_i);
encall_switch_type_i(global_eid,&re_i,2,int_array,10,double_array,10,float_array,10,char_array,10,long_array,10,byte_array,10);
//printf("re_i2=%d\n",re_i);
encall_switch_type_i(global_eid,&re_i,3,int_array,10,double_array,10,float_array,10,char_array,10,long_array,10,byte_array,10);
//printf("re_i3=%d\n",re_i);
encall_switch_type_i(global_eid,&re_i,4,int_array,10,double_array,10,float_array,10,char_array,10,long_array,10,byte_array,10);
//printf("re_i4=%d\n",re_i);
encall_switch_type_i(global_eid,&re_i,5,int_array,10,double_array,10,float_array,10,char_array,10,long_array,10,byte_array,10);
//printf("re_i5=%d\n",re_i);
encall_switch_type_i(global_eid,&re_i,6,int_array,10,double_array,10,float_array,10,char_array,10,long_array,10,byte_array,10);
//printf("re_i6=%d\n",re_i);
*/
//encall_varible(global_eid,k,7);
//encall_deleteValue(global_eid,&red);
/*
encall_switch_type_i(global_eid,&re_i,1,int_array,10,double_array,10,float_array,10,char_array,10,long_array,10,byte_array,10);
for(int i=2;i<5;i++){
	encall_varible(global_eid,k,7);
	encall_switch_type_i(global_eid,&re_i,i,int_array,10,double_array,10,float_array,10,char_array,10,long_array,10,byte_array,10);
	encall_deleteValue(global_eid,&red);
}
encall_deleteValue(global_eid,&red);
*/

}