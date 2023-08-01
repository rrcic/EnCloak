#include <unistd.h>
#include <string.h>
#include <sgx_cpuid.h>
#include <stdlib.h>
#include <string>
#include <string.h>
#define Table_Len 10000
#define MAX 100
#include "io/fcntl.h"
#include "io/mman.h"
#include "io/stat.h"
#include "io/stdio.h"
#include "io/stdlib.h"
#include "io/time.h"
#include "io/unistd.h"
#include <sgx_tcrypto.h>
#include <ctype.h>
#include <map>
#include<time.h>
#include<ctime>
using namespace std;
#include "Enclave.h"
#include "Enclave_t.h"  /* print_string */
#include "common.h"


clock_t t1,t2;
void printf(const char *fmt, ...)
{
    char buf[BUFSIZ] = {'\0'};
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(buf, BUFSIZ, fmt, ap);
    va_end(ap);
    ocall_print_string(buf);
}

//----------------struct--------------
// 八元组
struct Table_meta{
	int type;
	int p1;//index 0-100 from array  ,100-200 hash-int
	int p1_i; 
	int p2;
	int p2_i;
	int op; 
	int para_name;
	int para_i;
};

// function node
typedef struct Node {
	int v_int[20];
	double v_double[20];
	float v_float[10];
	char v_char[20];
	int v_byte[20];
	long v_long[20];
	
	char calluuid[33];	// 调用者uuid

	char array[10][33];	// array[0] = "某个32位uuid"， 表示0号形参是从该uuid的caller函数中传递而来的
	int  arrayIndex[10];	// 形参变量在caller中的编号
	long lineNo;

	int re[3];
}*SNODE, Node;

typedef struct ArrayNode2{

	IntArrayNode * int_arrNodes[30];
	CharArrayNode * char_arrNodes[30];
	DoubleArrayNode * double_arrNodes[30];
	int double_sz;
	int int_sz;
	int char_sz;
}*ANODE2,ArrayNode2;

// 新增0712
typedef struct ClassNode {
	int v_int[20];
	double v_double[20];
	float v_float[10];
	char v_char[20];
	int v_byte[20];
	long v_long[20];
}*CNODE, ClassNode;

typedef struct ObjectNode {
	int v_int[20];
	double v_double[20];
	float v_float[10];
	char v_char[20];
	int v_byte[20];
	long v_long[20];
}*ONODE, ObjectNode;


// 原方案，弃用
typedef struct ArrayNode {
	int* arr_int[10];
	double* arr_double[10];
	char* arr_char[10];
	long* arr_long[10];
	int* arr_byte[10];

	int intsize[10];
	int doublesize[10];
	int charsize[10];
	int longsize[10];
	int bytesize[10];
}*ANODE, ArrayNode;

// 原方案，弃用
typedef struct MultiArrayNode{
	int arr_int[10][100];
	double arr_double[10][100];
	long arr_long[10][100];

	int intsize[10];
	int doublesize[10];
}*MNODE, MultiArrayNode;

// 原方案，弃用
typedef struct PublicVariableNode{
	
	int v_i;	
	double v_d;
	float v_f;
	char v_c;
	int v_b;
	long v_l;	

	int arr_int[10];
	double arr_double[10];	
	long arr_long[10];	
	
	int arr_multi_int[100][100];
	double arr_multi_double[100][100];
	long arr_multi_long[2][2];
	int intsize;
	int doublesize;
	int longsize;

	int intmultisize[10];
	int doublemultisize[10];
	int longemultisize[10];
}*PNODE, PublicVariableNode;



//------------==================--------拷贝而来的HASHMAP的具体实现，可略过-----------========================-------------------
template<class Key, class Value>
class HashNode
{
public:
	Key    _key;
	Value  _value;
	HashNode *next;

	HashNode(Key key, Value value)
	{
		_key = key;
		_value = value;
		next = NULL;
	}
	~HashNode()
	{

	}
	HashNode& operator=(const HashNode& node)
	{
		_key = node.key;
		//_value = node.key;
		_value = node.value;
		next = node.next;
		return *this;
	}
};

template <class Key, class Value, class HashFunc, class EqualKey>
class HashMap
{
public:
	HashMap(int size);
	~HashMap();
	bool insert(const Key& key, const Value& value);
	bool del(const Key& key);
	Value& find(const Key& key);
	Value& operator [](const Key& key);

private:
	HashFunc hash;
	EqualKey equal;
	HashNode<Key, Value> **table;
	unsigned int _size;
	Value ValueNULL;
};


template <class Key, class Value, class HashFunc, class EqualKey>
HashMap<Key, Value, HashFunc, EqualKey>::HashMap(int size) : _size(size)
{
	hash = HashFunc();
	equal = EqualKey();
	table = new HashNode<Key, Value> *[_size];
	for (unsigned i = 0; i < _size; i++)
		table[i] = NULL;
}



template <class Key, class Value, class HashFunc, class EqualKey>
HashMap<Key, Value, HashFunc, EqualKey>::~HashMap()
{
	for (unsigned i = 0; i < _size; i++)
	{
		HashNode<Key, Value> *currentNode = table[i];
		while (currentNode)
		{
			HashNode<Key, Value> *temp = currentNode;
			currentNode = currentNode->next;
			delete temp;
		}
	}
	delete table;
}


template <class Key, class Value, class HashFunc, class EqualKey>
bool HashMap<Key, Value, HashFunc, EqualKey>::insert(const Key& key, const Value& value)
{
	int index = hash(key) % _size;
	HashNode<Key, Value> *node = new HashNode<Key, Value>(key, value);
	node->next = table[index];
	table[index] = node;
	return true;
}
template <class Key, class Value, class HashFunc, class EqualKey>
bool HashMap<Key, Value, HashFunc, EqualKey>::del(const Key& key)
{
	unsigned index = hash(key) % _size;
	HashNode<Key, Value> * node = table[index];
	HashNode<Key, Value> * prev = NULL;
	while (node)
	{
		if (node->_key == key)
		{
			if (prev == NULL)
			{
				table[index] = node->next;
			}
			else
			{
				prev->next = node->next;
			}
			delete node;
			return true;
		}
		prev = node;
		node = node->next;
	}
	return false;
}


template <class Key, class Value, class HashFunc, class EqualKey>
Value& HashMap<Key, Value, HashFunc, EqualKey>::find(const Key& key)
{
	unsigned  index = hash(key) % _size;
	if (table[index] == NULL){
		return ValueNULL;
	}
	else
	{	
		HashNode<Key, Value> * node = table[index];
		//printf("go in key\n");
		
		while (node)
		{
			//cout << "node->_key = " << node->_key << endl;
			
			if (node->_key == key){
				//printf(">>>>>>>>>>>>>find equal key<<<<<<<<<<<<<\n");
				//printf("key is :%ld\n",key);
				//printf("node key is :%ld\n",node->_key);
				return node->_value;
			}
				
			node = node->next;
		}
		//printf("key is :%d\n",key);
		//printf("node key is :%d\n",node->_key);
		printf("key is not find! index :%u\n",index);
		//cout << "key is not find!" << endl;
		return ValueNULL;
	}
}


template <class Key, class Value, class HashFunc, class EqualKey>
Value& HashMap<Key, Value, HashFunc, EqualKey>::operator [](const Key& key)
{
	return find(key);
}

class HashFunc
{
public:
	int operator()(const string & key)
	{
		int hash = 0;
		for (int i = 0; i < key.length(); ++i)
		{
			hash = hash << 7 ^ key[i];
		}
		return (hash & 0x7FFFFFFF);


		//return 0;
	}
};

class EqualKey
{
public:
	bool operator()(const string & A, const string & B)
	{
		if (A.compare(B) == 0)
			return true;
		else
			return false;
	}
};

// 弃用
HashMap<string, ANODE, HashFunc, EqualKey> hashmapArray(30); // HashMap
HashMap<string, MNODE, HashFunc, EqualKey> hashmapMultiArray(1); // HashMap
HashMap<string, PNODE, HashFunc, EqualKey> hashmapPublicV(30); // HashMap

HashMap<string, SNODE, HashFunc, EqualKey> hashmap(30);
HashMap<string, ANODE2, HashFunc, EqualKey> hashmapArray2(30);
HashMap<string, ONODE, HashFunc, EqualKey> hashmapMemberVariables(30);
HashMap<string, CNODE, HashFunc, EqualKey> hashmapStaticMemberVariables(30);
HashMap<string, ANODE2, HashFunc, EqualKey> hashmapMemberArray(30);
HashMap<string, ANODE2, HashFunc, EqualKey> hashmapStaticMemberArray(30);


//------------==================--------HASHMAP-----------========================-------------------


//--------------------------------------------------------------

//char file[500]="/home/xidian/CF/MatrixEncrypt/SGXindex1";


char updateFile[50]="/tmp/mergeIndex";


char file[50]="/tmp/SGXindex";
int hash_int[Table_Len];
double hash_double[Table_Len];
float hash_float[Table_Len];
char hash_char[Table_Len];
long hash_long[Table_Len];
char hash_byte[Table_Len];
int *table=(int*)malloc(sizeof(int)*10000);
int hash_index[Table_Len]; //for constant if it is int or double...

//invoke file
char invokefile[50]="/tmp/SGXinvoke";
int hash_invoke_int[Table_Len];
double hash_invoke_double[Table_Len];
char hash_invoke_char[Table_Len];
long hash_invoke_long[Table_Len];
int hash_invoke_byte[Table_Len];
int *invoketable=(int*)malloc(sizeof(int)*1000);
int hash_invoke_index[Table_Len]; //for constant if it is int or double...
int lineIndex[100];


// 八元组解密
int ecall_ctr_decrypt(uint8_t *sql, 
	const char *sgx_ctr_key, uint8_t *p_dst,int len)    //ecall_ctr_decrypt(c,key_t,ppp,64);
{
	const uint32_t src_len = len;
	uint8_t p_ctr[16]= {'0'};
	const uint32_t ctr_inc_bits = 128;
	uint8_t *sgx_ctr_keys = (uint8_t *)malloc(16*sizeof(char));
	memcpy(sgx_ctr_keys,sgx_ctr_key,16);

	//ocall_print_int(len);
	//ocall_print_string((const char*)sgx_ctr_key);
	sgx_status_t rc;
	uint8_t *p_dsts2 = (uint8_t *)malloc(src_len*sizeof(char));
	//uint8_t *p_dsts=
	rc = sgx_aes_ctr_decrypt((sgx_aes_gcm_128bit_key_t *)sgx_ctr_keys, sql, src_len, p_ctr, ctr_inc_bits, p_dsts2);

	for(int i=0; i<src_len; i++){
		p_dst[i] = p_dsts2[i];
		//ocall_print_string(stdout,"%c", p_dsts2[i]);
	}

	free(sgx_ctr_keys);
	return 0;
}


// 读取数据
int encall_hash_readin(char* buf,long line)
{
	char buffer[50];
	//return -10;
	char c=*buf;
	switch(c)
	{
		case 'i':strncpy(buffer,buf+4,44);//int_
			int int_data;
			int_data=atoi(buffer);
			hash_int[line]=int_data;
			hash_index[line] = 1;
			break;
		case 'd':strncpy(buffer,buf+7,44);//double_
			double double_data;
			double_data=atof(buffer);
			hash_double[line]=double_data;
			hash_index[line] = 2;
			break;
		case 'f':strncpy(buffer,buf+6,44);//float_
			float float_data;
			float_data=atof(buffer);
			hash_float[line]=(float)float_data;
			hash_index[line] = 3;
			break;
		case 'c':strncpy(buffer,buf+5,44);//char_
			char char_data;
			char_data=*buffer;
			hash_char[line]=char_data;
			hash_index[line] = 4;
			break;
		case 'l':strncpy(buffer,buf+5,44);//long_
			long long_data;
			long_data=atol(buffer);
			hash_long[line]=long_data;
			hash_index[line] = 5;
			break;
		case '\0':
			break;
		default:
			hash_int[line]=0;
			hash_double[line]=0;
			hash_float[line]=0;
			hash_char[line]=0;
			hash_long[line]=0;
			return -6;
	}
	return 1;
}
// 读取数据
int encall_hash_invoke_readin(char* buf,long line)
{
	char buffer[50];
	//return -10;
	char c=*buf;
	ocall_print_string("read value-------------------------\n");
	switch(c)
	{
		case 'i':strncpy(buffer,buf+4,44);//int_
			int int_data;
			int_data=atoi(buffer);
			hash_invoke_int[line]=int_data;
			hash_invoke_index[line] = 1;
			break;
		case 'd':strncpy(buffer,buf+7,44);//double_
			double double_data;
			double_data=atof(buffer);
			hash_invoke_double[line]=double_data;
			hash_invoke_index[line] = 2;
			break;
		case 'c':strncpy(buffer,buf+5,44);//char_
			char char_data;
			char_data=*buffer;
			hash_invoke_char[line]=char_data;
			hash_invoke_index[line] = 4;
			break;
		case 'l':strncpy(buffer,buf+5,44);//long_
			printf("$$$$$$$$$$$$$$$$$ %s\n", buffer);
			long long_data;
			long_data=atol(buffer);
			hash_invoke_long[line]=long_data;
			hash_invoke_index[line] = 5;
			break;
		case '\0':
			break;
		default:
			return -6;
	}
	return 1;
}

// 解析数据
Table_meta get_table_meta(long Line)
{
	Table_meta meta;
	meta.type=*(table+Line*8);
	meta.p1=*(table+Line*8+1);
	meta.p1_i=*(table+Line*8+2);
	meta.p2=*(table+Line*8+3);
	meta.p2_i=*(table+Line*8+4);
	meta.op=*(table+Line*8+5);
	meta.para_name=*(table+Line*8+6);
	meta.para_i=*(table+Line*8+7);
	return meta;
}
char ret[50000];
long ret_len=0;
long g_line_num=0;

// 根据行号分割文件
int split_file(int isIndex)
{
	char line[50]={0};
	int k=0;
	long line_num=0;
	ocall_print_string("splitting ret_len:\n");
	ocall_print_long(ret_len);

	
	for(long i=0;i<ret_len;i++){
		//printf("i:%d, %c \n",i+1,ret[i]);
		if(ret[i]=='\n'){
			//printf("BF erl line_num %ld \n",line_num);
			line[k]=0;
			if(k==0){
				continue;
			}

//printf("n i: %d %d %ld %d\n",i,k,line_num,isIndex);
			//printf("next linde:%s k: %d line_num:%ld\n",line,k,line_num);
			encall_read_line(line,k,line_num,isIndex);
			line_num++;
			//printf("AF erl line_num %ld \n",line_num);
			k=0;
		}else{
			line[k]=ret[i];
			//printf("line k: %c \n",line[k]);
			k++;
		}
	}
	g_line_num=line_num;	
	printf("line_num1: %ld \n",line_num);
	ret_len = 0;
	g_line_num = 0;
	//printf("line_num2: %ld \n",line_num);
	return line_num;
}

map<int,int> mymap;

//read updateIndex file to hashmapUpdateIndex
int handleline(char * text) {

    //printf("%s\n",text);
    char *p; 
    p = strtok(text, ",");
    bool flag = true;
    char *key;
    while(p){  
	    //printf("%s\n", p); 
	    
	
        if(flag){
		//printf("key=%s\n",p);
		key = p;
		flag=false;
    	}else{
		mymap[atoi(key)]=atoi(p);
	    	//printf("value=%s\n",p);
	    	flag= true;
	}
	//printf("%s\n",key);
	p = strtok(NULL, ",");  
	   
    }
    return 0;
}

void read_update_index_file()
{
	

	
	int reout=open(updateFile,O_RDONLY,S_IRUSR);

	//printf("reout:%d\n",reout);
//------------read out
	long l=0;
	char sss[MAX];
	int k=0;
	memset(sss,0,MAX);
	unsigned char c[MAX];
	//while(!reout.eof()){
	long loop2=0;
	long loop=0;
	while(1){
		l=read(reout,c,64);                                                //????????
	
		if(l<64){
			break;
		}
		if(64==l){
			c[64]=0;
			for(int i=0;i<l-1;i++){
				if(c[i]=='\n'){
				//	printf(",");
					sss[k++]=',';
				}else{
					//printf("%c",c[i]);
					sss[k++]=c[i];
				}
			}
		
			l=0;
			memset(c,0,65);
		}
	}
	if(l<64){
		c[l]=0;
		for(int i=0;i<l-1;i++){
	
			if(c[i]=='\n'){
			//	printf(",");
				sss[k++]=',';
			}else{
				//printf("%c",c[i]);
				sss[k++]=c[i];
			}
		}
		printf("\n");
		handleline(sss);
	
		l=0;
	}
	
}
//end read updatefile

int read_table(char* file,int isIndex)
{
	
	memset(ret,0,50000);
	char* key_t="1234567812345678";

	int reout=open(file,O_RDONLY,S_IRUSR);

	printf("reout:%d\n",reout);
	//printf("isIndex:%d\n",isIndex);
//------------read out
	long l=0;
	unsigned char sss[MAX];

	memset(sss,0,MAX);
	unsigned char c[MAX];
	//while(!reout.eof()){
	long loop2=0;
	long loop=0;
	while(1){
		loop++;
		if(loop%1000==0){
			sleep(0);
		}
		//reout.get(c);
		l=read(reout,c,64);                                                //????????
		//ocall_print_long(l);
		if(l<64){
			break;
		}
		
		//sss[l]=(unsigned char)c;
		//l++;
		if(64==l){
			c[64]=0;
			unsigned char ppp[MAX];
			memset(ppp,0,MAX);
			//ocall_print_string((const char*)c);
			ecall_ctr_decrypt(c,key_t,ppp,64);
			//ocall_print_string((const char*)ppp);
			for(int i=0;i<l;i++){
				//ocall_print_string("s");
				strncat(ret,(const char*)&ppp[i],1);
				//ocall_print_string("e");
			}
			ret_len=ret_len+l;
			l=0;
			//ocall_print_long(ret_len);
			memset(c,0,65);
		}
	}
	if(l<64){
		//printf("\n");
		//printf("Coming to less 64byte %d\n",l);
		
		c[l]=0;
		unsigned char ppp[MAX];
		memset(ppp,0,MAX);
		ecall_ctr_decrypt(c,key_t,ppp,l);
		//ocall_print_string((const char*)ppp);
		for(int i=0;i<l;i++){
			strncat(ret,(const char*)&ppp[i],1);
		}
		ret_len=ret_len+l;
		l=0;
		//ocall_print_long(ret_len);
	}
	//ocall_print_string("read ok before splite\n");
	//printf("read ok before splite ret_len:%d\n",ret_len);
	int lineno = split_file(isIndex);
	//printf("lineno:%d\n",lineno);
	//ocall_print_string("read_table ok\n");
	//close(reout);
	return lineno;
}

int encall_table_load(void)
{
	
	//printf("printf index once\n");
	printf("Start to write the hashmap about updateIndex\n");
	//clock_t start,end;
	//start = clock();
	read_update_index_file();
	//end = clock();
	//printf("read updateindex file time:%lf\n",((double)(end - start)/CLOCKS_PER_SEC));
	//printf("Write end!\n");
	//long s=0;
	//int* msgs=(int*)malloc(sizeof(int)*Table_Len);
	//memset(msgs,'\0',sizeof(int)*Table_Len);
	int lineno = read_table(file,1);
	//ocall_print_string("read index ok\n");
	//printf("after read table lineno = %d\n",lineno);

	//for test 0505/2020
	/*for(int i=1;i<=lineno;i++){
		printf("%d ",table[i-1]);
		if (i % 8 == 0){
			printf("\n");
		}
	}*/

	memset(invoketable, -1, sizeof(invoketable));
	lineno = read_table(invokefile,0);
	ocall_print_string("invoke read ok\n");
	/*for(int i=1;i<=lineno;i++){
		printf("%d ",invoketable[i-1]);
		if (i % 3 == 0){
			printf("\n");
		}
	}*/
	memset(lineIndex, -1, sizeof(lineIndex));
	//set lineIndex
	int temp = 0;
	for(int j=0;j<lineno;j++){
		if(invoketable[j]==0 && j % 3 ==0){
			lineIndex[temp] = j;
			temp++;
		}
	}

	return 1;
}


int encall_read_line(char* in_buf,int buf_len,long line,int isIndex)
{
	//printf("line=%s\n",line);
	int read_num=0;
	if(*in_buf>=48 && *in_buf<=57){// number
		read_num=atoi(in_buf);
	}else if(*in_buf == 45){
		read_num=atoi(in_buf);
	}else if (!strncmp(in_buf,"call_", 5)){ //call_
		char buffer[50];
		strncpy(buffer,in_buf+5,44);
		int call = atoi(buffer);
		read_num = call;

	}else if (!strncmp(in_buf,"re", 2)){ 
		read_num = -2;
	}else{
		//int in_flag=999; //int_0 double_2.5  
		read_num=0-line;
		//printf("%d\n",read_num);
		if(isIndex == 1){
			encall_hash_readin(in_buf,line);
		}else{
			encall_hash_invoke_readin(in_buf,line);	
		}
	}
	//printf("read_num:%d\n",read_num);
	if(isIndex == 1){
		table[line]=read_num;
	}else{
		//printf("invoke %ld %d\n",line,read_num);
		invoketable[line] = read_num;
	}
	//Enclave_Table_length++;

	//printf("over\n");
	return 0;
}




//-------------hotcall---------------------
void EcallStartResponder( HotCall* hotEcall )
{
    //printf("create thread======\n");
    void (*callbacks[1])(void*,void*,int*,int,double*,int,float*,int,char*,int,long*,int,char*,int,char*,char*,char*);
    callbacks[0] = encall_switch_type_branch;
    callbacks[3] = encall_switch_type_update;
    callbacks[4] = encall_switch_type_get_i;
    HotCallTable callTable;
    callTable.numEntries = 1;
    callTable.callbacks  = callbacks;
    //printf("111111111===========\n");
    HotCall_waitForCall( hotEcall, &callTable );
    //void* s = hotEcall -> re;
    //int *x = (int*)s;
    //printf("return num=%d\n",*x);
    //printf("waiting===========\n");
}
/*void EcallStartResponder1( HotCall* hotEcall1 )
{
    void (*callbac[1])(void*,void*,int*,double*,float*,char*,long*,char*,char*);
    callbac[3] = encall_switch_type_update;
    HotCallTable callTable;
    callTable.numEntries = 1;
    callTable.callbac  = callbac;
    HotCall_waitForCall( hotEcall1, &callTable );
}
void EcallStartResponder2( HotCall* hotEcall2 )
{
    void (*callbacks[1])(void*,void*,int*,double*,float*,char*,long*,char*,char*);
    callbacks[0] = encall_switch_type_get_i;
    HotCallTable callTable;
    callTable.numEntries = 1;
    callTable.callbacks  = callbacks;
    HotCall_waitForCall( hotEcall2, &callTable );
}
*/
void EcallStartResponder3( HotCall* hotEcall3 )
{
    void (*callback[1])(void*,char*,char*);
    callback[1] = encall_varible;
    callback[2] = encall_deleteValue;
    HotCallTable callTable;
    callTable.numEntries = 1;
    callTable.callback  = callback;
    HotCall_waitForCall( hotEcall3, &callTable );
}
//-----------------------------------------

// 涉及ANODE，原方案，弃用
void InitArray(ArrayNode *ANODE, int m){
	
	//int k=0;
	//printf("init num:%d",k++);
	//ANODE->arr_int = (int**)malloc(m * sizeof(int*));
	//ANODE->arr_double = (double**)malloc(m * sizeof(double*));
	//ANODE->arr_char = (char**)malloc(m * sizeof(char*));
	//ANODE->arr_long = (long**)malloc(m * sizeof(long*));
	//ANODE->arr_byte = (int**)malloc(m * sizeof(int*));

	for(int i=0;i<m;i++){
		ANODE->arr_int[i] = NULL;
		ANODE->arr_double[i] = NULL;
		ANODE->arr_char[i] = NULL;
		ANODE->arr_long[i] = NULL;
		ANODE->arr_byte[i] = NULL;
	}
}

// 涉及ANODE，原方案，弃用
void initArrayRow(ArrayNode *ANODE,int type, int size) {
	switch (type/10){
		case 7:
			//printf("initArrayRow size=%d\n",size);
			ANODE->arr_int[type % 10] = (int*)malloc(size * sizeof(int));
			memset(ANODE->arr_int[type % 10], 0, size);
			ANODE->intsize[type % 10] = size;
			//printf("after initArrayRow\n");
			break;
		case 8:
			ANODE->arr_double[type % 10] = (double*)malloc(size * sizeof(double));
			memset(ANODE->arr_double[type % 10], 0, size);
			ANODE->doublesize[type % 10] = size;
			break;
		case 10:
			ANODE->arr_char[type % 10] = (char*)malloc(size * sizeof(char));
			memset(ANODE->arr_char[type % 10], 0, size);
			ANODE->charsize[type % 10] = size;
			break;
		case 11:
			ANODE->arr_long[type % 10] = (long*)malloc(size * sizeof(long));
			memset(ANODE->arr_long[type % 10], 0, size);
			ANODE->longsize[type % 10] = size;
			break;
		case 12:
			ANODE->arr_byte[type % 10] = (int*)malloc(size * sizeof(int));
			memset(ANODE->arr_byte[type % 10], 0, size);
			ANODE->bytesize[type % 10] = size;
			break;
		default:
			break;
	}
}
// 释放数组，似乎也是弃用
void FreeArray(ArrayNode *ANODE,int m)
{
	for (int i = 0;i < m;i++) {
		if (ANODE->arr_int[i] != NULL) {
			free(ANODE->arr_int[i]);
		}else {
			break;
		}
	}
	for (int i = 0;i <m;i++) {
		if (ANODE->arr_double[i] != NULL) {
			free(ANODE->arr_double[i]);
		}else{
			break;
		}
	}
	for (int i = 0;i < m;i++) {
		if (ANODE->arr_char[i] != NULL) {
			free(ANODE->arr_char[i]);
		}else {
			break;
		}
	}
	for (int i = 0;i < m;i++) {
		if (ANODE->arr_long[i] != NULL) {
			free(ANODE->arr_long[i]);
		}else {
			break;
		}
	}
	for (int i = 0;i < m;i++) {
		if (ANODE->arr_byte[i] != NULL) {
			free(ANODE->arr_byte[i]);
		}else {
			break;
		}
	}
	free(ANODE->arr_double);
	free(ANODE->arr_int);
	free(ANODE->arr_long);
	free(ANODE->arr_char);
	free(ANODE->arr_byte);
}

// 将调用者caller函数中的形参敏感变量加载到被调用者函数callee中
void encall_varible(void* data,char* uuid,char* calluuid) { //int* k,

	//printf("[INIT] uuid=%s\n",uuid);
	long *data1 = (long*)data;
	long lineNo = *data1;

	SNODE s = (SNODE)malloc(sizeof(Node));

	if(lineNo != 0L){
		//printf("LineNo:%ld calluuid=%s\n",lineNo,calluuid);
		s-> lineNo = lineNo;
		memcpy(s->calluuid,calluuid,32);
		//printf("calluuid = %s\n",s->calluuid);
	
		int start = lineIndex[lineNo-1];
		int end = (lineIndex[lineNo]!=-1)?lineIndex[lineNo]:1000;
		int ii=0;
		int dd=0;
		int cc=0;
		int ll=0;
		int bb=0;
//printf("[B]this method has invokeuuid. start:%d end:%d\n",start,end);
		for(int i=start;i<end;i=i+3){
			int paraindex = invoketable[i];
			int isFromSelf = invoketable[i+1];
			int index = invoketable[i+2];
			if(paraindex == 0 && isFromSelf==0 && index==0) break;//out
			//printf("=paraindex:%d =isFromSelf:%d =index:%d\n",paraindex,isFromSelf,index);
			
			if(isFromSelf == 1 && paraindex !=-2){
				if(index < 0){ //constant
					//printf("=%d is a constant=\n",i);
					//printf("=hash_invoke_index[-index]=%d\n",hash_invoke_index[-index]);
					switch (hash_invoke_index[-index]) {
						case 1:
							s->v_int[ii++] = hash_invoke_int[-index];
							break;
						case 2:
							s->v_double[dd++] = hash_invoke_double[-index];
							break;
						case 4:
							s->v_char[cc++] = hash_invoke_char[-index];
							break;
						case 5:
							s->v_long[ll++] = hash_invoke_long[-index];
							break;
						case 6://????
							printf("[ERROR] I don't meet this problem!\n");
							s->v_byte[bb++] = hash_invoke_byte[-index];
							break;
					}
				}else if(index<100){ //array，没有像constant和variable一样进行深拷贝，index是形参在caller函数中的编号
					//printf("=%d is an array=\n",i);
					memcpy(s->array[paraindex],calluuid,32);			
					s->arrayIndex[paraindex] = index;
					//printf("%s\n",s->array[paraindex]);
					//printf("hashmapArray.find(%s)->arr_int[0][1]=%d\n",s->array[paraindex],hashmapArray.find(s->array[paraindex])->arr_int[0][1]);

				}else if(index>=100){           //variables
					//printf("=%d is a variables=\n",i);
					switch (index/100) {
						case 1:
							s->v_int[ii++] = hashmap.find(calluuid)->v_int[index-100];
							//printf("v_int[%d] = %d\n",index-100,hashmap.find(calluuid)->v_int[index-100]);
							break;
						case 2:
							s->v_double[dd++] = hashmap.find(calluuid)->v_double[index-200];
							break;
						case 4:
							s->v_char[cc++] = hashmap.find(calluuid)->v_char[index-400];
							break;
						case 5:
							s->v_long[ll++] = hashmap.find(calluuid)->v_long[index-500];
							break;
						case 6:
							printf("[ERROR] I don't meet this problem too!\n");
							s->v_byte[bb++] = hashmap.find(calluuid)->v_byte[index-600];
							break;
					}
					
				}		
			}else if(isFromSelf == 2){  //isFromSelf == 0 array
				memset(s->array[paraindex],0,32);
				memcpy(s->array[paraindex],hashmap.find(calluuid)->array[index],32);
				s->arrayIndex[paraindex] = hashmap.find(calluuid)->arrayIndex[index];
			}else{
				//printf("=%d is a return=\n",i);
				s->re[0] = paraindex;
				s->re[1] = isFromSelf;
				s->re[2] = index;
			}
		}
		//printf("[xx]hashmapArray.find(%s)->arr_int[0][1]=%d\n",s->array[0],hashmapArray.find(s->array[0])->arr_int[0][1]);
	}else{
		//printf("[A]this method has no invokeuuid.\n");
	}
	

	//insert
	if(!hashmap.insert(uuid,s)){
		printf("insert fail!! %s\n",uuid);
	}
	//printf("insert success!! %s\n",uuid);
//暂时注释跑敏感变量无数组情况
	ANODE a = (ANODE)malloc(sizeof(ArrayNode));
	InitArray(a, 10);
	if(!hashmapArray.insert(uuid,a)){
		printf("insert fail!! %s\n",uuid);
	}
	//多维数组注释1022-1026
	// struct MultiArrayNode m[10] = {NULL,NULL,NULL,NULL};
	// MNODE m = (MNODE)malloc(10*sizeof(MultiArrayNode));
	// if(!hashmapMultiArray.insert(uuid,m)){
	// 	printf("insert fail!! %s\n",uuid);
	// }

	
}

void encall_deleteValue(void* data,char* uuid,char* cuuid) {
	
	//printf("delete uuid=%s  cuuid=%s\n",uuid,cuuid);
	long *data1 = (long*)data;
	long status = *data1;
//printf("[DELETE] uuid=%s status=%ld\n",uuid,status);
	if(status==1L){
		printf("It need to destory! %s\n",cuuid);
		free(hashmapPublicV.find(cuuid));
		hashmapPublicV.find(cuuid) = NULL;
		hashmapPublicV.del(cuuid);
	}
	//printf("1\n");
	free(hashmap.find(uuid));
	//printf("2\n");
	hashmap.find(uuid) = NULL;
	//printf("3\n");
	hashmap.del(uuid);
	//printf("4\n");

	if(!hashmapArray.find(uuid)){
		FreeArray(hashmapArray.find(uuid),10);
	}
	//printf("5\n");
	if(hashmapArray2.find(uuid)){
		int sz=hashmapArray2.find(uuid)->int_sz;
		//printf("int_sz=%d\n", sz);
		for(int i=0;i<sz;i++){
			//printf("i=%d\n", i);
			if(hashmapArray2.find(uuid)->int_arrNodes[i]!=NULL){
				//printf("int_arrNodes[i]!=NULL\n");
				if(hashmapArray2.find(uuid)->int_arrNodes[i]->sz!=0){
					//printf("data sz=%d\n",hashmapArray2.find(uuid)->int_arrNodes[i]->sz);
					free(hashmapArray2.find(uuid)->int_arrNodes[i]->data);

				}
				//printf("free\n");
				//printf("d=%d\n",hashmapArray2.find(uuid)->int_arrNodes[i]->d);
				free(hashmapArray2.find(uuid)->int_arrNodes[i]);
				hashmapArray2.find(uuid)->int_arrNodes[i]=NULL;
					
					
				
			}
		}
	}
	//printf("6\n");
//污染变量中没有数组将916-922进行注释可以提高效率
	//printf("0\n");
	free(hashmapArray.find(uuid));   // I don't know if it will success free 0508
	hashmapArray.find(uuid) = NULL;
	hashmapArray.del(uuid);
	//printf("1\n");
	free(hashmapArray2.find(uuid));  
	//printf("2\n"); // I don't know if it will success free 0508
	hashmapArray2.find(uuid) = NULL;
	//printf("3\n");
	hashmapArray2.del(uuid);
	//printf("4\n");
	//free(hashmapMultiArray.find(uuid));
	//hashmapMultiArray.find(uuid) = NULL;
	//hashmapMultiArray.del(uuid);
	//printf("delete all success uuid=%s, status=%ld\n",uuid,status);
}
// 原方案
void encall_initmultiArray(long line,char* uuid,char* cuuid){
	
	
	if(!hashmapPublicV.find(cuuid)){
		printf("init PNODE cuuid=%s\n",cuuid);
	
		PNODE p = (PNODE)malloc(10*sizeof(PublicVariableNode));
		if(!hashmapPublicV.insert(cuuid,p)){
			printf("insert fail!! %s\n",cuuid);
		}
	}
}


/*int encall_switch_type_i(long Line,int* int_array,int int_tail,double* double_array,int double_tail,float* float_array,int float_tail,char* char_array,int char_tail,long* long_array, int long_tail,char* byte_array, int byte_tail,char* uuid) {
//ocall_print_string("go in encall_switch_type_i\n"); void* data,void* rei
//printf("encall_switch_type_i in enclave uuid:%s\n",uuid);
	//int *data1 = (int*)data;
        //int Line = *data1;
//printf("Line=%ld\n",Line);
	int type=*(table+Line*8);
	//hashmap.find(uuid)->Line = Line;
	//hashmap.find(uuid)->re = -99;
	//memcpy(hashmap.find(uuid)->int_array,int_array,20);
//printf("type=%d\n",type);
	//if (type == 10) {
		//return 0;
	//}
	int return_flag = -1;

	switch (type) {
		case 1:return_flag = print_int(Line, int_array,uuid);break;
		case 2:return_flag = print_double(Line, double_array,int_array,uuid);break;
		//case 3:return_flag = print_float(Line, float_array, uuid, ouuid, cuuid);break;
		case 4:return_flag = print_char(Line, char_array, uuid, ouuid, cuuid);break;
		case 5:return_flag = print_long(Line, long_array,uuid);break;

		case 6:return_flag = print_array_i(Line, int_array,int_tail,uuid);break;
		case 7:return_flag = print_array_d(Line, double_array,double_tail,uuid);break;
		//case 8:return_flag = print_array_f(Line, float_array,uuid);break;
		//case 9:return_flag = print_array_c(Line, char_array,uuid);break;
		//case 10:return_flag = print_array_l(Line, long_array,uuid);break;
		default:return_flag = -5;
	}
	// print_array();
        //printf("return num=%d\n",return_flag);
        //ocall_send_i(return_flag);
       //int *re = (int*)rei;
      // *re = return_flag;
	return return_flag;
}*/
// 原方案？
int encall_getArraySize(long Line,char* uuid){

	Table_meta meta=get_table_meta(Line);
	int p1 = meta.p1;
	int p1_i = meta.p1_i;
	int p2 = meta.p2;
	int p2_i = meta.p2_i;
	int op = meta.op;
	int para_name = meta.para_name;
	int para_i = meta.para_i;	
/*
printf("p1=%d\n",p1);
printf("p1_i=%d\n",p1_i);
printf("p2=%d\n",p2);
printf("p2_i=%d\n",p2_i);
printf("op=%d\n",op);
printf("para_name=%d\n",para_name);
printf("para_i=%d\n",para_i);
printf("----------------\n");*/
//printf("cuuid=%s\n",uuid);

	int return_size=0;
	if(p1_i>=700 && p1_i<=1200){ // this uuid is cuuid
		switch(p1_i/100){
			case 7:return_size = hashmapPublicV.find(uuid)[p1_i%10].intsize;break;
			case 8:return_size = hashmapPublicV.find(uuid)[p1_i%10].doublesize;break;
			//case 10:return_size = hashmapArray.find(uuid)->charsize[p1_i%10];break;
			//case 11:return_size = hashmapArray.find(uuid)->longsize[p1_i%10];break;
			//case 12:return_size = hashmapArray.find(uuid)->bytesize[p1_i%10];break;
		}
		//printf("[GET SIZE]hashmapPublicV.find(%s)[%d].doublesize=%d\n",uuid,p1_i%10,return_size);

	}else if(p1_i>=70 && p1_i<=120){
		
		switch(p1_i/10){
			case 7:
				if(hashmapArray.find(uuid)->intsize[p1_i%10]<0){
					int a = -hashmapArray.find(uuid)->intsize[p1_i%10];
					int b = hashmap.find(uuid)->v_int[a-100];
					return_size = hashmapMultiArray.find(uuid)[p1_i%10].intsize[b];
				}else{
					return_size = hashmapArray.find(uuid)->intsize[p1_i%10];
				}
				break;
			case 8:
				if(hashmapArray.find(uuid)->doublesize[p1_i%10]<0){
					int a = -hashmapArray.find(uuid)->doublesize[p1_i%10];
					int b = hashmap.find(uuid)->v_int[a-100];
					return_size = hashmapMultiArray.find(uuid)[p1_i%10].doublesize[b];
				}else{
					return_size = hashmapArray.find(uuid)->doublesize[p1_i%10];
				}
				break;

			case 10:return_size = hashmapArray.find(uuid)->charsize[p1_i%10];break;
			case 11:return_size = hashmapArray.find(uuid)->longsize[p1_i%10];break;
			case 12:return_size = hashmapArray.find(uuid)->bytesize[p1_i%10];break;
		}
	}else if(p1_i<10){
		int index = hashmap.find(uuid)->arrayIndex[p1_i];
		switch(index/10){
			case 7:return_size = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->intsize[index%10];break;
			case 8:return_size = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->doublesize[index%10];break;
			case 10:return_size = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->charsize[index%10];break;
			case 11:return_size = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->longsize[index%10];break;
			case 12:return_size = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->bytesize[index%10];break;
		}
	}
	//printf("return_size:%d\n",return_size);
	return return_size;
}

// 返回int数组，原方案
void encall_getIntArray(int* re,int size,long Line,char* uuid){
	
	Table_meta meta=get_table_meta(Line);
	//int p1 = meta.p1;
	int p1_i = meta.p1_i;
	if(p1_i >=700 && p1_i<=1200){ //this uuid is cuuid
		for(int i=0;i<size;i++){
			re[i] = hashmapPublicV.find(uuid)[p1_i%10].arr_int[i];
		}
	}else if(p1_i >= 70 && p1_i<=120){
		if(hashmapArray.find(uuid)->intsize[p1_i%10]<0){
			int a = -hashmapArray.find(uuid)->intsize[p1_i%10];
			int b = hashmap.find(uuid)->v_int[a-100];
			//printf("hashmapMultiArray.find(%s)[%d].arr_int[%d] ",uuid,p1_i%10,b);
			for(int i=0;i<size;i++){
				re[i] = hashmapMultiArray.find(uuid)[p1_i%10].arr_int[b][i];
				//printf("%d ",re[i]);
			}
			//printf("\n");
		}else{
			for(int i=0;i<size;i++){
				re[i] = hashmapArray.find(uuid)->arr_int[p1_i%10][i];
			}	
		}
	}else if(p1_i <10){
		//memcpy(re,hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_int[hashmap.find(uuid)->arrayIndex[p1_i]%10],size);
		for(int i=0;i<size;i++){
			re[i] = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_int[hashmap.find(uuid)->arrayIndex[p1_i]%10][i];
		}
	}

	/*if(Line==22L){
		for(int i=0;i<size;i++){
			printf("[Enclave] re[%d]=%d\n",i,re[i]);
		}
	}*/
}

void encall_getDoubleArray(double* re,int size,long Line,char* uuid){
	
	Table_meta meta=get_table_meta(Line);
	//int p1 = meta.p1;
	int p1_i = meta.p1_i;
	if(p1_i >=700 && p1_i<=1200){ //this uuid is cuuid
		for(int i=0;i<size;i++){
			re[i] = hashmapPublicV.find(uuid)[p1_i%10].arr_double[i];
		}
		//printf("[encall_getDoubleArray]%lf %lf\n",hashmapPublicV.find(uuid)[p1_i%10].arr_double[0],hashmapPublicV.find(uuid)[p1_i%10].arr_double[1]);

	}else if(p1_i >= 70 && p1_i<=120){
		if(hashmapArray.find(uuid)->doublesize[p1_i%10]<0){
			int a = -hashmapArray.find(uuid)->doublesize[p1_i%10];
			int b = hashmap.find(uuid)->v_int[a-100];
			for(int i=0;i<size;i++){
				re[i] = hashmapMultiArray.find(uuid)[p1_i%10].arr_double[b][i];
			}
		}else{
			for(int i=0;i<size;i++){
				re[i] = hashmapArray.find(uuid)->arr_double[p1_i%10][i];
			}	
		}
	}else if(p1_i <10){
		for(int i=0;i<size;i++){
			re[i] = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_double[hashmap.find(uuid)->arrayIndex[p1_i]%10][i];
		}
	}
}

// 原方案
void encall_initArray(char* uuid,int index,int size,int isSens){
	int realsize = 0;
	//get real size
	if(isSens == 0){
		realsize = size;
	}else if(isSens == 1){
		if(size>99 && size <200){
			realsize = hashmap.find(uuid)->v_int[size-100];
		}else{
			printf("Something Wrong in initArray Index Size! 0527\n");
		}
	}
	//printf("realsize=%d isSens=%d size=%d\n",realsize,isSens,size);
	initArrayRow(hashmapArray.find(uuid), index, realsize);
}

// 初始化数组节点
void encall_initNode(char* uuid,int type,int size){
		
	 //printf("\n\n\ninit node in enclave  size=%d type=%d\n\n\n",size,type);
	 //printf("uuid=%s\n", uuid);
	 ArrayNode2* node=hashmapArray2.find(uuid);
	//hashmapArray2.find(uuid);
	 if(node==NULL){
	 	printf("null\n");
	 	node=(ArrayNode2*)malloc(sizeof(ArrayNode2));
	 }
	 if(!hashmapArray2.insert(uuid,node)){
	 	printf("insert fail\n");
	 }
	 
	 if(type==7||type==13){
	 	 for(int i=0;i<size;i++){
	 	 	node->int_arrNodes[i]=(IntArrayNode*)malloc(sizeof(IntArrayNode));
	 	 	for(int j=0;j<5;j++){
	 	 		node->int_arrNodes[i]->index[j]=-1;
	 	 		node->int_arrNodes[i]->dimensions[j]=-1;
	 	 	}
	 	 	node->int_arrNodes[i]->paramLoc=-1;
	 	 	node->int_arrNodes[i]->sz=0;
	 	 }
	 	 node->int_sz=size;
	 }
	 if(node->int_arrNodes[0]==NULL){
	 	printf("null\n");
	 }else{
	 	printf("not null\n");
	 }
	  if(type==10){
	 	 for(int i=0;i<size;i++){
	 	 	node->char_arrNodes[i]=(CharArrayNode*)malloc(sizeof(CharArrayNode));
	 	 	for(int j=0;j<5;j++){
	 	 		node->char_arrNodes[i]->index[j]=-1;
	 	 		node->char_arrNodes[i]->dimensions[j]=-1;
	 	 	}
	 	 	node->char_arrNodes[i]->paramLoc=-1;
	 	 	node->char_arrNodes[i]->sz=0;
	 	 }
	 	 node->char_sz=size;
	 }
	 //  if(type==8||type==14){
	 // 	 for(int i=0;i<size;i++){
	 // 	 	node->double_arrNodes[i]=(DoubleArrayNode*)malloc(sizeof(DoubleArrayNode));
	 // 	 	for(int j=0;j<5;j++){
	 // 	 		node->double_arrNodes[i]->index[j]=-1;
	 // 	 		node->double_arrNodes[i]->dimensions[j]=-1;
	 // 	 	}
	 // 	 	node->double_arrNodes[i]->paramLoc=-1;
	 // 	 	node->double_arrNodes[i]->sz=0;
	 // 	 }
	 // 	 node->int_sz=size;
	 // }
	 
	
	//  for(int i=0;i<size;i++){
	// 	if(node->int_arrNodes[i]->index==NULL){
	// 		printf("is null\n");
	// 	}else{
	// 		printf("not null\n");
	// 	}
	// }
	
}

// 对应的是java中的GET语句，从enclave中取值，赋给某个变量
void encall_switch_type_get_i(void* data,void* rei,int* int_array,int int_tail,double* double_array,int double_tail,float* float_array,int float_tail,char* char_array,int char_tail,long* long_array, int long_tail,char* byte_array, int byte_tail,char* uuid, char* ouuid,char* cuuid) {
	long *data1 = (long*)data;
        long Line = *data1;
	//int type=*(table+Line*5);
	int return_flag = -1;
//printf("get Line=%d\n",Line);

	switch (*(table+Line*8)) {
		case 1:return_flag = print_int(Line, int_array, uuid, ouuid, cuuid);break;
		case 2:return_flag = print_double(Line, double_array, int_array, uuid, ouuid, cuuid);break;
		//case 3:return_flag = print_float(Line, float_array, uuid, ouuid, cuuid);break;
		case 4:return_flag = print_char(Line, char_array, uuid, ouuid, cuuid);break;
		case 5:return_flag = print_long(Line, long_array, int_array, uuid, ouuid, cuuid);break;
		case 6:return_flag = print_byte(Line, byte_array, int_array, ouuid, cuuid);break;
		//case 7:return_flag = print_array_i(Line, int_array,int_tail,uuid);break;
		//case 8:return_flag = print_array_d(Line, double_array,double_tail,uuid);break;
		default:return_flag = -5;
	}
       int *re = (int*)rei;
       *re = return_flag;
}

// 处理
void encall_switch_type_branch(void* data,void* rei,int* int_array,int int_tail,double* double_array,int double_tail,float* float_array,int float_tail,char* char_array,int char_tail,long* long_array, int long_tail,char* byte_array, int byte_tail,char* uuid, char* ouuid, char* cuuid) {

	long *data1 = (long*)data;
        long Line = *data1;
	int return_flag = -1;
	//printf("bracnch coming and line=%d  type=%d\n  ",Line,*(table+Line*8));


	// printf("[Error] Line=%ld\n",Line);
	// printf("[Error] type=%d\n",*(table+Line*8));
	// printf("[Error] p1=%d\n",*(table+Line*8+1));
	// printf("[Error] p1_i=%d\n",*(table+Line*8+2));
	// printf("[Error] p2=%d\n",*(table+Line*8+3));
	// printf("[Error] p2_i=%d\n",*(table+Line*8+4));
	// printf("[Error] op=%d\n",*(table+Line*8+5));
	// printf("[Error] pa=%d\n",*(table+Line*8+6));
	// printf("[Error] pa_i=%d\n",*(table+Line*8+7));
	// printf("[Error] uuid=%s\n",uuid);


	switch (*(table+Line*8)) {
		case 1:return_flag = print_int(Line, int_array, uuid, ouuid, cuuid);break;
		case 2:return_flag = print_double(Line, double_array, int_array, uuid, ouuid, cuuid);break;
		case 3:return_flag = print_float(Line, float_array, uuid, ouuid, cuuid);break;
		case 4:return_flag = print_char(Line, char_array, uuid, ouuid, cuuid);break;
		case 5:return_flag = print_long(Line, long_array, int_array, uuid, ouuid, cuuid);break;
		case 6:return_flag = print_byte(Line, byte_array, int_array, ouuid, cuuid);break;
		//case 7:return_flag = print_array_i(Line, int_array,int_tail,uuid);break;
		//case 8:return_flag = print_array_d(Line, double_array,double_tail,uuid);break;
		default:
			//printf("brach");
			return_flag = -5;
	}

       //printf("branch return:%d\n",return_flag);
       int *re = (int*)rei;
       *re = return_flag;
}

void encall_switch_type_update(void* data,void* rei,int* int_array,int int_tail,double* double_array,int double_tail,float* float_array,int float_tail,char* char_array,int char_tail,long* long_array, int long_tail,char* byte_array, int byte_tail,char* uuid, char* ouuid, char* cuuid) {
	long *data1 = (long*)data;
        long Line = *data1;
	int return_flag = -1;
	
	//printf("update coming and line=%d  type=%d\n  ",Line,*(table+Line*8));
	
	int numbers = mymap[Line];
	//printf("numbers=%d\n",numbers);
	//printf("uuid=%s\n",uuid);
	
	
	int count = 0;
	if(numbers==0){
		switch (*(table+Line*8)) {
			// TypeIndex的值
			case 1:return_flag = print_int(Line, int_array, uuid, ouuid, cuuid);break;
			case 2:return_flag = print_double(Line, double_array, int_array, uuid, ouuid, cuuid);break;
			case 3:return_flag = print_float(Line, float_array, uuid, ouuid, cuuid);break;
			case 4:return_flag = print_char(Line, char_array, uuid, ouuid, cuuid);break;
			case 5:return_flag = print_long(Line, long_array, int_array, uuid, ouuid, cuuid);break;
			case 6:return_flag = print_byte(Line, byte_array, int_array, ouuid, cuuid);break;

			case 7:return_flag = print_array_i(Line, int_array, int_tail, uuid, ouuid, cuuid);break;
			case 8:return_flag = print_array_d(Line, double_array, double_tail, uuid, ouuid, cuuid);break;
			// case 9: print_array_f
			case 10:return_flag = print_array_c(Line, char_array, char_tail, uuid, ouuid, cuuid);break;
			// case 11: print_array_l
			// case 12: print_array_b
			case 13:return_flag = print_array_i(Line, int_array, int_tail, uuid, ouuid, cuuid);break;
			case 14:return_flag = print_array_d(Line, double_array, double_tail, uuid, ouuid, cuuid);break;
				default:return_flag = -5;
		}
	
 	//int *re = (int*)rei;
       // *re = return_flag;
	}
	while(count<numbers){
		
		//printf("start\n");
		if(count>0){
			//printf("count=%d\n",count);
			Line = Line+1;
			//printf("start add line=%d\n",Line);
		}

		switch (*(table+Line*8)) {

			case 1:return_flag = print_int(Line, int_array, uuid, ouuid, cuuid);break;
			case 2:return_flag = print_double(Line, double_array, int_array, uuid, ouuid, cuuid);break;
			case 3:return_flag = print_float(Line, float_array, uuid, ouuid, cuuid);break;
			case 4:return_flag = print_char(Line, char_array, uuid, ouuid, cuuid);break;
			case 5:return_flag = print_long(Line, long_array, int_array, uuid, ouuid, cuuid);break;
			case 6:return_flag = print_byte(Line, byte_array, int_array, ouuid, cuuid);break;

			case 7:return_flag = print_array_i(Line, int_array, int_tail, uuid, ouuid, cuuid);break;
			case 8:return_flag = print_array_d(Line, double_array, double_tail, uuid, ouuid, cuuid);break;
			case 10:return_flag = print_array_c(Line, char_array, char_tail, uuid, ouuid, cuuid);break;
			case 13:return_flag = print_array_i(Line, int_array, int_tail, uuid, ouuid, cuuid);break;
			case 14:return_flag = print_array_d(Line, double_array, double_tail, uuid, ouuid, cuuid);break;
				default:return_flag = -5;
		}
		

	count++;
 	
	}
	int *re = (int*)rei;
        *re = return_flag;
}


double encall_switch_get_d(long Line, int* int_array, int lenint,double* double_array, int lendouble,float* float_array, int lenfloat,char* char_array, int lenchar,long* long_array, int lenlong,char* byte_array, int lenbyte,char* uuid) {
	int type=*(table+Line*8);
	double return_flag = -1;
	switch (type) {
		//case 1:return_flag = print_int(Line, int_array);break;
		case 2:return_flag = print_double(Line, double_array,int_array,uuid,NULL);break;
		//case 3:return_flag = print_float(Line, float_array);break;
		//case 4:return_flag = print_char(Line, char_array);break;
		//case 5:return_flag = print_long(Line, long_array);break;
		//case 6:return_flag = print_byte(Line, byte_array);break;
		default:return_flag = -5;
		}
	return return_flag;
}
/*
float encall_switch_type_f(long Line, int* int_array, int lenint,double* double_array, int lendouble,float* float_array, int lenfloat,char* char_array, int lenchar,long* long_array, int lenlong,char* byte_array, int lenbyte) {
	int type=*(table+Line*5);
	if (type == 10) {
		return 0;
	}
	float return_flag = -1;
	switch (type) {
		case 1:return_flag = print_int(Line, int_array);break;
		case 2:return_flag = print_double(Line, double_array);break;
		case 3:return_flag = print_float(Line, float_array);break;
		case 4:return_flag = print_char(Line, char_array);break;
		case 5:return_flag = print_long(Line, long_array);break;
		case 6:return_flag = print_byte(Line, byte_array);break;
		default:return_flag = -5;
		}
	return return_flag;
}

char encall_switch_type_c(long Line, int* int_array, int lenint,double* double_array, int lendouble,float* float_array, int lenfloat,char* char_array, int lenchar,long* long_array, int lenlong,char* byte_array, int lenbyte) {
	int type=*(table+Line*5);
	if (type == 10) {
		return 0;
	}
	char return_flag = -1;
	switch (type) {
		case 1:return_flag = print_int(Line, int_array);break;
		case 2:return_flag = print_double(Line, double_array);break;
		case 3:return_flag = print_float(Line, float_array);break;
		case 4:return_flag = print_char(Line, char_array);break;
		case 5:return_flag = print_long(Line, long_array);break;
		case 6:return_flag = print_byte(Line, byte_array);break;
		default:return_flag = -5;
		}
	return return_flag;
}
*/
long encall_switch_get_l(long Line, int* int_array, int lenint,double* double_array, int lendouble,float* float_array, int lenfloat,char* char_array, int lenchar,long* long_array, int lenlong,char* byte_array, int lenbyte,char* uuid) {
//ocall_print_string("go in encall_switch_type_l\n");
	int type=*(table+Line*8);
	long return_flag = -1;
	switch (type) {
		//case 1:return_flag = print_int(Line, int_array);break;
		//case 2:return_flag = print_double(Line, double_array);break;
		//case 3:return_flag = print_float(Line, float_array);break;
		//case 4:return_flag = print_char(Line, char_array);break;
		case 5:return_flag = print_long(Line, long_array,int_array,uuid,NULL);break;
		//case 6:return_flag = print_byte(Line, byte_array);break;
		default:return_flag = -5;
		}
	return return_flag;
}

// char encall_switch_type_b(long Line, int* int_array, int lenint,double* double_array, int lendouble,float* float_array, int lenfloat,char* char_array, int lenchar,long* long_array, int lenlong,char* byte_array, int lenbyte,char* uuid) {
// 	int type=*(table+Line*5);
// 	if (type == 10) {
// 		return 0;
// 	}
// 	char return_flag = -1;
// 	switch (type) {
// 		// case 1:return_flag = print_int(Line, int_array);break;
// 		// case 2:return_flag = print_double(Line, double_array);break;
// 		// case 3:return_flag = print_float(Line, float_array);break;
// 		// case 4:return_flag = print_char(Line, char_array);break;
// 		// case 5:return_flag = print_long(Line, long_array);break;
// 		case 6:return_flag = print_byte(Line, byte_array, int_array, ouuid, cuuid);break;
// 		default:return_flag = -5;
// 		}
// 	return return_flag;
// }

//----------------------------------------------------------------------------------------------------------
// [hyr]0723 add parameters ouuid, cuuid
int print_int(long Line, int* int_array, char* uuid, char* ouuid, char* cuuid)//---------------------------int
{
	
		Table_meta meta=get_table_meta(Line);

		int p1 = meta.p1;
		int p1_i = meta.p1_i;
		int p2 = meta.p2;
		int p2_i = meta.p2_i;
		int op = meta.op;
		int para_name = meta.para_name;
		int para_i = meta.para_i;	

		int return_flag = -999;
		int para1, para2;
		

		// return statement replacce! 0509
		if(p1==-2 && p1_i==-2 && p2==-2 && p2_i==-2 && op==-2){
			//printf("this is a return statement Line=%ld\n",Line);
			if(para_i != -1){
				printf("I don't think this if will active 0509\n");
			}else if(para_name>=100 && para_i == -1){ //only variables
				//printf("calluuid:%s \n",hashmap.find(uuid)->calluuid);
				hashmap.find(hashmap.find(uuid)->calluuid)->v_int[hashmap.find(uuid)->re[2]-100] = hashmap.find(uuid)->v_int[para_name-100];
			}else if(para_name<0 && para_i == -1){ //constant
				hashmap.find(hashmap.find(uuid)->calluuid)->v_int[hashmap.find(uuid)->re[2]-100] = hash_int[0-para_name];
			}
			//printf("20210720 1538 return_flag=%d\n",return_flag);
			return 1000;
			
		}
		
		// hyr 0723 modified
		// TODO 直接从hashmap里拿值，前提是里面已经有值了，是否涉及initValue和initNode两个函数？
		if (p1 < 0 && hash_index[0-p1] != 0) { //consants(why such condition)
			para1 = hash_int[0-p1];
		} else if (p1 < 10 && p1 > =0) { //list(for what)
			para1 = int_array[p1];
		} else if (p1 >= 100 && p1 < 200) { // sensitive variables
			para1 = hashmap.find(uuid)->v_int[p1 - 100];
		} else if (p1 >= 1000 && p1 < 2000 && ouuid != NULL) { // sensitive member variables
			para1 = hashmapMemberVariables.find(ouuid)->v_int[p1 - 1000];
		} else if (p1 >= 10000 && p1 < 20000 && cuuid != NULL) { // sensitive static member variables
			para1 = hashmapStaticMemberVariables.find(cuuid)->v_int[p1 - 10000];
		} else {
			printf("[hyr]error, unkonwn type!");
		}
		
		
		if (p2 < 0 && hash_index[0-p2] != 0) { //consants(why such condition)
			para2 = hash_int[0-p2];
		} else if (p2 < 10 && p2 > =0) { //list(for what)
			para2 = int_array[p2];
		} else if (p2 >= 100 && p2 < 200) { // sensitive variables
			para2 = hashmap.find(uuid)->v_int[p2 - 100];
		} else if (p2 >= 1000 && p2 < 2000 && ouuid != NULL) { // sensitive member variables
			para2 = hashmapMemberVariables.find(ouuid)->v_int[p2 - 1000];
		} else if (p2 >= 10000 && p2 < 20000 && cuuid != NULL) { // sensitive static member variables
			para2 = hashmapStaticMemberVariables.find(cuuid)->v_int[p2 - 10000];
		} else {
			printf("[hyr]error, unkonwn type!");
		}


		switch (op) {
			case -1:return_flag = para1;break;
			case 1:return_flag = para1 + para2;break;
			case 2:return_flag = para1 - para2;break;
			case 3:return_flag = para1 * para2;break;
			case 4:return_flag = para1 / para2;break;
			case 5:return_flag = para1 % para2;break;
			case 6:return_flag = (para1 == para2?1:0);break;
	 		case 7:return_flag = (para1 != para2?1:0);break;
	  		case 8:return_flag = (para1 > para2?1:0);break;
	  		case 9:return_flag = (para1 < para2?1:0);break;
	  		case 10:return_flag = (para1 >= para2?1:0);break;
	  		case 11:return_flag = (para1 <= para2?1:0);break;
			case 12:return_flag = para1 & para2;break;
			case 13:return_flag = para1 | para2;break;
			case 14:return_flag = para1 ^ para2;break;
			case 15:return_flag = para1 << para2;break;
			case 16:return_flag = para1 >> para2;break;
			case 17:return_flag = (unsigned int)para1 >> para2;break;
			default:return_flag = -11;
		}

		if (para_name >= 100 && para_name < 200) { // int type variable, Typeindex(while int, its value equals 1) * 100 + position
			hashmap.find(uuid)->v_int[para_name - 100] = return_flag;
		} else if (para_name >= 1000 && para_name < 2000 && ouuid != NULL) { // int type member variable, Typeindex * 1000 + position
			if (hashmapMemberVariables.find(ouuid) == NULL) {
				// init
				ONODE oNode = (ONODE)malloc(sizeof(ObjectNode));
				if (!hashmapMemberVariables.insert(ouuid, oNode)) {
					printf("[hyr] insert member variable fail!");
				}
			}
			hashmapMemberVariables.find(ouuid)->v_int[para_name - 1000] = return_flag;
		} else if (para_name >= 10000 && para_name < 20000 && cuuid != NULL) { // int type static memebr variable, *10000 + position
			if (hashmapStaticMemberVariables.find(cuuid) == NULL) {
				// init
				CNODE cNode = (CNODE)malloc(sizeof(ClassNode));
				if (!hashmapStaticMemberVariables.insert(cuuid, cNode)) {
					printf("[hyr] insert member variable fail!");
				}
			}
			hashmapStaticMemberVariables.find(cuuid)->v_int[para_name - 10000] = return_flag;
		}
		return_flag = 1000;
		return return_flag;


/*	
		if(return_flag==0){
			printf("p1=%d\n",p1);
			printf("p1_i=%d\n",p1_i);
			printf("p2=%d\n",p2);
			printf("p2_i=%d\n",p2_i);
			printf("op=%d\n",op);
			printf("para_name=%d\n",para_name);
			printf("para_i=%d\n",para_i);
			printf("uuid=%s\n",uuid);
		}
*/
		




		// 原方案

		/**
			para1 
		*/

// 		if(p1_i != -1){   //array
// 			//printf("20210720 come to 1545\n");
// 			if (p1 < 0 && hash_index[0-p1] != 0){  //consants
// 				if(p1_i>=70 && p1_i<=120){
// 					para1 = hashmapArray.find(uuid)->arr_int[p1_i%10][hash_int[0-p1]];
// 					// para1 = hashmapArray2.find(uuid)->int_arrNodes[p1_i%10][hash_int[0-p1]];
// 				}else if(p1_i < 10){	// from caller
// 					para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_int[hashmap.find(uuid)->arrayIndex[p1_i]%10][hash_int[0-p1]];
// 					// para1 = hashmapArray2.find(hashmap.find(uuid)->array[p1_i])->int_arrNodes[hashmap.find(uuid)->arrayIndex[p1_i]%10][hash_int[0-p1]];
// 				}else if(p1_i>=700 && p1_i<=1200){ //array field
// 					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid a!]\n");}
// 					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_int[hash_int[0-p1]];
// 				}else if(p1_i>=1300 && p1_i<=1800){ // multi array field, we need p2 as one of index
// 					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid b!]\n");}
// 					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_multi_int[hashmap.find(uuid)->v_int[p2-100]][hash_int[0-p1]];
// 				}else{
// 					//do nothing
// 				}
// 				printf("list 1562");
				
// 			}else if(p1<10 && p1>=0){ //list
// 				//printf("list 1564");
// 				if(p1_i>=70 && p1_i<=120){
// 					para1 = hashmapArray.find(uuid)->arr_int[p1_i%10][int_array[p1]];
// 				}else if(p1_i < 10){
// 					para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_int[hashmap.find(uuid)->arrayIndex[p1_i]%10][int_array[p1]];
// 				}else if(p1_i>=700 && p1_i<=1200){ //array field
// 					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid c!]\n");}
// 					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_int[int_array[p1]];
// 				}else if(p1_i>=1300 && p1_i<=1800){ // multi array field, we need p2 as one of index
// 					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid d!]\n");}
// 					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_multi_int[hashmap.find(uuid)->v_int[p2-100]][int_array[p1]];
// 				}else{
// 					//do nothing
// 				}

// 			}else if(p1 >=100 && p1<=699){ //encalve int~byte
// 				//int value = hashmap.find(uuid)->v_int[p1-100];
// 				//printf("1582value=%d\n",value);
// 				//printf("call0 uuid=%s,index=%d\n",hashmap.find(uuid)->array[p1_i],hashmap.find(uuid)->arrayIndex[p1_i]);
// 				if(p1_i>=70 && p1_i<=120){
// 					para1 = hashmapArray.find(uuid)->arr_int[p1_i%10][hashmap.find(uuid)->v_int[p1-100]];
// 				}else if(p1_i < 10){
// 					para1 =hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_int[hashmap.find(uuid)->arrayIndex[p1_i]%10][hashmap.find(uuid)->v_int[p1-100]];
// 				}else if(p1_i>=700 && p1_i<=1200){ //array field
// 					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid e!]\n");}
// 					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_int[hashmap.find(uuid)->v_int[p1-100]];
// 				}else if(p1_i>=1300 && p1_i<=1800){ // multi array field, we need p2 as one of index
// 					if(hashmapPublicV.find(cuuid)==NULL){
// 						printf("[ERROR get cuuid f! cuuid:%s Line=%ld]\n",cuuid,Line);
// 					}
// 					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_multi_int[hashmap.find(uuid)->v_int[p2-100]][hashmap.find(uuid)->v_int[p1-100]];
// 				}else{
// 					//do nothing
// 				}
// 			}else if(p1 == 10000){ //lengof method
// 				//printf("this meyhod is lengthof p1:%d p1_i:%d\n",p1,p1_i);
// 				if(p1_i>10){
// 					if(hashmapArray.find(uuid)->intsize[p1_i%10]<0){
// 						printf("[ERROR] I have not do this\n");
// 					}
// 					switch(p1_i/10){
// 						case 7:para1 = hashmapArray.find(uuid)->intsize[p1_i%10];break;
// 						case 8:para1 = hashmapArray.find(uuid)->doublesize[p1_i%10];break;
// 						case 10:para1 = hashmapArray.find(uuid)->charsize[p1_i%10];break;
// 						case 11:para1 = hashmapArray.find(uuid)->longsize[p1_i%10];break;
// 					}
// 				}else{
// 					int index = hashmap.find(uuid)->arrayIndex[p1_i];
// 					switch(index/10){
// 						case 7:para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->intsize[index%10];break;
// 						case 8:para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->doublesize[index%10];break;
// 						case 10:para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->charsize[index%10];break;
// 						case 11:para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->longsize[index%10];break;
// 					}
// 				}
			
// 			}else{
// 				//this is a array, but index is null
// 			}
// 		}else{	// no an array ,but possiable it is public variables

// 			if (p1 < 0 && hash_index[0-p1] != 0){  //consants

// 				para1 = hash_int[0-p1];

// 			}else if(p1<10 && p1>=0){ //list

// 				para1 = int_array[p1];
// 			}else if(p1>=20 && p1<=70){ // Public Variables , add on 0610/2020
// 				if(hashmapPublicV.find(cuuid) != NULL){
// 					para1 = hashmapPublicV.find(cuuid)[p1%10].v_i;
// 				}else{//init
// 					printf("[ERROR] print_int I don't think this will occur 6.10/2020\n");
// 				}
// 			}else{ //encalve
// 				//printf("here uuid=%s\n",uuid);
// 				switch(p1/100){    //maybe type cast
// 					case 1:para1 = hashmap.find(uuid)->v_int[p1-100];break;
// 					case 2:para1 = (int)hashmap.find(uuid)->v_double[p1-200];break;
// 					case 4:para1 = (int)hashmap.find(uuid)->v_char[p1-400];break;
// 					case 5:para1 = (int)hashmap.find(uuid)->v_long[p1-500];break;
// 					case 6:para1 = (int)hashmap.find(uuid)->v_byte[p1-600];break;
// 				}
				
// 				int ttpara1 = hashmap.find(uuid)->v_int[p1-100];   
// 				//printf("1649 uuid =%s  ; para1=%d\n",uuid,hashmap.find(uuid)->v_int[meta.p1-10]);	
// 			}
// 		}
// //printf("i success op1=%d\n",para1);
// 		/**
// 			para2 
// 		*/
// 		if(p2_i != -1){   //array
// 			if (p2 < 0 && hash_index[0-p2] != 0){  //consants
// 				if(p2_i>10){
// 					para2 = hashmapArray.find(uuid)->arr_int[p2_i%10][hash_int[0-p2]];
// 				}else{
// 					para2 = hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_int[hashmap.find(uuid)->arrayIndex[p2_i]%10][hash_int[0-p2]];
// 				}
// 			}else if(p2<10 && p2>=0){ //list

// 				if(p2_i>10){
// 					para2 = hashmapArray.find(uuid)->arr_int[p2_i%10][int_array[p2]];
// 				}else{
// 					para2 = hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_int[hashmap.find(uuid)->arrayIndex[p2_i]%10][int_array[p2]];
// 				}

// 			}else if(p2 >=100 && p2<=500){ //encalve int~long
// 				//int value = hashmap.find(uuid)->v_int[p1-100];
// 				//printf("value=%d\n",value);
// 				//printf("call0 uuid=%s,index=%d\n",hashmap.find(uuid)->array[p1_i],hashmap.find(uuid)->arrayIndex[p1_i]);
// 				if(p2_i>10){
// 					para2 = hashmapArray.find(uuid)->arr_int[p2_i%10][hashmap.find(uuid)->v_int[p2-100]];
// 				}else{
// 					para2 =hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_int[hashmap.find(uuid)->arrayIndex[p2_i]%10][hashmap.find(uuid)->v_int[p2-100]];
// 				}
// 			}
// 		}else{	// no an array

// 			if (p2 < 0 && hash_index[0-p2] != 0){  //consants

// 				para2 = hash_int[0-p2];

// 			}else if(p2<10 && p2>=0){ //list

// 				para2 = int_array[p2];
// 			}else{ //encalve
	
// 				switch(p2/100){    //maybe type cast
// 					case 1:para2 = hashmap.find(uuid)->v_int[p2-100];break;
// 					case 2:para2 = (int)hashmap.find(uuid)->v_double[p2-200];break;
// 					case 4:para2 = (int)hashmap.find(uuid)->v_char[p2-400];break;
// 					case 5:para2 = (int)hashmap.find(uuid)->v_long[p2-500];break;
// 					case 6:para2 = (int)hashmap.find(uuid)->v_byte[p2-600];break;
// 				}
// 				//printf("uuid =%s  ; para2=%d\n",uuid,hashmap.find(uuid)->v_int[meta.p2-10]);	
// 			}
// 		}
// /*if(Line == 0 || Line == 1){
// 	printf("i success op1=%d\n",para1);
// 	printf("i success op2=%d\n",para2);
// 	printf("i op=%d\n",meta.op);
// }*/
// 		switch (op) {
// 			case -1:return_flag = para1;break;
// 			case 1:return_flag = para1 + para2;break; //+
// 			case 2:return_flag = para1 - para2;break; //-
// 			case 3:return_flag = para1 * para2;break; //*
// 			case 4:return_flag = para1 / para2;break; // /
// 			case 5:return_flag = para1 % para2;break; // %
// 			case 6:return_flag =( para1== para2?1:0);break;
// 	 		case 7:return_flag =( para1!= para2?1:0);break;
// 	  		case 8:return_flag =( para1> para2?1:0);break;
// 	  		case 9:return_flag =( para1< para2?1:0);break;
// 	  		case 10:return_flag =(para1>=para2?1:0);break;
// 	  		case 11:return_flag =(para1<=para2?1:0);break;
// 			case 12:return_flag = para1 & para2;break;
// 			case 13:return_flag = para1 | para2;break;
// 			case 14:return_flag = para1 ^ para2;break;
// 			case 15:return_flag = para1 << para2;break;
// 			case 16:return_flag = para1 >> para2;break;
// 			case 17:return_flag = (unsigned int)para1 >> para2;break;
// 			default:return_flag = -11;
// 		}


// /*if(Line == 31L){
// 	printf("i success return_flag=%d\n",return_flag);	
// }*/

// //printf("i success return_flag=%d\n",return_flag);	
// 		if(para_i != -1){ // update to array
// 			//printf("i ==UPDATE to arrays==\n");
// 			if (para_name < 0 && hash_index[0-para_name] != 0){ //constant
// 				if(para_i>=70 && para_i<=120){
// 					hashmapArray.find(uuid)->arr_int[para_i%10][hash_int[0-para_name]] = return_flag;
// 					return_flag = 1000;
// 				}else if(para_i<10){
// 					hashmapArray.find(hashmap.find(uuid)->array[para_i])->arr_int[hashmap.find(uuid)->arrayIndex[para_i]%10][hash_int[0-para_name]] = return_flag;
// 					return_flag = 1000;
// 				}else if(para_i>=700 && para_i<=1200){ //array field
// 					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid g!]\n");}
// 					hashmapPublicV.find(cuuid)[para_i%10].arr_int[hash_int[0-para_name]] = return_flag;
// 					return_flag = 1000;	
// 				}else if(para_i>=1300 && para_i<=1800){ // multi array field, we need p2 as one of index
// 					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid h!]\n");}
// 					hashmapPublicV.find(cuuid)[para_i%10].arr_multi_int[hashmap.find(uuid)->v_int[p2_i-100]][hash_int[0-para_name]] = return_flag;
// 					return_flag = 1000;	
// 				}else{
// 					//do nothing
// 				}
			
// 			}else if(para_name >=100 ){ //encalve index
// 				if(para_i>=70 && para_i<=120){
// 					hashmapArray.find(uuid)->arr_int[para_i%10][hashmap.find(uuid)->v_int[para_name-100]] = return_flag;
// 					return_flag = 1000;
// 				}else if(para_i<10){
// 					hashmapArray.find(hashmap.find(uuid)->array[para_i])->arr_int[hashmap.find(uuid)->arrayIndex[para_i]%10][hashmap.find(uuid)->v_int[para_name-100]] = return_flag;
					
// 					return_flag = 1000;
// 				}else if(para_i>=700 && para_i<=1200){ //array field
// 					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid i!]\n");}
// 					hashmapPublicV.find(cuuid)[para_i%10].arr_int[hashmap.find(uuid)->v_int[para_name-100]] = return_flag;
// 					return_flag = 1000;	
// 				}else if(para_i>=1300 && para_i<=1800){ // multi array field, we need p2_i as one of index
// 					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid j! cuuid:%s Line=%ld]\n",cuuid,Line);}
// 					hashmapPublicV.find(cuuid)[para_i%10].arr_multi_int[hashmap.find(uuid)->v_int[p2_i-100]][hashmap.find(uuid)->v_int[para_name-100]] = return_flag;
// 					/*if(Line==49){
// 						printf("d[i][j]:%d\n",hashmapPublicV.find(cuuid)[para_i%10].arr_multi_int[hashmap.find(uuid)->v_int[p2_i-100]][hashmap.find(uuid)->v_int[para_name-100]]);
// 					}*/
// 					return_flag = 1000;	
// 				}else{
// 					//do nothing
// 				}
// 			}
// 		}else if(para_name>=20 && para_name<=70){ // Public Variables , add on 0610/2020
// 				if(hashmapPublicV.find(cuuid) != NULL){
// 					switch(para_name/10){    //maybe type cast
// 						case 2:hashmapPublicV.find(cuuid)[para_name%10].v_i = return_flag;break;
// 						case 3:hashmapPublicV.find(cuuid)[para_name%10].v_d = return_flag;break;
// 						case 5:hashmapPublicV.find(cuuid)[para_name%10].v_c = return_flag;break;
// 						case 6:hashmapPublicV.find(cuuid)[para_name%10].v_l = return_flag;break;
// 						case 7:hashmapPublicV.find(cuuid)[para_name%10].v_b = return_flag;break;
// 					}
// 				}else{//init
// 					PNODE p = (PNODE)malloc(10*sizeof(PublicVariableNode));
// 					if(!hashmapPublicV.insert(cuuid,p)){
// 						printf("insert fail!! %s\n",cuuid);
// 					}
// 					switch(para_name/10){    //maybe type cast
// 						case 2:hashmapPublicV.find(cuuid)[para_name%10].v_i = return_flag;break;
// 						case 3:hashmapPublicV.find(cuuid)[para_name%10].v_d = return_flag;break;
// 						case 5:hashmapPublicV.find(cuuid)[para_name%10].v_c = return_flag;break;
// 						case 6:hashmapPublicV.find(cuuid)[para_name%10].v_l = return_flag;break;
// 						case 7:hashmapPublicV.find(cuuid)[para_name%10].v_b = return_flag;break;
// 					}
// 				}
// 				return_flag = 1000;	
// 		}else if(para_name>0 && para_i == -1){  // update to variables
// 			switch(para_name/100){    //maybe type cast
// 				case 1:hashmap.find(uuid)->v_int[para_name-100] = return_flag;break;
// 				case 2:hashmap.find(uuid)->v_double[para_name-200] = (int)return_flag;break;
// 				case 4:hashmap.find(uuid)->v_char[para_name-400] = (int)return_flag;break;
// 				case 5:hashmap.find(uuid)->v_long[para_name-500] = (long)return_flag;break;
// 				case 6:hashmap.find(uuid)->v_byte[para_name-600] = return_flag;break;
// 			}
// 			/*if(Line == 61L){
// 				printf("20201119 %d\n",hashmap.find(uuid)->v_int[para_name-100]);
// 			}*/
// 			return_flag = 1000;	
// 		}
// 		//printf("20210720 return_flag=%d\n",return_flag);
// 		/*if(Line == 0 || Line == 1){
// 			printf("i success return_flag=%d\n",return_flag);	
// 		}*/
// /*	
// 		if(return_flag==0){
// 			printf("p1=%d\n",p1);
// 			printf("p1_i=%d\n",p1_i);
// 			printf("p2=%d\n",p2);
// 			printf("p2_i=%d\n",p2_i);
// 			printf("op=%d\n",op);
// 			printf("para_name=%d\n",para_name);
// 			printf("para_i=%d\n",para_i);
// 			printf("uuid=%s\n",uuid);
// 		}
// */
		
// 		return return_flag;

}
int calIntArrayIndex(INODE node){
	int d=0;
	while(node->dimensions[d]!=-1){
		d++;
	}
	int re=0;
	for(int i=0;i<d-1;i++){
		re+=(node->index[i]*node->dimensions[i+1]);
	}
	return re;
}
int calDoubleArrayIndex(DNODE node){
	int d=0;
	while(node->dimensions[d]!=-1){
		d++;
	}
	int re=0;
	for(int i=0;i<d-1;i++){
		re+=(node->index[i]*node->dimensions[i+1]);
	}
	return re;
}
int calCharArrayIndex(CNODE node){
	int d=0;
	while(node->dimensions[d]!=-1){
		d++;
	}
	int re=0;
	for(int i=0;i<d-1;i++){
		re+=(node->index[i]*node->dimensions[i+1]);
	}
	return re;
}


int print_array_d(long Line, double* double_array,int double_tail,char* uuid, char* ouuid, char* cuuid){


	
	//printf("==============================1===========================Line=%ld====\n",Line);
	//printf("enter  int print_array_i(long Line, int* int_array,int int_tail,char* uuid,char* cuuid)\n");
	
	// printf("uuid=%s\n",uuid);
	// printf("cuuid=%s\n",cuuid);
	Table_meta meta=get_table_meta(Line);
	int type=meta.type;
	int p1 = meta.p1;
	int p1_i = meta.p1_i;
	int p2 = meta.p2;
	int p2_i = meta.p2_i;
	int op = meta.op;
	int para_name = meta.para_name;
	int para_i = meta.para_i;	
	//printf("line=%ld p1=%d  p1_i=%d  p2=%d  p2_i=%d op=%d  para_name=%d  para_i=%d\n",Line,p1,p1_i,p2,p2_i,op,para_name,para_i);
		char *tmpuuid=(char*)malloc(33*sizeof(char));
		memcpy(tmpuuid,uuid,32);
		//printf("uuid=%s,  tmpuuid=%s\n", uuid,tmpuuid);
		if(p1==-2&&p1_i==-2&&p2==-2&&p2_i==-2&&op==-2){
				printf("return array\n");
				//printf("uuid=%s, calluuid=%s, re[2]=%d\n",uuid,hashmap.find(uuid)->calluuid,hashmap.find(uuid)->re[2]);
				DNODE node1=hashmapArray2.find(hashmap.find(uuid)->calluuid)->double_arrNodes[hashmap.find(uuid)->re[2]%10];
				DNODE node2=hashmapArray2.find(uuid)->double_arrNodes[para_i%10];
				node2=hashmapArray2.find(uuid)->double_arrNodes[node2->oriLocation%10];
				if(node1->location==0){
					node1->location=hashmap.find(uuid)->re[2]%10;
					node1->oriLocation=hashmap.find(uuid)->re[2]%10;
					node1->data=(double*)malloc(sizeof(double)*node2->sz);
					node1->d=node2->d;
					for(int i=0;i<3;i++){
						node1->dimensions[i]=node2->dimensions[i];
					}
					for(int i=0;i<node2->sz;i++){
					node1->data[i]=node2->data[i];
				}
					return 1000;
				}
				// printf("node1->loc=%d, node1->oriloc=%d\n",node1->location,node1->oriLocation);
				//printf("1\n");
				node1=hashmapArray2.find(hashmap.find(uuid)->calluuid)->double_arrNodes[node1->oriLocation%10];
				//printf("2\n");
			

				//printf("sz1=%d\n", node1->sz);
				//printf("sz2=%d\n", node2->sz);
				for(int i=0;i<node2->sz;i++){
					node1->data[i]=node2->data[i];
				}
				// for(int i=0;i<node2->sz;i++){
				// 	printf("arr[%d]=%d\n",i,node2->data[i]);
				// }
				// for(int i=0;i<node1->sz;i++){
				// 	printf("arr[%d]=%d\n",i,node1->data[i]);
				// }

		}else if(p2==0){
			//printf("type=7 p2=0\n");

			bool flag=true;
			int dim[3]={0};//dim[0] dim[1] dim[2] represent array's 1st 2nd 3th dimension 
			if(p1<0&&hash_index[0-p1]!=0){
				dim[0]=hash_double[0-p1];
				//printf("1 dimension constant: %d  int_%d\n", p1,hash_double[0-p1]);

			}else if(p1>=100&&p1<700){
				dim[0]=hashmap.find(uuid)->v_double[p1-100];
				//printf("1 dimension variable:%d %d\n",p1, hashmap.find(uuid)->v_double[p1-100]);
				
			}else{
				flag=false;
			}
			if(flag&&p1_i<0&&hash_index[0-p1_i]!=0){
				dim[1]=hash_double[0-p1_i];
				//printf("2 dimension constant: %d  int_%d\n", p1_i,hash_double[0-p1_i]);
			}else if(flag&&p1_i>=100&&p1_i<700){
				dim[1]=hashmap.find(uuid)->v_double[p1_i-100];
				//printf("2 dimension variable:%d %d\n",p1_i, hashmap.find(uuid)->v_double[p1_i-100]);
			}else{
				flag=false;
			}
			if(flag&&p2_i<0&&hash_index[0-p2_i]!=0){
				dim[2]=hash_double[0-p2_i];
				//printf("3 dimension constant: %d  int_%d\n", p2_i,hash_double[0-p2_i]);
			}else if(flag&&p2_i>=100&&p2_i<700){
				dim[2]=hashmap.find(uuid)->v_double[p2_i-100];
				//printf("3 dimension variable:%d %d\n",p2_i, hashmap.find(uuid)->v_double[p2_i-100]);
			}else{
				flag=false;
			}
			// for(int i=0;i<3;i++){
			// 	printf("dim[%d]=%d\n", i,dim[i]);
			// }
			int d=0;// how many dimensions
			int sz=1;//array size
			for(int i=0;i<3;i++){
				if(dim[i]!=0){
					d++;
					sz*=dim[i];
				}
			}
			//printf("uuid=%s  size=%d\n",uuid,sz);
			//printf("123\n");
			DNODE node=hashmapArray2.find(uuid)->double_arrNodes[para_i%10];
			//printf("456\n");
			node->d=d;//update d
			for(int i=0;i<d;i++){
				node->dimensions[i]=dim[i];//update dimensions
			}
			node->paramLoc=-1;
			node->data=(double*)malloc(sz*sizeof(double));//malllo space for data 
			node->sz=sz;

			return 1000;

		}else if(p2==1){
			//printf("type=7 p2=1\n");
			int oriLoc=p1_i;
			DNODE node=hashmapArray2.find(uuid)->double_arrNodes[para_i%10];
			node->oriLocation=oriLoc;
		
		}else if(p2==2){

			
			//ocall_print_string("type=7 p2=2\n");
			int loc=-1;
			int k=-1;
			if(para_i==-1){//int a=arr[0] left is variable
				//printf("int a=arr[0] before uuid: %s\n", uuid);
				DNODE node1=hashmapArray2.find(uuid)->double_arrNodes[p1_i%10];
				// for(int i=0;i<3;i++){
				// 	printf("node->index[%d]=%d\n", i,node1->index[i]);
				// }
				// for(int i=0;i<3;i++){
				// 	printf("node->dimensions[%d]=%d\n", i,node1->dimensions[i]);
				// }
				int idx=calDoubleArrayIndex(node1);
				//printf("idx=%d\n", idx);
				if(node1->paramLoc!=-1){//is formular array param
					//printf("isformular array param %d\n",node1->paramLoc);
					for(k=0;k<10;k++){
						if(k==node1->paramLoc){
							loc=hashmap.find(uuid)->arrayIndex[k];
							memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
							break;
						}
					}
				}
				

				if(loc!=-1){
					
					node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->double_arrNodes[loc%10];
					//printf("5\n");
					
				}
				//printf("uuid=%s,  tmpuuid=%s\n", uuid,tmpuuid);
				
				
				int index=-1;//array index
				if(p1<0&&hash_index[0-p1]!=0){
					index=hash_double[0-p1];
				}else if(p1>=100&&p1<700){
					index=hashmap.find(uuid)->v_double[p1-100];
				}
				//printf("index=%d\n", index);
				idx+=index;//
				DNODE node2=NULL;
				if(k!=-1){
					node2=hashmapArray2.find(hashmap.find(uuid)->array[k])->double_arrNodes[node1->oriLocation%10];
				}else{
					node2=hashmapArray2.find(uuid)->double_arrNodes[node1->oriLocation%10];
				}
				
				//printf("a=data[%d]\n",node2->data[idx]);
				//printf("\n\n");
				hashmap.find(uuid)->v_double[para_name-100]=node2->data[idx];//int a=arr[1][2][3]
				//printf("\n");
			}else{//arr[0]=3
				int loc=-1;
				int k=-1;
				
				DNODE node1=hashmapArray2.find(uuid)->double_arrNodes[para_i%10];
				for(int i=0;i<3;i++){
					//printf("node->index[%d]=%d\n", i,node1->index[i]);
					//printf("node->dimensions[%d]=%d\n", i,node1->dimensions[i]);
				}
				int idx=calDoubleArrayIndex(node1);
				//printf("idx=%d\n", idx);
				if(node1->paramLoc!=-1){//is formular array param
					//printf("isformular array param %d\n",node1->paramLoc);
					for(k=0;k<10;k++){
						if(k==node1->paramLoc){
							loc=hashmap.find(uuid)->arrayIndex[k];
							memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
							break;
						}
					}
				}
				//printf("uuid=%s,  tmpuuid=%s\n", uuid,hashmap.find(uuid)->array[k]);
				if(loc!=-1){
					node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->double_arrNodes[loc%10];
					
				}
				
				
				int index=-1;//arr[index]=num
				int num=-1;
				if(para_name<0&&hash_index[0-para_name]!=0){
					index=hash_double[0-para_name];
				}else if(para_name>=100&&para_name<700){
					index=hashmap.find(uuid)->v_double[para_name-100];
				}
				if(p1<0&&hash_index[0-p1]!=0){
					num=hash_double[0-p1];
				}else if(p1>=100&&p1<700){
					num=hashmap.find(uuid)->v_double[p1-100];
				}
				//("2\n");
				idx+=index;
				DNODE node2=NULL;
				if(k!=-1){
					//printf("k!=-1\n");
					node2=hashmapArray2.find(hashmap.find(uuid)->array[k])->double_arrNodes[node1->oriLocation%10];
				}else{
					//printf("k==-1\n");
					node2=hashmapArray2.find(uuid)->double_arrNodes[node1->oriLocation%10];
				}
				//printf("idx=%d\n",idx);
				// if(node2->data==NULL){
				// 	printf("NULL\n");
				// }
				node2->data[idx]=num;
				//printf("uuid=%s, calluuid=%s\n", uuid,tmpuuid);
			     //printf("data[%d]=%d\n", idx,num);
				//printf("data[%d]=%d",idx,num);
				//printf("\n\n");

			}
		
		}else if(p2==3){//arr2=arr1 arr2=arr1[0]
			//printf("type=7 p2=3\n");
			 
			 int loc=-1;
			 int k=-1;
			 
			DNODE node1=hashmapArray2.find(uuid)->double_arrNodes[p1_i%10];
			// for(int i=0;i<3;i++){
			// 	printf("node->index[%d]=%d\n",i,node1->index[i]);
			// }
			// if(node1->paramLoc!=-1){//is formular array param
			// 		printf("isformular array param %d\n",node1->paramLoc);
			// 		for(k=0;k<10;k++){
			// 			if(k==node1->paramLoc){
			// 				loc=hashmap.find(uuid)->arrayIndex[k];
			// 				memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
			// 				break;
			// 			}
			// 		}
			// 	}
			// if(loc!=-1)
			// 		node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->double_arrNodes[loc%10];
			DNODE node2=hashmapArray2.find(uuid)->double_arrNodes[para_i%10];
			node2->d=node1->d;//update d
			for(int i=0;i<5;i++){
				node2->dimensions[i]=node1->dimensions[i];//update dimesions
				node2->index[i]=node1->index[i];//update index
			}
			node2->oriLocation=node1->oriLocation;//update oriLocation
			for(int i=0;i<3;i++){
				///printf("node->index[%d]=%d\n",i,node1->index[i]);
			}
			//printf("uuid=%s, calluuid=%s\n", uuid,tmpuuid);
			//printf("node1: \n");
			//printNode(node1);
			//printf("node2: \n");
			//printNode(node2);
		
			
		}else if(p2==4){// append index
			//printf("type=7 p2=4\n");

			 int loc=-1;
			 int i=-1;
			 int k=-1;
			if(p1<0&&hash_index[0-p1]!=0){
				i=hash_double[0-p1];
			}else if(p1>=100&&p1<700){
				i==hashmap.find(uuid)->v_double[p1-100];
			}
			//printf("p1=%d i=%d\n",p1,i);
			DNODE node=hashmapArray2.find(uuid)->double_arrNodes[para_i%10];

			SNODE snode=hashmap.find(uuid);
			//printf("1\n");
			node->paramLoc=p1_i;
			if(p1==0&&p1_i==0){
				for(k=0;k<10;k++){
					if(k==node->paramLoc){
						loc=snode->arrayIndex[k];
						memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
						break;
					}
				}
				//printf("uuid=%s, tmpuuid=%s\n", uuid,tmpuuid);
				
				if(snode==NULL){
					//printf("hashmap.find(uuid)==NULL\n");
				}else{
					//printf("hashmap.find(uuid)!=NULL\n");
				}
				if(hashmapArray2.find(snode->array[k])==NULL){
					//printf("hashmapArray2.find(snode->array[k])==NULL\n");
				}else{
					//printf("hashmapArray2.find(snode->array[k])!=NULL\n");
				}
				if(hashmapArray2.find(snode->array[k])!=NULL){
					DNODE node2=hashmapArray2.find(snode->array[k])->double_arrNodes[loc%10];
					//printf("123\n");
					node->d=node2->d;//update d
					for(int i=0;i<5;i++){
					node->dimensions[i]=node2->dimensions[i];//update dimesions
					node->index[i]=node2->index[i];//update index
				}
				node->oriLocation=node2->oriLocation;//update oriLocation
				}
				
			}
			int j=0;
			for(int i=0;i<3;i++){
				//printf("node->index[%d]=%d\n",i,node->index[i]);
			}
			while(node->index[j]!=-1){
				j++;
				
			}
			
			node->index[j]=i;
			for(int i=0;i<3;i++){
				//printf("node->index[%d]=%d\n",i,node->index[i]);
			}
			
			

			
		

			
		}else if(p2==5){//get array length
			    //printf("type=7,p2=5\n");
				DNODE node1=hashmapArray2.find(uuid)->double_arrNodes[p1_i%10];
			    int d=0;
			    while(node1->index[d]!=-1){
			    	//printf("indxex[i]=%d\n", node1->index[d]);
			    	d++;
			    }
			    int loc=-1;
			    int k=-1;
			 	if(node1->paramLoc!=-1){//is formular array param
					//printf("isformular array param %d\n",node1->paramLoc);
					for(k=0;k<10;k++){
						if(k==node1->paramLoc){
							loc=hashmap.find(uuid)->arrayIndex[k];
							memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
							break;
						}
					}
				}
				//printf("uuid=%s, tmpuuid=%s\n", uuid,tmpuuid);
				if(loc!=-1){
					node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->double_arrNodes[loc%10];
				}
			    //printf("d=%d dimensions[d]=%d\n", d,node1->dimensions[d]);
			    hashmap.find(uuid)->v_double[para_name-100]=node1->dimensions[d];

				
		}
		else if(p2==-1){
			//ocall_print_string("p2=-1\n");
			
		}
		free(tmpuuid);
		//printf("leave  int print_array_i(long Line, int* int_array,int int_tail,char* uuid,char* cuuid)\n\na");
		return 1000;
		


	
}
double print_double(long Line, double* double_array, int* int_array, char* uuid, char* ouuid, char* cuuid)//---------------------------double
{
		Table_meta meta=get_table_meta(Line);
		double return_flag = -999;
		double para1,para2;

		int p1 = meta.p1;
		int p1_i = meta.p1_i;
		int p2 = meta.p2;
		int p2_i = meta.p2_i;
		int op = meta.op;
		int para_name = meta.para_name;
		int para_i = meta.para_i;
/*if(Line >=20 && Line<=26){
	printf("Line=%ld\n",Line);
	printf("p1=%d\n",p1);
	printf("p1_i=%d\n",p1_i);
	printf("p2=%d\n",p2);
	printf("p2_i=%d\n",p2_i);
	printf("op=%d\n",op);
	printf("para_name=%d\n",para_name);
	printf("para_i=%d\n",para_i);
	printf("----------------\n");
}*/
/*if(para_i>=700 || p1_i>=700){
	printf("[print_double]cuuid:%s Line=%ld\n",cuuid,Line);
}*/
		//return statement replacce! 0509
		if(p1==-2 &&  p1_i==-2 && p2==-2 && p2_i==-2 && op==-2){
			
			if(para_i != -1){
				printf("I don't think this if will active 0509\n");
			}else if(para_name>0 && para_i == -1){ //only variables
				hashmap.find(hashmap.find(uuid)->calluuid)->v_double[hashmap.find(uuid)->re[2]-100] = hashmap.find(uuid)->v_double[para_name-100];
			}else if(para_name<0 && para_i == -1){ //constant
				hashmap.find(hashmap.find(uuid)->calluuid)->v_double[hashmap.find(uuid)->re[2]-100] = hash_double[0-para_name];
			}
			return 1000;
		}

		/**
			para1 
		*/
		if(p1_i != -1){   //array
			if (p1 < 0 && hash_index[0-p1] != 0){  //consants

				if(p1_i>=70 && p1_i<=120){
					para1 = hashmapArray.find(uuid)->arr_double[p1_i%10][hash_int[0-p1]];
				}else if(p1_i < 10){
					para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_double[hashmap.find(uuid)->arrayIndex[p1_i]%10][hash_int[0-p1]];
				}else if(p1_i>=700 && p1_i<=1200){ //array field
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid k!]\n");}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_double[hash_int[0-p1]];
				}else if(p1_i>=1300 && p1_i<=1800){ // multi array field, we need p2 as one of index
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid l!]\n");}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_multi_double[hashmap.find(uuid)->v_int[p2-100]][hash_int[0-p1]];
				}else{
					//do nothing
				}

			}else if(p1<10 && p1>=0){ //list
				if(p1_i>=70 && p1_i<=120){
					para1 = hashmapArray.find(uuid)->arr_double[p1_i%10][int_array[p1]];
				}else if(p1_i < 10){
					para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_double[hashmap.find(uuid)->arrayIndex[p1_i]%10][int_array[p1]];
				}else if(p1_i>=700 && p1_i<=1200){ //array field
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid m!]\n");}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_double[int_array[p1]];
				}else if(p1_i>=1300 && p1_i<=1800){ // multi array field, we need p2 as one of index
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid n!]\n");}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_multi_double[hashmap.find(uuid)->v_int[p2-100]][int_array[p1]];
				}else{
					//do nothing
				}
			}else if(p1 >=100 && p1<=500){ //encalve int~long
				//printf("I think this if will ... 0508 d  p1=%d Line=%ld\n",p1,Line);
				if(p1_i>=70 && p1_i<=120){
					para1 = hashmapArray.find(uuid)->arr_double[p1_i%10][hashmap.find(uuid)->v_int[p1-100]];
				}else if(p1_i < 10){
					para1 =hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_double[hashmap.find(uuid)->arrayIndex[p1_i]%10][hashmap.find(uuid)->v_int[p1-100]];
				}else if(p1_i>=700 && p1_i<=1200){ //array field
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid o!]\n");}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_double[hashmap.find(uuid)->v_int[p1-100]];
				}else if(p1_i>=1300 && p1_i<=1800){ // multi array field, we need p2 as one of index
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid p!]\n");}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_multi_double[hashmap.find(uuid)->v_int[p2-100]][hashmap.find(uuid)->v_int[p1-100]];
				}else{
					//do nothing
				}
			}else{
				//this is a array, but index is null
			}
		}else{	// no an array

			if (p1 < 0 && hash_index[0-p1] != 0){  //consants

				para1 = hash_double[0-p1];

			}else if(p1<10 && p1>=0){ //list

				para1 = double_array[p1];
			}else{ //encalve
				switch(p1/100){    //maybe type cast
					case 1:para1 = (double)hashmap.find(uuid)->v_int[p1-100];break;
					case 2:para1 = hashmap.find(uuid)->v_double[p1-200];break;
					case 4:para1 = (double)hashmap.find(uuid)->v_char[p1-400];break;
					case 5:para1 = (double)hashmap.find(uuid)->v_long[p1-500];break;
					case 6:para1 = (double)hashmap.find(uuid)->v_byte[p1-600];break;
				}
				//para1 = hashmap.find(uuid)->v_int[p1-100];   
				//printf("uuid =%s  ; para1=%d\n",uuid,hashmap.find(uuid)->v_int[meta.p1-10]);	
			}
		}

		/**
			para2 
		*/
		if(p2_i != -1){   //array
			if (p2 < 0 && hash_index[0-p2] != 0){  //consants

				if(p2_i>10){
					para2 = hashmapArray.find(uuid)->arr_double[p2_i%10][hash_int[0-p2]];
				}else{
					para2 = hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_double[hashmap.find(uuid)->arrayIndex[p2_i]%10][hash_int[0-p2]];
				}

			}else if(p2<10 && p2>=0){ //list
				if(p2_i>10){
					para2 = hashmapArray.find(uuid)->arr_double[p2_i%10][int_array[p2]];
				}else{
					para2 = hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_double[hashmap.find(uuid)->arrayIndex[p2_i]%10][int_array[p2]];  //may be no use
				}
				printf("I think this if will be no use!!!!!0508 d p2=%d\n",p2);
			}else if(p2 >=100 && p2<=500){ //encalve int~long
				//printf("I think this if will ... 0508 d  p1=%d Line=%ld\n",p1,Line);
				if(p2_i>10){
					if(hashmapArray.find(uuid)->doublesize[p2_i%10]<0){
						int a = -hashmapArray.find(uuid)->doublesize[p2_i%10];
						para2 = hashmapMultiArray.find(uuid)[p2_i%10].arr_double[hashmap.find(uuid)->v_int[a-100]][hashmap.find(uuid)->v_int[p2-100]];
					}else{
						para2 = hashmapArray.find(uuid)->arr_double[p2_i%10][hashmap.find(uuid)->v_int[p2-100]];                                      ////may be ......
					}
				}else{
					para2 = hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_double[hashmap.find(uuid)->arrayIndex[p2_i]%10][hashmap.find(uuid)->v_int[p2-100]];
				}
				//printf("uuid =%s  ; para1=%d\n",uuid,hashmap.find(uuid)->v_int[meta.p1-10]);	
			}else{
				//this is a array, but index is null
			}
		}else{	// no an array

			if (p2 < 0 && hash_index[0-p2] != 0){  //consants

				para2 = hash_double[0-p2];

			}else if(p2<10 && p2>=0){ //list

				para2 = double_array[p2];
			}else{ //encalve
	
				switch(p2/100){    //maybe type cast
					case 1:para2 = (double)hashmap.find(uuid)->v_int[p2-100];break;
					case 2:para2 = hashmap.find(uuid)->v_double[p2-200];break;
					case 4:para2 = (double)hashmap.find(uuid)->v_char[p2-400];break;
					case 5:para2 = (double)hashmap.find(uuid)->v_long[p2-500];break;
					case 6:para2 = (double)hashmap.find(uuid)->v_byte[p2-600];break;
				}
				//printf("uuid =%s  ; para2=%d\n",uuid,hashmap.find(uuid)->v_int[meta.p2-10]);	
			}
		}
/*if(Line >=20 && Line<=26){
	printf("d success op1=%lf\n",para1);
	printf("d success op2=%lf\n",para2);
	printf("d op=%d\n",meta.op);
}*/
		switch (op) {
			case -1:return_flag = para1;break;
			case 1:return_flag = para1 + para2;break; //+
			case 2:return_flag = para1 - para2;break; //-
			case 3:return_flag = para1 * para2;break; //*
			case 4:return_flag = para1 / para2;break; // /
			//case 5:return_flag = para1 % para2;break; // %
			case 6:return_flag =( para1== para2?1:0);break;
	 		case 7:return_flag =( para1!= para2?1:0);break;
	  		case 8:return_flag =( para1> para2?1:0);break;
	  		case 9:return_flag =( para1< para2?1:0);break;
	  		case 10:return_flag =(para1>=para2?1:0);break;
	  		case 11:return_flag =(para1<=para2?1:0);break;
			//case 12:return_flag = para1 & para2;break;
			default:return_flag = -11;
		}
//printf("d success return_flag=%lf\n",return_flag);	
		if(para_i != -1){ // update to array
			//printf("d ==UPDATE to arrays==\n");
			if (para_name < 0 && hash_index[0-para_name] != 0){ //constant
				if(para_i>=70 && para_i<=120){
					hashmapArray.find(uuid)->arr_double[para_i%10][hash_int[0-para_name]] = return_flag;
					return_flag = 1000;
				}else if(para_i<10){
					hashmapArray.find(hashmap.find(uuid)->array[para_i])->arr_double[hashmap.find(uuid)->arrayIndex[para_i]%10][hash_int[0-para_name]] = return_flag;
					return_flag = 1000;
				}else if(para_i>=700 && para_i<=1200){ //array field
					hashmapPublicV.find(cuuid)[para_i%10].arr_double[hash_int[0-para_name]] = return_flag;
					return_flag = 1000;
				}else if(para_i>=1300 && para_i<=1800){ // multi array field, we need p2_i as one of index
					hashmapPublicV.find(cuuid)[para_i%10].arr_multi_double[hashmap.find(uuid)->v_int[p2_i-100]][hash_int[0-para_name]] = return_flag;
					return_flag = 1000;
				}else{
					//do nothing
				}
			
			}else if(para_name >=100 ){ //encalve
				if(para_i>=70 && para_i<=120){
					hashmapArray.find(uuid)->arr_double[para_i%10][hashmap.find(uuid)->v_int[para_name-100]] = return_flag;
					return_flag = 1000;
				}else if(para_i<10){
					hashmapArray.find(hashmap.find(uuid)->array[para_i])->arr_double[hashmap.find(uuid)->arrayIndex[para_i]%10][hashmap.find(uuid)->v_int[para_name-100]] = return_flag;
					
					return_flag = 1000;
				}else if(para_i>=700 && para_i<=1200){ //array field
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid q!]\n");}
					hashmapPublicV.find(cuuid)[para_i%10].arr_double[hashmap.find(uuid)->v_int[para_name-100]] = return_flag;
					/*if(Line==65){
						printf("x[i]:%lf\n",hashmapPublicV.find(cuuid)[para_i%10].arr_double[hashmap.find(uuid)->v_int[para_name-100]]);
					}*/
					return_flag = 1000;
				}else if(para_i>=1300 && para_i<=1800){ // multi array field, we need p2_i as one of index
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid r!]\n");}
					hashmapPublicV.find(cuuid)[para_i%10].arr_multi_double[hashmap.find(uuid)->v_int[p2_i-100]][hashmap.find(uuid)->v_int[para_name-100]] = return_flag;
					/*if(Line==43){
						printf("q[i][j]:%lf\n",hashmapPublicV.find(cuuid)[para_i%10].arr_multi_double[hashmap.find(uuid)->v_int[p2_i-100]][hashmap.find(uuid)->v_int[para_name-100]]);
					}*/
					return_flag = 1000;
				}else{
					//do nothing
				}
			}
	
		}else if(para_name>0 && para_i == -1){  // update to variables
			//printf("d ==UPDATE to variables==\n");
			
			switch(para_name/100){    //maybe type cast
				case 1:hashmap.find(uuid)->v_int[para_name-100] = (double)return_flag;break;
				case 2:hashmap.find(uuid)->v_double[para_name-200] = return_flag;break;
				case 4:hashmap.find(uuid)->v_char[para_name-400] = (char)return_flag;break;
				case 5:hashmap.find(uuid)->v_long[para_name-500] = (long)return_flag;break;
				case 6:hashmap.find(uuid)->v_byte[para_name-600] = (return_flag<0)?-1:1;
				       //printf("[Warning]I think only in Pi will counter this case!! 0603/2020\n");
				       break;
			}
			return_flag = 1000;	
		}
//printf("double p1=%lf\n",para1);
//printf("double p2=%lf\n",para2);
//printf("return_flag=%lf\n",return_flag); 
//ocall_print_string("d success\n");
		return return_flag;
}


float print_float(long Line, float* float_array, char* uuid, char* ouuid, char* cuuid)//---------------------------float
{
		Table_meta meta=get_table_meta(Line);
		float return_flag = -999;
		float para1,para2;
		if (meta.p1 < 0){  //consants
			para1 = hash_float[0-meta.p1];
		}else if(meta.p1<10 && meta.p1>=0){ //list
			para1 = float_array[meta.p1];
		}else{ //encalve
//			para1 = get_stacktop(s)->v_float[meta.p1 % 10];
		}
		
		if (meta.p2 < 0){  //consants
			para2 = hash_float[0-meta.p2];
		}else if(meta.p2<10 && meta.p2>=0){ //list
			para2 = float_array[meta.p2];
		}else{ //encalve
//			para2 = get_stacktop(s)->v_float[meta.p2 % 10];
		}
		switch (meta.op) {
			case -1:return_flag = para1;break;   //x=2; or x=y;
			case 1:return_flag = para1 + para2;break; //+
			case 2:return_flag = para1 - para2;break; //-
			case 3:return_flag = para1 * para2;break; //*
			case 4:return_flag = para1 / para2;break; // /
			//case 5:return_flag = para1 % para2;break; // %
			case 6:return_flag=( para1==para2?1:0);break;
	 		case 7:return_flag=( para1!=para2?1:0);break;
	  		case 8:return_flag=( para1>para2?1:0);break;
	  		case 9:return_flag=( para1<para2?1:0);break;
	  		case 10:return_flag=( para1>=para2?1:0);break;
	  		case 11:return_flag=( para1<=para2?1:0);break;
			default:return_flag = -11;
		}
		if (meta.para_name>0) { 
//			get_stacktop(s)->v_float[meta.para_name % 10] = return_flag;
			return_flag = 1000;
		}
ocall_print_string("f success\n");
		return return_flag;
}

int print_char(long Line, char* char_array, char* uuid, char* ouuid, char* cuuid)//---------------------------char
{		
		Table_meta meta=get_table_meta(Line);
		int return_flag = -999;
		char para1,para2;

		int p1 = meta.p1;
		int p1_i = meta.p1_i;
		int p2 = meta.p2;
		int p2_i = meta.p2_i;
		int op = meta.op;
		int para_name = meta.para_name;
		int para_i = meta.para_i;



		if(p1==-2 &&  p1_i==-2 && p2==-2 && p2_i==-2 && op==-2){
			
			if(para_i != -1){
				printf("[print_char]I don't think this if will active 0509\n");
			}else if(para_name>0 && para_i == -1){ //only variables
				hashmap.find(hashmap.find(uuid)->calluuid)->v_char[hashmap.find(uuid)->re[2]-100] = hashmap.find(uuid)->v_char[para_name-100];
			}else if(para_name<0 && para_i == -1){ //constant
				hashmap.find(hashmap.find(uuid)->calluuid)->v_char[hashmap.find(uuid)->re[2]-100] = hash_int[0-para_name];
			}
			return 1000;
		}

		/**
			para1 
		*/
		if(p1_i != -1){   //array
			if (p1 < 0 && hash_index[0-p1] != 0){  //consants
				printf("[print_char]I don't think this if will active 0605\n");
				//para1 = (p1_i>10)?
				//hashmapArray.find(uuid)->arr_char[p1_i%10][hash_int[0-p1]]:
				//hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_char[hashmap.find(uuid)->arrayIndex[p1_i]%10][hash_int[0-p1]];

			}else if(p1<10 && p1>=0){ //list
				printf("[print_char]I don't think this if will active 0605\n");
				//para1 = (p1_i>10)?
				//hashmapArray.find(uuid)->arr_char[p1_i%10][int_array[p1]]:
				//hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_char[hashmap.find(uuid)->arrayIndex[p1_i]%10][int_array[p1]];  //may be no use
			}else if(p1 >=100 && p1<=500){ //encalve int~long
				printf("[print_char]I don't think this if will active 0605\n");
				//para1 = (p1_i>10)?
				//hashmapArray.find(uuid)->arr_long[p1_i%10][hashmap.find(uuid)->v_int[p1-100]]:                                       ////may be ......
				//hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_long[hashmap.find(uuid)->arrayIndex[p1_i]%10][hashmap.find(uuid)->v_int[p1-100]];
				//printf("uuid =%s  ; para1=%d\n",uuid,hashmap.find(uuid)->v_int[meta.p1-10]);	
			}else{
				//this is a array, but index is null
			}
		}else{	// no an array

			if (p1 < 0 && hash_index[0-p1] != 0){  //consants
				
				para1 = hash_int[0-p1];

			}else if(p1<10 && p1>=0){ //list

				para1 = char_array[p1];
			}else{ //encalve
				switch(p1/100){    //maybe type cast
					case 1:para1 = (char)hashmap.find(uuid)->v_int[p1-100];break;
					case 2:para1 = (char)hashmap.find(uuid)->v_double[p1-200];break;
					case 4:para1 = hashmap.find(uuid)->v_char[p1-400];break;
					case 5:para1 = (char)hashmap.find(uuid)->v_long[p1-500];break;
					case 6:para1 = (char)hashmap.find(uuid)->v_byte[p1-600];break;
				}
				//para1 = hashmap.find(uuid)->v_int[p1-100];   
				//printf("uuid =%s  ; para1=%d\n",uuid,hashmap.find(uuid)->v_int[meta.p1-10]);	
			}
		}

		/**
			para2 
		*/
		if(p2_i != -1){   //array
			if (p2 < 0 && hash_index[0-p2] != 0){  //consants
				printf("[print_char]I don't think this if will active 0605\n");
				//para2 = (p2_i>10)?
				//hashmapArray.find(uuid)->arr_long[p2_i%10][hash_int[0-p2]]:
				//hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_long[hashmap.find(uuid)->arrayIndex[p2_i]%10][hash_int[0-p2]];

			}else if(p2<10 &&p2>=0){ //list
				printf("[print_char]I don't think this if will active 0605\n");
				//para2 = (p2_i>10)?
				//hashmapArray.find(uuid)->arr_long[p2_i%10][int_array[p2]]:
				//hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_long[hashmap.find(uuid)->arrayIndex[p2_i]%10][int_array[p2]];
			}else if(p2 >=100 ){ //encalve
				printf("[print_char]I don't think this if will active 0605\n");
				//para2 = (p2_i>10)?
				//hashmapArray.find(uuid)->arr_long[p2_i%10][hashmap.find(uuid)->v_int[p2-100]]:
				//hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_long[hashmap.find(uuid)->arrayIndex[p2_i]%10][hashmap.find(uuid)->v_int[p2-100]];
				//printf("uuid =%s  ; para2=%d\n",uuid,hashmap.find(uuid)->v_int[meta.p2-10]);	
			}else{
				//this is a array, but index is null
			}
		}else{	// no an array

			if (p2 < 0 && hash_index[0-p2] != 0){  //consants

				para2 = hash_int[0-p2];

			}else if(p2<10 && p2>=0){ //list

				para2 = char_array[p2];
			}else{ //encalve
	
				switch(p2/100){    //maybe type cast
					case 1:para2 = (char)hashmap.find(uuid)->v_int[p2-100];break;
					case 2:para2 = (char)hashmap.find(uuid)->v_double[p2-200];break;
					case 4:para2 = hashmap.find(uuid)->v_char[p2-400];break;
					case 5:para2 = (char)hashmap.find(uuid)->v_long[p2-500];break;
					case 6:para2 = (char)hashmap.find(uuid)->v_byte[p2-600];break;
				}
				//printf("uuid =%s  ; para2=%d\n",uuid,hashmap.find(uuid)->v_int[meta.p2-10]);	
			}
		}

/*if(Line == 47L){
	printf("l success op1=%ld\n",para1);
	printf("l success op2=%ld\n",para2);
	printf("l op=%d\n",meta.op);
}*/


		switch (op) {
			case -1:return_flag = para1;break;
			case 1:return_flag = para1 + para2;break; //+
			case 2:return_flag = para1 - para2;break; //-
			case 3:return_flag = para1 * para2;break; //*
			case 4:return_flag = para1 / para2;break; // /
			case 5:return_flag = para1 % para2;break; // %
			case 6:return_flag =( para1== para2?1:0);break;
	 		case 7:return_flag =( para1!= para2?1:0);break;
	  		case 8:return_flag =( para1> para2?1:0);break;
	  		case 9:return_flag =( para1< para2?1:0);break;
	  		case 10:return_flag =(para1>=para2?1:0);break;
	  		case 11:return_flag =(para1<=para2?1:0);break;
			//case 12:return_flag = para1 & para2;break;
			default:return_flag = -11;
		}

		if(para_i != -1){ // update to array
			printf("[print_char]I don't think this if will active 0605\n");
			/*if (para_name < 0 && hash_index[0-para_name] != 0){ //constant
				if(para_i>10){
					hashmapArray.find(uuid)->arr_long[para_i%10][hash_int[0-para_name]] = return_flag;
					return_flag = 1000;
				}else{
					hashmapArray.find(hashmap.find(uuid)->array[para_i])->arr_long[hashmap.find(uuid)->arrayIndex[para_i]%10][hash_int[0-para_name]] = return_flag;
					return_flag = 1000;
				}
			
			}else if(para_name >=100 ){ //encalve
				if(para_i>10){
					hashmapArray.find(uuid)->arr_long[para_i%10][hashmap.find(uuid)->v_int[p1-100]] = return_flag;
					return_flag = 1000;
				}else{
					hashmapArray.find(hashmap.find(uuid)->array[para_i])->arr_long[hashmap.find(uuid)->arrayIndex[para_i]%10][hashmap.find(uuid)->v_int[p1-100]] = return_flag;
					return_flag = 1000;
				}
			}
			*/
	
		}else if(para_name>0 && para_i == -1){  // update to variables
			//printf("d ==UPDATE to variables==\n");
			
			switch(para_name/100){    //maybe type cast
				case 1:hashmap.find(uuid)->v_int[para_name-100] = (char)return_flag;break;
				case 2:hashmap.find(uuid)->v_double[para_name-200] = (char)return_flag;break;
				case 4:hashmap.find(uuid)->v_char[para_name-400] = return_flag;break;
				case 5:hashmap.find(uuid)->v_long[para_name-500] = (char)return_flag;break;
				case 6:hashmap.find(uuid)->v_byte[para_name-600] = (char)return_flag;break;
			}
			return_flag = 1000;	
		}
		return return_flag;
}

long print_long(long Line,long* long_array,int* int_array,char* uuid,char* cuuid)//---------------------------int
{
//printf("----------------\n");
//ocall_print_string("go in print_int\n");
//printf("i Line=%ld\n",Line);		
		Table_meta meta=get_table_meta(Line);
/*if(Line == 29){
printf("----------------\n");
printf("Line=%ld\n",Line);
printf("op1=%d\n",meta.p1);
printf("op2=%d\n",meta.p2);
printf("op=%d\n",meta.op);
printf("para_name=%d\n",meta.para_name);
printf("----------------\n");    
}*/
		int p1 = meta.p1;
		int p1_i = meta.p1_i;
		int p2 = meta.p2;
		int p2_i = meta.p2_i;
		int op = meta.op;
		int para_name = meta.para_name;
		int para_i = meta.para_i;	
/*if(Line == 0 || Line == 1){
	printf("p1=%d\n",p1);
	printf("p1_i=%d\n",p1_i);
	printf("p2=%d\n",p2);
	printf("p2_i=%d\n",p2_i);
	printf("op=%d\n",op);
	printf("para_name=%d\n",para_name);
	printf("para_i=%d\n",para_i);
	printf("uuid=%s\n",uuid);
}*/

		long return_flag = -999;
		long para1,para2;
		


/*if(para_i>=700 || p1_i>=700){
	printf("[print_int]cuuid:%s Line=%ld\n",cuuid,Line);
}*/
		
		//return statement replacce! 0509
		if(p1==-2 && p1_i==-2 && p2==-2 && p2_i==-2 && op==-2){
			//printf("this is a return statement Line=%ld\n",Line);
			if(para_i != -1){
				printf("I don't think this if will active 0509\n");
			}else if(para_name>=100 && para_i == -1){ //only variables
				//printf("calluuid:%s \n",hashmap.find(uuid)->calluuid);
				hashmap.find(hashmap.find(uuid)->calluuid)->v_long[hashmap.find(uuid)->re[2]-100] = hashmap.find(uuid)->v_long[para_name-100];
			}else if(para_name<0 && para_i == -1){ //constant
				hashmap.find(hashmap.find(uuid)->calluuid)->v_long[hashmap.find(uuid)->re[2]-100] = hash_long[0-para_name];
			}
			//printf("20210720 1538 return_flag=%d\n",return_flag);
			return 1000;
			
		}

		/**
			para1 
		*/
		if(p1_i != -1){   //array
			//printf("20210720 come to 1545\n");
			if (p1 < 0 && hash_index[0-p1] != 0){  //consants
				if(p1_i>=70 && p1_i<=120){
					para1 = hashmapArray.find(uuid)->arr_long[p1_i%10][hash_long[0-p1]];
				}else if(p1_i < 10){
					para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_long[hashmap.find(uuid)->arrayIndex[p1_i]%10][hash_long[0-p1]];
				}else if(p1_i>=700 && p1_i<=1200){ //array field
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid a!]\n");}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_long[hash_long[0-p1]];
				}else if(p1_i>=1300 && p1_i<=1800){ // multi array field, we need p2 as one of index
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid b!]\n");}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_multi_long[hashmap.find(uuid)->v_long[p2-100]][hash_long[0-p1]];
				}else{
					//do nothing
				}
				printf("list 1562");
				
			}else if(p1<10 && p1>=0){ //list
				//printf("list 1564");
				if(p1_i>=70 && p1_i<=120){
					para1 = hashmapArray.find(uuid)->arr_long[p1_i%10][int_array[p1]];
				}else if(p1_i < 10){
					para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_long[hashmap.find(uuid)->arrayIndex[p1_i]%10][int_array[p1]];
				}else if(p1_i>=700 && p1_i<=1200){ //array field
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid c!]\n");}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_long[int_array[p1]];
				}else if(p1_i>=1300 && p1_i<=1800){ // multi array field, we need p2 as one of index
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid d!]\n");}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_multi_long[hashmap.find(uuid)->v_long[p2-100]][int_array[p1]];
				}else{
					//do nothing
				}

			}else if(p1 >=100 && p1<=699){ //encalve int~byte
				//int value = hashmap.find(uuid)->v_long[p1-100];
				//printf("1582value=%d\n",value);
				//printf("call0 uuid=%s,index=%d\n",hashmap.find(uuid)->array[p1_i],hashmap.find(uuid)->arrayIndex[p1_i]);
				if(p1_i>=70 && p1_i<=120){
					para1 = hashmapArray.find(uuid)->arr_long[p1_i%10][hashmap.find(uuid)->v_long[p1-100]];
				}else if(p1_i < 10){
					para1 =hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_long[hashmap.find(uuid)->arrayIndex[p1_i]%10][hashmap.find(uuid)->v_long[p1-100]];
				}else if(p1_i>=700 && p1_i<=1200){ //array field
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid e!]\n");}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_long[hashmap.find(uuid)->v_long[p1-100]];
				}else if(p1_i>=1300 && p1_i<=1800){ // multi array field, we need p2 as one of index
					if(hashmapPublicV.find(cuuid)==NULL){
						printf("[ERROR get cuuid f! cuuid:%s Line=%ld]\n",cuuid,Line);
					}
					para1 = hashmapPublicV.find(cuuid)[p1_i%10].arr_multi_long[hashmap.find(uuid)->v_long[p2-100]][hashmap.find(uuid)->v_long[p1-100]];
				}else{
					//do nothing
				}
			}else if(p1 == 10000){ //lengof method
				//printf("this meyhod is lengthof p1:%d p1_i:%d\n",p1,p1_i);
				if(p1_i>10){
					if(hashmapArray.find(uuid)->longsize[p1_i%10]<0){
						printf("[ERROR] I have not do this\n");
					}
					switch(p1_i/10){
						case 7:para1 = hashmapArray.find(uuid)->intsize[p1_i%10];break;
						case 8:para1 = hashmapArray.find(uuid)->doublesize[p1_i%10];break;
						case 10:para1 = hashmapArray.find(uuid)->charsize[p1_i%10];break;
						case 11:para1 = hashmapArray.find(uuid)->longsize[p1_i%10];break;
					}
				}else{
					int index = hashmap.find(uuid)->arrayIndex[p1_i];
					switch(index/10){
						case 7:para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->intsize[index%10];break;
						case 8:para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->doublesize[index%10];break;
						case 10:para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->charsize[index%10];break;
						case 11:para1 = hashmapArray.find(hashmap.find(uuid)->array[p1_i])->longsize[index%10];break;
					}
				}
			
			}else{
				//this is a array, but index is null
			}
		}else{	// no an array ,but possiable it is public variables

			if (p1 < 0 && hash_index[0-p1] != 0){  //consants

				para1 = hash_long[0-p1];

			}else if(p1<10 && p1>=0){ //list

				para1 = int_array[p1];
			}else if(p1>=20 && p1<=70){ // Public Variables , add on 0610/2020
				if(hashmapPublicV.find(cuuid) != NULL){
					para1 = hashmapPublicV.find(cuuid)[p1%10].v_i;
				}else{//init
					printf("[ERROR] print_int I don't think this will occur 6.10/2020\n");
				}
			}else{ //encalve
				//printf("here uuid=%s\n",uuid);
				switch(p1/100){    //maybe type cast
					case 1:para1 = hashmap.find(uuid)->v_int[p1-100];break;
					case 2:para1 = (long)hashmap.find(uuid)->v_double[p1-200];break;
					case 4:para1 = (long)hashmap.find(uuid)->v_char[p1-400];break;
					case 5:para1 = (long)hashmap.find(uuid)->v_long[p1-500];break;
					case 6:para1 = (long)hashmap.find(uuid)->v_byte[p1-600];break;
				}
				
				int ttpara1 = hashmap.find(uuid)->v_long[p1-100];   
				//printf("1649 uuid =%s  ; para1=%d\n",uuid,hashmap.find(uuid)->v_long[meta.p1-10]);	
			}
		}
//printf("i success op1=%d\n",para1);
		/**
			para2 
		*/
		if(p2_i != -1){   //array
			if (p2 < 0 && hash_index[0-p2] != 0){  //consants
				if(p2_i>10){
					para2 = hashmapArray.find(uuid)->arr_long[p2_i%10][hash_long[0-p2]];
				}else{
					para2 = hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_long[hashmap.find(uuid)->arrayIndex[p2_i]%10][hash_long[0-p2]];
				}
			}else if(p2<10 && p2>=0){ //list

				if(p2_i>10){
					para2 = hashmapArray.find(uuid)->arr_long[p2_i%10][int_array[p2]];
				}else{
					para2 = hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_long[hashmap.find(uuid)->arrayIndex[p2_i]%10][int_array[p2]];
				}

			}else if(p2 >=100 && p2<=500){ //encalve int~long
				//int value = hashmap.find(uuid)->v_long[p1-100];
				//printf("value=%d\n",value);
				//printf("call0 uuid=%s,index=%d\n",hashmap.find(uuid)->array[p1_i],hashmap.find(uuid)->arrayIndex[p1_i]);
				if(p2_i>10){
					para2 = hashmapArray.find(uuid)->arr_long[p2_i%10][hashmap.find(uuid)->v_long[p2-100]];
				}else{
					para2 =hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_long[hashmap.find(uuid)->arrayIndex[p2_i]%10][hashmap.find(uuid)->v_long[p2-100]];
				}
			}
		}else{	// no an array

			if (p2 < 0 && hash_index[0-p2] != 0){  //consants

				para2 = hash_long[0-p2];

			}else if(p2<10 && p2>=0){ //list

				para2 = int_array[p2];
			}else{ //encalve
	
				switch(p2/100){    //maybe type cast
					case 1:para2 = hashmap.find(uuid)->v_int[p2-100];break;
					case 2:para2 = (long)hashmap.find(uuid)->v_double[p2-200];break;
					case 4:para2 = (long)hashmap.find(uuid)->v_char[p2-400];break;
					case 5:para2 = (long)hashmap.find(uuid)->v_long[p2-500];break;
					case 6:para2 = (long)hashmap.find(uuid)->v_byte[p2-600];break;
				}
				//printf("uuid =%s  ; para2=%d\n",uuid,hashmap.find(uuid)->v_long[meta.p2-10]);	
			}
		}
/*if(Line == 0 || Line == 1){
	printf("i success op1=%d\n",para1);
	printf("i success op2=%d\n",para2);
	printf("i op=%d\n",meta.op);
}*/
		switch (op) {
			case -1:return_flag = para1;break;
			case 1:return_flag = para1 + para2;break; //+
			case 2:return_flag = para1 - para2;break; //-
			case 3:return_flag = para1 * para2;break; //*
			case 4:return_flag = para1 / para2;break; // /
			case 5:return_flag = para1 % para2;break; // %
			case 6:return_flag =( para1== para2?1:0);break;
	 		case 7:return_flag =( para1!= para2?1:0);break;
	  		case 8:return_flag =( para1> para2?1:0);break;
	  		case 9:return_flag =( para1< para2?1:0);break;
	  		case 10:return_flag =(para1>=para2?1:0);break;
	  		case 11:return_flag =(para1<=para2?1:0);break;
			case 12:return_flag = para1 & para2;break;
			case 13:return_flag = para1 | para2;break;
			case 14:return_flag = para1 ^ para2;break;
			case 15:return_flag = para1 << para2;break;
			case 16:return_flag = para1 >> para2;break;
			case 17:return_flag = (unsigned long)para1 >> para2;break;
			default:return_flag = -11;
		}


/*if(Line == 31L){
	printf("i success return_flag=%d\n",return_flag);	
}*/

//printf("i success return_flag=%d\n",return_flag);	
		if(para_i != -1){ // update to array
			//printf("i ==UPDATE to arrays==\n");
			if (para_name < 0 && hash_index[0-para_name] != 0){ //constant
				if(para_i>=70 && para_i<=120){
					hashmapArray.find(uuid)->arr_long[para_i%10][hash_long[0-para_name]] = return_flag;
					return_flag = 1000;
				}else if(para_i<10){
					hashmapArray.find(hashmap.find(uuid)->array[para_i])->arr_long[hashmap.find(uuid)->arrayIndex[para_i]%10][hash_long[0-para_name]] = return_flag;
					return_flag = 1000;
				}else if(para_i>=700 && para_i<=1200){ //array field
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid g!]\n");}
					hashmapPublicV.find(cuuid)[para_i%10].arr_long[hash_long[0-para_name]] = return_flag;
					return_flag = 1000;	
				}else if(para_i>=1300 && para_i<=1800){ // multi array field, we need p2 as one of index
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid h!]\n");}
					hashmapPublicV.find(cuuid)[para_i%10].arr_multi_long[hashmap.find(uuid)->v_long[p2_i-100]][hash_long[0-para_name]] = return_flag;
					return_flag = 1000;	
				}else{
					//do nothing
				}
			
			}else if(para_name >=100 ){ //encalve index
				if(para_i>=70 && para_i<=120){
					hashmapArray.find(uuid)->arr_long[para_i%10][hashmap.find(uuid)->v_long[para_name-100]] = return_flag;
					return_flag = 1000;
				}else if(para_i<10){
					hashmapArray.find(hashmap.find(uuid)->array[para_i])->arr_long[hashmap.find(uuid)->arrayIndex[para_i]%10][hashmap.find(uuid)->v_long[para_name-100]] = return_flag;
					
					return_flag = 1000;
				}else if(para_i>=700 && para_i<=1200){ //array field
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid i!]\n");}
					hashmapPublicV.find(cuuid)[para_i%10].arr_long[hashmap.find(uuid)->v_long[para_name-100]] = return_flag;
					return_flag = 1000;	
				}else if(para_i>=1300 && para_i<=1800){ // multi array field, we need p2_i as one of index
					if(hashmapPublicV.find(cuuid)==NULL){printf("[ERROR get cuuid j! cuuid:%s Line=%ld]\n",cuuid,Line);}
					hashmapPublicV.find(cuuid)[para_i%10].arr_multi_long[hashmap.find(uuid)->v_long[p2_i-100]][hashmap.find(uuid)->v_long[para_name-100]] = return_flag;
					/*if(Line==49){
						printf("d[i][j]:%d\n",hashmapPublicV.find(cuuid)[para_i%10].arr_multi_long[hashmap.find(uuid)->v_long[p2_i-100]][hashmap.find(uuid)->v_long[para_name-100]]);
					}*/
					return_flag = 1000;	
				}else{
					//do nothing
				}
			}
		}else if(para_name>=20 && para_name<=70){ // Public Variables , add on 0610/2020
				if(hashmapPublicV.find(cuuid) != NULL){
					switch(para_name/10){    //maybe type cast
						case 2:hashmapPublicV.find(cuuid)[para_name%10].v_i = return_flag;break;
						case 3:hashmapPublicV.find(cuuid)[para_name%10].v_d = return_flag;break;
						case 5:hashmapPublicV.find(cuuid)[para_name%10].v_c = return_flag;break;
						case 6:hashmapPublicV.find(cuuid)[para_name%10].v_l = return_flag;break;
						case 7:hashmapPublicV.find(cuuid)[para_name%10].v_b = return_flag;break;
					}
				}else{//init
					PNODE p = (PNODE)malloc(10*sizeof(PublicVariableNode));
					if(!hashmapPublicV.insert(cuuid,p)){
						printf("insert fail!! %s\n",cuuid);
					}
					switch(para_name/10){    //maybe type cast
						case 2:hashmapPublicV.find(cuuid)[para_name%10].v_i = return_flag;break;
						case 3:hashmapPublicV.find(cuuid)[para_name%10].v_d = return_flag;break;
						case 5:hashmapPublicV.find(cuuid)[para_name%10].v_c = return_flag;break;
						case 6:hashmapPublicV.find(cuuid)[para_name%10].v_l = return_flag;break;
						case 7:hashmapPublicV.find(cuuid)[para_name%10].v_b = return_flag;break;
					}
				}
				return_flag = 1000;	
		}else if(para_name>0 && para_i == -1){  // update to variables
			switch(para_name/100){    //maybe type cast
				case 1:hashmap.find(uuid)->v_long[para_name-100] = (int)return_flag;break;
				case 2:hashmap.find(uuid)->v_double[para_name-200] = (double)return_flag;break;
				case 4:hashmap.find(uuid)->v_char[para_name-400] = (char)return_flag;break;
				case 5:hashmap.find(uuid)->v_long[para_name-500] = return_flag;break;
				case 6:hashmap.find(uuid)->v_byte[para_name-600] = (int)return_flag;break;
			}
			/*if(Line == 61L){
				printf("20201119 %d\n",hashmap.find(uuid)->v_long[para_name-100]);
			}*/
			return_flag = 1000;	
		}
		//printf("20210720 return_flag=%d\n",return_flag);
		/*if(Line == 0 || Line == 1){
			printf("i success return_flag=%d\n",return_flag);	
		}*/
/*	
		if(return_flag==0){
			printf("p1=%d\n",p1);
			printf("p1_i=%d\n",p1_i);
			printf("p2=%d\n",p2);
			printf("p2_i=%d\n",p2_i);
			printf("op=%d\n",op);
			printf("para_name=%d\n",para_name);
			printf("para_i=%d\n",para_i);
			printf("uuid=%s\n",uuid);
		}
*/
		
		return return_flag;

}

int print_byte(long Line, char* byte_array,int* int_array,char* uuid)
{
	    printf("byte\n");
		Table_meta meta=get_table_meta(Line);
		int p1 = meta.p1;
		int p1_i = meta.p1_i;
		int p2 = meta.p2;
		int p2_i = meta.p2_i;
		int op = meta.op;
		int para_name = meta.para_name;
		int para_i = meta.para_i;

		
		int return_flag = -999;
		int para1,para2;
/*
printf("----------------\n");
printf("b Line=%ld\n",Line);
printf("b type=%d\n",meta.type);
printf("b op1=%d\n",meta.p1);
printf("b op2=%d\n",meta.p2);
printf("b op=%d\n",meta.op);
printf("b para_name=%d\n",meta.para_name);
printf("----------------\n");
*/


		
		//return statement replacce! 0509
		if(p1==-2 && p1_i==-2 && p2==-2 && p2_i==-2 && op==-2){
			//printf("this is a return statement Line=%ld\n",Line);
			if(para_i != -1){
				printf("I don't think this if will active 0509 byte\n");
			}else if(para_name>=600 && para_i == -1){ //only variables
				//printf("calluuid:%s \n",hashmap.find(uuid)->calluuid);
				hashmap.find(hashmap.find(uuid)->calluuid)->v_byte[hashmap.find(uuid)->re[2]-100] = hashmap.find(uuid)->v_int[para_name-100];
			}else if(para_name<0 && para_i == -1){ //constant
				hashmap.find(hashmap.find(uuid)->calluuid)->v_byte[hashmap.find(uuid)->re[2]-100] = hash_int[0-para_name];
			}
			return 1000;
		}

		/**
			para1 
		*/
		if(p1_i != -1){   //array
			if (p1 < 0 && hash_index[0-p1] != 0){  //consants

				para1 = (p1_i>10)?
				hashmapArray.find(uuid)->arr_byte[p1_i%10][hash_int[0-p1]]:
				hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_byte[hashmap.find(uuid)->arrayIndex[p1_i]%10][hash_int[0-p1]];

			}else if(p1<10 && p1>=0){ //list

				para1 = (p1_i>10)?
				hashmapArray.find(uuid)->arr_byte[p1_i%10][int_array[p1]]:
				hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_byte[hashmap.find(uuid)->arrayIndex[p1_i]%10][int_array[p1]];

			}else if(p1 >=600 && p1<=700){ //encalve byte
				
				para1 = (p1_i>10)?
				hashmapArray.find(uuid)->arr_byte[p1_i%10][hashmap.find(uuid)->v_int[p1-100]]:
				hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_byte[hashmap.find(uuid)->arrayIndex[p1_i]%10][hashmap.find(uuid)->v_int[p1-100]];
				
			}
		}else{	// no an array

			if (p1 < 0 && hash_index[0-p1] != 0){  //consants

				para1 = hash_int[0-p1];

			}else if(p1<10 && p1>=0){ //list

				para1 = byte_array[p1];
			}else{ //encalve
				//printf("here uuid=%s\n",uuid);
				//printf("hashmap.find(uuid)->v_byte[p1-600] %d\n",hashmap.find(uuid)->v_byte[p1-600]);
				switch(p1/100){    //maybe type cast
					case 1:para1 = hashmap.find(uuid)->v_int[p1-100];break;
					case 2:para1 = (int)hashmap.find(uuid)->v_double[p1-200];break;
					case 4:para1 = (int)hashmap.find(uuid)->v_char[p1-400];break;
					case 5:para1 = (int)hashmap.find(uuid)->v_long[p1-500];break;
					case 6:para1 = hashmap.find(uuid)->v_byte[p1-600];break;
				}
				//para1 = hashmap.find(uuid)->v_int[p1-100];   
				//printf("uuid =%s  ; para1=%d\n",uuid,hashmap.find(uuid)->v_byte[p1-600]);	
			}
		}
		/**
			para2 
		*/
		if(p2_i != -1){   //array
			if (p2 < 0 && hash_index[0-p2] != 0){  //consants

				para2 = (p2_i>10)?
				hashmapArray.find(uuid)->arr_byte[p2_i%10][hash_int[0-p2]]:
				hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_byte[hashmap.find(uuid)->arrayIndex[p2_i]%10][hash_int[0-p2]];

			}else if(p2<10 &&p2>=0){ //list

				para2 = (p2_i>10)?
				hashmapArray.find(uuid)->arr_byte[p2_i%10][byte_array[p2]]:
				hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_byte[hashmap.find(uuid)->arrayIndex[p2_i]%10][int_array[p2]];

			}else if(p2 >=100 ){ //encalve
	
				para2 = (p2_i>10)?
				hashmapArray.find(uuid)->arr_byte[p2_i%10][hashmap.find(uuid)->v_int[p2-100]]:
				hashmapArray.find(hashmap.find(uuid)->array[p2_i])->arr_byte[hashmap.find(uuid)->arrayIndex[p2_i]%10][hashmap.find(uuid)->v_int[p2-100]];
			}
		}else{	// no an array

			if (p2 < 0 && hash_index[0-p2] != 0){  //consants

				para2 = hash_int[0-p2];

			}else if(p2<10 && p2>=0){ //list

				para2 = byte_array[p2];
			}else{ //encalve
	
				switch(p2/100){    //maybe type cast
					case 1:para2 = hashmap.find(uuid)->v_int[p2-100];break;
					case 2:para2 = (int)hashmap.find(uuid)->v_double[p2-200];break;
					case 4:para2 = (int)hashmap.find(uuid)->v_char[p2-400];break;
					case 5:para2 = (int)hashmap.find(uuid)->v_long[p2-500];break;
					case 6:para2 = (int)hashmap.find(uuid)->v_byte[p2-600];break;
				}
				//printf("uuid =%s  ; para2=%d\n",uuid,hashmap.find(uuid)->v_int[meta.p2-10]);	
			}
		}

		switch (op) {
			case -1:return_flag = para1;break;
			case 1:return_flag = para1 + para2;break; //+
			case 2:return_flag = para1 - para2;break; //-
			case 3:return_flag = para1 * para2;break; //*
			case 4:return_flag = para1 / para2;break; // /
			case 5:return_flag = para1 % para2;break; // %
			case 6:return_flag =( para1== para2?1:0);break;
	 		case 7:return_flag =( para1!= para2?1:0);break;
	  		case 8:return_flag =( para1> para2?1:0);break;
	  		case 9:return_flag =( para1< para2?1:0);break;
	  		case 10:return_flag =(para1>=para2?1:0);break;
	  		case 11:return_flag =(para1<=para2?1:0);break;
			case 12:return_flag = para1 & para2;break;
			default:return_flag = -11;
		}
	
		if(para_i != -1){ // update to array
			//printf("i ==UPDATE to arrays==\n");
			if (para_name < 0 && hash_index[0-para_name] != 0){ //constant
				if(para_i>10){
					hashmapArray.find(uuid)->arr_byte[para_i%10][hash_int[0-para_name]] = return_flag;
					return_flag = 1000;
				}else{
					hashmapArray.find(hashmap.find(uuid)->array[para_i])->arr_byte[hashmap.find(uuid)->arrayIndex[para_i]%10][hash_int[0-para_name]] = return_flag;
					return_flag = 1000;
				}
			
			}else if(para_name >=100 ){ //encalve
				if(para_i>10){
					hashmapArray.find(uuid)->arr_byte[para_i%10][hashmap.find(uuid)->v_int[para_name-100]] = return_flag;
					return_flag = 1000;
				}else{
					hashmapArray.find(hashmap.find(uuid)->array[para_i])->arr_byte[hashmap.find(uuid)->arrayIndex[para_i]%10][hashmap.find(uuid)->v_int[para_name-100]] = return_flag;
					
					return_flag = 1000;
				}
			}
		}else if(para_name>0 && para_i == -1){  // update to variables
			//printf("b ==UPDATE to variables==\n");
			//hashmap.find(uuid)->v_byte[para_name-600] = return_flag;
			switch(para_name/100){    //maybe type cast
				case 1:hashmap.find(uuid)->v_int[para_name-100] = return_flag;break;
				case 2:hashmap.find(uuid)->v_double[para_name-200] = (double)return_flag;break;
				case 4:hashmap.find(uuid)->v_char[para_name-400] = (char)return_flag;break;
				case 5:hashmap.find(uuid)->v_long[para_name-500] = (int)return_flag;break;
				case 6:hashmap.find(uuid)->v_byte[para_name-600] = return_flag;break;
			}
			
			return_flag = 1000;	
		}
		printf("return_flag=%d\n",return_flag);
		return return_flag;
}



int print_array_i(long Line, int* int_array, int int_tail, char* uuid, char* ouuid, char* cuuid){

	// printf("uuid=%s\n", uuid);
	// printf("ouuid=%s\n", ouuid);
	// printf("cuuid=%s\n", cuuid);

	Table_meta meta=get_table_meta(Line);
	int type=meta.type;
	int p1 = meta.p1;
	int p1_i = meta.p1_i;
	int p2 = meta.p2;
	int p2_i = meta.p2_i;
	int op = meta.op;
	int para_name = meta.para_name;
	int para_i = meta.para_i;

	//printf("line=%ld p1=%d  p1_i=%d  p2=%d  p2_i=%d op=%d  para_name=%d  para_i=%d\n",Line,p1,p1_i,p2,p2_i,op,para_name,para_i);
	char *tmpuuid=(char*)malloc(33*sizeof(char));
	memcpy(tmpuuid,uuid,32);
	if(p1==-2&&p1_i==-2&&p2==-2&&p2_i==-2&&op==-2){
			printf("return array\n");
			//printf("uuid=%s, calluuid=%s, re[2]=%d\n",uuid,hashmap.find(uuid)->calluuid,hashmap.find(uuid)->re[2]);
			INODE node1=hashmapArray2.find(hashmap.find(uuid)->calluuid)->int_arrNodes[hashmap.find(uuid)->re[2]%10];
			INODE node2=hashmapArray2.find(uuid)->int_arrNodes[para_i%10];
			node2=hashmapArray2.find(uuid)->int_arrNodes[node2->oriLocation%10];
			if(node1->location==0){
				node1->location=hashmap.find(uuid)->re[2]%10;
				node1->oriLocation=hashmap.find(uuid)->re[2]%10;
				node1->data=(int*)malloc(sizeof(int)*node2->sz);
				node1->d=node2->d;
				for(int i=0;i<3;i++){
					node1->dimensions[i]=node2->dimensions[i];
				}
				for(int i=0;i<node2->sz;i++){
				node1->data[i]=node2->data[i];
			}
				return 1000;
			}
			node1=hashmapArray2.find(hashmap.find(uuid)->calluuid)->int_arrNodes[node1->oriLocation%10];

			for(int i=0;i<node2->sz;i++){
				node1->data[i]=node2->data[i];
			}


	}else if(p2==0){
		printf("type=7 p2=0\n");

		bool flag=true;
		int dim[3]={0};//dim[0] dim[1] dim[2] represent array's 1st 2nd 3th dimension 
		if(p1<0&&hash_index[0-p1]!=0){
			dim[0]=hash_int[0-p1];
			printf("1 dimension constant: %d  int_%d\n", p1,hash_int[0-p1]);

		}else if(p1>=100&&p1<700){
			dim[0]=hashmap.find(uuid)->v_int[p1-100];
			printf("1 dimension variable:%d %d\n",p1, hashmap.find(uuid)->v_int[p1-100]);
			
		}else{
			flag=false;
		}
		if(flag&&p1_i<0&&hash_index[0-p1_i]!=0){
			dim[1]=hash_int[0-p1_i];
			//printf("2 dimension constant: %d  int_%d\n", p1_i,hash_int[0-p1_i]);
		}else if(flag&&p1_i>=100&&p1_i<700){
			dim[1]=hashmap.find(uuid)->v_int[p1_i-100];
			//printf("2 dimension variable:%d %d\n",p1_i, hashmap.find(uuid)->v_int[p1_i-100]);
		}else{
			flag=false;
		}
		if(flag&&p2_i<0&&hash_index[0-p2_i]!=0){
			dim[2]=hash_int[0-p2_i];
			//printf("3 dimension constant: %d  int_%d\n", p2_i,hash_int[0-p2_i]);
		}else if(flag&&p2_i>=100&&p2_i<700){
			dim[2]=hashmap.find(uuid)->v_int[p2_i-100];
			//printf("3 dimension variable:%d %d\n",p2_i, hashmap.find(uuid)->v_int[p2_i-100]);
		}else{
			flag=false;
		}
		for(int i=0;i<3;i++){
			printf("dim[%d]=%d\n", i,dim[i]);
		}
		int d=0;// how many dimensions
		int sz=1;//array size
		for(int i=0;i<3;i++){
			if(dim[i]!=0){
				d++;
				sz*=dim[i];
			}
		}
		printf("uuid=%s  size=%d\n",uuid,sz);
		//printf("123\n");
		INODE node=hashmapArray2.find(uuid)->int_arrNodes[para_i%10];
		printf("456\n");
		if(node==NULL){
			printf("null\n");
		}
		node->d=d;//update d
		for(int i=0;i<d;i++){
			node->dimensions[i]=dim[i];//update dimensions
		}
		node->paramLoc=-1;
		node->data=(int*)malloc(sz*sizeof(int));//malllo space for data 
		node->sz=sz;

		return 1000;

	}else if(p2==1){
		printf("type=7 p2=1\n");
		int oriLoc=p1_i;
		printf("uuid: %s\n", uuid);
		if(hashmapArray2.find(uuid)!=NULL){
			printf("NOT null\n");
		}
		printf("para_i: %d\n", para_i);
		INODE node=hashmapArray2.find(uuid)->int_arrNodes[para_i%10];
		if(node==NULL){
			printf("null\n");
		}
		node->oriLocation=oriLoc;
		printf("123\n");
	
	}else if(p2==2){

		
		//ocall_print_string("type=7 p2=2\n");
		int loc=-1;
		int k=-1;
		if(para_i==-1){//int a=arr[0] left is variable
			//printf("int a=arr[0] before uuid: %s\n", uuid);
			INODE node1=hashmapArray2.find(uuid)->int_arrNodes[p1_i%10];
			// for(int i=0;i<3;i++){
			// 	printf("node->index[%d]=%d\n", i,node1->index[i]);
			// }
			// for(int i=0;i<3;i++){
			// 	printf("node->dimensions[%d]=%d\n", i,node1->dimensions[i]);
			// }
			int idx=calIntArrayIndex(node1);
			//printf("idx=%d\n", idx);
			if(node1->paramLoc!=-1){//is formular array param
				//printf("isformular array param %d\n",node1->paramLoc);
				for(k=0;k<10;k++){
					if(k==node1->paramLoc){
						loc=hashmap.find(uuid)->arrayIndex[k];
						memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
						break;
					}
				}
			}
			

			if(loc!=-1){
				
				node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->int_arrNodes[loc%10];
				//printf("5\n");
				
			}
			//printf("uuid=%s,  tmpuuid=%s\n", uuid,tmpuuid);
			
			
			int index=-1;//array index
			if(p1<0&&hash_index[0-p1]!=0){
				index=hash_int[0-p1];
			}else if(p1>=100&&p1<700){
				index=hashmap.find(uuid)->v_int[p1-100];
			}
			//printf("index=%d\n", index);
			idx+=index;//
			INODE node2=NULL;
			if(k!=-1){
				node2=hashmapArray2.find(hashmap.find(uuid)->array[k])->int_arrNodes[node1->oriLocation%10];
			}else{
				node2=hashmapArray2.find(uuid)->int_arrNodes[node1->oriLocation%10];
			}
			
			//printf("a=data[%d]\n",node2->data[idx]);
			//printf("\n\n");
			hashmap.find(uuid)->v_int[para_name-100]=node2->data[idx];//int a=arr[1][2][3]
			//printf("\n");
		}else{//arr[0]=3
			int loc=-1;
			int k=-1;
			
			INODE node1=hashmapArray2.find(uuid)->int_arrNodes[para_i%10];
			for(int i=0;i<3;i++){
				//printf("node->index[%d]=%d\n", i,node1->index[i]);
				//printf("node->dimensions[%d]=%d\n", i,node1->dimensions[i]);
			}
			int idx=calIntArrayIndex(node1);
			//printf("idx=%d\n", idx);
			if(node1->paramLoc!=-1){//is formular array param
				//printf("isformular array param %d\n",node1->paramLoc);
				for(k=0;k<10;k++){
					if(k==node1->paramLoc){
						loc=hashmap.find(uuid)->arrayIndex[k];
						memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
						break;
					}
				}
			}
			//printf("uuid=%s,  tmpuuid=%s\n", uuid,hashmap.find(uuid)->array[k]);
			if(loc!=-1){
				node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->int_arrNodes[loc%10];
				
			}
			
			
			int index=-1;//arr[index]=num
			int num=-1;
			if(para_name<0&&hash_index[0-para_name]!=0){
				index=hash_int[0-para_name];
			}else if(para_name>=100&&para_name<700){
				index=hashmap.find(uuid)->v_int[para_name-100];
			}
			if(p1<0&&hash_index[0-p1]!=0){
				num=hash_int[0-p1];
			}else if(p1>=100&&p1<700){
				num=hashmap.find(uuid)->v_int[p1-100];
			}
			//("2\n");
			idx+=index;
			INODE node2=NULL;
			if(k!=-1){
				//printf("k!=-1\n");
				node2=hashmapArray2.find(hashmap.find(uuid)->array[k])->int_arrNodes[node1->oriLocation%10];
			}else{
				//printf("k==-1\n");
				node2=hashmapArray2.find(uuid)->int_arrNodes[node1->oriLocation%10];
			}
			//printf("idx=%d\n",idx);
			// if(node2->data==NULL){
			// 	printf("NULL\n");
			// }
			node2->data[idx]=num;
			//printf("uuid=%s, calluuid=%s\n", uuid,tmpuuid);
		     //printf("data[%d]=%d\n", idx,num);
			//printf("data[%d]=%d",idx,num);
			//printf("\n\n");

		}
	
	}else if(p2==3){//arr2=arr1 arr2=arr1[0]
		//printf("type=7 p2=3\n");
		 
		 int loc=-1;
		 int k=-1;
		 
		INODE node1=hashmapArray2.find(uuid)->int_arrNodes[p1_i%10];
		// for(int i=0;i<3;i++){
		// 	printf("node->index[%d]=%d\n",i,node1->index[i]);
		// }
		// if(node1->paramLoc!=-1){//is formular array param
		// 		printf("isformular array param %d\n",node1->paramLoc);
		// 		for(k=0;k<10;k++){
		// 			if(k==node1->paramLoc){
		// 				loc=hashmap.find(uuid)->arrayIndex[k];
		// 				memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
		// 				break;
		// 			}
		// 		}
		// 	}
		// if(loc!=-1)
		// 		node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->int_arrNodes[loc%10];
		INODE node2=hashmapArray2.find(uuid)->int_arrNodes[para_i%10];
		node2->d=node1->d;//update d
		for(int i=0;i<5;i++){
			node2->dimensions[i]=node1->dimensions[i];//update dimesions
			node2->index[i]=node1->index[i];//update index
		}
		node2->oriLocation=node1->oriLocation;//update oriLocation
		for(int i=0;i<3;i++){
			///printf("node->index[%d]=%d\n",i,node1->index[i]);
		}
		//printf("uuid=%s, calluuid=%s\n", uuid,tmpuuid);
		//printf("node1: \n");
		//printNode(node1);
		//printf("node2: \n");
		//printNode(node2);
	
		
	}else if(p2==4){// append index
		//printf("type=7 p2=4\n");

		 int loc=-1;
		 int i=-1;
		 int k=-1;
		if(p1<0&&hash_index[0-p1]!=0){
			i=hash_int[0-p1];
		}else if(p1>=100&&p1<700){
			i==hashmap.find(uuid)->v_int[p1-100];
		}
		//printf("p1=%d i=%d\n",p1,i);
		INODE node=hashmapArray2.find(uuid)->int_arrNodes[para_i%10];

		SNODE snode=hashmap.find(uuid);
		//printf("1\n");
		node->paramLoc=p1_i;
		if(p1==0&&p1_i==0){
			for(k=0;k<10;k++){
				if(k==node->paramLoc){
					loc=snode->arrayIndex[k];
					memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
					break;
				}
			}
			//printf("uuid=%s, tmpuuid=%s\n", uuid,tmpuuid);
			
			if(snode==NULL){
				//printf("hashmap.find(uuid)==NULL\n");
			}else{
				//printf("hashmap.find(uuid)!=NULL\n");
			}
			if(hashmapArray2.find(snode->array[k])==NULL){
				//printf("hashmapArray2.find(snode->array[k])==NULL\n");
			}else{
				//printf("hashmapArray2.find(snode->array[k])!=NULL\n");
			}
			if(hashmapArray2.find(snode->array[k])!=NULL){
				INODE node2=hashmapArray2.find(snode->array[k])->int_arrNodes[loc%10];
				//printf("123\n");
				node->d=node2->d;//update d
				for(int i=0;i<5;i++){
				node->dimensions[i]=node2->dimensions[i];//update dimesions
				node->index[i]=node2->index[i];//update index
			}
			node->oriLocation=node2->oriLocation;//update oriLocation
			}
			
		}
		int j=0;
		for(int i=0;i<3;i++){
			//printf("node->index[%d]=%d\n",i,node->index[i]);
		}
		while(node->index[j]!=-1){
			j++;
			
		}
		
		node->index[j]=i;
		for(int i=0;i<3;i++){
			//printf("node->index[%d]=%d\n",i,node->index[i]);
		}
		
		
	}else if(p2==5){//get array length
		    //printf("type=7,p2=5\n");
			INODE node1=hashmapArray2.find(uuid)->int_arrNodes[p1_i%10];
			if(node1==NULL){
				printf("null\n");
			}
		    int d=0;
		    while(node1->index[d]!=-1){
		    	printf("indxex[i]=%d\n", node1->index[d]);
		    	d++;
		    }
		    int loc=-1;
		    int k=-1;
		 	if(node1->paramLoc!=-1){//is formular array param
				//printf("isformular array param %d\n",node1->paramLoc);
				for(k=0;k<10;k++){
					if(k==node1->paramLoc){
						loc=hashmap.find(uuid)->arrayIndex[k];
						memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
						break;
					}
				}
			}
			//printf("uuid=%s, tmpuuid=%s\n", uuid,tmpuuid);
			if(loc!=-1){
				node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->int_arrNodes[loc%10];
			}
		    //printf("d=%d dimensions[d]=%d\n", d,node1->dimensions[d]);
		    hashmap.find(uuid)->v_int[para_name-100]=node1->dimensions[d];

			
	}
	else if(p2==-1){
		//ocall_print_string("p2=-1\n");
		
	}
	free(tmpuuid);
	return 1000;
		
	// 这里还没有处理就直接return了，并没有处理成员变量的情况
	if (para_i >=700 && para_i<=1800 && ouuid != NULL) {	   // init member array
		printf("ouuid = %s", ouuid);
		if (hashmapMemberArray.find(ouuid) == NULL) {
			ANODE2 aNode = (ANODE2) malloc (sizeof(ArrayNode2));
			if (!hashmapMemberArray.insert(ouuid, aNode)) {
				printf("[hyr]insert member array fail!");
			}
		}
		for (int i = 0; i < int_tail; i++) {
			hashmapMemberArray.find(ouuid)->int_arrNodes[para_i%10]->data[i] = int_array[i];	
		}
		hashmapMemberArray.find(ouuid)->int_arrNodes[para_i%10]->size = int_tail; 
	} else if (para_i >=7000 && para_i<=18000 && cuuid != NULL) {	// init static member array
		printf("cuuid = %s", cuuid);
		if (hashmapStaticMemberArray.find(cuuid) == NULL) {
			ANODE2 aNode = (ANODE2) malloc (sizeof(ArrayNode2));
			if (!hashmapStaticMemberArray.insert(cuuid, aNode)) {
				printf("[hyr]insert static member array fail!");
			}
		}
		for (int i = 0; i < int_tail; i++) {
			hashmapStaticMemberArray.find(cuuid)->int_arrNodes[para_i%10]->data[i] = int_array[i];	
		}
		hashmapStaticMemberArray.find(cuuid)->int_arrNodes[para_i%10]->size = int_tail; 
	}



	// 原方案
	// if(para_i >=700 && para_i<=1200){  //field array
	// 	if(hashmapPublicV.find(cuuid) == NULL){
	// 		printf("[print_array_i] This is first create Cuuid=%s\n",cuuid);
	// 		PNODE p = (PNODE)malloc(10*sizeof(PublicVariableNode));
	// 		if(!hashmapPublicV.insert(cuuid,p)){
	// 			printf("insert fail!! %s\n",cuuid);
	// 		}
	// 	}	
	// 	if(p1_i <=10){
	// 		for(int i=0;i<int_tail;i++){
	// 			hashmapPublicV.find(cuuid)[para_i%10].arr_int[i] = int_array[i];
	// 		}
	// 		hashmapPublicV.find(cuuid)[para_i%10].intsize = int_tail;
	// 	}else{
	// 		printf("[print_array_i] I don't deal with this case I. 0601/2020\n");
	// 	}
	// }else if(para_i>=1300 && para_i<=1800){ //field multi array
	// 	if(hashmapPublicV.find(cuuid) == NULL){
	// 		printf("[print_array_i] This is first create Cuuid multi. cuuid=%s\n",cuuid);
	// 		PNODE p = (PNODE)malloc(10*sizeof(PublicVariableNode));
	// 		if(!hashmapPublicV.insert(cuuid,p)){
	// 			printf("insert fail!! %s\n",cuuid);
	// 		}
	// 	}
	// 	if(para_name != -1){
	// 		if(para_name >=100 && para_name<=200){ //this is index
	// 			if(p1_i <= 10){

	// 			}else if(p1_i >=70 && p1_i<=120){ //from ArrayNode
	// 				int size = hashmapArray.find(uuid)->intsize[p1_i%10];
	// 				for(int i=0;i<size;i++){
	// 				hashmapPublicV.find(cuuid)[para_i%10].arr_multi_int[hashmap.find(uuid)->v_int[para_name-100]][i] = hashmapArray.find(uuid)->arr_int[p1_i%10][i];
	// 				}
	// 				hashmapPublicV.find(cuuid)[para_i%10].intmultisize[hashmap.find(uuid)->v_int[para_name-100]] = size;
	// 			}
	// 		}else {
	// 			printf("[print_array_i] I don't deal with this case III. 0601/2020\n");
	// 		}
	// 	}else{
	// 		//do nothing
	// 	}
			
	// }else if(para_i >= 70 && para_i<=120){//70 80
	// 	if(p1_i > 10){
	// 		//memcpy(hashmapArray.find(uuid)->arr_int[para_i%10],hashmapArray.find(uuid)->arr_int[p1_i%10],hashmapArray.find(uuid)->intsize[p1_i%10]);
	// 		for(int i=0;i<hashmapArray.find(uuid)->intsize[p1_i%10];i++){
	// 			hashmapArray.find(uuid)->arr_int[para_i%10][i] = hashmapArray.find(uuid)->arr_int[p1_i%10][i];
	// 		}		
	// 	}else{
	// 		if(p1 == -1){ //array
	// 			if(hashmapArray.find(uuid)->arr_int[para_i%10] == NULL){
	// 				encall_initArray(uuid,para_i,int_tail,0);
	// 				for(int i=0;i<int_tail;i++){
	// 					hashmapArray.find(uuid)->arr_int[para_i%10][i] = int_array[i];
	// 				}
				
	// 			}else{
	// 				//memcpy(hashmapArray.find(uuid)->arr_int[para_i%10],int_array,int_tail);
	// 				for(int i=0;i<int_tail;i++){
	// 					//printf("B int_array[%d]=%d\n",i,int_array[i]);
	// 					hashmapArray.find(uuid)->arr_int[para_i%10][i] = int_array[i];
	// 				}
	// 			}
	// 		}else if(p1>=100){ //multiarray 
	// 				for(int i=0;i<int_tail;i++){
	// 					hashmapMultiArray.find(uuid)[para_i%10].arr_int[hashmap.find(uuid)->v_int[p1-100]][i] = int_array[i];
	// 				}
	// 				hashmapMultiArray.find(uuid)[para_i%10].intsize[hashmap.find(uuid)->v_int[p1-100]] = int_tail;
	// 				hashmapArray.find(uuid)->intsize[para_i%10] = -p1; //flag
	// 		}else if(p1<0){
	// 			printf("[ERROR] print_array_i  int_number type\n");
	// 		}
	// 	}
		
	// }else{
	// 	if(p1_i > 10){
	// 		memcpy(hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_int[hashmap.find(uuid)->arrayIndex[p1_i]%10],hashmapArray.find(uuid)->arr_int[p1_i%10],hashmapArray.find(uuid)->intsize[p1_i%10]);
	// 	}else{
	// 		memcpy(hashmapArray.find(hashmap.find(uuid)->array[p1_i])->arr_int[hashmap.find(uuid)->arrayIndex[p1_i]%10],int_array,int_tail);
	// 	}
	// }
	return 1000;
}




int print_array_c(long Line, char* char_array, int char_tail, char* uuid, char* ouuid, char* cuuid){


	
	//printf("==============================1===========================Line=%ld====\n",Line);
	//printf("enter  int print_array_c(long Line, int* int_array,int int_tail,char* uuid,char* cuuid)\n");
	
	// printf("uuid=%s\n",uuid);
	// printf("cuuid=%s\n",cuuid);
	Table_meta meta=get_table_meta(Line);
	int type=meta.type;
	int p1 = meta.p1;
	int p1_i = meta.p1_i;
	int p2 = meta.p2;
	int p2_i = meta.p2_i;
	int op = meta.op;
	int para_name = meta.para_name;
	int para_i = meta.para_i;	
	//printf("line=%ld p1=%d  p1_i=%d  p2=%d  p2_i=%d op=%d  para_name=%d  para_i=%d\n",Line,p1,p1_i,p2,p2_i,op,para_name,para_i);
		char *tmpuuid=(char*)malloc(33*sizeof(char));
		memcpy(tmpuuid,uuid,32);
		//printf("uuid=%s,  tmpuuid=%s\n", uuid,tmpuuid);
		if(p1==-2&&p1_i==-2&&p2==-2&&p2_i==-2&&op==-2){
				printf("return array\n");
				//printf("uuid=%s, calluuid=%s, re[2]=%d\n",uuid,hashmap.find(uuid)->calluuid,hashmap.find(uuid)->re[2]);
				CNODE node1=hashmapArray2.find(hashmap.find(uuid)->calluuid)->char_arrNodes[hashmap.find(uuid)->re[2]%10];
				CNODE node2=hashmapArray2.find(uuid)->char_arrNodes[para_i%10];
				node2=hashmapArray2.find(uuid)->char_arrNodes[node2->oriLocation%10];
				if(node1->location==0){
					node1->location=hashmap.find(uuid)->re[2]%10;
					node1->oriLocation=hashmap.find(uuid)->re[2]%10;
					node1->data=(char*)malloc(sizeof(char)*node2->sz);
					node1->d=node2->d;
					for(int i=0;i<3;i++){
						node1->dimensions[i]=node2->dimensions[i];
					}
					for(int i=0;i<node2->sz;i++){
					node1->data[i]=node2->data[i];
				}
					return 1000;
				}
				// printf("node1->loc=%d, node1->oriloc=%d\n",node1->location,node1->oriLocation);
				//printf("1\n");
				node1=hashmapArray2.find(hashmap.find(uuid)->calluuid)->char_arrNodes[node1->oriLocation%10];
				//printf("2\n");
			

				//printf("sz1=%d\n", node1->sz);
				//printf("sz2=%d\n", node2->sz);
				for(int i=0;i<node2->sz;i++){
					node1->data[i]=node2->data[i];
				}
				// for(int i=0;i<node2->sz;i++){
				// 	printf("arr[%d]=%d\n",i,node2->data[i]);
				// }
				// for(int i=0;i<node1->sz;i++){
				// 	printf("arr[%d]=%d\n",i,node1->data[i]);
				// }

		}else if(p2==0){
			printf("type=7 p2=0\n");

			bool flag=true;
			int dim[3]={0};//dim[0] dim[1] dim[2] represent array's 1st 2nd 3th dimension 
			if(p1<0&&hash_index[0-p1]!=0){
				dim[0]=hash_int[0-p1];
				printf("1 dimension constant: %d  int_%d\n", p1,hash_int[0-p1]);

			}else if(p1>=100&&p1<700){
				dim[0]=hashmap.find(uuid)->v_char[p1-100];
				printf("1 dimension variable:%d %d\n",p1, hashmap.find(uuid)->v_char[p1-100]);
				
			}else{
				flag=false;
			}
			if(flag&&p1_i<0&&hash_index[0-p1_i]!=0){
				dim[1]=hash_int[0-p1_i];
				//printf("2 dimension constant: %d  int_%d\n", p1_i,hash_double[0-p1_i]);
			}else if(flag&&p1_i>=100&&p1_i<700){
				dim[1]=hashmap.find(uuid)->v_char[p1_i-100];
				//printf("2 dimension variable:%d %d\n",p1_i, hashmap.find(uuid)->v_double[p1_i-100]);
			}else{
				flag=false;
			}
			if(flag&&p2_i<0&&hash_index[0-p2_i]!=0){
				dim[2]=hash_int[0-p2_i];
				//printf("3 dimension constant: %d  int_%d\n", p2_i,hash_double[0-p2_i]);
			}else if(flag&&p2_i>=100&&p2_i<700){
				dim[2]=hashmap.find(uuid)->v_char[p2_i-100];
				//printf("3 dimension variable:%d %d\n",p2_i, hashmap.find(uuid)->v_double[p2_i-100]);
			}else{
				flag=false;
			}
			for(int i=0;i<3;i++){
				printf("dim[%d]=%d\n", i,dim[i]);
			}
			int d=0;// how many dimensions
			int sz=1;//array size
			for(int i=0;i<3;i++){
				if(dim[i]!=0){
					d++;
					sz*=dim[i];
				}
			}
			printf("uuid=%s  size=%d\n",uuid,sz);
			//printf("123\n");
			CNODE node=hashmapArray2.find(uuid)->char_arrNodes[para_i%10];
			
			node->d=d;//update d
			for(int i=0;i<d;i++){
				node->dimensions[i]=dim[i];//update dimensions
			}
			printf("456\n");
			node->paramLoc=-1;
			node->data=(char*)malloc(sz*sizeof(char));//malllo space for data 
			node->sz=sz;

			return 1000;

		}else if(p2==1){
			//printf("type=7 p2=1\n");
			int oriLoc=p1_i;
			CNODE node=hashmapArray2.find(uuid)->char_arrNodes[para_i%10];
			node->oriLocation=oriLoc;
		
		}else if(p2==2){

			
			//ocall_print_string("type=7 p2=2\n");
			int loc=-1;
			int k=-1;
			if(para_i==-1){//int a=arr[0] left is variable
				//printf("int a=arr[0] before uuid: %s\n", uuid);
				CNODE node1=hashmapArray2.find(uuid)->char_arrNodes[p1_i%10];
				// for(int i=0;i<3;i++){
				// 	printf("node->index[%d]=%d\n", i,node1->index[i]);
				// }
				// for(int i=0;i<3;i++){
				// 	printf("node->dimensions[%d]=%d\n", i,node1->dimensions[i]);
				// }
				int idx=calCharArrayIndex(node1);
				//printf("idx=%d\n", idx);
				if(node1->paramLoc!=-1){//is formular array param
					//printf("isformular array param %d\n",node1->paramLoc);
					for(k=0;k<10;k++){
						if(k==node1->paramLoc){
							loc=hashmap.find(uuid)->arrayIndex[k];
							memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
							break;
						}
					}
				}
				

				if(loc!=-1){
					
					node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->char_arrNodes[loc%10];
					//printf("5\n");
					
				}
				//printf("uuid=%s,  tmpuuid=%s\n", uuid,tmpuuid);
				
				
				int index=-1;//array index
				if(p1<0&&hash_index[0-p1]!=0){
					index=hash_char[0-p1];
				}else if(p1>=100&&p1<700){
					index=hashmap.find(uuid)->v_char[p1-100];
				}
				//printf("index=%d\n", index);
				idx+=index;//
				CNODE node2=NULL;
				if(k!=-1){
					node2=hashmapArray2.find(hashmap.find(uuid)->array[k])->char_arrNodes[node1->oriLocation%10];
				}else{
					node2=hashmapArray2.find(uuid)->char_arrNodes[node1->oriLocation%10];
				}
				
				//printf("a=data[%d]\n",node2->data[idx]);
				//printf("\n\n");
				hashmap.find(uuid)->v_char[para_name-100]=node2->data[idx];//int a=arr[1][2][3]
				//printf("\n");
			}else{//arr[0]=3
				int loc=-1;
				int k=-1;
				
				CNODE node1=hashmapArray2.find(uuid)->char_arrNodes[para_i%10];
				for(int i=0;i<3;i++){
					//printf("node->index[%d]=%d\n", i,node1->index[i]);
					//printf("node->dimensions[%d]=%d\n", i,node1->dimensions[i]);
				}
				int idx=calCharArrayIndex(node1);
				//printf("idx=%d\n", idx);
				if(node1->paramLoc!=-1){//is formular array param
					//printf("isformular array param %d\n",node1->paramLoc);
					for(k=0;k<10;k++){
						if(k==node1->paramLoc){
							loc=hashmap.find(uuid)->arrayIndex[k];
							memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
							break;
						}
					}
				}
				//printf("uuid=%s,  tmpuuid=%s\n", uuid,hashmap.find(uuid)->array[k]);
				if(loc!=-1){
					node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->char_arrNodes[loc%10];
					
				}
				
				
				int index=-1;//arr[index]=num
				int num=-1;
				if(para_name<0&&hash_index[0-para_name]!=0){
					index=hash_char[0-para_name];
				}else if(para_name>=100&&para_name<700){
					index=hashmap.find(uuid)->v_char[para_name-100];
				}
				if(p1<0&&hash_index[0-p1]!=0){
					num=hash_char[0-p1];
				}else if(p1>=100&&p1<700){
					num=hashmap.find(uuid)->v_char[p1-100];
				}
				//("2\n");
				idx+=index;
				CNODE node2=NULL;
				if(k!=-1){
					//printf("k!=-1\n");
					node2=hashmapArray2.find(hashmap.find(uuid)->array[k])->char_arrNodes[node1->oriLocation%10];
				}else{
					//printf("k==-1\n");
					node2=hashmapArray2.find(uuid)->char_arrNodes[node1->oriLocation%10];
				}
				//printf("idx=%d\n",idx);
				// if(node2->data==NULL){
				// 	printf("NULL\n");
				// }
				node2->data[idx]=num;
				//printf("uuid=%s, calluuid=%s\n", uuid,tmpuuid);
			     //printf("data[%d]=%d\n", idx,num);
				//printf("data[%d]=%d",idx,num);
				//printf("\n\n");

			}
		
		}else if(p2==3){//arr2=arr1 arr2=arr1[0]
			//printf("type=7 p2=3\n");
			 
			 int loc=-1;
			 int k=-1;
			 
			CNODE node1=hashmapArray2.find(uuid)->char_arrNodes[p1_i%10];
			// for(int i=0;i<3;i++){
			// 	printf("node->index[%d]=%d\n",i,node1->index[i]);
			// }
			// if(node1->paramLoc!=-1){//is formular array param
			// 		printf("isformular array param %d\n",node1->paramLoc);
			// 		for(k=0;k<10;k++){
			// 			if(k==node1->paramLoc){
			// 				loc=hashmap.find(uuid)->arrayIndex[k];
			// 				memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
			// 				break;
			// 			}
			// 		}
			// 	}
			// if(loc!=-1)
			// 		node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->double_arrNodes[loc%10];
			CNODE node2=hashmapArray2.find(uuid)->char_arrNodes[para_i%10];
			node2->d=node1->d;//update d
			for(int i=0;i<5;i++){
				node2->dimensions[i]=node1->dimensions[i];//update dimesions
				node2->index[i]=node1->index[i];//update index
			}
			node2->oriLocation=node1->oriLocation;//update oriLocation
			for(int i=0;i<3;i++){
				///printf("node->index[%d]=%d\n",i,node1->index[i]);
			}
			//printf("uuid=%s, calluuid=%s\n", uuid,tmpuuid);
			//printf("node1: \n");
			//printNode(node1);
			//printf("node2: \n");
			//printNode(node2);
		
			
		}else if(p2==4){// append index
			//printf("type=7 p2=4\n");

			 int loc=-1;
			 int i=-1;
			 int k=-1;
			if(p1<0&&hash_index[0-p1]!=0){
				i=hash_char[0-p1];
			}else if(p1>=100&&p1<700){
				i==hashmap.find(uuid)->v_char[p1-100];
			}
			//printf("p1=%d i=%d\n",p1,i);
			CNODE node=hashmapArray2.find(uuid)->char_arrNodes[para_i%10];

			SNODE snode=hashmap.find(uuid);
			//printf("1\n");
			node->paramLoc=p1_i;
			if(p1==0&&p1_i==0){
				for(k=0;k<10;k++){
					if(k==node->paramLoc){
						loc=snode->arrayIndex[k];
						memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
						break;
					}
				}
				//printf("uuid=%s, tmpuuid=%s\n", uuid,tmpuuid);
				
				if(snode==NULL){
					//printf("hashmap.find(uuid)==NULL\n");
				}else{
					//printf("hashmap.find(uuid)!=NULL\n");
				}
				if(hashmapArray2.find(snode->array[k])==NULL){
					//printf("hashmapArray2.find(snode->array[k])==NULL\n");
				}else{
					//printf("hashmapArray2.find(snode->array[k])!=NULL\n");
				}
				if(hashmapArray2.find(snode->array[k])!=NULL){
					CNODE node2=hashmapArray2.find(snode->array[k])->char_arrNodes[loc%10];
					//printf("123\n");
					node->d=node2->d;//update d
					for(int i=0;i<5;i++){
					node->dimensions[i]=node2->dimensions[i];//update dimesions
					node->index[i]=node2->index[i];//update index
				}
				node->oriLocation=node2->oriLocation;//update oriLocation
				}
				
			}
			int j=0;
			for(int i=0;i<3;i++){
				//printf("node->index[%d]=%d\n",i,node->index[i]);
			}
			while(node->index[j]!=-1){
				j++;
				
			}
			
			node->index[j]=i;
			for(int i=0;i<3;i++){
				//printf("node->index[%d]=%d\n",i,node->index[i]);
			}
			
			

			
		

			
		}else if(p2==5){//get array length
			    //printf("type=10,p2=5\n");
				CNODE node1=hashmapArray2.find(uuid)->char_arrNodes[p1_i%10];
			    int d=0;
			    while(node1->index[d]!=-1){
			    	//printf("indxex[i]=%d\n", node1->index[d]);
			    	d++;
			    }
			    int loc=-1;
			    int k=-1;
			 	if(node1->paramLoc!=-1){//is formular array param
					//printf("isformular array param %d\n",node1->paramLoc);
					for(k=0;k<10;k++){
						if(k==node1->paramLoc){
							loc=hashmap.find(uuid)->arrayIndex[k];
							memcpy(tmpuuid,hashmap.find(uuid)->array[k],32);
							break;
						}
					}
				}
				//printf("uuid=%s, tmpuuid=%s\n", uuid,tmpuuid);
				if(loc!=-1){
					node1=hashmapArray2.find(hashmap.find(uuid)->array[k])->char_arrNodes[loc%10];
				}
			    //printf("d=%d dimensions[d]=%d\n", d,node1->dimensions[d]);
			    hashmap.find(uuid)->v_int[para_name-100]=node1->dimensions[d];

				
		}
		else if(p2==-1){
			//ocall_print_string("p2=-1\n");
			
		}
		free(tmpuuid);
		printf("leave  int print_array_c(long Line, int* int_array,int int_tail,char* uuid,char* cuuid)\n\na");
		return 1000;
		


	}