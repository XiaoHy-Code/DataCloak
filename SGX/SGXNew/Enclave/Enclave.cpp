#include <stdarg.h>
#include <stdio.h>	  /* vsnprintf */
# include <unistd.h>
#include <string.h>
#include <sgx_cpuid.h>
#include <stdlib.h>
#include <string>
#include <string.h>
#define Table_Len 1000
#define MAX 100
#include "io/fcntl.h"
#include "io/mman.h"
#include "io/stat.h"
#include "io/stdio.h"
#include "io/stdlib.h"
#include "io/time.h"
#include "io/unistd.h"
#include <sgx_tcrypto.h>

using namespace std;
#include "Enclave.h"
#include "Enclave_t.h"  /* print_string */
#include "common.h"
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
struct Table_meta{
	int type;
	int p1;
	int p2;
	int op; 
	int para_name;
};

typedef struct Node {
	int v_int[100];
	double v_double[20];
	//float v_float[10];
	char v_char[20];
	int v_byte[20];
	long v_long[20];

	char invokeruuid[33];

}*SNODE, Node;

//------------==================--------HASHMAP-----------========================-------------------
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
		_value = node.key;
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
	if (table[index] == NULL)
		return ValueNULL;
	else
	{
		HashNode<Key, Value> * node = table[index];
		//printf("go in key\n");
		while (node)
		{
			//cout << "node->_key = " << node->_key << endl;
			if (node->_key == key)
				return node->_value;
			node = node->next;
		}

		printf("key is not find!\n");
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

HashMap<string, SNODE, HashFunc, EqualKey> hashmap(64); // HashMap
//------------==================--------HASHMAP-----------========================-------------------

void encall_varible(char* uuid,char* invokeruuid) { //int* k,
	//printf("encall_varible in enclave uuid:%s ; invokeruuid:%s\n",uuid,invokeruuid);
	SNODE s = (SNODE)malloc(sizeof(Node));
	
	if(!hashmap.insert(uuid,s)){
		printf("insert fail!! %s\n",uuid);
	}
	if(hashmap.find(invokeruuid)){
		//printf("search invokeuuid success %s\n",invokeruuid);
		memcpy(hashmap.find(uuid)->invokeruuid,invokeruuid,33);
		//printf("strncpy invokeuuid success %s\n",hashmap.find(uuid)->invokeruuid);
	}
	//printf("insert success!! %s\n",uuid);
}
void encall_deleteValue(char* uuid,char* useless) {
	//printf("delete in enclave uuid:%s\n",uuid);

	free(hashmap.find(uuid));
	hashmap.find(uuid) = NULL;

	hashmap.del(uuid);
	//printf("delete success\n");
}

//--------------------------------------------------------------

//char file[500]="/home/xidian/CF/MatrixEncrypt/SGXindex1";

char file[50]="/tmp/SGXindex";

int hash_int[Table_Len];
double hash_double[Table_Len];
float hash_float[Table_Len];
char hash_char[Table_Len];
long hash_long[Table_Len];
char hash_byte[Table_Len];

int *table=(int*)malloc(sizeof(int)*10000);


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
			break;
		case 'd':strncpy(buffer,buf+7,44);//double_
			double double_data;
			double_data=atof(buffer);
			hash_double[line]=double_data;
			break;
		case 'f':strncpy(buffer,buf+6,44);//float_
			float float_data;
			float_data=atof(buffer);
			hash_float[line]=(float)float_data;
			break;
		case 'c':strncpy(buffer,buf+5,44);//char_
			char char_data;
			char_data=*buffer;
			hash_char[line]=char_data;
			//hash_char[line]=double_data;
			break;
		case 'l':strncpy(buffer,buf+5,44);//long_
			long long_data;
			long_data=atol(buffer);
			hash_long[line]=long_data;
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
Table_meta get_table_meta(long Line)
{
	Table_meta meta;
	meta.type=*(table+Line*5);
	meta.p1=*(table+Line*5+1);
	meta.p2=*(table+Line*5+2);
	meta.op=*(table+Line*5+3);
	meta.para_name=*(table+Line*5+4);
	return meta;
}
char ret[50000];
long ret_len=0;
long g_line_num=0;
int split_file()
{
	char line[50]={0};
	int k=0;
	long line_num=0;
	ocall_print_string("splitting\n");
	//ocall_print_long(ret_len);
	for(long i=0;i<ret_len;i++){
		//printf("%c",ret[i]);
		if(ret[i]=='\n'){
			line[k]=0;
			if(k==0){
				continue;
			}
			encall_read_line(line,k,line_num);
			line_num++;
			k=0;
		}else{
			line[k]=ret[i];
			k++;
		}
	}
	g_line_num=line_num;
	
	//ocall_print_long(line_num);
	return 0;
}

int read_table(char* file)
{
	
	memset(ret,0,50000);
	char* key_t="1234567812345678";

	int reout=open(file,O_RDONLY,S_IRUSR);

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
		c[l]=0;
		unsigned char ppp[MAX];
		memset(ppp,0,MAX);
		ecall_ctr_decrypt(c,key_t,ppp,l);
		for(int i=0;i<l;i++){
		strncat(ret,(const char*)&ppp[i],1);
		}
		ret_len=ret_len+l;
		l=0;
		//ocall_print_long(ret_len);
	}
	//ocall_print_string("read ok\n");
	split_file();
	//printf("%d\n",table[18]);
	return 0;
}

int encall_table_load(void)
{
	//long s=0;
	//int* msgs=(int*)malloc(sizeof(int)*Table_Len);
	//memset(msgs,'\0',sizeof(int)*Table_Len);
	read_table(file);
	ocall_print_string("read ok\n");
	return 1;
}


int encall_read_line(char* in_buf,int buf_len,long line)
{
	int read_num=0;
	if(*in_buf>=48 && *in_buf<=57){// number
		read_num=atoi(in_buf);
	}else if(*in_buf == 45){
		read_num=atoi(in_buf);
	}else{
		//int in_flag=999;
		read_num=0-line;
		//int load_flagh=-998;
		encall_hash_readin(in_buf,line);
	}
	//printf("%d\n",read_num);
	table[line]=read_num;
	//Enclave_Table_length++;
	return 0;
}


//-------------hotcall---------------------
void EcallStartResponder( HotCall* hotEcall )
{
    //printf("create thread======\n");
    void (*callbacks[1])(void*,void*,int*,double*,float*,char*,long*,char*,char*);
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
}*/
void EcallStartResponder3( HotCall* hotEcall3 )
{
    void (*callback[1])(char*,char*);
    callback[1] = encall_varible;
    callback[2] = encall_deleteValue;
    HotCallTable callTable;
    callTable.numEntries = 1;
    callTable.callback  = callback;
    HotCall_waitForCall( hotEcall3, &callTable );
}
//-----------------------------------------

/*
int encall_switch_type_i(long Line,int* int_array,double* double_array,float* float_array,char* char_array,long* long_array,char* byte_array,char* uuid) {
//ocall_print_string("go in encall_switch_type_i\n"); void* data,void* rei
//printf("encall_switch_type_i in enclave uuid:%s\n",uuid);
	//int *data1 = (int*)data;
        //int Line = *data1;
printf("Line=%d\n",Line);
	int type=*(table+Line*5);
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
		case 2:return_flag = print_double(Line, double_array,uuid);break;
		case 3:return_flag = print_float(Line, float_array,uuid);break;
		case 4:return_flag = print_char(Line, char_array,uuid);break;
		case 5:return_flag = print_long(Line, long_array,uuid);break;
		case 6:return_flag = print_byte(Line, byte_array,uuid);break;
		default:return_flag = -5;
	}
	// print_array();
        //printf("return num=%d\n",return_flag);
        //ocall_send_i(return_flag);
       //int *re = (int*)rei;
      // *re = return_flag;
	return return_flag;
}
*/

void encall_switch_type_get_i(void* data,void* rei,int* int_array,double* double_array,float* float_array,char* char_array,long* long_array,char*
byte_array,char* uuid) {
	long *data1 = (long*)data;
        long Line = *data1;
	//int type=*(table+Line*5);
	int return_flag = -1;
//printf("get Line=%d\n",Line);
	switch (*(table+Line*5)) {
		case 1:return_flag = print_int(Line, int_array,uuid);break;
		case 2:return_flag = print_double(Line, double_array,uuid);break;
		case 3:return_flag = print_float(Line, float_array,uuid);break;
		case 4:return_flag = print_char(Line, char_array,uuid);break;
		case 5:return_flag = print_long(Line, long_array,uuid);break;
		case 6:return_flag = print_byte(Line, byte_array,uuid);break;
		default:return_flag = -5;
	}
       int *re = (int*)rei;
       *re = return_flag;
}

void encall_switch_type_branch(void* data,void* rei,int* int_array,double* double_array,float* float_array,char* char_array,long* long_array,char* byte_array,char* uuid) {

	long *data1 = (long*)data;
        long Line = *data1;
	int return_flag = -1;
/*if(Line == 75){
	printf("[Error] Line=%ld\n",Line);
	printf("[Error] type=%d\n",*(table+Line*5));
	printf("[Error] p1=%d\n",*(table+Line*5+1));
	printf("[Error] p2=%d\n",*(table+Line*5+2));
	printf("[Error] op=%d\n",*(table+Line*5+3));
	printf("[Error] re=%d\n",*(table+Line*5+4));
}*/	
	switch (*(table+Line*5)) {
		case 1:return_flag = print_int(Line, int_array,uuid);break;
		case 2:return_flag = print_double(Line, double_array,uuid);break;
		case 3:return_flag = print_float(Line, float_array,uuid);break;
		case 4:return_flag = print_char(Line, char_array,uuid);break;
		case 5:return_flag = print_long(Line, long_array,uuid);break;
		case 6:return_flag = print_byte(Line, byte_array,uuid);break;
		default:return_flag = -5;
	}
	
       int *re = (int*)rei;
       *re = return_flag;
}

void encall_switch_type_update(void* data,void* rei,int* int_array,double* double_array,float* float_array,char* char_array,long* long_array,char* byte_array,char* uuid) {
	long *data1 = (long*)data;
        long Line = *data1;
	int return_flag = -1;
	
		switch (*(table+Line*5)) {
			case 1:return_flag = print_int(Line, int_array,uuid);break;
			case 2:return_flag = print_double(Line, double_array,uuid);break;
			case 3:return_flag = print_float(Line, float_array,uuid);break;
			case 4:return_flag = print_char(Line, char_array,uuid);break;
			case 5:return_flag = print_long(Line, long_array,uuid);break;
			case 6:return_flag = print_byte(Line, byte_array,uuid);break;
			default:return_flag = -5;
		}
		

		
 	int *re = (int*)rei;
        *re = return_flag;
}
/*
double encall_switch_type_d(long Line, int* int_array, int lenint,double* double_array, int lendouble,float* float_array, int lenfloat,char* char_array, int lenchar,long* long_array, int lenlong,char* byte_array, int lenbyte) {
printf("into encall_switch_type_d\n");
	int type=*(table+Line*5);
	if (type == 10) {
		return 0;
	}
	double return_flag = -1;
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

long encall_switch_type_l(long Line, int* int_array, int lenint,double* double_array, int lendouble,float* float_array, int lenfloat,char* char_array, int lenchar,long* long_array, int lenlong,char* byte_array, int lenbyte) {
//ocall_print_string("go in encall_switch_type_l\n");
	int type=*(table+Line*5);
	if (type == 10) {
		return 0;
	}
	long return_flag = -1;
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

char encall_switch_type_b(long Line, int* int_array, int lenint,double* double_array, int lendouble,float* float_array, int lenfloat,char* char_array, int lenchar,long* long_array, int lenlong,char* byte_array, int lenbyte) {
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
//----------------------------------------------------------------------------------------------------------

int print_int(long Line,int* int_array,char* uuid)//---------------------------int
{
//ocall_print_string("go in print_int\n");
		
		Table_meta meta=get_table_meta(Line);
/*if(Line == 75){
printf("----------------\n");
printf("Line=%ld\n",Line);
printf("op1=%d\n",meta.p1);
printf("op2=%d\n",meta.p2);
printf("op=%d\n",meta.op);
printf("para_name=%d\n",meta.para_name);
printf("uuid=%s\n",uuid);
printf("----------------\n");    
}*/
		int return_flag = -999;
		int para1,para2;
		if (get_table_meta(Line).p1 < 0){  //consants
			para1 = hash_int[0-get_table_meta(Line).p1];
		}else if(get_table_meta(Line).p1<10 && get_table_meta(Line).p1>=0){ //list
			para1 = int_array[get_table_meta(Line).p1];
		}else if(get_table_meta(Line).p1 > 150){
			//printf("[zystble1105]calleePre para1 before %s\n",hashmap.find(uuid)->invokeruuid);
			para1 = hashmap.find(hashmap.find(uuid)->invokeruuid)->v_int[get_table_meta(Line).p1-100];
			//printf("[zystble1105]calleePre para1:%d\n",para1);
		}else{ //encalve
	
			para1 = hashmap.find(uuid)->v_int[get_table_meta(Line).p1-100];   
			//printf("uuid =%s  ; para1=%d\n",uuid,hashmap.find(uuid)->v_int[meta.p1-10]);	
		}
		if (get_table_meta(Line).p2 < 0){  //consants
			para2 = hash_int[0-get_table_meta(Line).p2];
		}else if(get_table_meta(Line).p2<10 && get_table_meta(Line).p2>=0){ //list
			para2 = int_array[get_table_meta(Line).p2];
		}else{ //encalve
	
			para2 = hashmap.find(uuid)->v_int[get_table_meta(Line).p2-100];   
		}
/*if(Line == 75){
printf("success op1=%d\n",para1);
printf("success op2=%d\n",para2);
}*/
		switch (get_table_meta(Line).op) {
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
		if (get_table_meta(Line).para_name>0) {  //update
			if(get_table_meta(Line).para_name == 150){
				hashmap.find(hashmap.find(uuid)->invokeruuid)->v_int[get_table_meta(Line).para_name-100] = return_flag;
				//printf("return--150 %d\n",hashmap.find(hashmap.find(uuid)->invokeruuid)->v_int[get_table_meta(Line).para_name-100]);
			}else{
				hashmap.find(uuid)->v_int[get_table_meta(Line).para_name-100] = return_flag;
				//printf("B\n");
			}
			return_flag = 1000;	
		}
		
		return return_flag;

}

double print_double(long Line, double* double_array,char* uuid)//---------------------------double
{
		Table_meta meta=get_table_meta(Line);
		double return_flag = -999;
		double para1,para2;

/*printf("--------meta--------\n");
printf("d Line=%ld\n",Line);
printf("d op1=%d\n",meta.p1);
printf("d op2=%d\n",meta.p2);
printf("d op=%d\n",meta.op);
printf("d para_name=%d\n",meta.para_name);
printf("----------------\n"); */

		if (meta.p1 < 0){  //consants
			para1 = hash_double[0-meta.p1];
		}else if(meta.p1<10 && meta.p1>=0){ //list
			para1 = double_array[meta.p1];
		}else{ //encalve
			para1 = hashmap.find(uuid)->v_double[meta.p1 - 600];
		}
		
		if (meta.p2 < 0){  //consants
			para2 = hash_double[0-meta.p2];
		}else if(meta.p2<10 && meta.p2>=0){ //list
			para2 = double_array[meta.p2];
		}else{ //encalve
			para2 = hashmap.find(uuid)->v_double[meta.p2 - 600];
		}
		//printf("pa1=%lf,pa2=%lf\n",para1,para2);
		//printf("d op=%d\n",meta.op);
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
			//case 12:return_flag= para1 & para2;break;
			default:return_flag = -11;
		}
		if( meta.para_name>0){
			if(meta.op != 2){			
				hashmap.find(uuid)->v_int[meta.para_name - 600] = return_flag;                           //   edit for only Pi of Hadoop on 8.19
			}else{
				hashmap.find(uuid)->v_double[meta.para_name- 600] = return_flag;
			}
			return_flag = 1000;
		}
//printf("double p1=%lf\n",para1);
//printf("double p2=%lf\n",para2);
//printf("return_flag=%lf\n",return_flag); 
//ocall_print_string("d success\n");
		return return_flag;
}

float print_float(long Line, float* float_array,char* uuid)//---------------------------float
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

int print_char(long Line, char* char_array,char* uuid)//---------------------------char
{
//ocall_print_string("Go to c print_char\n");		
		Table_meta meta=get_table_meta(Line);
		int return_flag = -99;
		char para1,para2;

		if (meta.p1 < 0){  //consants
			para1 = hash_int[0-meta.p1];                             //edit for pagerank on 8.18  hash_int
		}else if(meta.p1<10 && meta.p1>=0){ //list
			para1 = char_array[meta.p1];
		}else{ //encalve
			para1 = hashmap.find(uuid)->v_char[meta.p1 - 400];
		}
		
		if (meta.p2 < 0){  //consants
			para2 = hash_int[0-meta.p2];
		}else if(meta.p2<10 && meta.p2>=0){ //list
			para2 = char_array[meta.p2];
		}else{ //encalve
			para2 = hashmap.find(uuid)->v_char[meta.p2 - 400];
		}
//printf("op1=%d\n",para1);
//printf("op2=%d\n",para2);
//printf("op=%d\n",meta.op);
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
			case 12:return_flag= para1 & para2;break;
			default:return_flag = -11;
		}
		//printf("return_flag=%d\n",return_flag);
		if (meta.para_name>0) { 
			//ocall_print_string("update char \n");
			hashmap.find(uuid)->v_char[meta.para_name - 400] = return_flag;
			//printf("return_flag=%c\n",get_stacktop(s)->v_char[meta.para_name % 40]);
			return_flag = 1000;
		}
//ocall_print_string("c success\n");
		return return_flag;
}

long print_long(long Line, long* long_array,char* uuid)//---------------------------long
{
//ocall_print_string("go in print_long\n");
		Table_meta meta=get_table_meta(Line);
/*
printf("------meta------\n");
printf("l Line=%ld\n",Line);
printf("l type=%d\n",meta.type);
printf("l op1=%d\n",meta.p1);
printf("l op2=%d\n",meta.p2);
printf("l op=%d\n",meta.op);
printf("l para_name=%d\n",meta.para_name);
printf("----------------\n");

printf("------long array------\n");
for(int i=0;i<20;i++){
	printf("%ld ",long_array[i]);
}
printf("\n");*/
		long return_flag = -999;
		long para1,para2;
		if (meta.p1 < 0){  //consants
			para1 = hash_long[0-meta.p1];
		}else if(meta.p1<10 && meta.p1>=0){ //list
			para1 = long_array[meta.p1];
		}else{ //encalve
			para1 = hashmap.find(uuid)->v_long[meta.p1 - 600];
		}
		
		if (meta.p2 < 0){  //consants
			para2 = hash_long[0-meta.p2];
		}else if(meta.p2<10 && meta.p2>=0){ //list
			para2 = long_array[meta.p2];
		}else{ //encalve
			para2 = hashmap.find(uuid)->v_long[meta.p2 - 600];
		}
		
		switch (meta.op) {
			case -1:return_flag = para1;break;   //x=2; or x=y;
			case 1:return_flag = para1 + para2;break; //+
			case 2:return_flag = para1 - para2;break; //-
			case 3:return_flag = para1 * para2;break; //*
			case 4:return_flag = para1 / para2;break; // /
			case 5:return_flag = para1 % para2;break; // %
			case 6:return_flag=( para1==para2?1:0);break;
	 		case 7:return_flag=( para1!=para2?1:0);break;
	  		case 8:return_flag=( para1>para2?1:0);break;
	  		case 9:return_flag=( para1<para2?1:0);break;
	  		case 10:return_flag=( para1>=para2?1:0);break;
	  		case 11:return_flag=( para1<=para2?1:0);break;	
			case 12:return_flag= para1 & para2;break;
			default:return_flag = -11;
		}
		//printf("Line is:%ld\n",Line);
		//printf("return is:%ld\n",return_flag);
		//printf("op is:%d\n",meta.op);
		//printf("meta.para_name is:%d\n",meta.para_name);
		if (meta.para_name>0) { 
			hashmap.find(uuid)->v_long[meta.para_name - 600] = return_flag;
//printf("long p1=%ld\n",para1);
//printf("long p2=%ld\n",para2);
//printf("return_flag=%ld\n",return_flag);
			return_flag = 1000;
		}
//ocall_print_string("l success\n");
		return return_flag;
}

int print_byte(long Line, char* byte_array,char* uuid)//---------------------------byte       edit 7.16  zystble
{
		Table_meta meta=get_table_meta(Line);
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
		Table_meta lastmeta = get_table_meta(Line-1L);		
/*
printf("----------------\n");
printf("b last Line=%ld\n",Line-1L);
printf("b last type=%d\n",lastmeta.type);
printf("b last op1=%d\n",lastmeta.p1);
printf("b last op2=%d\n",lastmeta.p2);
printf("b last op=%d\n",lastmeta.op);
printf("b last para_name=%d\n",lastmeta.para_name);
printf("----------------\n"); */

		int return_flag = -99;                                                    //edited
		int para1,para2;                                                          //edited unsigned char to int
		double para1_d;		
		
		if (meta.p1 < 0){  //consants
			para1 = hash_int[0-meta.p1];
		}else if(meta.p1<10 && meta.p1>=0){ //list
			para1 = byte_array[meta.p1];
		}
		else if(meta.p1 == 600 && lastmeta.op != 2 ){                          //deal with (double) if(a >b)  on 8.16 by zystble  from print_double
			para1 = hashmap.find(uuid)->v_int[meta.p1-600];
		}                                                                                            //edit 8.19                      
		else{ //encalve
			switch (lastmeta.type){
				case 1:para1 = hashmap.find(uuid)->v_int[meta.p1 - 600];break;
				case 2:para1_d = hashmap.find(uuid)->v_double[meta.p1 - 600];break;
				//case 3:para1 = get_stacktop(s)->v_float[meta.p1 % 60];
				//case 4:para1 = get_stacktop(s)->v_[meta.p1 % 60];
				case 5:para1 = hashmap.find(uuid)->v_long[meta.p1 - 600];break;
				//case 6:para1 = get_stacktop(s)->v_long[meta.p1 % 60];
				default:para1 = NULL;
			}
		}
		if (meta.p2 < 0){  //consants
			para2 = hash_int[0-meta.p2];                                      //edited
//printf("b success mate.p2 = %d\n",hash_int[0-meta.p2]);
		}else if(meta.p1<10 && meta.p1>=0){ //list
			para2 = byte_array[meta.p2];
		}else{ //encalve
			switch (lastmeta.type){
				case 1:para2 = hashmap.find(uuid)->v_int[meta.p1 - 600];
				case 2:para2 = hashmap.find(uuid)->v_double[meta.p1 - 600];
				//case 3:para1 = get_stacktop(s)->v_float[meta.p1 % 60];
				//case 4:para1 = get_stacktop(s)->v_[meta.p1 % 60];
				case 5:para2 = hashmap.find(uuid)->v_long[meta.p1 - 600];
				//case 6:para1 = get_stacktop(s)->v_long[meta.p1 % 60];
				default:para2 = NULL;
			}
		}
		if(lastmeta.type != 2){
			switch (meta.op) {
				case -1:return_flag = para1;break;   //x=2; or x=y;
				case 1:return_flag = para1 + para2;break; //+
				case 2:return_flag = para1 - para2;break; //-
				case 3:return_flag = para1 * para2;break; //*
				case 4:return_flag = para1 / para2;break; // /
				case 5:return_flag = para1 % para2;break; // %
				case 6:return_flag=( para1==para2?1:0);break;
	 			case 7:return_flag=( para1!=para2?1:0);break;
	  			case 8:return_flag=( para1>para2?1:0);break;
	  			case 9:return_flag=( para1<para2?1:0);break;
	  			case 10:return_flag=( para1>=para2?1:0);break;
	  			case 11:return_flag=( para1<=para2?1:0);break;
				case 12:return_flag= para1 & para2;break;
				default:return_flag = -11;
			}
			if (meta.para_name>0) { 
	//			printf("edit on 8.16 by zystble  enter print_byte!!!\n");
				hashmap.find(uuid)->v_byte[meta.para_name - 600] = return_flag;                //edit on 8.16 by zystble  v_int //  edit on 8.18 v_byte
				return_flag = 1000;
			}
		}else{
			switch (meta.op) {
				case -1:return_flag = para1_d;break;   //x=2; or x=y;
				case 1:return_flag = para1_d + para2;break; //+
				case 2:return_flag = para1_d - para2;break; //-
				case 3:return_flag = para1_d * para2;break; //*
				case 4:return_flag = para1_d / para2;break; // /
				case 5:return_flag = para1 % para2;break; // %                       edit 7.19
				case 6:return_flag=( para1_d==para2?1:0);break;
	 			case 7:return_flag=( para1_d!=para2?1:0);break;
	  			case 8:return_flag=( para1_d>para2?1:0);break;
	  			case 9:return_flag=( para1_d<para2?1:0);break;
	  			case 10:return_flag=( para1_d>=para2?1:0);break;
	  			case 11:return_flag=( para1_d<=para2?1:0);break;
				case 12:return_flag= para1 & para2;break;
				default:return_flag = -11;
			}
			if (meta.para_name>0) { 
	//			printf("edit on 8.16 by zystble  enter print_byte!!!\n");
				hashmap.find(uuid)->v_byte[meta.para_name - 600] = return_flag;                //edit on 8.16 by zystble
				return_flag = 1000;
			}
		}
//printf("b success return_flag:%d\n",return_flag);
		return return_flag;
}
