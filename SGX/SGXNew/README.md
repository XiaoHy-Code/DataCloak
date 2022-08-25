flag re<0 means error occured!  
...
//error -999    :input data type donot match matrix  
//error -5      :type not exist  
//error -1      :line number is out of range  
//error -2      :matrix not load yet  
//error -3      :matrix internal data mistake  
//error -6	:unrecognised matrix meta  
//error -11	:undefined operation symbol  
...

interface SGX_Lookup  
1.lookup data and compute them in enclave return the value  
SGX_Lookup->init enclave  
	  ->encall_table_load--->  
	  ->ecall  
	  ->destroy enclave  

//change the length of input array to 30;  

//5.11  
add folder io in App  
add folder io in Enclave  
Enclave.edl : import all edl from Enclave/io  
Encalve.cpp : include add .h from Enclave/io  
Makefile : $(wildcard Enclave/io/*.cpp) $(wildcard App/io/*.cpp)  

#make
#make clean
