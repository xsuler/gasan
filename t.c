#include <stdio.h>
#include <stdint.h>
#include "t.h"

char a[5]={0};
char b=0;
char c=0;

struct ff{
    int a;
    char b[4];
};

void enter_func(char* name){

}
 
void leave_func(){

}


void mark_valid(char* addr, int64_t size){
 printf("addr: %p, size: %ld\n",addr,size);
}
void mark_invalid(char* addr, int64_t size){
 printf("inv addr: %p, size: %ld\n",addr,size);
}


void report_xasan(int64_t* addr, int64_t size, int64_t type){
}



void func(){
   char a[4];
   char b[4];
   char c[4];
   struct ff f;
   f.b[0]=22;
   a[3]=123;
   b[1]=12;
}

int main(){
  func();
  printf("%p %p %p\n",&a,&b,&c);
  return 0;
}
