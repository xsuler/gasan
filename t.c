#include <stdio.h>
#include <stdint.h>

struct ff{
    int a;
    char b[4];
};

char a[10];
char b;
char c;
char d;


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
   printf("a: %p, b: %p, c:%p\n",a,b,c);
   printf("a: %d, b: %d,  ff: %d\n",a[1],b[1], f.b[0]);
}

int main(){
  printf("%p %p %p %p\n",&a,&b,&c,&d);
  return 0;
}
