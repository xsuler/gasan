#include<stdio.h>
#include<stdint.h>
#include<limits.h>

shadow_base=0;



int main(){
char a[10];
printf("%d %d\n",sizeof(int),__alignof__(a[0]));
return 0;
}
