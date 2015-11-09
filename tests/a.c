#include <stdio.h>
void eval(int x);
int main(){
    int sym_x,y;
    sym_x = 10;
    y=1;
    sym_x = sym_x-1;
    printf("%d",sym_x);
    eval(sym_x);
}
