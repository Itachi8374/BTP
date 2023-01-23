#include<assert.h>
int main(){
int x1,y1,i1,x0,y0,n,i0;
x0=5;
y0=10;
for(i0=1;i0<100;i0++){
    if(i0%3==0){
        x0=x0+1;
        y0=y0+1;
    }
    else if (i0%3==1){
       x0=x0-2;
       y0=y0*2;
    }
    else
  x0=x0+1;
}
x1=5;
y1=10;
for(i1=1;i1<100;i1++){
    if(i1%3==0){
        y1=y1+1;
    }
    else if (i1%3==1){
       y1=y1*2;
    }
    else
    y1=y1+3;
}
assert(x0==x1);   
assert(y0==y1);   
return 0;
}
