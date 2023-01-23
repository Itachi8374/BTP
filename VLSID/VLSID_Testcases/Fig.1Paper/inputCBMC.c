#include<assert.h>
void main(){
int n;
int i0;
int i1;
int x0;
int x1;
int y0;
int y1;
int out0;
int out1;
q00:
__CPROVER_assume( ( 0 + 1 * n>= 0 ) );
if( ( 0 + 1 * n>= 0 ) )
{
	i0 = 0  ;
	x0 = 0  ;
	y0 = 0  ;
__CPROVER_assume( ( 0 + 1 * i0 - 1 * n<= 0 ) );
	goto q01;
}
q01:
if( ( 0 + 1 * i0 - 1 * n<= 0 ) )
{
	x0 = 5  ;
	y0 = 0 + 1 * i0 + 1 * y0  ;
	i0 = 1 + 1 * i0  ;
	goto q01;
}
__CPROVER_assume( ( 0 + 1 * i0 - 1 * n> 0 ) );
if( ( 0 + 1 * i0 - 1 * n> 0 ) )
{
	out0 = 5 + 1 * x0 + 1 * y0  ;
	goto q03;
}
q03:
q10:
__CPROVER_assume( ( 0 + 1 * n>= 0 ) );
if( ( 0 + 1 * n>= 0 ) )
{
	i1 = 0  ;
	x1 = 5  ;
	y1 = 0  ;
__CPROVER_assume( ( 0 + 1 * i1 - 1 * n<= 0 ) );
	goto q11;
}
q11:
if( ( 0 + 1 * i1 - 1 * n<= 0 ) )
{
	y1 = 0 + 1 * i1 + 1 * y1  ;
	i1 = 1 + 1 * i1  ;
	goto q11;
}
__CPROVER_assume( ( 0 + 1 * i1 - 1 * n> 0 ) );
if( ( 0 + 1 * i1 - 1 * n> 0 ) )
{
	out1 = 0 + 1 * x1 + 1 * y1  ;
	goto q13;
}
q13:
assert(out0 == out1);
}