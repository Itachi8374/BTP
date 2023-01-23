#include<assert.h>
void main(){
int p0;
int y00;
int y01;
int p1;
int y10;
int y11;
int res0;
int res1;
int y20;
int y21;
int temp10;
int temp11;
int temp20;
int temp21;
int x0;
int x1;
int ex1;
int ex11;
int ex20;
int ex21;
int yout0;
int yout1;
q00:
	y00 = 0 + 1 * p0 ;
	y10 = 0 + 1 * p1 ;
	res0 = 1  ;
	goto q01;
q01:
if( ( 0 + 1 * y10 - 1 * y20 != 0 ) )
{
	temp10 = 2 + 1 * y10  ;
	temp20 = 2 + 1 * y20  ;
	x0 = 5  ;
	goto q02;
}
__CPROVER_assume( ( 0 + 1 * y10 - 1 * y20 == 0 ) );
if( ( 0 + 1 * y10 - 1 * y20 == 0 ) )
{
	ex20 = 0 + 1 * x0 + 1 * ex1 ;
	yout0 = 0 + 1 * y10 * res0  ;
	goto q0e;
}
q02:
__CPROVER_assume( ( 0 + 1 * temp10 != 0 ) );
if( ( 0 + 1 * temp10 != 0 ) )
{
	goto q04;
}
q04:
__CPROVER_assume( ( 0 + 1 * temp20 != 0 ) );
if( ( 0 + 1 * temp20 != 0 ) )
{
	goto q05;
}
q05:
__CPROVER_assume( ( 0 + 1 * y10 - 1 * y20 <= 0 ) );
if( ( 0 + 1 * y10 - 1 * y20 <= 0 ) )
{
	y20 = 0 - 1 * y10 + 1 * y20  ;
	goto q01;
}
q0e:
q10:
	ex11 = 0  ;
	y01 = 0 + 1 * p0 ;
	y11 = 0 + 1 * p1 ;
	res1 = 1  ;
	goto q1m;
q1m:
if( ( 0 + 1 * y11 - 1 * y21 != 0 ) )
{
	temp11 = 2 + 1 * y11  ;
	temp21 = 2 + 1 * y21  ;
	goto q11;
}
__CPROVER_assume( ( 0 + 1 * y11 - 1 * y21 == 0 ) );
if( ( 0 + 1 * y11 - 1 * y21 == 0 ) )
{
	x1 = 5  ;
	ex11 = 5  ;
	ex21 = 10  ;
	yout1 = 0 + 1 * y11 * res1  ;
	goto q12;
}
q11:
__CPROVER_assume( ( 0 + 1 * temp11 != 0 )  &&  ( 0 + 1 * temp21 != 0 )  &&  ( 0 + 1 * y11 - 1 * y21 <= 0 ) );
if( ( 0 + 1 * temp11 != 0 )  &&  ( 0 + 1 * temp21 != 0 )  &&  ( 0 + 1 * y11 - 1 * y21 <= 0 ) )
{
	y21 = 0 - 1 * y11 + 1 * y21  ;
	goto q1m;
}
q12:
assert(ex20 == ex21);
assert(yout0 == yout1);
}
