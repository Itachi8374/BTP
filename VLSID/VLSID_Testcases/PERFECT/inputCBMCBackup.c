#include<assert.h>
void main(){
int ext10;
int ext11;
int sum0;
int sum1;
int i0;
int i1;
int n;
int temp0;
int temp1;
int ext20;
int ext21;
int out0;
int out1;
q00:
	ext10 = 5  ;
	sum0 = 1  ;
	i0 = 2  ;
__CPROVER_assume( ( 0 + 1 * i0 - 1 * n< 0 ) );
	goto q01;
q01:
if( ( 0 + 1 * i0 - 1 * n< 0 ) )
{
	temp0 = 0 + 1  * n%i0 ;
	goto q02;
}
else
	goto q10;
q02:
if( ( -1 + 1 * temp0 == 0 ) )
{
	sum0 = 0 + 1 * i0 + 1 * sum0  ;
	i0 = 1 + 1 * i0  ;
	goto q01;
}
else
{
  i0=i0+1;
	goto q01;
}
q10:
	ext11 = 0  ;
	sum1 = 1  ;
	i1 = 2  ;
__CPROVER_assume( ( 0 + 1 * i1 - 1 * n< 0 ) );
	goto q11;
q11:
if( ( 0 + 1 * i1 - 1 * n< 0 ) )
{
	temp1 = 0 + 1  * n% i1 ;
	goto q12;
}
else
goto chk;
q12:
__CPROVER_assume( ( -1 + 1 * temp1 == 0 ) );
if( ( -1 + 1 * temp1 == 0 ) )
{
	sum1 = 3 + 1 * i1 + 1 * sum1  ;
	i1 = 1 + 1 * i1  ;
	goto q11;
}
else
{ 
	i1 = 1 + 1 * i1  ;
	goto q11;

}
chk:
assert(i0 == i1);
assert(sum0 == sum1);
assert(ext10 == ext11);
}
