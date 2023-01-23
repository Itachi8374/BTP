#include<assert.h>
void main(){
int ext10;
int ext11;
int s0;
int s1;
int i0;
int i1;
int b0;
int b1;
int t0;
int t1;
int ext20;
int ext21;
int a0;
int a1;
int n;
int ST5_120;
int ST5_121;
int ST6_150;
int ST6_151;
int sout0;
int sout1;
q00:
	ext10 = 5  ;
	s0 = 0  ;
	i0 = 0  ;
__CPROVER_assume( ( -15 + 1 * i0 <= 0 ) );
	goto q01;
q01:
if( ( -15 + 1 * i0 <= 0 ) )
{
	i0 = 1 + 1 * i0  ;
	t0 = 2 + 1 * b0  ;
	goto q02;
}
else goto q10;
q02:
if( ( -1 + 1 * t0 != 0 ) )
{
	goto q03;
}
else
{
  s0=s0+a0;
	goto q03;
}
q03:
if( ( 0 - 1 * n+ 1 * s0 >= 0 ) )
{
	s0 = 0 - 1 * n+ 1 * s0  ;
	ST5_120 = 0 + 2 * a0  ;
	b0 = 0 + 2 * b0  ;
	ST6_150 = 0 + 2 * a0 - 1 * n ;
	a0 = 0 + 2 * a0  ;
	goto q06;
}
else
{
	ST5_120 = 0 + 2 * a0  ;
	b0 = 0 + 2 * b0  ;
	ST6_150 = 0 + 2 * a0 - 1 * n ;
	a0 = 0 + 2 * a0  ;
	goto q06;
}
q06:
if( ( 0 + 1 * a0 - 1 * n< 0 ) )
{
	b0 = 1 + 1 * t0  ;
	a0 = 1 + 1 * t0  ;
	goto q01;
}
else
{
	a0 = a0 - n  ;
	goto q01;

}
q10:
	ext11 = 0  ;
	s1 = 0  ;
	i1 = 0  ;
	goto q11;
__CPROVER_assume( ( -15 + 1 * i1 <= 0 ) );
q11:
if( ( -15 + 1 * i1 <= 0 ) )
{
	t1 = 2 + 1 * b1  ;
	i1 = 1 + 1 * i1  ;
	goto q13;
}
else
goto chk;
q13:
if( ( -1 + 1 * t1 != 0 ) )
{
	goto q14;
}
else
{

  s0=a0+s0;
	goto q14;
}
q14:
if( ( 0 - 1 * n+ 1 * s1 >= 0 ) )
{
	s1 = 1 - 1 * n+ 1 * s1  ;
	a1 = 0 + 2 * a1  ;
	b1 = 0 + 2 * b1  ;
	goto q16;
}
else
{
	a1 = 0 + 2 * a1  ;
	b1 = 0 + 2 * b1  ;
	goto q16;
}
q16:
if( ( 0 + 1 * a1 - 1 * n< 0 ) )
{
	b1 = 1 + 1 * t1  ;
	a1 = 1 + 1 * t1  ;
	goto q11;
}
else
{
  a1=a1-n;
	goto q11;
}
chk:
assert(i0 == i1);
assert(ext10 == ext11);
assert(b0 == b1);
assert(s0 == s1);
assert(a0 == a1);
}
