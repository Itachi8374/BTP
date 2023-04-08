#include <assert.h>
void main(){
int counth_s = 0, counth_t = 0;
int s_s0;
int s_s1;
int s_t0;
int s_t1;
int i_s0;
int i_s1;
int i_t0;
int i_t1;
int b_s0;
int b_s1;
int b_t0;
int b_t1;
int ST1_8_s0;
int ST1_8_s1;
int ST1_8_t0;
int ST1_8_t1;
int sout_s0;
int sout_s1;
int sout_t0;
int sout_t1;
int a_s0;
int a_s1;
int a_t0;
int a_t1;
int n_s;
int n_t;
int ST5_12_s0;
int ST5_12_s1;
int ST5_12_t0;
int ST5_12_t1;
int ST6_15_s0;
int ST6_15_s1;
int ST6_15_t0;
int ST6_15_t1;
int s11_s0;
int s11_s1;
int s11_t0;
int s11_t1;

q00_s0:
	s_s0 = 0 ;
	i_s0 = 0 ;
	goto q01_s0;
q01_s0:
__CPROVER_assume( ( -15 + 1 * i_s0> 0 ) );
if( ( -15 + 1 * i_s0> 0 ) )
{
	sout_s0 = 0 + 1 * s_s0 ;
	goto q08_s0;
}
q08_s0:

q00_s1:
	s_s1 = 0 ;
	i_s1 = 0 ;
	goto q01_s1;
q01_s1:
__CPROVER_assume( ( -15 + 1 * i_s1> 0 ) );
if( ( -15 + 1 * i_s1> 0 ) )
{
	sout_s1 = 0 + 1 * s_s1 ;
	goto q08_s1;
}
q08_s1:

q00_t0:
	s_t0 = 0 ;
	i_t0 = 0 ;
	goto q01_t0;
q01_t0:
__CPROVER_assume( ( -15 + 1 * i_t0> 0 ) );
if( ( -15 + 1 * i_t0> 0 ) )
{
	sout_t0 = 0 + 1 * s_t0 ;
	goto q07_t0;
}
q07_t0:

q00_t1:
	s_t1 = 0 ;
	i_t1 = 0 ;
	goto q01_t1;
q01_t1:
__CPROVER_assume( ( -15 + 1 * i_t1> 0 ) );
if( ( -15 + 1 * i_t1> 0 ) )
{
	sout_t1 = 0 + 1 * s_t1 ;
	goto q07_t1;
}
q07_t1:



//Count Leaky Variables in M0
if( s_s0!= s_s1) counth_s++;
if( i_s0!= i_s1) counth_s++;
if( b_s0!= b_s1) counth_s++;
if( ST1_8_s0!= ST1_8_s1) counth_s++;
if( sout_s0!= sout_s1) counth_s++;
if( a_s0!= a_s1) counth_s++;
if( ST5_12_s0!= ST5_12_s1) counth_s++;
if( ST6_15_s0!= ST6_15_s1) counth_s++;
if( s11_s0!= s11_s1) counth_s++;


//Count Leaky Variables in M1
if( s_t0!= s_t1) counth_t++;
if( i_t0!= i_t1) counth_t++;
if( b_t0!= b_t1) counth_t++;
if( ST1_8_t0!= ST1_8_t1) counth_t++;
if( sout_t0!= sout_t1) counth_t++;
if( a_t0!= a_t1) counth_t++;
if( ST5_12_t0!= ST5_12_t1) counth_t++;
if( ST6_15_t0!= ST6_15_t1) counth_t++;
if( s11_t0!= s11_t1) counth_t++;
assert(counth_t <= counth_s);}