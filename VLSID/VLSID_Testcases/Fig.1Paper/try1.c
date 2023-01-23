int main()
{  
int i,out,y,x,n;

q00:
if( ( 0 + 1 * n < 0 ) )
{
out  =  -1 ;

goto q03;
}
if( ( 0 + 1 * n >= 0 ) )
{
i  =  0 ;
x  =  0 ;
y  =  0 ;

goto q01;
}
q01:
if( ( 0 + 1 * i - 1 * n > 0 ) )
{
out  =  5 + 1 * x + 1 * y ;

goto q03;
}
if( ( 0 + 1 * i - 1 * n <= 0 ) )
{
x  =  5 ;
y  =  0 + 1 * i + 1 * y ;

goto q02;
}
q03:
return 0;
q02:
i  =  1 + 1 * i ;

goto q01;

}
