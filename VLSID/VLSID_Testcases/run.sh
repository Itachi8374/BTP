CBMC_SAFE_STATUS=0
CBMC_UNSAFE_STATUS=10
cbmcOut="cbmc_output"
#clear the content of the file
> $cbmcOut 
MAX_TIME=1
c=1;
inputFile=$1;
#TIMEOUT="timeout $MAX_TIME"
TIMEOUT="timeout --preserve-status -k 3 $MAX_TIME"
#echo $# No of commmand line parameter
while true ; do
echo "Running: $TIMEOUT cbmc  -unwind $c --no-unwinding-assertions --trace  $inputFile >> $cbmcOut"
$TIMEOUT cbmc  -unwind $c --no-unwinding-assertions --trace $inputFile >> $cbmcOut 2>&1
exit_status=$?
#echo $exit_status
if [ $exit_status -eq $CBMC_SAFE_STATUS ]; then
	c=$((c + 1))
	> $cbmcOut 
elif [ $exit_status -eq $CBMC_UNSAFE_STATUS ]; then
##print Result	
	timeTaken=`grep "Runtime decision procedure" $cbmcOut | cut -d':' -f2`
	printf "\n"
	echo -e "Time Taken: $timeTaken"
	echo "Unwind Value: $c"
	sed -n -e '/Results/,/^$/p' $cbmcOut
break
else
	echo "Timeout"
	break;
fi
done
