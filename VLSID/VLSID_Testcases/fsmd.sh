gcc -fdump-tree-cfg=$1.cfg $1
out=$2 #output file name
find=";"
replace=","
gotoflag="No"
assign=""
cond=""
status=""
regex="<L[0-9]+>:"
>$out
echo -e "\"$1.org\"\n\n Q0 1 - | - Q2;\n" >$out
(
while IFS='' read -r line || [[ -n "$line" ]]; do
a=( $line )
##########################################
if [ "${a[0]}" == "<bb" ]; then
if [ "$status" == "bb" ]  &&[ "$gotoflag" == "No" ] ; then
assign=${assign//$find/$replace}  
assign=$(echo "$assign" | sed 's/\(.*\),/\1 /')
 echo -e "1 - | $assign Q$((bb+1));\n"
fi
assign="";
cond="";
status="bb"
printexp="ok"
gotoflag="No"
bb=${a[1]//>:};
echo -n "Q$bb "
###########################################
#elif [ "${a[0]}" ~= "<L$(($bb + 1))>:" ]; then
elif [[ ${a[0]} =~ $regex ]]; then
if [ "$assign" != "" ]; then
assign=${assign//$find/$replace}  
assign=$(echo "$assign" | sed 's/\(.*\),/\1 /')
echo -e "1 - | $assign Q1;\n"
echo "Q1 0;"
else
echo -e "- Q1;\n"
echo "Q1 0;"
fi
###########################################
elif [ "${a[0]}" == "if" ];then
status="if"
if [ "$assign" != "" ]; then 
assign=${assign//$find/$replace}  
assign=$(echo "$assign" | sed 's/\(.*\),/\1 /')
echo -e "1 - | $assign Q"${bb}000";\n\n"
echo -n "Q${bb}000 "
fi
cond=$(echo -n "$line" | awk -F '[()]' '{print $(NF-1)}')
echo -n "2 $cond | -"
###########################################
elif [ "${a[0]}" == "else" ]; then
status="else"
echo -n " !($cond) | -"
###########################################
elif [ "${a[0]}" == "return;" ]; then
status="return"
if [ "$assign" != "" ]; then
assign=${assign//$find/$replace}  
assign=$(echo "$assign" | sed 's/\(.*\),/\1 /')
echo -e "1 - | $assign Q1;\n"
echo "Q1 0;"
else
echo -e "1 - | - Q1;\n"
echo "Q1 0;"
fi
############################################
elif [ "${a[0]}" == "goto" ] && [ "$status" == "bb" ] ; then
gotoflag="Yes"
succ=${a[2]//>;};
if [ "$assign" != "" ]; then 
assign=${assign//$find/$replace}  
assign=$(echo "$assign" | sed 's/\(.*\),/\1 /')
echo -e "1 - | $assign Q$succ;\n"
else
echo -e "1- | - Q$succ;\n"
fi
#############################################
elif [ "${a[0]}" == "goto" ] && [ "$status" == "if" ] ; then
succ=${a[2]//>;};
gotoflag="Yes"
echo " Q$succ"
########################################
elif [ "${a[0]}" == "goto" ] && [ "$status" == "else" ] ; then
succ=${a[2]//>;};
gotoflag="Yes"
echo -e " Q$succ;\n"
########################################
elif [ "$printexp" == "ok" ] && [ "$status" != "return" ]  ; then
line=$(echo "${line//./}")
assign+=$line
##########################################
fi
done < "$1.cfg")>>$out
rm a.out
rm $1.cfg
fsmda2dot $2
