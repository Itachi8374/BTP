#include <stdio.h>
#include <sys/time.h>
#include <sys/resource.h>
#include <string.h>
#include <stdlib.h>
#include "FsmdaHeader.h"
#include "parser.h"
#include "valPropHeader.h"
#include <sys/stat.h>
#include <fcntl.h>


int *inputVarCheck;


PATH_PAIR_S * findcTrace(FSMD *, FSMD *,PATHS_LIST *,PATHS_LIST *,PATH_PAIR_S *,PATH_PAIR_S *,PATH_PAIR_S *);
void inputVariablefind(FSMD *,int *);
void printVarList();

void printcTrace(FSMD*, PATHS_LIST*, PATH_PAIR_S*, int);
void  cTraceUsingCBMC(FSMD *M0, FSMD *M1,PATHS_LIST *P0,PATHS_LIST *P1,PATH_PAIR_S *tempLIST,PATH_PAIR_S *tempE_u,PATH_PAIR_S *tempE_c, var_list *V0,var_list *V1)
{

  inputVarCheck=malloc(sizeof(int)*stab.numsymbols);
	PATH_PAIR_S *finalTempLIST;
	
	finalTempLIST=findcTrace(M0,M1,P0,P1,tempLIST,tempE_u,tempE_c);
	printcTrace(M0,P0,finalTempLIST,0);
	printcTrace(M1,P1,finalTempLIST,1);
  inputVariablefind(M0, inputVarCheck);
  freopen("inputCBMC.c", "w", stdout);
  printf("#include <assert.h>\n");
  printf("void main(){\n");
  printVarList();
  printf("}");
  fclose(stdout);
  stdout = fdopen(0,"w");
}

PATH_PAIR_S* reverseCTrace(PATH_PAIR_S* ctrace){
	PATH_PAIR_S* head = ctrace; 
	PATH_PAIR_S* cur = head->next;
	head->next = NULL;
	while(cur!=NULL){
		PATH_PAIR_S* next = cur->next;
		cur->next = head;
		head = cur;
		cur = next;
	}
	return head;
}


PATH_PAIR_S* findcTrace(FSMD *M0, FSMD *M1,PATHS_LIST *P0,PATHS_LIST *P1,PATH_PAIR_S *tempLIST,PATH_PAIR_S *tempE_u,PATH_PAIR_S *tempE_c)
{
	PATH_PAIR_S* ctrace = tempLIST;
	PATH_PAIR_S* head = ctrace;
	while(head->next!=NULL){
		head = head->next;
	}
	head->next = tempE_c;
	while(head->next!=NULL){
		head = head->next;
	}
	head->next = tempE_u;
	ctrace = reverseCTrace(ctrace);
	return ctrace;
}

void printcTrace(FSMD *M,PATHS_LIST *P,PATH_PAIR_S *tempLIST,int ind)
{
int k;
int pathID;
r_alpha *tempTransformation;
char *sym_value;
sym_value = (char * ) malloc( 1000*sizeof( char ) );
if(ind==0)
printf("\nM0 - cTrace\n");
else
printf("\nM1 - cTrace\n");
k=0;
//defV0.no_of_elements=0;
while(tempLIST!=(PATH_PAIR_S *)NULL)
{
  if(ind==0)
	pathID=tempLIST->p0;
  else
	pathID=tempLIST->p1;

  if(pathID<P->numpaths)  // avoid NULL Path
  {  
    printf("\n%s-->%s\n",M->states[P->paths[pathID].start].state_id,M->states[P->paths[pathID].end].state_id);
    write_lists(P->paths[pathID].condition);
    tempTransformation=P->paths[pathID].transformations;
    while(tempTransformation!=NULL)
    {
	  	symbol_for_index(tempTransformation->Assign.lhs, sym_value );
		  printf("\n %s := ", sym_value );
     // defV0.var_val[k++]=tempTransformation->Assign.lhs; // sotring the defiined variable
     // defV0.no_of_elements++;
		  write_lists(tempTransformation->Assign.rhs);
      		tempTransformation=tempTransformation->next;
	}
	printf("\n");
  } 
  tempLIST=tempLIST->next;
}
}

void inputVariablefind(FSMD *M,int *inputVarCheck)
{
	int i,j,k,flag;
	TRANSITION_ST *temp;

	printf("All Variables\n");
	
	for( j = 1; j < stab.numsymbols; j++ )
	{
		printf("%s\n",stab.sym_tab[j]);
		inputVarCheck[j]=TRUE;
	}
	
	
	for(i=0;i<M->numstates;i++) 
	{
	 	temp=M->states[i].translist;
	   	while(temp!=NULL) 
		{
	          //this loop will display all the transitions from a particular state
              		j=0;
			while( temp->action[j].rhs != NULL ) 
			{
				
				for( k = 1; k < stab.numsymbols; k++ )
				{
					if(temp->action[j].lhs==stab.val_tab[k])
					{
					
						inputVarCheck[k]=FALSE;
						break;
					}
				}
				j++;
			}

				temp=temp->next;
		}

	}
	
	printf("Input Variables\n");
	for( j = 1; j < stab.numsymbols; j++ )
	{
		flag=0;
		if(inputVarCheck[j]==TRUE)
		{
			for( i = 0; i < V0_V1.no_of_elements; i++ )
			{
				if(stab.val_tab[j]==V0_V1.var_val[i])
				{
					flag=1;
					break;
				}
			}
			if (flag==0)
			inputVarCheck[j]=FALSE;
		}
	if(inputVarCheck[j]==TRUE)
	printf("%s---%d--%d\n",stab.sym_tab[j],stab.val_tab[j],inputVarCheck[j]);
		
	}	
}

void printVarList()
{
	int j;
	for( j = 1; j < stab.numsymbols; j++ )
	{
		if(inputVarCheck[j]==FALSE)
		{
			printf( "int %s%c%c%d;\n", stab.sym_tab[j], '_', 's', 0 );
      printf( "int %s%c%c%d;\n", stab.sym_tab[j], '_', 's', 1 );
      printf( "int %s%c%c%d;\n", stab.sym_tab[j], '_', 't', 0 );
      printf( "int %s%c%c%d;\n", stab.sym_tab[j], '_', 't', 1 );
		}
		else
		printf( "int %s;\n",stab.sym_tab[j]);
		
	}
}
