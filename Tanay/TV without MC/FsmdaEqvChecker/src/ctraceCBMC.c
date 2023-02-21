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
void printcTrace(FSMD*, PATHS_LIST*, PATH_PAIR_S*, int);
void  cTraceUsingCBMC(FSMD *M0, FSMD *M1,PATHS_LIST *P0,PATHS_LIST *P1,PATH_PAIR_S *tempLIST,PATH_PAIR_S *tempE_u,PATH_PAIR_S *tempE_c, var_list *V0,var_list *V1)
{

  inputVarCheck=malloc(sizeof(int)*stab.numsymbols);
	PATH_PAIR_S *finalTempLIST;
	
	finalTempLIST=findcTrace(M0,M1,P0,P1,tempLIST,tempE_u,tempE_c);
	printcTrace(M0,P0,finalTempLIST,0);
	printcTrace(M1,P1,finalTempLIST,1);
}


PATH_PAIR_S* findcTrace(FSMD *M0, FSMD *M1,PATHS_LIST *P0,PATHS_LIST *P1,PATH_PAIR_S *tempLIST,PATH_PAIR_S *tempE_u,PATH_PAIR_S *tempE_c)
{
	PATH_PAIR_S *tempPathPairNode;
	printf("finding cTrace\n");
while(P0->paths[tempLIST->p0].start!=0||P1->paths[tempLIST->p1].start!=0)
{
	tempE_u=tempE_u->next;
  tempE_c=tempE_c->next;
  if(tempLIST->p0 < P0->numpaths)
  {
    while(tempE_u!=(PATH_PAIR_S *)NULL)
    { 
      if(P0->paths[tempE_u->p0].end==P0->paths[tempLIST->p0].start)
      {
        tempPathPairNode=initS(tempE_u->p0, tempE_u->p1, tempE_u->isLoop, tempLIST);
        tempLIST=tempPathPairNode;
        break;
      }
        tempE_u=tempE_u->next;
    }
    while(tempE_c!=(PATH_PAIR_S *)NULL)
    { 
      if(P0->paths[tempE_c->p0].end==P0->paths[tempLIST->p0].start)
      {
        tempPathPairNode=initS(tempE_c->p0, tempE_c->p1, tempE_c->isLoop, tempLIST);
        tempLIST=tempPathPairNode;
        break;
      }
      tempE_c=tempE_c->next;
    }
  }
 else
 {
    while(tempE_u!=(PATH_PAIR_S *)NULL)
    { 
      if(P1->paths[tempE_u->p1].end==P1->paths[tempLIST->p1].start)
      {
        tempPathPairNode=initS(tempE_u->p0, tempE_u->p1, tempE_u->isLoop, tempLIST);
        tempLIST=tempPathPairNode;
        break;
      }
       tempE_u=tempE_u->next;
    }
    tempE_c=tempE_c->next;
    while(tempE_c!=(PATH_PAIR_S *)NULL)
    {  
      if(P1->paths[tempE_c->p0].end==P1->paths[tempLIST->p1].start)
      {
        tempPathPairNode=initS(tempE_c->p0, tempE_c->p1, tempE_c->isLoop, tempLIST);
        tempLIST=tempPathPairNode;
        break;
      }
      tempE_c=tempE_c->next;
    }
  }
}
return tempLIST;
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

