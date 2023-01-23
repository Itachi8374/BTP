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


PATH_PAIR * findcTrace(FSMD *, FSMD *,PATHS_LIST *,PATHS_LIST *,PATH_PAIR *,PATH_PAIR *,PATH_PAIR *);
void  cTraceUsingCBMC(FSMD *M0, FSMD *M1,PATHS_LIST *P0,PATHS_LIST *P1,PATH_PAIR *tempLIST,PATH_PAIR *tempE_u,PATH_PAIR *tempE_c, var_list *V0,var_list *V1)
{

  inputVarCheck=malloc(sizeof(int)*stab.numsymbols);
	PATH_PAIR *finalTempLIST;
	
	finalTempLIST=findcTrace(M0,M1,P0,P1,tempLIST,tempE_u,tempE_c);
	printcTrace(M0,P0,finalTempLIST,0);
	printcTrace(M1,P1,finalTempLIST,1);
	inputVariablefind(M0,inputVarCheck);
	freopen("inputCBMC.c","w",stdout);
	printf("#include<assert.h>\n");
	printf("void main(){\n");
	printVarList();
	cTraceToC(M0,P0,finalTempLIST,0);
	cTraceToC(M1,P1,finalTempLIST,1);
	liveVariablecheck(finalTempLIST,P0);
	printf("}");
	fclose(stdout);
  stdout = fdopen(0, "w");
}
void printVarList()
{
	int j;
	for( j = 1; j < stab.numsymbols; j++ )
	{
		if(inputVarCheck[j]==FALSE)
		{
			printf( "int %s%d;\n", stab.sym_tab[j],0 );
			printf( "int %s%d;\n",  stab.sym_tab[j],1 );
		}
		else
		printf( "int %s;\n",stab.sym_tab[j]);
		
	}
}

PATH_PAIR * findcTrace(FSMD *M0, FSMD *M1,PATHS_LIST *P0,PATHS_LIST *P1,PATH_PAIR *tempLIST,PATH_PAIR *tempE_u,PATH_PAIR *tempE_c)
{
	PATH_PAIR *tempPathPairNode;
	printf("finding cTrace\n");
while(P0->paths[tempLIST->p0].start!=0||P1->paths[tempLIST->p1].start!=0)
{
	tempE_u=tempE_u->next;
  tempE_c=tempE_c->next;
  if(tempLIST->p0 < P0->numpaths)
  {
    while(tempE_u!=(PATH_PAIR *)NULL)
    { 
      if(P0->paths[tempE_u->p0].end==P0->paths[tempLIST->p0].start)
      {
        tempPathPairNode=initE();
        tempPathPairNode->p0=tempE_u->p0;
        tempPathPairNode->p1=tempE_u->p1;
        tempPathPairNode->next=tempLIST;
        tempLIST=tempPathPairNode;
        break;
      }
        tempE_u=tempE_u->next;
    }
    while(tempE_c!=(PATH_PAIR *)NULL)
    { 
      if(P0->paths[tempE_c->p0].end==P0->paths[tempLIST->p0].start)
      {
        tempPathPairNode=initE();
        tempPathPairNode->p0=tempE_c->p0;
        tempPathPairNode->p1=tempE_c->p1;
        tempPathPairNode->next=tempLIST;
        tempLIST=tempPathPairNode;
        break;
      }
      tempE_c=tempE_c->next;
    }
  }
 else
 {
    while(tempE_u!=(PATH_PAIR *)NULL)
    { 
      if(P1->paths[tempE_u->p1].end==P1->paths[tempLIST->p1].start)
      {
        tempPathPairNode=initE();
        tempPathPairNode->p0=tempE_u->p0;
        tempPathPairNode->p1=tempE_u->p1;
        tempPathPairNode->next=tempLIST;
        tempLIST=tempPathPairNode;
        break;
      }
       tempE_u=tempE_u->next;
    }
    tempE_c=tempE_c->next;
    while(tempE_c!=(PATH_PAIR *)NULL)
    {  
      if(P1->paths[tempE_c->p0].end==P1->paths[tempLIST->p1].start)
      {
        tempPathPairNode=initE();
        tempPathPairNode->p0=tempE_c->p0;
        tempPathPairNode->p1=tempE_c->p1;
        tempPathPairNode->next=tempLIST;
        tempLIST=tempPathPairNode;
        break;
      }
      tempE_c=tempE_c->next;
    }
  }
}
return tempLIST;
}

void printcTrace(FSMD *M,PATHS_LIST *P,PATH_PAIR *tempLIST,int ind)
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
while(tempLIST!=(PATH_PAIR *)NULL)
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

void cTraceToC(FSMD *M,PATHS_LIST *P,PATH_PAIR *tempLIST,int ind)
{
int i=0,pathID,flag=1,pathID1;
r_alpha *tempTransformation;
char *sym_value;
sym_value = (char * ) malloc( 1000*sizeof( char ) );
PATH_PAIR *tempLIST1;
PATH_PAIR *tempLIST2;
while(i<M->numstates)
{	
  	tempLIST1=tempLIST;
	while(tempLIST1!=(PATH_PAIR *)NULL)
	{
		if(ind==0)
		pathID=tempLIST1->p0;
  		else
		pathID=tempLIST1->p1;
  		if(pathID<P->numpaths && P->paths[pathID].start==i)  // avoid NULL Path
		{
			//printf("State id %s\n",M->states[i].state_id
			if(flag==1) // print label only one time
			printf("%s:\n",M->states[P->paths[pathID].start].state_id);
			flag=0;
			if(P->paths[pathID].condition!=NULL)
			{
				
				if(M->states[i].loop_header_flag!=TRUE || (M->states[i].loop_header_flag==TRUE && 
				M->states[P->paths[pathID].end].my_loop_header!=i))   //avoiding the loop exit condition 
				{
					printf("__CPROVER_assume(");
    					ssa_write_lists(P->paths[pathID].condition,ind);
					printf(");\n");
				}
				printf("if(");
    				ssa_write_lists(P->paths[pathID].condition,ind);
				printf(")\n{\n");
    				tempTransformation=P->paths[pathID].transformations;
				while(tempTransformation!=NULL)
    				{			
	  				symbol_for_index(tempTransformation->Assign.lhs, sym_value );
		  			printf("\t%s%d = ", sym_value,ind );
		  			ssa_write_lists(tempTransformation->Assign.rhs,ind);
					printf(" ;\n");
      					tempTransformation=tempTransformation->next;
				}
				
				if(M->states[P->paths[pathID].end].loop_header_flag==TRUE 
				&& M->states[P->paths[pathID].start].my_loop_header!=P->paths[pathID].end)  //printing the loop entry condition
				{	
  					tempLIST2=tempLIST;
					while(tempLIST2!=(PATH_PAIR *)NULL)
					{
						if(ind==0)
						pathID1=tempLIST2->p0;
 			 			else
						pathID1=tempLIST2->p1;
  						if(P->paths[pathID1].start== P->paths[pathID].end &&
						(M->states[P->paths[pathID1].end].my_loop_header==P->paths[pathID].end))  // avoid NULL Path
						{
							printf("__CPROVER_assume(");
    							ssa_write_lists(P->paths[pathID1].condition,ind);
							printf(");\n");
						}
						tempLIST2=tempLIST2->next;
						
					}

				}
				printf("\tgoto %s;\n",M->states[P->paths[pathID].end].state_id);
				printf("}\n");
			}
			else
			{
				tempTransformation=P->paths[pathID].transformations;
				while(tempTransformation!=NULL)
    				{			
	  				symbol_for_index(tempTransformation->Assign.lhs, sym_value );
		  			printf("\t%s%d = ", sym_value,ind );
		  			ssa_write_lists(tempTransformation->Assign.rhs);
					printf(" ;\n");
      					tempTransformation=tempTransformation->next;
				}
				printf("\tgoto %s;\n",M->states[P->paths[pathID].end].state_id);
			}	
    		}
		tempLIST1=tempLIST1->next;
	}
	flag=1;
	i++;
}			
  	//printing end state label excetp loop header
	tempLIST1=tempLIST;
	while(tempLIST1->next!=(PATH_PAIR *)NULL)
		tempLIST1=tempLIST1->next;
	
	if(ind==0)
		pathID=tempLIST1->p0;
  	else
		pathID=tempLIST1->p1;
	if(M->states[P->paths[pathID].end].loop_header_flag==FALSE)	
	printf("\%s:\n",M->states[P->paths[pathID].end].state_id);

}



//SSA  WRITE LIST
void ssa_write_lists( NC *root, int ssaInd ) //WRITE_LISTS <- for finding fast
{
  char *sym_value;
  int i;
  sym_value = (char * ) malloc( 1000*sizeof( char ) );

  if( root != NULL )
  {
	//KB start
	if(root->type == 0) root->type = 'S';
	//KB end
    if( root->type == 'R' || root->type == 'O' )
    {
       if( root->type == 'R' )
          printf( " ( " );
       ssa_write_lists( root->link,ssaInd );
    }

    switch( root->type )
    {
      case 'f':
        symbol_for_index( root->inc, sym_value );
        printf( "* %s( ", sym_value );
        break;
      case 'v':
         for( i = 0; i < stab.numsymbols; i++ )
         { 
          if( stab.val_tab[i] == root->inc )
            {
             strcpy( sym_value, stab.sym_tab[i] );
	     if(inputVarCheck[i]==FALSE)
             printf( "* %s%d ", sym_value,ssaInd);
	     else
             printf( "* %s", sym_value);
             break;
            } 
         }
        break;
      case 'T':
        printf( "%c %d ", ( root->inc >= 0 )?'+':'-',
                abs( root->inc ) );
        break;
      case 'S':
        printf( "%d ", root->inc );
        break;
      case 'R':
        switch( root->inc )
          {
          case 0: printf( ">= 0" );
            break;
          case 1: printf( "> 0" );
            break;
          case 2: printf( "<= 0" );
            break;
          case 3: printf( "< 0" );
            break;
          case 4: printf( "== 0" );
            break;
          case 5: printf( "!= 0" );
            break;
          }; // switch( root->inc )
        printf( " ) " );
        if( root->list != NULL )
          printf( " || " );
        break;
      case 'A':
        break;
      case 'O':
        if( root->list != NULL )
          printf( " && " );
        break;
      case 'D':
        printf( " * ( /   " );
        break;
      case 'M':
        printf( " * (%%   " ); //printf( "* ( %c %d   ",  root->type, root->inc );
        break;
      //KB: array start
      case 'w':
		printf( "write ( " );
		break;
	  case 'y':
	    symbol_for_index(root->inc, sym_value);
	    printf( "%s, ", sym_value );
	    break;
	  case 'a':
	    symbol_for_index(root->inc, sym_value);
	    printf( "* read ( %s, ", sym_value );
	    break;
      //KB: array end
      default:
        break;
    }; // switch( root->type )

    if( root->type != 'R' && root->type != 'O' )
      ssa_write_lists( root->link,ssaInd );
    if( root->type == 'f' || root->type == 'w') //2nd clause is for arrays
      printf( ")" );

    //KB: array start
    if(root->type == 'y')
      printf(", ");
    //A closing bracket has to be put explicitly in case the arrays
    //are of only one dimension
    if(root->type == 'a' && root->link->list == NULL)
      printf( ")" );
    //KB: array end

    if( root->type == 'S' && root->list != NULL )
    {
      printf( ", " );
      ssa_write_lists( root->list,ssaInd );
      printf(")");
      return;
    }

    ssa_write_lists( root->list,ssaInd );
  }
  return;
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

void liveVariablecheck(PATH_PAIR *tempLIST,PATHS_LIST *P)
{
	int i,j,k;
	char *sym_value;
	sym_value = (char * ) malloc( 1000*sizeof( char ) );
  while(tempLIST->next!=NULL)
  tempLIST=tempLIST->next;
  for(i=0;i<P->paths[tempLIST->p0].live->countLiveVar;i++)
  {
    for(j=0;j<V0_V1.no_of_elements;j++)
    {
      if(P->paths[tempLIST->p0].live->liveVar[i]==V0_V1.var_val[j])
      {
        for( k = 0; k < stab.numsymbols; k++ )
         { 
          if( stab.val_tab[k] == P->paths[tempLIST->p0].live->liveVar[i]  && inputVarCheck[k]==FALSE)
            {
		             
	     strcpy( sym_value, stab.sym_tab[k] );
             printf( "assert(%s0 == %s1);\n", sym_value,sym_value);
             break;
            } 
         }
        //symbol_for_index(P0.paths[tempLIST1->p0].live->liveVar[i], sym_value);
       // printf("%s;",sym_value);
      }
    }
    //printf("\n");
  }
}


