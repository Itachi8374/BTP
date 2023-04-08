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
char highInput[10];

PATH_PAIR_S * findcTrace(FSMD *, FSMD *,PATHS_LIST *,PATHS_LIST *,PATH_PAIR_S *,PATH_PAIR_S *,PATH_PAIR_S *);
void inputVariablefind(FSMD *,int *);
void printVarList();
void printcTrace(FSMD*, PATHS_LIST*, PATH_PAIR_S*, int);
void cTraceToC(FSMD*, PATHS_LIST*, PATH_PAIR_S*, int );
void countLeaky(int);

void getHighInput(){
	FILE *f1;
	f1 = fopen( "High.txt", "r" );
	while(!feof(f1)){
		fscanf( f1, "%s*", highInput);
		break;
	}
	fclose(f1);
	
}

void  cTraceUsingCBMC(FSMD *M0, FSMD *M1,PATHS_LIST *P0,PATHS_LIST *P1,PATH_PAIR_S *tempLIST,PATH_PAIR_S *tempE_u,PATH_PAIR_S *tempE_c, var_list *V0,var_list *V1)
{
	getHighInput();
	
  	inputVarCheck=malloc(sizeof(int)*stab.numsymbols);
	PATH_PAIR_S *finalTempLIST;
	
	finalTempLIST=findcTrace(M0,M1,P0,P1,tempLIST,tempE_u,tempE_c);
	printcTrace(M0,P0,finalTempLIST,0);
	printcTrace(M1,P1,finalTempLIST,1);
	inputVariablefind(M0, inputVarCheck);
	freopen("inputCBMC.c", "w", stdout);
	printf("#include <assert.h>\n");
	printf("void main(){\n");
	printf("int counth_s = 0, counth_t = 0;\n");
	printVarList();
	printf("\n");

	for(int i=0; i<4; ++i){
		if(i<2){
			cTraceToC(M0,P0,finalTempLIST,i);
		}else{
			cTraceToC(M1,P1,finalTempLIST,i);
		}
		
		printf("\n");
	}
	
	printf("\n\n//Count Leaky Variables in M0\n");
	countLeaky(0);
	printf("\n\n//Count Leaky Variables in M1\n");
	countLeaky(1);
	printf("assert(counth_t <= counth_s);");
	printf("}");
	fclose(stdout);
	stdout = fdopen(0,"w");
}

void countLeaky(int ind){
	for(int j = 1; j < stab.numsymbols; j++ )
	{
		if(inputVarCheck[j]==FALSE)
		{
			if(ind==0){
				printf( "if( %s_s0!= %s_s1) counth_s++;\n", stab.sym_tab[j], stab.sym_tab[j]);
			}else{
				printf( "if( %s_t0!= %s_t1) counth_t++;\n", stab.sym_tab[j], stab.sym_tab[j]);
			}
		}

	}
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
		else if(!strcmp(stab.sym_tab[j],highInput)){
			printf( "int %s%c%c;\n", stab.sym_tab[j], '_', 's');
			printf( "int %s%c%c;\n", stab.sym_tab[j], '_', 't');
		}else{
			printf( "int %s;\n",stab.sym_tab[j]);
		}
		
		
	}
}

//SSA  WRITE LIST
void ssa_write_lists( NC *root, int flag ) //WRITE_LISTS <- for finding fast
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
       ssa_write_lists( root->link,flag );
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
          	if( stab.val_tab[i] == root->inc ){
				strcpy( sym_value, stab.sym_tab[i] );
				if(inputVarCheck[i]==FALSE){
					switch(flag){
						case 0: printf("* %s_s0", sym_value); break;
						case 1: printf("* %s_s1", sym_value); break;
						case 2: printf("* %s_t0", sym_value); break;
						case 3: printf("* %s_t1", sym_value); break;
					}
				}else if(!strcmp(sym_value,highInput)){
					if(flag<2){
						printf( "* %s%c%c", sym_value, '_', 's');
					}else{
						printf( "* %s%c%c", sym_value, '_', 't');
					}
				}else{
					printf( "* %s",sym_value);
				}
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
		switch(flag){
			case 0: printf("%s_s0, ", sym_value); break;
			case 1: printf("%s_s1, ", sym_value); break;
			case 2: printf("%s_t0, ", sym_value); break;
			case 3: printf("%s_t1, ", sym_value); break;
		}
	    break;
	  case 'a':
	    symbol_for_index(root->inc, sym_value);
		switch(flag){
			case 0: printf("* read ( %s_s0, ", sym_value); break;
			case 1: printf("* read ( %s_s1, ", sym_value); break;
			case 2: printf("* read ( %s_t0, ", sym_value); break;
			case 3: printf("* read ( %s_t1, ", sym_value); break;
		}
	    break;
      //KB: array end
      default:
        break;
    }; // switch( root->type )

    if( root->type != 'R' && root->type != 'O' )
      ssa_write_lists( root->link,flag );
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
      ssa_write_lists( root->list,flag );
      printf(")");
      return;
    }

    ssa_write_lists( root->list, flag );
  }
  return;
}

void cTraceToC(FSMD* M, PATHS_LIST* P, PATH_PAIR_S* ctrace, int flag){
	char *sym_value;
	sym_value = (char * ) malloc( 1000*sizeof( char ) );
	int pathID = 0;
	PATH_PAIR_S* lastState = ctrace;
	while(ctrace!=NULL){
		if(flag<2){
			pathID = ctrace->p0;
		}else{
			pathID = ctrace->p1;;
		}

		switch(flag){
			case 0: printf("%s_s0:\n", M->states[P->paths[pathID].start].state_id); break;
			case 1: printf("%s_s1:\n", M->states[P->paths[pathID].start].state_id); break;
			case 2: printf("%s_t0:\n", M->states[P->paths[pathID].start].state_id); break;
			case 3: printf("%s_t1:\n", M->states[P->paths[pathID].start].state_id); break;
		}
		
		if(P->paths[pathID].condition!=NULL){
			printf("__CPROVER_assume(");
    		ssa_write_lists(P->paths[pathID].condition, flag);
			printf(");\n");
			printf("if(");
    		ssa_write_lists(P->paths[pathID].condition, flag);
			printf(")\n{\n");
			r_alpha* transformations =P->paths[pathID].transformations;
			while(transformations!=NULL)
			{			
				symbol_for_index(transformations->Assign.lhs, sym_value );
				switch(flag){
					case 0: printf("\t%s_s0 = ", sym_value); break;
					case 1: printf("\t%s_s1 = ", sym_value); break;
					case 2: printf("\t%s_t0 = ", sym_value); break;
					case 3: printf("\t%s_t1 = ", sym_value); break;
				}
				ssa_write_lists(transformations->Assign.rhs,flag);
				printf(" ;\n");
				transformations=transformations->next;
			}

			printf("\tgoto ");
			switch(flag){
				case 0: printf("%s_s0;\n", M->states[P->paths[pathID].end].state_id); break;
				case 1: printf("%s_s1;\n", M->states[P->paths[pathID].end].state_id); break;
				case 2: printf("%s_t0;\n", M->states[P->paths[pathID].end].state_id); break;
				case 3: printf("%s_t1;\n", M->states[P->paths[pathID].end].state_id); break;
			}
			printf("}\n");
			
		}else{
			r_alpha* transformations = P->paths[pathID].transformations;
			while(transformations!=NULL){
				symbol_for_index(transformations->Assign.lhs, sym_value);
				switch(flag){
					case 0: printf("\t%s_s0 = ", sym_value); break;
					case 1: printf("\t%s_s1 = ", sym_value); break;
					case 2: printf("\t%s_t0 = ", sym_value); break;
					case 3: printf("\t%s_t1 = ", sym_value); break;
				}
				ssa_write_lists(transformations->Assign.rhs, flag);
				printf(";\n");
				transformations = transformations->next;
			}
			printf("\tgoto ");
			switch(flag){
				case 0: printf("%s_s0;\n", M->states[P->paths[pathID].end].state_id); break;
				case 1: printf("%s_s1;\n", M->states[P->paths[pathID].end].state_id); break;
				case 2: printf("%s_t0;\n", M->states[P->paths[pathID].end].state_id); break;
				case 3: printf("%s_t1;\n", M->states[P->paths[pathID].end].state_id); break;
			}
		}
		ctrace = ctrace->next;
	}

	//Printing last state
	while(lastState->next!=(PATH_PAIR_S *)NULL){
		lastState=lastState->next;
	}
	
	if(flag<2){
		pathID = lastState->p0;
	}else{
		pathID = lastState->p1;
	}
	
	switch(flag){
		case 0: printf("%s_s0:\n", M->states[P->paths[pathID].end].state_id); break;
		case 1: printf("%s_s1:\n", M->states[P->paths[pathID].end].state_id); break;
		case 2: printf("%s_t0:\n", M->states[P->paths[pathID].end].state_id); break;
		case 3: printf("%s_t1:\n", M->states[P->paths[pathID].end].state_id); break;
	}
}
