#include <vector>
#include <deque>
#include <assert.h>
#include "stdio.h"

#include "struct.h"

#define DEBUG_STRUCT_CPP	0

using namespace std;

/****************************************************************
 * Functions to create a term on the heap from an existing term.
 ****************************************************************/

TERM new_term(TERM t1)
{
	TERM t2;

	if (DEBUG_STRUCT_CPP)	
		printf("\t\tCreating new term\n");

	t2.sym = strdup(t1.sym);
	t2.args = new_arg_p(t1.args);
	t2.is_var = t1.is_var;
	t2.num_args = t1.num_args;

	return t2;
}

ARG* new_arg_p(ARG *a1)
{
	if (DEBUG_STRUCT_CPP)
		printf("\t\tCreating new arg\n");

	if (a1 == NULL)
	{
		if (DEBUG_STRUCT_CPP)
			printf("\t\tnew_arg_p: a1 is null\n");
		return NULL;
	}
	else if (DEBUG_STRUCT_CPP)
		printf("\t\tnew_arg_p: a1 is NOT null\n");

	ARG *a2 = (ARG *)malloc(sizeof(struct arg_s));

	assert(a2 != NULL);

	a2->arg = new_term(a1->arg);
	a2->next = new_arg_p(a1->next);

	return a2;
}

/**************************************************************************
 * Functions to create a term on the heap from a symbol and vector of terms.
 ***************************************************************************/

TERM build_function_term(char* term_symbol, vector<TERM> v1)
{
     TERM t1;
     t1.sym = strdup(term_symbol);
     t1.is_var = 0;
     t1.num_args = 0;

     ARG* head = NULL;
     ARG* tail = NULL;

     for(unsigned int i = 0; i < v1.size(); i++) {
          ARG* new_arg = new ARG();
          new_arg->arg = new_term(v1[i]);
          new_arg->next = NULL;

          if (head == NULL)
               head = tail = new_arg;
          else {
               tail->next = new_arg;
               tail = new_arg;
          }
     }
     t1.args = head;

     return t1;
}

/**************************************************
 * Free the memory allocated on the heap for a term
 **************************************************/

void free_term(TERM t)
{
	if (t.args != NULL) 
		free_arg_p(t.args);

	if (t.sym != NULL)
		free(t.sym);

	return;
}


void free_arg_p(ARG *p)
{
	free_term(p->arg);

	if (p->next != NULL)
		free_arg_p(p->next);

	free(p);
}


/*******************************************************
 * Functions which print the fields in the data structs.
 *******************************************************/

void print_arg_struct(ARG a)
{
	print_term_struct(a.arg);
	
	if (a.next != NULL) 
	{
		printf(",");
		print_arg_struct(*(a.next));
	}
}

void print_term_struct(TERM t)
{
	if (t.sym == NULL)
		return;
	else
	 	printf("%s[%d]", t.sym, t.is_var);
	
	if (t.args != NULL)
	{
		printf("(");
		print_arg_struct(*(t.args));
		printf(")");
	}
		
}

void print_lit_struct(LIT l)
{
	if (l.is_pos == 0)
		printf("~ ");

	print_term_struct(l.atom);
}


/***********************************************************************
 * Functions used to print to stdout a clause as dijunction of literals. 
 ***********************************************************************/

void print_arg(ARG a)
{
	print_term(a.arg);
	
	if (a.next != NULL)
	{
		printf(",");
		print_arg(*(a.next));
	}
}

void print_term(TERM t)
{
	if (t.sym == NULL)	
		return;
	else
	 	printf("%s", t.sym);
	 	
	if (t.args != NULL)
	{
		printf("(");
		print_arg(*(t.args));
		printf(")");
	}
		
}

void print_lit(LIT l)
{
	if (l.is_pos == 0)
		printf("~ ");

	print_term(l.atom);

}

void print_arg_p(ARG *a)
{
	assert (a != NULL);

	print_term(a->arg);
	
	if (a->next != NULL)
	{
		printf(",");
		print_arg(*(a->next));
	}
	printf("\n");
}

/*******************************************************************
 * Function to create string or char array representation of a TERM
 *******************************************************************/

char* arg2string(const ARG a, char* str)
{
	str = term2string(a.arg, str);
	
	if (a.next != NULL)
	{
		strcat(str,",");
		str = arg2string(*(a.next),str);
	}

	return str;
}

char* term2string(const TERM t, char* str)
{
	if (t.sym == NULL)	
		return str;
	else
	 	strcat(str, t.sym);
	 	
	if (t.args != NULL) {
		strcat(str, "(");
		arg2string(*(t.args), str);
		strcat(str, ")");
	}

	return str;
}

string term_to_string( TERM &term_term )
{
     string term_string;
     assert( term_term.sym!=NULL );

     //variable
     if( term_term.is_var ) {
          term_string.append( term_term.sym);
     }
     //constant
     else if( (term_term.is_var == 0) && (term_term.args==NULL) ) {
          term_string.append( term_term.sym);
     }
     //function
     else {
          term_string.append( term_term.sym);
          ARG *term_arg=term_term.args;
          term_string= term_string + "(";
          assert( term_arg!=NULL );
          term_string=term_string+term_to_string(term_arg->arg);
          term_arg=term_arg->next;
          while( term_arg!=NULL ) {
               term_string+=", ";
               term_string=term_string+term_to_string(term_arg->arg);
               term_arg=term_arg->next;
          }
          term_string= term_string + ")";
     }

     return term_string;
}

string sub_to_string( SUB &substitution )
{
     string sub_string;

     assert( substitution.domain.sym != NULL && substitution.range.sym != NULL );

     sub_string.append( substitution.domain.sym);
     sub_string=sub_string + "=";
     sub_string=sub_string + term_to_string( substitution.range );

     return sub_string;
}

/*
 * equal() takes two terms and returns true if the terms have identical symbols
 * and false otherwise.
 */

bool equal(TERM s, TERM t)
{
     if(strcmp(s.sym,t.sym) != 0)
          return false;

     ARG *si = s.args;
     ARG *ti = t.args;

     while( si != NULL && ti != NULL && equal(si->arg,ti->arg) ) {
          si = si->next;
          ti = ti->next;
     }

     return (si == NULL && ti == NULL);
}

/* END OF FILE */
