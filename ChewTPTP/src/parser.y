 %{

#include "stdio.h" 
#include "stdlib.h"
#include "unistd.h"
#include "assert.h"

#include "main.h"
#include "struct.h"

#define DEBUG_PARSER_PRINT_GRAMMAR_TREE		0
#define DEBUG_PARSER_PRINT_DATA_STRUCT		0
#define DEBUG_PARSER_PRINT_HEADING			0
#define DEBUG_PARSER_PRINT_CL_A			0
#define DEBUG_PARSER_PRINT_LIT_A			0
#define DEBUG_PARSER_PRINT_ARG_A			0

#define UNASSIGNED				2
#define IS_A_VARIABLE				1
#define IS_NOT_A_VARIABLE			0

extern "C" {

  int yyparse();
  int yylex(void);
  void yyerror(char*);
  int yywrap()
  {
    return 1;
  }

}

using namespace std;

/**************************************
 * Global variables defined in main.cpp
 **************************************/
extern LIT **cl_a; 		/* Holds all clauses at the end of parsing a problem. */
extern int *num_lit;		/* Number of literals per clause. Set after the clause has been parsed. */
 
/**************************************
 * Other global variables used in parser
 ***************************************/

int num_clauses = 0;		/* Number of clauses currently added to cl_a. */

LIT lit_a[MAXLITS];		/* Array which temporarily holds literals while clause is being parsed. */
int lit_ct = 0;			/* Number of literals in the clause being parsed. */

ARG arg_a[MAXARGS];		/* Array which temporarily holds the arguments while literal is being parsed. */
int arg_ct = 0;			/* Number of arguments in the literal being parsed. */


/*********************************
 * Functions used during parsing.
 ********************************/

void reset_arg_a()
{
	int i = 0;
	
	/* 
	 * After parsing a term we reset arg_a[] so we can use it for the 
	 * next term. 
	 */
	
	for (i = 0; i < MAXARGS; i++)
	{
		arg_a[i].arg.sym = NULL;
		arg_a[i].arg.is_var = UNASSIGNED;
		arg_a[i].arg.num_args = 0;
		arg_a[i].arg.args = NULL;
		arg_a[i].next = NULL;
	}

	return;
} 

void reset_arg(int i)
{
	/* 
	 * While working up the grammar, we link arg_a[i] with its
	 * parent in arg_a[i-1] and reset arg_a[i]. 
	 */
	
	arg_a[i].arg.sym = NULL;
	arg_a[i].arg.is_var = UNASSIGNED;
	arg_a[i].arg.num_args = 0;
	arg_a[i].arg.args = NULL;
	arg_a[i].next = NULL;

	return;
} 


/**********************************
 * Functions for debugging. 
 *********************************/

void print_problem()
{
	int cl = 0;
	int lit = 0;

	if (DEBUG_PARSER_PRINT_HEADING)
	{
		printf("THE PROBLEM\n");
	}

	for (cl = 0; cl < num_clauses; cl++)
	{
		for (lit = 0; lit < num_lit[cl]; lit++)
		{
			print_lit(cl_a[cl][lit]);
			if (lit < num_lit[cl] - 1)
				printf(" | ");
		}
		printf("\n");
	}
	printf("\n");
	return;
}

void print_cl_a()
{
	int cl = 0;
	int lit = 0;

	if (DEBUG_PARSER_PRINT_HEADING)
	{
		printf("THE ARRAY containing %d clauses.\n", num_clauses);
	}

	for (cl = 0; cl < num_clauses; cl++)
	{
		for (lit = 0; lit < num_lit[cl]; lit++)
		{
			print_lit_struct(cl_a[cl][lit]);
			if (lit < num_lit[cl] - 1)
				printf(" | ");
		}
		printf("\n");
	}
	printf("\n");
	return;
}

void print_lit_a()
{
	int i = 0;

	if (DEBUG_PARSER_PRINT_HEADING)
	{
		printf("DEBUGGING lit_a[] containing %d literals.\n", lit_ct);
	}

	while (i < lit_ct) 
	{
		print_lit_struct(lit_a[i++]);
		if (i < lit_ct)
			printf(" | ");
	}
	printf("\n");
	return;
}


void print_arg_a()
{
	int i = 0;

	if (DEBUG_PARSER_PRINT_HEADING)
	{
		printf("DEBUGGING arg_a[]\n");
	}

	while (arg_a[i].arg.sym != NULL)
	{
		print_arg_struct(arg_a[i]);
		if (arg_a[i].next != NULL)
			printf(" , ");
		i++;
	}
	printf("\n");
	return;
}

void print_seperator() 
{
	printf("-----------------------------------------\n");
	return;
}


%}


%union {
	int	ival;	/* attribute value of  */
	float	rval;	/* attribute value of  */
	char	*sval;	/* attribute value of UPPER_WORD,LOWER_WORD */
}

%token FOF CNF TRUE FALSE INCLUDE 
%token DISTINCT_OBJECT DOLLAR_DOLLAR_WORD 

%token <sval> LOWER_WORD 
%token <sval> UPPER_WORD 
%token <sval> SINGLE_QUOTED
%token <rval> REAL
%token <ival> SIGNED_INTEGER
%token <ival> UNSIGNED_INTEGER

%type <sval> functor 
%type <sval> atomic_word 
%type <sval> constant 
%type <sval> constant_word 
%type <sval> plain_term 
%type <sval> variable
 

%%
TPTP_file:	TPTP_input
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("TPTP_file:TPTP_input\n");
	
			}
	| 	TPTP_file TPTP_input
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("TPTP_file:TPTP_file TPTP_input\n");
	
			}
	;

TPTP_input:	annotated_formula
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("TPTP_input:annotated_formula\n");
	
			}
	|	include		
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("TPTP_input:include\n");
				printf("SZS status InputError: include statement\n");
				exit(1);
	
			}
	;

annotated_formula:	cnf_annotated
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("annotated_formula:cnf_annotated\n");
	
			}
		;

cnf_annotated:	CNF '(' name ',' formula_role ',' cnf_formula annotations ')' '.'
			{
				/*
				 * An entire cnf clause has been parsed.  Data for lit_ct literals has 
				 * been stored in lit_a[]. 
				 */ 

				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("cnf_annotated:CNF(name,formula_role,cnf_formula annotations).\n");

				/*
				 * We record in num_lit[] how may literals are contained in the clause.
				 */

				num_lit[num_clauses] = lit_ct;

				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\t\tadd [%d] literals to cl_a[%d]\n", num_lit[num_clauses], num_clauses);

				if (DEBUG_PARSER_PRINT_LIT_A)
					print_lit_a();

				int i = 0;
			 	/* 
				 * We move the data of the literals in lit_a[] into the clause array cl_a[][].
 	 			 */
				for (i = 0; i < lit_ct; i++)
				{
					cl_a[num_clauses][i].is_pos = lit_a[i].is_pos;
					cl_a[num_clauses][i].atom.sym = lit_a[i].atom.sym;
					cl_a[num_clauses][i].atom.is_var = lit_a[i].atom.is_var;
					cl_a[num_clauses][i].atom.args = lit_a[i].atom.args;
				}
				/*
				 * We reset lit_a[] so the next clause being read can use it.
				 */
				for (i = 0; i < lit_ct; i++)
				{
					lit_a[i].atom.sym = NULL;
					lit_a[i].atom.is_var = UNASSIGNED;
					lit_a[i].atom.args = NULL;
				}
				/*
				 * We reset lit_ct so we can use in parsing the next clause and we
				 * increment the number of clauses parsed.
				 */
			
				lit_ct = 0;
				num_clauses++;
				if (DEBUG_PARSER_PRINT_CL_A)
					print_cl_a();

			}
	;

annotations: 	null	
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("annotations:null\n");
	
			}
	|	',' source optional_info
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("annotations:,source optional_info\n");
	
			}
	;

formula_role:	LOWER_WORD
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\nformula_role:LOWER_WORD\n");
	
			}
	;

cnf_formula:	'(' disjunction ')'
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("cnf_formula:(disjunction)\n");
	
			}
	|	disjunction
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("cnf_formula:disjunction\n");
	
			}
	;

disjunction:	literal 
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("disjunction:literal\n");
	
			}
	|	literal more_disjunction
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("disjunction:literal more_disjunction\n");
	
			}
	;

more_disjunction:	'|' literal
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("more_disjunction:|literal\n");
	
			}
		| 	'|' literal more_disjunction
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("more_disjunction:|literal more_disjunction\n");
	
			}
		;

literal:	atomic_formula
			{
				/*
				 * An entire literal has been parsed.  Data for it's term and arguements 
				 * has been stored in are in arg_a[0]. 
				 */
	 
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("literal:atomic_formula\n");
				
				/*
				 * We convert a defined_term with equality into a predicate with sym = "equals". 
				 * If sym != "equals" then the current literal which has been completely read 
				 * into memory is positive, otherwise is_pos depends on if the defined_term was
				 * an equality or disequality.
				 */
				
				if (strcmp(arg_a[0].arg.sym, "not_equals") == 0) {
					free(arg_a[0].arg.sym);
					arg_a[0].arg.sym = strdup("equals");
					lit_a[lit_ct].is_pos = 0;
				}
				else 
					lit_a[lit_ct].is_pos = 1;

				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\tlit_ct[%d] arg_ct[%d]\n",lit_ct, arg_ct);
				
				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\tlit_a[%d].is_pos: %d\n", lit_ct, lit_a[lit_ct].is_pos);

				/*
				 * When working up the parse tree we link child args to their parents
				 * and reset the child arg data in arg_a[] to be used by future args.
				 * When we reset the data, we decrement arg_ct.  When we have worked
				 * our way up the parse tree to a literal, the arg_ct should be 1.
				 */

				assert(arg_ct == 1);

				/*
				 * The contents of arg_a[0] are copied into lit_a[lit_ct].
				 */

				lit_a[lit_ct].atom.sym = arg_a[0].arg.sym;
				lit_a[lit_ct].atom.is_var = arg_a[0].arg.is_var;
				lit_a[lit_ct].atom.args = new_arg_p(arg_a[0].arg.args);
				
				/*
				 * arg_a[] is reset before parsing the next literal.
				 */

				reset_arg_a();

				arg_ct = 0;
				lit_ct++;

				if (DEBUG_PARSER_PRINT_LIT_A)
					print_lit_a();  

				if (DEBUG_PARSER_PRINT_ARG_A)
					print_arg_a();
	
			}			 
	|	'~' atomic_formula 
			{
				/*
				 * An entire literal has been parsed.  Data for it's term and arguements 
				 * has been stored in are in arg_a[0]. 
				 */
	 
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("literal:atomic_formula\n");
 
				/*
				 * The current literal which has been completely read into memory
				 * is negative. 
				 */
				
				lit_a[lit_ct].is_pos = 0;

				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\tlit_ct[%d] arg_ct[%d]\n",lit_ct, arg_ct);
				
				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\tlit_a[%d].is_pos: %d\n", lit_ct, lit_a[lit_ct].is_pos);

				/*
				 * When working up the parse tree we link child args to their parents
				 * and reset the child arg data in arg_a[] to be used by future args.
				 * When we reset the data, we decrement arg_ct.  When we have worked
				 * our way up the parse tree to a literal, the arg_ct should be 1.
				 */

				assert(arg_ct == 1);

				/*
				 * The contents of arg_a[0] are copied into lit_a[lit_ct].
				 */

				lit_a[lit_ct].atom.sym = arg_a[0].arg.sym;
				lit_a[lit_ct].atom.is_var = arg_a[0].arg.is_var;
				lit_a[lit_ct].atom.args = new_arg_p(arg_a[0].arg.args);
				
				/*
				 * arg_a[] is reset before parsing the next literal.
				 */

				reset_arg_a();

				arg_ct = 0;
				lit_ct++;

				if (DEBUG_PARSER_PRINT_LIT_A)
					print_lit_a();

				if (DEBUG_PARSER_PRINT_ARG_A)
					print_arg_a();
	
			}			 
	;

atomic_formula:	plain_atom
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("atomic_formula:plain_atom\n");
	
			}
	|	defined_atom
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("atomic_formula:defined_atom\n");
	
			}
	|	system_atom
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("atomic_formula:system_atom\n");
	
			}
	;

plain_atom:	plain_term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("plain_atom:plain_term\n");
	
			}
	;

arguments:	term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("arguments:term\n");
				
			}
	|	term ',' arguments
			{
				/*
				 * A list of arguments has been parsed (not necessarily a complete
				 * set of arguments).
				 */
			
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("arguments:term,arguments\n");

				/*
				 * Arguments are a linked list of args.  We link the child arg to
				 * its parent.
				 */

				arg_a[arg_ct - 2].next = new_arg_p(&arg_a[arg_ct - 1]);
				reset_arg(arg_ct - 1);
				arg_ct--;
	
			}
	;

defined_atom:	TRUE
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\ndefined_atom:TRUE\n");
	
			}
	|	FALSE
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\ndefined_atom:FALSE\n");
	
			}
	|	term defined_infix_pred term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("defined_atom:term defined_infix_pred term\n");
	
				arg_a[0].arg.args->next = new_arg_p(&arg_a[1]);
				reset_arg(1);
				arg_ct = 1;
			}
	;

defined_infix_pred:	'='	
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("defined_infix_pred:=\n");

				ARG* temp = new_arg_p(&arg_a[0]);
				reset_arg(0);

				arg_a[0].arg.sym = strdup("equals");
				arg_a[0].arg.is_var = IS_NOT_A_VARIABLE;
				arg_a[0].arg.args = temp;

				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\targ_a[0].arg.sym:[%s]\n", 
						arg_a[0].arg.sym);

				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\targ_a[0].arg.is_var:[%d]\n", 
						arg_a[0].arg.is_var);

				arg_ct = 1;
			}
		|	'!' '='	
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("defined_infix_pred:!=\n");
	
				ARG* temp = new_arg_p(&arg_a[0]);

				arg_a[0].arg.sym = strdup("not_equals");
				arg_a[0].arg.is_var = IS_NOT_A_VARIABLE;
				arg_a[0].arg.args = temp;

				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\targ_a[0].arg.sym:[%s]\n", 
						arg_a[0].arg.sym);

				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\targ_a[0].arg.is_var:[%d]\n", 
						arg_a[0].arg.is_var);

				arg_ct = 1;
			}
		;

system_atom:	system_term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("system_atom:system_term\n");
	
			}
	;

term:		function_term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("term:function_term\n");
				

			}
	|	variable
			{
				/*
				 * An entire varible has been parsed.
				 */

				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("term:variable\n");
				
				/*
				 * Assert that there is text in the buffer.
				 */

				assert($1 != NULL);
			
				/*
				 * Create string which consists of the clause index prefixed
				 * to the string in the buffer.
				 */

				//char temp[128];
				//sprintf(temp, "%d", num_clauses);
				//arg_a[arg_ct].arg.sym = strdup($1);
				//strcat(arg_a[arg_ct].arg.sym, temp);  
				
				char temp[128];
				sprintf(temp, "v_%s%d", $1, num_clauses);
				arg_a[arg_ct].arg.sym = strdup(temp);

				/*
				 * Set field to indicate the parsed arg is a variable.
				 */

			 	arg_a[arg_ct].arg.is_var = IS_A_VARIABLE;
				
				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\targ_a[%d].arg.sym:[%s]\n", 
						arg_ct, arg_a[arg_ct].arg.sym);

				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\targ_a[%d].arg.is_var:[%d]\n", 
						arg_ct, arg_a[arg_ct].arg.is_var);
				
				/*
				 * Increment the number of args parsed.
				 */
				
				arg_ct++;

			}
	;

function_term:	plain_term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("function_term:plain_term\n");
	
			}
	|	defined_term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("function_term:defined_term\n");
	
			}
	|	system_term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("function_term:system_term\n");
	
			}
	;

plain_term:	constant
			{	
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("plain_term:constant\n");

			}
	|	functor '(' arguments ')' 
			{
				/*
				 * A function with arguments has been parsed.
				 */

				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("plain_term:functor(arguments)\n");
				
				/*
   				 * The arguements to the function are copied and linked to the 
				 * function's args field.  The old arg is reset for later use.
				 */
				
				//arg_a[arg_ct - 2].arg.args = &arg_a[arg_ct - 1];

				arg_a[arg_ct - 2].arg.args = new_arg_p(&arg_a[arg_ct - 1]);
				reset_arg(arg_ct - 1);
				arg_ct--;

			}
	;

constant:	constant_word
			{
				/*
				 * A constant has been parsed.
				 */

				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("constant:constant_word\n");
				
				/*
 				 * We make sure that there is text in the buffer, copy the 
				 * string into an argument, and set that it is not a variable.
				 */

				assert($1 != NULL);
		
				char temp[128];
				sprintf(temp, "c_%s", $1);
				arg_a[arg_ct].arg.sym = strdup(temp);

			 	arg_a[arg_ct].arg.is_var = IS_NOT_A_VARIABLE;
				
				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\targ_a[%d].arg.sym:[%s]\n", 
						arg_ct, arg_a[arg_ct].arg.sym);

				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\targ_a[%d].arg.is_var:[%d]\n", 
						arg_ct, arg_a[arg_ct].arg.is_var);

				/*
				 * We increment the arguement counter.
				 */

				arg_ct++;
			} 
	;

functor:	atomic_word 
			{
				/*
				 * A function symbol has been parsed.
				 */

				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("functor:atomic_word\n");

				/*
 				 * We make sure that there is text in the buffer, copy the 
				 * string into an argument, and set that it is not a variable.
				 */
				
				assert($1 != NULL);

				char temp[128];
				sprintf(temp, "f_%s", $1);
				arg_a[arg_ct].arg.sym = strdup(temp);

			 	arg_a[arg_ct].arg.is_var = IS_NOT_A_VARIABLE;
				
				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\targ_a[%d].arg.sym:[%s]\n", 
						arg_ct, arg_a[arg_ct].arg.sym);

				if (DEBUG_PARSER_PRINT_DATA_STRUCT)
					printf("\targ_a[%d].arg.is_var:[%d]\n", 
						arg_ct, arg_a[arg_ct].arg.is_var);

				/*
				 * We increment the arguement counter.
				 */
				
				arg_ct++;
			}
			
	;

defined_term:	number
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("defined_term:number\n");
	
			}
	|	DISTINCT_OBJECT	
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\ndefined_term:DISTINCT_OBJECT\n");
	
			}
	;

system_term:	system_constant
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("system_term:system_constant\n");
	
			}
	|	system_functor '(' arguments ')'
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("system_term:system_functor(arguments)\n");
	
			}
	;

system_functor:	atomic_system_word
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("system_functor:atomic_system_word\n");
	
			}
	;

system_constant:	atomic_system_word
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("system_constant:atomic_system_word\n");
	
			}
	;

variable:	UPPER_WORD 
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\nvariable:UPPER_WORD\n");
	
			}	
	;

source:		general_term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("source:general_term\n");
	
			}
	;

optional_info:	',' useful_info
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("optional_info:,useful_info\n");
	
			}
	|	null
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("optional_info:null\n");
	
			}
	;

useful_info:	general_term_list
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("useful_info:general_term_list\n");
	
			}
	;

include:	INCLUDE '(' file_name formula_selection ')' '.'
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("INCLUDE(file_name formula_selection).\n");
	
			}
	;

formula_selection:	',' '[' name_list ']'
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("formula_selection:,[name_list]\n");
	
			}
		|	null
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("formula_selection:null\n");
	
			}
		;

name_list:	name
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("name_list:name\n");
	
			}
	|	name ',' name_list
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("name_list:name,name_list\n");
	
			}
	;

general_term:	general_data
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("general_term:general_data\n");
	
			}
	|	general_data ':' general_term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("general_term:general_data:general_term\n");
	
			}
	|	general_list
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("general_term:general_list\n");
	
			}
	;

general_data:	general_word
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("general_data:general_word\n");
	
			}
	|	general_word '(' general_arguments ')'
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("general_data:general_word\n");
	
			}
	|	number
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("general_data:number\n");
	
			}
	|	DISTINCT_OBJECT
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\ngeneral_data:DISTINCT_OBJECT\n");
	
			}
	;

general_arguments:	general_term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("general_arguments:general_term\n");
	
			}
		|	general_term ',' general_arguments
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("general_arguments:general_term\n");
	
			}
		;

general_list:	'[' ']'
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("[]\n");
	
			}
	|	'[' general_term_list ']'
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("general_list:[general_term_list]\n");
	
			}
	;

general_term_list:	general_term
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("general_term_list:general_term\n");
	
			}
		|	general_term ',' general_term_list
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("general_term_list:general_term , general_term_list\n");
	
			}
		;

name:		name_word
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("name:name_word\n");
	
			}
	|	UNSIGNED_INTEGER
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\nname:UNSIGNED_INTEGER\n");
	
			}
	;

atomic_word:	LOWER_WORD 
		{
			if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
				printf("\natomic_word:LOWER_WORD\n");

		}
	|	SINGLE_QUOTED 
		{
			if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
				printf("\natomic_word:SINGLE_QUOTED\n");

		}
	;


constant_word:	LOWER_WORD
		{
			if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
				printf("\nconstant_word:SINGLE_QUOTED\n");

		}
	|	SINGLE_QUOTED 
		{
			if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
				printf("\nconstant_word:SINGLE_QUOTED\n");

		}
	;

general_word:	LOWER_WORD
		{
			if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
				printf("\ngeneral_word:SINGLE_QUOTED\n");

		}
	|	SINGLE_QUOTED
		{
			if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
				printf("\ngeneral_word:SINGLE_QUOTED\n");
		
		}
	;

name_word:	LOWER_WORD 
		{
			if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
				printf("\nname_word:SINGLE_QUOTED\n");

		}
	|	SINGLE_QUOTED
		{
			if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
				printf("\nname_word:SINGLE_QUOTED\n");
		
		}
	;

atomic_system_word:	DOLLAR_DOLLAR_WORD
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\natomic_system_word:DOLLAR_DOLLAR_WORD\n");
		
			}
			
		;

number:		REAL
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\nnumber:REAL\n");
		
			}

	|	SIGNED_INTEGER
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\nnumber:SIGNED_INTEGER\n");
		
			}
	|	UNSIGNED_INTEGER
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\nnumber:UNSIGNED_INTEGER\n");
		
			}
	;

file_name:	atomic_word
			{
				if (DEBUG_PARSER_PRINT_GRAMMAR_TREE)
					printf("\nfile_name:atomic_word\n");
		
			}
	;

null:		
	;
%%

void yyerror(char *s)
{
	fprintf(stderr, "%s\n",s);
}



/*--------------END OF FILE-------------------*/
