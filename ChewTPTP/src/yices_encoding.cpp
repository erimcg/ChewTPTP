#include <vector>
#include <string>

#include "stdio.h" 
#include "stdlib.h"
#include "unistd.h"
#include "assert.h"

#include "struct.h"
#include "yicesl_c.h"

using namespace std;

//#define DEBUG 1

/**************************************
 * Global variables defined in main.cpp
 **************************************/

extern LIT **cl_a;
extern int *num_lit;	
extern int cl_ct;	
extern yicesl_context ctx;
extern vector<TERM> term_symbols;

int find_arg_terms(ARG a)
{
     TERM t = a.arg;

     if (t.args != NULL)
          t.num_args = find_arg_terms(*(t.args));
     else
          t.num_args = 0;

     vector<TERM>::iterator iter;
     bool duplicate = false;

     for (iter = term_symbols.begin(); iter != term_symbols.end(); ++iter)
     {
          TERM t2 = *(iter);
          if (strcmp(t2.sym, t.sym) == 0)
          {
               duplicate = true;
               break;
          }
     }

     if (duplicate == false)
          term_symbols.push_back(t);

     if (a.next != NULL)
          return find_arg_terms(*(a.next)) + 1;
     else
          return 1;
}

void find_terms_of_atom(TERM t)
{
     vector<TERM>::iterator iter;
     bool duplicate = false;

     for (iter = term_symbols.begin(); iter != term_symbols.end(); ++iter)
     {
          TERM t2 = *(iter);
          if (strcmp(t2.sym, t.sym) == 0)
          {
               duplicate = true;
               break;
          }
     }

     if (t.args != NULL)
          t.num_args = find_arg_terms(*(t.args));
     else
          t.num_args = 0;

     if (duplicate == false)
          term_symbols.push_back(t);

}

void find_terms()
{
     int cl = 0;
     int lit = 0;

     for (cl = 0; cl < cl_ct; cl++)
          for (lit = 0; lit < num_lit[cl]; lit++)
               find_terms_of_atom(cl_a[cl][lit].atom);

     return;
}

void assert_term_type()
{
     vector<TERM>::iterator iter;
     char yices_op[5024];

	find_terms();

     sprintf(yices_op, "(define-type term(datatype v_chewtptp");

     for (iter = term_symbols.begin(); iter != term_symbols.end(); ++iter)
     {
          TERM t1 = *(iter);
          if (t1.is_var == false && t1.num_args == 0)
               sprintf(yices_op, "%s %s", yices_op, t1.sym);
     }

     for (iter = term_symbols.begin(); iter != term_symbols.end(); ++iter)
     {
          TERM t2 = *(iter);
          if (t2.is_var == false && t2.num_args > 0)
          {
               sprintf(yices_op, "%s (%s", yices_op, t2.sym);
               for (int i = 0; i < t2.num_args; i++)
                    sprintf(yices_op, "%s %sarg%d::term", yices_op, t2.sym, i+1);
               sprintf(yices_op, "%s)", yices_op);
          }
     }
     sprintf(yices_op, "%s))", yices_op);
     yicesl_read(ctx, yices_op);

     for (iter = term_symbols.begin(); iter != term_symbols.end(); ++iter)
     {
          TERM t3 = *(iter);
          if (t3.is_var == true) {
               sprintf(yices_op, "(define %s::term)", t3.sym);
               yicesl_read(ctx, yices_op);
          }
     }

     return;
}

void term2YicesDatatype(TERM t, char* ptr)
{
     if (t.args == NULL)
     {
          strcat(ptr, t.sym);
          return;
     }

     strcat(ptr, "(");
     strcat(ptr, t.sym);
     ARG* arg1 = t.args;
     while(arg1 != NULL)
     {
          strcat(ptr, " ");
          term2YicesDatatype(arg1 -> arg, ptr);
          arg1 = arg1 -> next;
     }
     strcat(ptr, ")");
}

/*--------------END OF FILE-------------------*/
