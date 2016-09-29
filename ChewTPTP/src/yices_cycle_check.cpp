#include <vector>
#include <string>
#include <stack>
#include <iostream>
#include <fstream>
#include <sys/types.h>
#include <sys/wait.h>

#include "string.h"
#include "stdio.h" 
#include "stdlib.h"

#include "main.h"
#include "struct.h"
#include "unification.h"
#include "yices_encoding.h"
#include "yices_nonhorn_cyclic_tableaux_encoding.h"
#include "yicesl_c.h"

using namespace std;

/*********************************************
 * Global data structures defined in main.cpp 
 ********************************************/

extern LIT **cl_a;
extern yicesl_context ctx;
extern char output_file[];
extern char theorem_name[];
extern int verbose;

/********************************************
 * Global variables used in this source file.
 ********************************************/

vector<char*> yices_vars;
vector<SUB> yices_subs;

stack<char *> lit_stack;
vector<char *> lit_path;
deque<char*> exp_queue;
vector<SUB> lit_subs;
vector<SUB> yices_mgu;
vector<vector<SUB> > assert_subs;

TERM read_term(int &num_open_paren)
{
     char *ptr;
     ptr = strtok(NULL, " ");

     TERM t;
     vector<TERM> args;

     if (*ptr == '(') {
          num_open_paren++;
          int cur_level = num_open_paren;

          while(cur_level == num_open_paren)
               args.push_back(read_term(num_open_paren));

          t = build_function_term(ptr+1, args);
     }
     else if (*ptr == 'c' || *ptr == 'v') {

          for (unsigned int i = 0; i < strlen(ptr); i++)
               if (*(ptr+i) == ')')
                    num_open_paren--;

          for (unsigned int i = 0; i < strlen(ptr); i++)
               if (*(ptr+i) == ')')
                    *(ptr+i) = '\0';

          t.sym = strdup(ptr);
          t.num_args = 0;
          t.args = NULL;
     
		if (*ptr == 'c')
          	t.is_var = 0;
		else if (*ptr == 'v')
          	t.is_var = 1;
     }

     return t;
}


void get_yices_subs_and_vars()
{
     vector<char*> assignments;
 
    /*
      * Make sure that we can open the yices solution file.
      */

     ifstream yices_solution_stream(output_file);
     if (!yices_solution_stream) {
         	cout << "SZS status Error for " << theorem_name << 
          	": cannot open file " << output_file << endl;
		if (!verbose)
			remove_files_and_exit();
		else 
			exit(1);
     }

     yices_solution_stream.clear();
     yices_solution_stream.seekg(0);

	/*
 	 * Reset the vector that holds the true variables.
	 */

	yices_vars.clear();

     /*
      * For each line in the yikes solution file, if the line has an underscore then
	 * the line is part of an assignment which may span multiple lines, else if it 
	 * has a string 'true' it is a variable assignment. 
      */

     string str;
     while (!yices_solution_stream.eof()) {

          getline(yices_solution_stream, str);
          size_t i = str.find("_");
          if (i != string::npos) {
     		char assignment[1024];
     		const char *buf;
     		int lpar = 0;
     		int rpar = 0;
     		bool partial_assignment_found = true;
     		
			assignment[0] = '\0';

			while (partial_assignment_found) {

				buf = str.c_str();
		          strcat(assignment, buf);

		          /*
		           * Count number of left paren (lpar) and right paren (rpar).
		           * If lpar > rpar then next line is included in the current assignment.
		           */

		          for (unsigned int j = 0; j < strlen(buf); j++) {
		               if (buf[j] == '(')
		                    lpar++;
		               else if (buf[j] == ')')
		                    rpar++;
		          }

		          if (lpar == rpar) {
		               assignments.push_back(strdup(assignment));
    					partial_assignment_found = false;
		          }
		          else if (lpar < rpar) {
		          	cout << "SZS status Error for " << theorem_name << 
						": assignment has improper form" << endl;
					if (!verbose)
						remove_files_and_exit();
					else 
						exit(1);
		          }
		          else if (lpar > rpar) {

					while(true) {
     					if (!yices_solution_stream.eof()) {
          					getline(yices_solution_stream, str);
						}
						else {
		          			cout << "SZS status Error for " << theorem_name << 
								": incomplete assignment" << endl;
							if (!verbose)
								remove_files_and_exit();
							else 
								exit(1);
						}

						if (str.size() != 0) 
							break;
					}
	 
          			i = str.find("_");

     	     		if (i == string::npos) {
			         		cout << "SZS status Error for " << theorem_name << 
							": file has improper form" << endl;
						if (!verbose)
							remove_files_and_exit();
						else 
							exit(1);
					}
				}
				// now process str at top of loop
		     }
               continue;
          }
          size_t j = str.find("true");
          if (j != string::npos) {
			yices_vars.push_back(strdup(str.c_str()));
               continue;
          }
     }

     /*
      * Now close stream.
      */

     yices_solution_stream.close();

     /*
      * Parse each assignment (= domain range).  Convert domain and range
      * to chewtptp format TERMs and put in vector yices_subs.
      */

     char *c_ptr;
     for (unsigned int i = 0; i < assignments.size(); i++) {
          c_ptr = strtok(assignments[i], " ");

          if (c_ptr == NULL) {
          	cout << "SZS status Error for " << theorem_name << 
				": null token" << endl;
			if (!verbose)
				remove_files_and_exit();
			else 
				exit(1);
          }

          if (strcmp(c_ptr, "(=") != 0) {
          	cout << "SZS status Error for " << theorem_name << 
				": invalid first token" << endl;
			if (!verbose)
				remove_files_and_exit();
			else 
				exit(1);
          }

          SUB E;
          int ref_var = 0;

          E.domain = read_term(ref_var);
          E.range = read_term(ref_var);

          yices_subs.push_back(E);
     }

	/*
	 * Free the assignments
	 */

     for (unsigned int i = 0; i < assignments.size(); i++) {
		free(assignments[i]);
	}
	
}

int push_lits_on_stack(int clause_num, int lit_num)
{
	char prefix[8];  
	char s1[16];
	char s2[16];
	char s3[16];
	int len = 0;
	char *lit;

	/*
	 * We are looking for variables that are "true" of the form "lnak" where n is clause_num and k is any
	 * integer not equal to lit_num.
	 */

	sprintf(prefix, "l%da", clause_num);
	len = strlen(prefix);
	int count = 0;

	for (unsigned int i=0; i < yices_vars.size(); i++) {
		sscanf(yices_vars[i], "%s %s %s", s1, s2, s3);
	
		if (strncmp(s2, prefix, len) == 0){
			lit = strdup(s2);

			int c;
			int l;
			sscanf(lit, "l%da%d", &c, &l);

			if (l != lit_num) {
				lit_stack.push(lit);
				count++;
			}
		}
	}

	return count;
}

void get_lit(char *lit)
{
	int cl, l;
	sscanf(lit, "l%da%d", &cl, &l);

	print_lit(cl_a[cl][l]);	
}

void print_data_structs()
{
	int len = lit_path.size();

	cout << "---------------------\n";
	cout << "-lit path--\n";
	cout << "---------------------\n";
	for (int j = 0; j < len; j++) {
		cout << lit_path[j] << " - ";
		get_lit(lit_path[j]); 
		cout << "\n";
	}
	cout << "---------------------\n";

	len = exp_queue.size();

	cout << "---------------------\n";
	cout << "-exp queue-\n";
	cout << "---------------------\n";
	for (int j = 0; j < len; j++)
		cout << exp_queue[j] << "\n";
	cout << "---------------------\n";

}

void print_exp_queue()
{
	int len = exp_queue.size();

	cout << "-----------\n";
	cout << "-exp queue-\n";
	cout << "-----------\n";
	for (int j = 0; j < len; j++)
		cout << exp_queue[j] << "\n";
	cout << "-----------\n\n";

}

void backtrack()
{

	if (lit_stack.empty())
		return;

	char *lit = lit_stack.top();
	int cl, l;
	sscanf(lit, "l%da%d", &cl, &l);
	
	char prefix[16];
	sprintf(prefix, "l%da", cl);
	int prefix_len = strlen(prefix);

	int path_len = lit_path.size();

	char *back_lit;
	char *back_exp;
	for(int j = path_len - 1; j >= 0; j--) {
		if (strncmp(prefix, lit_path[j], prefix_len) == 0) {
			back_exp = exp_queue.back();
			exp_queue.pop_back();
			free(back_exp);

			back_lit = lit_path.back();
			lit_path.pop_back();
			free(back_lit);
	
			return;
		}
		back_exp = exp_queue.back();
		exp_queue.pop_back();
		free(back_exp);

		back_lit = lit_path.back();
		lit_path.pop_back();
		free(back_lit);
	}

	return;
}

bool subs_consistent() 
{
	TERM t1;
	TERM t2;
	vector<TERM> t1_args;
	vector<TERM> t2_args;
	bool is_unifiable = false;

	for (unsigned int i = 0; i != lit_subs.size(); i++) {
				t1_args.push_back(lit_subs[i].domain);
				t2_args.push_back(lit_subs[i].range);
	}
	for (unsigned int i = 0; i != yices_subs.size(); i++) {
				t1_args.push_back(yices_subs[i].domain);
				t2_args.push_back(yices_subs[i].range);
	}

	char *sym = strdup("f");	
	t1 = build_function_term(sym, t1_args);
	t2 = build_function_term(sym, t2_args); 
	free(sym);

	vector<SUB> mgu;
	is_unifiable = unifiable(t1,t2, mgu);

	free_term(t1);
	free_term(t2);

	for(unsigned int i = 0; i != mgu.size(); i++) {
		free_term(mgu[i].domain);
		free_term(mgu[i].range);
	}

	return is_unifiable;
}	

void apply_yices_mgu(TERM &t)
{ 
     //variable
   	if (t.is_var) {
		// find variable in yices_mgu and replace. 
		for (unsigned int i = 0; i != yices_mgu.size(); i++) {
			if (!yices_mgu[i].domain.is_var)
				continue;
			else if (strcmp(t.sym, yices_mgu[i].domain.sym) == 0) {
				free_term(t);
				t = new_term(yices_mgu[i].range);
				//t.is_var = yices_mgu[i].range.is_var;	
				//t.sym = yices_mgu[i].range.sym;
				//t.args = yices_mgu[i].range.args;
				break;
			}
		}	
     }
     //constant
     else if ((t.is_var == 0) && (t.args == NULL)) {
		return;
     }
     //function
     else {
          ARG *args = t.args;
          apply_yices_mgu(args->arg);

          args = args->next;
          while( args != NULL ) {
          	apply_yices_mgu(args->arg);
          	args = args->next;
          }
     }

     return;
}

/*
 * Yices returns equations of the form: f(f_arg x) = x and 
 * g(y) = f_arg x.  We need iterate through all of the terms
 * and substiture g(y) wherever we see f_arg x.
 *
 * TODO: There could be the case that the string 'arg' is
 * used as part of a term name in TPTP.  Fix our define-type
 * so that we are safe.
 */

void substitute_yices_args()
{

	TERM t1;
	TERM t2;
	string string_arg("arg");
	size_t found;

	for (unsigned int i = 0; i != yices_subs.size(); i++) {
		t1 = yices_subs[i].domain;
		t2 = yices_subs[i].range;

		/*
		 * Evidence shows that args definitions are usually in the domain
		 * though they may be in the range.
		 */

		string term_sym(t2.sym);
		found = term_sym.find(string_arg);

		if (found != string::npos) {
			TERM replace_me = t2;
			TERM replace_with = t1;

			for (unsigned int j = 0; j != yices_subs.size(); j++) {
				if (j != i) {
					replace_if_equal(replace_me, replace_with, yices_subs[j].domain);
					replace_if_equal(replace_me, replace_with, yices_subs[j].range);
				}
			}
			replace_if_equal(replace_me, replace_with, yices_subs[i].range);	
		}
	}
}
				


/*
 * Find the mgu for yices_subs.  Yices doesn't necessarily
 * give us the mgu. Return TRUE if assignments returned
 * by Yices are unifiable (they should very well be - thats
 * why we are using Yices after all), else return FALSE.
 */

bool set_yices_mgu()
{
	TERM t1;
	TERM t2;
	vector<TERM> t1_args;
	vector<TERM> t2_args;
	bool is_unifiable = false;

	substitute_yices_args();

	for (unsigned int i = 0; i != yices_subs.size(); i++) {
		t1_args.push_back(yices_subs[i].domain);
		t2_args.push_back(yices_subs[i].range);
	}

	char *sym = strdup("f");	
	t1 = build_function_term(sym, t1_args);
	t2 = build_function_term(sym, t2_args); 
	free(sym);

	is_unifiable = unifiable(t1,t2, yices_mgu);

	return is_unifiable;
}

bool comp_lits_unified()
{
	/*
	 * Substitute all variables in lit_subs[i] with those in yices_mgu 
	 * and see if domain and range are equal.  If so, we say that Yices
	 * assignments unify the literals's assignments (as opposed to 
	 * merely being 'unifiABLE'.)
	 */

	TERM domain;
	TERM range;
	
	for (unsigned int i = 0; i != lit_subs.size(); i++) {
		
		domain = new_term(lit_subs[i].domain);
		range = new_term(lit_subs[i].range);

		apply_yices_mgu(domain);
		apply_yices_mgu(range);

		bool terms_are_equal = equal(domain,range);

		free_term(domain);
		free_term(range);

		if (terms_are_equal == false) 
			return false;
	}

	return true;
}

int close_literal(char *lit)
{
	int i2, j2;
	sscanf(lit, "l%da%d", &i2, &j2);

	/*
	 * As we traverse the DAG we keep track of the path (lit_path) we are currently on
	 * and we keep track of all the sets of substitutions (lit_path_subs) used to unify 
	 * complementary literals on lit_path.
	 * 
	 * For each literal added to the end of lit_path (arg to close_literal()), we look 
	 * for a cycle.  That is, we look for the same literal appearing previously in lit_path.
	 *
	 * If while checking lit_path[i] we find a complementary literal then it MAY be used 
	 * to close the literal if we find a cycle.  If the substitutions are consistent with 
	 * yices_subs AND yices_subs unifies the substitutions then we
	 * consider the branch closed and backtrack.  Otherwise, we save in lit_path_subs the 
	 * set of substitutions.
	 *
	 * If while checking lit_path[i] we find the same literal (a cycle) AND lit_path_subs is
	 * empty then we assert the cycle does not exist.  Otherwise we assert that if the cycle 
	 * exists then one of the sets of substitutions must hold.
	 *
	 * If we do not find a cycle then Yices must have extended the literal so we find the 
	 * extension and continue traversing the path.
	 */

	assert_subs.clear();
	/*
	 * TODO: check for memory leak
	 */

	for (unsigned int i = 0; i < lit_path.size(); i++) {
		int i1, j1;
		sscanf(lit_path[i], "l%da%d", &i1, &j1);

		/*
		 * Check to see if lit is complementary to lit_path[i].
		 */

		lit_subs.clear();
       	if((cl_a[i1][j1].is_pos != cl_a[i2][j2].is_pos) && (unifiable(cl_a[i1][j1].atom, cl_a[i2][j2].atom, lit_subs))){

			/*
			 * Check if substitutions are consistent.  If not, then continue.
			 * If consistant and yices_subs is unifiable with lit_subs,
			 * then consider branch closed and backtrack, otherwise save subs and 
			 * continue looking for other complementary literals on this path.
			 */

			if (subs_consistent() == false) {
/*
 * Should we assert that the assignments for this unification if bad cycle exists.
 */
				continue;
			}
			else if (comp_lits_unified()) {
				lit_path.push_back(strdup(lit));	
				exp_queue.push_back(strdup("filler"));
				backtrack();
				return(0);
			}
			else {
				assert_subs.push_back(lit_subs);	
				continue;
			}
		}

		/*
		 * The literarals are not complementary or unifiable.  If they are not complementary
		 * they may be the same literal.  If they are the same, then we have an invalid cycle.
		 */

		if (strcmp(lit_path[i], lit) == 0){
					
			for(unsigned int j = 0; j < i; j++){
				char *front_exp = exp_queue.front();
				exp_queue.pop_front();
				free(front_exp);
			}

			return (exp_queue.size());
		}
	}

	/*
 	 * No cycle was found.  Get the expansion variable and
	 * traverse the tree.
	 */

	char prefix[32];
	char s1[32];
	char expansion[62];
	bool found_expansion = false;

	sprintf(prefix, "e%da%d", i2, j2);
	int len = strlen(prefix);

	for (unsigned int i=0; i < yices_vars.size(); i++) {
		sscanf(yices_vars[i], "%s %s", s1, expansion);
	
		if (strncmp(expansion, prefix, len) == 0){
			found_expansion = true;
			break;
		}
	}

	if (found_expansion == false) {
         	cout << "SZS status Error for " << theorem_name << 
			" can not close literal " << lit << endl;
		if (!verbose)
			remove_files_and_exit();
		else 
			exit(1);
	}

	lit_path.push_back(strdup(lit));	
	exp_queue.push_back(strdup(expansion));

	int cl, l;
	sscanf(expansion, "e%da%da%da%d", &i2, &j2, &cl, &l);

	if (push_lits_on_stack(cl, l) == 0) {
		backtrack();
	}
		
	return 0;
}

void init_data_structs()
{

}

void add_cycle_assertions()
{
     char yices_op[1024];

     sprintf(yices_op, "(assert (or");

	char *exp;
     while (!exp_queue.empty()) {
          sprintf(yices_op, "%s (not %s)", yices_op, exp_queue.front());
		exp = exp_queue.front();
          exp_queue.pop_front();
		free(exp);
     }

	for (unsigned int i = 0; i != assert_subs.size(); i++) {
		vector<SUB> cur_lit_sub = assert_subs[i];
		sprintf(yices_op, "%s (and ", yices_op);
		for (unsigned int j = 0; j != cur_lit_sub.size(); j++) {
			strcat(yices_op, "(= ");
			term2YicesDatatype(cur_lit_sub[j].domain, yices_op);
			strcat(yices_op, " ");
			term2YicesDatatype(cur_lit_sub[j].range, yices_op);
			strcat(yices_op, ")");
			free_term(cur_lit_sub[j].domain);
			free_term(cur_lit_sub[j].range);
		}
		strcat(yices_op, ")");
	}

     strcat(yices_op, "))");
     yicesl_read(ctx, yices_op);
	
}

void clean_memory_before_exit()
{

	for (unsigned int i= 0; i < yices_subs.size(); i++) {
		free_term(yices_subs[i].domain);
		free_term(yices_subs[i].range);
	}
	yices_subs.clear();

	for (unsigned int i= 0; i < yices_vars.size(); i++) {
		free(yices_vars[i]);
	}
	yices_vars.clear();

	while(!lit_stack.empty()) {
		char *lit = lit_stack.top();
		lit_stack.pop();
		free(lit);
	}

	while(!lit_path.empty()) {
		char *lit = lit_path.back();
		lit_path.pop_back();
		free(lit);
	}

	while(!exp_queue.empty()) {
		char *lit = exp_queue.back();
		exp_queue.pop_back();
		free(lit);
	}

	for (unsigned int i= 0; i < yices_mgu.size(); i++) {
		free_term(yices_mgu[i].domain);
		free_term(yices_mgu[i].range);
	}
	yices_mgu.clear();

}

bool found_invalid_cycles() 
{
	bool invalid_cycle = false;

	get_yices_subs_and_vars();

	set_yices_mgu();

	/*
	 * Print the clause that the proof begins with.  The clause is found by finding the first line 
	 * that begins with C# where # is an integer. Set n = # for future use.
	 */

	char s1[32];
	char s2[32];
	int found_a = 0;
	int n = 0;
	char c;

	for (unsigned int i=0; i < yices_vars.size(); i++) {
		sscanf(yices_vars[i], "%s %s", s1, s2);

		for (unsigned int i = 0; i < strlen(s2); i++)
			if (s2[i] == 'a')
				found_a = 1;

		if (s2[0] == 'c' && found_a == 0)
		{
			sscanf(s2, "%c%d", &c, &n);
			break;	
		}
	}

	init_data_structs();

	/*
	 * Push all the the true literals for the start clause n onto the stack.
	 */

	push_lits_on_stack(n, -1);

	/* 
	 * Process stack: pop a literal and determine if it was closed with a literal above
	 * it or if it is extended.
	 */

	while (!lit_stack.empty() && !invalid_cycle) {

		char *current_lit = lit_stack.top();
		lit_stack.pop();
	
		if (close_literal(current_lit) != 0) {
			add_cycle_assertions();
			invalid_cycle = true;
		}
	
		free(current_lit);
	}

	clean_memory_before_exit();

	return invalid_cycle;
}

/*--------------END OF FILE-------------------*/
