#include <map>
#include <vector>
#include <deque>
#include <string> 
#include <iostream>
#include <fstream>

#include <sys/stat.h>
#include <stdio.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <getopt.h>
#include <string.h>
#include <sys/time.h>
#include <fcntl.h>
#include <time.h>
#include <signal.h> 

#include "main.h"
#include "struct.h"
#include "unification.h"
#include "encode_util.h"
#include "yices_nonhorn_cyclic_tableaux_encoding.h"
#include "yices_cycle_check.h"

#include "yicesl_c.h"

extern FILE *yyin;
extern FILE *yyout;
//extern int yydebug;

extern "C" 
{
  int yyparse();
}

#define BUFSIZE			1024
#define VERSION_NUMBER 		"1.0.0"

#define YYOUT_ERROR_FILE		"/tmp/yyout.errors"

using namespace std;

/*******************************************************
 * Global data structures used in multiple source files. 
 *******************************************************/

LIT **cl_a;
int *num_lit;
int cl_ct = 0;
yicesl_context ctx; 
vector<SUB> sub_set;
vector<string> V_s;
map<string, int> all_subs;
map<string, int> all_symbols;

int verbose;
char theorem_file[128];					
char theorem_name[128];					
char yices_log_file[128]; 					
char output_file[128];

/*************************************************
 * Global variables used in this source file only.
 ************************************************/

vector<TERM> term_symbols;

/************
 * Help menu
 ************/

void print_help(char *program_name) {
	cout << program_name << "[OPTION]... FILE" << endl;
	cout << endl;
	cout << "  -h,    \tproblem contains only Horn clauses" << endl;	 
	cout << "  -i,    \tgenerate specified number of instances of problem (default = 1)" << endl;
	cout << "  -r,    \tuse rigid variables if instances > 1" << endl;
	cout << "  -v,    \tprint verbose messaging" << endl;
	cout << "  --help \tdisplay this help and exit" << endl;
	cout << endl;
	cout << "  Report bugs to mcgregre@clarkson.edu" << endl;
	exit(0);
} 

/****************************************************
 * Signal handler
 ****************************************************/

static void timout_interupt_handler(int signo)
{
	cout << "SZS status TimeOut for " << theorem_name << endl;
	exit(0);
}

static void segv_interupt_handler(int signo)
{
	cout << "SZS status Error for " << theorem_name << ": bounds exceeded" << endl;
	exit(1);
}

/************************************
 * Gracefully exit program 
 ************************************/

void remove_files_and_exit()
{
	remove(output_file);
	remove(yices_log_file);

	exit(0);
}

/***********************************************************************
 * count_number_of_clauses() opens up the theorem file and counts the
 * number of clauses.  This is used in main() to determine how much
 * memory to allocate.
 ***********************************************************************/ 

int count_number_of_clauses()
{
	char line[BUFSIZE];
	int n = 0;

	FILE *fp = fopen(theorem_file, "r");

	if (fp == NULL){
		printf("SZS status Error for %s: can not open %s for reading\n", theorem_name, theorem_file);
		remove_files_and_exit();
	}

	while (fgets(line, BUFSIZE, fp) != NULL)
		if (strncmp(line, "cnf", 3) == 0)
			n++;

	fclose(fp);
	return n;
}

/**********************************************************************
 * realloc_data_structs() reallocates the data structures which holds 
 * the problem to allow one additional set of fresh clauses.  The
 * clauses are added in main().
 **********************************************************************/
		
int realloc_data_structs(int orig_num_clauses, int num_copies) {

	cl_ct = orig_num_clauses * num_copies;
	LIT **tmp = new LIT*[cl_ct];

	for (int i = 0; i < cl_ct; i++)
		tmp[i] = new LIT[MAXLITS];
	
	int old_cl_ct = orig_num_clauses * (num_copies - 1);
		
	for (int i = 0; i < old_cl_ct; i++) {
		for (int j = 0; j < MAXLITS; j++) {
			tmp[i][j].atom.sym = cl_a[i][j].atom.sym;
			tmp[i][j].atom.args = cl_a[i][j].atom.args;
			tmp[i][j].atom.is_var = cl_a[i][j].atom.is_var;
			tmp[i][j].is_pos = cl_a[i][j].is_pos;
		}
	}

	for (int i = 0; i < old_cl_ct; i++) {
		free(cl_a[i]);
	}

	free(cl_a);
	cl_a = tmp;

	int *tmp_num_lit = new int[cl_ct];

 	for (int i = 0; i < old_cl_ct; i++)
		tmp_num_lit[i] = num_lit[i];

	free(num_lit);
	num_lit = tmp_num_lit;

	return cl_ct;	
}
 
/**********************************************************************
 * realloc_data_structs_and_copy() reallocates the data structures which 
 * holds the problem to allow one additional set of duplicate clauses.  
 * The clauses are copied in this function as well.
 **********************************************************************/

int realloc_data_structs_and_copy(int orig_num_clauses, int num_copies) 
{
	cl_ct = orig_num_clauses * num_copies;
	LIT **tmp = new LIT*[cl_ct];

	for (int i = 0; i < cl_ct; i++)
		tmp[i] = new LIT[MAXLITS];
	
	int old_cl_ct = orig_num_clauses * (num_copies - 1);
		
	for (int i = 0; i < old_cl_ct; i++) {
		for (int j = 0; j < MAXLITS; j++) {
			tmp[i][j].atom.sym = cl_a[i][j].atom.sym;
			tmp[i][j].atom.args = cl_a[i][j].atom.args;
			tmp[i][j].atom.is_var = cl_a[i][j].atom.is_var;
			tmp[i][j].is_pos = cl_a[i][j].is_pos;

			tmp[old_cl_ct + i][j].atom.sym = cl_a[i][j].atom.sym;
			tmp[old_cl_ct + i][j].atom.args = cl_a[i][j].atom.args;
			tmp[old_cl_ct + i][j].atom.is_var = cl_a[i][j].atom.is_var;
			tmp[old_cl_ct + i][j].is_pos = cl_a[i][j].is_pos;
		}
	}

	for (int i = 0; i < old_cl_ct; i++) {
		free(cl_a[i]);
	}

	free(cl_a);
	cl_a = tmp;

	int *tmp_num_lit = new int[cl_ct];

 	for (int i = 0; i < old_cl_ct; i++) {
		tmp_num_lit[i] = num_lit[i];
		tmp_num_lit[old_cl_ct + i] = num_lit[i];
	}

	free(num_lit);
	num_lit = tmp_num_lit;

	return cl_ct;
}

/**********************************************************
 * print_clauses() prints the problem as stored in memory.
 *********************************************************/

void print_clauses()
{
     int cl = 0;
     int lit = 0;

     for (cl = 0; cl < cl_ct; cl++)
     {
          for (lit = 0; lit < num_lit[cl]; lit++)
          {
               print_lit_struct(cl_a[cl][lit]);
               if (lit < num_lit[cl] - 1)
                    printf("|");
          }
          printf("\n");
     }
     printf("\n");
     return;
}

/****************************************************
 * Parse the file name from the path.
 * Both theorem_file and theorem_name are global vars
 *****************************************************/
void set_file_name()
{
     char *last_tok = NULL;
     struct stat buf;

	memset(&theorem_name, '\0', sizeof(theorem_name));

     if (theorem_file == NULL)
          return;

     if (stat(theorem_file, &buf) < 0)
          return;

     if (!S_ISREG(buf.st_mode))
          return;

     char *tmp = strdup(theorem_file);
     char *tok = strtok(tmp, "/");

     if (tok == NULL) {
		strcpy(theorem_name, tmp);
		free(tmp);
          return;
	}
     else
          last_tok = tok;

     while ((tok = strtok(NULL, "/")) != NULL)
          last_tok = tok;

	strcpy(theorem_name, last_tok);
	free(tmp);
     return;
}

void verify_smt_results()
{
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
    
     string str;
     if (!yices_solution_stream.eof()) {
          getline(yices_solution_stream, str);

		if (str.compare("sat") != 0) {
			cout << "SZS status Error for " << theorem_name <<
               	": SMT reports error - " << str << endl;

          	if (!verbose)
               	remove_files_and_exit();
			else
				exit(1);
		}
     }

	yices_solution_stream.close();
}

int main (int argc, char *argv[])
{
	//yydebug = 1;
	verbose = 0;							/* -v print verbose messages 	*/
	int rflag = 0;							/* -r rigid variables 		*/ 
	int num_instances = INT_MAX;				/* set by -i flag 		*/

	
	int c;								/* option variable 		*/
	opterr = 0;							/* getopt error 		*/

	/************************************************
	 * Make sure we can intercept SIGALRM and SIGXCPU
	 ************************************************/

	if (signal(SIGXCPU, timout_interupt_handler) == SIG_ERR) {
		cout << "SZS status Error: SIGXCPU not catchable" << endl;
		exit(1);
	}
	
	if (signal(SIGALRM, timout_interupt_handler) == SIG_ERR) {
		cout << "SZS status Error: SIGALRM not catchable" << endl;
		exit(1);
	}

	if (signal(SIGSEGV, segv_interupt_handler) == SIG_ERR) {
		cout << "SZS status Error: SIGSEGV not catchable" << endl;
		exit(1);
	}

	/************************ 
	 * Parse the command line 
	 ************************/

	if (argc == 1) {
		cout << "SZS status InputError: too few arguments" << endl;
		exit(1);
	}

	while (1) {
		static struct option long_options[] = {	
			{"help", no_argument, 0, 0},
			{0,0,0,0}
		};

		int option_index = 0;

		c = getopt_long(argc, argv, "rvi:", long_options, &option_index);

		if (c == -1)
			break;
	
		switch(c) {
			case 0:
				print_help(argv[0]);
				break;
			case 'r':
				rflag = 1;
				break;
			case 'v':
				verbose = 1;
				break;
			case 'i':
				num_instances = atoi(optarg);
				break;
			case '?':
				if (isprint(optopt))
					printf("SZS status InputError: unknown option '-%c'.\n", optopt);
				else
					printf("SZS status InputError: unknown option character '\\x%x'.\n", optopt);
				return 1;
			default:
				abort();
		}
	}

	if (verbose) 
		printf("Chewtptp version %s\n", VERSION_NUMBER);

	/*********************** 
	 * Get theorem file name 
	 ***********************/

	if (optind == argc) {
		cout << "SZS status InputError: too few arguements" << endl;
		return 1;
	}		

	strcpy(theorem_file, argv[optind]);
	
	set_file_name();

	if (strlen(theorem_name) == 0) {
		cout << "SZS status InputError: invalid file name" << endl;
		return 1;
	}

	/****************
	 * Set file names
	 ****************/

	sprintf(yices_log_file, "/tmp/%d-%s.yices_in", getpid(), theorem_name);
	sprintf(output_file, "/tmp/%d-%s.yices_out", getpid(), theorem_name);

	if (verbose) {
		cout << "Theorem File: " << theorem_file << endl;
		cout << "Yices Log File: " << yices_log_file << endl;
		cout << "Yices Output File: " << output_file << endl;
	}

	/*************************************************
	 * Inform user about the options that were chosen
	 *************************************************/

	if (verbose) {
		printf("Assuming problem is non-Horn\n");

		printf("Generating %d instance(s) of problem\n", num_instances);

		if (rflag && num_instances > 1)
			printf("Using identical variables when generating duplicate clauses\n");
		else if (num_instances > 1)
			printf("Using fresh variables in when generating duplicate clauses\n");
	}

	/*******************************************************
	 * Count the number of clauses so we can allocate memory
	 *******************************************************/

	int orig_num_clauses = count_number_of_clauses();
	cl_ct = orig_num_clauses;

	if (verbose)
		printf("%d clauses in %s\n", orig_num_clauses, theorem_name);

	/****************************
	 * Allocate memory for parser
	 ****************************/

	cl_a = new LIT*[cl_ct];

	for (int i = 0; i < cl_ct; i++)
		cl_a[i] = new LIT[MAXLITS];

	num_lit = new int[cl_ct];

	/************************
	 * Parse the theorem file 
	 ************************/

	if ((yyin = fopen(theorem_file, "r")) == NULL)
	{
		cout << "SZS status Error for " << theorem_name << " : can not open theorem file" << endl;
		return 1;
	}

	if ((yyout = fopen(YYOUT_ERROR_FILE, "w")) == NULL)
	{
		cout << "SZS status Error for " << theorem_name << " : can not open " << YYOUT_ERROR_FILE << endl;
		fclose(yyin);
		return 1;
	}

	if (yyparse() != 0) {
		cout << "SZS status SyntaxError for " << theorem_name << endl;
		fclose(yyin);
		fclose(yyout);
		remove(YYOUT_ERROR_FILE);
		return 1;
	}

	fclose(yyin);
	fclose(yyout);
	remove(YYOUT_ERROR_FILE);

	for (int i = 1; i <= num_instances; i++) 
	{
		/*************************************************************************
 		 * If additional instance of clauses is needed, generate another instance
		 * of each of the clauses.
		 *************************************************************************/

		if (verbose) 
			printf("Generating Instance No. %d Of Clauses\n", i);

		if(i > 1) {
			if (rflag) {
				cl_ct = realloc_data_structs_and_copy(orig_num_clauses, i);

			} else {	
				cl_ct = realloc_data_structs(orig_num_clauses, i);
			
				if ((yyin = fopen(theorem_file, "r")) == NULL) {
					cout << "SZS status for " << theorem_name << " : can not open theorem file" << endl;
					return 1;
				}

				if ((yyout = fopen(YYOUT_ERROR_FILE, "a")) == NULL) {
					cout << "SZS status for " << theorem_name << " : can not open " << YYOUT_ERROR_FILE << endl;
					fclose(yyin);
					return 1;	
				}

				if (yyparse() != 0) {
					cout << "SZS status SyntaxError for " << theorem_name << endl;
					fclose(yyin);
					fclose(yyout);
					remove(YYOUT_ERROR_FILE);
					return 1;
				}

				fclose(yyin);
				fclose(yyout);
				remove(YYOUT_ERROR_FILE);
			}
		}

		if (verbose)
			print_clauses();
		
		/*************************
		 * Set up Yices SMT solver
		 *************************/
			
		yicesl_enable_log_file (yices_log_file);
		yicesl_enable_type_checker(1);
		yicesl_set_output_file(output_file);
		ctx = yicesl_mk_context();

		char yices_op[36];
		sprintf(yices_op, "%s", "(set-evidence! true)");
  		yicesl_read(ctx, yices_op);

		/****************************
		 * Generate Tableaux encoding
		 ****************************/

		if (verbose)
			cout << "Generating Encoding ..." << endl;

		yices_non_horn_encoding();

		while (true) {

			/*************************************************** 
			 * Check if Yices reports consistant or inconsistant
			 ***************************************************/

			if (verbose)
				cout << "Processing Yices Context ..." << endl;

			remove(output_file);
			yicesl_set_output_file(output_file);

			sprintf(yices_op, "%s", "(check)");
  			yicesl_read(ctx, yices_op);

			if(!yicesl_inconsistent(ctx)) {

				/************************************************
				 * Check that Yices returned 'sat' in its output.
				 ************************************************/
	
				verify_smt_results();

				/*****************************************************
				 * Yices reports consistant: Check for invalid cycles.
				 * If invalid cycles are found, make assertions to 
				 * avoid them.
				 *****************************************************/

				if (verbose) {
					cout << "Yices Reports Consistent" << endl;
					cout << "Checking Cycles ..." << endl;
				}

				if (found_invalid_cycles() == true) {

					/******************************************************* 
					 * Bad cycles were found.  Assertions were made in
					 * found_invalid_cycles().  Re-check Yices consistentcy.
					 *******************************************************/

					if (verbose)
						cout << "Bad Cycle Found - Assertions Made" << endl;

					continue;
				}
				else {

					/**************************
					 * Problem is unsatisfiable
					 **************************/

					if (verbose)
						cout << "No Bad Cycles Found" << endl;

					cout << "SZS status Unsatisfiable for " << theorem_name << 
						": num instances = " << i << endl;
	
					if (!verbose)
						remove_files_and_exit();

					return(0);
				} 
			}
			else {

				/******************************************************** 
				 * Yices reports inconsistant: May need another instance
				 * of the problem clauses. Break out of Yices while loop.
				 *
				 * NOTE: We can not yet determine satisfiability - only
				 * unsatisfiability.
				 ********************************************************/

				if (verbose)
					cout << "Yices Reports Inconsistent" << endl;

				break;
			}
		}
	}

	/********************************************************************************
	 * We have instantiated 'num_instances' of clauses and have not found a solution.
	 ********************************************************************************/
	
	cout << "SZS status GaveUp for " << theorem_name << endl;
	
	if (!verbose)
		remove_files_and_exit();

	return 0;
}

/*--------------END OF FILE-------------------*/
