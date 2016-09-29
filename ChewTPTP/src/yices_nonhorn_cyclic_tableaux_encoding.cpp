#include <iostream>
#include <fstream>
#include <vector>
#include <map>
#include <string>

#include "stdio.h" 
#include "stdlib.h"
#include "unistd.h"
#include "assert.h"

#include "main.h"
#include "struct.h"
#include "encode_util.h"
#include "unification.h"

#include "yices_encoding.h"
#include "yicesl_c.h"

using namespace std;

/**************************************
 * Global variables defined in main.cpp
 **************************************/

extern LIT **cl_a;
extern int *num_lit;	
extern int cl_ct;	
extern yicesl_context ctx;
extern char theorem_name[];
 
/**************************************
 * Local global variables
 **************************************/

char yices_op[5024];

/******************************************
 * Output clauses like C_4 \/ C_5 \/ C_6.
 *
 * We print a single clause. 
 * Each literal in the clause represents a clause C
 * in S such that each literal in C is negative.
 *
 * Let i be a clause and let j be a literal in clause i.
 * For all i, if for all j, j is negative then output, Ci. 
 *
 ***************************************************/
void yices_non_horn_clauses1()
{
        /*****************************************************************
         * Here we define all of the possible clause and literal variables
         *****************************************************************/

	for (int i = 0 ; i < cl_ct ; i++)
	{
		sprintf (yices_op, "(define c%d::bool)",  i);
		yicesl_read(ctx, yices_op);

		for (int j = 0; j < num_lit[i]; j++) {
			sprintf (yices_op, "(define l%da%d::bool)", i, j);
			yicesl_read(ctx, yices_op);

			sprintf (yices_op, "(define c%da%d::bool)", i, j);
			yicesl_read(ctx, yices_op);
		}
	}
	 
     /*****************************************************************
	 * "bitmap" (0 or 1) of which clauses are negative.
      *****************************************************************/

	int neg_cl[cl_ct]; 
	int neg_cl_ct = 0;
	int paren_ct = 0;
	int neg_cl_one;
	int j = 0;

	for(j=0; j < cl_ct; j++)
		neg_cl[j] = 0;

	string str_c1("c");
	string str_c2;
	string str_c;
	LIT literal;
	bool B_all_negative = true;

	for (int i = 0 ; i < cl_ct ; i++)
	{
		B_all_negative = true;
		for (int j = 0; j < num_lit[i]; j++)
		{
			literal = cl_a[i][j];
			if(literal.is_pos == 1)
				B_all_negative = false;
		}

		if(B_all_negative)
		{
			str_c2 = int2string(i);
			str_c = str_c1 + str_c2;
			neg_cl[i] = 1;
			
		}
	}

        /*****************************************************************
	 * Now form the instruction for "(assert (or c1 (or c2 (or c3 ... ))))."
         *****************************************************************/

	sprintf(yices_op, "(assert");

	for(j = 0; j < cl_ct; j++) {
		if (neg_cl[j] == 1) {
			paren_ct++;
			neg_cl_ct++;
			if (neg_cl_ct == 1)
				neg_cl_one = j;	      
			else if (neg_cl_ct == 2) {
				sprintf(yices_op, "%s (or c%d \n", yices_op, neg_cl_one);	    
				neg_cl_ct--;
				neg_cl_one = j;
			}
		}
	}

	if (neg_cl_ct == 1) {
		sprintf(yices_op, "%s c%d", yices_op, neg_cl_one);	    	  
		j = 0;
		for (j = 0; j < paren_ct; j++)
			sprintf(yices_op, "%s)", yices_op);

		yicesl_read(ctx, yices_op);
	} 
	else {
		cout << "SZS status Satisfiable for " << theorem_name << ": no negative clauses" << endl;
		remove_files_and_exit();
	}
}

/*************************************************
 * ~C_i \/ Lij
 *
 * Let i be a clause and j be a literal in clause i.  
 * For all i and all j, output ~Ci \/ Lij.
 *
 * ~C_ij \/ L_ik where k != j
 *
 * Let i be a clause, j be a literal in clause i, and k be a literal in clause i.
 * For all i, for all j, for all k such that k != j, output ~Cij \/ Lik.
 *
 *************************************************/

void yices_non_horn_clauses2()
{
	string str_c;
	string str_c2;
	string str_l;

	for (int i = 0 ; i < cl_ct ; i++) {
		for (int j = 0; j < num_lit[i]; j++) {
			str_c2 = "c" + int2string(i);
			str_l = "l" + int2string(i) + "a" + int2string(j);

			sprintf(yices_op, "(assert (=> %s %s))", str_c2.c_str(), str_l.c_str());
			yicesl_read(ctx, yices_op);

			for (int k = 0; k < num_lit[i]; k++) {
				if(j != k) {
					str_c = "c" + int2string(i) + "a" + int2string(j);
					str_l = "l" + int2string(i) + "a" + int2string(k);

					sprintf(yices_op, "(assert (=> %s %s))", str_c.c_str(), str_l.c_str());
					yicesl_read(ctx, yices_op);
				}
			}
		}
	}
}

/***********************************************
 * ~L_31 \/ I_3120 \/ I_3140 \/ ...
 *
 * Let i be a clause, let j be a literal in i1. Let k be a clause and l be a literal in k.
 * For all i, for all j in i output ~Lij, and for all k such that i != k, 
 * if sign(j) != sign(l) and clause i and k are unifiable with literals j and l then 
 * output \/ Iijkl 
 *  
 * ~I_5120 \/ C_20
 *
 * Let i be a clause, let j be a literal in i. Let k be a clause and l be a literal in k.
 * For all i, for all j in i, for all k such that i != k, if sign(j) != sign(l) and 
 * clause i and k are unifiable with literals j and l then output
 * ~Iijkl \/ Ckl
 *
 * ~I_5120 \/ U_3
 *
 * Let i be a clause, let j be a literal in i. Let k be a clause and l be a literal in k.
 * For all i, for all j, for all k such that i != k, if sign(j) != sign(l) and 
 * clause i and k are unifiable with literals j and l then for each substitution m output 
 * ~Iijkl \/ Um 
 *
 **************************************/

void yices_non_horn_clauses3()					
{
	string str_c;
	string str_q;
	string str_l;
	string str_i;
	string str_u;
	string str_x1, str_x2;
	vector<string> clause1;
	vector<string> clause11;

	vector<SUB> sub1;
	bool is_unifiable;

	for(int i = 0; i < cl_ct; i++) {
		for(int j = 0; j < num_lit[i]; j++) {
			for(int k = 0; k < cl_ct; k++) {
				for(int l = 0; l < num_lit[k]; l++) {
					sprintf(yices_op, "(define e%da%da%da%d::bool)", i, j, k, l);
					yicesl_read(ctx, yices_op);
				}
			}
		}
	}

	for (int i1 = 0 ; i1 < cl_ct ; i1++) {
		for (int j1 = 0; j1 < num_lit[i1]; j1++) {
			clause1.clear();
	
			str_l = "l" + int2string(i1) + "a" + int2string(j1);	
			clause1.push_back(str_l);

			for (int i2 = 0 ; i2 < cl_ct ; i2++) {

				if(i1 != i2) {

					/*******************************************
					* for all positive literals in that clause
					*******************************************/
					for (int j2 = 0; j2 < num_lit[i2]; j2++) {

						if(cl_a[i1][j1].is_pos != cl_a[i2][j2].is_pos) {
							sub1.clear();
							is_unifiable = unifiable(cl_a[i1][j1].atom, cl_a[i2][j2].atom, sub1);
/*
 * TODO: free sub1 memory
 */
							if(is_unifiable) {

								str_i = "e" + int2string(i1) + "a" + int2string(j1) + "a" + int2string(i2) + "a" + int2string(j2);
								clause1.push_back(str_i);

								str_i = "e" + int2string(i1) + "a" + int2string(j1) + "a" + int2string(i2) + "a" + int2string(j2);
								str_c = "c" + int2string(i2) + "a" + int2string(j2);
	
								sprintf(yices_op, "(assert (=> %s %s))", str_i.c_str(), str_c.c_str());
								yicesl_read(ctx, yices_op);

								sprintf(yices_op, "(assert (=> %s (= ", str_i.c_str());
								term2YicesDatatype(cl_a[i1][j1].atom, yices_op);
								strcat(yices_op, " ");
								term2YicesDatatype(cl_a[i2][j2].atom, yices_op);
								strcat(yices_op, ")))");
								yicesl_read(ctx, yices_op);

							}
						}
					}
				}	
			}

			/**********************************
			* Print literal implies extenstions 
			***********************************/

			if (clause1.size() == 0) {
				cout << "Error: Clause1 should contain at least lxay." << endl;
				return; 
			}
			else if(clause1.size() == 1) {
				sprintf(yices_op, "(assert (not %s))", clause1[0].c_str());
				yicesl_read(ctx, yices_op);
			}
			else if(clause1.size() == 2) {
				sprintf(yices_op, "(assert (=> %s %s))", clause1[0].c_str(), clause1[1].c_str());
				yicesl_read(ctx, yices_op);
			}
			else {
				sprintf(yices_op, "(assert (=> %s (or", clause1[0].c_str());
				for(unsigned int j = 1; j < clause1.size(); j++)
					sprintf(yices_op, "%s %s", yices_op, clause1[j].c_str());
				sprintf(yices_op, "%s)))", yices_op);
				yicesl_read(ctx, yices_op);
			}
		}
	}
}

void yices_non_horn_encoding()
{
	assert_term_type();
	yices_non_horn_clauses1();
	yices_non_horn_clauses2();
	yices_non_horn_clauses3();

}

/*--------------END OF FILE-------------------*/
