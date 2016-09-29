#include <cassert>
#include <vector>
#include <iostream>
#include <fstream>

#include "struct.h"
#include "unification.h"

/*
 * occurs() returns true if the variable s occurs in term t otherwise returns false.
 * s is assumed to be a variable and t is any term.
 */

bool occurs(TERM s, TERM t)
{
	ARG *search_in = t.args;

	if(search_in == NULL) {
		if(strcmp(s.sym, t.sym) != 0) {
			return false;
		}
		else {
			return true;
		}
	}
	
	while(search_in != NULL) {
		if(occurs(s,search_in->arg)) {
			return true;
		}
		search_in = search_in->next; 
	}

	return false;
}

void replace_if_equal(const TERM &to_replace, const TERM &replace_with, TERM &replace_in)
{
	bool found_equal_terms = false;

	if(equal(to_replace, replace_in)) {
		found_equal_terms = true;
		free_term(replace_in);
		replace_in = new_term(replace_with);
	}

	ARG * replace_me = replace_in.args;

	while(replace_me != NULL) {
		replace_if_equal(to_replace, replace_with, replace_me->arg);
		replace_me = replace_me->next; 
	}
}

void replace(const TERM &to_replace, const TERM &replace_with, TERM &replace_in)
{
	if(strcmp(to_replace.sym, replace_in.sym) == 0) {
		free_term(replace_in);
		replace_in = new_term(replace_with);
	}

	ARG * replace_me = replace_in.args;

	while(replace_me != NULL) {
		replace(to_replace, replace_with, replace_me->arg);
		replace_me = replace_me->next; 
	}
}

void replace_terms(TERM to_replace, TERM replace_with, vector <SUB> &subs)
{
	for(vector<SUB>::iterator head = subs.begin(); head != subs.end(); head++) {
		replace(to_replace, replace_with, (*head).domain);
		replace(to_replace, replace_with, (*head).range);
	}
}

bool unifiable(TERM t1, TERM t2, vector <SUB> &mgu)
{
	vector <SUB> U;
	SUB E;
	E.domain = new_term(t1);
	E.range = new_term(t2);
	U.push_back(E);

	while(!U.empty()) {
		vector<SUB>::iterator head = U.begin();
		TERM s = (*head).domain;
		TERM t = (*head).range;

		/*
		 * If the domain s is a term of the form f(s1,...,sn) then we either 
		 * 	a) swap s and t IF t is a variable or
		 *	b) return false IF t is a term with a different function symbol else 
		 *	c) check the unifiability of the arguments of s and t
		 */
			
		if( s.is_var == 0 ) {
			if( t.is_var == 1 ) {
				U.erase(head);
				E.domain = t;
				E.range = s;
				U.push_back(E);
			}
			else { 
				assert(s.sym != NULL && t.sym != NULL);

				if(strcmp(s.sym, t.sym) != 0) {
					return false;
				}
				else {
					U.erase(head);

					ARG *si = s.args;
					ARG *ti = t.args;
	  
					while(si != NULL && ti != NULL) {
						E.domain = new_term((*si).arg);
						E.range = new_term((*ti).arg);
						U.push_back(E);
						si = si->next;
						ti = ti->next;
					}

					free_term(s);
					free_term(t); 
				} 
			}
		}

		/*
		 * If the domain s is a variable then we
		 * 	a) process the next pair of terms IF t is the same variable or
		 *	b) return false IF s occurs in t or
		 *	c) replace all instances of s in U and mgu with t AND add s = t to mgu.
		 */

		else {

			if(strcmp(s.sym,t.sym) == 0) {
				U.erase(head);
				free_term(s);
				free_term(t);
			}
			else if(occurs(s,t)) {
				return false;
			}
			else {
				U.erase(head);
				replace_terms(s, t, U);
				replace_terms(s, t, mgu);
				
				E.domain = s;
				E.range = t;
				mgu.push_back(E);
			}
		}
	} 
	return true;
}

/* END OF FILE */
