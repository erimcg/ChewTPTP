#ifndef _UNIFICATION_H_
#define _UNIFICATION_H_

#include <vector>
#include "struct.h"

bool occurs(TERM needle, TERM haystack);
void replace_if_equal(const TERM &to_replace, const TERM &replace_with, TERM &replace_in);
void replace(const TERM &to_replace, const TERM &replace_with, TERM &replace_in);
void replace_terms(TERM to_replace, TERM replace_with, vector <SUB> &subs);
bool unifiable(TERM t1, TERM t2, vector <SUB> &mgu /*Most General Unifier*/);
bool occurs_check(char*);

#endif
