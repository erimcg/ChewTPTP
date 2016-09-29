#ifndef _STRUCT_H_
#define _STRUCT_H_

#include <vector>
#include <string>

using namespace std;


struct arg_s;

typedef struct term_s {
        int is_var;
        char* sym;
	   int num_args;
        struct arg_s *args;
}TERM;

typedef struct arg_s {
        TERM arg;
        struct arg_s *next;
}ARG;

typedef struct lit_s {
        TERM atom;
        int is_pos;
}LIT;

typedef struct sub_s {
 	TERM domain;
	TERM range;
}SUB;


TERM build_function_term(char*, vector<TERM>);
TERM new_term(TERM);
ARG* new_arg_p(ARG*);
void free_term(TERM);
void free_arg_p(ARG*);

void print_lit_struct(LIT);
void print_term_struct(TERM);
void print_arg_struct(ARG);

void print_lit(LIT);
void print_term(TERM);
void print_arg(ARG);
void print_arg_p(ARG*);

char* term2string(TERM, char *);
char* arg2string(TERM, char*);
string sub_to_string(SUB&);
string term_to_string(TERM&);

bool equal(TERM, TERM);

#endif

