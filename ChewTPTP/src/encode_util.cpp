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

using namespace std;

/**************************************
 * Global variables defined in main.cpp
 **************************************/

extern map<string,  int> all_subs;
extern vector<SUB> sub_set;

extern map<string, int> all_symbols;
extern vector<string> V_s;

bool get_num(SUB &substitution, int &num)
/*
 * Given a substitution, we convert it to a string and search for it
 * in all_subs.  If found, we set num to the integer mapped to the string
 * and return true, otherwise we add it to all_subs and sub_set and return 
 * false.
 */
{
	string sub_str;

	sub_str = sub_to_string(substitution);

	if(all_subs.find(sub_str) != all_subs.end()) {
		num = all_subs[sub_str];
		return true;
	}
	else {
		all_subs[sub_str] = all_subs.size()-1;
		num = all_subs[sub_str];
		sub_set.push_back(substitution);

		assert(sub_set.size() == all_subs.size());
		return false;
	}
}

string int2string(int number)
/*
 * Return the string representation of the input number.
 */
{
	char tmp[128];
	sprintf(tmp,"%d", number);
	return string(tmp, 0, strlen(tmp));
}

int string2number(string str)
/*
 * Given a string (str) like I_123, we map the string to an integer in all_symbols.
 * This functions returns the interger mapped to the input string in all_symbols.
 * If the string is not present in all_symbols, we add the pair (string, n) where
 * n equals the size of all_symbols and we add the string to V_s.
 */
{
	if(all_symbols.find(str) != all_symbols.end())
	{
		return all_symbols[str];
	}
	else
	{
		all_symbols[str] = all_symbols.size();
		V_s.push_back(str);
		return all_symbols[str];
	}
}

/*--------------END OF FILE-------------------*/
