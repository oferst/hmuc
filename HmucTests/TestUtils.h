#pragma once
#include "ProofRebuilder.h"
#include "../hmuc/utils/ParseUtils.h"
namespace Minisat {

	//Convert an int (that should be parse from a literal in 
	//dimacs format) into a literal. Will not be able to parse the 
	//int 0, the resulting Lit will be an Undefined literal.
	Lit intToLit(int n) {
		assert(n != 0);
		if (n == 0) return mkLit(Var(var_Undef));
		int var = abs(n) - 1;
		return (n > 0) ? mkLit(var) : ~mkLit(var);
	}
	//Parse a literal given in string dimacs format into a Lit object.
	Lit strToLit(const std::string& s) {
		return intToLit(atoi(s.c_str()));
	}

	//Print clause in dimacs format.
	template <class T>
	void printClause(T& v, std::string text = "") {
		std::cout << text << std::endl;
		for (auto l : v)
			std::cout << (toDimacsLit(l)) << " ";
		std::cout << "0" << std::endl;
	}
	//std::regex re = std::regex{ R"([\s,;]+)" } will split (the std::string s) on space, comma and ;
	std::vector<std::string> splitByRegex(const std::string& s, std::regex re = std::regex{ R"([\s,;]+)" }, int numMatches = -1) {
		return std::vector<std::string>{ std::sregex_token_iterator{ s.begin(), s.end(), re, numMatches }, {}};
	}
}

