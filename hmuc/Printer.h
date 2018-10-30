#pragma once
#include "core\SolverTypes.h"
#include "core\Dimacs.h"
#include <iostream>
#include <fstream>
using namespace std;
namespace Minisat {

	
	template<typename S>
	static void printfSet(const S& s, char *msg) {
		printf("%s (", msg);
		for (auto& e : s) {
			printf("%d ", e);
		}
		printf(")\n");
	}
	template<typename T>
	static void printfVec(const T& v, const char *msg) {
		printf("%s (", msg);
		for (int i = 0; i < v.size(); ++i) {
			printf("%d ", v[i]);
		}
		printf(")\n");
	}
	static void printClause(const Clause& c, std::string text, ostream& out = std::cout)
	{
		out << text << std::endl;
		for (int i = 0; i < c.size(); i++)
			out << (todimacsLit(c[i])) << " ";
		out << "0" << std::endl;
	}
	static void printClause(const LitSet& c, std::string text,ostream& out = std::cout)
	{
		out << text << std::endl;
		for (auto& l : c)
			out << (todimacsLit(l)) << " ";
		out << "0" << std::endl;
	}
	static void printClause(const vec<Lit>& v, std::string text, ostream& out = std::cout)
	{
		out << text << std::endl;
		for (int i = 0; i < v.size(); i++)
			out << (todimacsLit(v[i])) << " ";
		out << "0" << std::endl;
	}
}