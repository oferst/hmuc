#pragma once
#include "core\SolverTypes.h"
#include "core\Dimacs.h"
namespace Minisat {

	
	template<typename S>
	static void printfSet(S& s, char *msg) {
		//if (v == NULL) printf("NULL\n");
		printf("%s (", msg);
		for (auto& e : s) {
			printf("%d ", e);
		}
		printf(")\n");
	}
	template<typename T>
	static void printfVec(T& v, char *msg) {
		//if (v == NULL) printf("NULL\n");
		printf("%s (", msg);
		for (int i = 0; i < v.size(); ++i) {
			printf("%d ", v[i]);
		}
		printf(")\n");
	}
	static void printClause(const Clause& c, std::string text)
	{
		std::cout << text << std::endl;
		for (int i = 0; i < c.size(); i++)
			std::cout << (todimacsLit(c[i])) << " ";
		std::cout << "0" << std::endl;
	}
	static void printClause(const LitSet& c, std::string text)
	{
		std::cout << text << std::endl;
		for (auto& l : c)
			std::cout << (todimacsLit(l)) << " ";
		std::cout << "0" << std::endl;
	}
	static void printClause(const vec<Lit>& v, std::string text)
	{
		std::cout << text << std::endl;
		for (int i = 0; i < v.size(); i++)
			std::cout << (todimacsLit(v[i])) << " ";
		std::cout << "0" << std::endl;
	}
}