#pragma once
#include "SolverHandle.h"
#include "RebuilderContext.h"

namespace Minisat {

typedef enum {//used in proof reconstruction when opt_blm_rebuild_proof is used
	Either=0,Left=1, Right=2, Both=3,
} ParentUsed;

//struct RebuilderContext {
//
//
//	//vec<Uid>& allPoEC;
//

//
//};

class ProofRebuilder{
	//A handle for the underlaying solver used to create the resolution graph.
	SolverHandle* sh;
	//A DB containing the current state of the proof rebuilding process.
	RebuilderContext* ctx;
	bool memberOfClause(Uid u, const Lit& l);
public:
	ProofRebuilder(SolverHandle* sh,RebuilderContext* ctx);
	void				RebuildProof(Lit startingConflLit, vec<Uid>& allPoEC);
	template<class T>
	Uid					proveBackboneLiteral(const Uid currUid, const T& initParents,const Lit& BL);
	template<class T>
	void				recordClausePivots(Uid uid, T& parents);
	LitSet&				recordClauseLits(Uid newUid);
	void				copyClause(Uid clauseFrom, LitSet& clauseTo);
	ParentUsed			findParentsUsed(const LitSet& leftLits, const Uid rightParentUid, const Lit& piv, const Lit& BL);
	template<class S, class C>
	Lit					resolveWithOverwrite(S& set, C& clause);
	class ResolutionException : public std::exception {
	public:
		ResolutionException(const char* msg) : std::exception(msg) {}
	};
};
}

