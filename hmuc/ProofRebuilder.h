#pragma once
#include "SolverHandle.h"
#include "RebuilderContext.h"

namespace Minisat {

typedef enum {//used in proof reconstruction when opt_blm_rebuild_proof is used
	Left, Right, Both, Either
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

public:
	ProofRebuilder(SolverHandle* sh,RebuilderContext* ctx);
	void RebuildProof(Lit startingConflLit, vec<Uid>& allPoEC);
	template<class T>
	Uid BackwardsTraversal(const Uid currUid, const T& initParents,const Lit& BL);
	LitSet& extractClauseLits(Uid newUid);
	template<class T>
	void addClausePivots(Uid uid, T& parents);
	void copyClause(Uid clauseFrom, LitSet& clauseTo);

	ParentUsed findParentsUsed(LitSet& leftLits, uint32_t rightParentUid, Lit piv);
	template<class S, class C>
	Lit resolve(S& set, C& clause);
};
}

