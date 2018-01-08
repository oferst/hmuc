#pragma once
#include "SolverHandle.h"
#include "RebuilderContext.h"

namespace Minisat {

typedef enum {//used in proof reconstruction when opt_blm_rebuild_proof is used
	Either=0,Left=1, Right=2, Both=3,
} ParentUsed;

struct ReconstructionResult {
	LitSet newClause;
	vec<Uid> actualParentsUsed;
	vec<Uid> actualIcParentsUsed;
	vec<Uid> actualRemParentsUsed;
	bool isIc;
};


class ProofRebuilder{
	//A handle for the underlaying solver used to create the resolution graph.
	SolverHandle* sh;
	//A DB containing the current state of the proof rebuilding process.
	RebuilderContext* ctx;
	bool memberOfClause(Uid u, const Lit& l);
	void clearCandidateParents(ReconstructionResult& reconRes);
	void addCandidateParent(Uid uid, bool isIc, ReconstructionResult& reconRes);
public:
	ProofRebuilder(SolverHandle* sh,RebuilderContext* ctx);
	template<class T>
	void					backwardsTraversal(const Uid currUid,
										const T& parents, 
										const Lit& BL,
										vec<Lit>& currPivots,
										std::list<Uid>& newParentsCandidates);

	void				RebuildProof(Lit startingConflLit, vec<Uid>& allPoEC);
	template<class T>
	Uid					proveBackboneLiteral(const Uid currUid, const T& initParents,const Lit& BL);
	template<class T>
	void				recordClausePivots(Uid uid, T& parents);
	LitSet&				recordClause(Uid newUid);
	//LitSet&				recordClauseLits(Uid newUid);
	void				copyClauseLits(Uid clauseFrom, LitSet& clauseTo);
	ParentUsed			findParentsUsed(const LitSet& leftLits, const Uid rightParentUid, const Lit& piv, const Lit& BL);
	template<class S, class C>
	Lit					resolveWithOverwrite(S& set, C& clause);
	void reconstructClause(Lit BL, std::list<Uid>& newParentsCandidates, vec<Lit>& currPivots, ReconstructionResult& reconRes);
	Uid allocReconstructedClause(Uid currUid, ReconstructionResult& reconRes);
	
	
	class ResolutionException : public std::exception {
	public:
		ResolutionException(const char* msg) : std::exception(msg) {}
	};


};
}

