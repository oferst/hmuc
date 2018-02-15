#pragma once
#include "SolverHandle.h"
#include "RebuilderContext.h"

namespace Minisat {

typedef enum {//used in proof reconstruction when opt_blm_rebuild_proof is used
	Either=0,Left=1, Right=2, Both=3,
} ParentUsed;


typedef LitSet DeferredAllocation;

typedef enum ClauseAllocStatus {
	Uninitialized, Allocated, Deferred
};



struct ClauseData {
	//If status is ic, then data will contain an uid,
	//otherwise, data will contain the literal content 
	//of the clause (for the purpose of deferred allocation).
	ClauseAllocStatus status;
	Lit origPiv;
	union {
		Uid clauseUid;
		LitSet* clauseContent;
	};
	ClauseData(const Lit& piv= mkLit(Var(var_Undef))) : status(Uninitialized),origPiv(piv){}
	ClauseData(const ClauseData& other) :status(other.status), origPiv(other.origPiv){
		switch (status) {
		case Allocated:
		case Uninitialized:
			clauseUid = other.clauseUid;
			break;
		case Deferred:
			clauseContent = new LitSet();
			replaceContent(*clauseContent, *other.clauseContent);
			break;
		default:
			clauseUid = CRef_Undef;
		}

	}
	void setIc(Uid uid) {
		assert(Uninitialized == status);
		status = Allocated;
		clauseUid = uid;
	}
	
	template<class T>
	void setNonIc(const T& lits)  {
		assert(Uninitialized == status);
		status = Deferred;
		clauseContent = new LitSet();
		for (auto l : lits)
			clauseContent->insert(l);
	}
	~ClauseData() {
		if (status == Deferred) 
				free(clauseContent);
	}
};

struct ReconstructionResult {
	LitSet newClause;
	std::list<ClauseData> parentsCandidates;
	std::list<ClauseData*> parentsUsed;
	bool isIc;
	ReconstructionResult() : isIc(false) {}
	~ReconstructionResult() {}
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
	int verbose = 0;
	ProofRebuilder(SolverHandle* sh,RebuilderContext* ctx);

	void RebuildProof(
		const Lit& startingConflLiteral, vec<Uid>& allPoEC, vec<Uid>& new_allPoEC, vec<Uid>& new_icPoEC);

	template<class T>
	Uid	proveBackboneLiteral(
							const Uid currUid, 
							const T& initParents,
							const Lit& BL, 
							ClauseData& clauseResult);
	template<class T>
	void backwardsTraversal(
							const Uid currUid,
							const T& parents, 
							const Lit& BL,
							const vec<Lit>& currPivots,
							std::list<ClauseData>& rebuiltparentsData);

	void reconstructClause(
							const Uid currUid,
							const Lit& BL, 
							const vec<Lit>& currPivots, 
							ReconstructionResult& reconRes);
	void allocateNonIcParents(ReconstructionResult& reconRes, vec<Uid>& allUids, vec<Uid>& icUids, vec<Uid>& nonIcUids);
	Uid allocReconstructedClause(
								const Uid& currUid, 
								ReconstructionResult& reconRes);
	
	template<class T>
	void recordClausePivots(Uid uid, const T& parents);

	LitSet&	recordClause(Uid newUid);

	void	copyClauseLits(Uid clauseFrom, LitSet& clauseTo);

	ParentUsed	findParentsUsed(const LitSet& leftLits, const LitSet& rightLits, const Lit& piv, const Lit& BL);
	
	template<class S, class C>
	Lit	resolveWithOverwrite(S& set, C& clause);

	
	
	class ResolutionException : public std::exception {
	public:
		ResolutionException(const char* msg) : std::exception(msg) {}
	};


};
}

