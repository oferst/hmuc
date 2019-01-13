#pragma once
#include "SolverHandle.h"
#include "RebuilderContext.h"
#include "Printer.h"

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
	void setAllocatedClauseData(Uid uid) {
		assert(Uninitialized == status);
		status = Allocated;
		clauseUid = uid;
	}
	
	template<class T>
	void setDeferredClauseData(const T& lits)  {
		assert(Uninitialized == status);
		status = Deferred;
		clauseContent = new LitSet();
		for (auto l : lits)
			clauseContent->insert(l);
	}
	~ClauseData() {
		if (status == Deferred) 
				delete(clauseContent);
	}
	
};

struct ReconstructionResult {
	LitSet newClause;
	std::list<ClauseData> rebuiltParentsCandidates;
	std::list<ClauseData*> parentsUsed;
	bool isIc;
	ReconstructionResult() : isIc(false) {}
	~ReconstructionResult() {}
};

struct ResolValidation {
	const LitSet& targetClause;
	bool valid;
	std::unordered_set<Var> pivotVars;
	ResolValidation(const LitSet& _targetClause) :targetClause(_targetClause), valid(true), pivotVars(std::unordered_set<Var>()){}
};
class ProofRebuilder{
	//A handle for the underlaying solver used to create the resolution graph.
	SolverHandle* sh;
	ofstream  out;
	//recording all the clauses that were build in the reconstruction.
	std::unordered_set<Uid> debugRebuiltClauses;

public:
	//A DB containing the current state of the proof rebuilding process.
	RebuilderContext* ctx;
	bool memberOfClause(Uid u, const Lit& l);
	
	template<class T>
	bool validateResolution(Uid resultClause, T& parents,vec<Lit>& pivots);
	template<class T>
	bool validateResolution(LitSet& clause, T& parents);
	bool verifyResolutionProof(const vec<Uid>& PoEC);

	void clearCandidateParents(ReconstructionResult& reconRes);
	void addCandidateParent(Uid uid, bool isIc, ReconstructionResult& reconRes);


	static int depth_debug;
	int verbose = 0;
	void printClauseData(const ClauseData& cd, const std::string& text) {
		switch(cd.status){
		case Allocated:
			sh->printClauseByUid(cd.clauseUid, text + " (A)"); break;
		case Deferred:
			printClause(*cd.clauseContent, text + " (D)"); break;
		case Uninitialized:
			printf((text + " (U)\n").c_str()); break;
		default: assert(0);
		}
	}



	ProofRebuilder(SolverHandle* sh, RebuilderContext* ctx);

	void RebuildProof(
		const Lit& startingConflLiteral, vec<Uid>& allPoEC, vec<Uid>& new_allPoEC, vec<Uid>& new_icPoEC);

	void correctResolutionOrder(Uid currUid, vec<Lit>& pivots);
	Uid	proveBackboneLiteral(
							const Uid currUid, 
							const Lit& BL, 
							ClauseData& clauseResult);
	void backwardsTraversal(
							const Uid currUid,
							const Lit& BL,
							const vec<Lit>& currPivots,
							std::list<ClauseData>& rebuiltparentsData);

	void calculateClause(
							const Uid currUid,
							const Lit& BL, 
							const vec<Lit>& currPivots, 
							ReconstructionResult& reconRes);
	void allocateNonIcParents(ReconstructionResult& reconRes, vec<Uid>& allUids, vec<Uid>& icUids);
	Uid allocReconstructedICClause(
								const Uid& currUid, 
								ReconstructionResult& reconRes,
								const Lit& BL);
	
	void recordClausePivots(Uid uid, ResolValidation& validation);

	LitSet&	recordClause(Uid newUid);

	void	copyClauseLits(Uid clauseFrom, LitSet& clauseTo);

	ParentUsed	findParentsUsed(const LitSet& leftLits, const LitSet& rightLits, const Lit& piv, const Lit& BL);
	
	template<class S, class C>
	Lit	resolveWithOverwrite(S& set, C& clause);
	template<class S, class C>
	Lit	resolveWithOverwrite(S& set, C& clause, ResolValidation& validation);
	
	void findParentDependencies(const vec<Uid>& parents, const vec<Lit>& pivots, const LitSet& resultClause, std::unordered_map<uint32_t,vec<uint32_t>>& dependencies);
	
	
	


};
}

