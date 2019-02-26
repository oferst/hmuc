#include "simp/SolverHandle.h"
namespace Minisat {

	SolverHandle::SolverHandle(Solver* _s = NULL) : s(_s)
	{
		vec<Uid>& icPoEC = s->icPoEC;
		vec<Uid>& allPoEC = s->allPoEC;
		int numOfNonIc = allPoEC.size() - icPoEC.size();
		int additionalSize = (numOfNonIc == 0) ? 0 : (1 + numOfNonIc + (allPoEC.size() / 32) + (int)((allPoEC.size() % 32) > 0));
		PoEC = (Resol*)malloc(4 * (Resol::SIZE + icPoEC.size() + additionalSize));
		vec<Uid> nonIcPoEC;
		new (PoEC) Resol(icPoEC, nonIcPoEC, allPoEC, true);
	}

	SolverHandle::~SolverHandle()
	{
		free(PoEC);
	}
	void SolverHandle::realocExistingResolution(Uid oldUid, const vec<Uid>& icParents, const vec<Uid>& remParents, const vec<Uid>& allParents) {
		s->resolGraph.realocExistingResolution(oldUid, icParents, remParents, allParents);
	}

	void SolverHandle::updateParentsOrder(Uid uid, const vec<Uid>& icParents, const vec<Uid>& remParents, const vec<Uid>& allParents) {
		s->resolGraph.updateParentsOrder(uid, icParents, remParents, allParents);
	}
	Uid SolverHandle::CRefToUid(CRef cref) {
		Uid uid;
		bool hasUid = s->hasUid(cref, uid);
		assert(hasUid);
		return uid;
	}

	CRef SolverHandle::UidToCRef(Uid uid) {
		return s->resolGraph.GetClauseRef(uid);
	}
	//Returns the clause recorded in the clause allocator. Note that a uid for a deleted clause will cause a crash here - use sh->getDelayedRemoval(uid) instead
	Clause& SolverHandle::getClause(Uid uid) {
		assert(CRef_Undef != UidToCRef(uid));
		return s->ca[UidToCRef(uid)];

	}
	vec<Lit>& SolverHandle::getDelayedRemoval(Uid uid) {
		assert(s->resolGraph.icDelayedRemoval.find(uid) != s->resolGraph.icDelayedRemoval.end());
		return *(s->resolGraph.icDelayedRemoval[uid]);

	}

	Resol& SolverHandle::getResol(Uid uid) {
		if (CRef_Undef == uid) {
			return *PoEC;
		}
		CResolutionGraph& g = s->resolGraph;
		return s->resolGraph.GetResol(getResolRef(uid));
	}

	RRef SolverHandle::getResolRef(Uid uid) {
		assert(uid <= Clause::GetNextUid() && uid != CRef_Undef);
		return s->resolGraph.GetResolRef(uid);
	}
	CRef SolverHandle::allocClause(vec<Lit>& lits, bool isLearned, bool isIc, bool hasUid) {

		return s->allocClause(lits, isLearned, isIc, hasUid);
	}
	CRef SolverHandle::allocClause(LitSet& lits, bool isLearned, bool isIc, bool hasUid) {
		vec<Lit> litVec;
		for (auto& l : lits)
			litVec.push(l);
		return  s->allocClause(litVec, isLearned, isIc, hasUid);
	}
	void SolverHandle::allocResol(CRef cref, vec<Uid>& allParents, vec<Uid>& icParents, vec<Uid>& remParents) {
		s->resolGraph.AddNewResolution(CRefToUid(cref), cref, icParents, remParents, allParents);
	}
	void SolverHandle::allocNonIcResol(CRef cref) {
		s->resolGraph.AddRemainderResolution(CRefToUid(cref), cref);

	}
	void SolverHandle::analyzeConflictingAssumptions(Lit initConflict, vec<Lit>& out_negConflicts, vec<uint32_t>& out_icParents, vec<uint32_t>& out_remParents, vec<uint32_t>& out_allParents) {
		s->analyzeFinal(initConflict, out_negConflicts, out_icParents, out_remParents, out_allParents);
	}
	vec<Uid>& SolverHandle::getIcPoEC() {
		return s->icPoEC;
	}

	vec<Uid>& SolverHandle::getPoEC() {
		return s->allPoEC;
	}

	bool SolverHandle::inRhombus(Uid uid) {
		return CRef_Undef == uid || (s->unbondedCone.find(uid) != s->unbondedCone.end());
	}
	int SolverHandle::level(Var v) {
		return s->level(v);
	}
	lbool SolverHandle::value(const Lit& l) {
		return s->value(l);
	}

	bool SolverHandle::hasDelayedRemoval(Uid uid) {
		return s->resolGraph.icDelayedRemoval.find(uid) != s->resolGraph.icDelayedRemoval.end();
	}
	
}