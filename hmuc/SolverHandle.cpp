#include "SolverHandle.h"
namespace Minisat {

SolverHandle::SolverHandle(Solver* _s=NULL): s(_s)
{
}

SolverHandle::~SolverHandle()
{
}
void SolverHandle::realocExistingResolution(Uid oldUid, const vec<Uid>& icParents, const vec<Uid>& remParents, const vec<Uid>& allParents) {
	s->resolGraph.realocExistingResolution(oldUid, icParents, remParents, allParents);
}

void SolverHandle::updateParentsOrder(Uid uid, const vec<Uid>& icParents, const vec<Uid>& remParents, const vec<Uid>& allParents) {
	s->resolGraph.updateParentsOrder(uid, icParents, remParents, allParents);
}
Uid SolverHandle::CRefToUid(CRef cref) {
	Uid uid;
	assert(s->hasUid(cref, uid));
	return uid;

	//s->has
	//Clause& c = s->ca[cref];
	//if (c.hasUid())
	//	return s->ca[cref].uid();
	//else
	//	return s->nonIcUidDeferredAlloc[cref];
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
	CResolutionGraph& g = s->resolGraph;
	return s->resolGraph.GetResol(getResolRef(uid));
}

RRef SolverHandle::getResolRef(Uid uid) {
	return s->resolGraph.GetResolRef(uid);
}
CRef SolverHandle::allocClause(vec<Lit>& lits, bool isLearned, bool isIc,bool hasUid) {

	return s->allocClause(lits, isLearned,isIc,hasUid);
}
CRef SolverHandle::allocClause(LitSet& lits, bool isLearned, bool isIc, bool hasUid) {
	vec<Lit> litVec;
	for (auto& l : lits)
		litVec.push(l);
	return  s->allocClause(litVec, isLearned,isIc, hasUid);
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
//vec<Lit>& SolverHandle::getPoEC_Piv() {
//	return s->allPoEC_pivots;
//}
bool SolverHandle::inRhombus(Uid uid) {
	
	//return CRef_Undef == uid || (s->map_cls_to_Tclause.find(uid) != s->map_cls_to_Tclause.end());
	return CRef_Undef == uid || (s->unbondedCone.find(uid)!= s->unbondedCone.end());
}

//template <class T>
//void SolverHandle::printClause(T clause, std::string msg) {
//	s->printClause(clause, msg);
//}

}