#include "SolverHandle.h"
namespace Minisat {

SolverHandle::SolverHandle(Solver* _s=NULL): s(_s)
{
}

SolverHandle::~SolverHandle()
{
}


Uid SolverHandle::CRefToUid(CRef cref) {
	return s->ca[cref].uid();
}

CRef SolverHandle::UidToCRef(Uid uid) {
	return s->resolGraph.GetClauseRef(uid);
}
Clause& SolverHandle::getClause(Uid uid) {
	return s->ca[UidToCRef(uid)];

}
vec<Lit>& SolverHandle::getDelayedRemoval(Uid uid) {
	assert(s->resolGraph.icDelayedRemoval.find(uid) != s->resolGraph.icDelayedRemoval.end());
	return *(s->resolGraph.icDelayedRemoval[uid]);

}

Resol& SolverHandle::getResol(Uid uid) {
	CResolutionGraph& g = s->resolGraph;
	return g.GetResol(g.GetResolRef(uid));
}
CRef SolverHandle::allocClause(vec<Lit>& lits, bool isLearned, bool isIc) {
	return s->ca.alloc(lits, isLearned, isIc);
}
CRef SolverHandle::allocClause(LitSet& lits, bool isLearned, bool isIc) {
	return s->ca.alloc(lits, isLearned, isIc);
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

vec<Uid>& SolverHandle::getPoEC() {
	return s->allPoEC;
}
vec<Lit>& SolverHandle::getPoEC_Piv() {
	return s->allPoEC_pivots;
}
bool SolverHandle::inRhombus(Uid uid) {
	return s->map_cls_to_Tclause.find(uid) != s->map_cls_to_Tclause.end();
}

//template <class T>
//void SolverHandle::printClause(T clause, std::string msg) {
//	s->printClause(clause, msg);
//}

}