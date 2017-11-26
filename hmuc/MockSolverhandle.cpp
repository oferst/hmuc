#include "MockSolverhandle.h"
namespace Minisat {


MockSolverhandle::MockSolverhandle(): SolverHandle(NULL){
	dummy.push(mkLit(111));
}

MockSolverhandle::~MockSolverhandle(){

}

Uid MockSolverhandle::CRefToUid(CRef cref) {
	return CRef_Undef;
}

CRef MockSolverhandle::UidToCRef(Uid uid) {
	return CRef_Undef;
} 


//vec<Lit>& MockSolverhandle::getDelayedRemoval(Uid uid) {
//	return vec<Lit>();
//}

//Resol& MockSolverhandle::getResol(Uid uid) {
//
//}

CRef MockSolverhandle::allocClause(vec<Lit>& lits, bool isLearned, bool isIc) {

}

CRef MockSolverhandle::allocClause(LitSet& lits, bool isLearned, bool isIc) {

}

void MockSolverhandle::allocResol(CRef cref, vec<Uid> allParents, vec<Uid> icParents, vec<Uid> remParents) {

}

void MockSolverhandle::analyzeConflictingAssumptions(Lit initConflict, vec<Lit>& out_negConflicts, vec<uint32_t>& out_icParents, vec<uint32_t>& out_remParents, vec<uint32_t>& out_allParents) {

}

Clause& MockSolverhandle::getClause(Uid uid) {}
vec<Lit>& MockSolverhandle::getDelayedRemoval(Uid uid) {}
Resol& MockSolverhandle::getResol(Uid uid) {}
}
