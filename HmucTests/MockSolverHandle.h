#pragma once
#include "gmock/gmock.h"
#include "SolverHandle.h"
namespace Minisat {
	class MockSolverHandle : public SolverHandle {
	public:
		MockSolverHandle() : SolverHandle(NULL) {}
		MOCK_METHOD0(getPoEC, vec<Uid>&());
		MOCK_METHOD0(getPoEC_Piv, vec<Lit>&());
		MOCK_METHOD1(CRefToUid, Uid(CRef cref));
		MOCK_METHOD1(UidToCRef, CRef(Uid uid));
		MOCK_METHOD1(getClause, Clause&(Uid uid));
		MOCK_METHOD1(getDelayedRemoval, vec<Lit>&(Uid uid));
		MOCK_METHOD1(getResol, Resol&(Uid uid));
		MOCK_METHOD1(inRhombus, bool(Uid uid));
		MOCK_METHOD1(allocNonIcResol, void(CRef cref));
		MOCK_METHOD3(allocClause, CRef(vec<Lit>& lits, bool isLearned, bool isIc));
		MOCK_METHOD3(allocClause, CRef(LitSet& lits, bool isLearned, bool isI));
		MOCK_METHOD4(allocResol, void(CRef cref, vec<Uid> allParents, vec<Uid> icParents, vec<Uid> remParents));
		MOCK_METHOD5(analyzeConflictingAssumptions, void(Lit initConflict, vec<Lit>& out_negConflicts, vec<uint32_t>& out_icParents, vec<uint32_t>& out_remParents, vec<uint32_t>& out_allParents));
	};
}