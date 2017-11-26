#pragma once


namespace Minisat {
class MockSolverhandle : public SolverHandle {
public:
	vec<Lit> dummy;
	MockSolverhandle();
	virtual ~MockSolverhandle();
	virtual Uid CRefToUid(CRef cref);
	virtual CRef UidToCRef(Uid uid);
	virtual CRef allocClause(vec<Lit>& lits, bool isLearned, bool isIc);
	virtual CRef allocClause(LitSet& lits, bool isLearned, bool isIc);
	virtual void allocResol(CRef cref, vec<Uid> allParents, vec<Uid> icParents, vec<Uid> remParents);
	virtual void analyzeConflictingAssumptions(Lit initConflict, vec<Lit>& out_negConflicts, vec<uint32_t>& out_icParents, vec<uint32_t>& out_remParents, vec<uint32_t>& out_allParents);
	virtual Clause& getClause(Uid uid);
	virtual vec<Lit>& getDelayedRemoval(Uid uid);
	virtual Resol& getResol(Uid uid);
	

};
}

