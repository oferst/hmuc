#pragma once
#include "simp/SimpSolver.h"
//#include <boost/iterator/iterator_facade.hpp>



namespace Minisat {
	class LitIter;
	class SolverHandle{
		Solver* s;
		Resol* PoEC;
	public:
	
		SolverHandle(Solver* _s);
		virtual ~SolverHandle();
		virtual vec<Uid>& getPoEC();
		virtual vec<Uid>& getIcPoEC();
		virtual Uid CRefToUid(CRef cref);
		virtual CRef UidToCRef(Uid uid);
		virtual Clause& getClause(Uid uid);
		virtual vec<Lit>& getDelayedRemoval(Uid uid);
		virtual Resol& getResol(Uid uid);
		virtual RRef getResolRef(Uid uid);
		virtual CRef allocClause(vec<Lit>& lits, bool isLearned, bool isIc,bool hasUid=false);
		virtual CRef allocClause(LitSet& lits, bool isLearned, bool isIc, bool hasUid = false);
		virtual void allocResol(CRef cref, vec<Uid>& allParents, vec<Uid>& icParents, vec<Uid>& remParents);
		virtual void allocNonIcResol(CRef cref);
		virtual void analyzeConflictingAssumptions(Lit initConflict, vec<Lit>& out_negConflicts, vec<uint32_t>& out_icParents, vec<uint32_t>& out_remParents, vec<uint32_t>& out_allParents);
		virtual bool inRhombus(Uid uid);
		virtual int level(Var v);

		virtual void updateParentsOrder(Uid uid, const vec<Uid>& icParents, const vec<Uid>& remParents, const vec<Uid>& allParents);
		
		virtual void realocExistingResolution(Uid oldUid, const vec<Uid>& icParents, const vec<Uid>& remParents, const vec<Uid>& allParents);

		void printClauseByUid(Uid uid, const std::string& msg,ostream& out=std::cout) { 
			s->printClauseByUid(uid, msg, out);
		}
		void getClauseByUid(Uid uid, vec<Lit>& outClause) {
			s->getClauseByUid(uid, outClause);
		}
		void getClauseByUid(Uid uid, LitSet& outClause) {
			s->getClauseByUid(uid, outClause);
		}
	};


}

