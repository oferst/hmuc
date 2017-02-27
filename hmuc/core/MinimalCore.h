#ifndef MINIMAL_CORE_H
#define MINIMAL_CORE_H

#include "simp/SimpSolver.h"
#include "mtl/Map.h"

namespace Minisat 
{

class CMinimalCore
{
public:
    CMinimalCore(SimpSolver& solver);

	void test(vec<uint32_t>&, Set<uint32_t>&, char * msg = "" ); 
    lbool Solve(bool pre);

	void testsat(); // !!

    inline SimpSolver& GetSolver() { return m_Solver; }

    void SetICNum(uint32_t nIcNum);

    bool m_bIcInConfl;
private:
   void PrintData(int unknownSize, int mucSize, int iter, bool last = false);

   uint32_t GetMaxIc(Map<uint32_t, uint32_t>& mapIcToScore);
   uint32_t GetMinIc(Map<uint32_t, uint32_t>& mapIcToScore);

   void Rotate_it(uint32_t clsUid, Var v, Set<uint32_t>& moreMucClauses, Set<uint32_t>& setMuc, bool bUseSet); // iterative version
   void Rotate(uint32_t clsUid, Var v, Set<uint32_t>& moreMucClauses, Set<uint32_t>& setMuc, bool bUseSet);

    SimpSolver& m_Solver;
    uint32_t m_nICSize;
    vec<vec<uint32_t> > m_Occurs;

    int m_nRotationCalled;
    int m_nRotationFirstCalls;
    int m_nRotationClausesAdded;
    int m_nSecondRotationClausesAdded;
    struct ClauseOrder {
        const Solver& solver;
        int m_RemoveOrder;
        bool operator () (unsigned x, unsigned y) const { 
            CRef refX = solver.GetClauseIndFromUid(x);
            if (refX == CRef_Undef)
                return false;
            CRef refY = solver.GetClauseIndFromUid(y);
            if (refY == CRef_Undef)
                return true;
            if (m_RemoveOrder == 0)
                return solver.GetClause(refX).size() > solver.GetClause(refY).size(); 
            else
                return solver.GetClause(refX).size() < solver.GetClause(refY).size(); 
        }
        ClauseOrder(const Solver& s, int remove_order) : solver(s), m_RemoveOrder(remove_order) { }
    };

    Heap<ClauseOrder> m_ClauseHeap;
    vec<uint32_t> m_ClausesForRemoval;
};

}

#endif
