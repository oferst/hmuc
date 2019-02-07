
/****************************************************************************************[Solver.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#ifndef Minisat_Solver_h
#define Minisat_Solver_h

#include "mtl/Vec.h"
#include "mtl/Heap.h"
#include "mtl/Alg.h"
#include "utils/Options.h"
#include "core/SolverTypes.h"
#include "DelayedResolGraphAlloc.h"
#include "core/ResolutionGraph.h"
#include <stdint.h>
#include <vector>
#include <string>
#include <unordered_map>
#include <map>
#include <unordered_set>
#include <tuple>
#include <iostream>
#include <fstream>
using namespace std;

// temporary, for testing a simplification of the code. 
#define NewParents
namespace Minisat {

//=================================================================================================
// Solver -- the main class:


enum pf_modes{
	none,
	clause_only, // negated ic-clause-to-remove
	pf, // unique prefix
	lpf, // literal-based, between iterations
	lpf_inprocess // literal-based, as part of search
};

//typedef enum {//used in proof reconstruction when opt_blm_rebuild_proof is used
//	Left, Right, Both, Either
//} ParentUsed;


class Solver {
	friend class SolverHandle;
public:
	static int debug_flag;
	void GeticUnits(vec<int>&);
	void GetUnsatCore(vec<Uid>& icCore, Set<Uid>& icAncestors, Set<Uid>& nonIcAncestors, bool debug = false, int maxCoreUid = -1, ostream& out = std::cout);
    void RemoveEverythingNotInRhombusOrMuc(Set<uint32_t>& cone, Set<uint32_t>& muc);
	void RemoveClauses_withoutICparents(vec<uint32_t>& cone);
    void RemoveClauses(vec<uint32_t>& cone);
    void BindClauses(vec<uint32_t>& cone, uint32_t initUid);
    void GroupBindClauses(vec<uint32_t>& initUids);
    void UnbindClauses(vec<uint32_t>& cone);
	void UnbindClauses(vec<uint32_t>& cone,std::unordered_set<Uid>& coneSet);
    CRef GetClauseIndFromUid(uint32_t uid) const
    {
        return resolGraph.GetClauseRef(uid);
    }
	CRef allocClause(vec<Lit>& lits,bool learnt, bool isIc, bool hasUid);

    Clause& GetClause(CRef ind) 
    {
        return ca[ind];
    }
    const Clause& GetClause(CRef ind) const
    {
        return ca[ind];
    }
	void getClauseByUid(Uid uid, vec<Lit>& outClause);
	void getClauseByUid(Uid uid, LitSet& outClause);

    ClauseAllocator& GetAlloc()
    {
        return ca;
    }

    void ReversePolarity() 
    {
        for (Var v = 0; v < nVars(); ++v)
        {
            polarity[v] = !polarity[v];
        }
    }

	double time_for_pf;	
	//time for proof reconstruction
	double time_for_pr;
	bool test_now;
	uint32_t nICtoRemove;   // the IC that is currently removed.
	
	// PoEC - Parents of Empty Clause
	vec<uint32_t> icPoEC; //ic parents of empty clause used in lpf_get_assumptions. Stores the ic parents of empty clause from the last unsat.
	vec<uint32_t> allPoEC; //All parents of empty clause from the last unsat. They are only maintained for using the proof reconstruction algorithm, and are not actually used outside of it.
	std::unordered_set<Uid> unbondedCone;

	
	int pf_Literals;



	bool pf_active;
	bool pf_zombie;  // when true, we know already that it is unsat, but we continue in order to get a proof. 
	int pf_zombie_iter;  // counts how many iterations we are already in zombie mode. 
	bool lpf_delay; // when true, it means that we did not reach the delay threshold (set by opt_pf_delay).	

	bool blm_rebuild_proof;


	int m_nSatCall;
    int m_nUnsatPathFalsificationCalls;
    vec<uint32_t> icParents;
	vec<uint32_t> allParents;
	vec<uint32_t> remParents;
    bool m_bUnsatByPathFalsification;
	int nUnsatByPF;
	int pf_prev_trail_size;
	bool test_mode;
	bool m_bConeRelevant;
		
    // Constructor/Destructor:
    //
	Solver();
    virtual ~Solver();

    // Problem specification:
    //
    Var     newVar    (bool polarity = true, bool dvar = true); // Add a new variable with parameters specifying variable mode.

    bool    addClause (const vec<Lit>& ps);                     // Add a clause to the solver. 
    bool    addEmptyClause();                                   // Add the empty clause, making the solver contradictory.
    bool    addClause (Lit p);                                  // Add a unit clause to the solver. 
    bool    addClause (Lit p, Lit q);                           // Add a binary clause to the solver. 
    bool    addClause (Lit p, Lit q, Lit r);                    // Add a ternary clause to the solver. 
    bool    addClause_(vec<Lit>& ps, bool ic = false, vec<uint32_t>* icparents = NULL);        // Add a clause to the solver without making superflous internal copy. Will
                                                                // change the passed vector 'ps'.

    // Solving:
    //
    bool    simplify     ();                        // Removes already satisfied clauses.
    bool    solve        (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions.
    lbool   solveLimited (const vec<Lit>& assumps); // Search for a model that respects a given set of assumptions (With resource constraints).
    bool    solve        ();                        // Search without assumptions.
    bool    solve        (Lit p);                   // Search for a model that respects a single assumption.
    bool    solve        (Lit p, Lit q);            // Search for a model that respects two assumptions.
    bool    solve        (Lit p, Lit q, Lit r);     // Search for a model that respects three assumptions.
    bool    okay         () const;                  // FALSE means solver is in a conflicting state

    void    toDimacs     (FILE* f, const vec<Lit>& assumps);            // Write CNF to file in DIMACS-format.
    void    toDimacs     (const char *file, const vec<Lit>& assumps);
    void    toDimacs     (FILE* f, Clause& c, vec<Var>& map, Var& max);

    // Convenience versions of 'toDimacs()':
    void    toDimacs     (const char* file);
    void    toDimacs     (const char* file, Lit p);
    void    toDimacs     (const char* file, Lit p, Lit q);
    void    toDimacs     (const char* file, Lit p, Lit q, Lit r);
    
    // Variable mode:
    // 
    void    setPolarity    (Var v, bool b); // Declare which polarity the decision heuristic should use for a variable. Requires mode 'polarity_user'.
    void    setDecisionVar (Var v, bool b); // Declare if a variable should be eligible for selection in the decision heuristic.

    // Read state:
    //
    lbool   value      (Var x) const;       // The current value of a variable.
    lbool   value      (Lit p) const;       // The current value of a literal.
    lbool   modelValue (Var x) const;       // The value of a variable in the last model. The last call to solve must have been satisfiable.
    lbool   modelValue (Lit p) const;       // The value of a literal in the last model. The last call to solve must have been satisfiable.
	
    int     nAssigns   ()      const;       // The current number of assigned literals.
    int     nClauses   ()      const;       // The current number of original clauses.
    int     nLearnts   ()      const;       // The current number of learnt clauses.
    int     nVars      ()      const;       // The current number of variables.
    int     nFreeVars  ()      const;

    // Resource constraints:
    //
    void    setConfBudget(int64_t x);
    void    setPropBudget(int64_t x);
    void    budgetOff();
    void    interrupt();          // Trigger a (potentially asynchronous) interruption of the solver.
    void    clearInterrupt();     // Clear interrupt indicator flag.

    // Memory management:
    //
    virtual void garbageCollect();
    void    checkGarbage(double gf);
    void    checkGarbage();
	
    // Extra results: (read-only member variable)
    //
    vec<lbool> model;             // If problem is satisfiable, this vector contains the model (if any).
    vec<Lit>   conflict;          // If problem is unsatisfiable (possibly under assumptions),
                                  // this vector represent the final conflict clause expressed in the assumptions.

    // Mode of operation:
    //

    int       verbosity;
    double    var_decay;
    double    clause_decay;
    double    random_var_freq;
    double    random_seed;
    bool      luby_restart;
    int       ccmin_mode;         // Controls conflict clause minimization (0=none, 1=basic, 2=deep).
    int       phase_saving;       // Controls the level of phase saving (0=none, 1=limited, 2=full).
    bool      rnd_pol;            // Use random polarities for branching heuristics.
    bool      rnd_init_act;       // Initialize variable activities with a small random value.
    double    garbage_frac;       // The fraction of wasted memory allowed before a garbage collection is triggered.

    int       restart_first;      // The initial restart limit.                                                                (default 100)
    double    restart_inc;        // The factor with which the restart limit is multiplied in each restart.                    (default 1.5)
    double    learntsize_factor;  // The initial limit for learnt clauses is a factor of the original clauses.                (default 1 / 3)
    double    learntsize_inc;     // The limit for learnt clauses is multiplied with this factor each restart.                 (default 1.1)

    int       learntsize_adjust_start_confl;
    double    learntsize_adjust_inc;

	

    // Statistics: (read-only member variable)
    //
    uint64_t solves, starts, decisions, rnd_decisions, propagations, conflicts;
    uint64_t dec_vars, clauses_literals, learnts_literals, max_literals, tot_literals;

    void AddConflictingIc(uint32_t uid);
    void CreateResolVertex(uint32_t uid);
    void ResetOk();
    int PF_get_assumptions(uint32_t uid, CRef cref);
	vec<Lit> LiteralsFromPathFalsification; //oferg: S(emptyClause) - from last LPF call, these are the literals found to be inferred from the formula
	int count_true_assump;
	int count_assump;
	// LPF
	int pf_mode;
	bool test_result;


	bool pf_early_unsat_terminate(); 
	void LPF_get_assumptions(uint32_t uid, vec<Lit>& lits);    
	bool lpf_compute_inprocess();
	bool isRebuildingProof();
	bool hasUid(CRef cref, Uid& outUid);

	Uid getUid(CRef cref);
	
	//bool inRhombus(Uid uid);
	//Uid updateClause(Uid uid, Lit BL, UidToLitVec& pivots, UidToUid& clauseUdates, UidToLitSet& newClauses_lits);
	//void RebuildProof(Lit startingConflLit);
	//void updateClauseLits(Uid newUid, UidToLitSet& newClauses_lits);
	//ParentUsed findParentsUsed(LitSet& leftLits, uint32_t rightParentUid, Lit piv, UidToLitSet& newClauses_lits);
	//template<class T>
	//int BackwardsTraversal(const Uid currUid, const T& initParents, const Lit BL, UidToLitVec& pivots, UidToUid& clausesUpdates, UidToLitSet& newClauses_lits,std::list<Uid>& out_parentsUidUpdates);
	//Uid recalculateClause(const Uid currUid, const vec<Lit>& pivots, const int initPivIdx, const std::list<Uid>& parentsUpdate, UidToUid& clausesUpdates, UidToLitSet& newClauses_lits);

	Uid ProveBackboneLiteral(Uid nodeId, Lit p, UidToLitVec& pivots, UidToUid& clauseUpdates, UidToLitSet& newClauses_lits);

	std::unordered_map<uint32_t, vec<Lit>* > map_cls_to_Tclause; // from clause index to its Tclause
	vec<Uid> rhombusParentOfEmptyClause;
	//bool rhombusValid;
	uint32_t lpfTopChainUid;
	uint32_t lpfBottomChainUid;
	vec<Lit> lpfBottomLits;

	bool CountParents(Map<uint32_t,uint32_t>& mapRealParents,uint32_t uid);
	void printResGraph(uint32_t, vec<uint32_t>&, vec<Lit>&  );
	void ResGraph2dotty(vec<uint32_t>&, vec<uint32_t>&, vec<Lit>& , const char*);
	//void ResSubgraph2dotty(vec<uint32_t>&, vec<uint32_t>&,Set<uint32_t>&, vec<Lit>&, const char*);
	uint32_t dottyCalls = 0; //!!

	//populates outRhombus with all uids that are 1) reachable from some root inRoots and 2) reach some leaf in inLeaves
	//void calcRhombus(vec<uint32_t>& inRoots, vec<uint32_t>& inLeaves, Set<uint32_t>& outRhombus);
	//________________________________________________________________________________________________
	
	void printLearntsDB();
	void printTrail();
	void printClauseByUid(uint32_t uid, std::string text,ostream& out = std::cout);
 //   void printClause(FILE* f, Clause& c);
	//	
	//void printClause(FILE * f, vec<Lit>& v, std::string text="");	

    template<class T>
    void printLits(FILE* f, const T& c)
    {
        for (int i = 0; i < c.size(); i++)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", var(c[i])+1);
    }

	CResolutionGraph resolGraph; 
protected:
    void findConflictICReasons(CRef ref);
    
    vec<CRef> icUnitClauses;
	//this vector is similar in function to the 'icLearnedUnitClauses' vector, but instead of finding the unit during search() (and having parents that resolved it), units in this vector are found via a simplification of an existing clause (a strengthening at d.l. 0), s.t. it isn't immediately apparent what are the parents of the new unit. Due to this, we don't add the new unit to the resolution graph, and we keep the weaker clause in the graph (although we do remove the weaker clause from the clause DB) 
	vec<CRef> icNonLearnedUnitClauses;
	
    vec<Map<Lit, CRef>::Pair> icImpl;
    Set<uint32_t> setGood; // setGood = clauses that all their parents are not IC
    vec<uint32_t> uidsVec;
    

    // Helper structures:
    //
    struct VarData { CRef reason; int level; };
    static inline VarData mkVarData(CRef cr, int l){ VarData d = {cr, l}; return d; }

    struct Watcher {
		// the clause for which the watcher watched.
        CRef cref;
		// The literal being watched by the watcher
        Lit  blocker;
        Watcher(CRef cr, Lit p) : cref(cr), blocker(p) {}
        bool operator==(const Watcher& w) const { return cref == w.cref; }
        bool operator!=(const Watcher& w) const { return cref != w.cref; }
    };

    struct WatcherDeleted
    {
        const ClauseAllocator& ca;
        WatcherDeleted(const ClauseAllocator& _ca) : ca(_ca) {}
		//bool isDeleted(const Watcher& w) const { return ca[w.cref].mark() == 1; }
        bool operator()(const Watcher& w) const { return ca[w.cref].mark() == 1; }
    };

    struct VarOrderLt {
        const vec<double>&  activity;
        bool operator () (Var x, Var y) const { return activity[x] > activity[y]; }
        VarOrderLt(const vec<double>&  act) : activity(act) { }
    };

// define 'learnts' as a vector, which enables using nth_element in reduce_db
#define LEARNT

    // Solver state:
    //
    bool                ok;               // If FALSE, the constraints are already unsatisfiable. No part of the solver state may be used!
    vec<CRef>           clauses;          // List of problem clauses.    
#ifdef LEARNT
	std::vector<CRef>   learnts;		  // List of learnt clauses. Using std::vector (rather than vec) gives us iterators, which then allows us to use nth_element in reduceDB.
	
#endif
    double              cla_inc;          // Amount to bump next clause with.
    vec<double>         activity;         // A heuristic measurement of the activity of a variable.
    double              var_inc;          // Amount to bump next variable with.
    OccLists<Lit, vec<Watcher>, WatcherDeleted>
                        watches;          // 'watches[lit]' is a list of constraints watching 'lit' (will go there if literal becomes true).
    vec<lbool>          assigns;          // The current assignments.
    vec<char>           polarity;         // The preferred polarity of each variable.
    vec<char>           decision;         // Declares if a variable is eligible for selection in the decision heuristic.
    vec<Lit>            trail;            // Assignment stack; stores all assigments made in the order they were made.
    vec<int>            trail_lim;        // Separator indices for different decision levels in 'trail'.
    vec<VarData>        vardata;          // Stores reason and level for each variable.
    int                 qhead;            // Head of queue (as index into the trail -- no more explicit propagation queue in MiniSat).
    int                 simpDB_assigns;   // Number of top-level assignments since last execution of 'simplify()'.
    int64_t             simpDB_props;     // Remaining number of propagations that must be made before next execution of 'simplify()'.
    vec<Lit>            assumptions;      // Current set of assumptions provided to solve by the user.
    Heap<VarOrderLt>    order_heap;       // A priority queue of variables ordered with respect to the variable activity.
    double              progress_estimate;// Set by 'search()'.
    bool                remove_satisfied; // Indicates whether possibly inefficient linear scan for satisfied clauses should be performed in 'simplify'.

    ClauseAllocator     ca;
	std::unordered_map<CRef, Uid> nonIcUidDeferredAlloc;
	DelayedResolGraphAlloc delayedAllocator;


    // Temporaries (to reduce allocation overhead). Each variable is prefixed by the method in which it is
    // used, except 'seen' which is used in several places.
    //
    vec<char>           seen;
    vec<Lit>            analyze_stack;
    vec<Lit>            analyze_toclear;
    vec<Lit>            add_tmp;

    double              max_learnts;
    double              learntsize_adjust_confl;
    int                 learntsize_adjust_cnt;

    // Resource constraints:
    //
    int64_t             conflict_budget;    // -1 means no budget.
    int64_t             propagation_budget; // -1 means no budget.
    bool                asynch_interrupt;

    // Main internal methods:
    //
    void     insertVarOrder   (Var x);                                                 // Insert a variable in the decision order priority queue.
    Lit      pickBranchLit    ();                                                      // Return the next decision variable.
    void     newDecisionLevel (int conflictC);                                         // Begins a new decision level.
    void     uncheckedEnqueue (Lit p, CRef from = CRef_Undef);                         // Enqueue a literal. Assumes value of literal is undefined.
    bool     enqueue          (Lit p, CRef from = CRef_Undef);                         // Test if fact 'p' contradicts current state, enqueue otherwise.
    CRef     propagate        ();                                                      // Perform unit propagation. Returns possibly conflicting clause.
    void     cancelUntil      (int level);                                             // Backtrack until a certain level.
    
	
	
	void	 analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, vec<uint32_t>& icParents, DelayedResolGraphAlloc& dAlloc);
	void     analyzeFinal(Lit p, vec<Lit>& out_conflict, vec<uint32_t>& out_icParents, vec<uint32_t>& out_remParents, vec<uint32_t>& out_allParents);
	//bool     litRedundant     (Lit p, uint32_t abstract_levels, vec<uint32_t>& icParents, vec<uint32_t>& remParents, vec<uint32_t>& allParents); // (helper method for 'analyze()')
	bool     litRedundant(Lit p, uint32_t abstract_levels, vec<uint32_t>& icParents,DelayedResolGraphAlloc& delayedAllocator); // (helper method for 'analyze()')


	//If in the analyze process we find a non-ic clause that participates 
	//in the resolution of a learned clause, then it might need to be 
	//allocated in the resolution graph as a remainder parent. This will 
	//take place in the case that the resulting learned clause has at 
	//least one icParent (meaning it's also an ic clause).
	
	//We keep the CRefs and not just the Uids of these clauses so we 
	//could map back every allocated remainder clause back to its current 
	//place in the ClauseAllocator database.
	vec<std::tuple<CRef,int,int>> nonIcResolGraphDeferredAlloc;
	Uid getUid(const Clause& c, CRef confl);

	//Update the lists of parents of the empty clause. The empty clause isn't represented by a 
	//resol node in the resolGraph, and therefore its parents' RefCount isn't normally incremented.
	//Post: All the parents in nextPoEC will have their RefCount incremented by 1.
	//Post: All the parents in prevPoEC will have their RefCount decremented by 1, and will be removed from the graph should their RefCount reach 0.
	void updatePoEC(vec<Uid>& prevPoEC, vec<Uid>& nextPoEC);

	lbool    search           (int nof_conflicts);                                     // Search for a given number of conflicts.
    lbool    solve_           ();                                                      // Main solve method (assumptions given in 'assumptions').
    void     reduceDB         ();                                                      // Reduce the set of learnt clauses.
    void     removeSatisfied  (vec<CRef>& cs);                                         // Called at decision level 0. Shrink 'cs' to contain only non-satisfied clauses.
	void     removeSatisfied_vector(std::vector<CRef>& cs);							   // Called at decision level 0.
    void     rebuildOrderHeap ();

	void allocIcResNode(Clause& cl, CRef cr);
    // Maintaining Variable/Clause activity:
    //
    void     varDecayActivity ();                      // Decay all variables with the specified factor. Implemented by increasing the 'bump' value instead.
    void     varBumpActivity  (Var v, double inc);     // Increase a variable with the current 'bump' value.
    void     varBumpActivity  (Var v);                 // Increase a variable with the current 'bump' value.
    void     claDecayActivity ();                      // Decay all clauses with the specified factor. Implemented by increasing the 'bump' value instead.
    void     claBumpActivity  (Clause& c);             // Increase a clause with the current 'bump' value.

    // Operations on clauses:
    //
    void     attachClause     (CRef cr);               // Attach a clause to watcher lists.
    void     detachClause     (CRef cr, bool strict = false); // Detach a clause to watcher lists.
    void     removeClause     (CRef cr);               // Detach and free a clause.
    bool     locked           (const Clause& c) const; // Returns TRUE if a clause is a reason for some implication in the current state.
    bool     satisfied        (const Clause& c) const; // Returns TRUE if a clause is satisfied in the current state.
	//bool satisfiedInVec(const Clause& c, vec<int>&) const; // Returns TRUE if c has a non-empty intersection with the input vector<Lit>.
	
    void     relocAll         (ClauseAllocator& to);

    // Misc:
    //
    int      decisionLevel    ()      const; // Gives the current decision level.
    uint32_t abstractLevel    (Var x) const; // Used to represent an abstraction of sets of decision levels.
    CRef     reason           (Var x) const;
    int      level            (Var x) const;
    double   progressEstimate ()      const; // DELETE THIS ?? IT'S NOT VERY USEFUL ...
    bool     withinBudget     ()      const;

    // Local Restart
    vec<int> vecConfl;			// conflicts per level counter

    // Glucose restarts
    vec<uint64_t>	decLevInConfl;
    int calculateDecisionLevels(vec<Lit>& cls);

    
    // Static helpers:
    //

    // Returns a random float 0 <= x < 1. Seed must never be 0.
    static inline double drand(double& seed) {
        seed *= 1389796;
        int q = (int)(seed / 2147483647);
        seed -= (double)q * 2147483647;
        return seed / 2147483647; }

    // Returns a random integer 0 <= x < size. Seed must never be 0.
    static inline int irand(double& seed, int size) {
        return (int)(drand(seed) * size); }


};


//=================================================================================================
// Implementation of inline methods:

inline CRef Solver::reason(Var x) const { return vardata[x].reason; }
inline int  Solver::level (Var x) const { return vardata[x].level; }

inline void Solver::insertVarOrder(Var x) {
    if (!order_heap.inHeap(x) && decision[x]) order_heap.insert(x); }

inline void Solver::varDecayActivity() { var_inc *= (1 / var_decay); }
inline void Solver::varBumpActivity(Var v) { varBumpActivity(v, var_inc); }
inline void Solver::varBumpActivity(Var v, double inc) {
    if ( (activity[v] += inc) > 1e100 ) {
        // Rescale:
        for (int i = 0; i < nVars(); i++)
            activity[i] *= 1e-100;
        var_inc *= 1e-100; }

    // Update order_heap with respect to new activity:
    if (order_heap.inHeap(v))
        order_heap.decrease(v); }

inline void Solver::claDecayActivity() { cla_inc *= (1 / clause_decay); }
inline void Solver::claBumpActivity (Clause& c) {
        if ( (c.activity() += cla_inc) > 1e20 ) {
            // Rescale:
            for (int i = 0; i < learnts.size(); i++)
                ca[learnts[i]].activity() *= 1e-20;
            cla_inc *= 1e-20; } }

inline void Solver::checkGarbage(void){ 
	return checkGarbage(garbage_frac); 
}
inline void Solver::checkGarbage(double gf){
    if (ca.wasted() > ca.size() * gf)
        garbageCollect(); 
}

// NOTE: enqueue does not set the ok flag! (only public methods do)
inline bool     Solver::enqueue         (Lit p, CRef from)      { return value(p) != l_Undef ? value(p) != l_False : (uncheckedEnqueue(p, from), true); }
inline bool     Solver::addClause       (const vec<Lit>& ps)    { ps.copyTo(add_tmp); return addClause_(add_tmp); }
inline bool     Solver::addEmptyClause  ()                      { add_tmp.clear(); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p)                 { add_tmp.clear(); add_tmp.push(p); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p, Lit q)          { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); return addClause_(add_tmp); }
inline bool     Solver::addClause       (Lit p, Lit q, Lit r)   { add_tmp.clear(); add_tmp.push(p); add_tmp.push(q); add_tmp.push(r); return addClause_(add_tmp); }
inline bool     Solver::locked          (const Clause& c) const { return value(c[0]) == l_True && reason(var(c[0])) != CRef_Undef && ca.lea(reason(var(c[0]))) == &c; }
inline void     Solver::newDecisionLevel(int conflictC)         { trail_lim.push(trail.size()); vecConfl.push(conflictC);}

inline int      Solver::decisionLevel ()      const   { return trail_lim.size(); }
inline uint32_t Solver::abstractLevel (Var x) const   { return 1 << (level(x) & 31); } // returns 2^(n mod 32) where n==level(x)
inline lbool    Solver::value         (Var x) const   { return assigns[x]; }
inline lbool    Solver::value         (Lit p) const   { return assigns[var(p)] ^ sign(p); }
inline lbool    Solver::modelValue    (Var x) const   { return model[x]; }
inline lbool    Solver::modelValue    (Lit p) const   { return model[var(p)] ^ sign(p); }

//current number of assignments, size of trail
inline int      Solver::nAssigns      ()      const   { return trail.size(); }
inline int      Solver::nClauses      ()      const   { return clauses.size(); }
inline int      Solver::nLearnts      ()      const   { return learnts.size(); }
inline int      Solver::nVars         ()      const   { return vardata.size(); }
inline int      Solver::nFreeVars     ()      const   { return (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]); }
inline void     Solver::setPolarity   (Var v, bool b) { polarity[v] = b; }
inline void     Solver::setDecisionVar(Var v, bool b) 
{ 
    if      ( b && !decision[v]) dec_vars++;
    else if (!b &&  decision[v]) dec_vars--;

    decision[v] = b;
    insertVarOrder(v);
}
inline void     Solver::setConfBudget(int64_t x){ conflict_budget    = conflicts    + x; }
inline void     Solver::setPropBudget(int64_t x){ propagation_budget = propagations + x; }
inline void     Solver::interrupt(){ asynch_interrupt = true; }
inline void     Solver::clearInterrupt(){ asynch_interrupt = false; }
inline void     Solver::budgetOff(){ conflict_budget = propagation_budget = -1; }
inline bool     Solver::withinBudget() const {
    return !asynch_interrupt &&
           (conflict_budget    < 0 || conflicts < (uint64_t)conflict_budget) &&
           (propagation_budget < 0 || propagations < (uint64_t)propagation_budget); }

// FIXME: after the introduction of asynchronous interruptions the solve-versions that return a
// pure bool do not give a safe interface. Either interrupts must be possible to turn off here, or
// all calls to solve must return an 'lbool'. I'm not yet sure which I prefer.
inline bool     Solver::solve         ()                    { budgetOff(); assumptions.clear(); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p)               { budgetOff(); assumptions.clear(); assumptions.push(p); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p, Lit q)        { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); return solve_() == l_True; }
inline bool     Solver::solve         (Lit p, Lit q, Lit r) { budgetOff(); assumptions.clear(); assumptions.push(p); assumptions.push(q); assumptions.push(r); return solve_() == l_True; }
inline bool     Solver::solve         (const vec<Lit>& assumps){ budgetOff(); assumps.copyTo(assumptions); return solve_() == l_True; }
inline lbool    Solver::solveLimited  (const vec<Lit>& assumps){ assumps.copyTo(assumptions); return solve_(); }
inline bool     Solver::okay          ()      const   { return ok; }

inline void     Solver::toDimacs     (const char* file){ vec<Lit> as; toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p){ vec<Lit> as; as.push(p); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q){ vec<Lit> as; as.push(p); as.push(q); toDimacs(file, as); }
inline void     Solver::toDimacs     (const char* file, Lit p, Lit q, Lit r){ vec<Lit> as; as.push(p); as.push(q); as.push(r); toDimacs(file, as); }







//=================================================================================================
// Debug etc:


//=================================================================================================




}

#endif


