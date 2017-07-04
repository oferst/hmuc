/***************************************************************************************[Solver.cc]
Copyright (cr) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (cr) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/

#include <math.h>
#include <algorithm> 
#include "mtl/Sort.h"
#include "core/Solver.h"
#include "utils/System.h"
#include <queue>
#include <unordered_map>
#include <vector>
#include <sstream>
#include <algorithm> 
#include<iostream>
#include<string>
using namespace Minisat;


//=================================================================================================
// Options:


static const char* _cat = "CORE";

static DoubleOption  opt_var_decay         (_cat, "var-decay",   "The variable activity decay factor",            0.95,     DoubleRange(0, false, 1, false));
static DoubleOption  opt_clause_decay      (_cat, "cla-decay",   "The clause activity decay factor",              0.999,    DoubleRange(0, false, 1, false));
static DoubleOption  opt_random_var_freq   (_cat, "rnd-freq",    "The frequency with which the decision heuristic tries to choose a random variable", 0, DoubleRange(0, true, 1, true));
static DoubleOption  opt_random_seed       (_cat, "rnd-seed",    "Used by the random variable selection",         91648253, DoubleRange(0, false, HUGE_VAL, false));
static IntOption     opt_ccmin_mode        (_cat, "ccmin-mode",  "Controls conflict clause minimization (0=none, 1=basic, 2=deep)", 2, IntRange(0, 2));
static IntOption     opt_phase_saving      (_cat, "phase-saving", "Controls the level of phase saving (0=none, 1=limited, 2=full)", 2, IntRange(0, 2));
static BoolOption    opt_rnd_init_act      (_cat, "rnd-init",    "Randomize the initial activity", false);
static BoolOption    opt_luby_restart      (_cat, "luby",        "Use the Luby restart sequence", true);
static IntOption     opt_restart_first     (_cat, "rfirst",      "The base restart interval", 100, IntRange(1, INT32_MAX));
static DoubleOption  opt_restart_inc       (_cat, "rinc",        "Restart interval increase factor", 2, DoubleRange(1, false, HUGE_VAL, false));
static DoubleOption  opt_garbage_frac      (_cat, "gc-frac",     "The fraction of wasted memory allowed before a garbage collection is triggered",  0.20, DoubleRange(0, false, HUGE_VAL, false));
static BoolOption    opt_ic_simplify       (_cat, "ic-simplify", "perform conflict simplification using other ic\n", false);
static IntOption     opt_bind_as_orig      (_cat, "bind-as-orig", "Bind ic clauses that are in muc as originals 0 - no, 1 - only original 2 - all cone\n", 2, IntRange(0,2));
static BoolOption    opt_post_ic_imp       (_cat, "post-ic-imp", "Postpone ic implications\n", true);
static BoolOption    opt_ic_as_dec         (_cat, "ic-as-dec",  "Treat ics as decisions during conflict analysis\n", false);
static BoolOption    opt_full_bck          (_cat, "full-bck",  "If backtrack to the end of original confl or new\n", true);
static BoolOption    opt_dec_l1            (_cat, "dec-l1",  "If to decide l1 or l2 (where l1 is 1UIP of first analyze and l2 is 1UIP where ic as dec)\n", true);
static BoolOption    opt_local_restart     (_cat, "local-restart", "Use local restart", true);
static BoolOption    opt_glucose           (_cat, "glucose", "use glucose deletion strategy", true);
static IntOption     opt_only_from         (_cat, "from-call", "start the optimization only from n-th operation", 2, IntRange(0, 100000));
static IntOption     opt_only_from_2       (_cat, "from-call_2", "start the optimization only from n-th operation", 20, IntRange(0, 100000));
static BoolOption    opt_use_clauses       (_cat, "use-clauses", "count from using clauses instead of sat calls for opt_only_from and opt_only_from2", false);
static IntOption     opt_max_fcls_in_arow  (_cat, "max-false-in-a-row", "Max number of times to run path falsification in a row (0 - no limit)", 0, IntRange(0,INT32_MAX)); 
static BoolOption    opt_lpf_cutoff        (_cat, "lpf-cutoff", "stop literal-based path-falsification if seems to be too costly", true);
static IntOption     opt_pf_delay          (_cat, "pf-delay", "delay activation of path-falsification until that many restarts", 0);
static IntOption     opt_pf_mode		   (_cat, "pf-mode", "{0-none, 1 - ic clause only, 2 - path-falsification (pf), 3-literal-based pf (lpf), 4 - lpf inprocess};", 4, IntRange(0,4));
static BoolOption    opt_test			   (_cat, "test", "test that the core is indeed unsat", false);
static BoolOption    opt_reverse_pf		   (_cat, "reverse-pf", "reverse order of lpf literals\n", false);
static BoolOption    opt_always_prove      (_cat, "always_prove", "prevent early termination due to assumptions; instead run proof to completion", true);
static IntOption     opt_pf_z_budget	   (_cat, "pf_z_budget", "# of restarts we budget for building a proof in case we already know it is unsat", 40, IntRange(-1,4000));
static BoolOption    opt_pf_reset_z_budget (_cat, "pf_reset_z_budget", "upon detection of unsat by assumptions, resets zombie-budget", false); 
//Multi Module Options
static const char* _mul = "MUL";
static BoolOption	 opt_blm_rebuild_proof(_mul, "blm-rebuild-proof",
	"following backbone literal mining (BLM), will generate a resolution proof of unsat, whether or not assumptions were used to deduce unsat of the formula", false);
//=================================================================================================

//=================================================================================================
// Constructor/Destructor:

uint32_t Clause::icUid = 0;

Solver::Solver() :

    // Parameters (user settable):
    //
  m_nSatCall(0), m_nUnsatPathFalsificationCalls(0)
  , verbosity        (1)
  , var_decay        (opt_var_decay)
  , clause_decay     (opt_clause_decay)
  , random_var_freq  (opt_random_var_freq)
  , random_seed      (opt_random_seed)
  , luby_restart     (opt_luby_restart)
  , ccmin_mode       (opt_ccmin_mode)
  , phase_saving     (opt_phase_saving)
  , rnd_pol          (false)
  , rnd_init_act     (opt_rnd_init_act)
  , garbage_frac     (opt_garbage_frac)
  , restart_first    (opt_restart_first)
  , restart_inc      (opt_restart_inc)
  , pf_mode			 (opt_pf_mode)
  , blm_rebuild_proof (opt_blm_rebuild_proof)
  , test_result		 (opt_test)
      // Parameters (the rest):
    //
  , learntsize_factor((double)1/(double)3), learntsize_inc(1.1)

    // Parameters (experimental):
    //
  , learntsize_adjust_start_confl (100)
  , learntsize_adjust_inc         (1.5)

    // Statistics: (formerly in 'SolverStats')
    //
  , solves(0), starts(0), decisions(0), rnd_decisions(0), propagations(0), conflicts(0)
  , dec_vars(0), clauses_literals(0), learnts_literals(0), max_literals(0), tot_literals(0)

  , m_bConeRelevant    (false)
  , ok                 (true)
  , cla_inc            (1)
  , var_inc            (1)
  , watches            (WatcherDeleted(ca))
  , qhead              (0)
  , simpDB_assigns     (-1)
  , simpDB_props       (0)
  , order_heap         (VarOrderLt(activity))
  , progress_estimate  (0)
  , remove_satisfied   (true)
  , count_true_assump  (0)
  ,  count_assump	   (0)
    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)  

  , nICtoRemove (0)
{
    vecConfl.push(0);
}


Solver::~Solver()
{
}


//=================================================================================================
// Minor methods:


// Creates a new SAT variable in the solver. If 'decision' is cleared, variable will not be
// used as a decision variable (NOTE! This has effects on the meaning of a SATISFIABLE result).
//
Var Solver::newVar(bool sign, bool dvar)
{
    int v = nVars();
    watches  .init(mkLit(v, false));
    watches  .init(mkLit(v, true ));
    assigns  .push(l_Undef);
    vardata  .push(mkVarData(CRef_Undef, 0));
    //activity .push(0);
    activity .push(rnd_init_act ? drand(random_seed) * 0.00001 : 0);
    seen     .push(0);
    polarity .push(sign);
    decision .push();
    trail    .capacity(v+1);
    setDecisionVar(v, dvar);
    return v;
}

bool Solver::addClause_(vec<Lit>& ps, bool ic, vec<uint32_t>* icParentsPtr)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
	//printf("a ");
    sort(ps);
    Lit p; int i, j;
    for (i = j = 0, p = lit_Undef; i < ps.size(); i++)
        if (value(ps[i]) == l_True || ps[i] == ~p)
            return true;
        else if (value(ps[i]) != l_False && ps[i] != p)
            ps[j++] = p = ps[i];
    ps.shrink(i - j);

    CRef cr;
    if (ps.size() == 0)
    {
        return ok = false;
    }
    if (ps.size() == 1){
        if (ic) 
        {
            cr = ca.alloc(ps, false, true);
            icUnitClauses.push(cr);
        }
        else
        {
            uncheckedEnqueue(ps[0]);
            return ok = (propagate() == CRef_Undef);
        }
    }else{
        cr = ca.alloc(ps, false, ic);

        clauses.push(cr);
        attachClause(cr);
    }

    if (ic) {
        resolGraph.AddNewResolution(ca[cr].uid(), cr, ((icParentsPtr == NULL) ? icParents : *icParentsPtr));
    }

    return true;
}

void Solver::attachClause(CRef cr) {
	//if (ca[cr].uid() == 368608) {
	//	//printf("%d attaching cr=%d\n", ca[cr].uid(), cr);
	//	printClause(ca[cr], std::to_string(ca[cr].uid()) + " attaching w. cr " + std::to_string(cr));
	//}
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }

void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    
    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
		if (cr == 86642) {
			printf("%d (uid for %d)\n", ca[cr].uid(), cr);
			//printClause(ca[cr], "detaching");
			printf("detaching %d size:%d\n", cr, c.size());
		}
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
		//if (c.uid() == 368608) {
		//	printf("smudeged\n");
		//	printf("%d\n", todimacsLit(c[0]));
		//}

        watches.smudge(~c[1]);
		//if (c.uid() == 368608) {
		//	printf("smudeged\n");
		//	printf("%d\n", todimacsLit(c[1]));
		//}
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }

void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];
	if (c.size() > 1 && c.mark() != 1) {
		detachClause(cr);
	}
    // Don't leave pointers to freed memory!
    if (locked(c)) 
		vardata[var(c[0])].reason = CRef_Undef;

	if (c.ic() && c.mark() != 2) {
		resolGraph.DeleteClause(c.uid());
	}

	c.mark(1);
	ca.free(cr);

//if (c.ic()) {
//	uint32_t uid = c.uid();
//	std::unordered_map<uint32_t,vec<Lit>*>& icDelayed = resolGraph.icDelayedRemoval;
//	if (icDelayed.find(uid) == icDelayed.end()) {
//		vec<Lit>* litVec = new vec<Lit>();
//		for (int i = 0; i < c.size(); ++i)
//			litVec->push(c[i]);
//		icDelayed[uid] = litVec;
//	}
//}




}

bool Solver::satisfied(const Clause& c) const {
	for (int i = 0; i < c.size(); i++) {
		if (value(c[i]) == l_True)
			return true;
	}
	return false;
}


// Revert to the state at the given level (keeping all assignment at 'level' but not beyond).
void Solver::cancelUntil(int level) {
	if (decisionLevel() > level) {
		for (int c = trail.size() - 1; c >= trail_lim[level]; c--) {
			Var      x = var(trail[c]);
			assigns[x] = l_Undef;
			if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
				polarity[x] = sign(trail[c]);
			insertVarOrder(x);
		}
		qhead = trail_lim[level];
		trail.shrink(trail.size() - trail_lim[level]);
		vecConfl.shrink(trail_lim.size() - level);
		trail_lim.shrink(trail_lim.size() - level);
	}
}

//=================================================================================================
// Major methods:

Lit Solver::pickBranchLit()
{
	Var next = var_Undef;

	// Random decision:
	if (drand(random_seed) < random_var_freq && !order_heap.empty()) {
		next = order_heap[irand(random_seed, order_heap.size())];
		if (value(next) == l_Undef && decision[next])
			rnd_decisions++;
	}

	// Activity based decision:
	while (next == var_Undef || value(next) != l_Undef || !decision[next])
		if (order_heap.empty()) {
			next = var_Undef;
			break;
		}
		else
			next = order_heap.removeMin();

	return next == var_Undef ? lit_Undef : mkLit(next, rnd_pol ? drand(random_seed) < 0.5 : polarity[next]);
}


/*_________________________________________________________________________________________________
|
|  analyze : (confl : Clause*) (out_learnt : vec<Lit>&) (out_btlevel : int&)  ->  [void]
|
|  Description:
|    Analyze conflict and produce a reason clause.
|
|    Pre-conditions:
|      * 'out_learnt' is assumed to be cleared.
|      * Current decision level must be greater than root level.
|
|    Post-conditions:
|      * 'out_learnt[0]' is the asserting literal at level 'out_btlevel'.
|      * If out_learnt.size() > 1 then 'out_learnt[1]' has the greatest decision level of the
|        rest of literals. There may be others from the same level though.
|
|________________________________________________________________________________________________@*/
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, vec<uint32_t>& icParents, vec<uint32_t>& remParents, vec<uint32_t>& allParents)
{
	int pathC = 0;
	Lit p = lit_Undef;

	// Generate conflict clause:
	//
	out_learnt.push();      // (leave room for the asserting literal)
	int index = trail.size() - 1;

	vec<CRef> nonIcParentsCRefs;
	vec<CRef> allParentsCRefs;

	do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)



        Clause& c = ca[confl];
        if (c.learnt() && !opt_glucose)
            claBumpActivity(c);

		if (c.ic())  icParents.push(c.uid());
		
		if (opt_blm_rebuild_proof) {
			if (!c.ic())
				nonIcParentsCRefs.push(confl);
			allParentsCRefs.push(confl);
		}
			
        for (int j = (p == lit_Undef) ? 0 : 1; j < c.size(); j++){
            Lit q = c[j];

            if (!seen[var(q)] && level(var(q)) > 0){
                varBumpActivity(var(q));

                seen[var(q)] = 1;
                if (level(var(q)) >= decisionLevel())
                    pathC++;
                else
                    out_learnt.push(q);
            }
        }

	

        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        p     = trail[index+1];
        confl = reason(var(p));
        seen[var(p)] = 0;
        pathC--;

    }while (pathC > 0);
    out_learnt[0] = ~p;



	if (opt_blm_rebuild_proof && 0 < icParents.size()) {
		int j, k;
		for (int i = j = k = 0; i < allParentsCRefs.size(); ++i) {
			CRef cr = allParentsCRefs[i];
			uint32_t uid;
			if (j<nonIcParentsCRefs.size() && nonIcParentsCRefs[j] == cr) {
				Clause& c = ca[cr];
				j++;
				if (!c.ic() && !c.isParentToIc()) {
					c.setIsParentToIc(true);
					//if (c.uid() == 368608) {
					//	//printf("%d rem to add %d\n", c.uid(), cr);
					//	printClause(c, std::to_string(c.uid()) + " rem node found w. cr "+ std::to_string(cr));
					//}
					resolGraph.AddRemainderResolution(c.uid(), cr);
					setGood.insert(c.uid());
				}
				uid = c.uid();
				remParents.push(uid);
			}
			else {
				uid = icParents[k++];
			}
			allParents.push(uid);
		}
	}

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

		for (i = j = 1; i < out_learnt.size(); i++) {
			if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level, icParents,allParents)) {
				out_learnt[j++] = out_learnt[i];
			}
		}
    }else if (ccmin_mode == 1){
        for (i = j = 1; i < out_learnt.size(); i++){
            Var x = var(out_learnt[i]);

            if (reason(x) == CRef_Undef)
                out_learnt[j++] = out_learnt[i];
            else{
                Clause& c = ca[reason(var(out_learnt[i]))];
                for (int k = 1; k < c.size(); k++)
                    if (!seen[var(c[k])] && level(var(c[k])) > 0){
                        out_learnt[j++] = out_learnt[i];
                        break; }
            }
        }
    } else
        i = j = out_learnt.size();

    max_literals += out_learnt.size();
    out_learnt.shrink(i - j);
    tot_literals += out_learnt.size();

    // Find correct backtrack level:
    //
    if (out_learnt.size() == 1)
        out_btlevel = 0;
    else{
        int max_i = 1;
        // Find the first literal assigned at the next-highest level:
        for (int i = 2; i < out_learnt.size(); i++)
            if (level(var(out_learnt[i])) > level(var(out_learnt[max_i])))
                max_i = i;
        // Swap-in this literal at index 1:
        Lit p             = out_learnt[max_i];
        out_learnt[max_i] = out_learnt[1];
        out_learnt[1]     = p;
        out_btlevel       = level(var(p));
    }

    for (int j = 0; j < analyze_toclear.size(); j++) seen[var(analyze_toclear[j])] = 0;    // ('seen[]' is now cleared)

}


// Check if 'p' can be removed. 'abstract_levels' is used to abort early if the algorithm is
// visiting literals at levels that cannot be removed later.
bool Solver::litRedundant(Lit p, uint32_t abstract_levels, vec<uint32_t>& icParents, vec<uint32_t>& allParents)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    int icTop = icParents.size();
	int parentsTop = allParents.size();
    while (analyze_stack.size() > 0){
        Var v = var(analyze_stack.last());
        assert(reason(v) != CRef_Undef);
        Clause& c = ca[reason(v)]; analyze_stack.pop();
        if (!opt_ic_simplify && (c.ic())) { // don't perform simplification on ics - and c is an ic so we stop here
            for (int j = top; j < analyze_toclear.size(); j++)
                seen[var(analyze_toclear[j])] = 0;
            analyze_toclear.shrink(analyze_toclear.size() - top);
            icParents.shrink(icParents.size() - icTop);
			if(opt_blm_rebuild_proof)
				allParents.shrink(allParents.size() - parentsTop);
            return false;
        }
        else if (c.ic())
        {
            icParents.push(c.uid());
			if (opt_blm_rebuild_proof)
				allParents.push(c.uid());
        }
		else if (opt_blm_rebuild_proof && c.isParentToIc())
			allParents.push(c.uid());

        for (int i = 1; i < c.size(); i++){
            Lit p  = c[i];
            if (!seen[var(p)] && level(var(p)) > 0){
                if (reason(var(p)) != CRef_Undef && (abstractLevel(var(p)) & abstract_levels) != 0){
                    seen[var(p)] = 1;
                    analyze_stack.push(p);
                    analyze_toclear.push(p);
                }else{
                    for (int j = top; j < analyze_toclear.size(); j++)
                        seen[var(analyze_toclear[j])] = 0;
                    analyze_toclear.shrink(analyze_toclear.size() - top);
                    icParents.shrink(icParents.size() - icTop);
					if (opt_blm_rebuild_proof)
						allParents.shrink(allParents.size() - parentsTop);
                    return false;
                }
            }
        }
    }

    return true;
}


/*_________________________________________________________________________________________________
|
|  analyzeFinal : (p : Lit)  ->  [void]
|  
|  Description:
|    Specialized analysis procedure to express the final conflict in terms of assumptions.
|    Calculates the (possibly empty) set of assumptions that led to the assignment of 'p', and
|    stores the result in 'out_conflict'.
|________________________________________________________________________________________________@*/
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict) {
    out_conflict.clear();
    out_conflict.push(p);
    if (decisionLevel() == 0)
        return;
    seen[var(p)] = 1;
    for (int i = trail.size()-1; i >= trail_lim[1]; i--) {
        Var x = var(trail[i]);
        if (seen[x]) {
            if (reason(x) == CRef_Undef) {
                assert(level(x) > 1);
                out_conflict.push(~trail[i]);
            } 
			else {
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 1)
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{

    assert(value(p) == l_Undef);
	//if (verbosity == 1) {
	//	if (from != CRef_Undef) {
	//		printf("enq %d = %d\n", todimacsLit(p), lbool(!sign(p)));
	//		printClause(ca[from], "reason");
	//	}
	//	else
	//		printf("enq %d = %d, reason uid = Undef\n", todimacsLit(p), lbool(!sign(p)));
	//}
    assigns[var(p)] = lbool(!sign(p));
    vardata[var(p)] = mkVarData(from, decisionLevel());
    trail.push_(p);
}


/*_________________________________________________________________________________________________
|
|  propagate : [void]  ->  [Clause*]
|  
|  Description:
|    Propagates all enqueued facts. If a conflict arises, the conflicting clause is returned,
|    otherwise CRef_Undef.
|  
|    Post-conditions:
|      * the propagation queue is empty, even if there was a conflict.
|________________________________________________________________________________________________@*/
CRef Solver::propagate()
{
    CRef    confl     = CRef_Undef;
    int     num_props = 0;
    watches.cleanAll();
    icImpl.clear();
    int icImplId = 0;
	//if (verbosity == 1)
	//	printf("prop #l %d", learnts.size());
		//if (verbosity == 1 && propagations == 50594638) {
		//	uint32_t uid = 368021;
		//	CRef crFromUid = GetClauseIndFromUid(uid);
		//	if (CRef_Undef != crFromUid) {
		//		printClause(ca[crFromUid], "CLAUSE uid " + std::to_string(uid) + "\n");

		//	}

		//	else
		//		printf("cluase uid %d not found\n", uid);
		//	int j = 0;
		//	int decision = 0;
		//	for (int i = 0; i < trail.size(); ++i) {
		//		if (i == trail_lim[j])
		//			printf("decision level %d starts at trail idx %d\n", decision++, trail_lim[j++]);
		//		printf("lit: %d\n", todimacsLit(trail[i]));
		//	}
		//}
    for (;;) 
	{
        while (qhead < trail.size()){
            Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
            vec<Watcher>&  ws  = watches[p];
            Watcher        *i, *j, *end;
            num_props++;
			//if (verbosity == 1 && propagations == 50594638) {


			//	CRef cr = reason(var(p));
			//	//printf("p=%d, reason=%d\n", todimacsLit(p), reason(var(p)));
			//	//if (cr != CRef_Undef)
			//	//	printClause(ca[cr], "reason uid " + std::to_string(ca[cr].uid()));
			//	//printf("\n");
			//}
            for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
                // Try to avoid inspecting the clause:
                Lit blocker = i->blocker;
                if (value(blocker) == l_True){
                    *j++ = *i++; continue; }

                // Make sure the false literal is data[1]:
                CRef     cr        = i->cref;
                Clause&  c         = ca[cr];
			
                Lit      false_lit = ~p;
                if (c[0] == false_lit)
                    c[0] = c[1], c[1] = false_lit;
                assert(c[1] == false_lit);
                i++;

                // If 0th watch is true, then clause is already satisfied.
                Lit     first = c[0];
                Watcher w     = Watcher(cr, first);
                if (first != blocker && value(first) == l_True){
                    *j++ = w; continue; }

                // Look for new watch:
                for (int k = 2; k < c.size(); k++)
                    if (value(c[k]) != l_False){
                        c[1] = c[k]; c[k] = false_lit;
                        watches[~c[1]].push(w);
                        goto NextClause; }

                // Did not find watch -- clause is unit under assignment:
                *j++ = w;
                if (value(first) == l_False){
                        confl = cr;
                        qhead = trail.size();
                        // Copy the remaining watches:
                        while (i < end)
                            *j++ = *i++;
                }
                else
                {
                    if ((decisionLevel() == 0) && (c.ic() || c.isParentToIc()))
                    {
                        add_tmp.clear();
                        add_tmp.push(first);
                        uint32_t uid = c.uid();
                        // after allocating new clause cr cannot be used because of possible memory relocation
                        CRef newCr = ca.alloc(add_tmp, false, c.ic(),c.isParentToIc());
                        Clause::DecreaseUid();
                        ca[newCr].uid() = uid;
                        ca[cr].mark(2);
                        removeClause(cr);
                        resolGraph.UpdateClauseRef(uid, newCr);
                        icUnitClauses.push(newCr);
                    }
                    else
                    {
                        if (opt_post_ic_imp && c.ic())
                        {
                            icImpl.push();
                            Map<Lit, CRef>::Pair& pair = icImpl.last();
                            pair.key = first;
                            pair.data = cr;
                        }
                        else
                            uncheckedEnqueue(first, cr);
                    }
                }

            NextClause:;
            }
            ws.shrink(i - j);
        }

        if (confl != CRef_Undef || icImplId == icImpl.size())
            break;
        else
        {
            while (icImplId != icImpl.size())
            {
                Map<Lit, CRef>::Pair& pair = icImpl[icImplId++];
                if (value(pair.key) == l_Undef)
                {
                    uncheckedEnqueue(pair.key, pair.data);
                    break;
                }
                else if (value(pair.key) == l_False)
                {
                    confl = pair.data;
                    break;
                }
            }
        }
    }
    propagations += num_props;
    simpDB_props -= num_props;
	//if (verbosity == 1)
	//	printf("%d\n", propagations);
    return confl;
}


/*_________________________________________________________________________________________________
|
|  reduceDB : ()  ->  [void]
|  
|  Description:
|    Remove half of the learnt clauses, minus the clauses locked by the current assignment. Locked
|    clauses are clauses that are reason to some assignment. Binary clauses are never removed.
|________________________________________________________________________________________________@*/
struct reduceDB_lt { 
    ClauseAllocator& ca;
    reduceDB_lt(ClauseAllocator& ca_) : ca(ca_) {}
    bool operator () (CRef x, CRef y) { 
        // First criteria 
        if(ca[x].size() > 2 && ca[y].size()==2) return 1;

        if(ca[y].size()>2 &&  ca[x].size() ==2) return 0;
        if(ca[x].size() ==2 && ca[y].size()==2) return 0;

        // Second one
        if(ca[x].activity()> ca[y].activity()) return 1;
        if(ca[x].activity()< ca[y].activity()) return 0;    

        return ca[x].size() < ca[y].size();
    }};

// a slightly optimized version of the minisat version. 
void Solver::reduceDB()
{
	int     i, j;
	double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

	std::nth_element(learnts.begin(), learnts.begin() + (learnts.size() / 2), learnts.end(), reduceDB_lt(ca)); // ceil(learnts.size() / 2)

	
	// We do not delete binary or locked clauses. From the rest, we delete clauses from the first half
	// and clauses with activity smaller than 'extra_lim'.
	
	int middle = learnts.size() / 2;
	for (i = j = 0; i < middle; i++) {
		CRef cr = learnts[i];
		const Clause& c = ca[cr];
		if (c.mark() == 0 && c.size() > 2 && !locked(c)) {
			removeClause(cr);
			//if (verbosity == 1)
				//printf("removed1 uid %d\n", c.uid());
		}
		else
			if (c.mark() != 1) {
				learnts[j++] = cr;

			}
	}

	// now the 2nd half (with higher activity). Note that we do not reset i,j.
	// Optimization: We choose one of two loops, depending on the activity value of the middle clause in the list. 
	// Recall that all clauses in the 2nd half (that have size > 2) have activity at least as high as this middle clause (ca[learnts[i]]), 
	// owing to nth_element (or sort) above, and will therefor falsify the condition "cr.activity() < extra_lim" below.
	// Hence no point checking this condition if the following if statement is false. 
	if (ca[learnts[i]].activity() < extra_lim) { // if this condition holds, we will check the activity of the other clauses.
		for (; i < learnts.size(); i++) { // now the 2nd half (with higher activity)
			CRef cr = learnts[i];
			const Clause& c = ca[cr];
			if (c.mark() == 0 && c.size() > 2 && !locked(c) && c.activity() < extra_lim) {
				removeClause(cr);
				//if (verbosity == 1)
					//printf("removed2 uid %d\n", c.uid());
			}
			else
				if (c.mark() != 1) {
					learnts[j++] = cr;

				}
		}
	}
	else { // note that the code below is the same as the above 'else'. We get here if we know that this else will always be taken.
		for (; i < learnts.size(); i++) { // now the 2nd half (with higher activity)
			const Clause& c = ca[learnts[i]];
				//if (verbosity == 1)
				//	printf("c.uid() %d ,mark = %d\n", c.uid(),c.mark());
			if (c.mark() != 1) {
				learnts[j++] = learnts[i];
			}
		}
	}

	int nDelElems = i - j;
	assert(nDelElems <= learnts.size()); 

	for (int i = 0; i < nDelElems; i++) 
		learnts.pop_back();

    
	checkGarbage();
    resolGraph.CheckGarbage();
}


void Solver::removeSatisfied_vector(std::vector<CRef>& cs)
{
	int i, j;
	for (i = j = 0; i < cs.size(); i++) {
		Clause& c = ca[cs[i]];
		if (c.mark() == 1)
			continue;
		if (c.mark() != 2 && satisfied(c)) { //oferg: we already checked that c.mark() != 1 at this point. Can only be c.mark() == 0? If so, than marking it as 0 again seems redundnet.
			if (verbosity == 1 && c.uid() == 369119)
				printf("removeSatisfied_vector %d\n", c.uid());
			c.mark(0);
			removeClause(cs[i]);
		}
		else //oferg: c.mark() == 2 or !satisfied(c)
			cs[j++] = cs[i];
	}
	int nelems = i - j;
	assert(nelems <= cs.size()); 
	for (int i = 0; i < nelems; i++) 
		cs.pop_back();
}

void Solver::removeSatisfied(vec<CRef>& cs)
{
    int i, j;
    for (i = j = 0; i < cs.size(); i++){
        Clause& c = ca[cs[i]];
        if (c.mark() == 1)
            continue;
        if (c.mark() != 2 && satisfied(c))
        {
			if (verbosity == 1 && c.uid() == 369119)
				printf("removeSatisfied %d\n", c.uid());
            c.mark(0);
			removeClause(cs[i]);
        }
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
}

void Solver::rebuildOrderHeap()
{
    vec<Var> vs;
    for (Var v = 0; v < nVars(); v++)
        if (decision[v] && value(v) == l_Undef)
            vs.push(v);
    order_heap.build(vs);
}

/*_________________________________________________________________________________________________
|
|  simplify : [void]  ->  [bool]
|  
|  Description:
|    Simplify the clause database according to the current top-level assigment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);

    if (!ok || propagate() != CRef_Undef)
        return ok = false; //illegal state at decision level 0 (dl 0): either there was a previous error (!ok) or propagation at dl 0 found a contradicition.

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:

	removeSatisfied_vector(learnts);

    if (remove_satisfied)        // Can be turned off.    
      removeSatisfied(clauses);
    removeSatisfied(icUnitClauses);
    checkGarbage();
    resolGraph.CheckGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}


template<typename T>
static void printfVec(T& v, char *msg) {
	if (v == NULL) printf("NULL\n");
	printf("%s (", msg);	
	for (int i = 0; i < v.size(); ++i) {
		printf("%d ", v[i]);
	}
	printf(")\n");
}

bool Solver::pf_early_unsat_terminate() { // default is true
	if ((opt_always_prove && (pf_zombie_iter <= opt_pf_z_budget)) 
		//|| 	(opt_max_fcls_in_arow && (++m_nUnsatPathFalsificationCalls == opt_max_fcls_in_arow))    // false by default anyway
		) { 
		pf_active = false;
		pf_zombie = true; // from here on we know already that it is unsat because we found a contradiction with the pf_literals, but we continue in order to get a proof.
		if (opt_pf_reset_z_budget) pf_zombie_iter = 0; 
		m_nUnsatPathFalsificationCalls = 0;
		return false;	
	}	
	m_bUnsatByPathFalsification = true;
	nUnsatByPF++;
	m_bConeRelevant = false; // since we reached a contradiction based on assumptions, we cannot use the cone, i.e., the cone includes facts (e.g. -cr) that were added owing to a meta-argument (path-falsification), but we cannot extract an accurate core from this without an additional SAT run. 		
	return true;
}



/*_________________________________________________________________________________________________
|
|  search : (nof_conflicts : int) (params : const SearchParams&)  ->  [lbool]
|  
|  Description:
|    Search for a model the specified number of conflicts. 
|    NOTE! Use negative value for 'nof_conflicts' indicate infinity.
|  
|  Output:
|    'l_True' if a partial assignment that is consistent with respect to the clauseset is found. If
|    all variables are decision variables, this means that the clause set is satisfiable. 'l_False'
|    if the clause set is unsatisfiable. 'l_Undef' if the bound on number of conflicts is reached.
|________________________________________________________________________________________________@*/
lbool Solver::search(int nof_conflicts)
{

    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    starts++;
    CRef confl = CRef_Undef;
    icParents.clear();
	if (opt_blm_rebuild_proof) {
		allParents.clear();
		remParents.clear();
	}
	int prev_trail_size = 0;	
	int old_falsified_literals;
	
	//if (verbosity == 1)
	//	printf("nof_conflicts %d\n", nof_conflicts);
	//int iii = 0;
	for (;;){
		if (asynch_interrupt) {
			return l_Undef;
		}

#pragma region dec_level_0

		
		if (decisionLevel() == 0) {
            // SimnonIcParentsplify the set of problem clauses:
            if (!simplify()) {
				// if we got here, it means that we found a contradiction regarless of the ICs, 
				// which means it's over. We clear parents_of_empty_clause because there is 
				// one more call to getUnsatcore which uses it.
				parents_of_empty_clause.clear(); // hack. 

                return l_False;
            }

			if (!test_mode && !pf_zombie && resolGraph.GetClauseRef(nICtoRemove) == CRef_Undef) { // this can happen if simplify removes the clause at level 0; 
				if (verbosity == 1) printf("root removed by simplify. Early unsat\n");
				if (pf_early_unsat_terminate()) {
					return l_False;
				}
			}

            newDecisionLevel(conflictC);  // from now we are at decision level 1.

            for (int nInd = 0; nInd < icUnitClauses.size(); ++nInd)
            {
                Clause& c = ca[icUnitClauses[nInd]];
                if (c.mark() != 0) // marked as 0 by default. 1 - if we are not allowed to use it because it is part of the cone of the clause that is currently removed. 
                    continue;
                Lit lit = c[0];
                if (value(lit) == l_False)
                {
                    confl = icUnitClauses[nInd];
                    break;
                }
                else if (value(lit) == l_True)
                {
                    continue;
                }

                uncheckedEnqueue(lit, icUnitClauses[nInd]);
				//if (verbosity == 1) {
				//	printf("enqueuing unit lit %d\n", todimacsLit(lit));
				//}
                confl = propagate();
                if (confl != CRef_Undef)
                    break;
            }									

        }



		if ( 
				pf_active && 	// delay
				pf_mode == lpf_inprocess &&
				// nICtoRemove > 0 && !test_mode &&
				confl == CRef_Undef && 					
				decisionLevel() == 1 &&
				(
					(m_bConeRelevant && (trail.size() > pf_prev_trail_size)) || 
					LiteralsFromPathFalsification.size() == 0  // if !m_bConeRelevant, then we only want to call compute_inprocess once, because the result is not changing. 
				)    				
		   )			 
		{
			
			if (lpf_compute_inprocess() == false) {
				return l_False; // early termination

			}

			//else printClause(LiteralsFromPathFalsification, "lpf computed");
		}
		

						

#pragma endregion
        if (confl == CRef_Undef)
            confl = propagate();
		
		

#pragma region conflict_case
		if (confl != CRef_Undef) {

				//printClause(ca[confl], "\ncurr conflict");


            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 1) { // a core based on interesting constraints. 
                findConflictICReasons(confl);

                return l_False;
            }

            if (decisionLevel() == 0) // a core without interesting constraints (only remainder clauses, which are those clauses that were already marked as being in the core); in the next step the core will be empty, so the process should terminate.
            {

                return l_False;  
            }

            learnt_clause.clear();
			
            analyze(confl, learnt_clause, backtrack_level, icParents,remParents,allParents);

			//oferg: This code is used only for an optimization we don't normally use 
			if (opt_ic_as_dec && learnt_clause.size() > 1 && icParents.size() > 0 && !ca[confl].ic()) {
                
				int index = trail.size() - 1;
                Lit l = trail[index];
                int dLevel = decisionLevel() + 1;
                // create a new decision level till ic clause
                while(!ca[reason(var(l))].ic())  {
                    // now we are going to learn a new 
                    vardata[var(l)].level = dLevel;
                    l = trail[--index];
                }

                vardata[var(l)].level = dLevel;
                vardata[var(l)].reason = CRef_Undef;
                trail_lim.push(index);
                vecConfl.push(conflictC);
                l = learnt_clause[0];
                learnt_clause.clear();
                int bckTrack = 0;
				printf("222\n");
                analyze(confl, learnt_clause, bckTrack, icParents,remParents,allParents);
                CRef cr = ca.alloc(learnt_clause, true, false);

				learnts.push_back(cr);
                attachClause(cr);
                if (!opt_glucose)
                    claBumpActivity(ca[cr]);
                else
                    ca[cr].activity() = calculateDecisionLevels(learnt_clause);
                cancelUntil(opt_full_bck ? backtrack_level : dLevel-2);
                newDecisionLevel(conflictC);
                uncheckedEnqueue(opt_dec_l1 ? l : learnt_clause[0]);
            }
            
			
			else { //oferg: This is the defualt case
				if (learnt_clause.size() == 1) { //oferg: learnt  unit clause
					if (icParents.size() > 0) {//oferg: and it's dependents on some ics

						//oferg: than we always add them to the resolGraph
						cancelUntil(1);
						CRef cr = ca.alloc(learnt_clause, false, true);
						icUnitClauses.push(cr);//oferg: using this instead of 'learnts' vec, will never delete this unit?

						Clause& cl = ca[cr];

						updateResolutionGraph(cl, cr);
						
						uncheckedEnqueue(learnt_clause[0], cr);
					 }
					else {//oferg: Otherwise just add the unit clause to BCP queue
						assert(backtrack_level == 0);
						cancelUntil(0);
						uncheckedEnqueue(learnt_clause[0]);
					}
				}
				else { //oferg: learnt clause is not a unit clause
					cancelUntil(backtrack_level);
					CRef cr = ca.alloc(learnt_clause, true, icParents.size() > 0);

					learnts.push_back(cr);
					attachClause(cr);
					Clause& cl = ca[cr];

					if (!opt_glucose)
						claBumpActivity(ca[cr]);
					else
						ca[cr].activity() = calculateDecisionLevels(learnt_clause);
					if (cl.ic()) {
						updateResolutionGraph(cl, cr);
					}
					uncheckedEnqueue(learnt_clause[0], cr);
				}
            }

            varDecayActivity();
            if (!opt_glucose)
                claDecayActivity();

            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;

                if (verbosity > 1)
                    printf("c | %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

            icParents.clear();
			if (opt_blm_rebuild_proof) {
				allParents.clear();
				remParents.clear();
			}
            confl = CRef_Undef;




        }
#pragma endregion

#pragma region no_conflict_case
		else {   // NO CONFLICT 
			//if (verbosity == 1) {
			//	printf("--- no conflict start ---\n");
			//	//for (int i = 0; i < trail.size(); ++i) {
			//	//	printf("%d\n", trail[i]);
			//	//}
			//	printf("--- no conflict end ---\n");
			//}
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts &&
                (!opt_local_restart || (conflictC - vecConfl[decisionLevel()]) >= nof_conflicts) || 
                !withinBudget()) { // Reached bound on number of conflicts:
				if (pf_zombie) {
					if (verbosity == 1) printf("Z ");
					if (++pf_zombie_iter > opt_pf_z_budget) { // magic cutoff number. We spent too much time at trying to rebuild a proof; instead we'll declare it unsat and do not reuse the cone.
						m_bUnsatByPathFalsification = true;
						nUnsatByPF++;
						m_bConeRelevant = false;
						return l_False;
					}
				}

				else if (verbosity == 1) printf("R ");
                progress_estimate = progressEstimate();				
                cancelUntil(1);
                return l_Undef; 
            }

			if ((int)(learnts.size()) - nAssigns() >= max_learnts) {
				//if (verbosity == 1)
				//	printf("reduceDB: learnts.size() before = %d\n", learnts.size());

				reduceDB();  // Reduce the set of learnt clauses:
				//if (verbosity == 1)
				//	printf("reduceDB: learnts.size() after = %d\n", learnts.size());
			}

            Lit next = lit_Undef;

			if (pf_active) {
				while (decisionLevel() - 1 < LiteralsFromPathFalsification.size()) { // literals in LiteralsFromPathFalsification are made assumptions
					count_assump++;
					Lit p = ~LiteralsFromPathFalsification[decisionLevel() - 1]; 
					if (value(p) == l_True)  { // literal already implied by previous literals
						newDecisionLevel(conflictC);  // ?? why increase decision level if it is a satisfied literal. Seems to be used for the guard of the loop, but artificially increases the dec. level. 
						count_true_assump++;
					}
					else if (value(p) == l_False) { // literals in LiteralsFromPathFalsification lead to a contradiction by themselves                                                                     
						if (pf_early_unsat_terminate()) {
							return l_False;
						}
						else break; //LiteralsFromPathFalsification.clear();


						//oferg: instead of breaking we are going to reconstruct the proof here
						//vec<Lit> conflictingAssumptions;
						//analyzeFinal(~p, conflictingAssumptions);

						//oferg: at this point, we have an assignment in conflict with one or more assumption (which, recall, are LPF literals that are inferred from the original formula.
						//oferg: parents_of_empty_clause shoould contain the ic clauses that were used to resolve the empty clause in a previous iteration. From it we should extract all 
						//the clauses that are reacable from cr (the nIcToRemove from the previous LPF extraction, where LiteralsFromPathFalsification was updated - maybe do it while running LPF extraction? 
						//Maybe someone did it before?)







						////!!
						//printf("++++++++++++ conflicting assumptions ++++++++++++++++\n");
						//printClause(conflictingAssumptions, "conflicting assumptions");
						//printClause(LiteralsFromPathFalsification, "lpf lits");
						//printClause(ca[resolGraph.GetClauseRef(nICtoRemove)], "nICtoRemove");
						//printf("size of allParentsCRef of empty: %d\n", parents_of_empty_clause.size());
						////!!
						//if (parents_of_empty_clause.size() < 50) exit(0);


						
					}
					else {
						next = p;  // this will become the assumption
						break;
					}
				}
			}
            			
            if (next == lit_Undef) { // New variable decision:                
                decisions++;
				if ((next = pickBranchLit()) == lit_Undef) {
					return l_True; // Model found:				
				}
				//else
				//	if (verbosity == 1)
				//		printf("#%d\n", todimacsLit(next));

            }
            // Increase decision level and enqueue 'next'
            newDecisionLevel(conflictC);
			//if (verbosity == 1 && propagations == 50594638) {
			//	printf("**************enqueuing decision lit %d**************\n", todimacsLit(next));
			//}
            uncheckedEnqueue(next);
			/*if (verbosity == 1)
				printf("dec: %d\n", next);*/
        }
#pragma endregion


    } // end of main loop

}

void Solver::updateResolutionGraph(Clause& cl, CRef cr) {
	//printf("%d %d %d\n", cl.uid(), cr,icParents.size());
	resolGraph.AddNewResolution(cl.uid(), cr, icParents,remParents,allParents);
}
double Solver::progressEstimate() const
{
    double  progress = 0;
    double  F = 1.0 / nVars();

    for (int i = 0; i <= decisionLevel(); i++){
        int beg = i == 0 ? 0 : trail_lim[i - 1];
        int end = i == decisionLevel() ? trail.size() : trail_lim[i];
        progress += pow(F, i) * (end - beg);
    }

    return progress / nVars();
}

/*
  Finite subsequences of the Luby-sequence:

  0: 1
  1: 1 1 2
  2: 1 1 2 1 1 2 4
  3: 1 1 2 1 1 2 4 1 1 2 1 1 2 4 8
  ...


 */

static double luby(double y, int x){

    // Find the finite subsequence that contains index 'x', and the
    // size of that subsequence:
    int size, seq;
    for (size = 1, seq = 0; size < x+1; seq++, size = 2*size+1);

    while (size-1 != x){
        size = (size-1)>>1;
        seq--;
        x = x % size;
    }

    return pow(y, seq);
}




bool Solver::lpf_compute_inprocess() {
	
				pf_prev_trail_size = trail.size();
				double before_time = cpuTime();								
				int old_falsified_literals = LiteralsFromPathFalsification.size();  // !! potential bug in statistics: if early-termination returns false, it resets this set. 
				int addLiterals = PF_get_assumptions(nICtoRemove, resolGraph.GetClauseRef(nICtoRemove));
				time_for_pf += (cpuTime() - before_time);								
				if (verbosity == 1) printf("*** in process lpf = %d\n", addLiterals);
				if (addLiterals == 0) { // If no literals are added it means that all paths from root are satisfied (otherwise we would at least have the literals in root), and hence the result of the next iteration is bound to be UNSAT. 				
					if (pf_early_unsat_terminate()) {
						printf("early termination\n");
						return false;
					}
				}
				pf_Literals += (addLiterals - old_falsified_literals);								
	
	return true;
}




// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{

    bool save_opt_ic_simplify = opt_ic_simplify;
    bool save_opt_post_ic_imp = opt_post_ic_imp;
    bool save_opt_ic_as_dec = opt_ic_as_dec;
    if (opt_only_from > m_nSatCall)
    {
        opt_ic_simplify = true;
        opt_post_ic_imp = false;
    }

    if (opt_only_from_2 > m_nSatCall)
    {
        opt_ic_as_dec = false;
    }

    m_bUnsatByPathFalsification = false;
    model.clear();
    conflict.clear();
    if (!ok) return l_False;

    solves++;
    decLevInConfl.growTo(nVars(), 0);

    max_learnts               = nClauses() * learntsize_factor;
    learntsize_adjust_confl   = learntsize_adjust_start_confl;
    learntsize_adjust_cnt     = (int)learntsize_adjust_confl;
    lbool   status            = l_Undef;

    if (verbosity > 1){
        printf("c ============================[ Search Statistics ]==============================\n");
        printf("c | Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("c |           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("c ===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;		
	pf_active = false;
	pf_zombie = false;	
	pf_prev_trail_size = 0;
	lpf_delay = false;






    while (status == l_Undef){
		
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
		if (!pf_zombie && !pf_active && !test_mode && nICtoRemove > 0 )
			pf_active = true;		
		lpf_delay = curr_restarts < opt_pf_delay;
			
		status = search(rest_base * restart_first);		
        
		if (asynch_interrupt && status == l_Undef)  return l_Undef;
        if (!withinBudget()) break;		
        curr_restarts++;		

    }
	
    if (verbosity > 1)
        printf("c ===============================================================================\n");

    if (status == l_True){
        // Extend & copy model:
        model.growTo(nVars());
        for (int i = 0; i < nVars(); i++) model[i] = value(i);
        if (!opt_use_clauses)
            ++m_nSatCall;
    }
/*    
    else if (status == l_False && conflict.size() == 0)
        ok = false;
*/

    opt_ic_simplify = save_opt_ic_simplify;
    opt_post_ic_imp = save_opt_post_ic_imp;
    opt_ic_as_dec = save_opt_ic_as_dec;
    cancelUntil(0);
    if (!m_bUnsatByPathFalsification)
    {
        m_nUnsatPathFalsificationCalls = 0;
    }

    return status;
}

//=================================================================================================
// Writing CNF to DIMACS:
// 
// FIXME: this needs to be rewritten completely.

static Var mapVar(Var x, vec<Var>& map, Var& max)
{
    if (map.size() <= x || map[x] == -1){
        map.growTo(x+1, -1);
        map[x] = max++;
    }
    return map[x];
}

void Solver::toDimacs(FILE* f, Clause& c, vec<Var>& map, Var& max)
{
    if (satisfied(c)) return;

    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) != l_False)
            fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", mapVar(var(c[i]), map, max)+1);
    fprintf(f, "0\n");
}

void Solver::toDimacs(const char *file, const vec<Lit>& assumps)
{
    FILE* f = fopen(file, "wr");
    if (f == NULL)
        fprintf(stderr, "could not open file %s\n", file), exit(1);
    toDimacs(f, assumps);
    fclose(f);
}

void Solver::toDimacs(FILE* f, const vec<Lit>& assumps)
{
    // Handle case when solver is in contradictory state:
    if (!ok){
        fprintf(f, "p cnf 1 2\n1 0\n-1 0\n");
        return; }

    vec<Var> map; Var max = 0;

    // Cannot use removeClauses here because it is not safe
    // to deallocate them at this point. Could be improved.
    int cnt = 0;
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]]))
            cnt++;
        
    for (int i = 0; i < clauses.size(); i++)
        if (!satisfied(ca[clauses[i]])){
            Clause& c = ca[clauses[i]];
            for (int j = 0; j < c.size(); j++)
                if (value(c[j]) != l_False)
                    mapVar(var(c[j]), map, max);
        }

    // Assumptions are added as unit clauses:
    cnt += assumptions.size();

    fprintf(f, "p cnf %d %d\n", max, cnt);

    for (int i = 0; i < assumptions.size(); i++){
        assert(value(assumptions[i]) != l_False);
        fprintf(f, "%s%d 0\n", sign(assumptions[i]) ? "-" : "", mapVar(var(assumptions[i]), map, max)+1);
    }

    for (int i = 0; i < clauses.size(); i++)
        toDimacs(f, ca[clauses[i]], map, max);

    if (verbosity > 1)
        printf("c Wrote %d clauses with %d variables.\n", cnt, max);
}

//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
    // All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);
            // printf(" >>> RELOCING: %s%d\n", sign(p)?"-":"", var(p)+1);
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
		//if (reason(var(trail[i])) == 55989)
		//	printf("-------- %d reason ----------\n", 55989);
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }
    
    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++) 
    {
		//if (learnts[i] == 55989)
		//	printf("-------- %d learnt ----------\n", 55989);
        ca.reloc(learnts[i], to);
        Clause& c = to[learnts[i]];
		if (c.ic() || c.isParentToIc()) {
           resolGraph.UpdateClauseRef(c.uid(), learnts[i]);
		}
    }

    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)  {
		//CRef oldCr = clauses[i];
		//if (oldCr == 55989) {
		//	printf("-------- %d orig clause ----------\n", 55989);
			//printClause(ca[clauses[i]], std::to_string(ca[clauses[i]].uid()) + " (uid), relocating oldCr = " + std::to_string(clauses[i]));
			//printClause(, std::to_string(ca[clauses[i]].uid()) + " (uid)");
		//}
		ca.reloc(clauses[i], to); //this changes the value of clauses[i] !!!!!!!!!!!!!!!!!!!!!!!!!!
        Clause& c = to[clauses[i]];
		//if (oldCrr == 55989) {
		//	//printf("-------- %d orig clause ----------\n", 55989);
		//	printClause(c, std::to_string(to[clauses[i]].uid()) + " (uid), relocated to newCr = " + std::to_string(clauses[i]));
		//	//printClause(, std::to_string(ca[clauses[i]].uid()) + " (uid)");
		//}


		if (c.ic() || c.isParentToIc()) {
			resolGraph.UpdateClauseRef(c.uid(), clauses[i]);
		}
    }

    for (int i = 0; i < icUnitClauses.size(); i++)
    {
        ca.reloc(icUnitClauses[i], to);
        Clause& c = to[icUnitClauses[i]];
        assert(c.ic());
        resolGraph.UpdateClauseRef(c.uid(), icUnitClauses[i]);
    }
}

void Solver::garbageCollect(){
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity > 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}
//Given an origConfl clause that is currently conflicting (i.e. all it's literals are falsified in the trail), find all
//the clauses that were used (were reasons) for such falsification (note that this is not necessarily a subset of the 
//original formula, as it may contain learned clauses). The reason (retuned through 'parents_of_empty_clause') are filtered 
//to contain only IC clause.
void Solver::findConflictICReasons(CRef origConfl) {
    assert (decisionLevel() == 1);	
	
    m_bConeRelevant = true;
    CRef confl = origConfl;
    int index   = trail.size() - 1;
    Var v = var_Undef;
    int nSeen = 0;
	parents_of_empty_clause.clear();
	resolGraph.m_EmptyClauseParents.clear();

    for (;;) {
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.ic()) {            
#ifdef NewParents
			parents_of_empty_clause.push(c.uid());
#endif
			resolGraph.m_EmptyClauseParents.insert(c.uid()); // duplicate to parents_of_empty_clause, but as a set, which is more convinient for checking if it contains an element. 

        }

        for (int j = (v == var_Undef) ? 0 : 1 ; j < c.size(); j++) {
            v = var(c[j]);
            assert(value(c[j]) == l_False);

            if (!seen[v] && level(v) > 0) {
                seen[v] = 1;
                ++nSeen;
            }
        }

        if (nSeen == 0)
            break;
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]); // walk backwards on trail and look for the first seen variable encountered
        v     = var(trail[index+1]); // index+1 becuase we walked one step too much in the line above (index--)
        confl = reason(v);
        seen[v] = 0;
        --nSeen;
    }
}

void Solver::GetUnsatCore(vec<uint32_t>& core, Set<uint32_t>& emptyClauseCone)
{
    core.clear();
    for (int nInd = 0; nInd < parents_of_empty_clause.size(); ++nInd)
    {
		if (emptyClauseCone.insert(parents_of_empty_clause[nInd])) {
			resolGraph.GetOriginalParentsUids(parents_of_empty_clause[nInd], core, emptyClauseCone);
		}
    }
	//printf("parents_of_empty_clause size: %d\n", core.size());
	//printf("unsatCore size: %d\n", core.size());
	//printf("emptyClauseCone size: %d\n", emptyClauseCone.elems());
}

// used for removing subsumed IC clauses. We want to remove them and their descendants, but if a 
// descendant has yet another IC parent, we do not want to remove it, because we rely on a path
// from ICs to the empty clause when using optimization pf-mode=3/pf-mode=4.

void Solver::RemoveClauses_withoutICparents(vec<uint32_t>& cone) {
	//printf("%s ", __FUNCTION__);
	resolGraph.AddNewRemainderUidsFromCone(setGood, cone);  // setGood = clauses that all their allParentsCRef are not IC
	resolGraph.GetClausesCones(cone); // find all cones of the roots we started from
	//printf("RemoveClauses_withoutICparents setGood = %d, cone = %d\n", setGood.elems(), cone.size());
	cancelUntil(0);
	// cone contains all the clauses we want to remove
	for (int i = 0; i < cone.size(); ++i)
	{
		CRef cr = resolGraph.GetClauseRef(cone[i]);
		if (cr != CRef_Undef && setGood.has(cone[i]))
		{
			ca[cr].mark(0);			
			removeClause(cr);
		}
	}
}

void Solver::RemoveClauses(vec<uint32_t>& cone)
{
    resolGraph.GetClausesCones(cone);
    cancelUntil(0);

    // cone contains all the clauses we want to remove
    for (int i = 0; i < cone.size(); ++i)
    {
        CRef cr = resolGraph.GetClauseRef(cone[i]);
        if (cr != CRef_Undef)
        {
			if (verbosity == 1 && ca[cr].uid() == 369119)
				printf("RemoveClauses %d\n", ca[cr].uid());
            ca[cr].mark(0);

            removeClause(cr);
        }
    }

    // check that all the clauses are actually removed
/*    for (int i = 0; i < cone.size(); ++i)
    {
        assert (resolGraph.GetClauseRef(cone[i]) == CRef_Undef);
        assert(resolGraph.GetResolRef(cone[i]) == CRef_Undef);
    }
*/
}
//void Solver::calcRhombus(vec<uint32_t>& inRoots, vec<uint32_t>& inLeaves, Set<uint32_t>& outRhombus) {
//	vec<uint32_t> curr,next;
//	Set<uint32_t> seen;
//	outRhombus.clear();
//	for (int i = 0; i < inRoots.size(); ++i)
//		if (seen.insert(inRoots[i]))
//			curr.push(inRoots[i]);
//
//	while (curr.size() > 0) {
//		printf("num of curr: %d\n", curr.size());
//		for (int i = 0; i < curr.size(); ++i) {
//			vec<uint32_t>& children = resolGraph.GetResol(curr[i]).m_Children;
//			printf("num of children: %d\n", children.size());
//			for (int j = 0; j < children.size(); ++j) {
//				if (seen.insert(children[j]))
//					next.push(children[j]);
//			}
//		}
//
//		next.swap(curr);
//		next.clear();
//
//	}
//
//	for (int i = 0; i < inLeaves.size(); ++i)
//		if(seen.has(inLeaves[i]) && outRhombus.insert(inLeaves[i]))
//			curr.push(inLeaves[i]);
//	while (curr.size() > 0) {
//		for (int i = 0; i < curr.size(); ++i) {
//			for (int j = 0; j < resolGraph.GetResol(curr[i]).ParentsSize(); ++j) {
//				uint32_t parent = resolGraph.GetResol(curr[i]).Parents()[j];
//				if (seen.has(parent) && outRhombus.insert(parent)) {
//					next.push(parent);
//				}
//			}
//		}
//		next.swap(curr);
//		next.clear();
//	}
//	printf("end");
//}
void Solver::RemoveEverythingNotInCone(Set<uint32_t>& cone, Set<uint32_t>& muc)
{
    uidsVec.clear();
	//    sort(uidsVec); // what is this for ? 
    cone.copyTo(uidsVec);
    cancelUntil(0);
    sort(uidsVec);
    int j = 0;
    for (uint32_t i = 0; i < resolGraph.GetMaxUid(); ++i) {
		//if (i == 369119 || i == 368608) {
		//if (i == 368608) {
		//	printf("%d in graph\n", i);
		//}

        if (i != uidsVec[j] && !muc.has(i)) { //uid i is not in the muc and not in the cone
			//if (i == 369119 || i == 368608) {
			//if ( i == 368608) {
			//	printf("%d not cone or muc\n",i);
			//}r
            CRef cr = resolGraph.GetClauseRef(i);
			if (cr != CRef_Undef) { // check that clause is not original otherwise we won't delete it
				//if (i == 368608) {
				//	printf("%d ?= %d, cr: %d\n", i, ca[cr].uid(), cr);
				//}
				 //if (i == 369119 || i == 368608) {
				//if ( i == 368608) {
				//	printf("%d defined \n",i);
				//	printf("%d ca[cr].isParentToIc() = %d \n",i, ca[cr].isParentToIc());
				//}
				Clause& c = ca[cr];

				if (opt_blm_rebuild_proof && c.isParentToIc()) {
				////	//if (i == 369119 || i == 368608) {
					//if (i == 368608) {
					//	printf("%d skip del\n", i);
					//}
					continue;
				}
				//if(verbosity == 1)
				//	printf("del %d %d %d\n", i,ca[cr].ic(), ca[cr].isParentToIc());

				//if (verbosity == 1)
				//	printf("%d, mark %d\n", ca[cr].uid(), ca[cr].mark());
				//if (i == 369119 || i == 368608) {
				//if (i == 368608) {
				//	printf("%d, mark %d\n", ca[cr].uid(), ca[cr].mark());
				//	printf("removing %d\n", i);
				//}
				c.mark(0);
				removeClause(cr);
			}
			//else if (i == 369119 || i == 368608) {
			//else if (i == 368608) {
			//		printf("%d undefined \n", i);
			//}
			
        }
        else if (i == uidsVec[j] && j < uidsVec.size()) {
            ++j;
        }
    }
	//printf("RemoveEverythingNotInCone cone.size() %d, muc.size() %d\n", cone.elems(), muc.elems());
}

void Solver::UnbindClauses(vec<uint32_t>& cone){
    resolGraph.GetClausesCones(cone);
    cancelUntil(0);
    // cone contains all the clauses we want to remove
    for (int i = 0; i < cone.size(); ++i) {
        CRef cr = resolGraph.GetClauseRef(cone[i]);
        if (cr != CRef_Undef) {
            Clause& c = ca[cr];
            if (c.size() > 1) {
                detachClause(cr);
                // so we will be able to use lazy watch removal

                c.mark(1); 
            }
            else {
                c.mark(2);
            }
        }
    }

    watches.cleanAll();

    for (int i = 0; i < cone.size(); ++i) {
        CRef cr = resolGraph.GetClauseRef(cone[i]);
        if (cr != CRef_Undef) {
            Clause& c = ca[cr];
			if (c.size() > 1) {
				if (verbosity == 1 && c.uid() == 369119)
					printf("UnbindClauses %d\n", c.uid());
				c.mark(0);
			}
        }
    }
	//printf("UnbindClauses cone.size() %d\n",  cone.size());
}


void Solver::BindClauses(vec<uint32_t>& cone, uint32_t startUid) {
    if (opt_bind_as_orig == 2) {
        vec<uint32_t> init(1);
        init[0] = startUid;
        resolGraph.AddNewRemainderUidsFromCone(setGood, init); // setGood will now contain clauses s.t. all their parents are not IC (and therefore not ic themselves)
		//printf("BindClauses cone.size() %d, setGood.size() %d\n", cone.size(), setGood.elems());
		//Oferg: note that when using 'opt_blm_rebuild_proof' a remainder clause that is a parent to an ic clause is still added to the resolution graph, 
		//however it doesn't have any parents and is in itself not considered an ic clause -
		//therefore it was automatically added to setGood 
    }
    cancelUntil(0);

    // cone contains all the clauses we want to bind back to solver as remainder
    for (int i = 0; i < cone.size(); ++i) {
        uint32_t uid = cone[i];
        CRef cr = resolGraph.GetClauseRef(uid);
        if (cr != CRef_Undef) {
            Clause& c = ca[cr];
            c.mark(0);
			if (verbosity == 1 && c.uid() == 369119)
				printf("bindClauses %d\n", c.uid());
            if ((opt_bind_as_orig == 1 && resolGraph.GetParentsNumber(uid) == 0) ||
                (opt_bind_as_orig == 2 && setGood.has(uid))) { // we now remove the clause and then rebuild and add it back as a remainder.
				if (resolGraph.GetParentsNumber(uid) == 0) {
					c.mark(2);
					//printClause(c, "uid " + std::to_string(uid) + " mark(2)");
				}
				else
					removeClause(cr);

                analyze_stack.clear(); // to be filled with cr's literals that are not false. 
                bool isSatisfied = false; 
                for (int litId = 0; litId < c.size(); ++litId)  {
                    if (value(c[litId]) == l_True) { // 'value' has information on level 0 only (because there was a 'cancelUntil(0)' after the run). 
                        isSatisfied = true; // the clause is satisfied at dec. level 0, we can discard it
                        break;
                    }
                    else if (value(c[litId]) == l_False) {// false at dec. level 0
                        continue;  // skip false literal
                    }
                    analyze_stack.push(c[litId]); // keep
                }

                if (isSatisfied)
                    continue;  // discard clause
                if (analyze_stack.size() == 0) {// empty clause at dec. level 0 ?
                    ok = false;
                    return;
                }
                if (analyze_stack.size() == 1) {
                    enqueue(analyze_stack[0]); // unit clause
                }
                else {
                    CRef newCr = ca.alloc(analyze_stack, c.learnt(), false);  // normal clause, not IC. The literals are in analyze_stack.
                    clauses.push(newCr);
                    attachClause(newCr);
                    if (opt_use_clauses)
                        ++m_nSatCall;
                }
            }
            else  {
                if (c.size() > 1) {
                    attachClause(cr);
                }
            }
        }
    }
}

// 'cone' contains root clauses to be re-binded as normal (not IC) clauses (because of rotation). 
void Solver::GroupBindClauses(vec<uint32_t>& cone)
{
    if (opt_bind_as_orig == 0) return;    

    if (opt_bind_as_orig == 2)
    {		
        resolGraph.AddNewRemainderUidsFromCone(setGood, cone); // setGood will now contain clauses that all their allParentsCRef are not IC
		//printf("setGood = %d, cone = %d ", setGood.elems(), cone.size());
		//printf("GroupBindClauses cone.size() %d, setGood.size() %d\n", cone.size(), setGood.elems());
        resolGraph.GetClausesCones(cone);  // This adds to cone all its cones. 
		//printf("cone = %d\n", cone.size());
    }
	    
    for (int i = 0; i < cone.size(); ++i)
    {
        uint32_t uid = cone[i];
        CRef cr = resolGraph.GetClauseRef(uid);
        if (cr != CRef_Undef)
        {

            Clause& c = ca[cr];
            c.mark(0);

            if ((opt_bind_as_orig == 1 && resolGraph.GetParentsNumber(uid) > 0) ||
                (opt_bind_as_orig == 2 && !setGood.has(uid)))
            {
                continue;  // not in setGood, hence it has to stay an IC clause; nothing to do. 
            }
			// we remove the clause, and later we will re-add it as a remainder, possibly shrinked. 
            if (resolGraph.GetParentsNumber(uid) == 0) {// original clause
            
                if (c.size() > 1)  {
                    detachClause(cr);
                    // so we will be able to use lazy watch removal
                    c.mark(1);  // delay removal of originals.
                }
            }
			else {
				removeClause(cr);
			}
                
            analyze_stack.clear();

            bool isSatisfied = false;
            for (int litId = 0; litId < c.size(); ++litId) {// we generate a simpler clause (or eliminate it) based on what's known in dec. level 0
                if (value(c[litId]) == l_True) {
                    isSatisfied = true;
                    break;
                }
                else if (value(c[litId]) == l_False)
                    continue;  // skip a literal that is false at dec. level 0
                
                analyze_stack.push(c[litId]);
            }

            if (isSatisfied) 
				continue;

            if (analyze_stack.size() == 0) { // empty clause at dec. level 0            
                ok = false;
                return;
            }

            if (analyze_stack.size() == 1) {
                enqueue(analyze_stack[0]);
            }
            else {

                CRef newCr = ca.alloc(analyze_stack, c.learnt(), false); // normal clause, not IC. The literals are in analyze_stack.
                clauses.push(newCr);
                attachClause(newCr);
                if (opt_use_clauses)
                    ++m_nSatCall;
            }
        }
    }

    watches.cleanAll();
    for (int i = 0; i < cone.size(); ++i)
    {
        uint32_t uid = cone[i];
        if (resolGraph.ValidUid(uid) && resolGraph.GetParentsNumber(uid) == 0)
        {
            CRef cr = resolGraph.GetClauseRef(uid);
            assert (cr != CRef_Undef);
            Clause& c = ca[cr];
            c.mark(2); // do not remove originals from resolution graph // originally the reason we needed them was for correctness checking in hhlmuc (code migration...), where the distinction between remainder and non remainder is important ('group 0' in hhlmuc).
        }
    }

}


int Solver::todimacsLit(Lit l) {
	int res = var(l) + 1;
	return sign(l) ? -res : res; 
}

void Solver::printLearntsDB() {
	printf("---- learnts start-----\n");
	for (int i = 0; i < learnts.size(); ++i) {
		printf("uid %d, mark %d\n", ca[learnts[i]].uid(), ca[learnts[i]].mark());
	}
	printf("---- learnts end-----\n");
}
void Solver::printTrail() {

}


void Solver::printClause(const Clause& c, std::string text)
{
	std::cout << text << std::endl;
	for (int i = 0; i < c.size(); i++)
		std::cout << (todimacsLit(c[i])) << " ";
	std::cout << "0" << std::endl;
}

void Solver::printClause(const vec<Lit>& v, std::string text)
{
	std::cout <<  text << std::endl;
	for (int i = 0; i < v.size(); i++)
		std::cout << (todimacsLit(v[i])) << " ";
	std::cout << "0" << std::endl;
}
void Solver::printClause(uint32_t uid, std::string text) {
	CRef cref = GetClauseIndFromUid(uid);
	if(uid == CRef_Undef)
		std::cout << "CRef_Undef" << std::endl;
	if(cref == CRef_Undef)
		std::cout << "clause deleted" << std::endl;
	else
		printClause(ca[cref], text);
}

void Solver::CreateResolVertex(uint32_t uid)
{
    assert(icParents.size() == 0);
	assert(remParents.size() == 0);
	assert(allParents.size() == 0);

    resolGraph.AddNewResolution(uid, CRef_Undef, icParents);
}

void Solver::AddConflictingIc(uint32_t uid)
{
    assert(icParents.size() == 0);
    icParents.push(uid);
    ok = true;
}

void Solver::ResetOk()
{
    ok = true;
}

int Solver::calculateDecisionLevels(vec<Lit>& cls)
{
    int decLevels = 0;
    for (int i=0; i<cls.size(); ++i )
    {
        int levelV = vardata[var(cls[i])].level;
        if (decLevInConfl[levelV] != conflicts)
        {
            ++decLevels;
            decLevInConfl[levelV] = conflicts;
        }
    }

    return decLevels;
}




int Solver::PF_get_assumptions(uint32_t uid, CRef cr) // Returns the number of literals in the falsified clause. 
{	
	LiteralsFromPathFalsification.clear();
	if ((opt_pf_mode == lpf || opt_pf_mode == lpf_inprocess) && m_bConeRelevant && !lpf_delay) {
		LPF_get_assumptions(uid, LiteralsFromPathFalsification);
		//printClause(LiteralsFromPathFalsification, "new S set");
		return LiteralsFromPathFalsification.size();
	}
	else {
		Clause& c = ca[cr];
		LiteralsFromPathFalsification.growTo(c.size());
		for (int i = 0; i < c.size(); ++i){
			LiteralsFromPathFalsification[i] = c[i];
			if (verbosity == 1) printf("%d ", c[i].x);
		}
		if (verbosity == 1) printf("pf = removed ic only.\n");
	}
	   
	

	if ((opt_pf_mode == pf || opt_pf_mode == lpf || opt_pf_mode == lpf_inprocess) && m_bConeRelevant) // chain (pf). Either in pf mode, or lpf/lpf_inprocess when we are in delay. 
    {
        uidsVec.clear();
        resolGraph.GetTillMultiChild(uid, uidsVec);

        for (int i = 0; i < uidsVec.size(); ++i)
        {
            CRef cr = resolGraph.GetClauseRef(uidsVec[i]);
            if (cr != CRef_Undef)
            {    
                Clause& c = ca[cr];
                for (int i = 0; i < c.size(); ++i)
                {
                    LiteralsFromPathFalsification.push(c[i]);
                }	
            }
        }
    }
	
	if (verbosity == 1) printfVec(LiteralsFromPathFalsification,"literals from pf");

    return LiteralsFromPathFalsification.size(); //nAddedClauses;
}

void Solver::GeticUnits(vec<int>& v) {	// ofer
	for (int nInd = 0; nInd < icUnitClauses.size(); ++nInd)
	{
		Clause& c = ca[icUnitClauses[nInd]];
		if (c.mark() != 0 )  //?? ask if necessary
			continue;
		v.push(c[0].x);
	}	
}


///  But it uses class Map which is multimap, which complicates it. Should be replaced with ordinary map.
bool Solver::CountParents(Map<uint32_t,uint32_t>& mapRealParents,uint32_t uid) { // uid is either cr itself, or the clause at the bottom of a chain
	int currUid,m;
	std::queue<uint32_t> q; // compute number of allParentsCRef in the cone of cr
	int maxQ = 0;
	int initialSpan = 0;
	q.push(uid);	 
	bool first = true;

	while (!q.empty()) {	
		if (opt_lpf_cutoff) {	
			maxQ = std::max((int)q.size(), maxQ);
			if (maxQ > 500) 
				return false;  // magic cutoff number
		}
		currUid = q.front();
		q.pop();
		CRef currResRef = resolGraph.GetResolRef(currUid);
		assert(currResRef != CRef_Undef);
		const Resol& r = resolGraph.GetResol(currResRef);

		for (m = 0 ; m < r.m_Children.size() ; m++) {
			uint32_t childUid = r.m_Children[m];
			if (!resolGraph.ValidUid(childUid)) 
				continue;
			CRef childClauseRef = resolGraph.GetClauseRef(childUid);	
			if ((pf_mode == lpf_inprocess) && (childClauseRef != CRef_Undef) &&  
				satisfied(ca[childClauseRef])) 
				continue;
			if (first && opt_lpf_cutoff && ++initialSpan > 400) 
				return false;  // magic cutoff number			
			if (mapRealParents.has(r.m_Children[m])) 
				++mapRealParents[r.m_Children[m]];	
			else {
				q.push(r.m_Children[m]);  
				mapRealParents.insert(r.m_Children[m], 1);
			}			
		}
		first = false;
	}	
	//printf("%d %d", initialSpan, maxQ);
	return true;
}


void Solver::printResGraph(uint32_t uid, vec<uint32_t>& parents_of_empty_clause, vec<Lit>& assumptions) // uid is either cr itself, or the clause at the bottom of a chain
{
int currUid,m;
	std::queue<uint32_t> q; // compute number of allParentsCRef in the cone of cr
	q.push(uid);	
    Map<uint32_t,uint32_t> mapRealParents;
	mapRealParents.insert(uid,0);	
	
	while (!q.empty()) 
	{
		currUid = q.front();
		bool parent_of_empty; 
		parent_of_empty = false;
		if (parents_of_empty_clause.binary_search(currUid)) {
			printf("*"); 
			parent_of_empty =true;
		}
		else printf(" ");
	
		printf("id = %d (", currUid);
		CRef c = resolGraph.GetClauseRef(currUid); // the clause reference of cr
		if (c == CRef_Undef) {
			printf("(deleted clause)");	
		}
		else {
			const Clause& cls = ca[c]; // the actual clause			
			for (int i=0 ; i < cls.size() ; i++){  // initially parent = cr
				printf("%d ", cls[i]); 				
			}			
		}		
		q.pop();
		
		CRef curr_ref = resolGraph.GetResolRef(currUid);
		const Resol& r = resolGraph.GetResol(curr_ref);
		if(r.m_Children.size()==0){  // no more children
			printf(")\n");
			continue;
		}
		printf(") children = ");
		for (m=0 ; m < r.m_Children.size() ; m++)
		{
			if (!resolGraph.ValidUid(r.m_Children[m])) continue;
			printf("%d, ", r.m_Children[m]);		
			if(!mapRealParents.has(r.m_Children[m]))
			{				
				mapRealParents.insert(r.m_Children[m],0);
				q.push(r.m_Children[m]);
			}
		}
		printf("\n");
	}	
}


void Solver::ResGraph2dotty(vec<uint32_t>& roots, vec<uint32_t>& parents_of_empty_clause, vec<Lit>& assumptions,const char* filename) // uid is either cr itself, or the clause at the bottom of a chain
{
	int currUid,m;
	vec<uint32_t> sorted_roots;
	vec<uint32_t> sorted_parents;
	vec<Lit> sorted_assumptions;
	//!!
	Set<uint32_t> seen;
	Set<uint32_t> nonRhombusParents;
	vec<uint32_t> q2;
	//!!
	parents_of_empty_clause.copyTo(sorted_parents);
	roots.copyTo(sorted_roots);
	assumptions.copyTo(sorted_assumptions);
	sort(sorted_parents);
	sort(sorted_roots);
	sort(sorted_assumptions);

	std::queue<uint32_t> q; 
	// compute number of allParentsCRef in the cone of cr
	Map<uint32_t,uint32_t> mapRealParents;
	for (int i = 0; i < sorted_roots.size(); ++i) {
		uint32_t uid = roots[i];
		q.push(uid);
		mapRealParents.insert(uid, 0);
	}
	FILE *dot;
	std::stringstream edges;
	edges << " ";

		dot = fopen(filename, "w");
		fprintf(dot, "digraph tclause {\n");

	while (!q.empty()) {
		currUid = q.front();
		//!!
		if (seen.insert(currUid))
			q2.push(currUid);
		//!!



		//print node data
		fprintf(dot, "node[");

		if (sorted_parents.binary_search(currUid)) 
			fprintf(dot,"color=green,");
		else if(sorted_roots.binary_search(currUid))
			fprintf(dot, "color=blue,");
		else fprintf(dot,"color=black,");

		CRef cr = resolGraph.GetClauseRef(currUid); // the clause reference of currUid
		if (cr == CRef_Undef) {
			//fprintf(dot, "label=\"");
			//vec<Lit>& vecLit = *resolGraph.icDelayedRemoval[currUid];
			//sort(vecLit);
			//for (int i = 0; i < vecLit.size(); i++) {  // initially parent = cr							
			//	if (sorted_assumptions.size()>0 && sorted_assumptions.binary_search(vecLit[i]))
			//		fprintf(dot, "*");
			//	fprintf(dot, "%d ", todimacsLit(vecLit[i]));
			//}
			//fprintf(dot, "\"");


			fprintf(dot, "label=\"D\"");
			//if(resolGraph.icDelayedRemoval.find(currUid) == resolGraph.icDelayedRemoval.end())
			//	printf("deleted %d not in icDelayed map\n", currUid);
		}
		else {
			const Clause& c = ca[cr]; // the actual clause
			fprintf(dot,"label=\"");
			for (int i=0 ; i < c.size() ; i++){  // initially parent = cr							
				if (sorted_assumptions.size()>0 && sorted_assumptions.binary_search(c[i]))
					fprintf(dot,"*");
				fprintf(dot,"%d ", todimacsLit(c[i]));
			}
			fprintf(dot,"\"");


		}
		fprintf(dot,"]; n%d;\n",currUid);

		//end print node data

		q.pop();

		CRef curr_ref = resolGraph.GetResolRef(currUid);
		const Resol& r = resolGraph.GetResol(curr_ref);
		if(r.m_Children.size()==0){  // no more children		
			continue;
		}		
		for (m=0 ; m < r.m_Children.size() ; m++) {
			if (!resolGraph.ValidUid(r.m_Children[m])) 
				continue;		
			edges << "n" << currUid << " -> n" << r.m_Children[m] << ";" << std::endl;
			
			if(!mapRealParents.has(r.m_Children[m])) {				
				mapRealParents.insert(r.m_Children[m],0);
				q.push(r.m_Children[m]);
			}
		}
	}

	//!!
	//for (int i = 0; i < q2.size();++i) {
	//	uint32_t currUid = q2[i];
	//	if (!resolGraph.ValidUid(currUid))
	//		continue;
	//	CRef resolRef = resolGraph.GetResolRef(currUid);
	//	Resol& resol = resolGraph.GetResol(resolRef);
	//	uint32_t parentsSize = resol.ParentsSize();
	//	if (currUid == 367885)
	//		printf("uid: %d parentsSize = %d\n", currUid,parentsSize);
	//	uint32_t* parents = resol.Parents();
	//	for (int j = 0; j < parentsSize; ++j) {
	//		uint32_t parent = parents[j];
	//		if (!resolGraph.ValidUid(parent))
	//			continue;
	//		if (seen.insert(parent)) {
	//			fprintf(dot, "node[");
	//			fprintf(dot, "color=red,");
	//			CRef cr = resolGraph.GetClauseRef(parent); // the clause reference of parent
	//			if (cr == CRef_Undef) {
	//				if (resolGraph.icDelayedRemoval.find(parent) == resolGraph.icDelayedRemoval.end()) {
	//					fprintf(dot, "label=\"D\"");
	//					printf("deleted %d not in icDelayed map\n", parent);
	//					continue;
	//				}
	//				fprintf(dot, "label=\"");
	//				vec<Lit>& vecLit = *resolGraph.icDelayedRemoval[parent];
	//				sort(vecLit);
	//				for (int i = 0; i < vecLit.size(); i++) {  // initially parent = cr							
	//					if (sorted_assumptions.size()>0 && sorted_assumptions.binary_search(vecLit[i]))
	//						fprintf(dot, "*");
	//					fprintf(dot, "%d ", todimacsLit(vecLit[i]));
	//				}
	//				fprintf(dot, "\"");

	//			}
	//			else {
	//				const Clause& c = ca[cr]; // the actual clause
	//				fprintf(dot, "label=\"");
	//				for (int i = 0; i < c.size(); i++) {  // initially parent = cr							
	//					if (sorted_assumptions.size()>0 && sorted_assumptions.binary_search(c[i]))
	//						fprintf(dot, "*");
	//					fprintf(dot, "%d ", todimacsLit(c[i]));
	//				}
	//				fprintf(dot, "\"");


	//			}
	//			fprintf(dot, "]; n%d;\n", parent);
	//		
	//		
	//		}
	//		edges << "n" << parent << " -> n" << currUid << ";" << std::endl;
	//	}
	//	q2.pop();
	//}
	//!!

		fprintf(dot,"%s};\n", edges.str().c_str());
		edges.clear();		
		fclose(dot);
}

//void Solver::ResSubgraph2dotty(vec<uint32_t>& roots, vec<uint32_t>& parents_of_empty_clause, Set<uint32_t>& subgraph, vec<Lit>& assumptions, const char* filename) // uid is either cr itself, or the clause at the bottom of a chain
//{
//	int currUid, m;
//	vec<uint32_t> sorted_roots;
//	vec<uint32_t> sorted_parents;
//	vec<Lit> sorted_assumptions;
//	parents_of_empty_clause.copyTo(sorted_parents);
//	roots.copyTo(sorted_roots);
//	assumptions.copyTo(sorted_assumptions);
//	sort(sorted_parents);
//	sort(sorted_roots);
//	sort(sorted_assumptions);
//
//	std::queue<uint32_t> q;
//	// compute number of allParentsCRef in the cone of cr
//	Map<uint32_t, uint32_t> mapRealParents;
//	for (int i = 0; i < sorted_roots.size(); ++i) {
//		uint32_t uid = roots[i];
//		q.push(uid);
//		mapRealParents.insert(uid, 0);
//	}
//	FILE *dot;
//	std::stringstream edges;
//	edges << " ";
//
//	dot = fopen(filename, "w");
//	fprintf(dot, "digraph tclause {\n");
//
//	while (!q.empty()) {
//		currUid = q.front();
//		if (!subgraph.has(currUid))
//			continue;
//
//		fprintf(dot, "node[");
//
//		if (sorted_parents.binary_search(currUid))
//			fprintf(dot, "color=green,");
//		else if (sorted_roots.binary_search(currUid))
//			fprintf(dot, "color=blue,");
//		else fprintf(dot, "color=black,");
//
//		CRef cr = resolGraph.GetClauseRef(currUid); // the clause reference of currUid
//		if (cr == CRef_Undef) {
//
//
//			//fprintf(dot, "label=\"");
//			//vec<Lit>& vecLit = *resolGraph.icDelayedRemoval[currUid];
//			//sort(vecLit);
//			//for (int i = 0; i < vecLit.size(); i++) {  // initially parent = cr							
//			//	if (sorted_assumptions.size()>0 && sorted_assumptions.binary_search(vecLit[i]))
//			//		fprintf(dot, "*");
//			//	fprintf(dot, "%d ", todimacsLit(vecLit[i]));
//			//}
//			//fprintf(dot, "\"");
//
//
//			fprintf(dot, "label=\"D\"");
//			//if (resolGraph.icDelayedRemoval.find(currUid) == resolGraph.icDelayedRemoval.end())
//			//	printf("deleted %d not in icDelayed map\n", currUid);
//
//		}
//		else {
//			const Clause& c = ca[cr]; // the actual clause
//
//
//			fprintf(dot, "label=\"");
//			for (int i = 0; i < c.size(); i++) {  // initially parent = cr							
//				if (sorted_assumptions.size()>0 && sorted_assumptions.binary_search(c[i]))
//					fprintf(dot, "*");
//				fprintf(dot, "%d ", todimacsLit(c[i]));
//			}
//			fprintf(dot, "\"");
//
//
//		}
//		fprintf(dot, "]; n%d;\n", currUid);
//		q.pop();
//
//		CRef curr_ref = resolGraph.GetResolRef(currUid);
//		const Resol& r = resolGraph.GetResol(curr_ref);
//		if (r.m_Children.size() == 0) {  // no more children		
//			continue;
//		}
//		for (m = 0; m < r.m_Children.size(); m++) {
//			if (!subgraph.has(r.m_Children[m]))
//				continue;
//			if (!resolGraph.ValidUid(r.m_Children[m])) 
//				continue;
//			edges << "n" << currUid << " -> n" << r.m_Children[m] << ";" << std::endl;
//
//			if (!mapRealParents.has(r.m_Children[m]))
//			{
//				mapRealParents.insert(r.m_Children[m], 0);
//				q.push(r.m_Children[m]);
//			}
//		}
//	}
//
//	fprintf(dot, "%s};\n", edges.str().c_str());
//	edges.clear();
//	fclose(dot);
//}



//// for best performance send the smaller vector via 'a'. a should be sorted (b not).
//static inline void Intersection_nonSorted(vec<Lit>& a, vec<Lit>& b, vec<Lit>& intersection)
//{
//	int b_itr = 0;
//	int lb = 0;
//	while (b_itr != b.size()) {
//		if (a.binary_search_inc(b[b_itr], lb)) intersection.push(b[b_itr]);
//		++b_itr;
//	}
//	return;
//}

/************************************************************************/
/* Literal-based Path-falsification. 
 * With clause "uid_root": unsat
 * Before removing it, we find literals that can be added as assumptions. 
 * A literal l can be added if -l appears on all paths from uid_root to (). 
 * we find such literals based on the equivalence: S(cr) = \cap_{p \in allParentsCRef(cr)} S(p) \cup cr, where S(cr) is a set of literals that we attach to a clause cr. 
 * For the root clause cr (defined by the parameter "uid_root"), S(cr) = cr;
*/
/************************************************************************/
void Solver::LPF_get_assumptions(
	uint32_t uid_root, /**< uid of a clause that we are about to remove */ // Doxygen-friendly comments. 
	vec<Lit>& assump_literals /**< to be filled with literals */

	)
{

	std::unordered_map<uint32_t, vec<Lit>* > map_cls_to_Tclause; // from clause index to its Tclause
	std::queue<uint32_t> queue;		
	Map<uint32_t,uint32_t> map_cls_parentsCount;  // maps from uid of clause, to the number of allParentsCRef on the relevant cone of cr, i.e., allParentsCRef on paths from cr to the empty clause.
	bool prefix = true; 
	int peakQueueSize = 0;
	vec<int> icUnits;

	assert(parents_of_empty_clause.size()>0); // empty clause always has allParentsCRef.
	
#pragma region compute_Top_Tclause
    CRef c = resolGraph.GetClauseRef(uid_root);  // the clause reference of cr
    Clause& cc = ca[c];							//  cr itself

	//!!
	//printClause(cc,"c to remove");
	//vec<uint32_t> roots;
	//roots.push(nICtoRemove);
	//printf("dottycall %d\n", dottyCalls);
	//Set<uint32_t> subgraph;
	//calcRhombus(roots, parents_of_empty_clause, subgraph);
	//ResGraph2dotty(roots, parents_of_empty_clause, assumptions, ("c:\\temp\\lpf" + std::to_string(dottyCalls++) + ".dot").c_str());
	//!!

	if ((pf_mode == lpf_inprocess) && satisfied(cc)) {
		if (verbosity == 1) printf("root is satisfied\n");
		return; 	
	}
	
	// adding root to Top_TClause. 
	vec<Lit>* Top_TClause = new vec<Lit>(); 
	for (int i = 0; i < cc.size(); ++i)	 //we can skip this code if 'uid_root' will be also added to 'uidvec_prefix'
		(*Top_TClause).push(cc[i]); 

    // adding clauses in the unit-chain to Top_Tclause. 
	vec<uint32_t> uidvec_prefix; 	
	resolGraph.GetTillMultiChild(uid_root, uidvec_prefix);
	for (int i = 0; i < uidvec_prefix.size(); ++i) { // for each clause in the prefix, add it's literals to Top_TClause
		CRef cr = resolGraph.GetClauseRef(uidvec_prefix[i]);
		if (cr != CRef_Undef) {    
			Clause& cl = ca[cr];
			for (int i = 0; i < cl.size(); ++i) {
				Lit l = cl[i];				
				if (pf_mode == lpf_inprocess && value(l) == l_True)
					return;
				(*Top_TClause).push(l);
			}	
		}
	}    

	if (uidvec_prefix.size() > 0) {
        assert(Top_TClause->size() > 0);
		uid_root = uidvec_prefix.last(); 
	}   	
#pragma endregion

    bool proceed = CountParents(map_cls_parentsCount , uid_root); //counts the allParentsCRef in cr's rhombus
    if (opt_lpf_cutoff && !proceed) { // add counter of allParentsCRef in the cone. Returns false if we predict there is no point to spend too much time on it. 
		Top_TClause->copyTo(assump_literals);
		if (verbosity == 1) printf("cutoff\n");
		return;
	}
	sort(*Top_TClause);
	// from hereon uid_root is the bottom clause in the unit-chain, and its Tclause is the union of the clauses in the chain.
	// printfVec(*Top_TClause, "Top clause");
	map_cls_to_Tclause[uid_root] = new vec<Lit>();
	
	queue.push(uid_root);
	while (!queue.empty()) {
		uint32_t curr_id = queue.front();
		queue.pop();		
		CRef cref = resolGraph.GetResolRef(curr_id);
		assert(cref != CRef_Undef); 
		Resol& res = resolGraph.GetResol(cref);
		int children_num = res.m_Children.size();
		if (children_num == 0)  //oferg: a parent of empty clause //oferg: seems to be redundent, the loop won't be performed if the number of children is 0, and it's the last thing done in that iteration anyway
			continue;	//oferg: we can mark these allParentsCRef of empty clause here, so that if we 
						//reconstruct a future proof using this proof (in the case we proved unsat using 
						//backbone literal\s), we could start an upwards rhombus traversal from these clauses only
		peakQueueSize = std::max((int)queue.size(),  peakQueueSize);
		
		for(int i = 0; i < children_num; ++i) {				
			CRef childUid = res.m_Children[i];
			if (!resolGraph.ValidUid(childUid)) 
				continue;
			CRef childClauseRef = resolGraph.GetClauseRef(childUid);			
			if ((pf_mode == lpf_inprocess) && (childClauseRef != CRef_Undef) &&  satisfied(ca[childClauseRef]))	{							
				continue; // lpf_inprocess. satisfied refers to current assignment. So this is relevant only if we call this function after at least one propagation in search.
			}					
			--map_cls_parentsCount[childUid]; // reducing allParentsCRef count	

			// intersection with allParentsCRef
			if (map_cls_to_Tclause.find(childUid) == map_cls_to_Tclause.end()) {// first time we visit the clause
				assert(map_cls_to_Tclause.count(curr_id)>0);
                map_cls_to_Tclause[childUid] = new vec<Lit>();
				map_cls_to_Tclause[curr_id]->copyTo(*map_cls_to_Tclause[childUid]);
			}
			else {  // otherwise we intersect the current Tclause with the one owned by the Top_TClause. 
                vec<Lit> intersection;
				Intersection(*map_cls_to_Tclause[curr_id], *map_cls_to_Tclause[childUid], intersection);  // intersection between Tclause-s of child and Top_TClause.                   
				map_cls_to_Tclause[childUid]->swap(intersection);
			}			


			// done with allParentsCRef. Now we should add the clause's literals to its Tclause. 
			if(map_cls_parentsCount[childUid] == 0) { 
				vec<Lit> tmp_union;
				vec<Lit> temp_lit;
				if (childClauseRef != CRef_Undef) {  // in case that clause is erased, we do not have its literals to add to its Tclause. 
					ca[childClauseRef].copyTo(temp_lit);
					sort(temp_lit);

					assert(map_cls_to_Tclause.count(childUid)>0);
					union_vec(*map_cls_to_Tclause[childUid], temp_lit, tmp_union);						
					map_cls_to_Tclause[childUid]->swap(tmp_union);					
				}
				queue.push(childUid);					
			}
		}
	}    
	
	// we now intersect the Tclause-s of the allParentsCRef of the empty clause	
	vec<Lit> tmp, res;
	bool first = true;
	for (int i = 0; i < parents_of_empty_clause.size(); ++i) {
		if (map_cls_to_Tclause.find(parents_of_empty_clause[i])== map_cls_to_Tclause.end()) 
			continue; // only those that have T-clause are actual allParentsCRef of the empty clause in rhombus(cr). 		
		int idx = parents_of_empty_clause[i];
		if (first) {
			(*map_cls_to_Tclause[idx]).swap(res);
			first = false;
		}
		else {				
			tmp.swap(res);				
			res.clear();
			Intersection(*map_cls_to_Tclause[idx], tmp, res);
		}

	}
	if ((pf_mode == lpf_inprocess) && first) {
		if (verbosity == 1) printf("no parent-of-empty-clause with a t-clause. should be unsat. \n");		
		// we are not returning here because we want the memory cleanup in the end; 
	}
	else union_vec(res, *Top_TClause, assump_literals); // adding the literals from the top chain 
	if (opt_reverse_pf) {
		int sz = assump_literals.size(); // reversing order just to test the effect. 
		for (int i = 0; i < sz / 2; ++i) {
			Lit t = assump_literals[i]; 
			assump_literals[i] = assump_literals[sz-1-i]; 
			assump_literals[sz-1-i] = t;
		}
	}
    // delete allocated vectors
    for (auto iter = map_cls_to_Tclause.begin(); iter != map_cls_to_Tclause.end(); ++iter){
        delete iter->second;
    }
	//printClause(assump_literals, "new assum literals");
	//printf("---------------------\n");
}



