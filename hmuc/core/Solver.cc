/***************************************************************************************[Solver.cc]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

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
static IntOption     opt_exp			   (_cat, "exp", "experiment index (not used in solver. only used externally, in bench) ", 0, IntRange(0,4));
static IntOption     opt_pf_z_budget	   (_cat, "pf_z_budget", "# of restarts we budget for building a proof in case we already know it is unsat", 40, IntRange(0,4000));
static BoolOption    opt_pf_reset_z_budget (_cat, "pf_reset_z_budget", "upon detection of unsat by assumptions, resets zombie-budget", false); 
static BoolOption    opt_pf_unsatopt	   (_cat, "pf_unsatopt", "unsat by assumptions: remove more clauses", false); 
static BoolOption    opt_pf_force		   (_cat, "pf_force", "Apply pf/lpf... even after unsat by assumptions (i.e., cone is irrelevant). Based on retaining resolution and clauses until a new unsat-without-assumptions appears. \n", false);
//static BoolOption    opt_trace		        
//=================================================================================================
// Constructor/Destructor:

uint32_t Clause::icUid = 0;

Solver::Solver() :

    // Parameters (user settable):
    //
  m_nSatCall(0), m_nUnsatPathFalsificationCalls(0),
  verbosity        (1)
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
  , pf_unsatopt		 (opt_pf_unsatopt)  
  , pf_force		 (opt_pf_force)
  , retain_proof     (opt_pf_unsatopt || opt_pf_force)
  , removed_from_learnts (false)
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

bool Solver::addClause_(vec<Lit>& ps, bool ic, vec<uint32_t>* parents)
{
    assert(decisionLevel() == 0);
    if (!ok) return false;

    // Check if clause is satisfied and remove false/duplicate literals:
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

    if (ic)
    {
        resol.AddNewResolution(ca[cr].uid(), cr, (parents == NULL) ? icParents : *parents);
    }

    return true;
}

void Solver::attachClause(CRef cr) {
    const Clause& c = ca[cr];	
    assert(c.size() > 1);
    watches[~c[0]].push(Watcher(cr, c[1]));
    watches[~c[1]].push(Watcher(cr, c[0]));
    if (c.learnt()) learnts_literals += c.size();
    else            clauses_literals += c.size(); }

void Solver::detachClause(CRef cr, bool strict) {
    const Clause& c = ca[cr];
    assert(c.size() > 1);
    int x = c.ic()? c.uid(): 0;
    if (strict){
        remove(watches[~c[0]], Watcher(cr, c[1]));
        remove(watches[~c[1]], Watcher(cr, c[0]));
    }else{
        // Lazy detaching: (NOTE! Must clean all watcher lists before garbage collecting this clause)
        watches.smudge(~c[0]);
        watches.smudge(~c[1]);
    }

    if (c.learnt()) learnts_literals -= c.size();
    else            clauses_literals -= c.size(); }

void Solver::removeClause(CRef cr) {
    Clause& c = ca[cr];	
    if (c.size() > 1)
        detachClause(cr);  // remove watches
    // Don't leave pointers to freed memory! // ?
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    if (c.ic() && c.mark() != 2)
        resol.DeleteClause(c.uid());  // remove reference to clause from resolution node
    c.mark(1); // the clause is no longer relevant; can be erased. 
    ca.free(cr);  // does not really free the clause. Only increases the counter of wasted space. The memory itself will be freed once in a while. 
}

bool Solver::satisfied(const Clause& c) const {	
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at the given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
	//printf("cancel-until %d %d\n", trail.size(), trail_lim[level]);
	if (decisionLevel() > level){
		//printf("trail size = %d\n", trail.size());
		for (int c = trail.size()-1; c >= trail_lim[level]; c--){
			Var      x  = var(trail[c]);
			//printf("%d ",x);
			assigns [x] = l_Undef;
			if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last()) {				
				polarity[x] = sign(trail[c]);
			}
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

    // Random decision: // ofer removed
/*    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }
			*/
    // Activity based decision:
    while (next == var_Undef || value(next) != l_Undef || !decision[next])
        if (order_heap.empty()){
            next = var_Undef;
            break;
        }else
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
void Solver::analyze(CRef confl, vec<Lit>& out_learnt, int& out_btlevel, vec<uint32_t>& icParents)
{
    int pathC = 0;
    Lit p     = lit_Undef;

    // Generate conflict clause:
    //
    out_learnt.push();      // (leave room for the asserting literal)
    int index   = trail.size() - 1;

    do{
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.learnt() && !opt_glucose)
            claBumpActivity(c);

        if (c.ic())
        {
            icParents.push(c.uid());
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

    // Simplify conflict clause:
    //
    int i, j;
    out_learnt.copyTo(analyze_toclear);
    if (ccmin_mode == 2){
        uint32_t abstract_level = 0;
        for (i = 1; i < out_learnt.size(); i++)
            abstract_level |= abstractLevel(var(out_learnt[i])); // (maintain an abstraction of levels involved in conflict)

        for (i = j = 1; i < out_learnt.size(); i++)
            if (reason(var(out_learnt[i])) == CRef_Undef || !litRedundant(out_learnt[i], abstract_level, icParents))
                out_learnt[j++] = out_learnt[i];
        
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
bool Solver::litRedundant(Lit p, uint32_t abstract_levels, vec<uint32_t>& icParents)
{
    analyze_stack.clear(); analyze_stack.push(p);
    int top = analyze_toclear.size();
    int icTop = icParents.size();
    while (analyze_stack.size() > 0){
        Var v = var(analyze_stack.last());
        assert(reason(v) != CRef_Undef);
        Clause& c = ca[reason(v)]; analyze_stack.pop();
        if (!opt_ic_simplify && c.ic())
        {
            for (int j = top; j < analyze_toclear.size(); j++)
                seen[var(analyze_toclear[j])] = 0;
            analyze_toclear.shrink(analyze_toclear.size() - top);
            icParents.shrink(icParents.size() - icTop);
            return false;
        }
        else if (c.ic())
        {
            icParents.push(c.uid());
        }

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
void Solver::analyzeFinal(Lit p, vec<Lit>& out_conflict)
{
    icParents.clear();
	out_conflict.clear();
    out_conflict.push(p);
#ifndef NDEBUG
	for (int j = 0; j < seen.size(); j++) assert(seen[j] == 0);  
#endif
    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(trail[i]); // originally was ~trail[i]. But we want the assumptions themselves.
            }else{
                Clause& c = ca[reason(x)];
				if (c.ic()) icParents.push(c.uid()); 
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0) 
                        seen[var(c[j])] = 1;
            }
            seen[x] = 0;
        }
    }

    seen[var(p)] = 0;
#ifndef NDEBUG
	for (int j = 0; j < seen.size(); j++) assert(seen[j] == 0);  
#endif
}


void Solver::uncheckedEnqueue(Lit p, CRef from)
{
    assert(value(p) == l_Undef);
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

    for (;;) 
    {
        while (qhead < trail.size()){
            Lit            p   = trail[qhead++];     // 'p' is enqueued fact to propagate.
            vec<Watcher>&  ws  = watches[p];
            Watcher        *i, *j, *end;
            num_props++;

            for (i = j = (Watcher*)ws, end = i + ws.size();  i != end;){
                // Try to avoid inspecting the clause:
                Lit blocker = i->blocker;
                if (value(blocker) == l_True){
                    *j++ = *i++; continue; }

                // Make sure the false literal is data[1]:
                CRef     cr        = i->cref;
                Clause&  c         = ca[cr];				
				//int x = c.ic() ? c.uid(): 0;
				//printf("cr=%d,", cr); 	
				//printClause(stdout,c);
				//printf("[%d]", c.mark());
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
                if (value(first) == l_False){  // found conflict
                        confl = cr;
                        qhead = trail.size();
                        // Copy the remaining watches:
                        while (i < end)
                            *j++ = *i++;
                }
                else  // unit propagation
                {
                    if ((decisionLevel() == 0) && c.ic())  // decisionlevel = 0 means that these are facts which are independent of ICs (facts dependent on ICs are kept at decisionlevel 1). We replace the clause by the unit that it implies. It is all because units of ICs are treated differently. 
                    {
                        add_tmp.clear();
                        add_tmp.push(first);
                        uint32_t uid = c.uid();
                        // after allocating new clause c cannot be used because of possible memory relocation
                        CRef newCr = ca.alloc(add_tmp, false, true);
                        Clause::DecreaseUid();
                        ca[newCr].uid() = uid;
                        ca[cr].mark(2); // do not erase from resolution inside removeClause below. 
                        removeClause(cr);
                        resol.UpdateInd(uid, newCr);
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
                        {
                            uncheckedEnqueue(first, cr);
                        }
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



void Solver::reduceDB()
{
	LOG("");
	int     i, j;	
	double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity
	removed_from_learnts = true;
	//checkuids(ca, "before reducedb");
	sort(learnts, reduceDB_lt(ca));
	// Don't delete binary or locked clauses. From the rest, delete clauses from the first half
	// and clauses with activity smaller than 'extra_lim':
	int cnt = 0;
	for (i = j = 0; i < learnts.size(); i++) {
		Clause& c = ca[learnts[i]];
		int mark = c.mark();
		//assert(c.mark() != 3); // this assertion is not necessarily true because we can have '3' clauses that were not removed from learnts before simply because this function was not called. 
		if (mark== 0 && c.size() > 2 && !locked(c) && (i < (learnts.size()) / 2 || c.activity() < extra_lim))  
		{
			removeClause(learnts[i]);
			cnt++;
		}
		else // maintains in learnt those that are not removed 
		{
			if (mark != 1 && mark != 3 && mark != 4)  
				learnts[j++] = learnts[i];
			if (mark == 4) pf_learnts_forceopt_current.push(learnts[i]);  // we need those for relocation inside checkgarbage/relocall
			if (mark == 3) pf_learnts_forceopt_accum.push(learnts[i]);  // we need those for relocation inside checkgarbage/relocall
		}
	}
	
	learnts.shrink(i - j);
	checkGarbage();
	resol.CheckGarbage();	
	//checkuids(ca, "after reducedb");
}

void Solver::removeSatisfied(vec<CRef>& cs)  // called with e.g. 'learnts'; remove clauses that are satisfied at level 0 and shrinks learnts. 
{
	LOG("");
    int i, j;
    for (i = j = 0; i < cs.size(); i++) {
        Clause& c = ca[cs[i]];
        if (c.mark() == 1)  // no watches on this clause anyway 
            continue;
        if (c.mark() == 0 && satisfied(c)) //!! was c.mark() != 2. Changed since we started using mark(3), and we do not want to remove those clauses. 
        {
            removeClause(cs[i]);
        }
        else
            cs[j++] = cs[i];
    }
    cs.shrink(i - j);
	//printf("learnts after removesatisfied: %d\n", cs.size());
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
|    Simplify the clause database according to the current top-level assignment. Currently, the only
|    thing done here is the removal of satisfied clauses, but more things can be put here.
|________________________________________________________________________________________________@*/
bool Solver::simplify()
{
    assert(decisionLevel() == 0);
	LOG("");
    if (!ok || propagate() != CRef_Undef)
        return ok = false;

    if (nAssigns() == simpDB_assigns || (simpDB_props > 0))
        return true;

    // Remove satisfied clauses:

    removeSatisfied(learnts);
    if (remove_satisfied)        // Can be turned off.    
      removeSatisfied(clauses);
    removeSatisfied(icUnitClauses);
    checkGarbage();
    resol.CheckGarbage();
    rebuildOrderHeap();

    simpDB_assigns = nAssigns();
    simpDB_props   = clauses_literals + learnts_literals;   // (shouldn't depend on stats really, but it will do for now)

    return true;
}

bool Solver::pf_early_unsat_terminate() { // default is true
	LOG("");
	if ((opt_always_prove && (pf_zombie_iter <= opt_pf_z_budget)) || 
		(opt_max_fcls_in_arow && (++m_nUnsatPathFalsificationCalls == opt_max_fcls_in_arow))
		) { 
		pf_active = false;
		pf_zombie = true; // from here on we know already that it is unsat because we found a contradiction with the pf_literals, but we continue in order to get a proof.
		if (opt_pf_reset_z_budget) pf_zombie_iter = 0; 
		m_nUnsatPathFalsificationCalls = 0;
		return false;	
	}	
	m_bUnsatByPathFalsification = true;
	nUnsatByPF++;
	m_bConeRelevant = false; // since we reached a contradiction based on assumptions, we cannot use the cone, i.e., the cone includes facts (e.g. -c) that were added owing to a meta-argument (path-falsification), but we cannot extract an accurate core from this without an additional SAT run. 		
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
	LOG("");
    assert(ok);
    int         backtrack_level;
    int         conflictC = 0;
    vec<Lit>    learnt_clause;
    starts++;
    CRef confl = CRef_Undef;
    icParents.clear();
	int prev_trail_size = 0;	
	int old_falsified_literals;
	
	
    for (;;){
        if (asynch_interrupt)
            return l_Undef;

#pragma region dec_level_0

		
		if (decisionLevel() == 0)
        {
            // Simplify the set of problem clauses:
            if (!simplify())  
            {
                return l_False;
            }

			if (!test_mode && !pf_zombie && resol.GetInd(nICtoRemove) == CRef_Undef) { // this can happen if simplify removes the clause at level 0; 
				printf("root removed by simplify. Early unsat\n");
				if (pf_early_unsat_terminate()) return l_False;				
			}

            newDecisionLevel(conflictC);  // from now we are at decision level 1.
            for (int nInd = 0; nInd < icUnitClauses.size(); ++nInd)  // going over units
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
					((m_bConeRelevant || pf_force) && (trail.size() > pf_prev_trail_size)) || 
					LiteralsFromPathFalsification.size() == 0  // if !m_bConeRelevant, then we only want to call compute_inprocess once, because the result is not changing. 
				)    				
		   )			 
		{
			if (lpf_compute_inprocess() == false) return l_False; // early termination
		}
		

						

#pragma endregion
        if (confl == CRef_Undef)
            confl = propagate();


#pragma region conflict_case
		if (confl != CRef_Undef){			
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 1) // a core based on interesting constraints. 
            {
                CreateParentsOfEmptyClause(confl);				
                return l_False;
            }

            if (decisionLevel() == 0) // a core without interesting constraints (only remainder clauses, which are those clauses that were already marked as being in the core); in the next step the core will be empty, so the process should terminate.
            {
                return l_False;  
            }

            learnt_clause.clear();
            analyze(confl, learnt_clause, backtrack_level, icParents);			
            if (opt_ic_as_dec && learnt_clause.size() > 1 && icParents.size() > 0 && !ca[confl].ic())
            {
                int index = trail.size() - 1;
                Lit l = trail[index];
                int dLevel = decisionLevel() + 1;
                // create a new decision level till ic clause
                while(!ca[reason(var(l))].ic())
                {
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
                analyze(confl, learnt_clause, bckTrack, icParents);				
                CRef cr = ca.alloc(learnt_clause, true, false);
                learnts.push(cr);		
                attachClause(cr);
                if (!opt_glucose)
                    claBumpActivity(ca[cr]);
                else
                    ca[cr].activity() = calculateDecisionLevels(learnt_clause);
                cancelUntil(opt_full_bck ? backtrack_level : dLevel-2);
                newDecisionLevel(conflictC);
                uncheckedEnqueue(opt_dec_l1 ? l : learnt_clause[0]);
            }
            else
            {
            if (learnt_clause.size() == 1)
            {
//                fprintf(flog, "b - %d : %d", backtrack_level, var(learnt_clause[0]) + 1);

                if (icParents.size() > 0)
                {
                    cancelUntil(1);
                    CRef cr = ca.alloc(learnt_clause, false, true);
                    icUnitClauses.push(cr);
                    resol.AddNewResolution(ca[cr].uid(), cr, icParents);
                    uncheckedEnqueue(learnt_clause[0], cr);
                 }
                else
                {
                    assert(backtrack_level == 0);
                    cancelUntil(0);
                    uncheckedEnqueue(learnt_clause[0]);
                }
            }
            else
            {
                cancelUntil(backtrack_level);
                CRef cr = ca.alloc(learnt_clause, true, icParents.size() > 0);
                learnts.push(cr);
                attachClause(cr);
                Clause& cl = ca[cr];
                if (!opt_glucose)
                    claBumpActivity(ca[cr]);
                else
                    ca[cr].activity() = calculateDecisionLevels(learnt_clause);
                if (cl.ic())
                {                    
					resol.AddNewResolution(cl.uid(), cr, icParents);
					
                }

                uncheckedEnqueue(learnt_clause[0], cr);
//                fprintf(flog, "b - %d :", backtrack_level);
//                printClause(flog, ca[cr]);
            }
            }

            varDecayActivity();
            if (!opt_glucose)
                claDecayActivity();

            if (--learntsize_adjust_cnt == 0){
                learntsize_adjust_confl *= learntsize_adjust_inc;
                learntsize_adjust_cnt    = (int)learntsize_adjust_confl;
                max_learnts             *= learntsize_inc;

            //    if (verbosity >= 1)
            //        printf("c | %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
            //               (int)conflicts, 
            //               (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
            //               (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

            icParents.clear();
            confl = CRef_Undef;
        }
#pragma endregion

#pragma region no_conflict_case
		else {   // NO CONFLICT          			
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts &&
                (!opt_local_restart || (conflictC - vecConfl[decisionLevel()]) >= nof_conflicts) || !withinBudget()) 
            {
                // Reached bound on number of conflicts:
				if (pf_zombie) {
					//printf("Z ");
					if (++pf_zombie_iter > opt_pf_z_budget) { // We spent too much time at trying to rebuild a proof; instead we'll declare it unsat and do not reuse the cone.
						m_bUnsatByPathFalsification = true;
						nUnsatByPF++;
						m_bConeRelevant = false;
						return l_False;
					}
				}
				//else printf("R ");						
				//printf("%d %d %d\n", conflictC, vecConfl[decisionLevel()], !withinBudget());
                progress_estimate = progressEstimate();				
                cancelUntil(1);
				
                return l_Undef; 
            }
			//printf("L: %d %d %f\n", learnts.size(), nAssigns(), max_learnts);
		    if ((learnts.size()-nAssigns() ) >= max_learnts)  
		 		reduceDB();  // Reduce the set of learnt clauses:

            Lit next = lit_Undef;

			if (pf_active) {  				
				while (decisionLevel() - 1 < LiteralsFromPathFalsification.size())  // literals in LiteralsFromPathFalsification are made assumptions
				{
					count_assump++;
					Lit p = ~LiteralsFromPathFalsification[decisionLevel() - 1]; 
					if (value(p) == l_True)  {// literal already implied by previous literals
						newDecisionLevel(conflictC);  // ?? why increase decision level if it is a satisfied literal. Seems to be used for the guard of the loop, but artificially increases the dec. level. 
						count_true_assump++;
					}
					else if (value(p) == l_False) { // literals in LiteralsFromPathFalsification lead to a contradiction by themselves                                                                     
						if (pf_early_unsat_terminate()) {
//							printf("contradiction with assumption %d\n", p);
							if (pf_unsatopt) {
								analyzeFinal(p, pf_assump_used_in_proof);  // fills pf_assump_used_in_proof with the used assumptions. 
								//	printfVec(pf_assump_used_in_proof, "assump used in proof");
							}							
							return l_False;
						}
						else break; //LiteralsFromPathFalsification.clear();
					}
					else 
					{
						next = p;  // this will become the assumption						
						break;
					}
				}
			}
            			
            if (next == lit_Undef) { // New variable decision:                
                decisions++;
                if ((next = pickBranchLit()) == lit_Undef) return l_True; // Model found:				
				//printf("%d (decisions = %d)\n", next, decisions);
            }
			//else printf("a%d\n", next);			
			/*printf("order_heap = ");
			for (int i = 0; i < order_heap.size(); i++)
				printf("%d ", order_heap[i]);
			printf("\n");*/
//			printf("next = %d\n", next);
            // Increase decision level and enqueue 'next'
            newDecisionLevel(conflictC);
            uncheckedEnqueue(next);
			
        }
#pragma endregion
    } // end of main loop
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
	
				/*printf("trail = ");
				for (int i = 0 ; i < trail.size(); ++i) printf("%d,",trail[i].x);
				printf("\n");*/
		  		LOG("");
				pf_prev_trail_size = trail.size();
				double before_time = cpuTime();								
				int old_falsified_literals = LiteralsFromPathFalsification.size();  // !! potential bug in statistics: if early-termination returns false, it resets this set. 
				int addLiterals = PF_get_assumptions(nICtoRemove, resol.GetInd(nICtoRemove), pf_force ? full : restricted);
				//printfVec(LiteralsFromPathFalsification, "lpf literals = ");
				time_for_pf += (cpuTime() - before_time);								
				printf("*** in process lpf = %d\n", addLiterals);
				if (addLiterals == 0) { // If no literals are added it means that all paths from root are satisfied (otherwise we would at least have the literals in root), and hence the result of the next iteration is bound to be UNSAT.
					if (pf_early_unsat_terminate()) return false;
				}
				pf_Literals += (addLiterals - old_falsified_literals);								
	
	return true;
}




// NOTE: assumptions passed in member-variable 'assumptions'.
lbool Solver::solve_()
{
	LOG("");
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

    if (verbosity >= 1){
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
	
    if (verbosity >= 1)
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

    if (verbosity > 0)
        printf("c Wrote %d clauses with %d variables.\n", cnt, max);
}


void Solver::checkuids(ClauseAllocator& ca, char* msg) {	// for testing. Checks that m_UidToData[uid].m_ClauseRef points to a clause c such that c.uid() == uid.
		printf("checking uids (%s) ", msg);
		fflush(stdout);
		for (int uid = 0; uid < resol.GetMaxUid(); ++uid) {
			CRef cr = resol.GetInd(uid); // in resolution:  m_UidToData[uid].m_ClauseRef;
			if (cr==CRef_Undef) continue;
			if (ca[cr].ic())
				if (ca[cr].uid() != uid) {
					printf("cr=%d, %d %d %d", cr, ca[cr].uid(), uid, ca[cr].mark());
					fflush(stdout);
					exit(1);
					//assert(0);
				}
		}
		printf(": ok\n");
		fflush(stdout);
	}


//=================================================================================================
// Garbage Collection methods:

void Solver::relocAll(ClauseAllocator& to)
{
	LOG("");
		
	// All watchers:
    //
    // for (int i = 0; i < watches.size(); i++)
    watches.cleanAll();
    for (int v = 0; v < nVars(); v++)
        for (int s = 0; s < 2; s++){
            Lit p = mkLit(v, s);            
            vec<Watcher>& ws = watches[p];
            for (int j = 0; j < ws.size(); j++)
                ca.reloc(ws[j].cref, to);
        }

    // All reasons:
    //
    for (int i = 0; i < trail.size(); i++){
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }
    
    // All learnt:
    
    for (int i = 0; i < learnts.size(); i++) 
    {
        ca.reloc(learnts[i], to);
        Clause& c = to[learnts[i]];
// 		assert(c.mark() != 3);   // this is not necessarily true when we get here via simplify/garbagecollect/ ... 
        if (c.ic()) {		  
          resol.UpdateInd(c.uid(), learnts[i]); 
		  assert(to[resol.GetInd(c.uid())].uid() == c.uid());			  
		}
    }		

	// clauses removed from learnts because they were marked '3' in previous iterations (as of the last golden proof) 
	
	for (int i = 0; i < pf_learnts_forceopt_accum.size(); i++) 
	{		
		ca.reloc(pf_learnts_forceopt_accum[i], to);
		Clause& c = to[pf_learnts_forceopt_accum[i]];
		assert(retain_proof);
		assert(c.mark() == 3);
		if (c.ic()) {
			resol.UpdateInd(c.uid(), pf_learnts_forceopt_accum[i]);
			assert(to[resol.GetInd(c.uid())].uid() == c.uid());
		}
	}

	// same, but for the current iteration
	for (int i = 0; i < pf_learnts_forceopt_current.size(); i++) 
	{
		assert(retain_proof);
		ca.reloc(pf_learnts_forceopt_current[i], to);  // 1st parameter sent by ref, hence get updated.
		Clause& c = to[pf_learnts_forceopt_current[i]];
		if (c.ic())
		{
			resol.UpdateInd(c.uid(), pf_learnts_forceopt_current[i]);
			assert(to[resol.GetInd(c.uid())].uid() == c.uid());
			  //if (ca[resol.GetInd(c.uid())].uid() != c.uid()) printf("gha2...");
		}
	}


    // All original:
    //
    for (int i = 0; i < clauses.size(); i++)
    {
        ca.reloc(clauses[i], to);
        Clause& c = to[clauses[i]];
        if (c.ic())
            resol.UpdateInd(c.uid(), clauses[i]);
    }

    for (int i = 0; i < icUnitClauses.size(); i++)
    {
        ca.reloc(icUnitClauses[i], to);
        Clause& c = to[icUnitClauses[i]];
        assert(c.ic());
        resol.UpdateInd(c.uid(), icUnitClauses[i]);
    }
}

void Solver::garbageCollect()
{
    // Initialize the next region to a size corresponding to the estimated utilization degree. This
    // is not precise but should avoid some unnecessary reallocations for the new region:
	LOG("");
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

/// see explanation in CreateParentsOfEmptyClause. The difference is that we activate this one at 1 < decision level < |assumptions| (or something like that...), which means that decisions were made.
/// this means that reason(v) if v is an assumption, is CRef_Undef.
void Solver::CreateParentsOfNegatedAssump(CRef ref)
{
	CRef confl = ref;
	int index   = trail.size() - 1;
	Var v = var_Undef;
	int nSeen = 0;
	int undefs = 0;
	vec<int>  saw; // holds the indices in 'seen' that we touched, for cleanup;
	resol.m_EmptyClauseParents.clear(); 
	for (;;) 
	{
	
		Clause& c = ca[confl];		
		if (c.ic())
		{
			icParents.push(c.uid()); 			
			resol.m_EmptyClauseParents.insert(c.uid()); 
		}

		for (int j = (v == var_Undef) ? 0 : 1 ; j < c.size(); j++)
		{
			v = var(c[j]);			
			printf("%d ", v);

			if (!seen[v] && level(v) > 0)
			{
				seen[v] = 1;
				saw.push(v); 
				++nSeen;
			}
		}

		if (nSeen == 0)
			break;

		// Select next clause to look at:
		//while (!seen[var(trail[index])] || reason(var(trail[index]) == CRef_Undef)) index--;
		int v;		
		while (1) {
			if (index < 0) { 				
				//printf("/ = %d\n", undefs); 
				for (int i = 0; i < saw.size(); ++i) {
					printf("%d,", saw[i]);
					seen[saw[i]] = 0;			
				}
				saw.clear(true); 
				return;
			}
			v = var(trail[index]);
			bool b1 = !seen[v];
			if (!b1) {
				bool b2 = reason(v) == CRef_Undef;
				if (!b2) break;
				undefs++;
			}
			index --;
		}
		confl = reason(v);
		
		seen[v] = 0;
		--nSeen;
	}
	
	printf("undefs = %d \n", undefs);
}

/// Goes over the trail of the current decision level (decision level 1, which here is like 0 in normal sat), and collects all the clauses that participated in the BCP.
/// These clauses together with the root (ref) can resolve the empty clause. 
void Solver::CreateParentsOfEmptyClause(CRef ref)
{
	assert (decisionLevel() == 1);
    m_bConeRelevant = true;
    CRef confl = ref;
    int index   = trail.size() - 1;
    Var v = var_Undef;
    int nSeen = 0;
    resol.m_EmptyClauseParents.clear();

    for (;;) 
    {
        assert(confl != CRef_Undef); // (otherwise should be UIP)
        Clause& c = ca[confl];

        if (c.ic())
        {
            icParents.push(c.uid());
            resol.m_EmptyClauseParents.insert(c.uid());
        }

        for (int j = (v == var_Undef) ? 0 : 1 ; j < c.size(); j++)
        {
            v = var(c[j]);
            assert(value(c[j]) == l_False);
            if (!seen[v] && level(v) > 0)
            {
                seen[v] = 1;
                ++nSeen;
            }
        }

        if (nSeen == 0)
            break;
        
        // Select next clause to look at:
        while (!seen[var(trail[index--])]);
        v     = var(trail[index+1]);
        confl = reason(v);
        seen[v] = 0;
        --nSeen;
    }
}

void Solver::GetUnsatCore(vec<uint32_t>& core, Set<uint32_t>& emptyClauseCone)
{
    emptyClauseCone.clear();
	core.clear();
    for (int nInd = 0; nInd < icParents.size(); ++nInd)
    {
        if (emptyClauseCone.insert(icParents[nInd])) {
				resol.GetOriginalParentsUids(icParents[nInd], core, emptyClauseCone);
		}
    }
}




void Solver::Remark(vec<uint32_t>& cone)
{	
	LOG("");
	resol.GetClausesCones(cone, 3, ca); // !! 
	printf("cone_Size remark= %d, learnts = %d\n", cone.size(), learnts.size());
	for (int i = 0; i < cone.size(); ++i)
	{
		CRef cr = resol.GetInd(cone[i]);
//		assert(cr != CRef_Undef);
		if (cr == CRef_Undef) continue;
		assert(ca[cr].mark() == 4 || ca[cr].mark() == 3);
		ca[cr].mark(3);
		resol.DecreaseReference_mark3(ca[cr].uid(), ca); // !!
		
	}
}

// used for removing subsumed IC clauses. We want to remove them and their descendants, but if a 
// descendant has yet another IC parent, we do not want to remove it, because we rely on a path
// from ICs to the empty clause when using optimization pf-mode=3/pf-mode=4.

void Solver::RemoveClauses_withoutICparents(vec<uint32_t>& cone, bool leaveMark3) {
	resol.GetAllIcUids(setGood, cone);  // setGood = clauses that all their parents are not IC
	resol.GetClausesCones(cone, -1, ca); // find all cones of the roots we started from
	cancelUntil(0);
	// cone contains all the clauses we want to remove
	for (int i = 0; i < cone.size(); ++i)
	{
		CRef cr = resol.GetInd(cone[i]);
		if (cr != CRef_Undef && setGood.has(cone[i]))
		{
			if (leaveMark3 && ca[cr].mark() == 3) continue;  // we need this because cone can contain roots of clauses from rotation. Their cone as computed by getclausescone above can contain mark3 clauses and we do not want to remove those.
			ca[cr].mark(0);
			removeClause(cr);
		}
	}
}

void Solver::RemoveClauses(vec<uint32_t>& cone, bool leaveMark3)
{
	LOG("");
    resol.GetClausesCones(cone, -1, ca);
    cancelUntil(0);

    // cone contains all the clauses we want to remove
    for (int i = 0; i < cone.size(); ++i)
    {
        CRef cr = resol.GetInd(cone[i]);
        if (cr != CRef_Undef)
        {
			if (leaveMark3 && ca[cr].mark() == 3) continue;  // we need this because cone can contain roots of clauses from rotation. Their cone as computed by getclausescone above can contain mark3 clauses and we do not want to remove those.
            ca[cr].mark(0);  // will be replaced with mark(removed) in removeClause below. Effectively this erases mark(2) if there was one. 
            removeClause(cr);
        }
    }
}

void Solver::RemoveEverythingNotInCone(Set<uint32_t>& cone, Set<uint32_t>& muc)
{
	LOG("");
    uidsVec.clear();    
    cone.copyTo(uidsVec);
    cancelUntil(0);
    sort(uidsVec);

    // cone contains all the clauses we want to remove
    int j = 0;
    for (uint32_t i = 0; i < resol.GetMaxUid(); ++i)
    {
        if (i != uidsVec[j] && !muc.has(i))
        {
            CRef cr = resol.GetInd(i);
            if (cr != CRef_Undef)
            {	
                // check that clause is not original otherwise we won't delete it
				Clause& c = ca[cr];
				assert(!c.ic() || i == c.uid());
                c.mark(0);
                removeClause(cr);
            }
        }
        else if (i == uidsVec[j] && j < uidsVec.size())
        {
            ++j;
        }
    }
}



void Solver::UnbindClauses(vec<uint32_t>& cone)
{
	LOG("");
	resol.GetClausesCones(cone, -1, ca);
	printf("cone_Size = %d, learnts_size = %d\n", cone.size(), learnts.size());
	cancelUntil(0);

	// cone contains all the clauses we want to remove
	for (int i = 0; i < cone.size(); ++i)
	{
		CRef cr = resol.GetInd(cone[i]);
		if (cr != CRef_Undef)
		{
			Clause& c = ca[cr];
			if (c.size() > 1)
			{
				detachClause(cr);
				// so we will be able to use lazy watch removal
				c.mark(1); 
			}
			else
			{
				c.mark(2);
			}
		}
	}

	watches.cleanAll();

	for (int i = 0; i < cone.size(); ++i)
	{
		CRef cr = resol.GetInd(cone[i]);
		if (cr != CRef_Undef)
		{
			Clause& c = ca[cr];
			if (c.size() > 1)
				c.mark(0);
		}
	}

}



/// temporary = true when called for unbinding a cone temporarily (starting a new iteration), until we know if the formula is unsat without that cone (if not, they will be revived). We mark them here with '4'.
/// temporary = false when called with unbinding of clauses that were found with the unsatopt optimization. Then we mark them with '3' (they will not be revived). 
void Solver::UnbindClauses_force(vec<uint32_t>& cone, bool temporary)
{
	LOG((temporary?"t":"f"));
    resol.GetClausesCones(cone, 3, ca); 
	printf("cone_Size %d= %d, learnts_size = %d\n", temporary, cone.size(), learnts.size());
    assert(decisionLevel() == 0);  // if this assertion does not fall, then we do not need the canceluntil(0) below. 
	cancelUntil(0);
    // now cone contains all the clauses we want to remove
    for (int i = 0; i < cone.size(); ++i)
    {
        CRef cr = resol.GetInd(cone[i]);
        if (cr != CRef_Undef)
        {
            Clause& c = ca[cr];	
			if (c.mark() == 3) continue;  // those were already detached.
			int x = c.ic() ? c.uid() : 0;
            if (c.size() > 1)
            {
                detachClause(cr);  // remove watches               
                c.mark(1);  // so we will be able to use lazy watch removal. Note that below it turns into c.mark(normal). Marking with 1 here, because watches.clearAll() below uses this marking to shrink the list. 
            }
            else
            {
                c.mark(2); // units. Note that units with mark > 0 are ignored inside search. Hence this is equivalent to erasing it from the list of ic units.
            }
        }
    }

    watches.cleanAll();  // removes watches of clauses that satisfy mark()==1
	int cnt = 0;
    for (int i = 0; i < cone.size(); ++i)
    {
		
        CRef cr = resol.GetInd(cone[i]);
        if (cr != CRef_Undef)
        {
            Clause& c = ca[cr];
			if (temporary) {
				c.mark(4);  
				cnt++; 				
			}
            else 
				if (c.size() > 1) {
                c.mark(3);   
				cnt++;
				}
        }
    }	
}

void Solver::BindClauses(vec<uint32_t>& cone, uint32_t startUid)  // called when SAT. 
{
	LOG("");

	vec<uint32_t> init(1);
	init[0] = startUid;
	//setGood is not cleared deliberately. This set is monotone: everything good stays good. It saves time in GetAllIcUids.
	resol.GetAllIcUids(setGood, init);  // setGood = all clauses in cone that their roots are in (startUid + remainder). Only those can be made remainder. 


	cancelUntil(0);  // after this line we are at decision level 0
	    
    for (int i = 0; i < cone.size(); ++i)
    {
        uint32_t uid = cone[i];
        CRef cr = resol.GetInd(uid);
        if (cr != CRef_Undef)
        {
            Clause& c = ca[cr];
			assert(!retain_proof || c.mark() == 4); // because cone is not supposed to include '3' clauses (this is guaranteed by unbindClauses, which computes the cone that eventually get here as a parameter)
            c.mark(0);
            if (setGood.has(uid))  // uid is in the cone of startUid (?); we add all clauses in that cone as remainder.
            {
                if (resol.GetParentsNumber(uid) == 0)  // original clauses
                {
                    c.mark(2);  // we do not erase original clauses, because they carry information tying the uid to the clause. Recall that this clause is unbound anyway, so it is ok that it is not erased and replicated below.  It is marked 2 so it won't be erased from resolution later on. 
                }
                else
                {
                    removeClause(cr); // because we will regenerate it below. 					
                }
				
                analyze_stack.clear();

                bool satClause = false;
                for (int litId = 0; litId < c.size(); ++litId)
                {
                    if (value(c[litId]) == l_True) 
                    {
                        satClause = true;
                        break;
                    }
                    else if (value(c[litId]) == l_False)
                    {
                        continue;  // skip literal
                    }
                    analyze_stack.push(c[litId]);  // those without a value
                }

                if (satClause)  // no point in adding a clause that is satisfied at level 0
                    continue;

                if (analyze_stack.size() == 0)  // found a clause unsat by current assignment at dec. level 0. This means we can end the whole process: the clauses that are in remainder (including those we added to that set because we know they are in the core), is contradicting. 
                {
                    ok = false;  
                    return;
                }

                if (analyze_stack.size() == 1)  // found an implied literal
                {
                    enqueue(analyze_stack[0]);
                }
                else  // a clause neither satisfied nor unsatisfied by current assignment is brought back to the formula
                {
                    CRef newCr = ca.alloc(analyze_stack, c.learnt(), false);  // last parameter false: it is not ic 
					// !!change later to:  if (c.learnt()) learnts.push(newCr) else 
                    clauses.push(newCr);
                    attachClause(newCr);
                    if (opt_use_clauses)
                        ++m_nSatCall;
                }
            }
            else
            {
                if (c.size() > 1)
                {
					if (retain_proof && removed_from_learnts) 
						learnts.push(cr); // clauses that we bind, were previously removed from learnts in relocall (if it was called).
                    attachClause(cr);
                }
            }
        }
    }
}

void Solver::GroupBindClauses(vec<uint32_t>& cone)
{
	LOG("");
	
	resol.GetAllIcUids(setGood, cone);
	LOG("after GetAllIcUids");
	resol.GetClausesCones(cone, 3, ca); // !!
	LOG("after getclausecones");
	
	// cone contains all the clauses we want to remove
    for (int i = 0; i < cone.size(); ++i)
    {
        uint32_t uid = cone[i];
        CRef cr = resol.GetInd(uid);
        if (cr != CRef_Undef)
        {

            Clause& c = ca[cr];
			if (c.mark() == 3) {				
				continue;  // Filtering out from 'rotation' mark3 clauses. 
			}
			assert(c.mark() != 4); // because we get here after bindclauses. 
            
			c.mark(0);

            if (!setGood.has(uid))            
                continue;            

            if (resol.GetParentsNumber(uid) == 0)
            {
                if (c.size() > 1)
                {
                    detachClause(cr); // in contrast to 'bindclauses' we get here with a group of clauses from rotation, which were not detached earlier. 
                    // so we will be able to use lazy watch removal
                    c.mark(1); 
                }
            }
            else
            {
                removeClause(cr);
            }
                
            analyze_stack.clear();

            bool satClause = false;
            for (int litId = 0; litId < c.size(); ++litId)
            {
                if (value(c[litId]) == l_True)
                {
                    satClause = true;
                    break;
                }
                else if (value(c[litId]) == l_False)
                {
                    continue;
                }
                analyze_stack.push(c[litId]);
            }

            if (satClause)
                continue;

            if (analyze_stack.size() == 0)  // the clause is unsat by the current assignment
            {
                ok = false;
                return;
            }

            if (analyze_stack.size() == 1)  // the current assignment imply a literal 
            {
                enqueue(analyze_stack[0]);
            }
            else
            {
                CRef newCr = ca.alloc(analyze_stack, c.learnt(), false);
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
        if (resol.ValidUid(uid) && resol.GetParentsNumber(uid) == 0)
        {
            CRef cr = resol.GetInd(uid);
            assert (cr != CRef_Undef);
            Clause& c = ca[cr];
			if (c.mark() == 3) continue;
            c.mark(2);
        }
    }
}

void Solver::printClause(FILE* f, const Clause& c)
{
    for (int i = 0; i < c.size(); i++)
       fprintf(f, "%s%d ", sign(c[i]) ? "-" : "", var(c[i])+1);
    fprintf(f, "0\n");
}

void Solver::CreateResolVertex(uint32_t uid)
{
    assert(icParents.size() == 0);
    resol.AddNewResolution(uid, CRef_Undef, icParents);
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




int Solver::PF_get_assumptions(uint32_t uid, CRef cr, get_assump_mode mode /*=restricted*/) // Returns the number of literals in the falsified clause.
{	
	LOG("");
    if (cr == CRef_Undef)  
        return 0;
   
	LiteralsFromPathFalsification.clear();
	assert(!m_bConeRelevant || pf_lits_in_all_cones.size() == 0);
	bool pf_relevant = (m_bConeRelevant || pf_lits_in_all_cones.size() > 0);  // if !m_bConeRelevant && pf_lits_in_all_cones.size() = 0 then there are no literals in the shared cut of all clauses removed since the last golden proof.
	
	if ((opt_pf_mode == lpf || opt_pf_mode == lpf_inprocess) && (mode != restricted || m_bConeRelevant) && !lpf_delay && pf_relevant)
	{			
		//printClause(stdout, ca[cr]);
		LPF_get_assumptions(uid, LiteralsFromPathFalsification, mode == restrict_to_used_assumptions); 
		//printf("literals returned by get_assumption = ("); 
		//for (int i = 0; i < LiteralsFromPathFalsification.size(); ++i) printf("%d ", LiteralsFromPathFalsification[i]); 
		//printf(")\n");			
		//printf("lpf found %d lits\n",LiteralsFromPathFalsification.size());
		//printfVec(LiteralsFromPathFalsification,"literals from lpf");
		return LiteralsFromPathFalsification.size();
	}
	else
	{
		Clause& c = ca[cr];
		//LiteralsFromPathFalsification.growTo(c.size());
		for (int i = 0; i < c.size(); ++i)
		{
			//if (!more_unsat_clauses_mode || (pf_assump_used_in_proof.size() > 0 && pf_assump_used_in_proof.binary_search(~c[i])))
			if (mode != restrict_to_used_assumptions || pf_assump_used_in_proof.binary_search(~c[i]))
				LiteralsFromPathFalsification.push(c[i]);
			//printf("%d ", c[i].x);
		}
	//	printf("pf = removed ic only.\n");
	}
	   
	

	if ((opt_pf_mode == pf || opt_pf_mode == lpf || opt_pf_mode == lpf_inprocess) && (mode!= restricted || m_bConeRelevant) && pf_relevant) // chain (pf). Either in pf mode, or lpf/lpf_inprocess when we are in delay. 
    {
        uidsVec.clear();
        resol.GetTillMultiChild(uid, uidsVec);

        for (int i = 0; i < uidsVec.size(); ++i)
        {
            CRef cr = resol.GetInd(uidsVec[i]);
            if (cr != CRef_Undef)
            {    
                Clause& c = ca[cr];
                for (int i = 0; i < c.size(); ++i)
                {
					//if (!more_unsat_clauses_mode || pf_assump_used_in_proof.binary_search(~c[i]))
					
					if (mode != restrict_to_used_assumptions || pf_assump_used_in_proof.binary_search(~c[i]))
						LiteralsFromPathFalsification.push(c[i]);
					if (mode==full) printf("pf_force added a clause\n");
                }	
            }
        }
    }
	//LiteralsFromPathFalsification.removeDuplicated_(); // !!ofer. removed for comparing to the original version. 
	

	//if (mode != restrict_to_used_assumptions) printfVec(LiteralsFromPathFalsification,"literals from pf");

    return LiteralsFromPathFalsification.size(); //nAddedClauses;
}



///  But it uses class Map which is multimap, which complicates it. Should be replaced with ordinary map.
bool Solver::CountParents(Map<uint32_t,uint32_t>& mapRealParents,uint32_t uid) // uid is either c itself, or the clause at the bottom of a chain
{
	LOG("");
	int current_id,m;
	std::queue<uint32_t> q; // compute number of parents in the cone of c
	int maxQ = 0;
	int initialSpan = 0;
	q.push(uid);	 
	bool first = true;

	while (!q.empty())
	{	
		if (opt_lpf_cutoff) {	
			maxQ = std::max((int)q.size(), maxQ);
			if (maxQ > 500) return false;  // magic cutoff number
		}
		current_id = q.front();
		q.pop();
		CRef curr_ref = resol.GetResolId(current_id);
		const Resol& r = resol.GetResol(curr_ref);

		for (m = 0 ; m < r.m_Children.size() ; m++)
		{
			CRef childUid = r.m_Children[m];
			if (!resol.ValidUid(childUid)) continue;
			CRef childClauseRef = resol.GetInd(childUid);				
			if ((pf_mode == lpf_inprocess) && (childClauseRef != CRef_Undef) &&  satisfied(ca[childClauseRef])) continue;	
			if (first && opt_lpf_cutoff) {
				++initialSpan;
				if (initialSpan > 400) return false;  // magic cutoff number			
			}
			if (mapRealParents.has(r.m_Children[m])) ++mapRealParents[r.m_Children[m]];	
			else
			{
				q.push(r.m_Children[m]);  
				mapRealParents.insert(r.m_Children[m], 1);
			}			
		}
		first = false;
	}	
	//printf("%d %d", initialSpan, maxQ);
	return true;
}


void Solver::printResGraph(uint32_t uid, vec<uint32_t>& parents_of_empty_clause, vec<Lit>& assumptions) // uid is either c itself, or the clause at the bottom of a chain
{
int current_id,m;
	std::queue<uint32_t> q; // compute number of parents in the cone of c
	q.push(uid);	
    Map<uint32_t,uint32_t> mapRealParents;
	mapRealParents.insert(uid,0);	
	
	while (!q.empty()) 
	{
		current_id = q.front();
		bool parent_of_empty; 
		parent_of_empty = false;
		if (parents_of_empty_clause.binary_search(current_id)) {
			printf("*"); 
			parent_of_empty =true;
		}
		else printf(" ");
	
		printf("id = %d (", current_id);
		CRef c = resol.GetInd(current_id); // the clause reference of c
		if (c == CRef_Undef) {
			printf("(deleted clause)");	
		}
		else {
			const Clause& cls = ca[c]; // the actual clause			
			for (int i=0 ; i < cls.size() ; i++){  // initially parent = c
				printf("%d ", cls[i]); 				
			}			
		}		
		q.pop();
		
		CRef curr_ref = resol.GetResolId(current_id);
		const Resol& r = resol.GetResol(curr_ref);
		if(r.m_Children.size()==0){  // no more children
			printf(")\n");
			continue;
		}
		printf(") children = ");
		for (m=0 ; m < r.m_Children.size() ; m++)
		{
			if (!resol.ValidUid(r.m_Children[m])) continue;
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


void Solver::ResGraph2dotty(uint32_t uid, vec<uint32_t>& parents_of_empty_clause, vec<Lit>& assumptions) // uid is either c itself, or the clause at the bottom of a chain
{
	int current_id,m;
	std::queue<uint32_t> q; // compute number of parents in the cone of c
	q.push(uid);	
	Map<uint32_t,uint32_t> mapRealParents;
	mapRealParents.insert(uid,0);	
	FILE *dot;
	std::stringstream edges;
	edges << " ";

		dot = fopen("tclause.dot", "w");
		fprintf(dot, "digraph tclause {\n");

	while (!q.empty()) 
	{
		current_id = q.front();
		bool parent_of_empty; 
		parent_of_empty = false;
		if (parents_of_empty_clause.binary_search(current_id)) {
			parent_of_empty =true;
		}
		
			fprintf(dot, "node[");
			if (parent_of_empty) fprintf(dot,"color=green,");			
			else fprintf(dot,"color=black,");
		
		
		CRef c = resol.GetInd(current_id); // the clause reference of c
		if (c == CRef_Undef) {
			fprintf(dot,"label=\"D\"");
		}
		else {
			const Clause& cls = ca[c]; // the actual clause
			fprintf(dot,"label=\"");
			for (int i=0 ; i < cls.size() ; i++){  // initially parent = c							
					if (assumptions.binary_search(cls[i])) fprintf(dot,"*");
					fprintf(dot,"%d ", cls[i]);				
			}
			fprintf(dot,"\"");
		}
		fprintf(dot,"]; n%d;\n",current_id);
		q.pop();

		CRef curr_ref = resol.GetResolId(current_id);
		const Resol& r = resol.GetResol(curr_ref);
		if(r.m_Children.size()==0){  // no more children		
			continue;
		}		
		for (m=0 ; m < r.m_Children.size() ; m++)
		{
			if (!resol.ValidUid(r.m_Children[m])) continue;		
			edges << "n" << current_id << " -> n" << r.m_Children[m] << ";" << std::endl;
			
			if(!mapRealParents.has(r.m_Children[m]))
			{				
				mapRealParents.insert(r.m_Children[m],0);
				q.push(r.m_Children[m]);
			}
		}		
	}	

		fprintf(dot,"%s};\n", edges.str().c_str());
		edges.clear();		
		fclose(dot);
}
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
 * we find such literals based on the equivalence: S(c) = \cap_{p \in parents(c)} S(p) \cup c, where S(c) is a set of literals that we attach to a clause c. 
 * For the root clause c (defined by the parameter "uid_root"), S(c) = c;
*/
/************************************************************************/
void Solver::LPF_get_assumptions(
	uint32_t uid_root, /**< uid of a clause that we are about to remove */ // Doxygen-friendly comments. 
	vec<Lit>& assump_literals, /**< to be filled with literals */
	bool more_unsat_clauses_mode /** when true, intersects the clauses literals with the set pf_assump_used_in_proof. */
	)
{
	LOG("");
	std::unordered_map<uint32_t, vec<Lit>* > map_cls_to_Tclause; // from clause index to its Tclause
	std::queue<uint32_t> queue;		
	Map<uint32_t,uint32_t> map_cls_parentsCount;  // maps from uid of clause, to the number of parents on the relevant cone of c, i.e., parents on paths from c to the empty clause.
	
	bool prefix = true; 
	int peakQueueSize = 0;
	vec<int> icUnits;	
	uint32_t uid_root_bck = uid_root;
	
	assert(m_bConeRelevant || pf_lits_in_all_cones.size() > 0); // because we check this before we go into this function. 

	if (prev_icParents.size() > 0) {  // if the result was unsat, this condition is true and we need to clear the previous list; otherwise this condition is false, and we use the parents_of_empty_clause form the last run that it was unsat.
		parents_of_empty_clause.clear();
		parents_of_empty_clause.growTo(prev_icParents.size());
		for (int i=0 ; i < prev_icParents.size() ; i++) { // prev_icParents holds the parents of the empty clause 
			parents_of_empty_clause[i] = prev_icParents[i];
		}	
		sort(parents_of_empty_clause); // sorted because we run binary-search on it later
	}		
	
	assert(parents_of_empty_clause.size()>0); // empty clause always has parents.
	
#pragma region compute_Top_Tclause

	vec<Lit>* Top_TClause = new vec<Lit>(); 
    CRef c = resol.GetInd(uid_root);  // the clause reference of c
    Clause& cc = ca[c];
//	printfVec(cc, "removing (c) ");

	if ((pf_mode == lpf_inprocess) && satisfied(cc)) {
		printf("root is satisfied\n");
		return; 	
	}
	
	// adding root to Top_TClause. 
	
	for (int i = 0; i < cc.size(); ++i)	
		if ((!more_unsat_clauses_mode || pf_assump_used_in_proof.binary_search(~cc[i])) 			 	
			// &&(m_bConeRelevant || pf_lits_in_all_cones.binary_search(cc[i]))
			)
			(*Top_TClause).push(cc[i]);

    // adding clauses in the unit-chain to Top_Tclause. 
	vec<uint32_t> uidvec_prefix; 	
	resol.GetTillMultiChild(uid_root, uidvec_prefix);
    
	for (int i = 0; i < uidvec_prefix.size(); ++i)  // for each clause in the prefix
	{
		CRef cr = resol.GetInd(uidvec_prefix[i]);
		if (cr != CRef_Undef)
		{    
			Clause& cl = ca[cr];
			for (int i = 0; i < cl.size(); ++i)
			{
				Lit l = cl[i];				
				if (pf_mode == lpf_inprocess) {
					if (value(l) == l_True) return;
				}
				if ((!more_unsat_clauses_mode || pf_assump_used_in_proof.binary_search(~l)) && 
					(m_bConeRelevant || pf_lits_in_all_cones.binary_search(l))
					)
					(*Top_TClause).push(l);
			}	
		}
	}    

	if (uidvec_prefix.size() > 0) {
		//assert(more_unsat_clauses_mode || Top_TClause->size() > 0); not true anymore since we added the search in pf_lits_in_all_cones
		uid_root = uidvec_prefix.last(); 
	}
/*	else { //!! seems like redundant given that we add the same clause higher up
			Clause& cl = ca[resol.GetInd(uid_root)];
			for (int i = 0; i < cl.size(); ++i)
			{
				Lit l = cl[i];				
				if (!more_unsat_clauses_mode || pf_assump_used_in_proof.binary_search(~l))
				(*Top_TClause).push(l);

        //ca[].copyTo(*Top_TClause);        
			}    	
	}
	*/
#pragma endregion

    bool proceed = CountParents(map_cls_parentsCount , uid_root);
    if (opt_lpf_cutoff && !proceed) { // add counter of parents in the cone. Returns false if we predict there is no point to spend too much time on it. 
		Top_TClause->copyTo(assump_literals);
		printf("cutoff\n");
		return;
	}
	
	sort(*Top_TClause);
	// from hereon uid_root is the bottom clause in the unit-chain, and its Tclause is the union of the clauses in the chain.
//	printfVec(*Top_TClause, "Top clause");
	map_cls_to_Tclause[uid_root] = new vec<Lit>();
	
	queue.push(uid_root);
	while (!queue.empty())
	{
		uint32_t curr_id = queue.front();
		queue.pop();		
		Resol& res = resol.GetResol(resol.GetResolId(curr_id));
		int children_num = res.m_Children.size();
		if (children_num == 0)  continue;
		peakQueueSize = std::max((int)queue.size(),  peakQueueSize);
//		printfVec(ca[curr_id], "curr_id");
		//bool has_valid_sibling = false;
		for(int i = 0; i < children_num; ++i)
		{				
			CRef childUid = res.m_Children[i];
			
			if (!resol.ValidUid(childUid)) continue;
			CRef childClauseRef = resol.GetInd(childUid);			
			
			if ((pf_mode == lpf_inprocess) && (childClauseRef != CRef_Undef) &&  satisfied(ca[childClauseRef]))					
			{				
				if (verbosity>2) printfVec(ca[childClauseRef], "satisfied. removed by lpf_inprocess");				
				continue; // lpf_inprocess. satisfied refers to current assignment. So this is relevant only if we call this function after at least one propagation in search.
			}					
			--map_cls_parentsCount[childUid]; // reducing parents count	

			// intersection with parents
			if (map_cls_to_Tclause.find(childUid) == map_cls_to_Tclause.end()) // first time we visit the clause
            {
				assert(map_cls_to_Tclause.count(curr_id)>0);
                map_cls_to_Tclause[childUid] = new vec<Lit>();
				map_cls_to_Tclause[curr_id]->copyTo(*map_cls_to_Tclause[childUid]);
			}
			else {  // otherwise we intersect the current Tclause with the one owned by the parent. 				
//				printfVec(*map_cls_to_Tclause[curr_id], "curr_id");
//				printfVec(*map_cls_to_Tclause[res.m_Children[i]], "child[i]");
                vec<Lit> intersection;
				Intersection(*map_cls_to_Tclause[curr_id], *map_cls_to_Tclause[childUid], intersection);  // intersection between Tclause-s of child and parent.                   
				map_cls_to_Tclause[childUid]->swap(intersection);
			}			

			// done with parents. Now we should add the clause's literals to its Tclause. 
			if(map_cls_parentsCount[childUid] == 0)  
			{ 
				vec<Lit> tmp_union;
				vec<Lit> temp_lit;
				if (childClauseRef != CRef_Undef) {  // in case that clause is erased, we do not have its literals to add to its Tclause. 
					ca[childClauseRef].copyTo(temp_lit);				
					sort(temp_lit);					

					if (more_unsat_clauses_mode) { // only follow literals in the set pf_assump_used_in_proof
						vec<Lit> temp_lit_projected;
						for (int i = 0; i < temp_lit.size(); ++i) {
							if (pf_assump_used_in_proof.binary_search(~temp_lit[i]) && (m_bConeRelevant || pf_lits_in_all_cones.binary_search(temp_lit[i])))  temp_lit_projected.push(temp_lit[i]);
						}
						if (temp_lit_projected.size() > 0) union_vec(*map_cls_to_Tclause[childUid], temp_lit_projected, tmp_union);					
					}
					else {
						
						assert(map_cls_to_Tclause.count(childUid)>0);
						union_vec(*map_cls_to_Tclause[childUid], temp_lit, tmp_union);
						if (!m_bConeRelevant) {
							vec<Lit> temp_intersect;
							Intersection(tmp_union, pf_lits_in_all_cones, temp_intersect);
							temp_intersect.swap(tmp_union);
						}						
					}
					


	//				printfVec(tmp_union, "union");				
					map_cls_to_Tclause[childUid]->swap(tmp_union);
					//tmp_union -> clear();
				}
				queue.push(childUid);					
			}
		}
	}    
	//printf(" %d", peakQueueSize);
	//if (prefix) printf("Top_TClause: (all one chain)\n");
	
	// we now intersect the Tclause-s of the parents of the empty clause	
	vec<Lit> tmp, res;
	bool first = true;
	for (int i = 0; i < parents_of_empty_clause.size(); ++i) {
		if (map_cls_to_Tclause.find(parents_of_empty_clause[i])== map_cls_to_Tclause.end()) continue; // only those that have T-clause are actual parents of the empty clause in cone(c). In some cases a node is a parent, but all paths to it were cut warlier by a clause that is currently satisfied. 
		
		if (first) {
			(*map_cls_to_Tclause[parents_of_empty_clause[i]]).swap(res);			
			first = false;
		}
		else {				
			tmp.swap(res);				
			res.clear();
			Intersection(*map_cls_to_Tclause[parents_of_empty_clause[i]], tmp, res);						
//			printfVec(res, "res - intersection");			
		}		
	}

	if ((pf_mode == lpf_inprocess) && first) {
		printf("no parent-of-empty-clause with a t-clause. should be unsat. \n"); 	
		test_now = true;

		//ResGraph2dotty(uid_root,parents_of_empty_clause, assump_literals);
		// we are not returning here because we want the memory cleanup in the end; 
	}
	//printf("\n");	
	else union_vec(res, *Top_TClause, assump_literals); // adding the literals from the top chain 

	if (opt_reverse_pf) {
		int sz = assump_literals.size(); // reversing order just to test the effect. 
		for (int i = 0; i < sz / 2; ++i) {Lit t = assump_literals[i]; assump_literals[i] = assump_literals[sz-1-i]; assump_literals[sz-1-i] = t;}
	}

	//printf(" %d\n", assump_literals.size());
	//ResGraph2dotty(uid_root, parents_of_empty_clause, assump_literals);
	//printResGraph(uid, parents_of_empty_clause, assump_literals);

		//printfVec(*Top_TClause, "Top_TClause (from chain)");
    // delete allocated vectors
    for (auto iter = map_cls_to_Tclause.begin(); iter != map_cls_to_Tclause.end(); ++iter)
    {
        delete iter->second;
    }	
	 //printf("--- exit get_Assumptions -----  \n");	
}



