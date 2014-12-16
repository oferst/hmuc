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
#include <queue>
#include <unordered_map>
#include <vector>
#include <sstream>
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
static BoolOption    opt_path_falsification (_cat, "path_falsification", "use path falsification", true);
static IntOption     opt_max_fcls_in_arow  (_cat, "max-false-in-a-row", "Max number of times to run path falsification in a row", 20, IntRange(0,INT32_MAX));
static BoolOption    opt_false_resol       (_cat, "false-resol", "use falsifying clause with resolution", true);


 
//=================================================================================================
// Constructor/Destructor:

uint32_t Clause::icUid = 0;

Solver::Solver() :

    // Parameters (user settable):
    //
  m_nSatCall(0), m_nUnsatPathFalsificationCalls(0),
  verbosity        (0)
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

    // Resource constraints:
    //
  , conflict_budget    (-1)
  , propagation_budget (-1)
  , asynch_interrupt   (false)  
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
        detachClause(cr);
    // Don't leave pointers to freed memory!
    if (locked(c)) vardata[var(c[0])].reason = CRef_Undef;
    if (c.ic() && c.mark() != 2)
        resol.DeleteClause(c.uid());
    c.mark(1); 
    ca.free(cr);

}

bool Solver::satisfied(const Clause& c) const {
    for (int i = 0; i < c.size(); i++)
        if (value(c[i]) == l_True)
            return true;
    return false; }


// Revert to the state at the given level (keeping all assignment at 'level' but not beyond).
//
void Solver::cancelUntil(int level) {
    if (decisionLevel() > level){
        for (int c = trail.size()-1; c >= trail_lim[level]; c--){
            Var      x  = var(trail[c]);
            assigns [x] = l_Undef;
            if (phase_saving > 1 || (phase_saving == 1) && c > trail_lim.last())
                polarity[x] = sign(trail[c]);
            insertVarOrder(x); }
        qhead = trail_lim[level];
        trail.shrink(trail.size() - trail_lim[level]);
        vecConfl.shrink(trail_lim.size() - level);
        trail_lim.shrink(trail_lim.size() - level);
    } }


//=================================================================================================
// Major methods:


Lit Solver::pickBranchLit()
{
    Var next = var_Undef;

    // Random decision:
    if (drand(random_seed) < random_var_freq && !order_heap.empty()){
        next = order_heap[irand(random_seed,order_heap.size())];
        if (value(next) == l_Undef && decision[next])
            rnd_decisions++; }

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
    out_conflict.clear();
    out_conflict.push(p);

    if (decisionLevel() == 0)
        return;

    seen[var(p)] = 1;

    for (int i = trail.size()-1; i >= trail_lim[0]; i--){
        Var x = var(trail[i]);
        if (seen[x]){
            if (reason(x) == CRef_Undef){
                assert(level(x) > 0);
                out_conflict.push(~trail[i]);
            }else{
                Clause& c = ca[reason(x)];
                for (int j = 1; j < c.size(); j++)
                    if (level(var(c[j])) > 0)
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
                    if (decisionLevel() == 0 && c.ic())
                    {
                        add_tmp.clear();
                        add_tmp.push(first);
                        uint32_t uid = c.uid();
                        // after allocating new clause c cannot be used because of possible memory relocation
                        CRef newCr = ca.alloc(add_tmp, false, true);
                        Clause::DecreaseUid();
                        ca[newCr].uid() = uid;
                        ca[cr].mark(2);
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
    int     i, j;
    double  extra_lim = cla_inc / learnts.size();    // Remove any clause below this activity

    sort(learnts, reduceDB_lt(ca));
    // Don't delete binary or locked clauses. From the rest, delete clauses from the first half
    // and clauses with activity smaller than 'extra_lim':
    for (i = j = 0; i < learnts.size(); i++){
        Clause& c = ca[learnts[i]];
        if (c.mark() == 0 && c.size() > 2 && !locked(c) && (i < learnts.size() / 2 || c.activity() < extra_lim))
            removeClause(learnts[i]);
        else
            if (c.mark() != 1)
                learnts[j++] = learnts[i];
    }
    learnts.shrink(i - j);
    checkGarbage();
    resol.CheckGarbage();
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

    for (;;){
        if (asynch_interrupt)
            return l_Undef;
        if (decisionLevel() == 0)
        {
            // Simplify the set of problem clauses:
            if (!simplify())  
            {
                return l_False;
            }

            newDecisionLevel(conflictC);
            for (int nInd = 0; nInd < icUnitClauses.size(); ++nInd)
            {
                Clause& c = ca[icUnitClauses[nInd]];
                if (c.mark() != 0)
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

        if (confl == CRef_Undef)
            confl = propagate();
        if (confl != CRef_Undef){
            // CONFLICT
            conflicts++; conflictC++;
            if (decisionLevel() == 1)
            {
                CreateUnsatCore(confl);
                return l_False;
            }

            if (decisionLevel() == 0) 
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

                if (verbosity >= 1)
                    printf("c | %9d | %7d %8d %8d | %8d %8d %6.0f | %6.3f %% |\n", 
                           (int)conflicts, 
                           (int)dec_vars - (trail_lim.size() == 0 ? trail.size() : trail_lim[0]), nClauses(), (int)clauses_literals, 
                           (int)max_learnts, nLearnts(), (double)learnts_literals/nLearnts(), progressEstimate()*100);
            }

            icParents.clear();
            confl = CRef_Undef;

        }
        else {   // NO CONFLICT          
            if (nof_conflicts >= 0 && conflictC >= nof_conflicts &&
                (!opt_local_restart || (conflictC - vecConfl[decisionLevel()]) >= nof_conflicts) || 
                !withinBudget()) 
            {
                // Reached bound on number of conflicts:
                progress_estimate = progressEstimate();
                cancelUntil(1);
                return l_Undef; 
            }

            if (learnts.size()-nAssigns() >= max_learnts)                  
				reduceDB();  // Reduce the set of learnt clauses:

            Lit next = lit_Undef;
/*
            while (decisionLevel() < assumptions.size()){
                // Perform user provided assumption:
                Lit p = assumptions[decisionLevel()];
                if (value(p) == l_True){
                    // Dummy decision level:
                    newDecisionLevel();
                }else if (value(p) == l_False){
                    analyzeFinal(~p, conflict);
                    return l_False;
                }else{
                    next = p;
                    break;
                }
            }
*/
            
            if (opt_path_falsification)  
            {				
                while (decisionLevel() - 1 < LiteralsFromPathFalsification.size())  // literals in LiteralsFromPathFalsification are made assumptions
                {
                    Lit p = ~LiteralsFromPathFalsification[decisionLevel() - 1]; 
                    if (value(p) == l_True)  // literal already implied by previous literals
                        newDecisionLevel(conflictC);  // ?? why increase decision level if it is a satisfied literal. Seems to be used for the guard of the loop, but artificially increases the dec. level. 
                    else if (value(p) == l_False) { // literals in LiteralsFromPathFalsification lead to a contradiction by themselves				                        
                        ++m_nUnsatPathFalsificationCalls;
                        if (m_nUnsatPathFalsificationCalls == opt_max_fcls_in_arow)
                        {
                            m_nUnsatPathFalsificationCalls = 0;
                            LiteralsFromPathFalsification.clear();
                        }
                        else
                        {
                            m_bUnsatByPathFalsification = true;
                            m_bConeRelevant = false;  // since we reached a contradiction based on assumptions, we cannot use the cone.
                            return l_False;
                        }
                    }
                    else 
                    {
                        next = p;  // this will become the assumption
                        break;
                    }
                }
            }


            if (next == lit_Undef) {
                // New variable decision:
                decisions++;
                next = pickBranchLit();
				// fprintf(flog, "d - %d\n", var(next)+1);

                if (next == lit_Undef)
                {                    
                    return l_True; // Model found:
                }
            }
			
            // Increase decision level and enqueue 'next'
            newDecisionLevel(conflictC);
            uncheckedEnqueue(next);
        }
    }
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

    if (verbosity >= 1){
        printf("c ============================[ Search Statistics ]==============================\n");
        printf("c | Conflicts |          ORIGINAL         |          LEARNT          | Progress |\n");
        printf("c |           |    Vars  Clauses Literals |    Limit  Clauses Lit/Cl |          |\n");
        printf("c ===============================================================================\n");
    }

    // Search:
    int curr_restarts = 0;
    while (status == l_Undef){
        double rest_base = luby_restart ? luby(restart_inc, curr_restarts) : pow(restart_inc, curr_restarts);
//        fprintf(flog, "Starts %d\n", curr_restarts);
        status = search(rest_base * restart_first);
        if (asynch_interrupt && status == l_Undef)
            return l_Undef;
//        fflush(flog);
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
        Var v = var(trail[i]);

        if (reason(v) != CRef_Undef && (ca[reason(v)].reloced() || locked(ca[reason(v)])))
            ca.reloc(vardata[v].reason, to);
    }
    
    // All learnt:
    //
    for (int i = 0; i < learnts.size(); i++) 
    {
        ca.reloc(learnts[i], to);
        Clause& c = to[learnts[i]];
        if (c.ic())
           resol.UpdateInd(c.uid(), learnts[i]);
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
    ClauseAllocator to(ca.size() - ca.wasted()); 

    relocAll(to);
    if (verbosity >= 2)
        printf("c |  Garbage collection:   %12d bytes => %12d bytes             |\n", 
               ca.size()*ClauseAllocator::Unit_Size, to.size()*ClauseAllocator::Unit_Size);
    to.moveTo(ca);
}

void Solver::CreateUnsatCore(CRef ref)
{
    if (decisionLevel() == 0)
        return;

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
    core.clear();
    for (int nInd = 0; nInd < icParents.size(); ++nInd)
    {
        if (emptyClauseCone.insert(icParents[nInd]))
            resol.GetOriginalParentsUids(icParents[nInd], core, emptyClauseCone);
    }
}

void Solver::RemoveClauses(vec<uint32_t>& cone)
{
    resol.GetClausesCones(cone);
    cancelUntil(0);

    // cone contains all the clauses we want to remove
    for (int i = 0; i < cone.size(); ++i)
    {
        CRef cr = resol.GetInd(cone[i]);
        if (cr != CRef_Undef)
        {
            ca[cr].mark(0);
            removeClause(cr);
        }
    }

    // check that all the clauses are actually removed
/*    for (int i = 0; i < cone.size(); ++i)
    {
        assert (resol.GetInd(cone[i]) == CRef_Undef);
        assert(resol.GetResolId(cone[i]) == CRef_Undef);
    }
*/
}

void Solver::RemoveEverythingNotInCone(Set<uint32_t>& cone, Set<uint32_t>& muc)
{
    uidsVec.clear();
    sort(uidsVec);
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
                ca[cr].mark(0);
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
    resol.GetClausesCones(cone);
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

void Solver::BindClauses(vec<uint32_t>& cone, uint32_t startUid)
{
    if (opt_bind_as_orig == 2)
    {
        vec<uint32_t> init(1);
        init[0] = startUid;
        resol.GetAllIcUids(setGood, init);
    }

    //resol.GetClausesCones(cone) - we don't need that because we pass the previous found set of nodes
    cancelUntil(0);

    // cone contains all the clauses we want to remove
    for (int i = 0; i < cone.size(); ++i)
    {
        uint32_t uid = cone[i];
        CRef cr = resol.GetInd(uid);
        if (cr != CRef_Undef)
        {
            Clause& c = ca[cr];
            c.mark(0);
            if ((opt_bind_as_orig == 1 && resol.GetParentsNumber(uid) == 0) ||
                (opt_bind_as_orig == 2 && setGood.has(uid)))
            {
                if (resol.GetParentsNumber(uid) == 0)
                {
                    c.mark(2); 
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

                if (analyze_stack.size() == 0)
                {
                    ok = false;
                    return;
                }

                if (analyze_stack.size() == 1)
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
            else
            {
                if (c.size() > 1)
                {
                    attachClause(cr);
                }
            }
        }
    }
}

void Solver::GroupBindClauses(vec<uint32_t>& cone)
{
    if (opt_bind_as_orig == 0)
    {
        return;
    }

    if (opt_bind_as_orig == 2)
    {
        resol.GetAllIcUids(setGood, cone);
        resol.GetClausesCones(cone);
    }

    // cone contains all the clauses we want to remove
    for (int i = 0; i < cone.size(); ++i)
    {
        uint32_t uid = cone[i];
        CRef cr = resol.GetInd(uid);
        if (cr != CRef_Undef)
        {

            Clause& c = ca[cr];
            c.mark(0);

            if ((opt_bind_as_orig == 1 && resol.GetParentsNumber(uid) > 0) ||
                (opt_bind_as_orig == 2 && !setGood.has(uid)))
            {
                continue;
            }

            if (resol.GetParentsNumber(uid) == 0)
            {
                if (c.size() > 1)
                {
                    detachClause(cr);
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

            if (analyze_stack.size() == 0)
            {
                ok = false;
                return;
            }

            if (analyze_stack.size() == 1)
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
            c.mark(2);
        }
    }
}

void Solver::printClause(FILE* f, Clause& c)
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


int Solver::PF_get_assumptions(uint32_t uid) // Returns the number of literals in the falsified clause. 
{
	static int count = 0;
    if (!opt_path_falsification)
        return 0;

    LiteralsFromPathFalsification.clear();
    if (uid == CRef_Undef)
        return 0;

    CRef cr = resol.GetInd(uid);
	if (cr == CRef_Undef) // it will be undefined when the last call was SAT 
        return -1;
    
	if (lpf && m_bConeRelevant)
	{			
		LPF_get_assumptions(uid, LiteralsFromPathFalsification); 
		//printf("(%d) literals returned by get_assumption = (", ++count); 
		//for (int i = 0; i < LiteralsFromPathFalsification.size(); ++i) printf("%d ", LiteralsFromPathFalsification[i]); 
		//printf(")\n");			
		//printf("counter of lits: %d\n",LiteralsFromPathFalsification.size());
		return LiteralsFromPathFalsification.size();
	}
	else
	{
		Clause& c = ca[cr];
		LiteralsFromPathFalsification.growTo(c.size());
		for (int i = 0; i < c.size(); ++i)
		{
			LiteralsFromPathFalsification[i] = c[i];
		}
	}
	   
	
	if (opt_false_resol && m_bConeRelevant)
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
                    LiteralsFromPathFalsification.push(c[i]);
                }	
            }
        }
    }
	LiteralsFromPathFalsification.removeDuplicated_();
	
	/*printf("falsified clause = ");
	for (int i = 0; i < LiteralsFromPathFalsification.size(); ++i) printf("%d ", LiteralsFromPathFalsification[i]); 
	printf("\n");*/



    return LiteralsFromPathFalsification.size(); //nAddedClauses;
}


static void printfIntVec(vec<uint32_t>& v, char *msg) {
	if (v == NULL) printf("NULL\n");
	printf("%s (", msg);	
	for (int i = 0; i < v.size(); ++i) {
		printf("%d ", v[i]);
	}
	printf(")\n");
}

static void printfLitVec(vec<Lit>& v, char *msg) {
	if (v == NULL) printf("NULL\n");
	printf("%s (", msg);	
	for (int i = 0; i < v.size(); ++i) {
		printf("%d ", v[i]);
	}
	printf(")\n");
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
	vec<Lit>& assump_literals /**< to be filled with literals */
	)
{
	std::unordered_map<uint32_t, vec<Lit>* > map_cls_to_Tclause; // from clause index to its Tclause
	std::queue<uint32_t> queue;	
	static vec<uint32_t> parents_of_empty_clause;  // parents of empty clause. Defined as static because when the result is SAT, we use the list from the last unsat.
	Map<uint32_t,uint32_t> map_cls_parentsCount;  // maps from uid of clause, to the number of parents on the relevant cone of c, i.e., parents on paths from c to the empty clause.
	bool prefix = true; 
	

	if (icParents.size() > 0) {  // if the result was unsat, this condition is true and we need to clear the previous list; otherwise this condition is false, and we use the parents_of_empty_clause form the last run that it was unsat.
		parents_of_empty_clause.clear();
		parents_of_empty_clause.growTo(icParents.size());
		for (int i=0 ; i < icParents.size() ; i++) { // icParents holds the parents of the empty clause 
			parents_of_empty_clause[i] = icParents[i];
		}	
		sort(parents_of_empty_clause); // sorted because we run binary-search on it later
	}
	
	//printfIntVec(parents_of_empty_clause,"parents of empty clause");
	
	assert(parents_of_empty_clause.size()>0); // empty clause always has parents.
    vec<Lit>* Top_TClause = new vec<Lit>(); 
    CRef c = resol.GetInd(uid_root);  // the clause reference of c
    Clause& cc = ca[c];
	
	// adding root to Top_TClause. 
	for (int i = 0; i < cc.size(); ++i)	
		(*Top_TClause).push(cc[i]);

    // adding clauses in the unit-chain to Top_Tclause. 
	vec<uint32_t> uidvec_prefix; 	
	resol.GetTillMultiChild(uid_root, uidvec_prefix);
    uint32_t last_in_chain;
	for (int i = 0; i < uidvec_prefix.size(); ++i)  // for each clause in the prefix
	{
		CRef cr = resol.GetInd(uidvec_prefix[i]);
		if (cr != CRef_Undef)
		{    
			Clause& cl = ca[cr];
			for (int i = 0; i < cl.size(); ++i)
			{
				(*Top_TClause).push(cl[i]);
			}	
		}
	}	
    
    
	if (uidvec_prefix.size() > 0) {
        assert(Top_TClause->size() > 0);
		uid_root = uidvec_prefix.last(); 
	}
	else {        
        ca[resol.GetInd(uid_root)].copyTo(*Top_TClause);        
	}
    sort(*Top_TClause);
	// from hereon uid_root is the bottom clause in the unit-chain, and its Tclause is the union of 
    map_cls_to_Tclause[uid_root] = new vec<Lit>();//Top_TClause;

    
    CountParents(map_cls_parentsCount , uid_root); // add counter of parents in the cone.
	
	queue.push(uid_root);
	while (!queue.empty())
	{
		uint32_t curr_id = queue.front();
		queue.pop();		
		Resol& res = resol.GetResol(resol.GetResolId(curr_id));
		int children_num = res.m_Children.size();
		if (children_num == 0)  continue;
		
		bool has_valid_sibling = false;
		for(int i = 0; i < children_num; ++i)
		{				
			if (!resol.ValidUid(res.m_Children[i])) continue;

			// reducing parents count	
            CRef childUid = res.m_Children[i];
			--map_cls_parentsCount[childUid];  

			// intersection with parents
			if (map_cls_to_Tclause.find(childUid) == map_cls_to_Tclause.end()) // first time we visit the clause			
            {   
				assert(map_cls_to_Tclause.count(curr_id)>0);  
                map_cls_to_Tclause[childUid] = new vec<Lit>();
				map_cls_to_Tclause[curr_id]->copyTo(*map_cls_to_Tclause[childUid]); 
			}
			else {  // otherwise we intersect the current Tclause with the one owned by the Top_TClause. 				
//				printfLitVec(*map_cls_to_Tclause[curr_id], "curr_id");
//				printfLitVec(*map_cls_to_Tclause[res.m_Children[i]], "child[i]");
                vec<Lit> intersection;
				Intersection(*map_cls_to_Tclause[curr_id], *map_cls_to_Tclause[childUid], intersection);  // intersection between Tclause-s of child and Top_TClause.                   
				map_cls_to_Tclause[childUid]->swap(intersection);
			}			

			// done with parents. Now we should add the clause's literals to its Tclause. 
			if(map_cls_parentsCount[childUid] == 0)  
			{ 
				vec<Lit> tmp_union;
				vec<Lit> temp_lit;
				if (resol.GetInd(childUid) != CRef_Undef) {  // in case that clause is erased, we do not have its literals to add to its Tclause. 
					ca[resol.GetInd(childUid)].copyTo(temp_lit);
					sort(temp_lit);

					assert(map_cls_to_Tclause.count(childUid)>0);
					union_vec(*map_cls_to_Tclause[childUid], temp_lit, tmp_union);					
					//printfLitVec(tmp_union, "union");				
					map_cls_to_Tclause[childUid]->swap(tmp_union);
					//tmp_union -> clear();
				}
				queue.push(childUid);					
			}
		}
	}    
	//if (prefix) printf("Top_TClause: (all one chain)\n");
	
	// we now intersect the Tclause-s of the parents of the empty clause
	// printf("parents_of_empty_clause: ");		
	vec<Lit> tmp, res;
	bool first = true;
	for (int i = 0; i < parents_of_empty_clause.size(); ++i) {
		if (map_cls_to_Tclause.find(parents_of_empty_clause[i])== map_cls_to_Tclause.end()) continue; // only those that have T-clause are actual parents of the empty clause in cone(c). 		
		
		if (first) {
			(*map_cls_to_Tclause[parents_of_empty_clause[i]]).swap(res);			
			first = false;
		}
		else {				
			tmp.swap(res);				
			res.clear();
			Intersection(*map_cls_to_Tclause[parents_of_empty_clause[i]], tmp, res);						
			//printfLitVec(*res, "res - intersection");			
		}		
	}
	//printf("\n");	
	union_vec(res, *Top_TClause, assump_literals); // adding the literals from the top chain 

	//ResGraph2dotty(uid, parents_of_empty_clause, assump_literals);
	//printResGraph(uid, parents_of_empty_clause, assump_literals);

	//	printfLitVec(*Top_TClause, "Top_TClause (from chain)");
    // delete allocated vectors
    for (auto iter = map_cls_to_Tclause.begin(); iter != map_cls_to_Tclause.end(); ++iter)
    {
        delete iter->second;
    }	
	 //printf("--- exit get_Assumptions -----  \n");	
}




///  But it uses class Map which is multimap, which complicates it. Should be replaced with ordinary map.
void Solver::CountParents(Map<uint32_t,uint32_t>& mapRealParents,uint32_t uid) // uid is either c itself, or the clause at the bottom of a chain
{
int current_id,m;
	std::queue<uint32_t> q; // compute number of parents in the cone of c
	q.push(uid);	 
	
	while (!q.empty())
	{
		current_id = q.front();
		q.pop();
		CRef curr_ref = resol.GetResolId(current_id);
		const Resol& r = resol.GetResol(curr_ref);
		
		for (m = 0 ; m < r.m_Children.size() ; m++)
		{
			if (!resol.ValidUid(r.m_Children[m])) continue;
			if (mapRealParents.has(r.m_Children[m])) ++mapRealParents[r.m_Children[m]];
			//if(mapRealParents[r.m_Children[m]]==0)  // we enter child to the queue only in the first time. 
			else
			{
				q.push(r.m_Children[m]);  
				mapRealParents.insert(r.m_Children[m], 1);
			}			
		}
	}
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