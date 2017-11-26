#pragma once
#include "ProofRebuilder.h"

namespace Minisat {

ProofRebuilder::ProofRebuilder(SolverHandle* _sh, RebuilderContext* _ctx) :
	sh(_sh), ctx(_ctx) {
	_ctx->getPivots(CRef_Undef).copyAll(_sh->getPoEC_Piv());
}

//Given that we located a conflict in a BL assumption (startingConflLit) and we have a previous proof of unsat that 
//explains the BL, we build a proof of all the BLs (-p0),...,(-pn) that are in conflict, as well as (p0,...,pn).
//left pre condition assumed is that for the previously found refutation, the parents of the empty clause have been 
//found, and their pivotsMap were calculated at that time. Those pivotsMap of PoEC are literals that for each two neighbouring
//parents, belong to the 'currParentUid' parent (the one with a higher position index), and the negation of the pivot belong to the 'left' parent.
void ProofRebuilder::RebuildProof(Lit startingConflLit, vec<Uid>& allPoEC) {
	vec<Uid> new_icPoEC;
	//vec<Uid> new_remPoEC;
	vec<Uid> new_allPoEC;


	/********************************************************************
	//PART 1
	Build the 'easy' half of the new proof here.
	Define p0 := -initConfBL (the negation of a backbone literal). We
	prove newC = (p0 v p1 v ... v pn), and add it to
	'ic_parents_of_empty_clause' (if it'clause ic), where negConflAssumptions are
	{p0, p1,...,pn}. Note that -p0, -p1,...,-pn will all be backbones, as
	they are assumption that are in conflict.
	*********************************************************************/
	//The negations of the assumptions in conflict (the negations of the backbones), will be filled with the conflicting assumption literals and create a new learned clause.
	vec<Lit> negConflAssumptions;
	//The ic parents of the clause (p0 v p1 v ... v pn) that will be learnt due to the conflicting assumptions literals.
	vec<Uid> confLits_icParents;
	//The remainder parents of the clause (p0 v p1 v ... v pn) that will be learnt due to the conflicting assumptions literals.
	vec<Uid> confLits_remParents;
	//All parents of the clause (p0 v p1 v ... v pn) that will be learnt due to the conflicting assumptions literals.
	vec<Uid> confLits_allParents;

	sh->analyzeConflictingAssumptions(startingConflLit, negConflAssumptions, confLits_icParents, confLits_remParents, confLits_allParents);
	//after analyzeFinal the vector negConflAssumptions contains all the set of negated BL that are in conflict - they are the reason for the current conflict - we will prove the  assumption (backbones) below.
	//confLits_icParents, confLits_remParents, confLits_allParents will contain all the reason clauses for the conflict - used in the resolution graph, as it is needed to allocate new resolution nodes.
	CRef newCr = sh->allocClause(negConflAssumptions, true, confLits_icParents.size() > 0);
	sh->allocResol(newCr, confLits_allParents, confLits_icParents, confLits_remParents);
	Uid uid = sh->CRefToUid(newCr);
	if (confLits_icParents.size() > 0)
		new_icPoEC.push(uid);
	//else
	//	new_remPoEC.push(uid);
	new_allPoEC.push(uid);

	/********************************************************************
	PART 2
	Now we build seperate proofs for the clasues (-p0), (-p1), ..., (-pn)
	(the backbones) using backwards proof traveral on the rhombus of c. We
	cut off all dependencies on c by removing clauses containing 
	the seperating literals p_i - each one of them can define a p_i-cut
	in the rhombus. The resulting unit clauses (-p_i) are then added
	 to 'new_icPoEC' (if they're ic).
	*********************************************************************/
	
	//negBL are those literals 'l' that appear on every path between
	//the removed clause c and the empty clause - these are the 
	//literals we want to cut off from the proof graph.
	for (Lit negBL : negConflAssumptions) {

		//the backbone literal itself, what we aim to prove, ~l.
		Lit BL = ~negBL;

		
		Uid newUnit = BackwardsTraversal(CRef_Undef, allPoEC, BL); //change 
		
		if (sh->getResol(newUnit).header.ic)
			new_icPoEC.push(newUnit);
		/*no need to allocate a place for the empty clause, only need to keep track of the ic parents and the total list of parents (no remainders kept)
		//else
		//	new_remPoEC.push(newUnit);
		*/
		new_allPoEC.push(newUnit);

	}

}


//For our purposes - if on rhombus(c) we found a literal l 
//that appears on every path between c and the empty clause 
//(i.e. we have an l-cut), then ~BL is l and BL is ~l. In the 
//backwards traversal we assume that 'currUid' doesn't conatian ~BL.
//First we traverse backwards on the parents of 'currUid', and build
//a list of possible updated parents. Each new (updated) parent added to this 
//'new_parents' list is built by using a BackwardsTraversal on an original 
//parent from 'parents'.
//The only three exceptions to traversing an original parent are when:
// 1) the parent contains ~BL - in which case we cut off the search as 
//	we reached the ~BL-cut (l-cut) in the rhombus.
// 2) the parent was already traversed - in which case we simply add 
//	the previously calculated resulting clause to the 'new_parents' list.
// 3) the clause isn't in the rhombus at all, so we don't need to update 
//	it and we keep the parent the same (note that, after checking 1, 
//	this parent will never contain ~BL i.e., even if a parent
//	isn't in rhombus(c) it can be cut off in 1) if it conatins ~BL.

template<class T>
Uid ProofRebuilder::BackwardsTraversal(
	const Uid currUid,
	const T& parents,
	const Lit& BL //input
	) {
	const Lit negBL = ~BL;

	if (!ctx->arePivotsKnown(currUid)) {//
		assert(!ctx->seenClause(currUid));
		//no pivots found - extract pivots using currUid'clause parents, result recoreded in 'RebuilderContext* ctx'.
		extractClauseLits(currUid);
		addClausePivots(currUid, parents);
	}
	assert(ctx->seenClause(currUid));
	assert(ctx->arePivotsKnown(currUid));
	vec<Lit>& currPivots = ctx->getPivots(currUid);
	assert(currPivots.size() + 1 == parents.size());



	//here we iterate in reverse on the parents of the current clause 
	//and decide (by using the pivots that were used to create the clause), 
	//which parents are going to be explored next

	std::list<Uid> new_parents;
	// A reverse itrerator for the parents container (should be either a vec<Uid> or a Resol node)
	auto rIter = parents.rbegin();
	int j = currPivots.size() - 1;
	for (; j >= 0; --j, --rIter) {//TODO: check that --rIter is the correct increment

		//current parent uid
		Uid pUid = *rIter;

		//The current pivot literal, current parent ('pUid') is the right
		//antecadent for the resolvent created using this pivot
		Lit currPiv = currPivots[j];

		if (currPiv == negBL) // cut off the 'pUid' parent 
			new_parents.push_back(CRef_Undef);
		else if (ctx->seenClause(pUid)) // clause was seen already
			new_parents.push_back(ctx->getNewClauseUid(pUid));
		else if (!sh->inRhombus(pUid)) {//clause isn't supposed to be changed at all, taken as-is
			new_parents.push_back(pUid);
			ctx->mapClausesUpdate(pUid,pUid);

			//TODO: check whether 'seen' can be achived 
			extractClauseLits(pUid);//now the clause will return 'true' on future ctx->seenClause(pUid) calls
		}
		else {
			Uid newUid = BackwardsTraversal(pUid, sh->getResol(pUid), BL);
			new_parents.push_back(newUid);
			ctx->mapClausesUpdate(pUid, newUid);
			extractClauseLits(pUid);
		}
		if (currPiv == BL) {
			//this means that the 'left' parent contains ~BL, which we want to cut off
			//in which case there is no point in continuing up this 'left' brach, we can avoid the 
			//recursive calls on the all the leftmost parents, possibly saving time.
			new_parents.push_back(CRef_Undef);
			break;
		}
	}

	//up until now we visited only the 'right' parents (relative to the pivots)
	//which means that the first (0th) parent wasn't visited yet
	//
	//rebuild the last, 0, clause here.
	//This is only performed if we didn't cut off the branch before that (j=0 in case we never satisfied 
	//"currPiv == BL" in the loop above), and also the clause in 
	// allPoEC[0] doesn't contain ~BL - which only happens if 
	//the leftmost, 0, pivot isn't bl (if bl were the pivot, then 
	//it would have been be a member of the 'currParentUid'
	//parent, and the 'left' parent would have contained negbl). in the
	//case that the last, 0, parent contains negbl, we would already have
	//used push_back(cref_undef) to represent the'left ' parent being cut off.
	//
	if (0 == j && currPivots[0] != BL) {
		Uid pUid = *parents.begin();
		new_parents.push_back(BackwardsTraversal(pUid, sh->getResol(pUid), BL));
	}

	if (currPivots[currPivots.size() - 1] == BL)
		return *new_parents.begin();





	return CRef_Undef;
}

//template<class T,class S>
//bool ProofRebuilder::member(T& elem, S& container) {
//	return container.find(elem) != container.end();
//}


//Uid ProofRebuilder::reconstructClause(
//	const Uid currUid,//Initial clause uid (before updating the clause), input only.
//	const vec<Lit>& pivots,//The pivots used to resolve the parents of the original clause, input only.
//	const int initPivIdx,//The index of the first pivot actually used in reconstruction (corrolates to the first updated parnet in the list 'parentsUpdate'), input only.
//	const std::list<Uid>& new_parents, //The uids of the previously updated parnet, along with the pivots used on the un-updated parents, will construct a new clause with some subset of these parents, input only.
//	RebuilderContext& ctx
//	){
//	//now we need to rebuild the clause given all the parents_of_backbone we already rebuilt.
//	//the resulting (BL) clause will be added to the new parents of the empty clause.
//	vec<Uid> icParents;
//	vec<Uid> remParents;
//	vec<Uid> allParents;
//	auto i = new_parents.begin();
//	int j = initPivIdx;
//	
//	Uid  currParentUid = *i;
//	if (CRef_Undef == currParentUid) {
//		currParentUid = *(++i);
//		++j;
//	}
//	LitSet* currLits = &ctx.newClauses_lits[currParentUid];
//	allParents.push(currParentUid);
//	if (sh->getResol(currParentUid).header.ic)
//		icParents.push(currParentUid);
//	else
//		remParents.push(currParentUid);
//	LitSet newClause;
//
//
//	
//	for (auto i = new_parents.begin(); i != new_parents.end(); ++i, ++j) {
//		assert(j < currPivots.size());
//		Lit piv = pivots[j];
//
//	}
//	return CRef_Undef;
//
//	//return j;
//
//}

//Uid ProofRebuilder::updateClause(Uid uidClauseToUpdate, Lit BL, RebuilderContext& ctx) {
//	//if clause was already updated (it was visited befor in the backwards traversal), then return it'clause known update.
//	//UidToLitVec& pivots = pivotsDB;
//	if (ctx.clausesUpdates.find(uidClauseToUpdate) != ctx.clausesUpdates.end())
//		return ctx.clausesUpdates[uidClauseToUpdate];
//	Uid uidClauseUpdated;
//	//if the clause to update isn't in the rhombus, then don't change it (no recursive update is necessary here)
//	if (!inRhombus(uidClauseToUpdate))
//		uidClauseUpdated = uidClauseToUpdate;
//	else
//		//else (it'clause in the rhombus but wasn't updated), then a new clause
//		//will be added to the solver and to the resolution graph. This updated will be recorded in 
//		//clauseUpdates and it'clause sorted contnet will be added to newClauses_sorted
//		//uidClauseUpdated = ProveBackboneLiteral(uidClauseToUpdate, BL, pivots, clauseUpdates, newClauses_lits);//rebuild clause and record the resulting update
//		recordClauseLits(uidClauseUpdated);
//	return ctx.clausesUpdates[uidClauseToUpdate] = uidClauseUpdated;
//}

//uses map_cls_to_Tclause for membership queries on rhombus(c).
//bool ProofRebuilder::inRhombus(Uid uid) {
//	//assert(rhombusValid());
//	return sh->inRhombus(uid);
//}

//Adds the literals in a clause 'uid' to the rebuilder data structure.
LitSet& ProofRebuilder::extractClauseLits(Uid uid) {
	if (!ctx->seenClause(uid)) {
		LitSet& toClause = ctx->getClause(uid);
		assert(toClause.size() == 0);
		copyClause(uid, toClause);
	}
	return ctx->getClause(uid);
}
//Reads the literals in from to the set to. The clause will be pulled from a sat solver through the use of the solver handler.
void ProofRebuilder::copyClause(Uid from, LitSet& to) {
	if (CRef_Undef != sh->UidToCRef(from))
		insertAll(sh->getClause(from), to);
	else
		insertAll(sh->getDelayedRemoval(from), to);
}


template<class T>
void ProofRebuilder::addClausePivots(Uid uid, T& parents) {
	//LitSet& clause = ctx->getClause(uid);
	LitSet clause;
	vec<Lit>& pivots = ctx->getPivots(uid);
	assert(pivots.size() == 0);
	//pivots.clear();
	for (auto p : parents) {
		Lit piv;
		piv = resolve(clause, extractClauseLits(p));
		if(piv != mkLit(var_Undef))
			pivots.push(piv);
	}
}

//resolve the current clause with the previous 
//clause and return it'clause pivot literal 
//(with the current clauses' polarity).
//set: 'right' parent, will caontain the resolvent result
//clause: 'left' parnet, the other parent used in the resolution
template<class S, class C>
Lit ProofRebuilder::resolve(S& set, C& clause) {
	Lit piv = mkLit(var_Undef);
	for (auto l : clause) {
		if (set.find(~l) == set.end())
			set.insert(l);
		else {
			set.erase(~l);
			assert(piv == mkLit(var_Undef));
			piv = l;
		}
	}
	return piv;
}

//
ParentUsed ProofRebuilder::findParentsUsed(LitSet& leftLits, Uid rightParentUid, Lit piv){
	if (CRef_Undef == rightParentUid)
		return Left;
	LitSet& rightLits = ctx->getClause(rightParentUid); // rightParentUid];
	bool inLeft = (leftLits.find(~piv) != leftLits.end());
	bool inRight = (rightLits.find(piv) != rightLits.end());
	if (inLeft && inRight)
		return Both;
	else if (inLeft && !inRight)
		return Right;
	else if (!inLeft && inRight)
		return Left;
	else //!inLeft && !inRight
		return Either;
}
}
