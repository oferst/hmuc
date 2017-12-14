#pragma once
#include "ProofRebuilder.h"

namespace Minisat {

bool ProofRebuilder::memberOfClause(Uid u, const Lit& l) {
	if (sh->UidToCRef(u) == CRef_Undef) {
		for (auto& l1 : sh->getClause(u))
			if (l == l1)
				return true;
	}
	else {
		for (auto& l1 : sh->getDelayedRemoval(u))
			if (l == l1)
				return true;
	}
	return false;
}


ProofRebuilder::ProofRebuilder(SolverHandle* _sh, RebuilderContext* _ctx) :
	sh(_sh), ctx(_ctx) {
}

//Given that we located a conflict in a BL assumption (startingConflLit) and we have a previous proof of unsat that 
//explains the BL, we build a proof of all the BLs (-p0),...,(-pn) that are in conflict, as well as (p0,...,pn).
//left pre condition assumed is that for the previously found refutation, the parents of the empty clause have been 
//found, and their pivotsMap were calculated at that time. Those pivotsMap of PoEC are literals that for each two neighbouring
//parents, belong to the 'currParentUid' parent (the one with a higher position index), and the negation of the pivot belong to the 'left' parent.
void ProofRebuilder::RebuildProof(Lit startingConflLit, vec<Uid>& allPoEC) {
	ctx->getPivots(CRef_Undef).clear();
	ctx->getPivots(CRef_Undef).copyAll(sh->getPoEC_Piv());

	vec<Uid> new_icPoEC;
	//vec<Uid> new_remPoEC;
	vec<Uid> new_allPoEC;


	/********************************************************************
	//PART 1
	Build the 'easy' half of the new proof here.
	Define p0 := -initConfBL (the negation of a backbone literal). We
	prove newC = (p0 v p1 v ... v pn), and add it to
	'ic_parents_of_empty_clause' (if it's an ic clause), where negConflAssumptions are
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

		ctx->clearUpdates();
		Uid newUnit = proveBackboneLiteral(CRef_Undef, allPoEC, BL);
		
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
Uid ProofRebuilder::proveBackboneLiteral(
	const Uid currUid,
	const T& parents,
	const Lit& BL //input
	) {
	assert(BL != ctx->dummy);
	const Lit negBL = ~BL;

	//Check whether we encountered this parent before (and therefore have an update for it.
	//If an updated version exists, return it's Uid.
	if (ctx->isClauseUpdated(currUid))
		return ctx->getClausesUpdate(currUid);
	//We shouldn't call 'proveBackboneLiteral' on a clause that conatins negBL (and the checks below should guarentee it).
	assert(!memberOfClause(currUid, negBL));

	//If the clause isn't in the Rhombus of the original clause c's rhombus, it shouldn't be changed at all.
	if (!sh->inRhombus(currUid)) {
		ctx->mapClausesUpdate(currUid, currUid);
		recordClauseLits(currUid);//now the clause will return 'true' on future ctx->isClauseSeen(pUid) calls
		return currUid;

	}

	/******************************
	
		BackwardsTraversal
	
	******************************/

	if (!ctx->arePivotsKnown(currUid)) {
		//no pivots found - extract pivots using currUid'clause parents, result recoreded in 'RebuilderContext* ctx'.
		recordClausePivots(currUid, parents);
	}
	assert(ctx->arePivotsKnown(currUid));
	vec<Lit>& currPivots = ctx->getPivots(currUid);
	assert(currPivots.size() == parents.size());



	//here we iterate in reverse on the parents of the current clause 
	//and decide (by using the pivots that were used to create the clause), 
	//which parents are going to be explored next

	std::list<Uid> new_parents; //rename: add candidates
	// A reverse itrerator for the parents container (should be either a vec<Uid> or a Resol node)
	auto rIter = parents.rbegin();
	int j = currPivots.size()-1;
	for (; j >= 0; --j, --rIter) {//TODO: check that --rIter is the correct increment

		//current parent uid
		Uid pUid = *rIter;
		assert(pUid != CRef_Undef);
		//The current pivot literal, current parent ('pUid') is the right
		//antecadent for the resolvent created using this pivot
		Lit currPiv = currPivots[j];
		assert(j >= 0);//sanity check
		assert(j > 0 || currPiv == ctx->dummy); // if j==0 then currPiv is a dummy pivot.
		assert(j == 0 || currPiv != ctx->dummy);// if j>0 then currPiv is a real pivot.
		if (currPiv == negBL) // cut off the 'pUid' parent 
			new_parents.push_front(CRef_Undef);
		else
			new_parents.push_front(proveBackboneLiteral(pUid, sh->getResol(pUid), BL));
		assert(ctx->isClauseUpdated(pUid));
		assert(ctx->getClausesUpdate(pUid) == *new_parents.begin());
		assert(ctx->isClauseSeen(ctx->getClausesUpdate(pUid)));

		if (currPiv == BL) {
			//this means that the 'left' parent contains ~BL, which we want to cut off,
			//and in which case there is no point in continuing up this 'left' branch, we can avoid the 
			//recursive calls on all the leftmost parents, possibly saving time.
			break;
		}
	}

	/******************************

		Proof Reconstruction

	******************************/

	LitSet newClause;
	LitSet* currClause = &newClause;

	vec<Uid> actualParentsUsed;
	vec<Uid> actualIcParentsUsed;
	vec<Uid> actualRemParentsUsed;

	bool isIc;
	bool isPrevIc;
	bool isNextIc;

	for (auto iter = new_parents.begin(); j < currPivots.size(); ++j, ++iter) {
		assert(iter != new_parents.end());
		Uid rightP = *iter;
		assert(ctx->isClauseSeen(rightP));
		switch (findParentsUsed(*currClause, rightP, currPivots[j],BL)) {
		case Left:
			continue; //skip the right parent, only considers the left parent.
		case Either:
			if ((*currClause).size() <= ctx->getClause(rightP).size()) //Heuristic choice
				continue; //skip the right parent, only considers the left parent.
			//else we do the 'Right' case
		case Right:
#pragma region ClearParentsList
			actualParentsUsed.clear();
			actualIcParentsUsed.clear();
			actualRemParentsUsed.clear();
#pragma endregion
#pragma region SetRightParentInList
			isNextIc = sh->getClause(rightP).ic();
			isPrevIc = isNextIc;
			isIc = isPrevIc | isNextIc;
			if (isNextIc)
				actualIcParentsUsed.push(rightP);
			else
				actualRemParentsUsed.push(rightP);
			actualParentsUsed.push(rightP);
			currClause = &ctx->getClause(rightP);
			break;
#pragma endregion
		case Both:
#pragma region ResolveLeftAndRight

			//copy left parent if needed
			if (&newClause != currClause) {
				replaceContent(newClause, *currClause);
				currClause = &newClause;
			}

			resolveWithOverwrite(newClause, ctx->getClause(rightP));
#pragma endregion
#pragma region AddRightParentToList
			isNextIc = sh->getClause(rightP).ic();
			isPrevIc = isIc;
			isIc = isPrevIc | isNextIc;
			if (isNextIc)
				actualIcParentsUsed.push(rightP);
			else
				actualRemParentsUsed.push(rightP);
			actualParentsUsed.push(rightP);
#pragma endregion

		}
	}

	Uid newUid = CRef_Undef;
	if (actualParentsUsed.size() == 1) {//Optimization - if only one parent was used, we don't need to allocate the clasue, as it already exists in the DB.
		assert(currClause == &ctx->getClause(actualParentsUsed[0]));
		newUid = actualParentsUsed[0];
	}
	//otherwise (if more than one parent was used), need to allocate a new clause
	else {
		assert(&newClause == currClause);
		CRef newCRef = sh->allocClause(newClause, true, isIc);
		assert(CRef_Undef != newCRef);
		sh->allocResol(newCRef, actualParentsUsed,actualIcParentsUsed,actualRemParentsUsed);
		newUid = sh->CRefToUid(newCRef);
		assert(CRef_Undef != newUid);
		assert(!ctx->isClauseSeen(newUid));
		LitSet& c = ctx->getClause(newUid);
		assert(c.size() == 0);
		replaceContent(c, newClause);
	}
	assert(ctx->isClauseSeen(newUid));
	ctx->mapClausesUpdate(currUid, newUid);
	return newUid;
}


//Adds the literals in a clause 'uid' to the rebuilder data structure.
LitSet& ProofRebuilder::recordClauseLits(Uid uid) {
	LitSet* toClause;
	if (!ctx->isClauseSeen(uid)) {
		toClause = &ctx->getClause(uid);
		assert(toClause->size() == 0);
		copyClause(uid, *toClause);
	}
	else
		toClause = &ctx->getClause(uid);
	return *toClause;
}
//Reads the literals in from to the set to. The clause will be pulled from a sat solver through the use of the solver handler.
void ProofRebuilder::copyClause(Uid from, LitSet& to) {
	if (CRef_Undef != sh->UidToCRef(from))
		insertAll(sh->getClause(from), to);
	else
		insertAll(sh->getDelayedRemoval(from), to);
}

template<class T>
void ProofRebuilder::recordClausePivots(Uid uid, T& parents) {
	if (!ctx->arePivotsKnown(uid)) {
		LitSet clause;
		vec<Lit>& pivots = ctx->getPivots(uid);
		assert(pivots.size() == 0);
		pivots.push(ctx->dummy);
		for (auto p : parents) {
			Lit piv;
			piv = resolveWithOverwrite(clause, recordClauseLits(p));
			if (piv != ctx->dummy)
				pivots.push(piv);
		}
	}
}

//resolve the current clause with the previous 
//clause and return it's clause pivot literal 
//(with the current clauses' polarity). 
//WILL OVERWRITE the clause in 'S& set' to contain the result.
//set: 'left' parent, will contain the result.
//clause: 'right' parnet, the other parent used in the resolution.
template<class T, class S>
Lit ProofRebuilder::resolveWithOverwrite(T& leftLits, S& rightLits) {
	Lit piv = ctx->dummy;
	for (auto l : rightLits) {
		if (leftLits.find(~l) == leftLits.end())
			leftLits.insert(l);
		else {
			leftLits.erase(~l);
			if (piv != ctx->dummy) {
				throw ResolutionException("First pivot assign should be to a dummy lit"); //should only be assigned once.
			}
				
			piv = l;
			if (piv == ctx->dummy) {
				throw ResolutionException("Pivot assigned cannot be a dummy literal");//and it should be assigned a different value than the dummy Lit.
			}
		}
	}
	return piv;
}

//
ParentUsed ProofRebuilder::findParentsUsed(const LitSet& leftLits,const Uid rightParentUid,const Lit& piv,const Lit& BL){
	if (BL == piv || ctx->dummy == piv)
		return Right;
	if (BL == ~piv || CRef_Undef == rightParentUid)
		return Left;
	LitSet& rightLits = ctx->getClause(rightParentUid); // rightParent LitSet;
	bool inLeft = (leftLits.find(~piv) != leftLits.end());
	bool inRight = (rightLits.find(piv) != rightLits.end());
	//If in neither return 'Either' (i.e. 0).
	//if only inRight return 'Left' (i.e. 1), 
	//if only inLeft return 'Right' (i.e. 2), 
	//if in both return 'Both' (i.e. 3), 
	return (ParentUsed)(2*(int)inLeft +  (int)inRight);
}



}
