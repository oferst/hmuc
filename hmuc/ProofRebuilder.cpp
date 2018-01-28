#pragma once
#include "ProofRebuilder.h"
#include "core/SolverTypes.h"
namespace Minisat {
bool ProofRebuilder::memberOfClause(Uid u, const Lit& l) {
	if (u == CRef_Undef)
		return false;
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

/*
Given that we located a conflict in a BL assumption (startingConflLiteral) 
and we have a previous proof of unsat that explains the BL, we build 
a proof of all the BLs (-p0),...,(-pn) that are in conflict, as well 
as (p0,...,pn). Left precondition assumed is that for the previously 
found refutation, the parents of the empty clause have been found, and 
their pivotsMap were calculated at that time. Those pivotsMap of PoEC 
are literals that for each two neighboring parents, belong to the 
'currParentUid' parent (the one with a higher position index), and 
the negation of the pivot belong to the 'left' parent.
*/
void ProofRebuilder::RebuildProof(const Lit& startingConflLiteral, vec<Uid>& allPoEC, vec<Uid>& new_allPoEC, vec<Uid>& new_icPoEC) {
	ctx->getPivots(CRef_Undef).clear();
	ctx->getPivots(CRef_Undef).copyAll(sh->getPoEC_Piv());

	//PART 1
	/********************************************************************
	Build the 'easy' half of the new proof here.
	Define p0 := -initConfBL (the negation of a backbone literal). We
	prove newC = (p0 v p1 v ... v pn), and add it to
	'ic_parents_of_empty_clause' (if it's an ic clause), where negConflAssumptions are
	{p0, p1,...,pn}. Note that -p0, -p1,...,-pn will all be backbones, as
	they are assumption that are in conflict.
	*********************************************************************/
	//The negations of the assumptions in conflict (the negations
	//of the backbones), will be filled with the conflicting 
	//assumption literals and create a new learned clause.
	vec<Lit> negConflAssumptions;
	//The ic parents of the clause (p0 v p1 v ... v pn) 
	//that will be learned due to the conflicting assumptions literals.
	vec<Uid> confLits_icParents;
	//The remainder parents of the clause (p0 v p1 v ... v pn)
	//that will be learned due to the conflicting assumptions literals.
	vec<Uid> confLits_remParents;
	//All parents of the clause (p0 v p1 v ... v pn) that will
	//be learned due to the conflicting assumptions literals.
	vec<Uid> confLits_allParents;

	sh->analyzeConflictingAssumptions(startingConflLiteral, negConflAssumptions, confLits_icParents, confLits_remParents, confLits_allParents);

	Uid uid;
	ReconstructionResult result;
	std::list<ClauseData>& allParents = result.parentsCandidates;
	//after analyzeFinal the vector negConflAssumptions contains all the set of negated BL that are in conflict - they are the reason for the current conflict - we will prove the  assumption (backbones) below.
	//confLits_icParents, confLits_remParents, confLits_allParents will contain all the reason clauses for the conflict - used in the resolution graph, as it is needed to allocate new resolution nodes.
	allParents.push_front(ClauseData());
	ClauseData& newParent = result.parentsCandidates.front();
	if (confLits_icParents.size() == 0) {
		newParent.setNonIc(negConflAssumptions);
	}
	else {
		CRef newCr = sh->allocClause(negConflAssumptions, true, confLits_icParents.size() > 0);
		sh->allocResol(newCr, confLits_allParents, confLits_icParents, confLits_remParents);
		newParent.setIc(sh->CRefToUid(newCr));
		result.isIc = true; // a parent is ic, and therefore the resulting node is also ic.
	}
	//PART 2
	/********************************************************************
	Now we build separate proofs for the clauses (-p0), (-p1), ..., (-pn)
	(the backbones) using backwards proof traversal on the rhombus of c. We
	cut off all dependencies on c by removing clauses containing 
	the separating literals p_i - each one of them can define a p_i-cut
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
		allParents.push_front(ClauseData());
		ClauseData& newUnitParent = result.parentsCandidates.front();
		
		/******************************************************
			proveBackboneLiteral - The main work is done here
		*******************************************************/
		proveBackboneLiteral(CRef_Undef, allPoEC, BL, newUnitParent);
		
		result.isIc = result.isIc || Ic == newUnitParent.clauseType;
	}

	//Iterate over reconstruction result and find if there exists an ic parent at all.
	//If there exists an ic parent, allocate remainder resolution for every non ic parent found in the reconstruction
	if (result.isIc) {
		Uid unitUid = CRef_Undef;
		CRef newCr = CRef_Undef;
		for (ClauseData& newUnitParent : result.parentsCandidates) {
			switch (newUnitParent.clauseType) {
			case NonIc:
				newCr = sh->allocClause(*newUnitParent.clauseContent, true, false);
				assert(CRef_Undef != newCr);
				sh->allocNonIcResol(newCr);
				unitUid = sh->CRefToUid(newCr);
				assert(CRef_Undef != unitUid);

				break;
			case Ic:
				unitUid = newUnitParent.clauseUid;
				assert(CRef_Undef != unitUid);
				new_icPoEC.push(unitUid);

				break;
			case Unknown:
				throw(ResolutionException("A clause with 'Unknown' type was build"));
			}
			new_allPoEC.push(unitUid);
		}
	}
}

/*
For our purposes - if on rhombus(c) we found a literal l 
that appears on every path between c and the empty clause 
(i.e. we have an l-cut), then ~BL is l and BL is ~l. In the 
backwards traversal we assume that 'currUid' doesn't contain ~BL.
First we traverse backwards on the parents of 'currUid', and build
a list of possible updated parents. Each new (updated) parent added 
to this 'parentCandidates' list is built by using a 
BackwardsTraversal on an original 
parent from 'parents'.
The only three exceptions to traversing an original parent are when:
 1) the parent contains ~BL - in which case we cut off the search as 
	we reached the ~BL-cut (l-cut) in the rhombus.
 2) the parent was already traversed - in which case we simply add 
	the previously calculated resulting clause to the 'parentCandidates' 
	list.
 3) the clause isn't in the rhombus at all, so we don't need to update 
	it and we keep the parent the same (note that, after checking 1, 
	this parent will never contain ~BL i.e., even if a parent
	isn't in rhombus(c) it can be cut off in 1) if it contains ~BL.
*/
template<class T>
void ProofRebuilder::backwardsTraversal(
							const Uid currUid,
							const T& parents,
							const Lit& BL,
							const vec<Lit>& currPivots,
							std::list<ClauseData>& rebuiltparentsData){
	/*
	Here we iterate in reverse on the parents of the current clause 
	and decide (by using the pivots that were used to create the 
	clause), which parents are going to be explored next.
	*/
	Lit negBL = ~BL;
	//A reverse iterator for the parents container 
	//(should be either a vec<Uid> or a Resol node).
	auto rIter = parents.rbegin();
	int j = currPivots.size() - 1;
	for (; j >= 0; --j, --rIter) {
		//current parent uid
		Uid pUid = *rIter;  
		//The current pivot literal, current parent ('pUid') is the 
		//right antecedent for the resolvent created using this pivot
		Lit currPiv = currPivots[j];
		//assert(j >= 0);//sanity check
		//assert(j > 0 || currPiv == ctx->dummy); // if j==0 then currPiv is a dummy pivot.
		//assert(j == 0 || currPiv != ctx->dummy);// if j>0 then currPiv is a real pivot.
		
		rebuiltparentsData.push_front(ClauseData());
		ClauseData& currParent = rebuiltparentsData.front();
		if (currPiv == negBL) { // cut off the 'pUid' parent by skipping current parent (it's type is Unknown)
			continue;
		}
		else {
			proveBackboneLiteral(pUid, sh->getResol(pUid), BL, currParent);
		}
		if (currPiv == BL) {
			break;
			/*
			this means that the 'left' parent contains ~BL, which we 
			want to cut off, and in which case there is no point in 
			continuing up this 'left' branch, we can avoid the 
			recursive calls on all the leftmost parents, possibly 
			saving time.
			*/
		}
	}
}
void ProofRebuilder::reconstructClause(const Lit& BL, 
						const vec<Lit>& currPivots,
						ReconstructionResult& reconRes) {
	LitSet& newClause = reconRes.newClause;
	assert(newClause.size() == 0);
	bool& isIc = reconRes.isIc;

	LitSet* currClause = &newClause;
	bool isPrevIc;
	bool isRightParentIc;
	/*
	Determine the starting index for the forward iteration. 
	Recall that, previously, we iterated in reverse order on
	the original parents\pivots, all the while populating 
	candidate updated parents. Had we encountered a cut-off 
	point in the form of a piv==BL, then we resulted in a 
	partial list of candidates (relative to the list of 
	original parent) and, moreover, the candidates encountered 
	are the only those last parents in the original parents
	vector (we iterated in reverse on the parents). In order 
	to now iterate on the pivots (which correspond to the 
	original parents vector) in tandem with iterating on the 
	candidate parents, we start the iterating from an index 
	initiated on the difference between the size of the 
	original parents (equal to the number of pivots), and the 
	populated list of candidates parent
	*/
	int j = currPivots.size() - (reconRes.parentsCandidates.size());
	assert(j >= 0 && j < currPivots.size() - 1);
	//-1 because we must have at least one candidate parent
	auto parentIter = reconRes.parentsCandidates.begin();
	for (;j < currPivots.size(); ++j, ++parentIter) {
		bool isRightParentIc = (Ic == parentIter->clauseType);
		LitSet& lits = (isRightParentIc ?  ctx->getClauseLits(parentIter->clauseUid) : *parentIter->clauseContent);
		assert(!isRightParentIc || ctx->isIc(parentIter->clauseUid));
		ParentUsed pu = findParentsUsed(*currClause, lits, currPivots[j], BL);
		switch (pu) {
		//Skip the right parent, only considers the left parent.
		//Note that the left parent always a right parent in the 
		//previous iteration (except for the dummy parent in the 
		//beginning), which means that we don't need to do anything 
		//to record it, as if it was a useful parent, then it was 
		//added previously.
		case Left:
			break;
		//Heuristically check which clause is bigger. if the 
		//left parent is smaller, choose the left parent by 
		//skipping the right parent, otherwise, we choose the 
		//right parent by  doing the 'Right' case below.
		case Either:
			if ((*currClause).size() <= lits.size()) //Heuristic choice
				break;
		//Choose the right parent, and discard the rest. I.e., keep 
		//only the right parent as a candidate, while forgetting 
		//all previously chosen parents
		case Right:
			//Clear previous parents candidates list.
			reconRes.parentsUsed.clear();
			reconRes.parentsUsed.push_back(&(*parentIter));
			reconRes.isIc = isRightParentIc;
			//Set new right parent candidate in lists.
			currClause = &(lits);
			break;
		//Resolve left and right parents (left parent is the 
		//result of the previous iteration)
		case Both:
			//First, record right parent in list of candidates and 
			//track it's ic label.
			reconRes.parentsUsed.push_back(&(*parentIter));
			reconRes.isIc = isIc | isRightParentIc;

			//Next, copy left parent literals, if needed
			if (&newClause != currClause) {
				replaceContent(newClause, *currClause);
				currClause = &newClause;
			}
			//And lastly, resolve left and right parents
			resolveWithOverwrite(newClause, lits);

		}
	}
}


Uid ProofRebuilder::
			allocReconstructedClause(const Uid& currUid, 
								ReconstructionResult& reconRes) {
	//Must have at least one ic parent!
	if (!reconRes.isIc) return CRef_Undef;
	LitSet& newClause = reconRes.newClause;
	std::list<ClauseData*>& actualParentsUsed = reconRes.parentsUsed;
	Uid newUid;

	/*Optimization*/
	// - if no literals were subtracted from the clause, 
	//then there is no need to allocate space for a new clause, just 
	//use the previous clause itself
	if (ctx->getClauseLits(currUid).size() == newClause.size()) {
		newUid = currUid; 
	}
	/*Optimization*/
	//If only one parent was used, we don't 
	//need to allocate the clause, as it already exists in the DB (if ic).
	else if (actualParentsUsed.size() == 1) {
		ClauseData* singleParent = *actualParentsUsed.begin();
		assert(singleParent->clauseType == Ic);
		newUid = singleParent->clauseUid;
	}
	//otherwise (if more than one parent was used, but at least 
	//one of them isn't an original parent (a parent removed also 
	//counts as an unoriginal parent)), we need to allocate a new 
	//clause
	else {
		//Now is the point where we allocate all the nonIc parents (if any exists)
		vec<Uid> allParents,icParents, nonIcParents;
		allocateNonIcParents(reconRes, allParents, icParents, nonIcParents);

		CRef newCRef = sh->allocClause(reconRes.newClause, true, reconRes.isIc);
		assert(CRef_Undef != newCRef);
		sh->allocResol(newCRef, allParents, icParents, nonIcParents);
		newUid = sh->CRefToUid(newCRef);
		assert(CRef_Undef != newUid);
		//assert(!ctx->isClauseSeen(newUid));
		LitSet& c = ctx->getClauseLits(newUid);
		//assert(c.size() == 0);
		replaceContent(c, newClause);
	}
	return newUid;
}
void ProofRebuilder::allocateNonIcParents(ReconstructionResult& reconRes, vec<Uid>& allUids, vec<Uid>& icUids,vec<Uid>& nonIcUids) {
	assert(reconRes.isIc);
	for (auto data : reconRes.parentsUsed) {
		Uid uid = CRef_Undef;
		CRef cr = CRef_Undef;
		switch (data->clauseType) {
		case Ic:
			uid = data->clauseUid;
			assert(CRef_Undef != uid);
			icUids.push(uid);
			allUids.push(uid);
			break;
		case NonIc:
			cr = sh->allocClause(*data->clauseContent, true, false);
			assert(CRef_Undef != cr);
			sh->allocNonIcResol(cr);
			uid = sh->CRefToUid(cr);
			assert(CRef_Undef != uid);
			nonIcUids.push(uid);
			allUids.push(uid);
			break;
		case Unknown:
			throw ResolutionException("actual parent used is of type 'Unknown'");
		}
	}
}
template<class T>
Uid ProofRebuilder::proveBackboneLiteral(
	const Uid currUid,
	const T& parents,
	const Lit& BL,
	ClauseData& result
	) {
	assert(BL != ctx->dummy);

	/******************************
		Check stop conditions.
	******************************/
	//Check whether we encountered this parent before (and therefore
	//have an update for it. If an updated version exists, return 
	//it's uid.
	if (ctx->isClauseUpdated(currUid)) 
		return ctx->getClausesUpdate(currUid);
	//We shouldn't call 'proveBackboneLiteral' on a clause that
	//contains negBL (and the checks below should guarantees it).
	assert(!memberOfClause(currUid, ~BL));
	//If the clause isn't in the Rhombus of the original clause c's
	//rhombus, it shouldn't be changed at all.
	if (!sh->inRhombus(currUid)) {
		ctx->setClausesUpdate(currUid,currUid);
		recordClause(currUid);
		//now the clause will return 'true'
		//on future ctx->isClauseSeen(pUid) calls
		return currUid;
	}

	/*****************************************
		Calculate pivot literals (if needed).
	*****************************************/
	if (!ctx->arePivotsKnown(currUid)) {
		//no pivots found - extract pivots using currUid'
		//clause parents, result recorded in 'RebuilderContext* ctx'.
		recordClausePivots(currUid, parents);
	}
	assert(ctx->arePivotsKnown(currUid));
	vec<Lit>& currPivots = ctx->getPivots(currUid);
	assert(currPivots.size() == parents.size());//first pivot is always a dummy literal, which allows us to assume that the size of the parents vector is the size of the pivots vector

	//All candidates parents uids for the reconstructed parents 
	//for the current node under reconstruction. Note that some 
	//parents might not be ic, and therefore weren't allocated. In which case their
	//in which case they weren't allocated in the solver and the resolution graph, 
	//and instead their literals were stored in a ClauseData object. 
	//If the current node is found to be ic, then these parents are now parents-to-ic, 
	//and an allocation should be performed now.
	ReconstructionResult reconRes;
	std::list<ClauseData>& rebuiltParentsData = reconRes.parentsCandidates;

	/**************************************************
		BackwardsTraversal (RECURSIVE inner call here).
	***************************************************/
	backwardsTraversal(currUid, parents, BL, currPivots, rebuiltParentsData);

	/******************************
		Proof Reconstruction.
	******************************/
	reconstructClause(BL, currPivots, reconRes);

	/*********************************
		Allocate clause, if needed.
	**********************************/
	Uid newUid;
	if (reconRes.isIc) {
		newUid = allocReconstructedClause(currUid, reconRes);
		assert(ctx->isClauseSeen(newUid));
		ctx->setClausesUpdate(currUid, newUid);
		result.setIc(newUid);
	}
	else {
		newUid = CRef_Undef;
		result.setNonIc(reconRes.newClause);
	}
	
	return newUid;
}


//If uid wasn't recorded previously, Copies the literals owned by 
//'uid' to the re-builder data structure, and also records the ic 
//label of the clause
LitSet& ProofRebuilder::recordClause(Uid uid) {
	LitSet& clauseLits = ctx->getClauseLits(uid);
	if (!ctx->isClauseSeen(uid)) {
		ctx->isIc(uid) = sh->getResol(uid).header.ic;
		copyClauseLits(uid, clauseLits);
	}
	return clauseLits;
}

//Reads the literals in from to the set to. The clause will be 
//pulled from the sat solver through the use of the solver handler.
void ProofRebuilder::copyClauseLits(Uid from, LitSet& to) {
	if (CRef_Undef != sh->UidToCRef(from))
		insertAll(sh->getClause(from), to);
	else
		insertAll(sh->getDelayedRemoval(from), to);
}

template<class T>
void ProofRebuilder::recordClausePivots(Uid uid, const T& parents) {
	if (!ctx->arePivotsKnown(uid)) {
		LitSet clause;
		vec<Lit>& pivots = ctx->getPivots(uid);
		assert(pivots.size() == 0);
		pivots.push(ctx->dummy);
		for (auto p : parents) {
			Lit piv;
			piv = resolveWithOverwrite(clause, recordClause(p));
			if (piv != ctx->dummy)
				pivots.push(piv);
		}
	}
}

//resolve the current clause with the previous clause and return 
//it's clause pivot literal (with the current clauses' polarity). 
//WILL OVERWRITE the clause in 'S& set' to contain the result.
//set: 'left' parent, will contain the result.
//clause: 'right' parent, the other parent used in the resolution.
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

//Finds the relevant parent to take between the left and right parents 
//(represented by two sets of literals).
//If piv == BL or there is no actual valid pivot lit (no left parent), 
//	then represent cutting off the left parent by returning 'Right'
//If piv == ~BL or there are no literals in right parent (no right parent),
//	then represent cutting off the right parent by returning 'Left'
//If piv is in neither parent 
//	then return 'Either' (i.e. 0 in the enum).
//If piv is only in the right parent 
//	then return 'Left' (i.e. 1 in the enum).
//If piv is only in the left parent 
//	then return 'Right' (i.e. 2 in the enum). 
//If piv is in both parent 
//	then return 'Both' (i.e. 3 in the enum).
ParentUsed ProofRebuilder::findParentsUsed(const LitSet& leftLits, const LitSet& rightLits,const Lit& piv,const Lit& BL){

	if (BL == piv ||  piv == ctx->dummy )
		return Right;
	//rightLits.size() == 0 means that the right clause was cut by backwards traversal
	if (BL == ~piv || rightLits.size() == 0)
		return Left;
	bool inLeft = (leftLits.find(~piv) != leftLits.end());
	bool inRight = (rightLits.find(piv) != rightLits.end());
	return (ParentUsed)(2*(int)inLeft +  (int)inRight);
}

}
