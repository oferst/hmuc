#pragma once
#include "ProofRebuilder.h"
#include "core/SolverTypes.h"
#include "Printer.h"
#include "Graph.h"
#include <sstream>
namespace Minisat {
bool ProofRebuilder::memberOfClause(Uid u, const Lit& l) {
	if (u == CRef_Undef)
		return false;
	if (sh->UidToCRef(u) != CRef_Undef) {
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

template<class T>
bool ProofRebuilder::validateResolution(LitSet& clause, T& parents) {

	LitSet actualClause;
	ResolValidation v = ResolValidation(clause);
	for (auto& p : parents) {
		//sh->printClauseByUid(p,"parent " + std::to_string(p));
		Lit piv;
		if(ctx->isClauseSeen(p))
			piv = resolveWithOverwrite(actualClause, ctx->getClauseLits(p), v);
		else {
			LitSet parentClause;
			sh->getClauseByUid(p, parentClause);
			piv = resolveWithOverwrite(actualClause, parentClause, v);
		}
		//printf("Piv: %d\n",toDimacsLit(piv));
	}
	return (actualClause == clause && v.valid);
}

template<class T>
bool ProofRebuilder::validateResolution(Uid uid, T& parents,vec<Lit>& pivots) {

	LitSet actualClause;
	ResolValidation v = ResolValidation(ctx->getClauseLits(uid));
	bool pivotsMatch = true;
	int i = 0;
	for (auto& p : parents) {
		Lit piv;
		try {
			if (ctx->isClauseSeen(p))
				piv = resolveWithOverwrite(actualClause, ctx->getClauseLits(p), v);
			else {
				LitSet parentClause;
				sh->getClauseByUid(p, parentClause);
				piv = resolveWithOverwrite(actualClause, parentClause, v);
			}
		}
		catch (ResolutionException& e) {
			printf(e.what());
			printf("%s Uid: %d pUid: %d\n", __func__, uid, p);
			sh->printClauseByUid(uid, "clause " + std::to_string(uid));
			for (Uid p : parents) {
				sh->printClauseByUid(p, "parent " + std::to_string(p));
			}
			throw e;
		}
		pivotsMatch = pivotsMatch && (piv == pivots[i++]);
	}
	return ((pivots.size() == i) && pivotsMatch && (actualClause == ctx->getClauseLits(uid)) && v.valid);

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
int ProofRebuilder::depth_debug = 0;
void ProofRebuilder::RebuildProof(const Lit& startingConflLiteral, vec<Uid>& allPoEC, vec<Uid>& new_allPoEC, vec<Uid>& new_icPoEC) {
	ProofRebuilder::depth_debug = 0;

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
	ReconstructionResult result;
	std::list<ClauseData>& allParents = result.rebuiltParentsCandidates;
	//after analyzeFinal the vector negConflAssumptions contains all the set of negated BL that are in conflict - they are the reason for the current conflict - we will prove the  assumption (backbones) below.
	//confLits_icParents, confLits_remParents, confLits_allParents will contain all the reason clauses for the conflict - used in the resolution graph, as it is needed to allocate new resolution nodes.
	allParents.push_back(ClauseData());
	ClauseData& newParent = allParents.back();
	if (confLits_icParents.size() == 0) {
		newParent.setDeferredClauseData(negConflAssumptions);

	}
	else {
		CRef newCr = sh->allocClause(negConflAssumptions, true, true, true);
		sh->allocResol(newCr, confLits_allParents, confLits_icParents, confLits_remParents);
		Uid uid = sh->CRefToUid(newCr);
		newParent.setAllocatedClauseData(uid);
		assert(debugRebuiltClauses.insert(uid).second);
		ctx->isIc(uid) = true;
		result.isIc = true; // a parent is ic, and therefore the resulting node is also ic.
	}
	//printClause(negConflAssumptions, "negConflAssumptions");
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
	for (int i = negConflAssumptions.size()-1; i >=0; --i) {
		Lit negBL = negConflAssumptions[i];
		//the backbone literal itself, what we aim to prove, ~l.
		Lit BL = ~negBL;
		printf("CURRENT BL: %d\n", todimacsLit(BL));
		ctx->clearUpdates();
		allParents.push_back(ClauseData(BL));
		ClauseData& newUnitParent = allParents.back();
		
		/********************************************************
			proveBackboneLiteral - The main work is done here
		*********************************************************/
		proveBackboneLiteral(CRef_Undef, allPoEC, BL, newUnitParent);
		result.isIc = result.isIc || (Allocated == newUnitParent.status && sh->getResol(newUnitParent.clauseUid).header.ic);
	}


	//Iterate over reconstruction result and find if there exists an ic parent at all.
	//If there exists an ic parent, allocate remainder resolution for every non ic parent found in the reconstruction
	if (result.isIc) {
		Uid unitUid = CRef_Undef;
		CRef newCr = CRef_Undef;
		for (ClauseData& parentData : result.rebuiltParentsCandidates) {
			switch (parentData.status) {
			case Deferred:
				newCr = sh->allocClause(*(parentData.clauseContent), true, false,true);
				assert(CRef_Undef != newCr);
				sh->allocNonIcResol(newCr);
				unitUid = sh->CRefToUid(newCr);
				ctx->isIc(unitUid) = false;
				assert(CRef_Undef != unitUid);
				break;
			case Allocated:
				unitUid = parentData.clauseUid;
				assert(CRef_Undef != unitUid);
				new_icPoEC.push(unitUid);

				break;
			case Uninitialized:
				throw(ResolutionException("A clause with 'Unknown' type was build"));
			}
			new_allPoEC.push(unitUid);
		}

	}

	//assert(verifyResolutionProof(new_allPoEC));

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
							std::list<ClauseData>& rebuiltParentsData){
	/*
	Here we iterate in reverse on the parents of the current clause 
	and decide (by using the pivots that were used to create the 
	clause), which parents are going to be explored next.
	*/
	Lit negBL = ~BL;
	//A reverse iterator for the parents container 
	//(should be either a vec<Uid> or a Resol node).
	
	vec<Uid> currParents;
	for (auto& p : sh->getResol(currUid))
		currParents.push(p);
	int i = currParents.size() - 1;
	int j = currPivots.size() - 1;
	for (; j >= 0; --j, --i) {
		//current parent uid
		Uid pUid = currParents[i];
		//The current pivot literal, current parent ('pUid') is the 
		//right antecedent for the resolvent created using this pivot
		Lit currPiv = currPivots[j];
		//assert(j >= 0);//sanity check
		//assert(j > 0 || currPiv == ctx->dummy); // if j==0 then currPiv is a dummy pivot.
		//assert(j == 0 || currPiv != ctx->dummy);// if j>0 then currPiv is a real pivot.
		if (currPiv == negBL) { // cut off the 'pUid' parent by skipping current parent (it's type is Uninitialized)
			continue;
		}
		else {
			rebuiltParentsData.push_front(ClauseData(currPiv));
			ClauseData& currParent = rebuiltParentsData.front();
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
void ProofRebuilder::calculateClause(const Uid currUid, const Lit& BL,
						const vec<Lit>& currPivots,
						ReconstructionResult& reconRes) {
	LitSet& newClause = reconRes.newClause;
	assert(newClause.size() == 0);
	bool& isIc = reconRes.isIc;
	assert(!isIc);

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
	vector (we iterated in reversed order on the parents). In order 
	to now iterate on the pivots (which correspond to the 
	original parents vector) in tandem with iterating on the 
	candidate parents, we start iterating from an index 
	initiated on the difference between the size of the 
	original parents (equal to the number of pivots), and the 
	populated list of candidates parent
	*/



	for (ClauseData& parentData : reconRes.rebuiltParentsCandidates) {
		bool isAlloc = Allocated == parentData.status;
		bool isRightParentIc = isAlloc && sh->getResol(parentData.clauseUid).header.ic;
		LitSet& lits = (isAlloc ?  ctx->getClauseLits(parentData.clauseUid) : *parentData.clauseContent);
		ParentUsed pu = findParentsUsed(*currClause, lits, parentData.origPiv, BL);


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
			reconRes.parentsUsed.push_back(&(parentData));
			reconRes.isIc = isRightParentIc;
			//Set new right parent candidate in lists.
			currClause = &(lits);
			break;
		//Resolve left and right parents (left parent is the 
		//result of the previous iteration)
		case Both:
			//First, record right parent in list of candidates and 
			//track it's ic label.
			reconRes.parentsUsed.push_back(&(parentData));
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
	if (&newClause != currClause) {
		newClause.clear();
		for (auto& l : *currClause) {
			newClause.insert(l);
		}
	}
	//if (!reconRes.isIc) {
	//	printf("NONIC clause was built\n");
	//}
	
}


Uid ProofRebuilder::
			allocReconstructedICClause(const Uid& currUid, 
								ReconstructionResult& reconRes,
								const Lit& BL) {
	//Must have at least one ic parent!
	if (!reconRes.isIc) return CRef_Undef;
	LitSet& newClause = reconRes.newClause;
	std::list<ClauseData*>& actualParentsUsed = reconRes.parentsUsed;
	Uid newUid;


	/*Optimization*/
	//If only one parent was used, we don't 
	//need to allocate the clause, as it already exists in the DB (if ic).
	if (actualParentsUsed.size() == 1) {
		ClauseData* singleParent = *actualParentsUsed.begin();
		assert(singleParent->status == Allocated); //the single parent is ic, and therefore should be allocated
		newUid = singleParent->clauseUid;
		assert(CRef_Undef != newUid);
	}
	//otherwise (if more than one parent was used) we need to change the graph and\or the solver data to reflect the new construction
	else {
		//Now is the point where we allocate all the nonIc parents (if any exist)
		vec<Uid> allParents,icParents, nonIcParents;
		allocateNonIcParents(reconRes, allParents, icParents, nonIcParents);

		//if (ctx->getClauseLits(currUid).size() == newClause.size() && 
		//	member(BL,ctx->getClauseLits(currUid))){

		//	//check whether the clause wasn't changed, and if not, will only 
		//	//update the resolution graph with the new parents.
		//	//(Note: the resulting clause will always contain BL, therefore the 
		//	//only case where the clause might not have changed at all is 
		//	//when BL was already a member of the original clause).
		//	sh->realocExistingResolution(currUid, icParents,nonIcParents,allParents);
		//	newUid = currUid;
		//	assert(CRef_Undef != newUid);
		//} else {
	
		//if clause was changed we now allocate it in the solver and resolGraph
		//TODO: what if the clause already exists in the system and we only 
		//found a different proof for it? is this case possible? 
		//Will it affect the search\Rotation\BLM algorithms? 


		CRef newCRef = sh->allocClause(reconRes.newClause, true, true, true);
		sh->allocResol(newCRef, allParents, icParents, nonIcParents);

		newUid = sh->CRefToUid(newCRef);
		assert(debugRebuiltClauses.insert(newUid).second);
		assert(CRef_Undef != newUid);
		LitSet& c = ctx->getClauseLits(newUid);
		replaceContent(c, newClause);
			
		assert(validateResolution(reconRes.newClause, allParents));
		// }
	}
	ctx->isIc(newUid) = true;
	return newUid;
}
void ProofRebuilder::allocateNonIcParents(ReconstructionResult& reconRes, vec<Uid>& allUids, vec<Uid>& icUids,vec<Uid>& nonIcUids) {
	assert(reconRes.isIc);
	for (auto data : reconRes.parentsUsed) {
		Uid uid = CRef_Undef;
		CRef cr = CRef_Undef;
		switch (data->status) {
		case Allocated:
			uid = data->clauseUid;
			assert(CRef_Undef != uid);
			if(sh->getResol(uid).header.ic)
				icUids.push(uid);
			else
				nonIcUids.push(uid);
			allUids.push(uid);
			break;
		case Deferred:
			cr = sh->allocClause(*data->clauseContent, true, false,true);
			assert(CRef_Undef != cr);
			sh->allocNonIcResol(cr);
			uid = sh->CRefToUid(cr);
			assert(CRef_Undef != uid);
			nonIcUids.push(uid);
			allUids.push(uid);
			break;
		case Uninitialized:
			throw ResolutionException("actual parent used is of type 'Unknown'");
		}
	}
}


//Finding the dependencies on the pivots for each parent.
//Each parent contributes a pivot literal l (the parent was the reason that the l was assigned an l_true value in the conflict analysis, i.e., l was asserted).
//l must appear after any appearances of its negated literal.
//l must appear exactly once, and only in the parent which contributed it.
//This is the reason that
//1) once l was used in the hyper-resolution that created the Resol node (i.e. by a conflict analysis step), l or ~l cannot appear in any subsequent parents, and
//2) all parents containing ~l must appear in the hyper resolution before l.
//This allows us to map for each pivot l all the parents that contain ~l as dependent on it, with implementation via a DAG.
//Later on a topological sort can be used on the graph to find a correct ordering of parents to output a  valid hyper-resolution step.
template<class T>
void ProofRebuilder::findParentDependencies(Uid uid, const T& parents, const vec<Lit>& pivots, const LitSet& resultClause, std::unordered_map<uint32_t,vec<uint32_t>>& dependencies) {
	assert(parents.size() == pivots.size());
	int i = 0;
	std::unordered_map<Var, uint32_t> pivVar2Idx;
	std::unordered_map<Uid, uint32_t> parent2Idx;
	vec<Uid> idx2Parent;
	vec<Var> idx2PivVar;
	for (auto& p : parents) {
		idx2Parent.push(p);//idx is i
		parent2Idx[p] = i;
		Var pivVar = var(pivots[i]);
		idx2PivVar.push(pivVar);//idx is i
		pivVar2Idx[pivVar] = i;
		++i;
	}
	assert(parents.size() == idx2Parent.size());
	assert(parents.size() == idx2PivVar.size());
	assert(parents.size() == parent2Idx.size());
	assert(parents.size() == pivVar2Idx.size());
	i = 0;
	for (auto& p : parents) {
		assert(i == parent2Idx[p]);
		assert(ctx->isClauseSeen(p));
		vec<Lit> constLits;
		LitSet& currentParent = ctx->getClauseLits(p);
		for (auto& l : currentParent) {

			//if the literal appears in the target clause, it must not have been removed by resolution
			if (member(l, resultClause)) {
				assert(!member(var(l), pivVar2Idx));
				continue;
			}
			if (!member(var(l), pivVar2Idx)) {
				assert(sh->level(var(l) == 0));
				constLits.push(l);
				printf("for parent %d Lit %d is at level(var(l)): %d\n", p, todimacsLit(~l), sh->level(var(l)));
				continue;
			}
			//the index of the current pivot literal, 
			uint32_t pivIdx = pivVar2Idx[var(l)];
			if (pivIdx == i) {
				continue;
			}

			//if literal doesn't appear in the resulting clause, we check 
			//for the pivot it's dependent  upon (i.e., the pivot that 
			//removed the literal via resolution), and add the relevant 
			//parent to the dependencies list
			assert(member(var(l), pivVar2Idx));
			//the pivot index is also the index of the (single) parent containing it
			//i.e., this is a parent we are dependent on because of the literal l.
			assert(pivIdx < idx2Parent.size());
			LitSet& currPivotParent = ctx->getClauseLits(idx2Parent[pivIdx]);
			
			
			if (!member(~l, currPivotParent)) {
				assert(sh->level(var(l) == 0));
				//constLits.push(l);
				//printf("for parent %d Lit %d is at level(var(l)): %d\n", p, todimacsLit(~l), sh->level(var(l)));
				continue;
			}
			//assert(member(~l, ctx->getClauseLits(idx2Parent[pivIdx])));
			dependencies[i].push(pivIdx);//the current parent is dependent on the pivot's location
		}
		i++;

		//for (auto& l : constLits) {
		//	currentParent.erase(l);
		//}
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
	if (ctx->isClauseUpdated(currUid)) {
		result.setAllocatedClauseData(ctx->getClausesUpdate(currUid));
		assert(CRef_Undef != ctx->getClausesUpdate(currUid));
		return ctx->getClausesUpdate(currUid);
	}
	//We shouldn't call 'proveBackboneLiteral' on a clause that
	//contains negBL (and the checks below should guarantees it).

	assert(!memberOfClause(currUid, ~BL));
	//If the clause isn't in the Rhombus of the original clause c's
	//rhombus, it shouldn't be changed at all.
	if (!sh->inRhombus(currUid)) {
		assert(CRef_Undef != currUid);
		ctx->setClausesUpdate(currUid,currUid);
		LitSet& lits = recordClause(currUid);
		//now the clause will return 'true'
		//on future ctx->isClauseSeen(pUid) calls
		result.setAllocatedClauseData(currUid);
		return currUid;
	}

	/*****************************************
		Calculate pivot literals (if needed).
	*****************************************/
	
	ResolValidation validator(ctx->getClauseLits(currUid));
	if (!ctx->arePivotsKnown(currUid)) {
		//no pivots found - extract pivots using currUid'
		//clause parents, result recorded in 'RebuilderContext* ctx'.
		recordClausePivots(currUid, parents, validator);
	}



	assert(ctx->arePivotsKnown(currUid));
	vec<Lit>& currPivots = ctx->getPivots(currUid);
	//first pivot is always a dummy literal, which allows us to 
	//assume that the size of the parents vector is the size of 
	//the pivots vector.
	if (currPivots.size() != parents.size()) {
		printClause(currPivots, "pivots");

		printf("currPivots.size() %d != %d parents.size()", currPivots.size(), parents.size());
	}
	assert(currPivots.size() == parents.size());




	//due to a simplification during learning of a clause, some parents might be
	//out of order relative to the end result, we need to find a corrent ordering 
	//of parents that results in the resolutiiion result. 
	//we do that by constructing a dependency graph between parents (the analysis in 
	//the solver ensures that we can construct a DAG from the current set of parent)
	//according to pivots, and running a topological sorting on the graph.
	//the resulting ordering must be written into the resolution node before
	//continuing the proof reconstruction
	
	if (!validator.valid) {
		vec<Uid> currParents;
		for (auto& p : sh->getResol(currUid)) {
			currParents.push(p);
		}
		assert(CRef_Undef != currUid);
		std::unordered_map<uint32_t, vec<uint32_t>> dependenciesByIdx;
		findParentDependencies(currUid, currParents, currPivots, ctx->getClauseLits(currUid), dependenciesByIdx);
		Graph<uint32_t> g(currParents.size());
		for (auto& idxPair : dependenciesByIdx) {
			uint32_t idx1 = idxPair.first;
			for (auto& idx2 : idxPair.second) {
				g.addEdge(idx1, idx2);
			}
		}
		vec<uint32_t> sortedParentsIdx;
		g.topologicalSort(sortedParentsIdx);
		

		vec<Uid> updatedParents;
		vec<Lit> updatePivots;
		for (uint32_t idx : sortedParentsIdx) {
			updatedParents.push(currParents[idx]);
			updatePivots.push(currPivots[idx]);
		}
		replaceVecContent(currPivots, updatePivots);
		assert(validateResolution(currUid, updatedParents, currPivots));

		vec<Uid> icParents;
		vec<Uid> remParent;
		vec<Uid>& allParents = updatedParents;
		for (auto& p : allParents) {
			assert(ctx->isClauseSeen(p));
			if (ctx->isIc(p)) {
				icParents.push(p);
			}
			else {
				remParent.push(p);
			}
		}
		sh->updateParentsOrder(currUid, icParents, remParent, allParents);
		assert(validateResolution(currUid,updatedParents, updatePivots));
	}


	//A container used for book-keeping, will contain the result of reconstruction.
	//After calling 'backwardsTraversal' with it, it will contain the parents candidates 
	//for reconstruction)
	//After calling 'reonstructClasue' with it, it will contain both the actual parents
	//that were used in reconstruction (out of the candidates), as well as the set '
	//of literals that were the result of resolving said parents.
	//This information will be used after that in the allocation of the newly 
	//reconstructed clause (if needed), in the function 'allocReconstructedICClause'.
	ReconstructionResult reconRes;

	//All candidates parents uids for the reconstructed parents 
	//for the current node under reconstruction. Note that some 
	std::list<ClauseData>& rebuiltParentsCandidates = reconRes.rebuiltParentsCandidates;

	
	/**************************************************
		BackwardsTraversal (RECURSIVE inner call here).
	***************************************************/
	backwardsTraversal(currUid, parents, BL, currPivots, rebuiltParentsCandidates);
	
	/******************************
		Proof Reconstruction.
	******************************/

	calculateClause(currUid,BL, currPivots, reconRes);

	/*********************************
		Allocate clause, if needed.
	**********************************/
	Uid newUid;
	if (reconRes.isIc) {
		if (reconRes.parentsUsed.size() > 1)
			newUid = allocReconstructedICClause(currUid, reconRes, BL);
		else
			newUid = (*reconRes.parentsUsed.begin())->clauseUid;
		assert(ctx->isClauseSeen(newUid));
		ctx->setClausesUpdate(currUid, newUid);
		result.setAllocatedClauseData(newUid);
		assert(ctx->getClauseLits(newUid).find(BL) != ctx->getClauseLits(newUid).end());
	}
	else {
		newUid = CRef_Undef;
		result.setDeferredClauseData(reconRes.newClause);
		assert(result.clauseContent->find(BL) != result.clauseContent->end());
	}
	
	return newUid;
}


//If uid wasn't recorded previously, Copies the literals owned by 
//'uid' to the re-builder data structure, and also records the ic 
//label of the clause
LitSet& ProofRebuilder::recordClause(Uid uid) {

	if (ctx->isClauseSeen(uid)) {
		return ctx->getClauseLits(uid);
	}
	LitSet& clauseLits = ctx->getClauseLits(uid) = LitSet();

	ctx->isIc(uid) = sh->getResol(uid).header.ic;
	copyClauseLits(uid, clauseLits);

	return clauseLits;
}

//Reads the literals in from to the set to. The clause will be 
//pulled from the sat solver through the use of the solver handler.
void ProofRebuilder::copyClauseLits(Uid from, LitSet& to) {
	if(sh->hasDelayedRemoval(from))
		insertAll(sh->getDelayedRemoval(from), to);
	else 
		insertAll(sh->getClause(from), to);
}

template<class T>
void ProofRebuilder::recordClausePivots(Uid uid, const T& parents, ResolValidation& validation) {
	if (!ctx->arePivotsKnown(uid)) {
		LitSet clause;
		vec<Lit>& pivots = ctx->getPivots(uid) = vec<Lit>();
		pivots.push(ctx->dummy);
		std::unordered_map<Var, uint32_t> piv2Idx;
		int i = 0;
		for (auto& p : sh->getResol(uid)) {
			LitSet& rightClause = recordClause(p);
			try {
				Lit piv = resolveWithOverwrite(clause, rightClause, validation);
				if (piv != ctx->dummy) {
					pivots.push(piv);
					validation.pivotVars.insert(var(piv));
				}
			}
			catch (ResolutionException& e) {
				printf(e.what());
				printf("%s Uid: %d pUid: %d\n", __func__, uid, p);
				sh->printClauseByUid(uid, "clause " + std::to_string(uid));
				for (Uid p : parents) {
					sh->printClauseByUid(p, "parent " + std::to_string(p));
				}
				throw e;
			}
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
template<class T, class S>
Lit ProofRebuilder::resolveWithOverwrite(T& leftLits, S& rightLits, ResolValidation& validation) {
	Lit piv = ctx->dummy;
	int initialSize = leftLits.size();
	for (auto& l : rightLits) {
		if (leftLits.find(~l) == leftLits.end()) {
			leftLits.insert(l);
		}
		else {
			leftLits.erase(~l);
			if (piv != ctx->dummy) {
				printf("should be dummy pivot\n");
				throw ResolutionException("First pivot assign should be to a dummy lit"); //should only be assigned once.
			}
			piv = l;
		}


		if (validation.valid) {
			if (!member(l, validation.targetClause) ){
				//if (sh->level(var(l)) == 0) {
				//	leftLits.erase(l);
				//}
				//else 
					if(member(var(l), validation.pivotVars)) {
					validation.valid = false;
				}
			}
		}
	}
	if (initialSize > 0 && piv == ctx->dummy) {
		ostringstream oss;
		printClause(leftLits, "leftLits", oss);
		oss << std::endl;
		printClause(rightLits, "rightLits", oss);
		throw ResolutionException(("Pivot assigned cannot be a dummy literal.\n" + oss.str()).c_str());
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
	bool c = BL == piv;
	bool d = piv == ctx->dummy;
	if (BL == piv ||  piv == ctx->dummy)
		return Right;

	bool a = BL == ~piv;
	bool b = rightLits.size() == 0;
	if (BL == ~piv || rightLits.size() == 0)
		return Left;
	bool inLeft = (leftLits.find(~piv) != leftLits.end());
	bool inRight = (rightLits.find(piv) != rightLits.end());
	return (ParentUsed)(2*(int)inLeft +  (int)inRight);
}


bool ProofRebuilder::verifyResolutionProof(const vec<Uid>& PoEC) {
	//DEBUG from here 
	//sanity check: the resulting resolution graph is independent of the clause removed (c).
	//sanity check: validate all resolution steps in the resulting graph.
	Set<Uid> seen;
	vec<Uid> newIcCore;
	vec<Uid> clausesToCheck;
	printf("\n\nVALIDATION START\n");
	verbose = 1;
	printf("validating %d clauses\n", debugRebuiltClauses.size());
	Set<Uid> oldClauses, newClauses;
	int nValidated = 0;
	for (auto& p : PoEC) {
		sh->printClauseByUid(p, "new PoEC " + std::to_string(p) + " ic: " + std::to_string(ctx->isIc(p)));
		assert(!sh->inRhombus(p));//a clause not in the original rhombus (it is independent of the clause to remove c).
		assert(!seen.has(p));//all the PoEC were built during this call,  and they should be independent of each other.
		assert(!oldClauses.has(p));
		clausesToCheck.push(p);
		while (clausesToCheck.size() > 0) {
			Uid uid = clausesToCheck.last();
			clausesToCheck.pop();

			if (seen.insert(uid)) {
				assert(!sh->inRhombus(uid));
				

				Resol& resol = sh->getResol(uid);
				if (debugRebuiltClauses.find(uid) != debugRebuiltClauses.end()) {

					if (resol.size() == 0) {
						printf("no parents for %d\n", uid);
						continue;
					}
					LitSet clause;
					sh->getClauseByUid(uid, clause);
					//printClause(clause, "+++curr uid: " + std::to_string(uid)+ "+++");
					//bool v = ;
					assert(validateResolution(clause, resol));
					nValidated++;
					printf("%d V\n", uid);
				}

				assert(resol.header.ic);
				int icParentSize = resol.icParentsSize();
				if (icParentSize == 0) {
					assert(!sh->inRhombus(uid));
					newIcCore.push(uid);
				}
				else {
					Uid* icParents = resol.IcParents();
					for (int i = 0; i < icParentSize; ++i) {
						clausesToCheck.push(icParents[i]);
					}
				}
			}
		}
	}
	std::unordered_set<Uid> newIcParentsSet;
	for (auto& uid : newIcCore)
		newIcParentsSet.insert(uid);
	printf("validation - new ic core size %d\n", newIcParentsSet.size());
	printf("validation - new rhombus size %d\n", seen.elems());
	verbose = 0;
	printf("nValidated: %d\n", nValidated);
	printf("\nVALIDATION END\n\n");
	return true;
}


}
