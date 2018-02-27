#pragma once
#include "ProofRebuilder.h"
#include "core/SolverTypes.h"
#include "Printer.h"
#include "Graph.h"
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
bool ProofRebuilder::validateResolution(Uid uid, vec<Uid>& parents,vec<Lit>& pivots) {

	LitSet actualClause;
	ResolValidation v = ResolValidation(ctx->getClauseLits(uid));
	bool pivotsMatch = true;
	int i = 0;
	for (auto& p : parents) {
		Lit piv = resolveWithOverwrite(actualClause, ctx->getClauseLits(p), v);
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
void ProofRebuilder::RebuildProof(const Lit& startingConflLiteral, vec<Uid>& allPoEC, vec<Uid>& new_allPoEC, vec<Uid>& new_icPoEC) {
	printf("REBUILDING PROOF\n");
	//ctx->getPivots(CRef_Undef).clear();
	//vec<Lit>& initPivots = ctx->getPivots(CRef_Undef) = vec<Lit>();
	//initPivots.push(ctx->dummy);
	//for (auto piv : sh->getPoEC_Piv()) {
	//	initPivots.push(piv);
	//}
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
	ClauseData& newParent = allParents.front();
	printf("negConflAssumptions is ic: %d\n", confLits_icParents.size() > 0);
	if (confLits_icParents.size() == 0) {
		newParent.setNonIc(negConflAssumptions);
	}
	else {
		CRef newCr = sh->allocClause(negConflAssumptions, true, confLits_icParents.size() > 0);
		sh->allocResol(newCr, confLits_allParents, confLits_icParents, confLits_remParents);
		Uid uid = sh->CRefToUid(newCr);
		newParent.setAllocatedClauseData(uid);
		ctx->isIc(uid) = true;
		result.isIc = true; // a parent is ic, and therefore the resulting node is also ic.
	}
	printClause(negConflAssumptions, "negConflAssumptions");

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
	//for (Lit negBL : negConflAssumptions) {
		//the backbone literal itself, what we aim to prove, ~l.
		Lit BL = ~negBL;
		ctx->clearUpdates();
		allParents.push_front(ClauseData(BL));
		ClauseData& newUnitParent = allParents.front();
		
		/******************************************************
			proveBackboneLiteral - The main work is done here
		*******************************************************/
		proveBackboneLiteral(CRef_Undef, allPoEC, BL, newUnitParent);
		result.isIc = result.isIc || Allocated == newUnitParent.status;
		if (newUnitParent.status == Allocated)
			sh->printClauseByUid(newUnitParent.clauseUid, "------newParent Allocated");
		else if (newUnitParent.status == Deferred)
			printClause(*newUnitParent.clauseContent, "-------newParent Deferred");
		else
			printf("error parent uninitialized");
	}


	//Iterate over reconstruction result and find if there exists an ic parent at all.
	//If there exists an ic parent, allocate remainder resolution for every non ic parent found in the reconstruction
	if (result.isIc) {
		Uid unitUid = CRef_Undef;
		CRef newCr = CRef_Undef;
		for (ClauseData& parentData : result.parentsCandidates) {
			switch (parentData.status) {
			case Deferred:
				newCr = sh->allocClause(*(parentData.clauseContent), true, false);
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
	for (auto& p : new_allPoEC) {
		sh->printClauseByUid(p, "new PoEC " + std::to_string(p) + " ic: " + std::to_string(ctx->isIc(p)));
	}
	for (auto& p : new_icPoEC) {
		sh->printClauseByUid(p, "new icPoEC " + std::to_string(p));
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
							std::list<ClauseData>& rebuiltParentsData){
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
		if (currPiv == negBL) { // cut off the 'pUid' parent by skipping current parent (it's type is Uninitialized)
			continue;
		}
		else {
			rebuiltParentsData.push_front(ClauseData(currPiv));
			ClauseData& currParent = rebuiltParentsData.front();
			proveBackboneLiteral(pUid, sh->getResol(pUid), BL, currParent);
			if (currUid == 5016 && toDimacsLit(BL) == 1021)
				verbose = 1;
			else
				verbose = 0;
		}
		if (currPiv == BL) {
			if (verbose) printf("cutoff point here (uid: %d)\n",currUid);
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
void ProofRebuilder::reconstructClause(const Uid currUid, const Lit& BL,
						const vec<Lit>& currPivots,
						ReconstructionResult& reconRes) {
	LitSet& newClause = reconRes.newClause;
	assert(newClause.size() == 0);
	bool& isIc = reconRes.isIc;
	//if (currUid == 5335) {
	//	printClause(currPivots, "actual pivots");
	//}
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
	//int j = currPivots.size() - (reconRes.parentsCandidates.size());
	//assert(j >= 0 && j < currPivots.size() - 1);
	//-1 because we must have at least one candidate parent
	//auto parentIter = reconRes.parentsCandidates.begin();

	for (ClauseData& parentData : reconRes.parentsCandidates) {
		
		bool isRightParentIc = (Allocated == parentData.status && ctx->isIc(parentData.clauseUid));
		LitSet& lits = (isRightParentIc ?  ctx->getClauseLits(parentData.clauseUid) : *parentData.clauseContent);

		assert(!isRightParentIc || ctx->isIc(parentData.clauseUid));
		
		
		ParentUsed pu = findParentsUsed(*currClause, lits, parentData.origPiv, BL);
		if (1 == verbose) {
			printf("\n\n**********\n");
			printClause(vec<Lit>({ parentData.origPiv }), "piv");
			printClause(*currClause, "left parent");
			printClause(lits, "right parent is ic: " + std::to_string(isRightParentIc));
		}

		switch (pu) {

		//Skip the right parent, only considers the left parent.
		//Note that the left parent always a right parent in the 
		//previous iteration (except for the dummy parent in the 
		//beginning), which means that we don't need to do anything 
		//to record it, as if it was a useful parent, then it was 
		//added previously.
		case Left:
			if (1 == verbose) printf("left parent used\n");
			break;
		//Heuristically check which clause is bigger. if the 
		//left parent is smaller, choose the left parent by 
		//skipping the right parent, otherwise, we choose the 
		//right parent by  doing the 'Right' case below.
		case Either:

			if ((*currClause).size() <= lits.size()) //Heuristic choice
				if (1 == verbose) printf("left parent used\n");
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
			if (1 == verbose) printf("right parent used\n");
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
			if (1 == verbose) printf("both parents used\n");

		}
		if (1 == verbose) {
			printClause(*currClause, "result");
			//printf("**********\n");
		}
	}
	if (1 == verbose) {
		printf("\n\n\n********************\n");
		for (auto& pPtr : reconRes.parentsUsed) {
			if (pPtr->status == Allocated)
				sh->printClauseByUid(pPtr->clauseUid, "parent is ic: " + std::to_string(pPtr->status == Allocated));
			else if (pPtr->status == Deferred)
				printClause(*pPtr->clauseContent, "parent is ic: " + std::to_string(pPtr->status == Allocated));
			else {
				printf("ERROR!"); exit(-1);
			}
		}
		printClause(reconRes.newClause, "\n\nRESULT");
		printf("********************\n");
	}
	
}


Uid ProofRebuilder::
			allocReconstructedClause(const Uid& currUid, 
								ReconstructionResult& reconRes,
								const Lit& BL) {
	//Must have at least one ic parent!
	if (!reconRes.isIc) return CRef_Undef;
	LitSet& newClause = reconRes.newClause;
	std::list<ClauseData*>& actualParentsUsed = reconRes.parentsUsed;
	Uid newUid;

	/*Optimization*/
	// - if no literals were subtracted from the clause, 
	//then there is no need to allocate space for a new clause, just 
	//use the previous clause itself
	if (ctx->getClauseLits(currUid).size() == newClause.size() && ctx->getClauseLits(currUid).find(BL) != ctx->getClauseLits(currUid).end()) {

		newUid = currUid;
		assert(CRef_Undef != newUid);
	}
	/*Optimization*/
	//If only one parent was used, we don't 
	//need to allocate the clause, as it already exists in the DB (if ic).
	else if (actualParentsUsed.size() == 1) {
		ClauseData* singleParent = *actualParentsUsed.begin();
		assert(singleParent->status == Allocated);
		newUid = singleParent->clauseUid;
		assert(CRef_Undef != newUid);
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
			icUids.push(uid);
			allUids.push(uid);
			break;
		case Deferred:
			cr = sh->allocClause(*data->clauseContent, true, false);
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

template<class T>
void ProofRebuilder::findParentDependencies(const T& parents, const vec<Lit>& pivots, const LitSet& resultClause, std::unordered_map<uint32_t,vec<uint32_t>>& dependencies) {
	int i = 0;
	assert(parents.size() == pivots.size());
	std::unordered_map<Var, uint32_t> pivVar2Idx;
	std::unordered_map<Uid, uint32_t> parent2Idx;
	vec<Uid> idx2Parent;
	vec<Var> idx2PivVar;
	printf("<FIND PARNET DEPENDENCIES>\n");
	printClause(resultClause, "wantedResult");
	for (auto& p : parents) {
		//printf("<parent pre iteration = %d>\n", p);
		//printf("pivots[%d] : %d\n", i,todimacsLit(pivots[i]));
		//printf("var(pivots[%d]) : %d\n", i, var(pivots[i]));
		//printf("parent idx : %d\n", i);
		idx2Parent.push(p);
		//printf("idx2Parent[%d] : %d\n", i, idx2Parent[i]);
		parent2Idx[p ] = i;
		//printf("parent2Idx[%d] : %d\n", p, parent2Idx[p]);
		Var pivVar = var(pivots[i]);
		idx2PivVar.push(pivVar);
		//printf("idx2PivVar[%d] : %d\n", i, idx2PivVar[i]);
		pivVar2Idx[pivVar] = i;
		//printf("pivVar2Idx[var(pivots[%d])] : %d\n", i, pivVar2Idx[var(pivots[i])]);
		//sh->printClauseByUid(p, "\tparnet ");
		++i;
		//printf("<\\parent pre iteration= %d>\n", p);
	}
	assert(parents.size() == idx2Parent.size());
	assert(parents.size() == idx2PivVar.size());
	assert(parents.size() == parent2Idx.size());
	assert(parents.size() == pivVar2Idx.size());
	i = 0;
	for (auto& p : parents) {
		printf("<parent NEXT iteration = %d>\n", p);
		sh->printClauseByUid(p, "parnet p " +std::to_string(p));
		assert(i == parent2Idx[p]);
		assert(ctx->isClauseSeen(p));
		//printClause(ctx->getClauseLits(p), "ctx->getClauseLits(p)");
		for (auto& l : ctx->getClauseLits(p)) {

			//printf("curr lit %d\n", todimacsLit(l));
			int literal = todimacsLit(l);


			//if (-1026 == literal) continue;

			assert(var(l) == var(~l));
			if (member(l, resultClause)) {
				assert(!member(var(l), pivVar2Idx));
				continue;
			}
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
			//printf("pivVar2Idx[var(%d)] = %d\n", todimacsLit(l), pivVar2Idx[var(l)]);
			//printf("pivIdx = %d (sould be equal to pivVar2Idx[var(%d)]) \n", pivIdx, todimacsLit(l));
			//printf("idx2Parent[%d] = %d\n", pivIdx, idx2Parent[pivIdx]);
			//printClause(ctx->getClauseLits(idx2Parent[pivIdx]), "ctx->getClauseLits(idx2Parent[pivIdx])");
			assert(pivIdx < idx2Parent.size());
			assert(member(~l, ctx->getClauseLits(idx2Parent[pivIdx])));
			dependencies[i].push(pivIdx);//the current parent is dependent on the pivot's location
			printf("for lit %d added dependency (%d,%d)\n", todimacsLit(l), i, pivIdx);
		}
		i++;
		printf("<\\nparent NEXT iteration = %d>\n", p);
	}
	printf("<\\FIND PARNET DEPENDENCIES>\n");
}


template<class T>
Uid ProofRebuilder::proveBackboneLiteral(
	const Uid currUid,
	const T& parents,
	const Lit& BL,
	ClauseData& result
	) {
	if (currUid == 5016 && toDimacsLit(BL) == 1021)
		verbose = 1;
	else 
		verbose = 0;
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
	//printf("\n");
	//printClause(vec<Lit>({ ~BL }),"neg backbone");
	//sh->printClauseByUid(currUid, "current clause");
	//printf("\n");
	assert(!memberOfClause(currUid, ~BL));
	//If the clause isn't in the Rhombus of the original clause c's
	//rhombus, it shouldn't be changed at all.
	if (!sh->inRhombus(currUid)) {
		assert(CRef_Undef != currUid);
		ctx->setClausesUpdate(currUid,currUid);
		recordClause(currUid);
		//now the clause will return 'true'
		//on future ctx->isClauseSeen(pUid) calls
		result.setAllocatedClauseData(currUid);
		return currUid;
	}

	/*****************************************
		Calculate pivot literals (if needed).
	*****************************************/
	
	ResolValidation validation(ctx->getClauseLits(currUid));
	if (!ctx->arePivotsKnown(currUid)) {
		//no pivots found - extract pivots using currUid'
		//clause parents, result recorded in 'RebuilderContext* ctx'.
		recordClausePivots(currUid, parents, validation);
	}



	assert(ctx->arePivotsKnown(currUid));
	vec<Lit>& currPivots = ctx->getPivots(currUid);

	assert(currPivots.size() == parents.size());//first pivot is always a dummy literal, which allows us to assume that the size of the parents vector is the size of the pivots vector
	//All candidates parents uids for the reconstructed parents 
	//for the current node under reconstruction. Note that some 



	//due to a simplification during learning of a clause, some parents might be
	//out of order relative to the end result, we need to find a corrent ordering 
	//of parents that results in the resolutiiion result. 
	//we do that by constructing a dependency graph between parents (the analysis in 
	//the solver ensures that we can construct a DAG from the current set of parent)
	//according to pivots, and running a topological sorting on the graph.
	//the resulting ordering must be written into the resolution node before
	//continuing the proof reconstruction
	//if (currUid == 5016) {
	//}
	if (!validation.valid) {
		assert(CRef_Undef != currUid);
		std::unordered_map<uint32_t, vec<uint32_t>> dependencies;
		findParentDependencies(parents, currPivots, ctx->getClauseLits(currUid), dependencies);
		Graph<uint32_t> g(parents.size());
		for (auto& pair : dependencies) {
			uint32_t idx1 = pair.first;
			for (auto& idx2 : pair.second) {
				g.addEdge(idx1, idx2);
			}
		}
		vec<uint32_t> sortedParentsIdx;
		g.topologicalSort(sortedParentsIdx);
		

		//if (currUid == 5016) {
		//	vec<Uid> parentsVec;
		//	for (auto& p : parents) {
		//		parentsVec.push(p);
		//	}
		//	printf("++++++++TOPOLOGICAL+++++++++++++\n");
		//	for (auto& idx : sortedParentsIdx) {
		//		sh->printClauseByUid(parentsVec[idx], "parnet " + std::to_string(parentsVec[idx]));
		//	}
		//}


		vec<Uid> parentsVec;
		for (auto& p : parents) {
			parentsVec.push(p);
		}
		vec<Uid> updatedParents;
		vec<Lit> updatePivots;
		for (uint32_t idx : sortedParentsIdx) {
			updatedParents.push(parentsVec[idx]);
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
		
		
		sh->updateExistingResolution(currUid, icParents, remParent, allParents);
		assert(validateResolution(currUid,updatedParents, updatePivots));

		if (currUid == 5016) {
			printf("++++++++TOPOLOGICAL+++++++++++++\n");
			for (auto& p : parents) {
				sh->printClauseByUid(p, "parnet " + std::to_string(p));
			}
		}




		//& currResol = sh->getResol(currUid);


		//updateResolutionParent(currUid, sortedParentsIdx);
	}


	//parents might not be ic, and therefore weren't allocated. In which case their
	//in which case they weren't allocated in the solver and the resolution graph, 
	//and instead their literals were stored in a ClauseData object. 
	//If the current node is found to be ic, then these parents are now parents-to-ic, 
	//and an allocation should be performed now.
	ReconstructionResult reconRes;
	std::list<ClauseData>& rebuiltParentsData = reconRes.parentsCandidates;
	if (1 == verbose) {
		printf("\n\n----------\n");
		sh->printClauseByUid(currUid, "original clause "+ std::to_string(currUid));
		printClause(vec<Lit>({ BL }), "BL");
		printClause(currPivots, "pivots");
			for (auto& p : parents){
				if (p == 2380){
					assert(ctx->isClauseSeen(p));
					printClause(ctx->getClauseLits(p), "clause 2380 from ctx");
				}
	/*					return ctx->getClauseLits(uid);
					}*/

				sh->printClauseByUid(p, "parent "+ std::to_string(p)+" in rhombus: " + std::to_string(sh->inRhombus(p)));
			}
	}
	/**************************************************
		BackwardsTraversal (RECURSIVE inner call here).
	***************************************************/
	backwardsTraversal(currUid, parents, BL, currPivots, rebuiltParentsData);
	if (currUid == 5016 && toDimacsLit(BL) == 1021)
		verbose = 1;
	else
		verbose = 0;
	/******************************
		Proof Reconstruction.
	******************************/
	//printf("RECONSTRUCT %d\n", currUid);
	reconstructClause(currUid,BL, currPivots, reconRes);

	/*********************************
		Allocate clause, if needed.
	**********************************/
	Uid newUid;
	if (reconRes.isIc) {
		newUid = allocReconstructedClause(currUid, reconRes, BL);
		assert(ctx->isClauseSeen(newUid));
		ctx->setClausesUpdate(currUid, newUid);
		result.setAllocatedClauseData(newUid);
		if (verbose && ctx->getClauseLits(newUid).find(BL) == ctx->getClauseLits(newUid).end()) {
			printClause(ctx->getClauseLits(newUid), "result clause in ctx");
		 }
		assert(ctx->getClauseLits(newUid).find(BL) != ctx->getClauseLits(newUid).end());
		//assert(ctx->getClauseLits(newUid).find(BL) != ctx->getClauseLits(newUid).end());
	}
	else {
		newUid = CRef_Undef;
		result.setNonIc(reconRes.newClause);
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
	//printClause(clauseLits, "parent " + std::to_string(uid)+ " lits");

	ctx->isIc(uid) = sh->getResol(uid).header.ic;
	copyClauseLits(uid, clauseLits);
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
void ProofRebuilder::recordClausePivots(Uid uid, const T& parents, ResolValidation& validation) {
	if (!ctx->arePivotsKnown(uid)) {
		//if(uid==5016) sh->printClauseByUid(uid, "CALC PIVOTS HERE");
		LitSet clause;
		//LitSet tempClause;
		vec<Lit>& pivots = ctx->getPivots(uid) = vec<Lit>();
		assert(pivots.size() == 0);
		pivots.push(ctx->dummy);


		std::unordered_map<Var, uint32_t> piv2Idx;

		for (auto& p : parents) {
			LitSet& rightClause = recordClause(p);
			Lit piv = resolveWithOverwrite(clause, rightClause,validation);
			if (piv != ctx->dummy) {
				pivots.push(piv);
				validation.pivotVars.insert(var(piv));
			}
		}

		//UidToUid parentDependencies;
		//LitSet originalClause; copyClauseLits(uid, originalClause);
		////if(uid == 5016) printClause(originalClause, "original clause");

		//std::unordered_map<Uid, uint32_t> parent2Idx;
		//vec<Uid> idx2Parent;
		//struct Node {
		//	uint32_t data;
		//	Lit piv;
		//	Node *prev, *next;
		//	Node(uint32_t _data=CRef_Undef, Lit _piv = mkLit(Var(var_Undef)), Node* _prev = NULL, Node* _next = NULL) :data(_data), prev(_prev), next(_next) {}
		//};
		//vec<Node*> idx2ParentNode;
		//for (auto& p : parents) {
		//	//here we do the resolution step, along with a validation step: 
		//	//For each literal l that appears in the rightLiterals set, 
		//	//if it was already removed by a use of a pivot l or ~l, 
		//	//BUT it doesn't appear in the clause calculated by the solver,
		//	//we conclude that the current parent was added by a simplification 
		//	//step in the solver (in which we add parents allow us to drop 
		//	//literals that are already proved by other literals in the clause -
		//	//for details see "https://ie.technion.ac.il/~ofers/sat_smt/1_ofer_contrasat.pptx")
		//	//In this case the current parent's place in the parents ordering 
		//	//is incorrect, and we need to locate the place to move the current parent - 
		//	//the slot right before the pivot for l is the safest place. Note that 
		//	//this might happen to several literals l in this parent, in which case 
		//	//we will place the parent in the smallest slot found

		//	LitSet& rightLits = rightClause;
		//	//if (uid == 5016) {
		//	//	printClause(rightClause, "rightClause " + std::to_string(p));
		//	//	sh->printClauseByUid(p, "parent " + std::to_string(p));
		//	//}
		//	//will hold the first parent that the current parent p is dependent on (with the minimal idx)
		//	uint32_t parentDependencyIdx = UINT32_MAX;
		//	for (const Lit& l : rightLits) {
		//	//	if the current literal was removed via resolution (i.e. it was a pivot before), and it isn't a member of the resulting clause, then the current parent isn't placed correctly and it's place is at least before the place where the pivot appears in
		//		if((!member(l,originalClause)) && (member(var(l),piv2Idx))) {
		//			//if (uid == 5016) {

		//			//	printClause(vec<Lit>({ l }), "PROBLEM LIT ");
		//			//	printf("!member(l,originalClause) %d\n", !member(l, originalClause));
		//			//	printf("member(var(l),piv2Idx) %d\n", member(var(l), piv2Idx));
		//			//}
		//			parentDependencyIdx = minimum(parentDependencyIdx, piv2Idx[var(l)]);
		//			//if (uid == 5016) {
		//			//	printf("parentDependencyIdx %d\n", parentDependencyIdx);
		//			//}
		//		}
		//	}
		//	piv2Idx[var(piv)] = pivots.size()-1;
		//	parent2Idx[p] = pivots.size()-1;
		//	//if (uid == 5016) {
		//	//	sh->printClauseByUid(p,"$$$p "+std::to_string(p));
		//	//	printf("$$$parent2Idx[p] %d\n", parent2Idx[p]);

		//	//}
		//	idx2Parent.push(p);
		//	idx2ParentNode.push(new Node(p,piv));

		//	if (parentDependencyIdx != UINT32_MAX) {
		//		assert(parentDependencyIdx > 0);
		//		parentDependencies[p] = idx2Parent[parentDependencyIdx];
		//	}
		//}
		//if (uid == 5016) {
		//	printf("\nparent dependencies\n");
		//	for (auto& pair : parentDependencies) {
		//		sh->printClauseByUid(pair.first, "first");
		//		sh->printClauseByUid(pair.second, "second");
		//		printf("\n");
		//	}
		//	printf("\\parent dependencies\n");
		//}
		//assert(parent2Idx.size() == parents.size());
		//assert(idx2Parent.size() == parents.size());
		//assert(idx2ParentNode.size() == parents.size());
		//assert(pivots.size() == parents.size());
		//assert(pivots.size() >= parentDependencies.size());
		//for (int i = 1; i < idx2ParentNode.size(); ++i) {
		//	idx2ParentNode[i]->prev = idx2ParentNode[i - 1];
		//	idx2ParentNode[i - 1]->next = idx2ParentNode[i];
		//}

		//if (uid == 5016) printf("\n\n******************************************\n");
		//if (uid == 5016) printf("num dependencies %d\n", parentDependencies.size());

		//for(auto& pair : parentDependencies){



		//	Node* first = idx2ParentNode[parent2Idx[pair.first]];
		//	if(uid == 5016) sh->printClauseByUid(first->data, "first");

		//	Node* second = idx2ParentNode[parent2Idx[pair.second]];
		//	if (uid == 5016) sh->printClauseByUid(second->data, "second");

		//	Node* predecessor = second->prev;
		//	first->next = second;
		//	second->prev = first;
		//	first->prev = predecessor;
		//	if (NULL != predecessor)
		//		predecessor->next = first;

		//}
		//vec<Uid> correctedParents;
		//vec<Lit> correctedPivots;
		//Node* curr = idx2ParentNode[0];

		//std::unordered_set<Uid> seenParents;
		//for (int i = 0; i < idx2ParentNode.size(); ++i) {
		//}
		//if (uid == 5016) printf("******************************************\n\n");

		//////while (NULL != curr) {
		//if (uid == 5016) sh->printClauseByUid(curr->data, "parent");

		////	correctedParents.push(curr->data);
		////	assert(seenParents.find(curr->data) == seenParents.end());
		////	seenParents.insert(curr->data);
		////	curr = curr->next;
		////}

		//for (Node* n : idx2ParentNode)
		//	delete n;


		//assert(correctedParents.size() == parents.size());
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

		if (validation.valid) {
			if (!member(l, validation.targetClause) && member(var(l), validation.pivotVars)) {
				validation.valid = false;
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

	if (BL == piv ||  piv == ctx->dummy)
		return Right;
	//rightLits.size() == 0 means that the right clause was cut by backwards traversal
	if (BL == ~piv || rightLits.size() == 0)
		return Left;
	bool inLeft = (leftLits.find(~piv) != leftLits.end());
	bool inRight = (rightLits.find(piv) != rightLits.end());
	return (ParentUsed)(2*(int)inLeft +  (int)inRight);
}

}
