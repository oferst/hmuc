#include "core/MinimalCore.h"
#include "utils/ParseUtils.h"
#include "mtl/Sort.h"
#include "utils/System.h"
#include "mtl/Heap.h"
#include <stdio.h>
#include <assert.h>

#include<vector>



namespace Minisat {
	static const char* _cat = "MUC";
	static BoolOption    opt_muc_print(_cat, "muc-progress", "print progress lines", false);
	static BoolOption    opt_muc_rotate(_cat, "muc-rotate", "perform rotation algorithm", true);
	static BoolOption    opt_print_sol(_cat, "muc-print-sol", "print the satisfying solution", false);
	static DoubleOption  opt_set_ratio(_cat, "set-ratio", "When we should start using set", 0.0, DoubleRange(0.0, true, 1000000.0, true));
	static BoolOption    opt_second_sat_call(_cat, "sec-sat-call", "call solver again to get a different SAT assignment", false);
	static BoolOption    opt_sec_rot_use_prev(_cat, "sec-call-use-prev", "include in second rotation-call previously discovered clauses", true);
	static IntOption     opt_remove_order(_cat, "remove-order", "removal order: 0 - biggest, 1 - smallest, 2 - highest, 3 - lowest, 4 - rotation\n", 4, IntRange(0, 4));
	static BoolOption    opt_only_cone(_cat, "only-cone", "remove all the clauses outside the empty clause cone\n", true);
	static IntOption     max_Iter(_cat, "max-iter", "allow for a maximum number of iteration before cutting of the search\n", -1, IntRange(-1, 2147483647));


	CMinimalCore::CMinimalCore(SimpSolver& solver) :
		m_bIcInConfl(false)
		, m_Solver(solver)
		, m_nICSize(0)
		, m_nRotationCalled(0)
		, m_nRotationFirstCalls(0)
		, m_nRotationClausesAdded(0)
		, m_nSecondRotationClausesAdded(0)
		, m_ClauseHeap(ClauseOrder(m_Solver, opt_remove_order))
	{}

	void CMinimalCore::SetICNum(uint32_t nIcNum)
	{
		m_nICSize = nIcNum;
	}

	void CMinimalCore::PrintData(int unknownSize, int mucSize, int iter, std::string msg, bool last)
	{
		if (opt_muc_print)
		{
			printf("c %siter %d time %g not-muc %d unknown %d muc %d %s\n",
				last ? "final " : "",
				iter,
				0.0,//cpuTime(),
				m_nICSize - mucSize - unknownSize,
				unknownSize,
				mucSize,
				msg.c_str());
		}
		if (last) {
			printf("### time %g\n", cpuTime());
		}
	}

	class rec_record {
	public:
		uint32_t uid;
		Var v;
		std::vector<lbool> model;

		rec_record(uint32_t _uid, Var _v, std::vector<lbool>& _model) :uid(_uid), v(_v) { model = _model; }
	};


	uint32_t CMinimalCore::GetMaxIc(Map<uint32_t, uint32_t>& mapIcToScore)
	{
		uint32_t maxVal = 0;
		uint32_t maxInd = 0;
		for (int bucketId = 0; bucketId < mapIcToScore.bucket_count(); ++bucketId)
		{
			const vec<Map<uint32_t, uint32_t>::Pair>& bucket = mapIcToScore.bucket(bucketId);
			for (int elId = 0; elId < bucket.size(); ++elId)
			{
				const Map<uint32_t, uint32_t>::Pair& pair = bucket[elId];
				if (pair.data > maxVal)
				{
					maxVal = pair.data;
					maxInd = pair.key;
				}
			}
		}

		return maxInd;
	}

	uint32_t CMinimalCore::GetMinIc(Map<uint32_t, uint32_t>& mapIcToScore)
	{
		uint32_t minVal = UINT32_MAX;
		uint32_t minInd = UINT32_MAX;
		for (int bucketId = 0; bucketId < mapIcToScore.bucket_count(); ++bucketId)
		{
			const vec<Map<uint32_t, uint32_t>::Pair>& bucket = mapIcToScore.bucket(bucketId);
			for (int elId = 0; elId < bucket.size(); ++elId)
			{
				const Map<uint32_t, uint32_t>::Pair& pair = bucket[elId];
				if (pair.data < minVal)
				{
					minVal = pair.data;
					minInd = pair.key;
					if (minVal == 1)
						return minInd;
				}
			}
		}

		return minInd;
	}



	inline static lbool  Modelvalue(Lit p, std::vector<lbool>& model) { return model[var(p)] ^ sign(p); }

	void CMinimalCore::Rotate_it(uint32_t uid, Var v, Set<uint32_t>& moreMucClauses, Set<uint32_t>& setMuc, bool bUseSet)
	{

		++m_nRotationCalled;
		std::vector<rec_record> S; 	// stack of active calls 
		std::vector<lbool> mymodel;
		for (int i = 0; i < m_Solver.model.size(); ++i) mymodel.push_back(m_Solver.model[i]);
		rec_record rec = rec_record(uid, v, mymodel);
		S.push_back(rec); 	// call f(x)
		while (S.size() > 0) {
			rec_record curr = S.back();
			S.pop_back();

			CRef ref = m_Solver.GetClauseIndFromUid(curr.uid);
			assert(ref != CRef_Undef);
			Clause& cls = m_Solver.GetClause(ref);
			for (int i = 0; i < cls.size(); ++i)
			{
				// we will pass one by one literal and check if the clause is satisfiable with change 
				Var checkVar = var(cls[i]);
				if (checkVar == curr.v)
				{
					continue;
				}

				// first we swap v in the model and count the number of clauses that became unsat as a result of it
				//assert(m_Solver.modelValue(cls[i]) == l_False);
				curr.model[checkVar] = curr.model[checkVar] ^ 1;

				// now we need to check how many variables are 
				vec<uint32_t>& _cs = m_Occurs[toInt(~cls[i])];
				uint32_t* cs = (uint32_t*)_cs;
				int unsatClss = 0;
				uint32_t unsatClsUid = CRef_Undef;
				uint32_t unsatCls1 = CRef_Undef;
				uint32_t unsatCls2 = CRef_Undef;
				for (int j = 0; j < _cs.size() && unsatClss < 2; ++j)
				{
					CRef ref = m_Solver.GetClauseIndFromUid(cs[j]);
					// check if this clause was previously removed
					if (ref == CRef_Undef)
						continue;
					Clause& cls = m_Solver.GetClause(ref);
					int litInd = 0;
					for (; litInd < cls.size(); ++litInd)
					{
						assert(Modelvalue(cls[litInd], curr.model) != l_Undef);
						if (Modelvalue(cls[litInd], curr.model) == l_True)
						{
							break;
						}
					}

					if (litInd == cls.size()) // check if the clause is unsat
					{
						++unsatClss;
						unsatClsUid = cs[j];
						if (unsatClss == 1)
						{
							unsatCls1 = unsatClsUid;
						}
						else
						{
							unsatCls2 = unsatClsUid;
						}
					}
				}
				assert(unsatClss > 0);


				if (unsatClss == 2 && opt_remove_order == 4)
				{
					if (!setMuc.has(unsatCls1))
						m_uidRotationBlockers.push(unsatCls1);
					if (!setMuc.has(unsatCls2))
						m_uidRotationBlockers.push(unsatCls2);
				}
				else if (unsatClss == 1)
				{
					if (bUseSet)
					{
						if (!setMuc.has(unsatClsUid) && moreMucClauses.insert(unsatClsUid))
						{
							S.push_back(rec_record(unsatClsUid, checkVar, curr.model));
						}
					}
					else
					{
						if (moreMucClauses.insert(unsatClsUid))
						{
							S.push_back(rec_record(unsatClsUid, checkVar, curr.model));
						}
					}
				}
				// swap the value back to what it was before			
				curr.model[checkVar] = curr.model[checkVar] ^ 1;
			}
		}
	}

	void CMinimalCore::Rotate(uint32_t uid, Var v, Set<uint32_t>& moreMucClauses, Set<uint32_t>& setMuc, bool bUseSet)
	{

		//printf("rotate %d on var %d, setMuc.size() (after) %d,moreMucClauses.size() (after) %d \n", uid, v, setMuc.elems(), moreMucClauses.elems());

		++m_nRotationCalled;
		CRef ref = m_Solver.GetClauseIndFromUid(uid);
		assert(ref != CRef_Undef);
		Clause& cls = m_Solver.GetClause(ref);
		for (int i = 0; i < cls.size(); ++i)
		{
			// we will pass one by one literal and check if the clause is satisfiable with change 
			Var checkVar = var(cls[i]);
			if (checkVar == v)
			{
				continue;
			}
			// first we swap v in the model and count the number of clauses that became unsat as a result of it
			assert(m_Solver.modelValue(cls[i]) == l_False);
			m_Solver.model[checkVar] = m_Solver.model[checkVar] ^ 1;
			// now we need to check how many variables are 
			vec<uint32_t>& _cs = m_Occurs[toInt(~cls[i])]; //TODO: lazy clean m_Occurs, remove deleted clauses

			uint32_t* cs = (uint32_t*)_cs;
			int unsatClss = 0;
			uint32_t unsatClsUid = CRef_Undef;
			uint32_t unsatClsUid1 = CRef_Undef;
			uint32_t unsatClsUid2 = CRef_Undef;
			for (int j = 0; j < _cs.size() && unsatClss < 2; ++j)
			{
				CRef ref = m_Solver.GetClauseIndFromUid(cs[j]);
				// check if this clause was previously removed
				if (ref == CRef_Undef)
					continue;
				Clause& cls = m_Solver.GetClause(ref);
				int litInd = 0;
				for (; litInd < cls.size(); ++litInd)
				{
					assert(m_Solver.modelValue(cls[litInd]) != l_Undef);
					if (m_Solver.modelValue(cls[litInd]) == l_True)
					{
						break;
					}
				}
				// check if the clause is unsat
				if (litInd == cls.size())
				{
					//m_Solver.printClause(cls, std::to_string(cls.uid()) + " unsat");

					++unsatClss;
					unsatClsUid = cs[j];
					if (unsatClss == 1)
					{
						unsatClsUid1 = unsatClsUid;
						//if (m_Solver.verbosity == 1)
						//	m_Solver.printClauseByUid(unsatClsUid1, "unsatCls1");
					}
					else
					{
						unsatClsUid2 = unsatClsUid;
						//if (m_Solver.verbosity == 1)
						//	m_Solver.printClauseByUid(unsatClsUid2, "unsatCls2");
					}
				}
				//else {
				//	m_Solver.printClause(cls, std::to_string(cls.uid()) + " sat");
				//}

			}

			assert(unsatClss > 0);



			//if (unsatClss == 1) { // exactly one clause is unsat for current assignment
			//	if (bUseSet) { // if true, do rotation only when the clause wasn't seen in either the 'setMuc' or the 'moreMucClauses' collections
			//		if (!setMuc.has(unsatClsUid) && moreMucClauses.insert(unsatClsUid)) {
			//			Rotate(unsatClsUid, checkVar, moreMucClauses, setMuc, bUseSet);
			//		}
			//	}
			//	else {
			//		if (moreMucClauses.insert(unsatClsUid)) {
			//			Rotate(unsatClsUid, checkVar, moreMucClauses, setMuc, bUseSet);
			//		}
			//	}
			//}
			if (unsatClss == 1 && (!bUseSet || !setMuc.has(unsatClsUid)) && moreMucClauses.insert(unsatClsUid)) {
				Rotate(unsatClsUid, checkVar, moreMucClauses, setMuc, bUseSet);
			}



			else if (unsatClss == 2 && opt_remove_order == 4) {
				if (!setMuc.has(unsatClsUid1)) {
					m_uidRotationBlockers.push(unsatClsUid1);
				}
				if (!setMuc.has(unsatClsUid2)) {
					m_uidRotationBlockers.push(unsatClsUid2);
				}
			}

			// swap the value back to what it was before
			m_Solver.model[checkVar] = m_Solver.model[checkVar] ^ 1;
		}

	}


	void CMinimalCore::test(vec<uint32_t>& vecUnknown, Set<uint32_t>& setMuc, char* msg) {
		{
			printf("Testing...%s\n", msg);
			Solver testsolver;
			testsolver.test_mode = true;
			vec<Lit> lits;
			for (int i = 0; i < m_Solver.nVars(); ++i)
				testsolver.newVar();
			for (int i = 0; i < vecUnknown.size(); ++i) {
				CRef ref = m_Solver.GetClauseIndFromUid(vecUnknown[i]);
				if (ref == CRef_Undef) continue;
				Clause& cls = m_Solver.GetClause(ref);
				//m_Solver.printClause(stdout, cls);
				lits.clear();
				cls.copyTo(lits);
				testsolver.addClause(lits);
			}

			vec<unsigned int> tmpvec;
			setMuc.copyTo(tmpvec);

			for (int i = 0; i < tmpvec.size(); ++i) {
				CRef ref = m_Solver.GetClauseIndFromUid(tmpvec[i]);
				if (ref == CRef_Undef) continue;
				Clause& cls = m_Solver.GetClause(ref);
				lits.clear();
				cls.copyTo(lits);
				testsolver.addClause(lits);
			}
			if (testsolver.solve()) {
				printf("did not pass test.");
				exit(1);
			}
			printf("passed test...\n");
		}
	}
	bool CMinimalCore::test(std::unordered_set<Uid>& core, char* msg) {
		Solver testsolver;
		testsolver.test_mode = true;
		vec<Lit> lits;
		for (int i = 0; i < m_Solver.nVars(); ++i)
			testsolver.newVar();
		vec<unsigned int> tmpvec;
		for (Uid uid : core) tmpvec.push(uid);

		for (int i = 0; i < tmpvec.size(); ++i) {
			CRef ref = m_Solver.GetClauseIndFromUid(tmpvec[i]);
			if (ref == CRef_Undef) continue;
			Clause& cls = m_Solver.GetClause(ref);
			lits.clear();
			cls.copyTo(lits);
			testsolver.addClause(lits);
		}
		printf("test for sat now\n");
		return testsolver.solve();
	}


	lbool CMinimalCore::Solve(bool pre)
	{
		vec<uint32_t> vecNextUnknown;
		vec<uint32_t> vecCurrentUnknown;
		vec<uint32_t> currIcCore;
		vec<Lit> assumptions;
		uint32_t nIcForRemove = 0;
		vec<uint32_t> vecUidsToRemove;
		lbool result = l_Undef;
		Set<Uid> setMuc;  // set of ICs that must be in the core
		Set<Uid> moreMucClauses;
		Set<Uid> rhombus; // the set of clauses on the path from the removed clause c, to the empty clause. 
		Set<Uid> nonIcRhombus;
		vec<Uid> moreMucVec;
		double time_after_initial_run;
		double longestcall = 0;
		int lpf_boost_found_trivial_UNSAT = 0;

		m_Solver.time_for_pf = 0.0;
		m_Solver.time_for_pr = 0.0;
		m_Solver.nICtoRemove = 0;
		m_Solver.pf_Literals = 0;
		m_Solver.nUnsatByPF = 0;
		m_Solver.pf_zombie_iter = 0;
		m_Solver.test_mode = false;
		m_Solver.test_now = false;
		// run preprocessing
		double before_time = cpuTime();
		if (!m_bIcInConfl)
			m_bIcInConfl = !m_Solver.eliminate(pre);
		double simplified_time = cpuTime();
		if (m_Solver.verbosity > 1)
		{
			printf("c |  Simplification time:  %12.2f s                                       |\n", simplified_time - before_time);
			printf("c |                                                                             |\n");
		}

		m_Occurs.growTo(m_Solver.nVars() << 1);
		int nIteration = 0;
		int exitIter = max_Iter;
		for (; true; ++nIteration) {


			if (!m_bIcInConfl) {
				before_time = cpuTime();
				result = ((Solver*)&m_Solver)->solveLimited(assumptions);  // SAT call	

				if (nIteration) {
					double time = cpuTime() - before_time;
					if (time > longestcall) longestcall = time;
				}
				if (nIteration == 0) time_after_initial_run = cpuTime();
			}

			else {
				result = l_False;
				m_bIcInConfl = false;
				m_Solver.ResetOk();
			}

#pragma region UNSAT_case
			if (result == l_FalseLevel0) {
				vecNextUnknown.clear();
				goto end;
			}
			if (result == l_False || result == l_FalseNoProof) {
				if (result == l_False && (!m_Solver.m_bUnsatByPathFalsification ||
					m_Solver.isRebuildingProof())) {
					//The normal case where we have a new proof of UNSAT from 
					//the solver.
					if (m_Solver.verbosity == 1) printf("UNSAT \n");

					//First get all the clauses in the UNSAT core - all ic root of 
					//the new resolution graph (i.e., proof of UNSAT) that was 
					//generated by the solver.
					rhombus.clear();
					currIcCore.clear();
					nonIcRhombus.clear();
					m_Solver.GetUnsatCore(currIcCore, rhombus, nonIcRhombus, false, m_nICSize);

					//For each clause in ic core check whether it's not already 
					//in the MUC, and if not then mark it as an unknown ic the be 
					//checked. 

					assert(vecNextUnknown.size() == 0); // !! if not then check why it is not necessarily empty before we fill it with the core.
					for (auto& uid : currIcCore) { // go over clauses in icCore											
						if (uid > m_nICSize) {
							printf("Uid not in original ics: %d\n", uid);

						}
						assert(uid <= m_nICSize);
						if (!setMuc.has(uid)) {
							assert(m_Solver.resolGraph.GetResol(m_Solver.resolGraph.GetResolRef(uid)).header.ic);
							vecNextUnknown.push(uid);
						}

						if (nIteration == 0) {
							if (opt_muc_rotate) {
								// get clauses and add them to "occ list" that is used only in rotate. 
								CRef ref = m_Solver.GetClauseIndFromUid(uid);
								Clause& cls = m_Solver.GetClause(ref);
								for (int i = 0; i < cls.size(); ++i) {
									m_Occurs[toInt(cls[i])].push(uid);
								}
							}
							if (opt_remove_order < 2) {
								m_ClauseHeap.insert(uid);
							}
						}
					}

					vecNextUnknown.removeDuplicated_(); // see why we need it sorted and without duplicates below. 

					PrintData(vecNextUnknown.size(), setMuc.elems(), nIteration, "unsat");

					//if (m_Solver.test_result) test(vecNextUnknown, setMuc, "normal unsat");


					if (vecNextUnknown.size() == 0)	break;

					// ic = interesting clause (not remainder)
					// Removing unused ics and their clauses.

					//Both vecNextUnknown and vecCurrentUnknown are sorted (via 
					//removeDuplicated_). For nIteration > 0, we go over those 
					//clauses in vecCurrentUnknown, and check if they are also 
					//in vecNextUnknown. If not, then we enter them to 
					//'vecUidsToRemove' (if the clause is not going to be check 
					//in the future, as it isn't in 'vecNextUnknown', then it's
					//unnecessary to keep it for future checks, (it's not ic anymore).
					//This means that everything not in the core, and everything in 
					//the core, but also in the MUC, is not ic anymore.
					//'vecNextUnknown' is reset to 0 in the end of the big loop, 
					//and then populated with clauses in the core. 
					assert(vecNextUnknown.size() != vecCurrentUnknown.size());
					int nIndUnknown = 0;
					int nSize = nIteration == 0 ? m_nICSize : vecCurrentUnknown.size();

					//This vector will be populated with the difference between the current ic (unknown) clauses, and the next ic (unknown) clauses.
					vecUidsToRemove.clear();
					for (int i = 0; i < nSize; ++i) { //go over vecCurrentUnknown
						Uid nextUid = nIteration == 0 ? i : vecCurrentUnknown[i];
						if (nextUid != vecNextUnknown[nIndUnknown]) {
							assert(vecUidsToRemove.size() == 0 || vecUidsToRemove.last() < nextUid);
							vecUidsToRemove.push(nextUid);
						}
						else if (nIndUnknown < vecNextUnknown.size() - 1) {
							++nIndUnknown;
						}
						//TODO: add a 'last' else case to quickly iterate over the rest
						//of the i indices and add their relevant Uids to be removed (all the 
						//vecNextUnknown were already iterated over, there is no possibility 
						//of encountering other clauses that shouldn't be removed.
					}


					if (!opt_only_cone)
						m_Solver.RemoveClauses(vecUidsToRemove);
					else {
						m_Solver.RemoveEverythingNotInRhombusOrMuc(rhombus, setMuc);
					}
				}
				else {  // unsat, but contradiction was discovered when the assumptions were added (and opt_blm_rebuild_proof = false).
					if (m_Solver.verbosity == 1) {
						if (result == l_FalseNoProof)
							printf("UNSAT without proof, due to simplification.\n");
						else
							printf("UNSAT (by assumptions)\n");
					}
					remove(vecCurrentUnknown, nIcForRemove);
					if (vecCurrentUnknown.size() == 0) break;
					vecCurrentUnknown.swap(vecNextUnknown);
					vecUidsToRemove.clear();
					vecUidsToRemove.push(nIcForRemove);
					m_Solver.RemoveClauses(vecUidsToRemove);

					if (m_Solver.test_result && m_Solver.test_now) // test_now is used for debugging. Set it near suspicious locations
						test(vecNextUnknown, setMuc, "unsat by assumptions");
					m_Solver.test_now = false;

					PrintData(vecNextUnknown.size(), setMuc.elems(), nIteration, "unsat - blm assumption");
				}
			}
#pragma endregion

#pragma region SAT_case
			else if (result == l_True) {
				if (m_Solver.verbosity == 1) printf("SAT\n");
				if (nIteration == 0) { printf("### SAT\n"); return result; }// the problem is sat			

				// we removed too much ics; add the last one back
				setMuc.insert(nIcForRemove);
				remove(vecCurrentUnknown, nIcForRemove); // remove the index of the clause from the (sorted) current unknown list



				if (vecCurrentUnknown.size() == 0) {
					result = l_False;
					break;
				}
				//Reintroduce the clauses that were previously removed back 
				//into the formula, as normal ('remainder') clauses.
				//Note that here 'vecUidsToRemove' contain the clauses that 
				//were removed in the previous iteration. 
				m_Solver.BindClauses(vecUidsToRemove, nIcForRemove);
#pragma region rotation

				if (opt_muc_rotate) {
					moreMucClauses.clear(); // Here we will collect more clauses to be moved from vecCurrentUnknown (the IC list) and be added to setMuc (i.e., bound as remainder). 
					vec<uint32_t> UidsToBind;  // a subset of moreMucClauses that are not already in setMuc. These we need to bind back as setMuc and remove from vecCurrentUnknown.
					++m_nRotationFirstCalls;
					if (m_Solver.verbosity == 1) printf("Rotate...\n");

					Rotate(nIcForRemove, var_Undef, moreMucClauses, setMuc, ((opt_set_ratio * setMuc.elems()) >= vecCurrentUnknown.size()));
					//Rotate_it(nIcForRemove, var_Undef, moreMucClauses, setMuc, ((opt_set_ratio * setMuc.elems()) >= vecCurrentUnknown.size()));  // a little slower. Supposed to prevent stack-overflow problems with the recursive version. 

					if (opt_second_sat_call) {
						if (m_Solver.verbosity == -1) {
							printf("opt_second_sat_call\n");
						}
						if (!opt_sec_rot_use_prev) {
							moreMucVec.clear();
							moreMucClauses.copyTo(moreMucVec);

							for (int i = 0; i < moreMucVec.size(); ++i) {
								uint32_t uid = moreMucVec[i];
								if (setMuc.insert(uid)) {
									++m_nRotationClausesAdded;
									UidsToBind.push(uid);
									remove(vecCurrentUnknown, uid);
								}
							}

							moreMucClauses.clear();
						}

						int nSizeBefore = setMuc.elems();
						m_Solver.ReversePolarity();
						((Solver*)&m_Solver)->solveLimited(assumptions);
						if (m_Solver.verbosity == 1) printf("Rotate...\n");
						Rotate(nIcForRemove, var_Undef, moreMucClauses, setMuc, ((opt_set_ratio * setMuc.elems()) >= vecCurrentUnknown.size()));
						//Rotate_it(nIcForRemove, var_Undef, moreMucClauses, setMuc, ((opt_set_ratio * setMuc.elems()) >= vecCurrentUnknown.size()));
						m_nSecondRotationClausesAdded += (setMuc.elems() - nSizeBefore);
					}

					moreMucVec.clear();
					moreMucClauses.copyTo(moreMucVec);
					//if (m_Solver.verbosity == -1) {
					//	printf("(before) adding moreMucVec.size() %d to setMuc.size() %d\n", moreMucVec.size(), setMuc.elems());

					//}
					for (int i = 0; i < moreMucVec.size(); ++i)
					{
						uint32_t uid = moreMucVec[i];
						if (setMuc.insert(uid)) // true if it is a new item
						{
							++m_nRotationClausesAdded;
							UidsToBind.push(uid);
							remove(vecCurrentUnknown, uid);
						}
					}
					//if (m_Solver.verbosity == -1) {
					//	printf("(after) adding moreMucVec.size() %d to setMuc.size() %d\n", moreMucVec.size(), setMuc.elems());

					//}
					if (vecCurrentUnknown.size() == 0)
					{
						result = l_False;
						break;
					}
					// sort(vecUidsToRemove); // does not seem necessary
					m_Solver.GroupBindClauses(UidsToBind);
				}
#pragma endregion
				vecCurrentUnknown.swap(vecNextUnknown);

				PrintData(vecNextUnknown.size(), setMuc.elems(), nIteration, "sat");

			}
#pragma endregion

#pragma region Interupt_case
			else
			{
				// interrupt
				if (nIteration != 0)
					vecCurrentUnknown.swap(vecNextUnknown);
				else
				{
					vecNextUnknown.growTo(m_nICSize);
					for (uint32_t nInd = 0; nInd < m_nICSize; ++nInd)
					{
						vecNextUnknown[nInd] = nInd;
					}
				}

				break;
			}
#pragma endregion

#pragma region search_next_clause


			// searching for the next clause c to attempt removing			
			vecUidsToRemove.clear();
			CRef cr;
			while (true) {
				switch ((unsigned)opt_remove_order) {
				case 4: // here we first try to remove a clause that interrupted rotation (when we have two unsat clauses instead of 1)
					nIcForRemove = CRef_Undef;
					while (nIcForRemove == CRef_Undef && m_uidRotationBlockers.size() > 0) {
						nIcForRemove = m_uidRotationBlockers.last();
						m_uidRotationBlockers.pop();
						if (!find(vecNextUnknown, nIcForRemove))
							nIcForRemove = CRef_Undef;
					}

					if (nIcForRemove != CRef_Undef)
						break;  // note the conditional break. If we did not find such a clause (marked by rotation as interrupting), we continue to the '2' strategy below. 
				case 2:
					nIcForRemove = vecNextUnknown.last();
					break;
				case 3:
					nIcForRemove = vecNextUnknown[0];
					break;
				case 0:
				case 1:
					nIcForRemove = CRef_Undef;
					while (nIcForRemove == CRef_Undef) {
						nIcForRemove = m_ClauseHeap.removeMin();
						if (setMuc.has(nIcForRemove) || !find(vecNextUnknown, nIcForRemove))
							nIcForRemove = CRef_Undef;
					}
					break;
				}

				cr = m_Solver.resolGraph.GetClauseRef(nIcForRemove);
				if (cr != CRef_Undef) {
					break;  // if == Cref_Undef, then this clause was removed from the resolution graph (by rotation?). 

				}
				// the clause we selected is trivially satisfied (i.e., there is a remainder unit clause that subsumes it)				
				vecUidsToRemove.push(nIcForRemove);
				remove(vecNextUnknown, nIcForRemove);
				if (vecNextUnknown.size() == 0) { // no unknowns left, end of story. 
					result = l_False;
					goto end;
				}
			}
#pragma endregion

			if (m_Solver.pf_mode != none) {
#ifndef NewParents				
				if ((result == l_False) && m_Solver.m_bConeRelevant && (m_Solver.pf_mode == lpf || m_Solver.pf_mode == lpf_inprocess)) {
					m_Solver.icParents.copyTo(m_Solver.prev_icParents);
					// m_Solver.resolGraph.m_icPoEC.copyTo()
					if (nIteration == 0) m_Solver.icParents.copyTo(m_Solver.parents_of_empty_clause);
				}
#endif

				// now we mine for backbone literals, via PF_get_assumptions.
				// We activate it in all modes except lpf_inprocess because of the option to 
				// delay activation of lpf_inprocess via lpf_block
				if (m_Solver.pf_mode == clause_only || m_Solver.pf_mode == pf || m_Solver.pf_mode == lpf) {
					double before_time = cpuTime();
					int addLiterals = m_Solver.PF_get_assumptions(nIcForRemove, cr);
					if (m_Solver.verbosity == 1) printf("(between iterations) assumption literals = %d\n", addLiterals);
					m_Solver.pf_Literals += addLiterals;
					m_Solver.time_for_pf += (cpuTime() - before_time);
				}
				else m_Solver.LiteralsFromPathFalsification.clear(); // lpf_inprocess needs this, because it might compute this set in a previous iteration. Note that lpf_inprocess is not activated if !m_bConeRelevant		
			}

			// we now remove clauses that are trivially satisfied by units in the remainder, as well as all their descendants. 
			if (vecUidsToRemove.size() > 0) {
				if (m_Solver.pf_mode == lpf || m_Solver.pf_mode == lpf_inprocess)
					m_Solver.RemoveClauses_withoutICparents(vecUidsToRemove); // we need to maintain clauses from IC's to the empty clause with these optimizations. 
				else m_Solver.RemoveClauses(vecUidsToRemove); // remove all their cones. 
				vecUidsToRemove.clear();
			}
			vecUidsToRemove.push(nIcForRemove);

			// removes cone(nIcForRemove);
			//After this line, vecUidsToRemove contains all clauses that were unbounded from the formula

			if (m_Solver.isRebuildingProof()) {
				m_Solver.unbindedCone.clear();
				m_Solver.UnbindClauses(vecUidsToRemove, m_Solver.unbindedCone);
			}
			else {
				m_Solver.UnbindClauses(vecUidsToRemove);
			}
			vecCurrentUnknown.swap(vecNextUnknown);
			vecNextUnknown.clear();
			m_Solver.nICtoRemove = nIcForRemove;



			if (exitIter > 0 && nIteration == exitIter - 1)
				m_Solver.verbosity = -1;
			if (exitIter > 0 && nIteration == exitIter)
				exit(5);
		}  // main 'true' loop

#pragma region end_of_story

		end : PrintData(vecNextUnknown.size(), setMuc.elems(), nIteration, "last", true);
		vec<uint32_t> vecMuc;
		setMuc.copyTo(vecMuc);
		sort(vecMuc);

		/*printf("Summary: nIteration = %d muc size = %d rotation first-calls = %d\n" 
			"rotations = %d rotation clauses added = %d second rotation clauses added = %d pf literals = %d\n", 
			nIteration, vecMuc.size(), 
			m_nRotationFirstCalls, m_nRotationCalled, m_nRotationClausesAdded, m_nSecondRotationClausesAdded, m_Solver.pf_Literals);
			*/
		printf("### muc-size %d", vecMuc.size());
		printf("### lpf_literals %d\n", m_Solver.pf_Literals);
		printf("### UNSAT_by_pf %d\n", m_Solver.nUnsatByPF);
		printf("### iter %d\n", nIteration);
		printf("### true_assump_ratio %f\n", (float)m_Solver.count_assump > 0 ? (float)m_Solver.count_true_assump / (float)m_Solver.count_assump : 0.0);
		printf("### nettime %g\n", cpuTime() - time_after_initial_run);
		printf("### longestcall %g\n", longestcall);

		if (m_Solver.test_result) {
			test(vecNextUnknown, setMuc, "final");
			std::unordered_set<Uid> unsatCore;
			std::unordered_set<Uid> partialCore;



			//setMuc.copyTo(currentPartialCore);
			for (int i = 0; i < setMuc.bucket_count(); ++i)
				for (int j = 0; j < setMuc.bucket(i).size(); ++j)
					unsatCore.insert(setMuc.bucket(i)[j]);
			int i = 0;
			for (Uid uid : unsatCore) {
				partialCore.clear();
				partialCore.insert(unsatCore.begin(), unsatCore.end());
				partialCore.erase(uid);//should now be SAT
				bool isSat = test(partialCore, "isSat?");
				if (!isSat) {
					printf("Core is not minimal! test number %d\n", i);
					//exit(1);
				}
				++i;
			}
			printf("Core is minimal!\n");

		}


		if (opt_print_sol)
		{
			printf("v ");
			for (int nInd = 0; nInd < vecNextUnknown.size(); ++nInd)
			{
				printf("%d ", vecNextUnknown[nInd] + 1);
				/*CRef ref = m_Solver.GetClauseIndFromUid(vecNextUnknown[nInd]);
				assert(ref != CRef_Undef);
				Clause& cls = m_Solver.GetClause(ref);
				m_Solver.printClause(stdout, cls);				*/
			}

			for (int nInd = 0; nInd < vecMuc.size(); ++nInd)
			{
				printf("%d ", vecMuc[nInd] + 1);
				/*CRef ref = m_Solver.GetClauseIndFromUid(vecMuc[nInd]);
				assert(ref != CRef_Undef);
				Clause& cls = m_Solver.GetClause(ref);
				m_Solver.printClause(stdout, cls);*/
			}
			printf("0\n");
		}
#pragma endregion

		return result;
	}

	//void CMinimalCore::testsat() {
	//	vec<Lit> dummy;
	//	int var1 = abs(1) - 1; // var = 1	
	//	int var2 = abs(2) - 1; // var = 2	
	//	int var8 = abs(8) - 1; // var = 8	
	//	Lit BLM1 = mkLit(var1); // BLM 1 means assumption = -1		
	//	Lit BLM2 = mkLit(var2); // BLM 2 means assumption = -2	
	//	Lit BLM8 = mkLit(var8); // BLM 8 means assumption = -8	
	//	m_Solver.nICtoRemove = 1;
	//	m_Solver.test_mode = false;
	//	m_Solver.pf_zombie = false;
	//	m_Solver.LiteralsFromPathFalsification.push(BLM1); // reminder: enter the negated assumption.
	//	m_Solver.LiteralsFromPathFalsification.push(BLM2); // reminder: enter the negated assumption.
	//	m_Solver.LiteralsFromPathFalsification.push(BLM8); // reminder: enter the negated assumption.
	//	lbool res = ((Solver*)&m_Solver)->solveLimited(dummy);
	//	printf("vars = %d\n", m_Solver.nVars());
	//	if (res == l_True) printf("SAT\n");
	//	else if (res == l_False) printf("UNSAT\n");
	//	else printf("unknown\n");

	//	exit(0);
	//}


}



