#include "core/MinimalCore.h"
#include "utils/ParseUtils.h"
#include "mtl/Sort.h"
#include "utils/System.h"
#include "mtl/Heap.h"
#include <stdio.h>
#include <assert.h>

#include<vector>



namespace Minisat
{

	static const char* _cat = "MUC";
	static BoolOption    opt_muc_print			(_cat, "muc-progress", "print progress lines", true);
	static BoolOption    opt_muc_rotate			(_cat, "muc-rotate", "perform rotation algorithm", true);
	static BoolOption    opt_print_sol			(_cat, "muc-print-sol", "print the satisfying solution", true);
	static DoubleOption  opt_set_ratio			(_cat, "set-ratio",   "When we should start using set", 0.0, DoubleRange(0.0, true, 1000000.0, true));
	static BoolOption    opt_second_sat_call	(_cat, "sec-sat-call", "call solver again to get a different SAT assignment", false);
	static BoolOption    opt_sec_rot_use_prev	(_cat, "sec-call-use-prev", "include in second rotation-call previously discovered clauses", true);
	static IntOption     opt_remove_order		(_cat, "remove-order", "removal order: 0 - biggest, 1 - smallest, 2 - highest, 3 - lowest, 4 - rotation\n", 2, IntRange(0, 4));
	static BoolOption    opt_only_cone			(_cat, "only-cone", "remove all the clauses outside the empty clause cone\n", true);
	

	CMinimalCore::CMinimalCore(SimpSolver& solver): 
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

	void CMinimalCore::PrintData(int unknownSize, int mucSize, int iter, bool last)
	{
		if (opt_muc_print)
		{
			printf("c %siter %d time %g not-muc %d unknown %d muc %d\n", 
				last ? "final " : "", 
				iter + 1, 
				cpuTime(),
				m_nICSize - mucSize - unknownSize, 
				unknownSize, 
				mucSize);
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

		rec_record(uint32_t _uid, Var _v, std::vector<lbool>& _model):uid(_uid), v(_v)  {model = _model;} 
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



	inline static lbool  Modelvalue(Lit p, std::vector<lbool>& model) {return model[var(p)] ^ sign(p);}

	void CMinimalCore::Rotate_it(uint32_t uid, Var v, Set<uint32_t>& moreMucClauses, Set<uint32_t>& setMuc, bool bUseSet)
	{
		++m_nRotationCalled;
		std::vector<rec_record> S; 	// stack of active calls 
		std::vector<lbool> mymodel;
		for (int i = 0; i < m_Solver.model.size(); ++i) mymodel.push_back(m_Solver.model[i]);
		rec_record rec = rec_record(uid, v, mymodel);
		S.push_back(rec); 	// call f(x)
		while(S.size() > 0) { 
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
					if  (ref == CRef_Undef)
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
						m_ClausesForRemoval.push(unsatCls1);
					if (!setMuc.has(unsatCls2))
						m_ClausesForRemoval.push(unsatCls2);
				}
				else if (unsatClss == 1) 
				{
					if (bUseSet)
					{
						if (!setMuc.has(unsatClsUid) && moreMucClauses.insert(unsatClsUid))
						{		
							S.push_back(rec_record(unsatClsUid, checkVar,curr.model)); 
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
				if  (ref == CRef_Undef)
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

			if (unsatClss == 1) 
			{
				if (bUseSet)
				{
					if (!setMuc.has(unsatClsUid) && moreMucClauses.insert(unsatClsUid))
					{
						Rotate(unsatClsUid, checkVar, moreMucClauses, setMuc, bUseSet);
					}
				}
				else
				{
					if (moreMucClauses.insert(unsatClsUid))
					{
						Rotate(unsatClsUid, checkVar, moreMucClauses, setMuc, bUseSet);
					}
				}
			}
			else if (unsatClss == 2 && opt_remove_order == 4)
			{
				if (!setMuc.has(unsatCls1))
					m_ClausesForRemoval.push(unsatCls1);
				if (!setMuc.has(unsatCls2))
					m_ClausesForRemoval.push(unsatCls2);
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


	lbool CMinimalCore::Solve(bool pre)
	{
		vec<uint32_t> vecUnknown;
		vec<uint32_t> vecPrevUnknown;
		vec<uint32_t> vecUids;
		vec<Lit> assumptions;
		uint32_t nIcForRemove = 0;
		vec<uint32_t> vecUidsToRemove;
		lbool result = l_Undef;
		Set<uint32_t> setMuc;  // set of ICs that must be in the core
		Set<uint32_t> moreMucClauses;
		Set<uint32_t> emptyClauseCone;
		vec<uint32_t> moreMucVec;
		
		
		int lpf_boost_found_trivial_UNSAT = 0;
				
		m_Solver.time_for_pf = 0.0;		
		m_Solver.nICtoRemove = 0; 
		m_Solver.pf_Literals = 0;
		m_Solver.nUnsatByPF = 0;
		//m_Solver.lpf_inprocess_added = 0;
		m_Solver.test_mode = false;
		// run preprocessing
		double before_time = cpuTime();
		if (!m_bIcInConfl)
			m_bIcInConfl = !m_Solver.eliminate(pre);
		double simplified_time = cpuTime();
		if (m_Solver.verbosity > 0)
		{
			printf("c |  Simplification time:  %12.2f s                                       |\n", simplified_time - before_time);
			printf("c |                                                                             |\n"); 
		}

		m_Occurs.growTo(m_Solver.nVars() << 1);
		int nIteration = 0;		
		for (; true; ++nIteration)
		{		
			if (!m_bIcInConfl) {				
				result = ((Solver*)&m_Solver)->solveLimited(assumptions);  // SAT call	
			}

			else
			{
				result = l_False;
				m_bIcInConfl = false;
				m_Solver.ResetOk();
			}
			
#pragma region UNSAT_case

			if (result == l_False) {
				if(!m_Solver.m_bUnsatByPathFalsification)
				{
					// First get all the clauses in unsat core
					printf("UNSAT (normal)\n");
					emptyClauseCone.clear();
					m_Solver.GetUnsatCore(vecUids, emptyClauseCone);
					// vecUids.removeDuplicated_();
					// for each clause in vecUids check if its ic
					// and mark it as unknown. 
					for (int nInd = 0; nInd < vecUids.size(); ++nInd)
					{
						uint32_t nIc = vecUids[nInd];
						assert(nIc <= m_nICSize);
						if (!setMuc.has(nIc))
						{
							vecUnknown.push(nIc);
						}

						if (nIteration == 0)
						{
							// get clauses and add them to occ list
							CRef ref = m_Solver.GetClauseIndFromUid(nIc);
							Clause& cls = m_Solver.GetClause(ref);
							for (int i = 0; i < cls.size(); ++i)
							{
								m_Occurs[toInt(cls[i])].push(nIc);
							}

							if (opt_remove_order < 2)
							{
								m_ClauseHeap.insert(nIc);
							}
						}
					}
					vecUnknown.removeDuplicated_();

					PrintData(vecUnknown.size(), setMuc.elems(), nIteration);


					//if (m_Solver.test_result) test(vecUnknown, setMuc, "normal unsat");


					if (vecUnknown.size() == 0)
					{
						break;
					}

					// now lets remove all unused ics and all their clauses
					// for the first iteration all ics are inside so this need
					// a different treatment, for all others we will check 
					// the previous vector

					// build backward resolution relation so it will be much
					// easier to remove cones
					assert(vecUnknown.size() != vecPrevUnknown.size());
					int nIndUnknown = 0;
					int nSize = nIteration == 0 ? m_nICSize : vecPrevUnknown.size();
					vecUidsToRemove.clear();
					for (int nInd = 0; nInd < nSize; ++nInd)
					{
						uint32_t nIcId = nIteration == 0 ? nInd : vecPrevUnknown[nInd];
						if (nIcId != vecUnknown[nIndUnknown])
						{
							// remove from sat solver
							// get all the clauses that are related to this ic
							assert(vecUidsToRemove.size() == 0 || vecUidsToRemove.last() < nIcId);
							vecUidsToRemove.push(nIcId);
							//                    setNotMuc.insert(nIcId);
						}
						else
						{
							if (nIndUnknown + 1 < vecUnknown.size())
							{
								++nIndUnknown;
							}
						}
					}

					//sort(vecUidsToRemove);
					// remove their cones				
					if (!opt_only_cone)
						m_Solver.RemoveClauses(vecUidsToRemove);
					else
						m_Solver.RemoveEverythingNotInCone(emptyClauseCone, setMuc);

				}
				else {  // unsat, but contradiction was discovered when the assumptions were added.
					printf("UNSAT (by assumptions)\n");
					remove(vecPrevUnknown, nIcForRemove);
					if (vecPrevUnknown.size() == 0) break;
					vecPrevUnknown.swap(vecUnknown);
					vecUidsToRemove.clear();
					vecUidsToRemove.push(nIcForRemove);
					m_Solver.RemoveClauses(vecUidsToRemove);    		

				if (m_Solver.test_result && m_Solver.test_now) // test_now is used for debugging. Set it near suspicious locations
					test(vecUnknown, setMuc, "unsat by assumptions");
				m_Solver.test_now = false;


				PrintData(vecUnknown.size(), setMuc.elems(), nIteration);
				}
			}
#pragma endregion

#pragma region SAT_case
			else if (result == l_True)
			{
				printf("SAT\n");
				/*for (int j = 0; j < 300; ++j)
					printf("%d ", m_Solver.model[j]);*/
				


				if (nIteration == 0)
					return result; // the problem is sat			

				// we removed too much ics; add the last one back
				setMuc.insert(nIcForRemove);  
				remove(vecPrevUnknown, nIcForRemove); // remove the index of the clause from the unknown list
				if (vecPrevUnknown.size() == 0)
				{
					result = l_False;
					break;
				}

				m_Solver.BindClauses(vecUidsToRemove, nIcForRemove); // introduce the clauses that were previously removed back into the formula, as 'normal' clauses
#pragma region rotation

				if (opt_muc_rotate)
				{
					vecUidsToRemove.clear();
					moreMucClauses.clear();
					++m_nRotationFirstCalls;
					printf("Rotate...\n");
					Rotate(nIcForRemove, var_Undef, moreMucClauses, setMuc, ((opt_set_ratio * setMuc.elems()) >= vecPrevUnknown.size()));
					//Rotate_it(nIcForRemove, var_Undef, moreMucClauses, setMuc, ((opt_set_ratio * setMuc.elems()) >= vecPrevUnknown.size()));  // a little slower. Supposed to prevent stack-overflow problems with the recursive version. 

					if (opt_second_sat_call)
					{
						if (!opt_sec_rot_use_prev)
						{
							moreMucVec.clear();
							moreMucClauses.copyTo(moreMucVec);

							for (int i = 0; i < moreMucVec.size(); ++i)
							{
								uint32_t uid = moreMucVec[i];
								if (setMuc.insert(uid))
								{
									++m_nRotationClausesAdded;
									vecUidsToRemove.push(uid);
									remove(vecPrevUnknown, uid);
								}
							}

							moreMucClauses.clear();
						}

						int nSizeBefore = setMuc.elems();
						m_Solver.ReversePolarity();
						((Solver*)&m_Solver)->solveLimited(assumptions);
						printf("Rotate...\n");
						Rotate(nIcForRemove, var_Undef, moreMucClauses, setMuc, ((opt_set_ratio * setMuc.elems()) >= vecPrevUnknown.size()));
						//Rotate_it(nIcForRemove, var_Undef, moreMucClauses, setMuc, ((opt_set_ratio * setMuc.elems()) >= vecPrevUnknown.size()));
						m_nSecondRotationClausesAdded += (setMuc.elems() - nSizeBefore);
					}

					moreMucVec.clear();
					moreMucClauses.copyTo(moreMucVec);

					for (int i = 0; i < moreMucVec.size(); ++i)
					{
						uint32_t uid = moreMucVec[i];
						if (setMuc.insert(uid))
						{
							++m_nRotationClausesAdded;
							vecUidsToRemove.push(uid);
							remove(vecPrevUnknown, uid);
						}
					}

					if (vecPrevUnknown.size() == 0)
					{
						result = l_False;
						break;
					}

					sort(vecUidsToRemove);
					m_Solver.GroupBindClauses(vecUidsToRemove);
				}
#pragma endregion
				vecPrevUnknown.swap(vecUnknown);
				PrintData(vecUnknown.size(), setMuc.elems(), nIteration);			
			}			
#pragma endregion

#pragma region Interupt_case
			else
			{
				// interrupt
				if (nIteration != 0)
					vecPrevUnknown.swap(vecUnknown);
				else
				{
					vecUnknown.growTo(m_nICSize);
					for (uint32_t nInd = 0; nInd < m_nICSize; ++nInd)
					{
						vecUnknown[nInd] = nInd;
					}
				}

				break;
			}
#pragma endregion

#pragma region search_next_clause
			// searching for the next clause c to attempt removing			
			vecUidsToRemove.clear(); 
			CRef cr;
			while (true)  
			{
				switch ((unsigned)opt_remove_order)
				{
				case 4:
					nIcForRemove = CRef_Undef;
					while (nIcForRemove == CRef_Undef && m_ClausesForRemoval.size() > 0)
					{
						nIcForRemove = m_ClausesForRemoval.last();
						m_ClausesForRemoval.pop();
						if (!find(vecUnknown, nIcForRemove))
							nIcForRemove = CRef_Undef;
					}

					if (nIcForRemove != CRef_Undef)
					{
						break;
					}
				case 2:
					nIcForRemove = vecUnknown.last();
					break;
				case 3:
					nIcForRemove = vecUnknown[0];
					break;
				case 0:
				case 1:
					nIcForRemove = CRef_Undef;
					while (nIcForRemove == CRef_Undef)
					{
						nIcForRemove = m_ClauseHeap.removeMin();

						if (setMuc.has(nIcForRemove) || !find(vecUnknown, nIcForRemove))
							nIcForRemove = CRef_Undef;
					}
					break;
				}

				cr = m_Solver.resol.GetInd(nIcForRemove);
				if (cr != CRef_Undef) break;

				// the clause we selected is undefined because it was removed, possibly by rotation							
				vecUidsToRemove.push(nIcForRemove);
				remove(vecUnknown, nIcForRemove);
				if (vecUnknown.size() == 0)  { // no unknowns left, end of story. 
					result = l_False;
					goto end;
				}				
			}
#pragma endregion

			
			printf("nictoremove = %d\n", nIcForRemove);
			if (m_Solver.pf_mode != none) {
				bool ClauseOnly = (m_Solver.pf_mode == clause_only ) || !m_Solver.m_bConeRelevant;	// we will only add a clause in pf_get_assumptions 
				if (!ClauseOnly && (result == l_False) && (m_Solver.pf_mode == lpf || m_Solver.pf_mode == lpf_inprocess))	 {
					m_Solver.icParents.copyTo(m_Solver.prev_icParents);
					if (nIteration == 0) m_Solver.icParents.copyTo(m_Solver.parents_of_empty_clause);
				}
				if (m_Solver.pf_mode == clause_only || m_Solver.pf_mode == pf || m_Solver.pf_mode == lpf)  // note that we do not use ClauseOnly, because in mode lpf_inprocess, even if !m_bConeRelevant, we do not want to apply it here, because of the option to delay it via lpf_block
				{				
					double before_time = cpuTime();
					int addLiterals = m_Solver.PF_get_assumptions(nIcForRemove, cr);
					printf("(between iterations) assumption literals = %d\n", addLiterals);										
					m_Solver.pf_Literals += addLiterals;
					m_Solver.time_for_pf += (cpuTime() - before_time);						
				}
				else m_Solver.LiteralsFromPathFalsification.clear(); // lpf_inprocess needs this, because it might compute this set in a previous iteration. Note that lpf_inprocess is not activated if !m_bConeRelevant		
			}
			m_Solver.RemoveClauses(vecUidsToRemove);
			vecUidsToRemove.clear();
			vecUidsToRemove.push(nIcForRemove);
			m_Solver.UnbindClauses(vecUidsToRemove); // removes cone(nIcForRemove);
			vecPrevUnknown.swap(vecUnknown);
			vecUnknown.clear();
			m_Solver.nICtoRemove = nIcForRemove;
//			printf("decisions = %d ", m_Solver.decisions );
//			printf("propagations = %d ", m_Solver.propagations );
//			printf("conflicts = %d\n", m_Solver.conflicts );
		}  // main 'true' loop

#pragma region end_of_story

end:	PrintData(vecUnknown.size(), setMuc.elems(), nIteration, true);
		vec<uint32_t> vecMuc;
		setMuc.copyTo(vecMuc);
		sort(vecMuc);

		printf("Summary: %d %d %d %d %d %d %d\n", nIteration, vecMuc.size(), m_nRotationFirstCalls, m_nRotationCalled, m_nRotationClausesAdded, m_nSecondRotationClausesAdded, m_Solver.pf_Literals);
		printf("### lpf_literals %d\n", m_Solver.pf_Literals);
		//printf("### secondary_lpf_literals %d\n", m_Solver.lpf_inprocess_added);
		printf("### UNSAT_by_pf %d\n", m_Solver.nUnsatByPF);
		printf("### iter %d\n", nIteration);		



		if (m_Solver.test_result ) test(vecUnknown, setMuc, "final");


		if (opt_print_sol)
		{
			printf("v ");
			for (int nInd = 0; nInd < vecUnknown.size(); ++nInd)
			{
				printf("%d ", vecUnknown[nInd] + 1);
			}

			for (int nInd = 0; nInd < vecMuc.size(); ++nInd)
			{
				printf("%d ", vecMuc[nInd] + 1);
			}
			printf("0\n");
		}
#pragma endregion

		return result;
	}
}
