#include "ResolutionGraph.h"

#include "mtl/Sort.h"
#include <vector>
#include <algorithm>
#include <stdint.h>
#include "utils/Printer.h"
namespace Minisat
{

int Resol::debug_resol = 0;
//allocates a new Resol for an existing clause (reprs. by it's uid), without changing it's uid. Deletes the old Resol fro, the system. 
void CResolutionGraph::realocExistingResolution(Uid uid, const vec<Uid>& icParents, const vec<Uid>& remParents, const vec<Uid>& allParents) {
	auto& oldPair = m_UidToData[uid];
	RRef oldRRef = oldPair.m_ResolRef;
	Resol& oldResol = m_RA[uid];
	RRef newRRef;
	if (icParents.size() > 0) {
		newRRef = m_RA.alloc(icParents, remParents, allParents, true);
	}
	else {
		vec<Uid> dummyParents;
		newRRef = m_RA.alloc(dummyParents, dummyParents, dummyParents, false);
	}
	assert(oldRRef != newRRef);
	m_RA.free(oldRRef);
	oldPair.m_ResolRef = newRRef;
}

void CResolutionGraph::AddNewResolution
    (Uid nNewClauseUid, CRef ref, const vec<Uid>& icParents, const vec<Uid>& nonIcParents, const vec<Uid>& allParents){
	m_UidToData.growTo(nNewClauseUid + 1);
	RRef refResol = m_RA.alloc(icParents, nonIcParents, allParents, true);

    // increase reference count for all the icparents
	if (nonIcParents.size() > 0) { //this is true only when allowing for parents to ic who are not themselves ic
		for (int nInd = 0; nInd < allParents.size(); ++nInd) {
			Uid pUid = allParents[nInd];
			CRef resRef = GetResolRef(pUid);
			if (resRef == CRef_Undef)
				continue;
			Resol& res = GetResol(resRef);
			++res.header.m_nRefCount;
			res.m_Children.push(nNewClauseUid);
		}

	}

	//the original code for creating a new resol node.
	//For now (July 2017) it was kept seperated from the changes above to allow for 
	//easy regression testing
	else {
		for (int nInd = 0; nInd < icParents.size(); ++nInd) {
			RRef resRef = GetResolRef(icParents[nInd]);
			if (resRef == CRef_Undef)
				continue;
			Resol& res = GetResol(resRef);
			++res.header.m_nRefCount;
			res.m_Children.push(nNewClauseUid);
		}
	}
    m_UidToData[nNewClauseUid].m_ClauseRef = ref;
    m_UidToData[nNewClauseUid].m_ResolRef = refResol;


}

void CResolutionGraph::AddNewResolution
(uint32_t nNewClauseUid, CRef ref, const vec<uint32_t>& icParents) {
	vec<uint32_t> dummy;
	
	AddNewResolution(nNewClauseUid, ref, icParents, dummy, dummy);
}


void CResolutionGraph::AddRemainderResolution(uint32_t nNewClauseUid, CRef ref) {
	m_UidToData.growTo(nNewClauseUid + 1);
	vec<Uid> dummyParents;
	RRef refResol = m_RA.alloc(dummyParents, dummyParents, dummyParents,false);
	m_UidToData[nNewClauseUid].m_ClauseRef = ref;
	m_UidToData[nNewClauseUid].m_ResolRef = refResol;
}

void CResolutionGraph::reallocRemainderResolution(Uid nUid) {
	vec<Uid> dummyParents;
	RRef refResol = m_RA.alloc(dummyParents, dummyParents, dummyParents, false);
	assert(CRef_Undef != m_UidToData[nUid].m_ClauseRef);
	m_UidToData[nUid].m_ResolRef = refResol;
	m_RA[refResol].header.m_nRefCount = 0;
}
void CResolutionGraph::DecreaseReference(uint32_t nUid){
	
	RRef& ref = m_UidToData[nUid].m_ResolRef;

	if (ref == CRef_Undef)
		return;
    Resol& res = GetResol(ref);


	--res.header.m_nRefCount;
    if (res.header.m_nRefCount <= 0) {

        // first decrease reference count for all the icParents
        uint32_t* parents = res.IcParents();
        for (int i = 0; i < res.icParentsSize(); ++i) {
			DecreaseReference(parents[i]);
        }
		// also decrease reference count for all the nonIc Parents (if any exist)
		if (res.header.hasNonIcParents) {
			parents = res.nonIcParents();

			for (int i = 0; i < res.nonIcParentsSize(); ++i) {
				Uid pUid = parents[i];
				
				DecreaseReference(pUid);
				RRef rref = GetResolRef(pUid);

			}
		}

		//then mark node as free in resol graph (lazy removal), by counting the size of memory to free
        m_RA.free(ref);
		// and removing reference to it from m_RA

		
		ref = CRef_Undef;
		if(!res.header.ic)
			 m_UidToData[nUid].m_ClauseRef = CRef_Undef;
		if (icDelayedRemoval.find(nUid) != icDelayedRemoval.end()) {
			delete(icDelayedRemoval[nUid]);
			icDelayedRemoval.erase(nUid);
		}

    }
	
}

void CResolutionGraph::GetOriginalParentsUids(Uid nUid, vec<Uid>& allIcOriginalClauses, Set<Uid>& rhombus,bool debug,int maxCoreUid, ostream& out,std::string msg_prefix)
{
	//if (nUid > GetNextAvailableUid())
	//	throw ResolutionException(("uid " + std::to_string(nUid) + " larger than MaxUid " + std::to_string(GetNextAvailableUid())).c_str());

    Resol& resol = m_RA[m_UidToData[nUid].m_ResolRef];
	assert(resol.header.ic);
    int icParentsSize = resol.icParentsSize();

    if (icParentsSize == 0) {//assuming a clause is ic, having no parents means it is an original clause (a root), and we add it as such and stop.
		if (nUid > maxCoreUid) {
			printf("Trying to add non original ic uid %d\n", nUid);
		}
		allIcOriginalClauses.push(nUid);

        return;
    }
    uint32_t* icParents = resol.IcParents();
    for (int i = 0; i < icParentsSize; ++i) {
		assert(GetResol(GetResolRef(icParents[i])).header.ic);
		//if (icParents[i] > GetNextAvailableUid())
		//	throw ResolutionException(("icParents[i] " + std::to_string(icParents[i]) + " larger than MaxUid " + std::to_string(GetNextAvailableUid())).c_str());

        if (rhombus.insert(icParents[i])){
			GetOriginalParentsUids(icParents[i], allIcOriginalClauses, rhombus, debug, maxCoreUid,out,msg_prefix);
		}
     }
 }

void CResolutionGraph::GetClausesCones(vec<Uid>& cone) {
    Set<Uid> set;
    set.add(cone);
    for (int nInd = 0; nInd < cone.size(); ++nInd) {
		Uid nUid = cone[nInd];
        RRef ref = GetResolRef(nUid);
        if (ref == CRef_Undef)
            continue;
        Resol& resol = GetResol(ref);
        if (resol.m_Children.size() > 0) {
            const vec<Uid>& children = resol.m_Children;
            for (int i = 0; i < children.size(); ++i)  {
				Uid childUid = children[i];
                if (GetResolRef(childUid) != CRef_Undef && set.insert(childUid))
                    cone.push(childUid);
            }
        }
    }
}
void CResolutionGraph::GetClausesCones(vec<Uid>& cone,std::unordered_set<Uid>& coneSet) {
	assert(coneSet.size() == 0);
	for (auto& uid : cone) {
		coneSet.insert(uid);
	}
	for (int nInd = 0; nInd < cone.size(); ++nInd) {
		Uid nUid = cone[nInd];
		RRef ref = GetResolRef(nUid);
		if (ref == CRef_Undef)
			continue;
		Resol& resol = GetResol(ref);
		if (resol.m_Children.size() > 0) {
			const vec<Uid>& children = resol.m_Children;
			for (int i = 0; i < children.size(); ++i) {
				Uid childUid = children[i];
				//'coneSet.insert(childUid).second' is a boolean indicating whether childUid was inserted to coneSet (i.e. childUid encountered for the first time)
				if (GetResolRef(childUid) != CRef_Undef && coneSet.insert(childUid).second)
					cone.push(childUid);
			}
		}
	}
}
void CResolutionGraph::GetTillMultiChild(uint32_t nStartUid, vec<uint32_t>& uniquePath) {
    uint32_t nextUid = nStartUid;
    while (nextUid != CRef_Undef) {
		RRef rr = GetResolRef(nextUid);
        if (RRef_Undef == rr)
            return;
		Resol& resol = GetResol(rr); // m_RA[m_UidToData[nextUid].m_ResolRef];
        if (resol.m_Children.size() != 1 || m_icPoEC.has(nextUid)) //oferg: why would we skip on a parent of the empty clause?
            return;    
        nextUid = resol.m_Children[0];
        uniquePath.push(nextUid);
    }
}

void CResolutionGraph::Shrink()
{
    int nSize = m_UidToData.size();
    m_RA.StartReloc();
	for (int nUid = 0; nUid < nSize; ++nUid) {
		
		uint32_t prevNumOfIcParents, prevNumOfNonIcParents, newNumOfIcParents, newNumOfNonIcParents;
		if (m_UidToData[nUid].m_ResolRef != RRef_Undef) {
			prevNumOfIcParents = m_RA[m_UidToData[nUid].m_ResolRef].icParentsSize();
			prevNumOfNonIcParents = m_RA[m_UidToData[nUid].m_ResolRef].nonIcParentsSize();
		}
		m_RA.Reloc(m_UidToData[nUid].m_ResolRef);
		if (m_UidToData[nUid].m_ResolRef != RRef_Undef) {

			newNumOfIcParents = m_RA[m_UidToData[nUid].m_ResolRef].icParentsSize();
			newNumOfNonIcParents = m_RA[m_UidToData[nUid].m_ResolRef].nonIcParentsSize();
			if (prevNumOfIcParents != newNumOfIcParents) {
				printf("%d num of ic parents changed from %d to %d\n", nUid, prevNumOfIcParents, newNumOfIcParents);
			}
			if (prevNumOfNonIcParents != newNumOfNonIcParents) {
				printf("%d num of nonic parents changed from %d to %d\n", nUid, prevNumOfNonIcParents, newNumOfNonIcParents);
			}
		}


	}
    m_RA.FinishReloc();
}

// using vector rather than vec, which enables us to use std::sort, which does not stack-overflow at least for now. 

// assuming the clauses in 'start' are not IC anymore (e.g., we bind them back as originals (remainders), after 'SAT' case), 
// then NewRemainders will be filled with all their descendants that now do not have an IC ancestor. 
void CResolutionGraph::AddNewRemainderUidsFromCone(Set<uint32_t>& NewRemainders, vec<uint32_t>& start) {
	std::vector<uint32_t> vecNextCheck;
	std::vector<uint32_t> vecCurrCheck;
	bool firstTime = true;

	//everything in start is now a new remainder clause
	NewRemainders.add(start);

	// add starting new remainders to be checked
	for (int i = 0; i < start.size(); ++i) {
		vecCurrCheck.push_back(start[i]);
	}

	while (vecCurrCheck.size() > 0) {
		for (int i = 0; i < vecCurrCheck.size(); ++i) {
			int nUid = vecCurrCheck[i];
			if (!firstTime && NewRemainders.has(nUid))
				continue;
			RRef resolRef = GetResolRef(nUid);
			if (resolRef == CRef_Undef) // oferg: already deleted from resolution graph (all children must have been deleted already, no point in checking deeper)
				continue;

			Resol& resol = GetResol(resolRef);

			int j = 0;
			int nParents = resol.icParentsSize();
			uint32_t* parents = resol.IcParents();
			for (; j < nParents; ++j) {
				if (!NewRemainders.has(parents[j])) // stop visiting parents if at least one of them is currently not a remainder
					break;
			}

			if (j == nParents) {// if all parents are now remainder,i.e., not ics.
				if (!firstTime) { // than (except for the fisrt iteration (where the clause was pre-added))
					NewRemainders.insert(nUid); //add the newly found remainder to the resulting 'NewRemainders'
				}
				// and lastly, pass over all it's children and add them to be checked
				for (int nChild = 0; nChild < resol.m_Children.size(); ++nChild) {
					vecNextCheck.push_back(resol.m_Children[nChild]);
				}
			}
		}

		firstTime = false;

		if (vecNextCheck.size() == 0) {
			return;
		}

		// this implements removeduplicated_ for a std:vector
		std::sort(vecNextCheck.begin(), vecNextCheck.end());
		int nNewInd = 0;
		int nOldInd = 1;
		for (; nOldInd < vecNextCheck.size(); ++nOldInd) {
			if (vecNextCheck[nNewInd] != vecNextCheck[nOldInd]) {
				vecNextCheck[++nNewInd] = vecNextCheck[nOldInd];
			}
		}
		vecNextCheck.resize(nNewInd + 1);
		vecNextCheck.swap(vecCurrCheck);
		vecNextCheck.clear();
	}
}
	void CResolutionGraph::updateParentsOrder(Uid uid, const vec<Uid>& icParents, const vec<Uid>& remParents, const vec<Uid>& allParents) {
		assert(CRef_Undef != uid);
		RRef rRef = m_UidToData[uid].m_ResolRef;
		assert(CRef_Undef != rRef);
		m_RA.updateAllocated(rRef, icParents, remParents, allParents);
	}

}
