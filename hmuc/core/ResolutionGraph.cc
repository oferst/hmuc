#include "ResolutionGraph.h"

#include "mtl/Sort.h"
#include <vector>
#include <algorithm>
#include <stdint.h>

namespace Minisat
{

void CResolutionGraph::AddNewResolution
    (uint32_t nNewClauseUid, CRef ref, const vec<uint32_t>& icParents, const vec<uint32_t>& remParents, const vec<uint32_t>& allParents){
	
	m_UidToData.growTo(nNewClauseUid + 1);
	CRef refResol = m_RA.alloc(icParents, remParents, allParents, true);
    // increase reference count for all the icparents
    
	if (remParents.size() > 0) { //this is true only when allowing for parents to ic who are not themselves ic
		for (int nInd = 0; nInd < allParents.size(); ++nInd) {
			CRef resRef = GetResolRef(allParents[nInd]);
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
			CRef resRef = GetResolRef(icParents[nInd]);
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
	vec<CRef> dummyParents;
	CRef refResol = m_RA.alloc(dummyParents, dummyParents, dummyParents,false);
	m_UidToData[nNewClauseUid].m_ClauseRef = ref;
	m_UidToData[nNewClauseUid].m_ResolRef = refResol;
	m_RA[refResol].header.m_nRefCount = 0;
}
void CResolutionGraph::DecreaseReference(uint32_t nUid){
    CRef& ref = m_UidToData[nUid].m_ResolRef;
	if (ref == CRef_Undef)
		return;
    Resol& res = GetResol(ref);
    --res.header.m_nRefCount;
    if (res.header.m_nRefCount <= 0) {

        // first decrease reference count for all the icparents
        uint32_t* parents = res.Parents();
        for (int pUid = 0; pUid < res.ParentsSize(); ++pUid) {
            DecreaseReference(parents[pUid]);
        }


		//than mark node as free in resol graph (lazy removal), by counting the size of memory to free
        m_RA.free(ref);
		// and removing reference to it from m_RA

        ref = CRef_Undef;
		//if (temp_ics.has(nUid))
		//	temp_ics.remove(nUid);
		//if (icDelayedRemoval.find(nUid) != icDelayedRemoval.end()) {
		//	delete(icDelayedRemoval[nUid]);
		//	icDelayedRemoval.erase(nUid);
		//}
    }
	
}

void CResolutionGraph::GetOriginalParentsUids(uint32_t nUid, vec<uint32_t>& allParents, Set<uint32_t>& checked)
{
    Resol& resol = m_RA[m_UidToData[nUid].m_ResolRef];
    int nParentsSize = resol.ParentsSize();

    if (nParentsSize == 0) {
        allParents.push(nUid);
        return;
    }
    uint32_t* parents = resol.Parents();

    for (int i = 0; i < nParentsSize; ++i) {
		CRef parentRef = GetResolRef(parents[i]);
        if (GetResol(parentRef).header.ic && checked.insert(parents[i]))
			GetOriginalParentsUids(parents[i], allParents, checked);
     }
 }

 /*
void CResolutionGraph::BuildBackwardResolution()
{
    // clean all the maps
    RemoveDeleted();
    vec<uint32_t> dummy;
    // pass over ResolutionMap and create corresponding vectors
    for (int nBucket = 0; nBucket < m_ResolutionMap.bucket_count(); ++nBucket)
    {
        // each bucket its a pair between uid to vector of uids
        const vec< Map<uint32_t, vec<uint32_t> >::Pair>&  pairs = m_ResolutionMap.bucket(nBucket);
        for (int nPair = 0; nPair < pairs.size(); ++nPair)
        {
            const Map<uint32_t, vec<uint32_t> >::Pair&  pair = pairs[nPair];
            dummy.push(pair.key);
            int nParents = pair.data.size();
            for (int nParent = 0; nParent < nParents; ++nParent)
            {
                if (m_BackwardResolutionMap.has(pair.data[nParent]))
                {
                    m_BackwardResolutionMap[pair.data[nParent]].push(pair.key);
                }
                else
                {
                    m_BackwardResolutionMap.insert(pair.data[nParent], dummy);
                }
            }

            dummy.pop();
        }
    }
}
*/
void CResolutionGraph::GetClausesCones(vec<uint32_t>& cone) {
    Set<uint32_t> set;
    set.add(cone);
    for (int nInd = 0; nInd < cone.size(); ++nInd) {
        uint32_t nUid = cone[nInd];
        CRef ref = GetResolRef(nUid);
        if (ref == CRef_Undef)
            continue;
        Resol& resol = GetResol(ref);
        if (resol.m_Children.size() > 0) {
            const vec<uint32_t>& children = resol.m_Children;
            for (int i = 0; i < children.size(); ++i)  {
                uint32_t childUid = children[i];
                if (GetResolRef(childUid) != CRef_Undef && set.insert(childUid))
                    cone.push(childUid);
            }
        }
    }
}

void CResolutionGraph::GetTillMultiChild(uint32_t nStartUid, vec<uint32_t>& uniquePath) {
    uint32_t nextUid = nStartUid;
    while (nextUid != CRef_Undef) {
        if (m_UidToData[nextUid].m_ResolRef == CRef_Undef)
            return;
		Resol& resol = GetResol(GetResolRef(nextUid)); // m_RA[m_UidToData[nextUid].m_ResolRef];
        if (resol.m_Children.size() != 1 || m_EmptyClauseParents.has(nextUid)) //oferg: why would we skip on a parent of the empty clause?
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
		//if (nUid == 367885)
		//	printf("uid: %d reloc\n", nUid);
		m_RA.Reloc(m_UidToData[nUid].m_ResolRef);
	}
    m_RA.FinishReloc();
}

// using vector rather than vec, which enables us to use std::sort, which does not stack-overflow at least for now. 

// assuming the clauses in 'start' are not IC anymore (e.g., we bind them back as originals, after 'SAT' case), 
// then NewRemainders will be filled with all their descendants that now do not have an IC ancestor. 
void CResolutionGraph::AddNewRemainderUidsFromCone(Set<uint32_t>& NewRemainders, vec<uint32_t>& start) {
	std::vector<uint32_t> vecNextCheck;
	std::vector<uint32_t> vecCurrCheck;
	bool firstTime = true;

	// add children of all sets to be checked
	NewRemainders.add(start);
	for (int i = 0; i < start.size(); ++i) {
		vecCurrCheck.push_back(start[i]);
	}
	
	while (vecCurrCheck.size() > 0) {
		for (int i = 0; i < vecCurrCheck.size(); ++i) {
			int nUid = vecCurrCheck[i];
			if (!firstTime && NewRemainders.has(nUid))
				continue;
			CRef resolRef = GetResolRef(nUid);
			if (resolRef == CRef_Undef) // oferg: already deleted from resolution graph (all children must have been deleted already, no point in checking deeper)
				continue;

			Resol& resol = GetResol(resolRef);

			int nParents = resol.ParentsSize();
			int j = 0;
			uint32_t* parents = resol.Parents();
			for (; j < nParents; ++j) {
				if (!NewRemainders.has(parents[j]))
					break;
			}

			if (j == nParents) {// all icparents are 'good',i.e., not ics.
				if (!firstTime) {
					NewRemainders.insert(nUid);
				}
				// pass over all children and add them to be checked
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
	//("icDelayedRemoval size: %d\n", icDelayedRemoval.size());
// print:	printf("setgood.size = %d, start.size = %d\n", NewRemainders.elems(), start.size());
}


}
