#include "ResolutionGraph.h"

#include "mtl/Sort.h"
#include <vector>
#include <algorithm>
#include <stdint.h>

namespace Minisat
{

void CResolutionGraph::AddNewResolution
    (uint32_t nNewClauseId, CRef ref, const vec<uint32_t>& parents)
{
    m_UidToData.growTo(nNewClauseId + 1);
    CRef refResol = m_RA.alloc(parents);

    // increase reference count for all the parents
    for (int nInd = 0; nInd < parents.size(); ++nInd)
    {
        Resol& res = m_RA[m_UidToData[parents[nInd]].m_ResolRef];
        ++res.m_nRefCount;
        res.m_Children.push(nNewClauseId);
    }

    m_UidToData[nNewClauseId].m_ClauseRef = ref;
    m_UidToData[nNewClauseId].m_ResolRef = refResol;
}

// subtracts 1 from reference of nUid. If ref = 0, it means that both nUid and its children 
// were removed from the resolution graph, so we notify the parents of nUid that this child is now removed, 
// by calling this function recursively. If this was the last child of the parent, then this will continue to propagate. 
// So Decreasereference may propagate upwards.
void CResolutionGraph::DecreaseReference(uint32_t nUid)
{
    CRef& ref = m_UidToData[nUid].m_ResolRef;
    Resol& res = m_RA[ref];
    --res.m_nRefCount;
    if (res.m_nRefCount == 0) // no more children
    {
        // first decrease reference count for all the parents
        uint32_t* parents = res.Parents();
        for (int nInd = 0; nInd < res.ParentsSize(); ++nInd)
        {
            DecreaseReference(parents[nInd]);
        }

        m_RA.free(ref);
		// printf("removing ref to %d\n", nUid);
        ref = CRef_Undef;
    }
}

void CResolutionGraph::GetOriginalParentsUids(uint32_t nUid, vec<uint32_t>& allParents, Set<uint32_t>& checked)
{
    Resol& resol = m_RA[m_UidToData[nUid].m_ResolRef];
    int nParentsSize = resol.ParentsSize();
 
     if (nParentsSize == 0)
     {
         allParents.push(nUid);
         return;
     }

     uint32_t* parents = resol.Parents();

     for (int nParentId = 0; nParentId < nParentsSize; ++nParentId)
     {
         if (checked.insert(parents[nParentId]))
            GetOriginalParentsUids(parents[nParentId], allParents, checked);
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
void CResolutionGraph::GetClausesCones(vec<uint32_t>& cone)
{
    Set<uint32_t> set;
    set.add(cone);
    for (int nInd = 0; nInd < cone.size(); ++nInd)
    {
        uint32_t nUid = cone[nInd];
        CRef ref = m_UidToData[nUid].m_ResolRef;
        if (ref == CRef_Undef)
            continue;
        Resol& resol = m_RA[m_UidToData[nUid].m_ResolRef];
        if (resol.m_Children.size() > 0)
        {
            const vec<uint32_t>& children = resol.m_Children;
            for (int nChild = 0; nChild < children.size(); ++nChild)
            {
                uint32_t nChildId = children[nChild];
                if (m_UidToData[nChildId].m_ResolRef != CRef_Undef && set.insert(nChildId))
                    cone.push(nChildId);
            }
        }
    }
}

void CResolutionGraph::GetTillMultiChild(uint32_t nStartUid, vec<uint32_t>& uniquePath)
{
    uint32_t nextUid = nStartUid;

    while (nextUid != CRef_Undef)
    {
        if (m_UidToData[nextUid].m_ResolRef == CRef_Undef)
        {
            return;
        }
        Resol& resol = m_RA[m_UidToData[nextUid].m_ResolRef];

        if (resol.m_Children.size() != 1 || m_EmptyClauseParents.has(nextUid))
        {
            return;
        }        

        nextUid = resol.m_Children[0];
        uniquePath.push(nextUid);
    }
}

void CResolutionGraph::Shrink()
{
    int nSize = m_UidToData.size();
    m_RA.StartReloc();
    for (int nId = 0; nId < nSize; ++nId)
    {
        m_RA.Reloc(m_UidToData[nId].m_ResolRef);
    }
    m_RA.FinishReloc();
}


// assuming the clauses in 'start' are not IC anymore (e.g., we bind them back as originals, after 'SAT' case), 
// then NewRemainders will be filled with all their descendants that now do not have an IC ancestor. 
void CResolutionGraph::GetNewRemaindersFromCone(Set<uint32_t>& NewRemainders, vec<uint32_t>& start)
{
	std::vector<uint32_t> vecNextCheck;
	std::vector<uint32_t> vecCurrCheck;
	bool firstTime = true;

	// add children of all sets to be checked

	NewRemainders.add(start);
	for (int i = 0; i < start.size(); ++i) 
		vecCurrCheck.push_back(start[i]);
	
	while (vecCurrCheck.size() > 0)
	{
		for (int i = 0; i < vecCurrCheck.size(); ++i) {
			int nUid = vecCurrCheck[i];
			if (!firstTime && NewRemainders.has(nUid))
				continue;

			CRef resolRef = m_UidToData[nUid].m_ResolRef;

			if (resolRef == CRef_Undef)
				continue;

			Resol& resol = m_RA[resolRef];
			int nParents = resol.ParentsSize();
			int j = 0;
			uint32_t* parents = resol.Parents();
			for (; j < nParents; ++j)
			{
				if (!NewRemainders.has(parents[j]))
					break;
			}

			if (j == nParents) // all parents are 'good',i.e., not ics.
			{
				if (!firstTime)
					NewRemainders.insert(nUid);
				// pass over all children and add them to be checked
				for (int nChild = 0; nChild < resol.m_Children.size(); ++nChild)
				{
					vecNextCheck.push_back(resol.m_Children[nChild]);
				}
			}
		}

		firstTime = false;

		// this implements removeduplicated_ for a std:vector
		if (vecNextCheck.size() == 0) return;

		std::sort(vecNextCheck.begin(), vecNextCheck.end());
		int nNewInd = 0;
		int nOldInd = 1;
		for (; nOldInd < vecNextCheck.size(); ++nOldInd)
		{
			if (vecNextCheck[nNewInd] != vecNextCheck[nOldInd])
			{
				vecNextCheck[++nNewInd] = vecNextCheck[nOldInd];
			}
		}
		vecNextCheck.resize(nNewInd + 1);
		
		vecNextCheck.swap(vecCurrCheck);
		vecNextCheck.clear();
	}
// print:	printf("setgood.size = %d, start.size = %d\n", NewRemainders.elems(), start.size());
}



}
