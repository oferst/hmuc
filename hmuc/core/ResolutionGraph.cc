#include "ResolutionGraph.h"

#include "mtl/Sort.h"

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


// Every resolution node has m_nRefCount initialized to 1 (by the constructor or Resol).
// So if a resolution node has m_nRefCount == 0, it means that it points to a clause that was removed (we call this function only from DeleteClause, which sets ClauseRef = Cref_Undef), and has no children.
void CResolutionGraph::DecreaseReference(uint32_t nUid)
{
    CRef& ref = m_UidToData[nUid].m_ResolRef;
	assert(ref != CRef_Undef);
    Resol& res = m_RA[ref];
    --res.m_nRefCount;
    if (res.m_nRefCount == 0)
    {
        // first decrease reference count for all the parents
        uint32_t* parents = res.Parents();
        for (int nInd = 0; nInd < res.ParentsSize(); ++nInd)
        {
            DecreaseReference(parents[nInd]);
        }

        m_RA.free(ref);		
        ref = CRef_Undef;
    }
}

void CResolutionGraph::DecreaseReference_mark3(uint32_t nUid, ClauseAllocator& ca)
{
	CRef& ref = m_UidToData[nUid].m_ResolRef;
	assert(ref != CRef_Undef);
	Resol& res = m_RA[ref];
	--res.m_nRefCount;
	if (res.m_nRefCount == 0)
	{
		// first decrease reference count for all the parents
		uint32_t* parents = res.Parents();
		for (int nInd = 0; nInd < res.ParentsSize(); ++nInd)
		{
			DecreaseReference_mark3(parents[nInd], ca);
		}
		CRef cr = m_UidToData[nUid].m_ClauseRef;
		if (cr != CRef_Undef)
		{
			ca[cr].mark(3);				
		}
		//m_RA.free(ref);
		//ref = CRef_Undef;
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


void CResolutionGraph::GetClausesCones(vec<uint32_t>& cone, int stopAtMark, ClauseAllocator& ca)
{
	Set<uint32_t> set;
	set.add(cone);
	for (int nInd = 0; nInd < cone.size(); ++nInd)
	{
		uint32_t nUid = cone[nInd];
		//if (stopAtMark >=0) {
			CRef cr = GetInd(nInd);
			if (cr != CRef_Undef) {
				Clause& c = ca[cr];				
				//printf("%d (%d), ", nUid, c.mark());
			}
			//else printf("%d!, ", nUid);
			//if (!(nUid % 20)) printf("\n");
		//}

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
				if (stopAtMark >= 0) {					
					CRef cr = GetInd(nChildId);
					if (cr != CRef_Undef) {
						Clause& c = ca[cr];
						if (c.mark() == stopAtMark) continue;
					}
				}
				if (m_UidToData[nChildId].m_ResolRef != CRef_Undef && set.insert(nChildId)) {					
					cone.push(nChildId);
				}
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
            return;  // how can it be that we are 
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


void CResolutionGraph::GetAllIcUids(Set<uint32_t>& setGood, vec<uint32_t>& start)
{	
    vec<uint32_t> vecToCheck;
    vec<uint32_t> vecCurrChecked;
    bool firstTime = true;

    // add children of all sets to be checked

    setGood.add(start);
    start.copyTo(vecCurrChecked);
    while (vecCurrChecked.size() > 0)
    {
        for (int i = 0; i < vecCurrChecked.size(); ++i)
        {
            int nUid = vecCurrChecked[i];
            if (!firstTime && setGood.has(nUid))
                continue;

            CRef ref = m_UidToData[nUid].m_ResolRef;

            if (ref == CRef_Undef)
                continue;

            Resol& resol = m_RA[ref];
            int nParents = resol.ParentsSize();
            int j = 0;
            uint32_t* parents = resol.Parents();
            for (; j < nParents; ++j)
            {
                if (!setGood.has(parents[j]))
                    break;
            }

            if (j == nParents)
            {
                if (!firstTime)
                    setGood.insert(nUid);
                // pass over all children and add them to be checked
                for (int nChild = 0; nChild < resol.m_Children.size(); ++nChild)
                {
                    vecToCheck.push(resol.m_Children[nChild]);
                }
            }
        }

        firstTime = false;
        //vecToCheck.removeDuplicated_(); // !! just because it leads to stack overflow.
        vecToCheck.swap(vecCurrChecked);
        vecToCheck.clear();
    }
}

}
