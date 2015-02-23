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

void CResolutionGraph::DecreaseReference(uint32_t nUid)
{
    CRef& ref = m_UidToData[nUid].m_ResolRef;
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
        vecToCheck.removeDuplicated_();
        vecToCheck.swap(vecCurrChecked);
        vecToCheck.clear();
    }
}

}
