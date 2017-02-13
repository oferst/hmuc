#ifndef RESOLUTION_GRAPH_H
#define RESOLUTION_GRAPH_H

#include "mtl/Map.h"
#include "mtl/Set.h"
#include "core/SolverTypes.h"

#include <string.h>

namespace Minisat
{

class Resol //oferg: The nodes in the resultion graph (probably)
{
public:
    vec<uint32_t> m_Children;
    uint32_t m_nRefCount;
    //uint32_t GetParent(int nParentId) //oferg: unused
    //{
    //    assert((uint32_t)nParentId > m_Parents[0].size);
    //    return m_Parents[nParentId + 1].parent;
    //}

    uint32_t* Parents()
    {
       return &m_Parents[1].parent;
    }

    inline int ParentsSize() const
    {
        return m_Parents[0].size;
    }

    uint32_t Size() const
    {
        return SIZE + ParentsSize();
    }

    friend class ResolAllocator;
private:
	union {
		uint32_t size;
		uint32_t parent;
	} m_Parents[0];
    static const uint32_t SIZE = (sizeof(vec<uint32_t>) >> 2) + 2; //oferg: why does size of a node has an extry 5U empty places?

    Resol(const vec<uint32_t>& parents) :
       m_Children(), m_nRefCount(1)
    {
        //new (&m_Children) vec<uint32_t>();
        m_Parents[0].size = parents.size();
        for (int nParentId = 0; nParentId < parents.size(); ++nParentId)
        {
            m_Parents[nParentId + 1].parent = parents[nParentId];
        }
    }
};

class ResolAllocator : public RegionAllocator<uint32_t>
{
public:
    CRef alloc(const vec<uint32_t>& parents)
    {
        CRef cid = RegionAllocator<uint32_t>::alloc(Resol::SIZE + parents.size());
        
        new (lea(cid)) Resol(parents);

        return cid;
    } 

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Resol&       operator[](Ref r)       { return (Resol&)RegionAllocator<uint32_t>::operator[](r); }
    const Resol& operator[](Ref r) const { return (Resol&)RegionAllocator<uint32_t>::operator[](r); }
    Resol*       lea       (Ref r)       { return (Resol*)RegionAllocator<uint32_t>::lea(r); }
    const Resol* lea       (Ref r) const { return (Resol*)RegionAllocator<uint32_t>::lea(r); }
    Ref           ael       (const Resol* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(CRef cid)
    {
        Resol& r = operator[](cid);
        r.m_Children.clear(true);
        RegionAllocator<uint32_t>::free(r.Size());
    }

    void StartReloc()
    {
        m_LastRelocLoc = 0;
    }

    void Reloc(CRef& from)
    {
        if (from == CRef_Undef)
            return;
        uint32_t size = operator[](from).Size();

        if (from == m_LastRelocLoc)
        {
            // the same clause no need to copy
            m_LastRelocLoc += size;
            return;
        }

        assert(from > m_LastRelocLoc);
        uint32_t* pFrom = RegionAllocator<uint32_t>::lea(from);
        uint32_t* pTo = RegionAllocator<uint32_t>::lea(m_LastRelocLoc);
        //memcpy(RegionAllocator<uint32_t>::lea(m_LastRelocLoc), , size);
        for (uint32_t nPart = 0; nPart < size; ++nPart)
        {
            *pTo = *pFrom;
            ++pTo;
            ++pFrom;
        }

        from = m_LastRelocLoc;
        m_LastRelocLoc += size;
    }

    void FinishReloc()
    {   
        SetSize(m_LastRelocLoc);
        ClearWasted();
    }

private:
    CRef m_LastRelocLoc;
};

class CResolutionGraph
{
public:
	//________________________________________________________________________________________________

    Resol& GetResol(CRef ref)
	{
	 return m_RA[ref]; 
	}

//________________________________________________________________________________________________


    void AddNewResolution(uint32_t nNewClauseId, CRef ref, const vec<uint32_t>& parents);

    void UpdateInd(uint32_t nUid, CRef newRef)
    {
        assert(m_UidToData[nUid].m_ResolRef != CRef_Undef);
        assert(m_UidToData[nUid].m_ClauseRef != CRef_Undef);
        m_UidToData[nUid].m_ClauseRef = newRef;
    }

    CRef GetInd(uint32_t nUid) const
    {
        return m_UidToData[nUid].m_ClauseRef;
    }

    CRef GetResolId(uint32_t nUid) 
    { 
        return m_UidToData[nUid].m_ResolRef;
    }

    void DeleteClause(uint32_t nUid)
    {
        DecreaseReference(nUid);
        m_UidToData[nUid].m_ClauseRef = CRef_Undef;
    }

    void GetOriginalParentsUids(uint32_t nUid, vec<uint32_t>& parents, Set<uint32_t>& checked);

    //void BuildBackwardResolution();

    //void DestroyBackwardResolution();

    void GetClausesCones(vec<uint32_t>& cone);

    void CheckGarbage()
    {
        if (m_RA.wasted() > m_RA.size() * 0.3)
            Shrink();
    }

    int GetParentsNumber(uint32_t nUid)
    {
        return m_RA[m_UidToData[nUid].m_ResolRef].ParentsSize();
    }

    void GetAllIcUids(Set<uint32_t>& good, vec<uint32_t>& start);

    void GetTillMultiChild(uint32_t nStartUid, vec<uint32_t>& uniquePath);

    bool ValidUid(uint32_t uid)
    {
        return m_UidToData[uid].m_ResolRef != CRef_Undef;
    }

    uint32_t GetMaxUid() const
    {
        return m_UidToData.size();
    }

    Set<uint32_t> m_EmptyClauseParents;

private:
    void DecreaseReference(uint32_t nUid);

    void Shrink();

    struct Pair 
    {
        CRef m_ClauseRef;
        CRef m_ResolRef;

        Pair() : m_ClauseRef(CRef_Undef) , m_ResolRef(CRef_Undef)
        {}
    };

    // Map that contains mapping between clause uid to its ind in clause buffer
    vec<Pair> m_UidToData;

    ResolAllocator m_RA;
    vec<uint32_t> dummy;
};

}

#endif


