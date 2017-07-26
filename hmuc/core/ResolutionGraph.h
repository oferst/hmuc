#ifndef RESOLUTION_GRAPH_H
#define RESOLUTION_GRAPH_H

#include "mtl/Map.h"
#include "mtl/Set.h"
#include "core/SolverTypes.h"
#include<unordered_map>
#include <string.h>

namespace Minisat
{
	typedef CRef RRef; //RRef - Resolution Ref
	const RRef RRef_Undef = CRef_Undef;



//class SimpleParentIter {
//	uint32_t m_idx;
//	const uint32_t* m_data;
//public:
//	SimpleParentIter(const uint32_t* data, uint32_t idx = 0) : m_data(data), m_idx(idx) {}
//	bool operator!=(const SimpleParentIter& other) { return m_idx != other.m_idx; }
//	const SimpleParentIter& operator++() { m_idx++; return *this; }
//	const uint32_t& operator*() const { return m_data[m_idx]; };
//};

class MixedParentIter {
public:
	uint32_t m_icIdx;
	uint32_t m_remIdx;
	const uint32_t* m_icParents;
	const uint32_t* m_remParents;
	const uint32_t* m_flags;

	uint32_t idx;
	uint32_t flagWord;
	uint32_t flagOffset;
	uint32_t currUid;

	MixedParentIter(const uint32_t* icParents,
					const uint32_t* remParents,
					const uint32_t* flags, 
					uint32_t icIdx = 0, 
					uint32_t remIdx = 0) : 
		m_icParents(icParents),m_remParents(remParents), m_flags(flags),
		m_icIdx(icIdx),m_remIdx(remIdx){
		if (m_remParents == NULL) {
			assert(NULL != m_icParents);
			currUid = m_icParents[m_icIdx++];
		}
		else {
			idx = m_icIdx + m_remIdx;
			flagOffset = idx % 32;
			flagWord = m_flags[idx/32] << flagOffset;
			if (flagWord & 0x80000000)
				currUid = m_icParents[m_icIdx++];
			else
				currUid = m_remParents[m_remIdx++];
		}
	}
	bool operator!=(const MixedParentIter& other) { 
		return (m_icIdx + m_remIdx) != (other.m_icIdx + other.m_remIdx); 
	}
	const MixedParentIter& operator++() { 
		if (m_remParents == NULL) {
			currUid = m_icParents[m_icIdx++];
		}
		else {
			if (++flagOffset == 32) {
				flagOffset = 0;
				flagWord = m_flags[(m_icIdx + m_remIdx) / 32];
			}
			else
				flagWord = flagWord << 1;
			if (flagWord & 0x80000000)
				currUid = m_icParents[m_icIdx++];
			else
				currUid = m_remParents[m_remIdx++];
		}
		return *this; 
	}
	const uint32_t& operator*() const { 
		return currUid; 
	}
};

class Resol
{
public:
    vec<uint32_t> m_Children;
	struct {
		unsigned ic : 1;
		unsigned hasRemParents : 1; //if this flag is turned on, then this node containes some remainder clauses as parents (in m_Parents below) - can only active when using opt-blm-rebuild-proof to reconstruct a proof in a BLM calc
		unsigned m_nRefCount : 30; // the number of nodes (this node + children) known to be ic by this node. Basically the count of all the ic children and (if this node is ic) itself

	} header;
    union {
		uint32_t icSize;
        uint32_t icParent;

		uint32_t remSize;//size of parnets who are remainder clauses (at the time of creating this Resol node)
		uint32_t remParent; // uid of parnets who are remainder clauses (at the time of creating this Resol node)
		uint32_t guideFlags;
		//an ordering  guide (implemented as a boolean array packed to uint32_t array) to the location of each parnet (ic or rem) in the node - 0 means to look for it in the rem part - while 1 means to look for the ic part. This array tracks to total ordering of the parents as it was determined in creating the node (the arder of the parents during the analyze conflict call is the order kept here)


    } m_Parents[0];


	MixedParentIter begin() const {
		const uint32_t* icParents = &(m_Parents[1].icParent);
		const uint32_t* remParents = (header.hasRemParents) ? &(m_Parents[2 + IcParentsSize()].remParent): NULL;
		const uint32_t* flags = (header.hasRemParents) ? &(m_Parents[2 + IcParentsSize()+remParentsSize()].guideFlags) : NULL;
		return MixedParentIter(icParents, remParents, flags,0,0);
	}


	MixedParentIter end() const { 
		const uint32_t* icParents = &(m_Parents[1].icParent);
		const uint32_t* remParents = (header.hasRemParents) ? &(m_Parents[2 + IcParentsSize()].remParent) : NULL;
		const uint32_t* flags = (header.hasRemParents) ? &(m_Parents[2 + IcParentsSize() + remParentsSize()].guideFlags) : NULL;
		return MixedParentIter(icParents, remParents, flags, IcParentsSize(), remParentsSize());
	}


    uint32_t* IcParents(){
       return &m_Parents[1].icParent;
    }
	uint32_t* RemParents(){
		assert(header.hasRemParents);
		return (header.hasRemParents) ? &m_Parents[2 + IcParentsSize()].remParent : NULL;
	}
    inline int IcParentsSize() const
    {
        return m_Parents[0].icSize;
    }
	inline int remParentsSize() const
	{
		assert(header.hasRemParents);
		return (header.hasRemParents) ? m_Parents[IcParentsSize() + 1].remSize : 0;
	}
	
	//this function returns the size of the addidtional data in case remainder clases are saved in a resol node, in units of 32-bit words
	inline int additionalRemDataSize() const
	{
		if (!header.hasRemParents)
			return 0;
		int totalParentsNum = IcParentsSize() + remParentsSize();
		return  1 + (totalParentsNum / 32) + (int)((totalParentsNum % 32) != 0); //the +1 is for the cell holding the number of remainders - all the rest are for the size of the flag array
	}
    uint32_t Size() const
    {
		int totalParentsNum = IcParentsSize() + remParentsSize();
		
        return SIZE + totalParentsNum + additionalRemDataSize(); //if remainders exists, add 1 for their header
    }


    friend class ResolAllocator;
//private:
    static const uint32_t SIZE = (sizeof(vec<uint32_t>) >> 2) + 2;

    Resol(const vec<uint32_t>& icParents,const vec<uint32_t>& remainderParents, const vec<uint32_t>& allParents,bool ic)
    {
		header.ic = (int)ic;
		
		header.m_nRefCount = 1;
        m_Parents[0].icSize = icParents.size();

		if (remainderParents.size() == 0) {
			header.hasRemParents = 0;
			for (int i = 0; i < icParents.size(); ++i) {
				int offset = 1;
				m_Parents[i + offset].icParent = icParents[i];
			}
		}




		else { // remainderParents.size() > 0
			header.hasRemParents = 1;
			m_Parents[icParents.size() + 1].remSize = remainderParents.size();
			uint32_t i, j, k; i = j = k = 0;
			uint32_t icOffset = 1;
			uint32_t remOffset = 2 + icParents.size();
			uint32_t guidesOffset = 2 + icParents.size() + remainderParents.size();
			uint32_t guideFlags = 0;

			assert(icParents.size() + remainderParents.size() == allParents.size());


			for (uint32_t idx = 0; idx < allParents.size(); ++idx) {
				if((idx % 32) == 0)
					guideFlags = 0;
				else
					guideFlags = guideFlags << 1;

				if (icParents[i] == allParents[idx]) {
					m_Parents[i + icOffset].icParent = allParents[idx];
					guideFlags = guideFlags | 1;
					i++;
				} 
				else {
					assert(allParents[idx] == remainderParents[j]);
					m_Parents[j + remOffset].remParent = allParents[idx];
					// LSB in guideFlags remains 0 here
					j++;
				}													
				if ((idx % 32) == 31) {										// if currently idx is equiv to 31 (mod 32), then next idx divisible by 32, and in the current iter we finished filling a 32bit guide word,
					m_Parents[guidesOffset + k].guideFlags = guideFlags;	// we place the guides in the proper place in the guide array,
					k++;
				}
			}
			if ((allParents.size() % 32) != 0)
				m_Parents[guidesOffset + k].guideFlags =  guideFlags << (32 - (allParents.size() % 32));
		}
		

    }
};

class ResolAllocator : public RegionAllocator<uint32_t>
{
public:
    CRef alloc(const vec<uint32_t>& icParents, const vec<uint32_t>& remParents, const vec<uint32_t>& allParents,bool ic)
    {

		int additionalSize = (remParents.size() == 0) ? 0 : (1 + remParents.size() + (allParents.size() / 32) + (int)((allParents.size() % 32) > 0));
		CRef cid = RegionAllocator<uint32_t>::alloc(Resol::SIZE + icParents.size() + additionalSize);

        new (lea(cid)) Resol(icParents,remParents,allParents,ic);

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

    void Reloc(CRef& from) //'from' is a resol ref
    {
        if (from == CRef_Undef)
            return;
        uint32_t size = operator[](from).Size();

        if (from == m_LastRelocLoc) {  // the same clause no need to copy
            m_LastRelocLoc += size;
            return;
        }

        assert(from > m_LastRelocLoc);
        uint32_t* pFrom = RegionAllocator<uint32_t>::lea(from);
        uint32_t* pTo = RegionAllocator<uint32_t>::lea(m_LastRelocLoc);
        //memcpy(RegionAllocator<uint32_t>::lea(m_LastRelocLoc), , size);
        for (uint32_t nPart = 0; nPart < size; ++nPart) {
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


    void AddNewResolution(uint32_t nNewClauseId, CRef ref, const vec<uint32_t>& icParents, const vec<uint32_t>& remParents, const vec<uint32_t>& allParents);
	void AddNewResolution(uint32_t nNewClauseId, CRef ref, const vec<uint32_t>& icParents);
	void AddRemainderResolution(uint32_t nNewClauseId, CRef ref);
	//Set<uint32_t> temp_ics;

    void UpdateClauseRef(uint32_t nUid, CRef newRef) {
        assert(m_UidToData[nUid].m_ResolRef != CRef_Undef);
        assert(m_UidToData[nUid].m_ClauseRef != CRef_Undef);
        m_UidToData[nUid].m_ClauseRef = newRef;
    }

    CRef GetClauseRef(uint32_t nUid) const // formerly 'GetInd'
    {
        return m_UidToData[nUid].m_ClauseRef;
    }

    CRef GetResolRef(uint32_t nUid) // Formerly 'GetResolId'
    { 
        return m_UidToData[nUid].m_ResolRef;
    }

    void DeleteClause(uint32_t nUid) {
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
        return GetResol(GetResolRef(nUid)).IcParentsSize();
    }

    void AddNewRemainderUidsFromCone(Set<uint32_t>& good, vec<uint32_t>& start);

    void GetTillMultiChild(uint32_t nStartUid, vec<uint32_t>& uniquePath);

    bool ValidUid(uint32_t uid)
    {
        return GetResolRef(uid) != RRef_Undef;
    }

    uint32_t GetMaxUid() const
    {
        return m_UidToData.size();
    }

    Set<uint32_t> m_EmptyClauseParents;


	std::unordered_map<uint32_t, vec<Lit>*>  icDelayedRemoval;
	std::unordered_map<uint32_t, vec<Lit>* > mapClsToTClausePivotsInRhombus; // if opt_blm_rebuild_proof, in lpf_get_assumptions we find, for every clause in rhombus, the pivots through th parents in the rhombus (literals that appear in a parent but not in a child are pivots)
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


