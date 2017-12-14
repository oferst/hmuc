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





class ParentIter;
class Resol
{
public:
    vec<uint32_t> m_Children;
	struct {
		unsigned ic : 1;
		unsigned hasRemParents : 1; //if this flag is turned on, then this node containes some remainder clauses as parents (in m_Parents below) - can only active when using opt-blm-rebuild-proof to findParentsUsed a proof in a BLM calc
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
	uint32_t size() const
	{
		return Size();
	}

    friend class ResolAllocator;
//private:
    static const uint32_t SIZE = (sizeof(vec<uint32_t>) >> 2) + 2;

    Resol(const vec<uint32_t>& icParents,const vec<uint32_t>& remParents, const vec<uint32_t>& allParents,bool ic){
		assert(icParents.size() + remParents.size() == allParents.size());	
		header.ic = (int)ic;
		header.m_nRefCount = 1;

        m_Parents[0].icSize = icParents.size();
		uint32_t* ics = &(m_Parents[1].icParent);
		if (0 == remParents.size()) {
			header.hasRemParents = 0;
			for (int i = 0; i < icParents.size(); ++i) {
				ics[i] = icParents[i];
			}
		}
		else { // remParents.size() > 0
			header.hasRemParents = 1;
			m_Parents[icParents.size() + 1].remSize = remParents.size();
			uint32_t * rems = &(m_Parents[icParents.size() + 2].remParent);
			uint32_t * flags = &(m_Parents[icParents.size() + 2 + remParentsSize()].guideFlags);
			uint32_t i, j; i = j = 0;
			BitArray ba = BitArray(flags);
			for (uint32_t idx = 0; idx < allParents.size(); ++idx) {	
				if (icParents[i] == allParents[idx]) {
					ics[i++] = allParents[idx];
					ba.addBitMSB(1);
				} 
				else {
					assert(allParents[idx] == remParents[j]);
					rems[j++] = allParents[idx];
					ba.addBitMSB(0);
				}													
			}
		}
    }
	class ParentIter {
		const Resol& r;
		const uint32_t size;
		int idx;
		int icIdx;
		int remIdx;

		const uint32_t* flags;
		uint32_t f_word;
		uint32_t f_mask;

		void initFlags() {
			f_mask = 1 << (idx % 32);
			f_word = flags[idx / 32];
			updateIdxsUsingFlags();
		}
		//f_mask is a 32-bit word with a single bit on, incrementing it will bit-shift the bit towards the MSB. If overflowing, rotate back to LSB.
		void incFlagData() {
			if (f_mask < MAX_MASK)
				f_mask = f_mask << 1;
			else {
				f_mask = MIN_MASK;
				f_word = flags[idx / 32];
			}

		}
		//check new flag in flags array. If the new flag is 1 then the next parent is an ic, otherwise it is remainder. Increment the relevant new index accordingly.
		void updateIdxsUsingFlags() {
			if (f_mask & f_word) // f_word = flags[idx/32] is the current segment of the flag array we are looking at, f_mask = (1 << idx%32) is a positive power of 2, or a 32-bit word with a single '1' bit that represents the current offset in the current f_word. & (bitwise AND) between f_word and f_mask results in the current relevant flag bit.
				icIdx++;
			else
				remIdx++;
		}
	public:
		ParentIter(const Resol& _r, uint32_t _idx = 0) : r(_r), size(_r.IcParentsSize() + _r.remParentsSize()), idx(_idx), icIdx(-1),remIdx(-1), flags( (_r.header.hasRemParents) ? &(_r.m_Parents[2 + _r.IcParentsSize() + _r.remParentsSize()].guideFlags) : NULL ){
			if (r.header.hasRemParents) 
				initFlags();
		}
		bool operator!=(const ParentIter& other) {
			return &r != &other.r || idx != other.idx;
		}
		const ParentIter& operator++() {
			idx++;
			if (idx > size)
				//if already at the end of the interator, do nothing to actually increment it.
				idx = size;
			else {
				if (!r.header.hasRemParents)
					//no remainder parents, iterate only on ic parents.
					icIdx++; 
				else {
					//remainder parents exist, use flag array to increment between ic and rem parents.
					incFlagData();
					updateIdxsUsingFlags();
				}
			}
			return *this;
		}
		const uint32_t& operator*() const {
			if (idx >= size)
				return CRef_Undef;
			else if (r.header.hasRemParents && !(f_mask & f_word)) //next parent is a remainder parent
				return r.m_Parents[2 + r.IcParentsSize() + remIdx].remParent;
			else //next parent is an ic parent
				return r.m_Parents[1 + icIdx].icParent;
		}
	};

	class RevParentIter {
		const Resol& r;
		const uint32_t size;
		int idx;
		int icIdx;
		int remIdx;

		const uint32_t* flags;
		uint32_t f_word;
		uint32_t f_mask;

		void initFlags() {
			f_mask = 1 << (idx % 32);
			f_word = flags[idx / 32];
			updateIdxsUsingFlags();
		}
		//f_mask is a 32-bit word with a single bit on, incrementing it will bit-shift the bit towards the MSB. If overflowing, rotate back to LSB.
		void decFlagData() {
			if (f_mask > MIN_MASK)
				f_mask = f_mask >> 1;
			else {
				f_mask = MAX_MASK;
				f_word = flags[idx / 32];
			}

		}
		//check new flag in flags array. If the new flag is 1 then the next parent is an ic, otherwise it is remainder. Increment the relevant new index accordingly.
		void updateIdxsUsingFlags() {
			if (f_mask & f_word) // f_word = flags[idx/32] is the current segment of the flag array we are looking at, f_mask = (1 << idx%32) is a positive power of 2, or a 32-bit word with a single '1' bit that represents the current offset in the current f_word. & (bitwise AND) between f_word and f_mask results in the current relevant flag bit.
				icIdx--;
			else
				remIdx--;
		}
	public:
		RevParentIter(const Resol& _r, uint32_t _idx) : r(_r), size(_r.IcParentsSize() + _r.remParentsSize()), idx(_idx), icIdx(_r.IcParentsSize()), remIdx(_r.remParentsSize()), flags((_r.header.hasRemParents) ? &(_r.m_Parents[2 + _r.IcParentsSize() + _r.remParentsSize()].guideFlags) : NULL) {
			if (r.header.hasRemParents)
				initFlags();
		}
		bool operator!=(const RevParentIter& other) {
			return &r != &other.r || idx != other.idx;
		}
		const RevParentIter& operator--() {
			idx--;
			if (idx < -1)
				//if already at the start of the iterator, do nothing to actually decrement it.
				idx = -1;
			else {
				if (!r.header.hasRemParents)
					//no remainder parents, iterate only on ic parents.
					icIdx--;
				else {
					//remainder parents exist, use flag array to decrement between ic and rem parents.
					decFlagData();
					updateIdxsUsingFlags();
				}
			}
			return *this;
		}
		const uint32_t& operator*() const {
			if (idx <= -1)
				return CRef_Undef;
			else if (r.header.hasRemParents && !(f_mask & f_word)) //next parent is a remainder parent
				return r.m_Parents[2 + r.IcParentsSize() + remIdx].remParent;
			else //next parent is an ic parent
				return r.m_Parents[1 + icIdx].icParent;
		}
	};



	const ParentIter begin() const{
		return ParentIter(*this, 0);
	}
	const RevParentIter rbegin() const {
		printf("size: %d\n", IcParentsSize() + remParentsSize() - 1);
		return RevParentIter(*this, IcParentsSize() + remParentsSize() - 1);
	}


	const ParentIter end() const {
		return ParentIter(*this, IcParentsSize() + remParentsSize());
	}
	 const RevParentIter rend() const {
		return RevParentIter(*this, -1);
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

    Set<uint32_t> m_icPoEC;


	std::unordered_map<uint32_t, vec<Lit>*>  icDelayedRemoval;

	//std::unordered_map<uint32_t, vec<Lit>* > mapClsToTClausePivotsInRhombus; // if opt_blm_rebuild_proof, in lpf_get_assumptions we find, for every clause in rhombus, the pivots through th parents in the rhombus (literals that appear in a parent but not in a child are pivots)
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


