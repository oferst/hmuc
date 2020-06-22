#ifndef RESOLUTION_GRAPH_H
#define RESOLUTION_GRAPH_H

#include "mtl/Map.h"
#include "mtl/Set.h"
#include "core/SolverTypes.h"
#include<unordered_map>
#include <string.h>
#include <iostream>
#include <fstream>
using namespace std;
namespace Minisat
{
	typedef CRef RRef; //RRef - Resolution Ref
	const RRef RRef_Undef = CRef_Undef;



class ParentIter;
class Resol
{

#define IC_OFFSET 1
#define NON_IC_OFFSET 1
public:
	static int debug_resol;
	//a vec<Uid> containing the Uids of the children of this node.
	//Note that unlike the parents, child nodes are dynamically added and 
	//therefore cannot be declared at construction - the solution is to 
	//use a vec<Uid> object that is able to grow dynamically, 
	//and will not be allocated in advance. 
	//Takes up 4 32-bit words in memory
    vec<uint32_t> m_Children;
	struct {
		unsigned ic : 1;
		unsigned hasNonIcParents : 1; //if this flag is turned on, then this node contains some remainder clauses as parents (in m_Parents below) - can only active when using opt-blm-rebuild-proof to findParentsUsed a proof in a BLM calc
		unsigned m_nRefCount : 30; // the number of nodes (this node + children) known to be ic by this node. Basically the count of all the ic children and (if this node is ic) itself

	} header; //take up 1 32-bit words in memory
    union {
		uint32_t icSize;
        uint32_t icParent;
		uint32_t nonIcSize;//number of non-ic parnet clauses (at the time of creating this Resol node)
		uint32_t nonIcParent; //uid of non-ic parnet clause (at the time of creating this Resol node)
		uint32_t guideFlags;//an ordering  guide (implemented as a boolean array packed to uint32_t array) to the location of each parnet (ic or non-ic) in the node - 0 is non-ic part - while 1 is an ic. This array implements a total ordering of the parents as was defined by the resolution order that created the current Resol node.
    } m_Parents[0];

    uint32_t* IcParents(){
       return &m_Parents[IC_OFFSET].icParent;
    }
	uint32_t* nonIcParents(){
		return (header.hasNonIcParents) ? &m_Parents[IC_OFFSET + icParentsSize() + NON_IC_OFFSET].nonIcParent : NULL;
	}
    inline int icParentsSize() const{
        return m_Parents[0].icSize;
    }
	inline int nonIcParentsSize() const{
		return (!header.hasNonIcParents) ? 0 : m_Parents[IC_OFFSET + icParentsSize()].nonIcSize;
	}
	
	//this function returns the size (i.e. number of 32-bit words) of the additional data in case non-ic clauses are recorded in the resol node
	inline int nonIcData32bitSize() const {
		if (!header.hasNonIcParents)
			return 0;
		int totalParentsNum = icParentsSize() + nonIcParentsSize();
		//the +1 is for the word containing the number of non-ic parents - 
		//while the rest is the size of the flag array
		return  1 + (totalParentsNum / 32) + (int)((totalParentsNum % 32) != 0); 
	}
    uint32_t sizeIn32Bit() const {
		int totalParentsNum = icParentsSize() + nonIcParentsSize();
        return SIZE + totalParentsNum + nonIcData32bitSize();
    }
	//Number of total parents
	uint32_t size() const {
		return icParentsSize() + nonIcParentsSize();
	}

    friend class ResolAllocator;
//private:
	
	//This represents the number of 32-bit words needed to record the m_children vec, the header, and the icSize uint32_t.
    static const uint32_t SIZE = (sizeof(vec<uint32_t>) >> 2) + 2;

    Resol(const vec<Uid>& icParents,const vec<Uid>& remParents, const vec<Uid>& allParents,bool ic, bool WriteInPlace = false){
		//assert(icParents.size() + remParents.size() == allParents.size());
		if (!WriteInPlace) { // this flag is true only when we reorder the parents in an existing resol node. In such a case there is no need to change the header. 
			header.ic = (int)ic;
			header.m_nRefCount = 1;
		}

        m_Parents[0].icSize = icParents.size();
		uint32_t* ics = &(m_Parents[IC_OFFSET].icParent);
		if (allParents.size() == 0  || allParents.size() == icParents.size()) {
			header.hasNonIcParents = 0;
			for (int i = 0; i < icParents.size(); ++i) {
				ics[i] = icParents[i];
			}
		}
		else { // remParents.size() > 0
			header.hasNonIcParents = 1;
			m_Parents[IC_OFFSET + icParents.size()].nonIcSize = allParents.size()- icParents.size();
			uint32_t * rems = &(m_Parents[IC_OFFSET + icParents.size() + NON_IC_OFFSET].nonIcParent);
			uint32_t * flags = &(m_Parents[IC_OFFSET + icParents.size() + NON_IC_OFFSET + nonIcParentsSize()].guideFlags);
			uint32_t i, j; i = j = 0;
			BitArray ba = BitArray(flags);
			for (uint32_t idx = 0; idx < allParents.size(); ++idx) {	
				if (i<icParents.size() &&  icParents[i] == allParents[idx]) {
					ics[i++] = allParents[idx];
					ba.addBitMSB(1);
				} 
				else {
					//assert(allParents[idx] == remParents[j]);
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
		void updateIdxs() {
			if (!r.header.hasNonIcParents | (f_mask & f_word)) // f_word = flags[idx/32] is the current segment of the flag array we are looking at, f_mask = (1 << idx%32) is a positive power of 2, or a 32-bit word with a single '1' bit that represents the current offset in the current f_word. & (bitwise AND) between f_word and f_mask results in the current relevant flag bit.
				icIdx++;
			else
				remIdx++;
		}
	public:
		ParentIter(const Resol& _r, uint32_t _idx = 0) : 
			r(_r), 
			size(_r.icParentsSize() + _r.nonIcParentsSize()), 
			idx(_idx), 
			icIdx(-1),
			remIdx(-1), 
			flags( (_r.header.hasNonIcParents) ? &(_r.m_Parents[IC_OFFSET + _r.icParentsSize() +NON_IC_OFFSET+ _r.nonIcParentsSize()].guideFlags) : NULL ){
			if (r.header.hasNonIcParents) {
				initFlags();
			}
			updateIdxs();
		}
		bool operator!=(const ParentIter& other) {
			return &r != &other.r || idx != other.idx;
		}
		const ParentIter& operator++() {
			idx++;
			if (idx > size)
				//if already at the end of the iterator, do nothing to actually increment it.
				idx = size;
			else {
				if (r.header.hasNonIcParents) {
					//remainder parents exist, use flag array to increment between ic and rem parents
					incFlagData();
				}
				updateIdxs();
			}
			return *this;
		}
		const uint32_t& operator*() const {
			if (idx >= size)
				return CRef_Undef;
			else if (r.header.hasNonIcParents && !(f_mask & f_word)) //next parent is a remainder parent
				return r.m_Parents[IC_OFFSET + r.icParentsSize() +NON_IC_OFFSET+ remIdx].nonIcParent;
			else {
				return r.m_Parents[IC_OFFSET + icIdx].icParent;
			}
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
		void updateIdxs() {
			if (!r.header.hasNonIcParents || f_mask & f_word) // f_word = flags[idx/32] is the current segment of the flag array we are looking at, f_mask = (1 << idx%32) is a positive power of 2, or a 32-bit word with a single '1' bit that represents the current offset in the current f_word. & (bitwise AND) between f_word and f_mask results in the current relevant flag bit.
				--icIdx;
			else
				--remIdx;
		}
	public:
		RevParentIter(const Resol& _r, int _idx) : 
			r(_r), 
			size(_r.icParentsSize() + _r.nonIcParentsSize()), 
			idx(_idx), 
			icIdx(_r.icParentsSize()), 
			remIdx(_r.nonIcParentsSize()), 
			flags((_r.header.hasNonIcParents) ? &(_r.m_Parents[IC_OFFSET + _r.icParentsSize()+NON_IC_OFFSET + _r.nonIcParentsSize()].guideFlags) : NULL) {
			if (r.header.hasNonIcParents)
				initFlags();
			updateIdxs();
		}
		bool operator!=(const RevParentIter& other) {
			return &r != &other.r || idx != other.idx;
		}
		const RevParentIter& operator--() {

			--idx;
			if (idx < -1)
				//if already at the start of the iterator, do nothing to actually decrement it.
				idx = -1;
			else {
				if (r.header.hasNonIcParents) {
					//remainder parents exist, use flag array to decrement between ic and rem parents.
					decFlagData();
				}
				updateIdxs();
			}
			return *this;
		}
		const uint32_t& operator*() const {
			if (idx <= -1)
				return CRef_Undef;
			else if (r.header.hasNonIcParents && !(f_mask & f_word)) //next parent is a remainder parent
				return r.m_Parents[IC_OFFSET + r.icParentsSize() +NON_IC_OFFSET+ remIdx].nonIcParent;
			else { //next parent is an ic parent
				return r.m_Parents[IC_OFFSET + icIdx].icParent;
			}
		}
	};



	const ParentIter begin() const{
		return ParentIter(*this, 0);
	}
	const RevParentIter rbegin() const {
		return RevParentIter(*this, icParentsSize() + nonIcParentsSize()-1);
	}


	const ParentIter end() const {
		return ParentIter(*this, icParentsSize() + nonIcParentsSize());
	}
	 const RevParentIter rend() const {
		return RevParentIter(*this, -1);
	}
};

class ResolAllocator : public RegionAllocator<uint32_t>
{
public:
	void updateAllocated(RRef rRef, const vec<uint32_t>& icParents, const vec<uint32_t>& remParents, const vec<uint32_t>& allParents) {
		new (lea(rRef)) Resol(icParents, remParents, allParents, operator[](rRef).header.ic, true);
	}
    RRef alloc(const vec<uint32_t>& icParents, const vec<uint32_t>& remParents, const vec<uint32_t>& allParents,bool ic)
    {

		int additionalSize = (remParents.size() == 0) ? 0 : (1 + remParents.size() + (allParents.size() / 32) + (int)((allParents.size() % 32) > 0));
		RRef rRef = RegionAllocator<uint32_t>::alloc(Resol::SIZE + icParents.size() + additionalSize);

        new (lea(rRef)) Resol(icParents,remParents,allParents,ic);
        return rRef;
    } 

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Resol&       operator[](Ref r)       { return (Resol&)RegionAllocator<uint32_t>::operator[](r); }
    const Resol& operator[](Ref r) const { return (Resol&)RegionAllocator<uint32_t>::operator[](r); }
    Resol*       lea       (Ref r)       { return (Resol*)RegionAllocator<uint32_t>::lea(r); }
    const Resol* lea       (Ref r) const { return (Resol*)RegionAllocator<uint32_t>::lea(r); }
    Ref           ael       (const Resol* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(RRef rref)
    {
        Resol& r = operator[](rref);
        r.m_Children.clear(true);
        RegionAllocator<uint32_t>::free(r.sizeIn32Bit());
    }

    void StartReloc()
    {
        m_LastRelocLoc = 0;
    }

    void Reloc(RRef& from) //'from' is a resol ref
    {
        if (from == RRef_Undef)
            return;
        uint32_t size = operator[](from).sizeIn32Bit();

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

	int verbose = 0;
	//________________________________________________________________________________________________

    Resol& GetResol(RRef ref){
	 return m_RA[ref]; 
	}

//________________________________________________________________________________________________


	void AddNewResolution(uint32_t nNewClauseId, CRef ref, const vec<Uid>& icParents);
    void AddNewResolution(uint32_t nNewClauseId, CRef ref, const vec<Uid>& icParents, const vec<Uid>& remParents, const vec<Uid>& allParents);
	void AddRemainderResolution(uint32_t nNewClauseId, CRef ref);
	void reallocRemainderResolution(Uid nUid);
	Uid allocConstUnitResol(Lit l);

	//Set<uint32_t> temp_ics;
	void updateParentsOrder(Uid uid, const vec<Uid>& icParents, const vec<Uid>& remParents, const vec<Uid>& allParents);
    void UpdateClauseRef(uint32_t nUid, CRef newRef) {
        assert(m_UidToData[nUid].m_ResolRef != CRef_Undef);
        assert(m_UidToData[nUid].m_ClauseRef != CRef_Undef);
		m_UidToData[nUid].m_ClauseRef = newRef;
    }
	void UpdateResolRef(uint32_t nUid, RRef newRef) {

		assert(m_UidToData[nUid].m_ResolRef != CRef_Undef);
		assert(newRef != CRef_Undef);
		m_UidToData[nUid].m_ResolRef = newRef;
	}
	//void realocExistingResolution(Uid oldUid, const vec<Uid>& icParents, const vec<Uid>& remParents, const vec<Uid>& allParents);
    CRef GetClauseRef(uint32_t nUid) const {// formerly 'GetInd'
		return m_UidToData[nUid].m_ClauseRef;
    }

    RRef GetResolRef(uint32_t nUid) { // Formerly 'GetResolId
        return m_UidToData[nUid].m_ResolRef;
    }

    void DeleteClause(uint32_t nUid) {
		DecreaseReference(nUid);
		m_UidToData[nUid].m_ClauseRef = CRef_Undef;
    }

    void GetOriginalParentsUids(Uid nUid, vec<Uid>& parents, Set<Uid>& checked,bool debug=false,int maxCoreUid = -1,ostream& out = std::cout,std::string msg_prefix = "");

    void GetClausesCones(vec<uint32_t>& cone);
	void GetClausesCones(vec<uint32_t>& cone,std::unordered_set<Uid>& coneSet);
    void CheckGarbage()
    {
		//TODO: We need to re-activate shrinkiing. Clauses who were re-allocated to the end of the Resol data arrey (due to requiring more space) could be moved back to their original ordering, in which case they can overwrite some bytes of the following clause.
   //     if (m_RA.wasted() > m_RA.size() * 0.3)te
   //        
			//Shrink();
    }

    int GetParentsNumber(uint32_t nUid)
    {
        return GetResol(GetResolRef(nUid)).icParentsSize();
    }

    void AddNewRemainderUidsFromCone(Set<uint32_t>& good, vec<uint32_t>& start);
	
    void GetTillMultiChild(uint32_t nStartUid, vec<uint32_t>& uniquePath);

    bool ValidUid(uint32_t uid)
    {
        return GetResolRef(uid) != RRef_Undef;
    }

    uint32_t GetNextAvailableUid() const {
		return Clause::GetNextUid();
			//m_UidToData.size();
    }

    Set<uint32_t> m_icPoEC;


	std::unordered_map<uint32_t, vec<Lit>*>  icDelayedRemoval;

	//std::unordered_map<uint32_t, vec<Lit>* > mapClsToTClausePivotsInRhombus; // if opt_blm_rebuild_proof, in lpf_get_assumptions we find, for every clause in rhombus, the pivots through th parents in the rhombus (literals that appear in a parent but not in a child are pivots)
    
	struct Pair 
    {
        CRef m_ClauseRef;
        CRef m_ResolRef;

        Pair() : m_ClauseRef(CRef_Undef) , m_ResolRef(CRef_Undef)
        {}
    };
    // Map that contains mapping between an clause uid to its ind in clause buffer
    vec<Pair> m_UidToData;
	

private:
    void DecreaseReference(uint32_t nUid);


    void Shrink();



    ResolAllocator m_RA;
    vec<uint32_t> dummy;
};




}

#endif


