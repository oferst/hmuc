/***********************************************************************************[SolverTypes.h]
Copyright (c) 2003-2006, Niklas Een, Niklas Sorensson
Copyright (c) 2007-2010, Niklas Sorensson

Permission is hereby granted, free of charge, to any person obtaining a copy of this software and
associated documentation files (the "Software"), to deal in the Software without restriction,
including without limitation the rights to use, copy, modify, merge, publish, distribute,
sublicense, and/or sell copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all copies or
substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR IMPLIED, INCLUDING BUT
NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM,
DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT
OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
**************************************************************************************************/


#ifndef Minisat_SolverTypes_h
#define Minisat_SolverTypes_h

#include <assert.h>

#include "mtl/IntTypes.h"
#include "mtl/Alg.h"
#include "mtl/Vec.h"
#include "mtl/Map.h"
#include "mtl/Alloc.h"
#include<iostream>
#include<string>
#include <unordered_map>
#include <unordered_set>


namespace Minisat {

//=================================================================================================
// Variables, literals, lifted booleans, clauses:


// NOTE! Variables are just integers. No abstraction here. They should be chosen from 0..N,
// so that they can be used as array indices.

typedef int Var;
#define var_Undef (-1)


struct Lit {
    int     x;

    // Use this as a constructor:
    friend Lit mkLit(Var var, bool sign = false);

    bool operator == (Lit p) const { return x == p.x; }
	size_t operator()() { return (size_t)x; }
    bool operator != (Lit p) const { return x != p.x; }
    bool operator <  (Lit p) const { return x < p.x;  } // '<' makes p, ~p adjacent in the ordering.
};


struct LitHash {
	std::size_t operator()(const Lit& _l) const {
		return std::hash<int>()(_l.x);
	}
};

inline  Lit  mkLit     (Var var, bool sign) { Lit p; p.x = var + var + (int)sign; return p; }
inline  Lit  operator ~(Lit p)              { Lit q; q.x = p.x ^ 1; return q; }
inline  Lit  operator ^(Lit p, bool b)      { Lit q; q.x = p.x ^ (unsigned int)b; return q; }
//sign==false means the literal is positive
inline  bool sign      (Lit p)              { return p.x & 1; }
inline  int  var       (Lit p)              { return p.x >> 1; }

inline int toDimacsLit(Lit l) {
	int res = var(l) + 1;
	return sign(l) ? -res : res;
}
// Mapping Literals to and from compact integers suitable for array indexing:
inline  int  toInt     (Var v)              { return v; } 
inline  int  toInt     (Lit p)              { return p.x; } 
inline  Lit  toLit     (int i)              { Lit p; p.x = i; return p; } 

//const Lit lit_Undef = mkLit(var_Undef, false);  // }- Useful special constants.
//const Lit lit_Error = mkLit(var_Undef, true );  // }

const Lit lit_Undef = { -2 };  // }- Useful special constants.
const Lit lit_Error = { -1 };  // }


//=================================================================================================
// Lifted booleans:
//
// NOTE: this implementation is optimized for the case when comparisons between values are mostly
//       between one variable and one constant. Some care had to be taken to make sure that gcc 
//       does enough constant propagation to produce sensible code, and this appears to be somewhat
//       fragile unfortunately.

#define l_True  (lbool((uint8_t)0)) // gcc does not do constant propagation if these are real constants.
#define l_False (lbool((uint8_t)1))
#define l_Undef (lbool((uint8_t)2))

class lbool {
    uint8_t value;

public:
    explicit lbool(uint8_t v) : value(v) { }

    lbool()       : value(0) { }
    explicit lbool(bool x) : value(!x) { }

    bool  operator == (lbool b) const { return ((b.value&2) & (value&2)) | (!(b.value&2)&(value == b.value)); }
    bool  operator != (lbool b) const { return !(*this == b); }
    lbool operator ^  (bool  b) const { return lbool((uint8_t)(value^(uint8_t)b)); }

    lbool operator && (lbool b) const { 
        uint8_t sel = (this->value << 1) | (b.value << 3);
        uint8_t v   = (0xF7F755F4 >> sel) & 3;
        return lbool(v); }

    lbool operator || (lbool b) const {
        uint8_t sel = (this->value << 1) | (b.value << 3);
        uint8_t v   = (0xFCFCF400 >> sel) & 3;
        return lbool(v); }

    friend int   toInt  (lbool l);
    friend lbool toLbool(int   v);
};

inline int   toInt  (lbool l) { return l.value; }
inline lbool toLbool(int   v) { return lbool((uint8_t)v);  }

//=================================================================================================
// Clause -- a simple class for representing a clause:

class Clause;

typedef uint32_t Uid;
typedef std::unordered_map<Uid, vec<Lit>> UidToLitVec;
typedef std::unordered_set<Lit, LitHash> LitSet;
typedef std::unordered_map<Uid, LitSet> UidToLitSet;
typedef std::unordered_map<Uid, Uid> UidToUid;
typedef std::unordered_map<Uid, bool> UidLabel;

typedef RegionAllocator<uint32_t>::Ref CRef;
class Clause {
    struct {
		// mark(0): default
		// mark(1): can be deleted next time we garbage collect.  
		// mark(2): remove, but do not remove from resolution graph (usually after mark(2) we update the reference to the clause in the resolution graph). 
        unsigned mark      : 2;
        unsigned learnt    : 1;
        unsigned has_extra : 1;
        unsigned reloced   : 1;
        unsigned ic        : 1;
		//unsigned parentToIc : 1; //oferg To document
		unsigned hasUid	 : 1;
		unsigned size      : 25;
		
	}                            header;
    union { Lit lit; float act; uint32_t abs; CRef rel; uint32_t uid; } data[0];

    static Uid nextUid;

    friend class ClauseAllocator;

    // NOTE: This constructor cannot be used directly (doesn't allocate enough memory).
    template<class V>
    Clause(const V& ps, bool use_extra, bool learnt, bool ic,bool hasUid = false) {
        header.mark      = 0;
        header.learnt    = learnt;
        header.ic      = ic;
		//header.parentToIc = isParentToIc;
		header.hasUid = ic | hasUid;// initially, a non-ic Clause wouldn't have an uid (internally), even if it's a parent to an ic clause and appears in the resolution graph. The actual Uid for the current clause can be accessed by the CRef, through deferredUidAlloc
        header.has_extra = use_extra;
        header.reloced   = 0;
        header.size      = ps.size();

		int i = 0;
		for (Lit l : ps) {
			data[i++].lit = l;
		}

        if (header.has_extra){
            if (header.learnt)
                data[header.size].act = 0; 
            else 
                calcAbstraction(); 
		}

        if (ic || hasUid) {
			Uid uid = nextUid++;
			if (uid == 13456) {
				printf("Creating probl. clause\n");
			}
            data[header.size + (int)header.has_extra].uid = uid;
        }

    }

public:
	static int debugFlag;
	static uint32_t GetNextUid() {return nextUid; }
	static uint32_t GetLastUid() { return nextUid - 1; }
	static void DecreaseUid() {  --nextUid; }
	static uint32_t SetNextUid(uint32_t newUid) { return nextUid = newUid; }
	//void setIsParentToIc(bool isParent) {
	//	header.parentToIc = isParent;
	//	assert(!(header.parentToIc && header.ic));
	//}
	void printClause(std::string text) {
		std::cout << text << std::endl;
		for (int i = 0; i < this->size(); i++) {
			Lit l = (*this)[i];
			int litVal = var((*this)[i]) + 1;
			litVal = sign(l) ? -litVal : litVal;
			std::cout << litVal << " ";
		}
		std::cout << "0" << std::endl;
	}
	void* getHeaderAddr() {
		return &header;
	}
	void* getDataAddr() {
		return data;
	}



    void calcAbstraction() {
        assert(header.has_extra);
        uint32_t abstraction = 0;
        for (int i = 0; i < size(); i++)
            abstraction |= 1 << (var(data[i].lit) & 31);
        data[header.size].abs = abstraction;  }


    int          size        ()      const   { return header.size; }
    void         shrink      (int i)         { 
        assert(i <= size()); 
        if (header.has_extra) 
            data[header.size-i] = data[header.size]; 
        if (header.ic || header.hasUid)
            data[header.size-i + (int)header.has_extra] = data[header.size + (int)header.has_extra];
        header.size -= i; 
    }
    void         pop         ()             { shrink(1); }
    bool         learnt      ()      const  { return header.learnt; }
    bool         ic			 ()      const	{ return header.ic; }
	//bool		 isParentToIc()		 const	{ return header.parentToIc; }
	//Queries whether a Clause object contains Uid data (internally). A clause might have a Uid associated with it that is not kept in the Clause object itself (i.e. the Uid is kept externally), and in this case the query will return 'false' for such clauses.
	bool         hasUid		 ()      const  { return header.hasUid; }
    bool         has_extra   ()      const  { return header.has_extra; }
    uint32_t     mark        ()      const  { return header.mark; }
	
	// mark(0): default
	// mark(1): can be deleted next time we garbage collect.  
	// mark(2): remove, but do not remove from resolution graph (usually after mark(2) we update the reference to the clause in the resolution graph). 
	void         mark(uint32_t m) { header.mark = m; }
    const Lit&   last        ()      const   { return data[header.size-1].lit; }

    bool         reloced     ()      const   { return header.reloced; }
    CRef         relocation  ()      const   { return data[0].rel; }
    void         relocate    (CRef c)        { header.reloced = 1; data[0].rel = c; }

    // NOTE: somewhat unsafe to change the clause in-place! Must manually call 'calcAbstraction' afterwards for
    //       subsumption operations to behave correctly.
    Lit&         operator [] (int i)         { return data[i].lit; }
    Lit          operator [] (int i) const   { return data[i].lit; }
    operator const Lit* (void) const         { return (Lit*)data; }

    float&       activity    ()              { assert(header.has_extra); return data[header.size].act; }
	float       activity() const{ assert(header.has_extra); return data[header.size].act; }
    uint32_t     abstraction () const        { assert(header.has_extra); return data[header.size].abs; }
    uint32_t&    uid         ()              { assert(header.ic || (header.hasUid)); 
		return data[header.size + (int)header.has_extra].uid; }
    uint32_t     uid         () const        { //assert(header.ic || header.parentToIc); 
		return data[header.size + (int)header.has_extra].uid; }
    void         copyTo      (vec<Lit>& other) {
        other.growTo(size());
        for (int i = 0 ; i < size() ; i++) {  // initially parent = c
            other[i] = data[i].lit; 
        }	
    }

    Lit          subsumes    (const Clause& other) const;
    void         strengthen  (Lit p);
	class ClauseIter {
		const Clause& c;
		int i;
	public:
		//ClauseIter() : c(Clause(vec<Lit>(),false,false,false)), i(-1){}
		ClauseIter(const Clause& _c, int _i = 0) : c(_c), i(_i) {}
		ClauseIter(const ClauseIter& o) : c(o.c), i(o.i) {}
		bool operator!=(const ClauseIter& o) { return &c != &o.c || i != o.i; }
		const Lit& operator*() { return (i < 0 || i >= c.size()) ? mkLit(var_Undef) : c[i]; }
		ClauseIter& operator++() { ++i; return *this; }
		//ClauseIter operator++(int) { ClauseIter result(*this); ++(*this); return result; }
		ClauseIter& operator--() { --i; return *this; }
		//ClauseIter operator--(int) { ClauseIter result(*this); --(*this); return result; }
	};


	const ClauseIter begin() const { return ClauseIter(*this, 0); }
	const ClauseIter end() const { return ClauseIter(*this, this->size()); }

};

//=================================================================================================
// ClauseAllocator -- a simple class for allocating memory for clauses:


const CRef CRef_Undef = RegionAllocator<uint32_t>::Ref_Undef;

class ClauseAllocator : public RegionAllocator<uint32_t>
{
    static int clauseWord32Size(int size, bool has_extra, bool has_uid){
        return (sizeof(Clause) + (sizeof(Lit) * (size + (int)has_extra + (int)has_uid))) / sizeof(uint32_t); }
 public:
    bool extra_clause_field;

    ClauseAllocator(uint32_t start_cap) : RegionAllocator<uint32_t>(start_cap), extra_clause_field(false){}
    ClauseAllocator() : extra_clause_field(false){}

    void moveTo(ClauseAllocator& to){
        to.extra_clause_field = extra_clause_field;
        RegionAllocator<uint32_t>::moveTo(to); 
	}

    template<class Lits>
    CRef alloc(const Lits& ps, bool learnt = false, bool ic = false,bool hasUid=false) {
        assert(sizeof(Lit)      == sizeof(uint32_t));
        assert(sizeof(float)    == sizeof(uint32_t));
        bool has_extra = learnt | extra_clause_field;
		bool has_uid = ic | hasUid;
		
		CRef newCr = RegionAllocator<uint32_t>::alloc(clauseWord32Size(ps.size(), has_extra, has_uid));
        new (lea(newCr)) Clause(ps, has_extra, learnt, ic, has_uid);
        return newCr;
    }

    // Deref, Load Effective Address (LEA), Inverse of LEA (AEL):
    Clause&       operator[](Ref r)       { return (Clause&)RegionAllocator<uint32_t>::operator[](r); }
    const Clause& operator[](Ref r) const { return (Clause&)RegionAllocator<uint32_t>::operator[](r); }
    Clause*       lea       (Ref r)       { return (Clause*)RegionAllocator<uint32_t>::lea(r); }
    const Clause* lea       (Ref r) const { return (Clause*)RegionAllocator<uint32_t>::lea(r); }
    Ref           ael       (const Clause* t){ return RegionAllocator<uint32_t>::ael((uint32_t*)t); }

    void free(CRef cid)
    {
        Clause& c = operator[](cid);
		//bool has_uid = c.ic();
		//bool has_uid = c.ic() || c.isParentToIc();
		bool has_uid = true;
        RegionAllocator<uint32_t>::free(clauseWord32Size(c.size(), c.has_extra(), has_uid));
    }

    void reloc(CRef& cr, ClauseAllocator& to) {
        Clause& c = operator[](cr);
		CRef prevCr = cr;

        if (c.reloced()) { cr = c.relocation(); return; }     
        cr = to.alloc(c, c.learnt(), c.ic() ,c.hasUid());
		
		c.relocate(cr);
        
        // Copy extra data-fields: 
        // (This could be cleaned-up. Generalize Clause-constructor to be applicable here instead?)
		Clause& newC = to[cr];
		newC.mark(c.mark());
        if (newC.learnt())
			newC.activity() = c.activity();
        else if (newC.has_extra())
			newC.calcAbstraction();
        
		if (newC.hasUid()) {
            // we don't want to increase uid here
			Clause::DecreaseUid();
			newC.uid() = c.uid();
        }
    }
	void relocWithUid(CRef& cr, ClauseAllocator& to,Uid uid) {
		Clause& c = operator[](cr);
		if (c.reloced()) { 
			assert(to[c.relocation()].uid() == uid);
			cr = c.relocation(); return; 
		}
		assert(!c.ic() && !c.hasUid());
		cr = to.alloc(c, c.learnt(), c.ic(),true);
		c.relocate(cr);
		// Copy extra data-fields: 
		// (This could be cleaned-up. Generalize Clause-constructor to be applicable here instead?)
		Clause& newC = to[cr];
		newC.mark(c.mark());
		if (newC.learnt())
			newC.activity() = c.activity();
		else if (newC.has_extra())
			newC.calcAbstraction();
		newC.uid() = uid;
		Clause::DecreaseUid();
	}
};


//=================================================================================================
// OccLists -- a class for maintaining occurence lists with lazy deletion:

template<class Idx, class Vec, class Deleted>
class OccLists
{
    vec<Vec>  occs;
    vec<char> dirty;
    vec<Idx>  dirties;
    Deleted   deleted;

 public:
    OccLists(const Deleted& d) : deleted(d) {}
    
    void  init      (const Idx& idx){ occs.growTo(toInt(idx)+1); dirty.growTo(toInt(idx)+1, 0); }
    // Vec&  operator[](const Idx& idx){ return occs[toInt(idx)]; }
    Vec&  operator[](const Idx& idx){ 
		return occs[toInt(idx)]; 
	}
    Vec&  lookup    (const Idx& idx){ 
		if (dirty[toInt(idx)]) 
			clean(idx); 
		return occs[toInt(idx)]; 
	}

    void  cleanAll  ();
    void  clean     (const Idx& idx);
    void  smudge    (const Idx& idx){
        if (dirty[toInt(idx)] == 0){
            dirty[toInt(idx)] = 1;
            dirties.push(idx);
        }
    }

    void  clear(bool free = true){
        occs   .clear(free);
        dirty  .clear(free);
        dirties.clear(free);
    }
};


template<class Idx, class Vec, class Deleted>
void OccLists<Idx,Vec,Deleted>::cleanAll()
{
    for (int i = 0; i < dirties.size(); i++)
        // Dirties may contain duplicates so check here if a variable is already cleaned:
        if (dirty[toInt(dirties[i])])
            clean(dirties[i]);
    dirties.clear();
}


template<class Idx, class Vec, class Deleted>
void OccLists<Idx,Vec,Deleted>::clean(const Idx& idx)
{
    Vec& vec = occs[toInt(idx)];
    int  i, j;
	for (i = j = 0; i < vec.size(); i++) {
		bool isDeleted = deleted.operator()((vec[i]));
        if (!isDeleted)
            vec[j++] = vec[i];
	}
    vec.shrink(i - j);
    dirty[toInt(idx)] = 0;
}


//=================================================================================================
// CMap -- a class for mapping clauses to values:


template<class T>
class CMap
{
    struct CRefHash {
        uint32_t operator()(CRef cr) const { return (uint32_t)cr; } };

    typedef Map<CRef, T, CRefHash> HashTable;
    HashTable map;
        
 public:
    // Size-operations:
    void     clear       ()                           { map.clear(); }
    int      size        ()                const      { return map.elems(); }

    
    // Insert/Remove/Test mapping:
    void     insert      (CRef cr, const T& t){ map.insert(cr, t); }
    void     growTo      (CRef cr, const T& t){ map.insert(cr, t); } // NOTE: for compatibility
    void     remove      (CRef cr)            { map.remove(cr); }
    bool     has         (CRef cr, T& t)      { return map.peek(cr, t); }

    // Vector interface (the clause 'c' must already exist):
    const T& operator [] (CRef cr) const      { return map[cr]; }
    T&       operator [] (CRef cr)            { return map[cr]; }

    // Iteration (not transparent at all at the moment):
    int  bucket_count() const { return map.bucket_count(); }
    const vec<typename HashTable::Pair>& bucket(int i) const { return map.bucket(i); }

    // Move contents to other map:
    void moveTo(CMap& other){ map.moveTo(other.map); }

    // TMP debug:
    void debug(){
        printf(" --- size = %d, bucket_count = %d\n", size(), map.bucket_count()); }
};


/*_________________________________________________________________________________________________
|
|  subsumes : (other : const Clause&)  ->  Lit
|  
|  Description:
|       Checks if clause subsumes 'other', and at the same time, if it can be used to simplify 'other'
|       by subsumption resolution.
|  
|    Result:
|       lit_Error  - No subsumption or simplification
|       lit_Undef  - Clause subsumes 'other'
|       p          - The literal p can be deleted from 'other'
|________________________________________________________________________________________________@*/
inline Lit Clause::subsumes(const Clause& other) const
{
    //if (other.size() < size() || (extra.abst & ~other.extra.abst) != 0)
    //if (other.size() < size() || (!learnt() && !other.learnt() && (extra.abst & ~other.extra.abst) != 0))
    assert(!header.learnt);   assert(!other.header.learnt);
    assert(header.has_extra); assert(other.header.has_extra);
    if (other.header.size < header.size || (data[header.size].abs & ~other.data[other.header.size].abs) != 0)
        return lit_Error;

    Lit        ret = lit_Undef;
    const Lit* c   = (const Lit*)(*this);
    const Lit* d   = (const Lit*)other;

    for (unsigned i = 0; i < header.size; i++) {
        // search for c[i] or ~c[i]
        for (unsigned j = 0; j < other.header.size; j++)
            if (c[i] == d[j])
                goto ok;
            else if (ret == lit_Undef && c[i] == ~d[j]){
                ret = c[i];
                goto ok;
            }

        // did not find it
        return lit_Error;
    ok:;
    }

    return ret;
}

inline void Clause::strengthen(Lit p)
{
    remove(*this, p);
    calcAbstraction();
}

//=================================================================================================
class ResolutionException : public std::exception {
public:
	ResolutionException(const char* msg) : std::exception(msg) {}
};
}


#endif
