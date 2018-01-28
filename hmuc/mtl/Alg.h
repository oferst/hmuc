/*******************************************************************************************[Alg.h]
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

#ifndef Minisat_Alg_h
#define Minisat_Alg_h

#include "mtl/Vec.h"

namespace Minisat {
#define MIN_MASK 1
#define MAX_MASK 0x80000000
//=================================================================================================
// Useful functions on vector-like types:

//=================================================================================================
// Removing and searching for elements:
//

template<class V, class T>
static inline void remove(V& ts, const T& t)
{
    int j = 0;
    for (; j < ts.size() && ts[j] != t; j++);
    assert(j < ts.size());
    for (; j < ts.size()-1; j++) ts[j] = ts[j+1];
    ts.pop();
}


template<class V, class T>
static inline bool find(V& ts, const T& t)
{
    int j = 0;
    for (; j < ts.size() && ts[j] != t; j++);
    return j < ts.size();
}


//=================================================================================================
// Copying vectors with support for nested vector types:
//

// Base case:
template<class T>
static inline void copy(const T& from, T& to)
{
    to = from;
}

// Recursive case:
template<class T>
static inline void copy(const vec<T>& from, vec<T>& to, bool append = false)
{
    if (!append)
        to.clear();
    for (int i = 0; i < from.size(); i++){
        to.push();
        copy(from[i], to.last());
    }
}

template<class A, class B, class C>
static inline void union_vec(A& a, B& b, C& union_)
{
    union_.clear();
    int b_itr = 0 ,a_itr = 0,i;
    while (true)
    {	
        if (a_itr==a.size()) 
        {
            for(i=b_itr;i<b.size();i++)
            {
                union_.push(b[i]);
            }
            break;
        }
        if (b_itr==b.size()) 
        {
            for(i=a_itr;i<a.size();i++)
            {
                union_.push(a[i]);
            }
            break;
        }
        if (a[a_itr]<b[b_itr]) 
        { 
            union_.push(a[a_itr]);
            a_itr++;
        }
        else if (b[b_itr]<a[a_itr]) 
        { 
            union_.push(b[b_itr]);
            b_itr++;
        }
        else 
        { 
            union_.push(a[a_itr]); 
            a_itr++;
            b_itr++;
        }
    }
    return;
}


template <class A, class B>
static inline bool Contains(A& a, B& b)   // true <-> a contains b   // not tested yet.
{
    int b_itr = 0 ,a_itr = 0;
	int gap = a.size() - b.size();
    while (a_itr!=a.size() && b_itr!=b.size())  
    {
		if (a[a_itr]<b[b_itr]) {++a_itr; if (gap-- == 0) return false; }
        else if (b[b_itr]<a[a_itr]) return false;
        else {            
            ++a_itr;
            ++b_itr;
        }
    }
    return b_itr == b.size();			
}



template <class A, class B, class C>
static inline void Diff(A& a, B& b, C& diff)   // diff = a - b   // not tested yet.
{
    int b_itr = 0 ,a_itr = 0;
    while (a_itr!=a.size() && b_itr!=b.size())  
    {
		if (a[a_itr]<b[b_itr]) {diff.push(a[a_itr]); ++a_itr;}
        else if (b[b_itr]<a[a_itr]) ++b_itr;
        else {            
            ++a_itr;
            ++b_itr;
        }
    }
    return;			
}

template <class S, class T>
static inline void replaceContent(S& toReplace, T& with) {
	toReplace.clear();
	for (auto l : with)
		toReplace.insert(l);
}
template <class S, class T>
static inline void replaceVecContent(S& toReplace, T& with) {
	toReplace.clear();
	for (auto l : with)
		toReplace.push(l);
}
template <class S, class T, class U>
static inline void unionContnet(S& a, T& b, U& res) {
	res.clear();
	for (auto l : a)
		res.insert(l);
	for (auto l : b)
		res.insert(l);
}

template <class A, class B, class C>
static inline void Intersection(A& a, B& b, C& intersection)
{
    int b_itr = 0 ,a_itr = 0;
    while (a_itr!=a.size() && b_itr!=b.size())  //intersection
    {
        if (a[a_itr]<b[b_itr]) ++a_itr;
        else if (b[b_itr]<a[a_itr]) ++b_itr;
        else {
            intersection.push(a[a_itr]);
            ++a_itr;
            ++b_itr;
        }
    }
    return;			
}

template<class T>
static inline void append(const vec<T>& from, vec<T>& to){ copy(from, to, true); }


template <class A, class B, class C>
static inline bool empty_intersection(A& a, B& b)  // true if empty
{
	int b_itr = 0 ,a_itr = 0;
	while (a_itr!=a.size() && b_itr!=b.size())  
	{
		if (a[a_itr]<b[b_itr]) ++a_itr;
		else if (b[b_itr]<a[a_itr]) ++b_itr;
		else return false;
	}
	return true;			
}

template<class A, class B>
static inline void insertAll(A& from, B& to) {
	for (int i = 0; i < from.size(); ++i)
		to.insert(from[i]);
}
//static uint32_t rev32Bits(uint32_t n) {
//	n = (n >> 1) & 0x55555555 | (n << 1) & 0xaaaaaaaa;
//	n = (n >> 2) & 0x33333333 | (n << 2) & 0xcccccccc;
//	n = (n >> 4) & 0x0f0f0f0f | (n << 4) & 0xf0f0f0f0;
//	n = (n >> 8) & 0x00ff00ff | (n << 8) & 0xff00ff00;
//	n = (n >> 16) & 0x0000ffff | (n << 16) & 0xffff0000;
//	return n;
//}


typedef uint32_t word_t;
typedef char bit_t;
typedef uint32_t wordPos_t;
//Stores bit in an array of 32-bit words, later bit are added first as new MSB and then (every 32 bits) to the next word in the 32-bit word array.
//This is just an interface for easy bit array access and manipulation (including iteration),
//i.e., DOESN'T ALLOCATE the word_t array itself! - user (yes, you) has to manage his own memory.
//struct BiIterBitArr;
struct BitArray {
	word_t *words;
	uint32_t curr_free_idx, n_words_used;
	bool debug;

	//Initiates the bit array metadata, doesn't do memcopy - assumes that _words is an allocated array and was filled with _nbits of data already
	BitArray(word_t *_words, uint32_t _nbits=0, bool _debug = false) :
		words(_words), 
		curr_free_idx(_nbits & 0x1f),
		n_words_used((_nbits >> 5) + (uint32_t)(0 != curr_free_idx)),
		debug(_debug) {}
	BitArray& operator=(const BitArray other) {
		words = other.words;
		curr_free_idx = other.curr_free_idx;
		n_words_used = other.n_words_used;
		return *this;
	}
	////Simple forward iterator for BitArray 
	//struct IterBitArr {
	//	const BitArray& ba;
	//	word_t currWord;
	//	int currWordIdx;
	//	int currOffset;
	//	IterBitArr(const BitArray& _ba, uint32_t _pos = 0) : ba(_ba) {
	//		if (0 > _pos || _pos > (ba.size())) {
	//			currWordIdx = currOffset = -1;
	//		}
	//		else {
	//			currWordIdx = _pos >> 5;
	//			currOffset = _pos & 0x1f;
	//		}
	//		if (0 <= currOffset)
	//			currWord = ba.words[currWordIdx] >> currOffset;
	//	}
	//	bool operator!=(const IterBitArr& other) {
	//		return (&ba != &other.ba) || (currOffset != other.currOffset) || (currWordIdx != other.currWordIdx);
	//	}
	//	const IterBitArr& operator++() {
	//		if (0 <= currOffset) {
	//			assert(0 <= currWordIdx);
	//			if (((++currOffset) & 0x1f) == 0) {
	//				currWord = ba.words[++currWordIdx];
	//				currOffset = 0;
	//			}
	//			else
	//				currWord = currWord >> 1;
	//		}
	//		return *this;
	//	}
	//	const uint32_t& operator*() const {
	//		assert((0 <= currOffset) && (0 <= currWordIdx) && (((currWordIdx >> 5) + currOffset) < ba->size()));
	//		return currWord & 1;
	//	}

	//};

	//Bi-directional iterator for BitArray
	//struct BiIterBitArr {
	//	BitArray& ba;
	//	int maxSize;
	//	int pos;
	//	uint32_t word;
	//	uint32_t mask;
	//	BiIterBitArr(): ba(BitArray(NULL)), maxSize(0), pos(-1){

	//	}
	//	BiIterBitArr(BitArray& _ba, uint32_t _pos = 0) : ba(_ba), maxSize(_ba.size()), pos(_pos){
	//		if (0 <= pos && pos < maxSize) {
	//			word = (_ba.words[_pos / 32]);
	//			mask = (1 << (_pos % 32));
	//		}
	//	}
	//	bool operator!=(const BiIterBitArr& other) {
	//		return (ba.words != (other.ba.words)) || (pos != other.pos);
	//	}
	//	BiIterBitArr& operator++() {
	//		pos++;
	//		if (0 <= pos && pos < maxSize) {
	//			if (MAX_MASK == mask) {
	//				mask = MIN_MASK;
	//				word = ba.words[pos / 32];
	//			}
	//			else {
	//				mask = mask << 1;
	//			}
	//		}
	//		else 
	//			pos = maxSize;
	//		return *this;
	//	}
	//	BiIterBitArr& operator--() {
	//		pos--;
	//		if (0 <= pos && pos < maxSize) {
	//			if (MIN_MASK == mask) {
	//				mask = MAX_MASK;
	//				word = ba.words[pos / 32];
	//			}
	//			else {
	//				mask = mask >> 1;
	//			}
	//		}
	//		else 
	//			pos = -1;
	//		return *this;
	//	}

	//	const uint32_t operator*() const {
	//		return (0 != (word & mask));
	//	}

	//	BiIterBitArr& operator=(const BiIterBitArr other) {
	//		ba = other.ba;
	//		maxSize = other.maxSize;
	//		pos = other.pos;
	//		word = other.word;
	//		mask = other.mask;

	//	}
	//};
	//word_t getWord(wordPos_t i) {
	//	assert(0 <= i && i < n_words_used-1);
	//	return words[i];
	//}

	//Adds b as the MSB bit in the array
	void addBitMSB(bit_t b) {
		if (0 == curr_free_idx)
			words[n_words_used++] = b & 1;
		else {
			uint32_t wIdx = n_words_used - 1;
			words[wIdx] = (words[wIdx] | ((b & 1) << curr_free_idx));
		}
		if (32 == ++curr_free_idx)
			curr_free_idx = 0;
	}

	const uint32_t size() const {
		return ((n_words_used - (bool)(curr_free_idx)) << 5) + curr_free_idx;
	}
	//BiIterBitArr begin() {
	//	return BiIterBitArr(*this);
	//}
	////const BiIterBitArr begin() const {
	////	return BiIterBitArr(*this);
	////}
	//BiIterBitArr end() {
	//	return BiIterBitArr(*this, size());
	//}
	////const BiIterBitArr end() const {
	////	return BiIterBitArr(*this, size());
	////}
};






//=================================================================================================
}

#endif
