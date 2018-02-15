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

typedef uint32_t word_t;
typedef char bit_t;
typedef uint32_t wordPos_t;
//Stores bit in an array of 32-bit words, later bit are added first as new MSB and then (every 32 bits) to the next word in the 32-bit word array.
//This is just an interface for easy bit array access and manipulation (including iteration),
//i.e., DOESN'T ALLOCATE the word_t array itself! - user (yes, you) has to manage his own memory.
struct BitArray {
	word_t *words;
	//the next free to write bit in the array
	uint32_t currBitIdx;
	uint32_t numWordsUsed;
	bool debug;

	//Initiates the bit array metadata, doesn't do memcopy - assumes that _words is an allocated array and was filled with _nbits of data already
	BitArray(word_t *_words, uint32_t _nbits=0, bool _debug = false) :
		words(_words), 
		currBitIdx(_nbits & 0x1f),
		numWordsUsed((_nbits >> 5) + (uint32_t)(0 != currBitIdx)),
		debug(_debug) {}
	BitArray& operator=(const BitArray other) {
		words = other.words;
		currBitIdx = other.currBitIdx;
		numWordsUsed = other.numWordsUsed;
		return *this;
	}
	//Adds b as the MSB bit in the array
	void addBitMSB(bit_t b) {
		if (0 == currBitIdx)
			words[numWordsUsed++] = b & 1;
		else {
			uint32_t currWordIdx = numWordsUsed - 1;
			words[currWordIdx] = (words[currWordIdx] | ((b & 1) << currBitIdx));
			//note that 'bitwise or' will be correct here because the current word (in words[currWordIdx]) is initiated to '(0^31)1'
		}
		if (32 == ++currBitIdx)
			currBitIdx = 0;
	}

	const uint32_t size() const {
		return ((numWordsUsed - (bool)(currBitIdx)) << 5) + currBitIdx;
	}
};






//=================================================================================================
}

#endif
