/*******************************************************************************************[Vec.h]
Copyright (c) 2003-2007, Niklas Een, Niklas Sorensson
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

#ifndef Minisat_Vec_h
#define Minisat_Vec_h

#include <assert.h>
#include <new>
#include <stdio.h>
#include <iterator>
#include "mtl/IntTypes.h"
#include "mtl/XAlloc.h"

namespace Minisat {

//=================================================================================================
// Automatically resizable arrays
//
// NOTE! Don't use this vector on datatypes that cannot be re-located in memory (with realloc)
template<class T>
	class Iter;

template<class T>
class vec {
    T*  data;
    int sz;
    int cap;
	typedef Iter<T>  iterator;
	typedef Iter<const T>  const_iterator;

    // Helpers for calculating next capacity:
    static inline int  imax   (int x, int y) { int mask = (y-x) >> (sizeof(int)*8-1); return (x&mask) + (y&(~mask)); }
    //static inline void nextCap(int& cap){ cap += ((cap >> 1) + 2) & ~1; }
    static inline void nextCap(int& cap){ cap += ((cap >> 1) + 2) & ~1; }

public:
    // Constructors:
    vec()                       : data(NULL) , sz(0)   , cap(0)    { }
    explicit vec(int size)      : data(NULL) , sz(0)   , cap(0)    { growTo(size); }
    vec(int size, const T& pad) : data(NULL) , sz(0)   , cap(0)    { growTo(size, pad); }
   ~vec()                                                          { clear(true); }

    // Pointer to first element:
    operator T*       (void)           { return data; }

	//oferg: Iter operations
	iterator begin() { return iterator(&data[0]); }
	const_iterator begin() const { return const_iterator(&data[0]); }
	iterator end() { return iterator(&data[sz - 1]); };
	const_iterator end() const { return const_iterator(&data[sz - 1]); }

    // Size operations:
    int      size     (void) const     { return sz; }
    void     shrink   (int nelems)     { assert(nelems <= sz); for (int i = 0; i < nelems; i++) sz--, data[sz].~T(); }
    void     shrink_  (int nelems)     { assert(nelems <= sz); sz -= nelems; }
    int      capacity (void) const     { return cap; }
    void     capacity (int min_cap);
    void     growTo   (int size);
    void     growTo   (int size, const T& pad);
    void     clear    (bool dealloc = false);

    // Stack interface:
    void     push  (void)              { if (sz == cap) capacity(sz+1); new (&data[sz]) T(); sz++; }
    void     push  (const T& elem)     { if (sz == cap) capacity(sz+1); data[sz++] = elem; }
    void     push_ (const T& elem)     { assert(sz < cap); data[sz++] = elem; }
    void     pop   (void)              { assert(sz > 0); sz--, data[sz].~T(); }
    // NOTE: it seems possible that overflow can happen in the 'sz+1' expression of 'push()', but
    // in fact it can not since it requires that 'cap' is equal to INT_MAX. This in turn can not
    // happen given the way capacities are calculated (below). Essentially, all capacities are
    // even, but INT_MAX is odd.

    const T& last  (void) const        { return data[sz-1]; }
    T&       last  (void)              { return data[sz-1]; }

    // Vector interface:
    const T& operator [] (int index) const { return data[index]; }
    T&       operator [] (int index)       { return data[index]; }

    // Duplicatation (preferred instead):
    void copyTo(vec<T>& copy) const { copy.clear(); copy.growTo(sz); for (int i = 0; i < sz; i++) copy[i] = data[i]; }
    void addTo(vec<T>& dest) const 
    { 
        int size = dest.size();
        dest.growTo(size + sz); 
        for (int i = 0; i < sz; i++) 
            dest[size + i] = data[i]; 
    }

    void moveTo(vec<T>& dest) { dest.clear(true); dest.data = data; dest.sz = sz; dest.cap = cap; data = NULL; sz = 0; cap = 0; }

    // Don't Allow copying (error prone): -- CHANGED to allow
    vec<T>&  operator = (const vec<T>& other) { other.copyTo(*this); return *this; }
             vec<T>     (const vec<T>& other) { other.copyTo(*this); }


    // better than moveTo because keeps allocated memory
    void swap(vec<T>& other)
    {
        T*  tmpData = other.data;
        int tmpSz = other.sz;
        int tmpCap = other.cap;

        other.data = this->data;
        other.sz = this->sz;
        other.cap = this->cap;
        this->data = tmpData;
        this->sz = tmpSz;
        this->cap = tmpCap;
    }

    void removeDuplicated_()
    {
        sort(*this);
        int nNewInd = 0;
        int nOldInd = 1;
        for (; nOldInd < sz; ++nOldInd)
        {
            if (data[nNewInd] != data[nOldInd])
            {
                data[++nNewInd] = data[nOldInd];
            }
        }

        shrink_(nOldInd - nNewInd - 1);
    }

    void insert(int place, const T& elem)
    {
        push();
        for (int i = sz - 1; i > place; --i)
        {
            data[i] = data[i-1];
        }

        data[place] = elem;
    }
    
    void print()
    {
        printf("********************************\n");
        for (int i = 0; i < sz; ++i)
        {
            printf("%d ", data[i]);
        }
        printf("\n");

    }


	int lower_bound (const T& val) // ofer
	{
		int it, step, 
			first = 0, // searching from beginning
			count = sz - 1;	 // to end
		while (count>0)
		{
			it = first; step=count/2; it += step;
			if (data[it]<val) {                 
				first=++it;
				count-=step+1;
			}
			else count=step;
		}
		return first;
	}

	bool binary_search (const T& val) // ofer. Assumes object is sorted. 
	{		
		if (val < data[0]) return false;
		int first = lower_bound(val);
		return (data[first] == val);
	}

	bool search (const T& val) // ofer. does not assume object is sorted. 
	{				
		for (int i = 0; i < size(); ++i) 
			if (data[i] == val) 
				return true;
		return false;
	}


	int lower_bound_inc (const T& val, int first) // ofer
	{
		int it, step, 			
			count = sz;	 // to end
		while (count>0)
		{
			it = first; step=count/2; it += step;
			if (data[it]<val) {                 
				first=++it;
				count-=step+1;
			}
			else count=step;
		}
		return first;
	}

	bool binary_search_inc (const T& val, int& lb) // ofer. Assumes object is sorted. 
	{		
		if (val < data[0]) return false;
		lb = lower_bound(val);
		return (data[lb] == val);
	}

};




template<typename T>
static void printfVec(T& v, char *msg) {
	if (v == NULL) printf("NULL\n");
	printf("%s (", msg);	
	for (int i = 0; i < v.size(); ++i) {
		printf("%d ", v[i]);
	}
	printf(")\n");
}

template<class T>
void vec<T>::capacity(int min_cap) {
    if (cap >= min_cap) return;
    int add = imax((min_cap - cap + 1) & ~1, ((cap >> 1) + 2) & ~1);   // NOTE: grow by approximately 3/2
    if (add > INT_MAX - cap || ((data = (T*)::realloc(data, (cap += add) * sizeof(T))) == NULL) && errno == ENOMEM)
        throw OutOfMemoryException();
 }


template<class T>
void vec<T>::growTo(int size, const T& pad) {
    if (sz >= size) return;
    capacity(size);
    for (int i = sz; i < size; i++) data[i] = pad;
    sz = size; }


template<class T>
void vec<T>::growTo(int size) {
    if (sz >= size) return;
    capacity(size);
    for (int i = sz; i < size; i++) new (&data[i]) T();
    sz = size; }


template<class T>
void vec<T>::clear(bool dealloc) {
    if (data != NULL){
        for (int i = 0; i < sz; i++) data[i].~T();
        sz = 0;
        if (dealloc) free(data), data = NULL, cap = 0; } 
}

//=================================================================================================


template<typename T>
class Iter : public std::iterator<std::random_access_iterator_tag,T,ptrdiff_t,T*,T&>{
public:
	Iter(T* ptr = nullptr) { m_ptr = ptr; }
	Iter(const Iter<T>& rawIterator) = default;
	~Iter() {};
	Iter<T>& operator=(const Iter<T>& rawIterator) = default;
	Iter<T>& operator=(T* ptr) { m_ptr = ptr; return (*this); }
	operator bool() const {return (m_ptr!=Null);}
	bool operator==(const Iter<T>& rawIterator)const { return (m_ptr == rawIterator.getConstPtr()); }
	bool operator!=(const Iter<T>& rawIterator)const { return (m_ptr != rawIterator.getConstPtr()); }
	Iter<T>& operator+=(const ptrdiff_t& movement) { m_ptr += movement; return (*this); }
	Iter<T>& operator-=(const ptrdiff_t& movement) { m_ptr -= movement; return (*this); }
	Iter<T>& operator++() { ++m_ptr; return (*this); }
	Iter<T>& operator--() { --m_ptr; return (*this); }
	Iter<T> operator++(ptrdiff_t) { auto temp(*this); ++m_ptr; return temp; }
	Iter<T> operator--(ptrdiff_t) { auto temp(*this); --m_ptr; return temp; }
	Iter<T> operator+(const ptrdiff_t& movement) { auto oldPtr = m_ptr; m_ptr += movement; auto temp(*this); m_ptr = oldPtr; return temp; }
	Iter<T> operator-(const ptrdiff_t& movement) { auto oldPtr = m_ptr; m_ptr -= movement; auto temp(*this); m_ptr = oldPtr; return temp; }
	ptrdiff_t operator-(const Iter<T>& rawIterator) { return std::distance(rawIterator.getPtr(), this->getPtr()); };
	T&  operator*() { return *m_ptr; }
	const T& operator*()const { return *m_ptr; }
	T* operator->() { return m_ptr; }
	T* getPtr()const { return m_ptr; }
	const T* getConstPtr()const { return m_ptr; }

protected:
	T* m_ptr;
};


}

#endif

