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

//=================================================================================================
}

#endif
