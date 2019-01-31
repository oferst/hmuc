#pragma once
#include "mtl/Vec.h"

#include "core/SolverTypes.h"
#include "core/ResolutionGraph.h"

namespace Minisat {
	class DelayedResolGraphAlloc {

	public:
		struct allocJob {
			ClauseAllocator* caPtr;
			//Clause* c;
			CRef cref;
			bool isIc;
			bool hasUid;
			allocJob(ClauseAllocator* _caPtr, CRef _cref, bool _isIc, bool _hasUid) :
				caPtr(_caPtr), cref(_cref), isIc(_isIc), hasUid(_hasUid) {}
			
		};
		CResolutionGraph* g;
		vec<allocJob> jobs;
		int firstIc;
		std::unordered_map<CRef, Uid>& uidDeferredAlloc;

		DelayedResolGraphAlloc(CResolutionGraph* _g, std::unordered_map<CRef, Uid>& uidDefferedAlloc);
		void addJob(ClauseAllocator* caPtr, CRef cref);
		void shrink(int numToCancel);
		int size();
		void clear();
		void executeJobs(vec<Uid>& nonIcParents, vec<Uid>& allParents);

	};
}