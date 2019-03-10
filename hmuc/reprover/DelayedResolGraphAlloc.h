#pragma once
#include "mtl/Vec.h"
#include <list>
#include "core/SolverTypes.h"
#include "core/ResolutionGraph.h"

namespace Minisat {
	class DelayedResolGraphAlloc {

	public:
		struct allocJob {
			ClauseAllocator* caPtr;
			CRef cref;
			bool isIc;
			bool hasUid;
			allocJob(ClauseAllocator* _caPtr, CRef _cref, bool _isIc, bool _hasUid) :
				caPtr(_caPtr), cref(_cref), isIc(_isIc), hasUid(_hasUid) {}
			allocJob() :allocJob(NULL,CRef_Undef,false,false){}
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