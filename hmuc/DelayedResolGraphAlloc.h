#pragma once
#include "mtl/Vec.h"

#include "core/SolverTypes.h"
#include "core/ResolutionGraph.h"

namespace Minisat {
	class DelayedResolGraphAlloc {

	public:
		struct allocJob {
			Clause* c;
			CRef cref;
			bool isIc;
			bool hasUid;
			allocJob(Clause* _c, CRef _cref, bool _isIc, bool _hasUid) :
				c(_c), cref(_cref), isIc(_isIc), hasUid(_hasUid) {}
			
		};
		CResolutionGraph* g;
		vec<allocJob> jobs;
		int firstIc;
		std::unordered_map<CRef, Uid>& uidDeferredAlloc;

		DelayedResolGraphAlloc(CResolutionGraph* _g, std::unordered_map<CRef, Uid>& uidDefferedAlloc);
		void addJob(Clause& c, CRef cref);
		void shrink(int numToCancel);
		int size();
		void clear();
		void executeJobs(vec<Uid>& nonIcParents, vec<Uid>& allParents);

	};
}