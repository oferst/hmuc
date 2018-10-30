#include "DelayedResolGraphAlloc.h"

#include "Printer.h"

using namespace Minisat;
DelayedResolGraphAlloc::DelayedResolGraphAlloc(CResolutionGraph* _g, std::unordered_map<CRef, Uid>& _uidDefferedAlloc) : g(_g),uidDeferredAlloc(_uidDefferedAlloc),firstIc(-1){}
void DelayedResolGraphAlloc::addJob(Clause& c, CRef cref) {
	if (firstIc == -1 && c.ic())
		firstIc = jobs.size();
	jobs.push(allocJob(&c,cref,c.ic(),c.hasUid()));
}
void DelayedResolGraphAlloc::shrink(int numToCancel) {
	jobs.shrink(numToCancel);
	if (jobs.size() <= firstIc)
		firstIc = -1;
	
}
int DelayedResolGraphAlloc::size() {
	return jobs.size();
}
void DelayedResolGraphAlloc::clear() {
	jobs.clear();
	firstIc = -1;
}
void DelayedResolGraphAlloc::executeJobs(vec<Uid>& nonIcParents, vec<Uid>& allParents) {
	assert(nonIcParents.size() == 0 && allParents.size() == 0);

	
	assert(firstIc >= 0);
	//Uid nextUid = Clause::GetNextUid();
	
		//for (auto& job : jobs) {
		//	Clause& c = *job.c;
		//	CRef cref = job.cref;
		//	Uid uid;
		//	if (job.hasUid)//if it is an ic clause than it must have a uid
		//		uid = c.uid();
		//	else if (uidDeferredAlloc.find(cref) != uidDeferredAlloc.end()) {
		//		assert(c.isParentToIc());
		//		uid = uidDeferredAlloc[cref];
		//	}
		//	else {//it is a new clause which is not allocated in the graph, and it is a parent to an ic clause - allocate it now
		//		assert(!c.isParentToIc());
		//		uid = nextUid++;
		//	}
		////printf("uid: %u, %d\n", uid, c.ic());
		////printClause(c, "uid " + std::to_string(uid) + " ic? " + std::to_string(c.ic()));
		//}
		////printf("-----------\n");

	Uid nextUid = Clause::GetNextUid();
	for (auto& job : jobs) {
		Clause& c = *job.c;
		CRef cref = job.cref;
		Uid uid;

		if (job.hasUid)//if it is an ic clause than it must have a uid
			uid = c.uid();
		else if (uidDeferredAlloc.find(cref) != uidDeferredAlloc.end()) {
			assert(c.isParentToIc());
			uid = uidDeferredAlloc[cref];
		}
		else {//it is a new clause which is not allocated in the graph, and it is a parent to an ic clause - allocate it now
			assert(!c.isParentToIc());
			uid = nextUid++;
			c.setIsParentToIc(true);
			g->AddRemainderResolution(uid, cref);
			uidDeferredAlloc[cref] = uid;
		}

		if (!job.isIc)
			nonIcParents.push(uid);
		allParents.push(uid);
	}
	Clause::SetNextUid(nextUid);
}
