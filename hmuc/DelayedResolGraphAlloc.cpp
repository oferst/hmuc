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
	Uid nextUid = Clause::GetNextUid();
	for (auto& job : jobs) {
		Clause& c = *job.c;
		CRef cref = job.cref;

		Uid uid = CRef_Undef;

		if (job.hasUid)
			//if clause has a Uid (allocated internally in the Clause object), then it also has a node in the graph, don't allocate a new node.
			uid = c.uid();
		else if (uidDeferredAlloc.find(cref) != uidDeferredAlloc.end()){
			//if clause has a Uid (allocated externally to the Clause object), then it also has a node in the graph, don't allocate a new node.
			assert(!c.ic());
			uid = uidDeferredAlloc[cref];
		}

		if (uid != CRef_Undef && RRef_Undef == g->GetResolRef(uid)) {
			g->AddRemainderResolution(uid, cref);
			assert(RRef_Undef != g->GetResolRef(uid));
		}
		if(uid == CRef_Undef){//otherwise, the clause has no Uid, allocate it a node in the graph now, and allocate it a Uid (externally). 
			assert(!c.ic());
			uid = nextUid++;
			//Clause::SetNextUid(uid);
			g->AddRemainderResolution(uid, cref);
			uidDeferredAlloc[cref] = uid;
		}

		if (!job.isIc)
			nonIcParents.push(uid);
		
		allParents.push(uid);
	}
	Clause::SetNextUid(nextUid);
}
