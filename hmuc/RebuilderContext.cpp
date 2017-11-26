#include "RebuilderContext.h"

namespace Minisat {

	RebuilderContext::RebuilderContext(){}


	RebuilderContext::~RebuilderContext(){}


	bool RebuilderContext::seenClause(Uid uid) {
		return seenClauses.find(uid) != seenClauses.end();
	}
	LitSet& RebuilderContext::getClause(Uid uid) {
		return seenClauses[uid];
	}
	vec<Lit>& RebuilderContext::getPivots(Uid uid) {
		return seenPivots[uid];
	}
	bool RebuilderContext::arePivotsKnown(Uid uid) {
		return seenPivots.find(uid) != seenPivots.end();
	}
	void RebuilderContext::mapClausesUpdate(Uid oldUid, Uid newUid) {
		clausesUpdates[oldUid] = newUid;
	}
	Uid RebuilderContext::getNewClauseUid(Uid oldUid) {
		return clausesUpdates[oldUid];
	}
	bool RebuilderContext::clasueUpdated(Uid oldUid) {
		return clausesUpdates.find(oldUid) != clausesUpdates.end();
	}
}