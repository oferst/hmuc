#include "RebuilderContext.h"

namespace Minisat {

	//RebuilderContext::RebuilderContext(){}


	//RebuilderContext::~RebuilderContext(){}


	bool RebuilderContext::isClauseSeen(Uid uid) {
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
	Uid RebuilderContext::getClausesUpdate(Uid oldUid) {
		return clausesUpdates[oldUid];
	}
	bool RebuilderContext::isClauseUpdated(Uid oldUid) {
		return clausesUpdates.find(oldUid) != clausesUpdates.end();
	}
	void RebuilderContext::clearUpdates() {
		clausesUpdates.clear();
	}
}