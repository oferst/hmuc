#include "RebuilderContext.h"

namespace Minisat {



	LitSet& RebuilderContext::getClauseLits(Uid uid) {
		return seenClauses[uid];
	}


	Uid RebuilderContext::getClausesUpdate(Uid oldUid) {
		return clausesUpdates[oldUid];
	}
	void RebuilderContext::setClausesUpdate(Uid oldUid,Uid newUid) {
		clausesUpdates[oldUid]= newUid;
	}
	
	vec<Lit>& RebuilderContext::getPivots(Uid uid) {
		return seenPivots[uid];
	}

	bool& RebuilderContext::isIc(Uid uid) {
		return areIcs[uid];
	}

	
	void RebuilderContext::clearUpdates() {
		clausesUpdates.clear();
		//seenPivots.clear();
		//seenClauses.clear();
		//areIcs.clear();
		

	}


	bool RebuilderContext::isClauseSeen(Uid uid) {
		return seenClauses.find(uid) != seenClauses.end();
	}
	bool RebuilderContext::arePivotsKnown(Uid uid) {
		return  seenPivots.find(uid) != seenPivots.end();
	}
	bool RebuilderContext::isClauseUpdated(Uid oldUid) {
		return clausesUpdates.find(oldUid) != clausesUpdates.end();
	}

}