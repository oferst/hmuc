#pragma once
#include "gmock/gmock.h"
#include "RebuilderContext.h"
namespace Minisat {
	class MockRebuilderContext : public RebuilderContext {
	public:
		MockRebuilderContext() : RebuilderContext() {}
		MOCK_METHOD0(clearUpdates, void());
		MOCK_METHOD1(getClause, LitSet&(Uid uid));
		MOCK_METHOD1(getClausesUpdate, Uid(Uid oldUid));
		MOCK_METHOD1(getPivots, vec<Lit>&(Uid uid));
		MOCK_METHOD1(isClauseSeen, bool(Uid uid));
		MOCK_METHOD1(isClauseUpdated, bool(Uid oldUid));
		MOCK_METHOD1(arePivotsKnown, bool(Uid uid));
		MOCK_METHOD2(mapClausesUpdate, void(Uid oldUid, Uid newUid));

	};

}