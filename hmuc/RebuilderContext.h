#pragma once
#include "SolverHandle.h"
namespace Minisat {
	class RebuilderContext
	{
		//This map will contain all the pivotsMap for nodes that will be visited in the backwards traversal,
		//every 'key' is the uid of a node, and it maps to a vector of literals - each literal is a pivot 
		//between two consecutive parents of the node 'key'. Every pivot should be a member of the 'currParentUid'
		//parent (higher index), and the negation of the pivot will belong to the 'left' parent.
		UidToLitVec seenPivots;

		//This map will contain all the literals for clauses that are parents of clauses in c's rhombus, and that
		//were visited during the current proof reconstruction context
		UidToLitSet seenClauses;

		//will contain a mapping between an old, unreconstructed clause uid, and the uid of it's updated version.
		UidToUid clausesUpdates;

	public:
		const Lit dummy = mkLit(var_Undef);

		RebuilderContext() {}
		virtual ~RebuilderContext() {}

		virtual LitSet&			getClause(Uid uid);
		virtual Uid				getClausesUpdate(Uid oldUid);
		virtual vec<Lit>&		getPivots(Uid uid);
		
		virtual void			mapClausesUpdate(Uid oldUid, Uid newUid);
		virtual void			clearUpdates();

		virtual bool			isClauseSeen(Uid uid);
		virtual bool			isClauseUpdated(Uid oldUid);
		virtual bool			arePivotsKnown(Uid uid);
	};

}