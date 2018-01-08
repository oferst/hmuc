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

		UidLabel areIcs;


	public:
		const Lit dummy = mkLit(var_Undef);

		RebuilderContext() {}
		virtual ~RebuilderContext() {}

		/**********************************
			Mutators (set + get) methods 
			for the context database
		***********************************/
		//Mutator for the set of literals owned by uid.
		virtual LitSet&			getClauseLits(Uid uid);
		
		//Mutator for the oldUid's updated uid.
		virtual Uid&			getClausesUpdate(Uid oldUid);
		
		//Mutator for the set of pivots (literals) generating uid from it's parents.
		virtual vec<Lit>&		getPivots(Uid uid);
		
		//Mutator for the ic label associated with uid.
		virtual bool&			isIc(Uid uid);


		//Clears all updates between proving each backbone literal (BL)
		virtual void			clearUpdates();


		/**********************************
			boolean queries for the 
				context database
		***********************************/
		//If answers 'true' then clause's literals were already recorded
		virtual bool			isClauseSeen(Uid uid);
		//If answers 'true' then clause's then we finished finding an update to this clause during the reconstruction of this BL proof
		virtual bool			isClauseUpdated(Uid oldUid);
		//If answers 'true' then we visited this clause in this or previous proof iteration, at which point we already extracted the pivots necessary for the current (and future) reconstructions.
		virtual bool			arePivotsKnown(Uid uid);
	};

}