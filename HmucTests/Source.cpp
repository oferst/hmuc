#include "MockRebuilderContext.h"
#include "MockSolverHandle.h"
#include "ProofRebuilder.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
#include "../hmuc/utils/ParseUtils.h"
#include <regex>
#include <vector>
#include "TestUtils.h"
using ::testing::AtLeast; 
using ::testing::AtMost;
using ::testing::Exactly;
using ::testing::ReturnRef;
using ::testing::Return;
using ::testing::_;
using ::testing::Mock;
using ::testing::Test;
using ::testing::ContainerEq;
using std::vector;
namespace Minisat {


	class ClauseReconstructSetup {
	public:
		ClauseReconstructSetup() {
			pivots.push(RebuilderContext().dummy);
		}
		vec<Lit> pivots;
		UidToLitSet parentLits;
		std::unordered_map<Uid, bool> ics;
		std::list<Uid> candidateParents;
		
		
		ClauseReconstructSetup& loadPivots(std::string s) {
			pivots.push(mkLit(Var(var_Undef)));
			std::vector<std::string>  pivs = splitByRegex(s);
			for (auto p : pivs) 
				pivots.push(strToLit(p));
			return *this;
		}
		ClauseReconstructSetup& loadParentLits(Uid id,const std::string& s, bool isIc=true) {
			candidateParents.push_back(id);
			ics[id] = isIc;
			std::vector<std::string>  lits = splitByRegex(s);
			LitSet& clause = parentLits[id];
			clause.clear();
			for (auto l : lits)
				clause.insert(strToLit(l));
			return *this;
		}
		void setup(MockRebuilderContext& context) {
			assert(pivots.size() >= parentLits.size());
			for (auto& pair : parentLits) {
				EXPECT_CALL(context, getClauseLits(pair.first)).WillRepeatedly(ReturnRef(pair.second));
				EXPECT_CALL(context, isIc(pair.first)).WillRepeatedly(ReturnRef(ics[pair.first]));
			}
		}
	};




	class ProofRebuilderTest : public ::testing::Test {
	protected:
		MockSolverHandle sh;
		MockRebuilderContext ctx;
		ProofRebuilder prr;
		vec<Lit> ctx_PoEC_pivots;
		vec<Lit> sh_PoEC_pivots;
		LitSet s_empty, sLeft, sRight;
		Lit BL = mkLit(Var(1));
		Lit piv = mkLit(Var(2));
		Uid rightUid = 1;
		ProofRebuilderTest() : prr(&sh,&ctx) {

		}

		virtual ~ProofRebuilderTest() {
		}

		virtual void SetUp() {
			sLeft.clear();
			sRight.clear();
		}

		virtual void TearDown() {
			Mock::VerifyAndClear(&ctx);
			Mock::VerifyAndClear(&sh);
		}
	};

	TEST_F(ProofRebuilderTest, SanityCheck) {

	}
	TEST_F(ProofRebuilderTest, SanityCheckWithExpectation) {
		EXPECT_TRUE(true);
	}

	TEST_F(ProofRebuilderTest, findParentUsed_dummyPivotResultsInRightParent) {

		EXPECT_CALL(ctx, getClauseLits(_)).Times(Exactly(0));
		ASSERT_EQ(Right,prr.findParentsUsed(s_empty, rightUid, ctx.dummy, mkLit(Var(1))));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_BLPivotResultsInRightParent) {
		EXPECT_CALL(ctx, getClauseLits(_)).Times(Exactly(0));
		ASSERT_EQ(Right, prr.findParentsUsed(s_empty, rightUid, piv, piv));
		ASSERT_EQ(Right, prr.findParentsUsed(s_empty, rightUid, ~piv, ~piv));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_negBLPivotResultsInLeftParent) {
		EXPECT_CALL(ctx, getClauseLits(_)).Times(Exactly(0));
		ASSERT_EQ(Left, prr.findParentsUsed(s_empty, rightUid, ~piv, piv));
		ASSERT_EQ(Left, prr.findParentsUsed(s_empty, rightUid, piv, ~piv));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_ParentUidEqualsCRefUndefResultsInLeftParent) {
		EXPECT_CALL(ctx, getClauseLits(_)).Times(Exactly(0));
		ASSERT_EQ(Left, prr.findParentsUsed(s_empty, CRef_Undef, mkLit(Var(2), true), mkLit(Var(1))));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_negPivotInLeftParnetOnlyResultsInRightParent) {
		sLeft.insert(~piv);
		EXPECT_CALL(ctx, getClauseLits(rightUid)).Times(Exactly(1)).WillOnce(ReturnRef(sRight));
		ASSERT_EQ(Right, prr.findParentsUsed(sLeft, rightUid, piv, BL));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_PivotInRightParnetOnlyResultsInLeftParent) {
		sRight.insert(piv);
		EXPECT_CALL(ctx, getClauseLits(rightUid)).Times(Exactly(1)).WillOnce(ReturnRef(sRight));
		ASSERT_EQ(Left, prr.findParentsUsed(sLeft, rightUid, piv, BL));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_PivotInBothParnetsResultsInBoth) {
		sRight.insert(piv);
		sLeft.insert(~piv);
		EXPECT_CALL(ctx, getClauseLits(rightUid)).Times(Exactly(1)).WillOnce(ReturnRef(sRight));
		ASSERT_EQ(Both, prr.findParentsUsed(sLeft, rightUid, piv, BL));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_PivotInNeitherParnetsResultsInEither) {
		EXPECT_CALL(ctx, getClauseLits(rightUid)).Times(Exactly(1)).WillOnce(ReturnRef(sRight));
		ASSERT_EQ(Either, prr.findParentsUsed(sLeft, rightUid, piv, BL));
	}

	TEST_F(ProofRebuilderTest,ResolveWithOverwriteTestEmptySets){
		//for (int i = 0; i < 5; ++i) {
		//	sLeft.insert(mkLit(Var(i + 5), true));
		//	sRight.insert(mkLit(Var(i + 10)));
		//}
		LitSet tempL = sLeft;
		LitSet tempR = sRight ;
		ASSERT_EQ(ctx.dummy, prr.resolveWithOverwrite(sLeft, sRight));
		ASSERT_THAT(tempL, ContainerEq(sLeft));
		ASSERT_THAT(tempR, ContainerEq(sRight));
	}
	TEST_F(ProofRebuilderTest, ResolveWithOverwriteLeftEmptyRightNotEmpty) {
		for (int i = 0; i < 5; ++i) {
			sRight.insert(mkLit(Var(i + 10)));
		}
		LitSet tempR = sRight;
		ASSERT_EQ(ctx.dummy, prr.resolveWithOverwrite(sLeft, sRight));
		ASSERT_THAT(sRight, ContainerEq(sLeft));
		ASSERT_THAT(tempR, ContainerEq(sRight));
	}


	TEST_F(ProofRebuilderTest, ResolveWithOverwriteLeftNotEmptyRightEmpty) {
		for (int i = 0; i < 5; ++i) {
			sLeft.insert(mkLit(Var(i + 10)));
		}
		LitSet tempL = sLeft;
		LitSet tempR = sRight;
		ASSERT_EQ(ctx.dummy, prr.resolveWithOverwrite(sLeft, sRight));
		ASSERT_THAT(tempR, ContainerEq(sRight));
		ASSERT_THAT(tempL, ContainerEq(sLeft));
	}
	TEST_F(ProofRebuilderTest, ResolveWithOverwriteNoCommonPivot) {
		for (int i = 0; i < 5; ++i) {
			sLeft.insert(mkLit(Var(i + 10)));
		}
		for (int i = 0; i < 5; ++i) {
			sLeft.insert(mkLit(Var(i + 20),true));
		}
		LitSet tempR = sRight;
		LitSet Union;
		unionContnet(sLeft, sRight , Union);
		ASSERT_EQ(ctx.dummy, prr.resolveWithOverwrite(sLeft, sRight));
		ASSERT_THAT(tempR, ContainerEq(sRight));
		ASSERT_THAT(Union, ContainerEq(sLeft));
	}
	TEST_F(ProofRebuilderTest, ResolveWithOverwriteWithPosPivot) {
		for (int i = 0; i < 5; ++i) {
			sLeft.insert(mkLit(Var(i + 10)));
		}
		for (int i = 0; i < 5; ++i) {
			sLeft.insert(mkLit(Var(i + 20), true));
		}
		LitSet Union; 
		unionContnet(sLeft, sRight, Union);

		sLeft.insert(~piv);
		sRight.insert(piv);
		LitSet tempR = sRight;
		ASSERT_EQ(piv, prr.resolveWithOverwrite(sLeft, sRight));
		ASSERT_THAT(tempR, ContainerEq(sRight));
		ASSERT_THAT(Union, ContainerEq(sLeft)); //expected result in sLeft ('side-effect')
	}

	TEST_F(ProofRebuilderTest, ResolveWithOverwriteWithNegPivot) {
		for (int i = 0; i < 5; ++i) {
			sLeft.insert(mkLit(Var(i + 10)));
		}
		for (int i = 0; i < 5; ++i) {
			sLeft.insert(mkLit(Var(i + 20), true));
		}
		LitSet Union;
		unionContnet(sLeft, sRight, Union);
		sLeft.insert(piv);
		sRight.insert(~piv);
		LitSet tempR = sRight;
		ASSERT_EQ(~piv, prr.resolveWithOverwrite(sLeft, sRight));
		ASSERT_THAT(tempR, ContainerEq(sRight));
		ASSERT_THAT(Union, ContainerEq(sLeft)); //expected result in sLeft ('side-effect')
	}
	TEST_F(ProofRebuilderTest, ResolveWithOverwriteCantResolveWithTwoPivots) {
		for (int i = 0; i < 5; ++i) {
			sLeft.insert(mkLit(Var(i + 10)));
		}
		for (int i = 0; i < 5; ++i) {
			sLeft.insert(mkLit(Var(i + 20), true));
		}
		sLeft.insert(piv);
		sRight.insert(~piv);
		Lit piv2 = mkLit(Var(3));
		sLeft.insert(piv2);
		sRight.insert(~piv2);
		ASSERT_THROW(prr.resolveWithOverwrite(sLeft, sRight),ProofRebuilder::ResolutionException);
	}
	TEST_F(ProofRebuilderTest, reconstructClauseAllPivotsPresentAndBLPresent) {
		Lit BL = intToLit(3);
		ClauseReconstructSetup su;
		su.
			loadParentLits(1, "-1,2,3", true).
			loadParentLits(2, "-2,4,5", true).
			loadParentLits(3, "1,4",	true).
			loadParentLits(4, "-4",		true).
			loadParentLits(5, "-5",		true).
			loadPivots("-2,1,-4,-5").
			setup(ctx);
		
		//just a sanity check - after calling mock context should agree with the literals generated for each parent
		for(Uid id : su.candidateParents)
			ASSERT_EQ(ctx.getClauseLits(id), su.parentLits[id]);
		LitSet s1{ intToLit(-1),intToLit(2),intToLit(3) };
		LitSet s2{ intToLit(-2),intToLit(4),intToLit(5) };
		LitSet s3{ intToLit(1),intToLit(4) };
		LitSet s4{ intToLit(-4) };
		LitSet s5{ intToLit(-5) };
		ASSERT_EQ(ctx.getClauseLits(1), s1);
		ASSERT_EQ(ctx.getClauseLits(2), s2);
		ASSERT_EQ(ctx.getClauseLits(3), s3);
		ASSERT_EQ(ctx.getClauseLits(4), s4);
		ASSERT_EQ(ctx.getClauseLits(5), s5);
		//end sanity check


		//The UUT
		ReconstructionResult rr;
		prr.reconstructClause(BL, su.candidateParents, su.pivots, rr);
		LitSet expected{ intToLit(3) };
		ASSERT_EQ(rr.newClause, expected);
		vector<Uid> expectedParents = vector<Uid>{ 1,2,3,4,5 };
		ASSERT_EQ(rr.actualParentsUsed.size(), expectedParents.size());
		for (int i = 0; i < expectedParents.size(); ++i)
			ASSERT_EQ(expectedParents[i], rr.actualParentsUsed[i]);
	}

	TEST_F(ProofRebuilderTest, reconstructClauseAllPivotsPresentAndBLMissing) {
		Lit BL = intToLit(2018);
		
		ClauseReconstructSetup su;
		su.
			loadParentLits(1, "-1,2,3", true).
			loadParentLits(2, "-2,4,5", true).
			loadParentLits(3, "1,4", true).
			loadParentLits(4, "-4", true).
			loadParentLits(5, "-5", true).
			loadPivots("-2,1,-4,-5").
			setup(ctx);

		//The UUT
		ReconstructionResult rr;
		prr.reconstructClause(BL, su.candidateParents, su.pivots, rr);
		LitSet expected{ intToLit(3) };
		ASSERT_EQ(rr.newClause, expected);
		vector<Uid> expectedParents = vector<Uid>{ 1,2,3,4,5 };
		ASSERT_EQ(rr.actualParentsUsed.size(), expectedParents.size());
		for (int i = 0; i < expectedParents.size(); ++i)
			ASSERT_EQ(expectedParents[i], rr.actualParentsUsed[i]);
	}
	TEST_F(ProofRebuilderTest, reconstructClauseAllPivotsPresentAndBLAsLastPivot) {
		Lit BL = intToLit(-5);

		ClauseReconstructSetup su;
		su.
			loadParentLits(1, "-1,2,3", true).
			loadParentLits(2, "-2,4,5", true).
			loadParentLits(3, "1,4", true).
			loadParentLits(4, "-4", true).
			loadParentLits(5, "-5", true).
			loadPivots("-2,1,-4,-5").
			setup(ctx);

		//The UUT
		ReconstructionResult rr;
		prr.reconstructClause(BL, su.candidateParents, su.pivots, rr);
		vector<Uid> expectedParents = vector<Uid>{ 5 };
		ASSERT_EQ(rr.actualParentsUsed.size(), expectedParents.size());
		for (int i = 0; i < expectedParents.size(); ++i)
			ASSERT_EQ(expectedParents[i], rr.actualParentsUsed[i]);
	}
	TEST_F(ProofRebuilderTest, reconstructClauseAllPivotsPresentAndNegBLAsLastPivot) {
		Lit BL = intToLit(5);

		ClauseReconstructSetup su;
		su.
			loadParentLits(1, "-1,2,3", true).
			loadParentLits(2, "-2,4,5", true).
			loadParentLits(3, "1,4", true).
			loadParentLits(4, "-4", true).
			loadParentLits(5, "-5", true).
			loadPivots("-2,1,-4,-5").
			setup(ctx);

		ReconstructionResult rr;
		//The UUT
		prr.reconstructClause(BL, su.candidateParents, su.pivots, rr);
		LitSet expected{ intToLit(3),intToLit(5) };
		ASSERT_EQ(rr.newClause, expected);
		vector<Uid> expectedParents = vector<Uid>{1,2,3,4};
		ASSERT_EQ(rr.actualParentsUsed.size(), expectedParents.size());
		for (int i = 0; i < expectedParents.size(); ++i)
			ASSERT_EQ(expectedParents[i], rr.actualParentsUsed[i]);
	}
	TEST_F(ProofRebuilderTest, LiveUnit) {
		Lit BL = intToLit(1);

		ClauseReconstructSetup su;
		su.
			loadParentLits(1, "-1,2,3", true).
			loadParentLits(2, "-2,4,5", true).
			loadParentLits(3, "1,4", true).
			loadParentLits(4, "-4", true).
			loadParentLits(5, "-5", true).
			loadPivots("-2,1,-4,-5").
			setup(ctx);

		ReconstructionResult rr;
		//The UUT
		prr.reconstructClause(BL, su.candidateParents, su.pivots, rr);
		LitSet expected{ intToLit(1) };
		ASSERT_EQ(rr.newClause, expected);
		vector<Uid> expectedParents = vector<Uid>{ 3,4 };
		ASSERT_EQ(rr.actualParentsUsed.size(), expectedParents.size());
		for (int i = 0; i < expectedParents.size(); ++i)
			ASSERT_EQ(expectedParents[i], rr.actualParentsUsed[i]);
	}

	int main(int argc, char** argv) {
		// The following line must be executed to initialize Google Mock
		// (and Google Test) before running the tests.
		::testing::InitGoogleMock(&argc, argv);
		return RUN_ALL_TESTS();
	}



}