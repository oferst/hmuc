#include "MockRebuilderContext.h"
#include "MockSolverHandle.h"
#include "ProofRebuilder.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
using ::testing::AtLeast; 
using ::testing::AtMost;
using ::testing::Exactly;
using ::testing::ReturnRef;
using ::testing::_;
using ::testing::Mock;
using ::testing::Test;
using ::testing::ContainerEq;

namespace Minisat {
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

		EXPECT_CALL(ctx, getClause(_)).Times(Exactly(0));
		ASSERT_EQ(Right,prr.findParentsUsed(s_empty, rightUid, ctx.dummy, mkLit(Var(1))));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_BLPivotResultsInRightParent) {
		EXPECT_CALL(ctx, getClause(_)).Times(Exactly(0));
		ASSERT_EQ(Right, prr.findParentsUsed(s_empty, rightUid, piv, piv));
		ASSERT_EQ(Right, prr.findParentsUsed(s_empty, rightUid, ~piv, ~piv));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_negBLPivotResultsInLeftParent) {
		EXPECT_CALL(ctx, getClause(_)).Times(Exactly(0));
		ASSERT_EQ(Left, prr.findParentsUsed(s_empty, rightUid, ~piv, piv));
		ASSERT_EQ(Left, prr.findParentsUsed(s_empty, rightUid, piv, ~piv));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_ParentUidEqualsCRefUndefResultsInLeftParent) {
		EXPECT_CALL(ctx, getClause(_)).Times(Exactly(0));
		ASSERT_EQ(Left, prr.findParentsUsed(s_empty, CRef_Undef, mkLit(Var(2), true), mkLit(Var(1))));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_negPivotInLeftParnetOnlyResultsInRightParent) {
		sLeft.insert(~piv);
		EXPECT_CALL(ctx, getClause(rightUid)).Times(Exactly(1)).WillOnce(ReturnRef(sRight));
		ASSERT_EQ(Right, prr.findParentsUsed(sLeft, rightUid, piv, BL));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_PivotInRightParnetOnlyResultsInLeftParent) {
		sRight.insert(piv);
		EXPECT_CALL(ctx, getClause(rightUid)).Times(Exactly(1)).WillOnce(ReturnRef(sRight));
		ASSERT_EQ(Left, prr.findParentsUsed(sLeft, rightUid, piv, BL));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_PivotInBothParnetsResultsInBoth) {
		sRight.insert(piv);
		sLeft.insert(~piv);
		EXPECT_CALL(ctx, getClause(rightUid)).Times(Exactly(1)).WillOnce(ReturnRef(sRight));
		ASSERT_EQ(Both, prr.findParentsUsed(sLeft, rightUid, piv, BL));
	}
	TEST_F(ProofRebuilderTest, findParentUsed_PivotInNeitherParnetsResultsInEither) {
		EXPECT_CALL(ctx, getClause(rightUid)).Times(Exactly(1)).WillOnce(ReturnRef(sRight));
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


	int main(int argc, char** argv) {
		// The following line must be executed to initialize Google Mock
		// (and Google Test) before running the tests.
		::testing::InitGoogleMock(&argc, argv);
		return RUN_ALL_TESTS();
	}
}