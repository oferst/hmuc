#include "MockTurtle.h"
#include "TurtleUser.h"
#include "gmock/gmock.h"
#include "gtest/gtest.h"
using ::testing::AtLeast;                     // #1
using ::testing::AtMost;
using ::testing::Exactly;
TEST(PainterTest, CanDrawSomething) {
	MockTurtle turtle;                          // #2
	EXPECT_CALL(turtle, PenDown())              // #3
		.Times(AtMost(2));
	EXPECT_CALL(turtle, PenDown())              // #3
		.Times(Exactly(1));
	TurtleUser user(&turtle);                   // #4

	//EXPECT_TRUE(painter.DrawCircle(0, 0, 10));
}                                             // #5

int main(int argc, char** argv) {
	printf("hello world");
	// The following line must be executed to initialize Google Mock
	// (and Google Test) before running the tests.
	::testing::InitGoogleMock(&argc, argv);
	return RUN_ALL_TESTS();
}