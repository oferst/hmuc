#pragma once
#include "Turtle.h"
class TurtleUser
{
	Turtle* t;
public:
	TurtleUser(Turtle* _t) : t(_t) { t->PenDown(); t->PenDown();
	}
	~TurtleUser() {}
	void UseTurtle() { t->Forward(1); }
};

