#pragma once
#include <string>
void Assert(bool b,const std::string & msg = "") {
//#ifdef _DEBUG
	if (!b) throw(0);
//#endif
}