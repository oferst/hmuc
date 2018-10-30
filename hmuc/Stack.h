#pragma once
#include "core\SolverTypes.h"

namespace Minisat{
	struct StackNode {
		uint32_t data;
		StackNode *prev, *next;
		StackNode(uint32_t _data, StackNode* _prev=NULL, StackNode* _next = NULL) :data(_data), prev(_prev), next(_next) {}
	};
class Stack{
public:
	StackNode *head, *tail;
	Stack(){
		head = tail = NULL;
	}
	void push(uint32_t data) {
		StackNode* temp = new StackNode(data);
		if (NULL == tail) {
			head = tail = temp;
		}
		else {
			assert(NULL == tail->next);
			tail->next = temp;
			temp->prev = tail;
		}
	}
	StackNode* top() { return tail; }
	void pop() {
		if (NULL == tail) return;

		StackNode* temp = tail;
		tail = tail->prev;
		tail->next = NULL;
		delete temp;
	}
	bool empty() {
		return NULL == tail;
	}

	~Stack(){
		StackNode* i = head;
		if (NULL == i) return;
		while (NULL != i->next) {
			i->next->prev = i;
			i = i->next;
			delete  i->prev;
		}
	}
};
}

