#pragma once
#include <inttypes.h>
#include <list>
#include <stack>
#
using namespace std;
namespace Minisat {

template<class V>
class Graph{
	//size of graph
	uint32_t N;
	//edges of graph via an adjacency list
	list<V> *adj;

	void topologicalSortUtil(V v, bool visited[],stack<V> &Stack){
		// Mark the current node as visited.
		visited[v] = true;

		// Recur for all the vertices adjacent to this vertex
		list<V>::iterator i;
		for(V& v : adj[v])
		//for (i = adj[v].begin(); i != adj[v].end(); ++i)
			if (!visited[v])
				topologicalSortUtil(v, visited, Stack);

		// Push current vertex to stack which stores result
		Stack.push(v);
	}
public:
	Graph(uint32_t _N): N(_N), adj(new list<V>[_N]) {}

	void addEdge(V v, V w){
		adj[v].push_back(w); // Add w to v’s list.
	}
	// The function to do Topological Sort. It uses recursive 
	// topologicalSortUtil()
	void Graph::topologicalSort(vec<V>& result){
		stack<V> Stack;

		// Mark all the vertices as not visited
		bool *visited = new bool[N];
		for (int i = 0; i < N; i++)
			visited[i] = false;

		// Call the recursive helper function to store Topological
		// Sort starting from all vertices one by one
		for (int i = 0; i < N; i++)
			if (!visited[i])
				topologicalSortUtil(i, visited, Stack);

		// Print contents of stack
		while (!Stack.empty()){
			result.push(Stack.top());
			Stack.pop();
		}
		delete[] visited;
	}
	~Graph(){
		delete[] adj;
	}
};
}

