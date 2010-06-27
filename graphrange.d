// Written in the D programming language

/**
This module offers some conversions functions from a Graph to a range.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.graphrange;

import dranges.graph, dranges.stack, dranges.queue, dranges.range2;

// TODO : EdgeRange that return 'true' edges (node doublets)
// TODO : the same, but lazy, so as not to use two O(N+E) operations to iterate on edges.

/**
Basic function returning g's nodes, as they were entered at creation. It's a 'greedy'
range, as it returns the entire array in one time (which is an O(1) operation, so no big deal).
Example:
----
Graph g;
foreach(node; nodes(g)) {
    //... do stuff
}
----
*/
Node[] nodes(Graph g) {
    return g.nodes;
}

/**
Another simple function returning g's edges as a lazy range. You can modify the
edges in the graph in this way.
Example:
----
Graph g;
// constructing g, with different edges' lengths.
foreach(edge; edges(g3)) {
    edge.changeProperty("length", 1.0);
}
// Now, all edges have the same unit length
----
*/
Concat!(Edge[][]) edges(Graph g) {
    return concat(g.edges.values);
}


///
enum TraversalMode {DepthFirst, BreadthFirst};

/**
A lazy range struct that traverses a graph in a depth-first or breadth-first manner,
as specified at creation with the TraversalMode enum.
*/
struct GraphTraversal(TraversalMode travmode) {
    bool[Node] visited;
    Graph graph;
    static if (travmode == TraversalMode.DepthFirst)
        Stack!(Node) toBeVisited;
    else
        Queue!(Node) toBeVisited;

    this(Graph g) {
        this(g, g.nodes[0]); // No first node given: we begin on g's first node.
    }

    this(Graph g, Node n) {
        graph = g;
        toBeVisited = typeof(toBeVisited)(g.numNodes());
        toBeVisited.push(n); // The node n is the beginning of the traversal.
    }

    Node front() {
        return toBeVisited.top();
    }

    void pushNodes(Node first) {
        static if (travmode == TraversalMode.DepthFirst) { // depth -> stack -> foreach_reverse
            foreach_reverse(edge; graph.edges[first]) {
                if (!(edge.to in visited)) toBeVisited.push(edge.to);
            }
        }
        else { // breadth -> queue -> foreach
            foreach(edge; graph.edges[first]) {
                if (!(edge.to in visited)) toBeVisited.push(edge.to);
            }
        }
    }

    @property GraphTraversal save() { return this;}

    void popFront() {
        auto first = toBeVisited.pop();
        visited[first] = true;
        pushNodes(first);
   }

    bool empty() {
        // We purge old nodes that have already been visited due to cycles in the graph
        while (!toBeVisited.empty() && (toBeVisited.top() in visited)) toBeVisited.pop();
        return toBeVisited.empty;
    }
}

/**
Helper function to create a Traversal struct.
I have problems with default template values.
*/
GraphTraversal!(TraversalMode.DepthFirst) depthFirst(Graph g) {
    return GraphTraversal!(TraversalMode.DepthFirst)(g);
}
/// ditto
GraphTraversal!(TraversalMode.BreadthFirst) breadthFirst(Graph g) {
    return GraphTraversal!(TraversalMode.BreadthFirst)(g);
}

