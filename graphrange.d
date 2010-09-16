// Written in the D programming language

/**
This module offers some conversions functions from a Graph to a range.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.graphrange;

import std.array,
       std.exception,
       std.range;

import dranges.algorithm,
       dranges.graph,
       dranges.queue,
       dranges.range,
       dranges.stack;

///
enum TraversalMode {DepthFirst, BreadthFirst};

/**
A lazy range struct that traverses a graph in a depth-first or breadth-first manner,
as specified at creation with the TraversalMode enum. It produces labels, not the nodes or their values.
See_Also: traversal, valueTraversal.
*/
struct GraphTraversal(N,E,TraversalMode travmode) if (isNode!N && isEdge!E)
{
    alias typeof(N.label) Label;
    bool[Label] visited;
    Graph!(N,E) graph;

    static if (travmode == TraversalMode.DepthFirst)
        Stack!Label toBeVisited;
    else
        Queue!Label toBeVisited;

    this(Graph!(N,E) g) {
        this(g, g.labels.front); // No first node given: we begin on g's "first" node.
    }

    this(Graph!(N,E) g, Label l) {
        enforce(l in g);
        graph = g;
        toBeVisited = typeof(toBeVisited)(g.size);
        toBeVisited.push(l); // The node n is the beginning of the traversal.
    }

    Label front() {
        return toBeVisited.top();
    }

    void pushNodes(Label first) {
        static if (travmode == TraversalMode.DepthFirst) { // depth -> stack -> foreach_reverse
            foreach_reverse(Label l; graph.neighbors(first)) { // node
                if (!(l in visited)) toBeVisited.push(l);
            }
        }
        else { // breadth -> queue -> foreach
            foreach(Label l; graph.neighbors(first)) {
                if (!(l in visited)) toBeVisited.push(l);
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
Generic function to create a Traversal struct. Prefer the use of depthFirst or breadthFirst.
*/
GraphTraversal!(N,E,trav)
traversal(TraversalMode trav, N,E,L)(Graph!(N,E) graph, L label)
if(is(typeof(N.label) == L))
{
    return GraphTraversal!(N,E,trav)(graph, label);
}

/**
Returns a range that traverses the graph in a depth-first or breadth-first way, from the node labeled label. The graph returns labels, not nodes.
*/
GraphTraversal!(N,E,TraversalMode.DepthFirst) depthFirst(N,E,L)(Graph!(N,E) graph, L label) if(is(typeof(N.label) == L))
{
    return GraphTraversal!(N,E,TraversalMode.DepthFirst)(graph, label);
}

/// ditto
GraphTraversal!(N,E,TraversalMode.BreadthFirst) breadthFirst(N,E,L)(Graph!(N,E) graph, L label) if(is(typeof(N.label) == L))
{
    return GraphTraversal!(N,E,TraversalMode.BreadthFirst)(graph, label);
}

/**
Returns a range that traverses the graph in a depth-first or breadth-first way, from node label, and returns
the nodes value.
Note: first try, probably horribly inefficient.
*/
TMapType!("a[b].value", Repeat!(Graph!(N,E)), GraphTraversal!(N,E,TraversalMode.DepthFirst))
depthFirstValues(N,E,L)(Graph!(N,E) graph, L label) if(is(typeof(N.label) == L))
{
    return tmap!"a[b].value"(repeat(graph), depthFirst(graph,label));
}

/// ditto
TMapType!("a[b].value", Repeat!(Graph!(N,E)), GraphTraversal!(N,E,TraversalMode.BreadthFirst))
breadthFirstValues(N,E,L)(Graph!(N,E) graph, L label) if(is(typeof(N.label) == L))
{
    return tmap!"a[b].value"(repeat(graph), breadthFirst(graph,label));
}
