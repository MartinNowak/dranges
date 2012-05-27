// Written in the D programming language

/**
This module contains a few _graph implementations, to use the algorithms presented in dranges.graphalgorithm.
In a _graph, nodes are defined by a (unique) label, and a value. A label can be of any type, $(D string) being the
most common, and will be used to refer to a particular node. A value can also be of any type and is just the payload stored
in the node.

An edge is a (directed) link from a node to another. It's represented as two labels.

The basic idea is that to construct a _graph (and for many algorithms) nodes and edges just have to obey small constraints:
for a node, to have a $(M .label) and a $(M .value) member, and for an edge, to have a $(M .from) and a $(M .to) member.
To compile, all the nodes in a _graph must have the same type and the edges must be compatible:
the label they point to must have the correct type (compile-time check) and the correct value (runtime check).

Then, for richer structures, nodes and edges can expose other members, typically somthing like $(M .weight), $(M .length),
$(M .capacity), $(M .flow) or $(M .color). Algorithm will check for the existence of such members and refuse to compile if they do not exist.
(An idea to pursue could be to provide a simple _graph and an associative array of labels, to give the algorithm access to some property,
 like a double[Edge] AA giving the lengths of edges.)

As of this writing, I changed $(M Graph) back to a struct, and $(M UndirectedGraph) also. On the other hand
directed acyclic graphs might be modelized by an $(M assumeAcyclic) wrapper, like $(M std.algorithm) does for sorted ranges. We'll see.

TODO:
lots of things. Shaping up UndirectedGraph, trying a DAG class, a bidirectional _graph (with access not only to the successors/outedges of a node
but also to its predecessors/ingoing edges). Also, iterating on a _graph is easy, but modifying it, not so much. I might define some cursor-like structure,
for example created by $(M opIndex[label]), that would give ref access to a node, its payload but also to its successors. See also the $(M dranges.recursive)
module for similar ideas. I get the impression that I can unite recursive ranges and cursors in one entity.

TODO:
Once this has stabilized some, make $(M Graph) a container by providing some of $(M std.container.TotalContainer) primitives. Not all make sense for a graph.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.graph;

import std.algorithm,
       std.array,
       std.conv,
       std.exception,
       std.file,
       std.string,
       std.traits,
       std.typetuple;

import dranges.typetuple;

/// constraint template.
template isNode(N)
{
    enum bool isNode = is(typeof(N.label)) && is(typeof(N.value));
}

/// constraint template.
template isEdge(E)
{
    enum bool isEdge = is(typeof(E.from)) && is(typeof(E.to)) && is(typeof(E.from) == typeof(E.to));
}


template isNodeOrEdge(T)
{
    enum bool isNodeOrEdge = isNode!T || isEdge!T;
}

/// extracts the label type from a node.
template Label(N) if (isNode!N)
{
    alias typeof(N.label) Label;
}

/// extracts the value (payload) type from a node.
template Value(N) if (isNode!N)
{
    alias typeof(N.value) Value;
}

/// extracts the label type from an edge.
template Label(E) if (isEdge!E)
{
    alias typeof(E.from) Label;
}

/// basic Node struct, the minimal interface a Node must provide.
struct Node(Label, Value = Label) {
    Label label;
    Value value;
}

/// creates a Node from a label and a value.
Node!(Label, Value) node(Label,Value)(Label label, Value value)
{
    return Node!(Label, Value)(label, value);
}

/// creates a node which has equal label and values. Useful when you just want the structure of a graph
/// and are not interested in storing content in it.
Node!(Label, Label) node(Label)(Label label)
{
    return Node!(Label, Label)(label, label);
}

/// basic edge, provides the minimum members an edge must have.
struct Edge(Label)
{
    Label from, to;
    string toString() { return std.conv.to!string(from) ~ "->" ~ std.conv.to!string(to);}
}

/// factory function to create an edge and do type deduction on labels.
Edge!Label edge(Label)(Label l1, Label l2)
{
    return Edge!Label(l1,l2);
}

/**
First try at having a richer Node.
*/
struct WeightedNode(Value, Label = string, Weight = double)
{
    Label label;
    Value value;
    Weight weight;
}

/**
An edge with a $(M length) member. A problem remains: how to generically
construct the reversed edge (going from 'to' to 'from') from an unknown type
providing the edge interface? The internal structure may be complicated and initialized in
a non-trivial way.
*/
struct LengthyEdge(Label, Length)
{
    Label from, to;
    Length length;
}


/**
A simple directed graph struct, parameterized on the nodes and edge types. These must be compatible:
the nodes have at least a label (its "name") and a value, and the edges link two labels.
*/
struct Graph(N,E) if (isNode!N && isEdge!E && is(Label!N == Label!E))
{
    alias N NodeType; /// exposed node type.
    alias E EdgeType; /// exposed edge type.
    alias Label!N LabelType; /// exposed label type.
    alias Value!N ValueType; /// exposed payload type.

    NodeType[Label!N] _nodes;
    EdgeType[][Label!N] _edges;
    // bool[Edge] edgeExists;

//    static Graph!(CommonType!(StaticFilter!(isNode,T)),
//           Select!(StaticFilter!(isEdge,T).length == 0,
//                   Edge!(typeof(CommonType!(StaticFilter!(isNode,T)).label)),
//                   CommonType!(StaticFilter!(isEdge,T))
//                   )
//           )
//    opCall(T...)(T nodesOrEdges) if(isValidNodeEdgeList!T)
//    {
//        auto g = new Graph!(CommonType!(StaticFilter!(isNode,T)),
//           Select!(StaticFilter!(isEdge,T).length == 0,
//                   Edge!(typeof(CommonType!(StaticFilter!(isNode,T)).label)),
//                   CommonType!(StaticFilter!(isEdge,T))))();
//        foreach(i, Type; T)
//        {
//            static if (isNode!Type)
//                g.addNode(nodesOrEdges[i]);
//            else
//                g.addEdge(nodesOrEdges[i]);
//        }
//        return g;
//    }
    this(T...)(T nodesOrEdges) if(isValidNodeEdgeList!T)
    {
        foreach(i, Type; T)
        {
            static if (isNode!Type)
                addNode(nodesOrEdges[i]);
            else
                addEdge(nodesOrEdges[i]);
        }
    }

    /// Concatenation operator, to create a graph with a new node in it.
    Graph!(N,E) opBinary(string op)(NodeType n) if (op == "~")
    {
        auto result = this;
        result.addNode(n);
        return result;
    }

    /// adding a node to the graph.
    void opOpAssign(string op)(NodeType n) if (op == "~")
    {
        addNode(n);
    }

    /// The same, with an edge.
    Graph!(N,E) opBinary(string op)(EdgeType e) if (op == "~")
    {
        auto result = this;
        result.addEdge(e);
        return result;
    }

    /// ditto.
    void opOpBinary(string op)(EdgeType e) if (op == "~")
    {
        addNode(e);
    }

    /**
    Basic functionality. If n is already a node, does nothing.
    If n is indeed new, it adds it to the graph, with no edges.
    */
    void addNode(NodeType n)
    {
        if (!isValidNode(n.label))
        {
            _nodes[n.label] = n;
            _edges[n.label] = [];
        }
    }

    /**
    Basic functionality. If to or from are not in the graph, or
    if both are in the graph and an edge already exists between them, it does nothing.
    Else, it adds the edge going _from from _to to (normal situation).
    */
    void addEdge(Label!N from, Label!N to)
    {
        addEdge(EdgeType(from, to));
    }

    /// Adds an edge to the grap.
    void addEdge(EdgeType edge)
    {
        if (canAddEdge(edge.from, edge.to))
        {
            _edges[edge.from] ~= edge;
        }
    }

    /// Add new nodes to the graph.
    void addNodes(NodeType[] n)
    {
        foreach(node; n) addNode(node);
    }

    /// Add new edges (a Label!N[] array) to node n, in a batch.
    void addEdges(Label!N from, Label!N[] toNodes)
    {
        foreach(to; toNodes) addEdge(from, to);
    }

    /// Checks if there is a node labeled l in the graph. It's a O(N lg N) operation, N being the number of nodes.
    bool isValidNode(Label!N l)
    {
        return (l in _nodes) ? true : false;
    }

    /// Checks than to and from are valid nodes labels and that no edge exists between them.
    bool canAddEdge(Label!N from, Label!N to)
    {
        if (isValidNode(from) && isValidNode(to))
        {
            foreach(edge; _edges[from])
            {
                if (edge.to == to) return false;
            }
            return true;
        }
        return false;
    }

    ///
    bool isValidEdge(Label!N from, Label!N to)
    {
        if (isValidNode(from) && isValidNode(to))
        {
            foreach(edge; _edges[from])
            {
                if (edge.to == to) return true;
            }
            return false;
        }
        return false;
    }

    ///
    bool isValidEdge(EdgeType e)
    {
        if (isValidNode(e.from) && isValidNode(e.to))
        {
            foreach(edge; _edges[e.from])
            {
                if (edge.to == e.to) return true;
            }
            return false;
        }
        return false;
    }

    /// Returns an array containing a copy of the graph's nodes. It's not lazy.
    NodeType[] nodes() @property
    {
        return _nodes.values;
    }

    /// Returns the labels of a graph. It's not lazy.
    Label!N[] labels() @property
    {
        return _nodes.keys;
    }

    /// Returns the edges as an array. It's not lazy.
    EdgeType[] edges() @property
    {
        EdgeType[] result;
        foreach(label, edgeList; _edges) result ~= edgeList;
        return result;
    }

    /// A Graph size is its number of nodes.
    size_t size() @property
    {
        return _nodes.length;
    }

    /// the valency of a node is the number of its outcoming edges.
    size_t valency(Label!N l)
    {
        enforce(isValidNode(l), "valency called on a inexistent node: " ~to!string(l));
        return _edges[l].length;
    }

    /// Returns the children of the node labeled l, as a label array.
    Label!N[] successors(Label!N l)
    {
        enforce(isValidNode(l), "neighbors called on a inexistent node: " ~to!string(l));
        Label!N[] result;
        foreach(edge; _edges[l])
        {
            result ~= edge.to;
        }
        return result;
    }

    /// returns true iff the node labeled l has children (outcoming edges).
    bool hasChildren(Label!N l)
    {
        enforce(isValidNode(l), "hasChildren called on a inexistent node: "~to!string(l));
        return (_edges[l].length != 0);
    }

    /// returns true iff the node labeled l is a sink in the graph (a leaf in tree parlance, a node without outgoing edges).
    bool isSink(Label!N l)
    {
        enforce(isValidNode(l), "isLeaf called on a inexistent node: "~to!string(l));
        return (_edges[l].length != 0);
    }

    /// returns true if l is in the graph
    bool opIn_r(Label!N l)
    {
        return isValidNode(l);
    }

    /// returns true if e is in the graph
    bool opIn_r(EdgeType e)
    {
        return isValidEdge(e);
    }

    /// returns the node labeled l. It's one of the few functions there that returns a true node.
    NodeType opIndex(Label!N l)
    {
        enforce(isValidNode(l), "No node labeled " ~ to!string(l) ~ " in the graph.");
        return _nodes[l];
    }

    /**
    Deletes the node labeled l from the graph. You can force dangling bonds (ie, invalide edges pointing
    to a now-inexistent node) by setting danglingBonds to true. I do not think it's a good idea.
    */
    void deleteNode(Label!N l, bool danglingBonds = false)
    {
        enforce(isValidNode(l), "Trying to delete an inexistent node");

        _nodes.remove(l);
        _edges.remove(l);

        if (!danglingBonds)
        {
            foreach(Label!N ll, ref edgeList; _edges)
            {
                foreach(i, edge; edgeList)
                {
                    if (edge.to == l)
                    {
                        edgeList = edgeList[0..i] ~ edgeList[i+1 .. $];
                    }
                }
            }
        }
    }

    /// Suppresses the edge going _from from _to to.
    void deleteEdge(Label!N from, Label!N to)
    {
        // enforce?
        if (isValidNode(from) && isValidNode(to))
        {
            auto edgeList = _edges[from];
            foreach(int i, EdgeType edge; edgeList) // looking for the edge.
            {
                if (edge.to == to) // found it: we destroy it
                {
                    edgeList = edgeList[0..i] ~ edgeList[i+1..$];
                    return;
                }
            }
            throw new Exception("Graph: trying to suppress a non-existing edge");
        }
        throw new Exception("Graph: trying to to suppress a edge between nodes not in the graph.");
    }

    /// Suppresses the edge e.
    void deleteEdge(EdgeType e)
    {
        deleteEdge(e.from, e.to);
    }

    /// Suppresses all edges going from the node labeled l (thus making it a leaf).
    void deleteEdges(Label!N l)
    {
        if (isValidNode(l))
        {
            _edges[l].length = 0;
        } else
        {
            throw new Exception("Graph: trying to suppress edges to an non-existing Node.");
        }
    }

    /// to print the graph.
    string toString()
    {
        string tos = "Graph ";
        tos ~= "(" ~ to!string(numNodes()) ~ " nodes, " ~ to!string(numEdges()) ~ " edges) :\n";
        foreach(label, node; _nodes)
        {
            tos ~= "\t" ~ to!string(label) ~ ": " ~ to!string(node.value);
            tos ~= " [";
            if (label in _edges)
            {
                auto edgeList = _edges[label];
                foreach(i, edge; edgeList)
                {
                    tos ~= to!string(edge.to);
                    if (i < edgeList.length-1) tos ~= ", ";
                }
                tos ~= "]\n";
            }
            else
            {
                tos ~= " -> leaf\n";
            }
        }
        return tos;
    }

    /// equivalent to $(M .size).
    size_t numNodes() @property
    {
        return _nodes.length;
    }

    /**
    Returns the total number of edges. It's not a pre-calculated value. Maybe that would
    be a good idea to have a counter somewhere instead of calculating it that way.
    */
    size_t numEdges() @property
    {
        size_t num = 0;
        foreach(label, edgeList; _edges)
        {
            num += edgeList.length;
        }
        return num;
    }
}

template isValidNodeEdgeList(T...)
{
    static if (allSatisfy!(isNodeOrEdge, T)        // if they are all nodes or edges,
           && (StaticFilter!(isNode,T).length > 0) // if there is at least one node,
           && !is(CommonType!(StaticFilter!(isNode,T)) == void)) // do nodes have a common type?
    {
           static if (StaticFilter!(isEdge,T).length) // and if there is at least one edge ...
                enum bool isValidNodeEdgeList = !is(CommonType!(StaticFilter!(isEdge,T)) == void) // ... do these edges have a common type?
                                                 // and are nodes and edges compatible?
                                             &&  is(typeof(CommonType!(StaticFilter!(isNode,T)).label) == typeof(CommonType!(StaticFilter!(isEdge,T)).to));
            else  // No edge in the list
                enum bool isValidNodeEdgeList = true;
    }
    else
        enum bool isValidNodeEdgeList = false;

}

/**
Builds a Graph from a list of nodes and edges. The signature may by odious, but usage is very simple: just
give it a list of nodes and edges.
----
auto g = graph(node("A", 1.0), node("B", 2), node("C", 3.141592), edge("A", "B"), edge("A", "C"), node("D", -1.0), edge("D", "C"));
----
(Curse you DDoc for making me destroy my layout to work around a bug).

The function will determine the nodes and edges types from the list, make sure they are compatible
and build the graph out of it. In the above example, the nodes will be labeled by a $(D string),
and contain a value of type $(D double).

Note that it needs at least one node to determine the $(D Graph) type,
so you cannot build a nodeless graph from it. Instead, just create the appropriate struct:
----
Graph!(Node!(Label, Value), Edge!(Label)) g;
----
Right now, it builds the graph exactly as you typed it, so you cannot add an edge linking
nodes that are not both already in the graph. That will change in the future: it will filter the nodes, add
them to the graph, and then add the edges.
*/
Graph!(CommonType!(StaticFilter!(isNode,T)),
       Select!(is(CommonType!(StaticFilter!(isEdge,T)) == void),
               Edge!(typeof(CommonType!(StaticFilter!(isNode,T)).label)),
               CommonType!(StaticFilter!(isEdge,T))
               )
       )
graph(T...)(T edgesOrNodes) if(isValidNodeEdgeList!T)
{
    return typeof(return)(edgesOrNodes);
}

/**
Undirected graph, built upon a directed graph. Still experimental.
*/
struct UndirectedGraph(N,E) if (isNode!N && isEdge!E && is(Label!N == Label!E))
{
    alias N NodeType; /// exposed node type.
    alias E EdgeType; /// exposed edge type.
    alias Label!N LabelType; /// exposed label type.
    alias Value!N ValueType; /// exposed payload type.

    Graph!(N,E) _graph;

    this(T...)(T nodesOrEdges) if(isValidNodeEdgeList!T)
    {
        foreach(i, Type; T)
        {
            static if (isNode!Type)
                _graph.addNode(nodesOrEdges[i]);
            else
            {
                addEdge(nodesOrEdges[i]);
            }
        }
    }

    void addEdge(E edge)
    {
        if (_graph.canAddEdge(edge.from, edge.to))
        {
            _graph._edges[edge.from] ~= edge;
            if (edge.from != edge.to)
            {
                _graph._edges[edge.to] ~= E(edge.to, edge.from, edge.tupleof[2..$]);
            }
        }
    }

    /// to print the graph.
    string toString()
    {
        string tos = "Undirected Graph ";
        tos ~= "(" ~ to!string(_graph.numNodes) ~ " nodes, " ~ to!string(_graph.numEdges/2) ~ " edges) :\n";
        foreach(label, node; _graph._nodes)
        {
            tos ~= "\t" ~ to!string(label) ~ ": " ~ to!string(node.value);
            tos ~= " [";
            if (label in _graph._edges)
            {
                auto edgeList = _graph._edges[label];
                foreach(i, edge; edgeList)
                {
                    tos ~= to!string(edge.to);
                    if (i < edgeList.length-1) tos ~= ", ";
                }
                tos ~= "]\n";
            }
            else
            {
                tos ~= " -> leaf\n";
            }
        }
        return tos;
    }

//    auto opDispatch(string s, T...)(T args)
//    {
//        mixin("return _graph."~s~"(args);");
//    }
    alias _graph this;
}

/// ditto.
UndirectedGraph!(CommonType!(StaticFilter!(isNode,T)),
                   Select!(is(CommonType!(StaticFilter!(isEdge,T)) == void),
                           Edge!(typeof(CommonType!(StaticFilter!(isNode,T)).label)),
                           CommonType!(StaticFilter!(isEdge,T))
                           )
                   )
undirectedGraph(T...)(T edgesOrNodes) if(isValidNodeEdgeList!T)
{
    return typeof(return)(edgesOrNodes);
}
