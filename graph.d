/**
This module contains a few graph implementations, to use the algorithms presented in dranges.graphalgorithm.

This module was introduced from an older codebase. I will clean it up to homogeneize it with the rest of this project.
*/
module dranges.graph;

import std.stdio;
import std.conv;
import std.string;
import std.contracts;
import std.file;
import std.process;

import dranges.graphrange;
public import dranges.properties;


/* TODO:
sub-graphs
pre and post ordering
strongly connected components
meta-graph
shortest path
*/

///
struct Node {
    mixin addProperties;

    int pre, post;

    this(R...)(R rest) {
        static if (rest.length) {
            this.addProperties(rest);
        }
    }

    string toString() {
        return name;
    }
}

/// The default struct
struct Edge {
    Node from;
    Node to;
    mixin addProperties;

    this(R...)(Node from, Node to, R rest) {
        this.from = from;
        this.to = to;
        static if (rest.length) {
            this.addProperties(rest);
        }
    }

    string toString() {
        return from.name ~ " -> " ~ to.name;
    }

    double length() {
        return hasProperty("length") ? getProperty!double("length") : 1.0;
    }
}

/**
Simple graph struct.
*/
struct Graph {
    Node[] nodes;
    Edge[][Node] edges;

    /** Basic functionality. If n is already a node, does nothing.
     If n is indeed new, it adds it to the graph, with no edges.
    */
    size_t addNode(Node n) {
        if (!isValidNode(n)) {
            nodes ~= n;
            edges[nodes[$-1]] = [];
        }
        return nodes.length;
    }

    /** Basic functionality. If to or from are not in the graph, or
     if both are in the graph and an edge already exists between them, it does nothing.
     Else, it adds the edge going _from from _to to (normal situation).
     */
    size_t addEdge(R...)(Node from, Node to, R rest) {
        Edge edge = Edge(from, to);
        static if (rest.length) {
            edge.addProperties(rest);
        }
        if (canAddEdge(from, to)) {
            edges[from] ~= edge;
        }
        return edges[from].length;
    }

    /// Directly add an Edge -> you also got the properties.
    size_t addEdge(R...)(Edge edge, R rest) {
        static if (rest.length) {
            edge.addProperties(rest);
        }
        if (canAddEdge(edge.from, edge.to)) {
            edges[edge.from] ~= edge;
        }
        return edges[edge.from].length;
    }

    /// Add new nodes to the graph.
    size_t addNodes(Node[] n) {
        foreach(node; n) {
            addNode(node);
        }
        return nodes.length;
    }

    /// Add new edges (a Node[] array) to node n, in a batch.
    size_t addEdges(Node from, Node[] toNodes) {
        foreach(to; toNodes) {
            addEdge(from, to);
        }
        return edges[from].length;
    }

    /// Checks than n is in the graph.
    bool isValidNode(Node n) {
        return (n in edges) ? true : false;
    }

    /// Checks than to and from are valid nodes and than _no edge exists between them_.
    bool canAddEdge(Node from, Node to) {
        if (isValidNode(from) && isValidNode(to)) {
            foreach(edge; edges[from]) {
                if (edge.to == to) return false;
            }
            return true;
        }
        return false;
    }

    bool isValidEdge(Node from, Node to) {
        if (isValidNode(from) && isValidNode(to)) {
            foreach(edge; edges[from]) {
                if (edge.to == to) return true;
            }
            return false;
        }
        return false;
    }

    bool isValidEdge(Edge e) {
        if (isValidNode(e.from) && isValidNode(e.to)) {
            foreach(edge; edges[e.from]) {
                if (edge.to == e.to) return true;
            }
            return false;
        }
        return false;
    }

    /// A Graph size is its number of nodes.
    size_t size() {
        return nodes.length;
    }

    /// The order of a graph is the maximum valency of the nodes.
    size_t order() {
        size_t max = size_t.min;
        foreach(node; nodes) {
            auto v = valency(node);
            if (max < v) max = v;
        }
        return max;
    }

    ///
    size_t valency(Node n) {
        enforce(isValidNode(n), "valency called on a inexistent node.");
        return edges[n].length;
    }

    ///
    Node[] neighbors(Node n) {
        enforce(isValidNode(n), "neighbors called on a inexistent node.");
        Node[] result;
        foreach(edge; edges[n]) {
            result ~= edge.to;
        }
        return result;
    }

    ///
    bool hasChildren(Node n) {
        enforce(isValidNode(n), "hasChildren called on a inexistent node.");
        return (edges[n].length != 0);
    }

    ///
    bool isLeaf(Node n) {
        return !hasChildren(n);
    }

    ///
    bool opIn_r(Node n) {
        return (n in edges) ? true : false;
    }

    ///
    bool opIn_r(Edge e) {
        return isValidEdge(e);
    }

    ///
    void deleteNode(Node n, bool danglingBonds = true) {
        enforce(isValidNode(n), "Trying to delete an inexistent node");

        if (!danglingBonds) {
            foreach(ref edgeList; edges) {
                foreach(i, edge; edgeList) {
                    if (edge.to == n) {
                        edgeList = edgeList[0..i] ~ edgeList[i+1 .. $];
                    }
                }
            }
        }

        foreach(int i, Node node; nodes) {
            if (node == n) {
                nodes = nodes[0..i] ~ nodes[i+1..$];
                break;
            }
        }

        edges.remove(n);
    }

    /// Suppress the edge _from from _to to.
    void deleteEdge(Node from, Node to) {
        if (isValidNode(from) && isValidNode(to)) {
            auto edgeList = edges[from];
            foreach(int i, Edge edge; edgeList) { // looking for the edge.
                if (edge.to == to) { // found it: we destroy it
                    edgeList = edgeList[0..i] ~ edgeList[i+1..$];
                    return;
                }
            }
            throw new Exception("Graph: trying to suppress a non-existing edge");
        }
        throw new Exception("Graph: trying to to suppress a edge between nodes not in the graph.");
    }

    /// Suppress the edge e.
    void deleteEdge(Edge e) {
        deleteEdge(e.from, e.to);
    }

    /// Suppress all edges coming from Node n (thus making it a leaf).
    void deleteEdges(Node n) {
        if (isValidNode(n)) {
            edges[n].length = 0;
        } else {
            throw new Exception("Graph: trying to suppress edges to an non-existing Node.");
        }
    }

    ///
    string toString() {
        string tos = "Graph ";
        tos ~= "(" ~ to!string(numNodes()) ~ " nodes, " ~ to!string(numEdges()) ~ " edges) :\n";
        foreach(node; nodes) {
            tos ~= "\t" ~ node.name;
//            if (node.hasProperties) tos ~= "(" ~ to!string(node.getPropertiesNames()) ~")";
            tos ~= " [";
            foreach(edge; edges[node]) {
                tos ~= edge.to.name;
//                if (edge.hasProperties) tos ~= "(" ~ to!string(edge.getPropertiesNames()) ~")";
                tos ~= ", ";
            }
            if (tos.endsWith(", ")) tos = tos[0..$-2]; // If there were children
            tos ~= "]\n";
            if (!(node in edges)) tos ~= " -> leaf\n";
        }
        return tos;
    }

    ///
    size_t numNodes() { return nodes.length;}

    ///
    size_t numEdges() {
        size_t num = 0;
        foreach(edgeList; edges) {
            num += edgeList.length;
        }
        return num;
    }
}

/**
Returns: the complement graph of g: same nodes, but complementary edges:
for each pair (u,v) in nodes(g), if (u,v) is in g, then it's not in the complement.
On the contrary, if (u,v) is not in g, then it's an edge in the complement.
See_Also: inverse.
*/
Graph complementGraph(Graph g) {
    Graph result;
    result.addNodes(g.nodes);
    foreach(node1; nodes(g)) {
        foreach(node2; nodes(g)) {
            Edge e = Edge(node1, node2);
            if (e in g) {
            }
            else {
                result.addEdge(e);
            }
        }
    }
    return result;
}

/**
Returns: the complete graph with the same nodes as g. A complete graph has all possible edges.
(also, its density is 1.0).
*/
Graph completedGraph(Graph g) {
    Graph result;
    result.addNodes(g.nodes);
    foreach(node1; nodes(g)) {
        foreach(node2; nodes(g)) {
            result.addEdge(node1, node2);
        }
    }
    return result;
}

/**
Returns:
a string giving the graph representation using the dot language, from Graphviz.

Also, writes the file $(M name).dot to the current directory.

Caution:
This is just a helper/debugging function to easily visualize the graphs. Use with caution.
*/
string toGraphviz(Graph g, string name = "graph")
{
    string gv = "digraph G {";
    foreach(el; g.edges.values)
    {
        foreach(e; el) {
            gv ~= to!string(e.from) ~" -> "~ to!string(e.to) ~ ";";
        }
    }
    gv ~= "}";
    std.file.write(name~".dot", gv);
    return gv;
