// Written in the D programming language

/**
Some algorithms on graphs: extracting the meta-graph, finding path
in the graph and such.

All the algorithms in this module come from their descriptions in
<a href = "http://www.cs.berkeley.edu/~vazirani/algorithms.html">this book</a>.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.graphalgorithm;

import std.stdio;
import std.typecons;
import std.math: isInfinity;
import std.contracts;
import std.algorithm;
import std.range;

import dranges.graph, dranges.queue, dranges.priorityqueue, dranges.set;
import dranges.graphrange;


/**
Explore a graph g from the node n. The use of recursion makes it similar to depth-first
traversal.
Returns :
An array of nodes, which are the nodes reachable from node n.
*/
Node[] explore(Graph g, Node n, bool[Node] visited = (bool[Node]).init) {
    Node[] result = [n];
    visited[n] = true;
    foreach(edge; g.edges[n]) {
        if (!(edge.to in visited) || !visited[edge.to]) {
            result ~= explore(g, edge.to, visited);
        }
    }
    return result;
}

/**
Returns:
The graph connected components: sub-graphs that are connected.
*/
Node[][] connectedComponents(Graph g) {
    Node[][] result;
    bool[Node] visited;
    foreach(node; g.nodes) {visited[node] = false;}

    Node[] explore(Node n) {
        Node[] result = [n];
        visited[n] = true;
        foreach(edge; g.edges[n]) {
            if (!visited[edge.to]) result ~= explore(edge.to);
        }
        return result;
    }

    foreach(node; g.nodes) {
        if (!visited[node]) result ~= explore(node);
    }
    return result;
}

/**
Returns:
In a tuple, the nodes sorted by decreasing post number and the pre and post-visit timings of g nodes, in associative arrays pre and post.
*/
Tuple!(Node[], int[Node], int[Node]) clock(Graph g) {
    bool[Node] visited;
    Node[] postOrdered;
    int[Node] pre, post;
    int clock = 1;
    foreach(node; g.nodes) visited[node] = false;

    void explore(Node n) {
        visited[n] = true;
        pre[n] = clock; // pre-visit number
        clock++;
        foreach(edge; g.edges[n]) {
            if (!visited[edge.to]) explore(edge.to);
        }
        post[n] = clock; // post-visit number
        clock++;
        postOrdered ~= n;
    }

    foreach(node; g.nodes) {
        if (!visited[node]) explore(node);
    }

    return tuple(postOrdered.reverse, pre, post);
}

/**
Returns:
The reverse graph of g: same nodes, vertices inverted
(ie: an edge going from A to B becomes an edge from B to A, with the same properties).
This graph is useful in certain algorithms, like decomposing
a graph into its strongly connected components and creating its metagraph.
Note:
it's not smart enough to reverse the edges' classification, if any (that would
need distinguishing between forward and tree edges).
See_Also:
isAcyclic(Graph g).
*/
Graph reversedGraph(Graph g) {
    Graph result;
    foreach(node; g.nodes) result.addNode(node);

    foreach(from; g.nodes) {
        foreach(edge; g.edges[from]) {
            if (edge.hasProperties) {
                Edge reversed = edge; // This way, we get the properties also
                reversed.to = edge.from;
                reversed.from = edge.to;
                result.addEdge(reversed);
            }
            else { // no properties
                result.addEdge(edge.to, from);
            }
        }
    }
    return result;
}

/**
Returns:
The list of strongly connected components (the nodes of sub-graphs
where all nodes can be reached from one another).
*/
Node[][] stronglyConnectedComponents(Graph g) {
    Node[] postOrder = clock(reversedGraph(g)).field[0]; // nodes sorted by decreasing post-order, for the inverted graph
    Node[][] scc;
    bool[Node] visited;
    foreach(node; postOrder) {visited[node] = false;}

    Node[] explore(Node n) {
        Node[] result = [n];
        visited[n] = true;
        foreach(edge; g.edges[n]) {
            if (!visited[edge.to]) result ~= explore(edge.to);
        }
        return result;
    }

    foreach(node; postOrder) {
        if (!visited[node]) scc ~= explore(node);
    }
    return scc;
}

/**
Returns:
The subgraphs created by the strongly connected components.
*/
Graph[] subGraphs(Graph g) {
    auto components = stronglyConnectedComponents(g);
    Graph[] subgraphs;
    foreach(component; components) {
        Graph sg;
        sg.addNodes(component);
        foreach(node; component) {
            foreach(edge; g.edges[node]) {
                sg.addEdge(node, edge.to); // works because outward pointing edges won't be added (the link to invalid nodes)
            }                              // I could also test is edge.to points into component
        }
        subgraphs ~= sg;
    }
    return subgraphs;
}

/**
Returns:
The meta-graph associated to g. That's the graph whose nodes are the subgraphs of g
and the edges the edges between these subgraphs. The meta-graph nodes names are the concatenation
of each subgraphs nodes names.

As is internally calls subGraphs, it returns the resulting subgraphs in a tuple
with the meta-graph proper (the two are mostly used together). The scc list can be obtained
as the subgraphs' nodes.

Note:
It could be coded more efficiently: all these successsive functions (reversedGraph - clock
- stronglyConnectedComponents - subGraphs - metaGraph) could be integrated into one metagraph function: some
work is duplicated: while we extract the scc, we could create the metanodes and their names, and
get the outgoing edge without having to painfully find them afterwards as is done there.
But, who cares: for my graphs, it takes a fraction of second to find the MG: there is no need right now to spend 2 days to
shave off some ms.
*/
Tuple!(Graph, Graph[]) metaGraph(Graph g) {
    auto subgraphs = subGraphs(g);
    Graph metagraph;
    Node[Node] metaedges; // Helper array to find, when I have a node (extremities of an outgoing edge),
                          // which subgraph (and so, metanode -> node in the metagraph) has this particular node.

    foreach(subgraph; subgraphs) { // Creating metanodes
        Node metanode;
        string names;
        foreach(node; subgraph.nodes) {
            names ~= node.name;
        }
        metanode.addProperty("name", names);
        foreach(node; subgraph.nodes) { // We have to use foreach again, because metanode was changed by having a new property.
            metaedges[node] = metanode; // this node is in this metanode
        }
        metagraph.addNode(metanode);
    }

    foreach(subgraph; subgraphs) { // finding edges between subgraphs
        foreach(node; subgraph.nodes) {
            if (subgraph.edges[node].length != g.edges[node].length) { // This node has edges pointing to other subgraphs
                foreach(edge; g.edges[node]) {
                    if (!subgraph.isValidNode(edge.to)) { // Node not existing in the subgraph, but existing in the original graph
                        Node metaedgePointingTo = metaedges[edge.to];
                        Node metaedgePointingFrom = metaedges[node];
                        metagraph.addEdge(metaedgePointingFrom, metaedgePointingTo);
                    }
                }
            }
        }
    }

    return tuple(metagraph, subgraphs);
}

///
enum EdgeClassification {TreeForward, Back, Cross};

/**
Classify edges between Tree&Forward edges, back edges and cross edges, without distinguishing
between Tree and Forward. It will modify the graph, adding properties to the edges.
*/
void classifyEdges(ref Graph g) {
    auto clockedNodes = clock(g); // Tuple!(Node[], int[Node], int[Node])
    auto pre = clockedNodes.field[1]; // pre-order number for g's nodes
    auto post = clockedNodes.field[2]; // post-order number

    EdgeClassification classify(int u1, int u2, int v1, int v2) {
        if ((u1<v1) && (v2<u2)) { // v inside u
            return EdgeClassification.TreeForward; // could be Tree or Forward
        }
        if ((v1<u1) && (u2<v2)) { // u inside v
            return EdgeClassification.Back;
        }
        return EdgeClassification.Cross;
    }

    foreach(node; g.nodes) {
        foreach(edge; g.edges[node]) {
            edge.addProperty("edge type", classify(pre[node], post[node], pre[edge.to], post[edge.to]));
        }
    }
}

/**
Returns: True if the graph is acyclic, false otherwise.
*/
bool isAcyclic(ref Graph g) {
    auto clockedNodes = clock(g); // Tuple!(Node[], int[Node], int[Node])
    auto pre = clockedNodes.field[1]; // pre-order number for g's nodes
    auto post = clockedNodes.field[2]; // post-order number

    foreach(node; g.nodes) {
        foreach(edge; g.edges[node]) {
            if ((pre[edge.to] < pre[node]) && (post[node] < post[edge.to])) { // Back edge -> cyclic
                return false; // -> early out
            }
        }
    }
    return true;
}

/**
Returns:
The linearized version of a Directed Acyclic Graph (DAG).
*/
Graph linearize(Graph g, bool testForAcyclic = false) {
    if (testForAcyclic && !isAcyclic(g)) {
        throw new Exception("Cannot linearize a cyclic graph");
    }
    Graph linearized;
    linearized.addNodes(clock(g).field[0]);
    foreach(int i, Node node; linearized.nodes[0..$-1]) {
        linearized.addEdge(node, linearized.nodes[i+1]);
    }
    return linearized;
}


/**
Returns:
The distance (in number of nodes) between node n and all other nodes, as an associative array.
dist(n,n) = 0.
if node B is not reachable from node A, distanceFrom(g, A)[B] = size_t.max;
Remark:
another solution would be not to include B as a key in the associative array. Why not?
*/
size_t[Node] numNodesFrom(Graph g, Node from) {
    size_t[Node] dist;
    foreach(node; g.nodes) dist[node] = size_t.max;
    dist[from] = 0;

    Queue!(Node) queue = Queue!(Node)(g.numNodes());
    queue.push(from);
    while (!queue.empty) {
        Node u = queue.pop;
        foreach(v; g.edges[u]) {
            if (dist[v.to] == size_t.max) {
                queue.push(v.to);
                dist[v.to] = dist[u] + 1;
            }
        }
    }
    return dist;
}

/**
Implements Dijkstra's shortest path algorithm.
It takes for input a Graph g whose edges must have a positive "length" property (the
algorithm expect a length stored as a double). It's a O(N+E) algorithm, where
N is g's number of nodes and E its number of edges.

A optional parameter, checkForNegativeLength (default to false, no check) forces
the function to verify that each encountered edge length is not negative. It will
throw an Exception if such an edge is found.

Returns:
As the other 'shortest path' algortihm in this module,
dijkstra returns a tuple which has for first field an array containing
the shortest distance from begin to the other nodes (a $(D double[node]) associative array).
If a node cannot be reached, the distance is ($D double.max).
The second field contains the predecessor of each node in their path to begin: a Node[Node] array.
*/
Tuple!(double[Node], Node[Node])
dijkstra(Graph g, Node begin, bool checkForNegativeLength = false) {
    double[Node] distancesFrom;
    Node[Node] previousNode;
    double[size_t] dist; // Needed because Tuples of structs and my PQ implementation don't mix. Too bad.
    size_t[Node] indexOf; // ditto

    foreach(index, node; g.nodes) {
        indexOf[node] = index;
        dist[index] = double.infinity;
        distancesFrom[node] = double.infinity;
        if (node == begin) {
            dist[index] = 0.0;
            distancesFrom[begin] = 0.0;
        }
    }

    auto H = priorityQueue(dist);
    foreach(u; H) {
        size_t indexOfFrom = u.field[1];
        Node from = g.nodes[indexOfFrom];
        foreach(edge; g.edges[from]) {
            Node to = edge.to;
            size_t indexOfTo = indexOf[to];
            double oldDist = dist[indexOfTo];
            double edgeLength = edge.getProperty!(double)("length");

            if (checkForNegativeLength && (edgeLength < 0.0)) throw new Exception("Dijkstra: negative edge length for edge " ~ edge.toString);

            double newDist = dist[indexOfFrom] + edgeLength;
            if (oldDist > newDist) {
                H.changePriority(indexOfTo, oldDist, newDist);
                dist[indexOfTo] = newDist;
                distancesFrom[to] = newDist;
                previousNode[to] = from;
            }
        }
    }
    return tuple(distancesFrom, previousNode);
}

/**
Implements the Bellman-Ford algorithm for finding the shortest path
in graphs with positive or negative edge length.  It imposes almost
no condition on the graph, but it's a O(N*E) algorithm, where
N is the number of nodes, and E is the number of edges. As such,it could
be slower than dijkstra or dagShortestPath (my own timings on small
graphs show on the contrary Bellman-Ford to be the quickest of the three).

The only condition on the graph is that there must be not negative cycle
(cycles whose total length is negative), but it's a general condition on shortest path algorithms:
if there is a negative cycle, you can take it many times in your path,
each time decreasing the path total length, without limit. An optional argument
checkForNegativeCycle (default value: false) will provoke such a test (it's done at the end
of the computation, so it does not change the global speed of bellmanFord).

As with other 'shortest path' algorithm (dijkstra and dagShortestPath), it takes for input
a Graph and a Node inside the graph and returns a tuple of distances from the node (a double[Node]
associative array) and a previous node tree, on the form of a Node[Node] array.
*/
Tuple!(double[Node], Node[Node])
bellmanFord(Graph g, Node begin, bool checkForNegativeCycle = false) {
    double[Node] distancesFrom;
    Node[Node] previousNode;

    foreach(node; g.nodes) {
        distancesFrom[node] = double.infinity;
    }
    distancesFrom[begin] = 0.0;

    bool updated = true; // For an early exit if the algo converged before the end. See Algorithms.pdf p. 129
    for(int i = 0; (i < g.nodes.length-1) && (updated); ++i) {
        updated = false;
        foreach(node; g.nodes) {
            foreach(edge; g.edges[node]) {
                double edgeLength = edge.getProperty!(double)("length");
                if (distancesFrom[edge.to] > distancesFrom[node] + edgeLength) {
                    distancesFrom[edge.to] = distancesFrom[node] + edgeLength;
                    previousNode[edge.to] = node;
                    updated = true;
                }
            }
        }
    }
    if (checkForNegativeCycle) { // Do one more round of udpates. If some length change, there is a negative cycle.
                                 // See Algorithms.pdf on p. 129
        updated = false;
        foreach(node; g.nodes) {
            foreach(edge; g.edges[node]) {
                double edgeLength = edge.getProperty!(double)("length");
                if (distancesFrom[edge.to] > distancesFrom[node] + edgeLength) {
                    distancesFrom[edge.to] = distancesFrom[node] + edgeLength;
                    previousNode[edge.to] = node;
                    updated = true;
                }
            }
        }
        if (updated) throw new Exception("bellmanFord: there is a negative cycle in the input graph.");
    }
    return tuple(distancesFrom, previousNode);
}

/**
Implements a shortest path algorithm for DAG (Directed Acyclic Graphs).
As these can be linearized (with linearize(Graph g)), there is a simple
O(E) algorithm for them.

The optional argument checkForAcyclicity (default: false) forces a check
on g's acyclicity. In case a cycle is found, an Exception is throw.

As with other 'shortest path' algorithm (dijkstra and bellmanFord), it takes for input
a Graph and a Node inside the graph and returns a tuple of distances from the node (a double[Node]
associative array) and a previous node tree, on the form of a Node[Node] array.
*/
Tuple!(double[Node], Node[Node]) dagShortestPath(Graph g, Node begin, bool checkForAcyclicity = false) {
    if (checkForAcyclicity && !isAcyclic(g)) throw new Exception("dagShortestPath: the input graph is not a DAG.");

    double[Node] distancesFrom;
    Node[Node] previousNode;

    foreach(node; g.nodes) {
        distancesFrom[node] = double.infinity;
    }
    distancesFrom[begin] = 0.0;

    auto linearized = linearize(g);
    foreach(node; linearized.nodes) {
        foreach(edge; g.edges[node]) {
            double edgeLength = edge.getProperty!(double)("length");
            if (distancesFrom[edge.to] > distancesFrom[node] + edgeLength) {
                distancesFrom[edge.to] = distancesFrom[node] + edgeLength;
                previousNode[edge.to] = node;
            }
        }
    }
    return tuple(distancesFrom, previousNode);
}

/**
Gives the shortest path in g between g's nodes from and to. The algorithm
used is selected by the caller with the template parameter algo. Just pass
the name of the function (it defaults to bellmanFord, the most generic but also
in theory the slowest algorithm).

The optional argument check (default: false), if set to true, uses the 'with checks'
version of the algorithm.

Example:
----
Graph g;
Node from, begin;
auto path = shortestPath!(dijkstra)(g, from, to).
----
Returns: a tuple of the path (a Node[] array) and the distance (a double).
*/
Tuple!(Node[], double) shortestPath(alias algo = bellmanFord)(Graph g, Node from, Node to, bool check = false) {
    if (from == to) return tuple([to][], 0.0);

    auto dij = algo(g, from, check);
    double length = dij.field[0][to];
    Node[] path;
    if (isInfinity(length)) return tuple(path, double.infinity);
    path = [to];
    Node current = to;
    do {
        current = dij.field[1][current];
        path ~= current;
    }
    while (current != from);
    return tuple(path.reverse, length);
}

/// the eccentricity of a graph.
size_t eccentricity(Graph g, Node n) {
    enforce((n in g), "Inexistent Node: " ~ n.name);
    auto dist = numNodesFrom(g, n);
    return dist.values.sort[$-1];
}

/// the radius of a graph.
size_t radius(Graph g) {
    size_t result = size_t.max;
    foreach(node; nodes(g)) {
        auto e = eccentricity(g, node);
        if (result > e) result = e;
    }
    return result;
}

/// the diameter of a graph.
size_t diameter(Graph g) {
    size_t result = size_t.min;
    foreach(node; nodes(g)) {
        auto e = eccentricity(g, node);
        if (result < e) result = e;
    }
    return result;
}

/// the accessibility matrix.
size_t[Node][Node] accessibilityMatrix(Graph g) {
    size_t[Node][Node] result;
    foreach(node; nodes(g)) {
        result[node] = numNodesFrom(g, node);

    }
    return result;
}

/**
Extracts the subgraph of g corresponding from the nodes array.
*/
Graph subgraph(Graph g, Node[] nodes) {
    Graph result;
    result.addNodes(nodes);
    foreach(node; nodes) {
        foreach(edge; g.edges[node]) {
            result.addEdge(edge);
        }
    }
    return result;
}

/**
Implements Kruskal's minimum spanning tree algorithm. See algorithms.pdf on p. 139.
The minimum spanning tree of a graph is a tree that connects all the graph's nodes
using lowest possible length/weight for all edges.
Returns: g's spanning tree, as a Graph.
*/
Graph minimumSpanningTree(Graph g) {
    Graph mst;
    Set!(Node)[] NodeSets;
    Edge[] edgesByLength;
    size_t[Node] find;

    foreach(edge; edges(g)) {
        edgesByLength ~= edge;
        find[edge.from] = NodeSets.length;
        NodeSets ~= Set!(Node)(edge.from); // Begin with creating a new one-node set for each node
        find[edge.to] = NodeSets.length;
        NodeSets ~= Set!(Node)(edge.to);
    }
    double l(Edge e) {
        return e.getProperty!double("length");
    }
    sort!((Edge a,Edge b) {return (l(a) < l(b));})(edgesByLength);

    foreach(edge; edgesByLength) {
        Node to = edge.to;
        Node from = edge.from;
        if (find[to] != find[from]) {
            mst.addNode(to);
            mst.addNode(from);
            mst.addEdge(edge);
            NodeSets[find[to]] = fusion(NodeSets[find[to]], NodeSets[find[from]]);
            foreach(node; find.keys) {
                if (find[node] == find[from]) find[node] = find[to];
            }
        }
    }
    return mst;
}
