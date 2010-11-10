// Written in the D programming language

/**
Some algorithms on graphs: extracting the meta-graph, finding path
in the graph and such.

The most complicated algorithms in this module come from their descriptions in
<a href = "http://www.cs.berkeley.edu/~vazirani/algorithms.html">this book</a>.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.graphalgorithm;

import std.algorithm,
       std.conv,
       std.exception,
       std.math,
       std.range,
       std.stdio,
       std.string,
       std.typecons;

import dranges.graph,
       dranges.graphrange,
       dranges.priorityqueue,
       dranges.queue,
       dranges.set;

/**
Returns: the complement graph of g: same nodes, but complementary edges:
for each pair (u,v) in g.nodes, if (u,v) is in g, then it's not in the complement.
Conversely, if (u,v) is not in g, then it's an edge in the complement.
See_Also: $(M reversedGraph).

TODO: conserve the edge properties
*/
Graph!(N,E) complementGraph(N,E)(Graph!(N,E) g) {
    Graph!(N,E) result;
    result.addNodes(g.nodes);
    foreach(n1; g.nodes) {
        foreach(n2; g.nodes) {
            auto e = edge(n1.label, n2.label);
            if (e !in g)
            {
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
Graph!(N,E) completedGraph(N,E)(Graph!(N,E) g) {
    Graph!(N,E) result;
    result.addNodes(g.nodes);
    foreach(n1; g.nodes) {
        foreach(n2; g.nodes) {
            result.addEdge(n1, n2);
        }
    }
    return result;
}

/**
Returns:
The reverse graph of g: same nodes, edges inverted
(ie: an edge going from A to B becomes an edge from B to A).
This graph is useful in certain algorithms, like decomposing
a graph into its strongly connected components and creating its metagraph.
Note:
it's not smart enough to reverse the edges' classification, if any (that would
need distinguishing between forward and tree edges).
See_Also:
isAcyclic(Graph g).
BUG: refactoring, the egdes properties such as their length/weight are not properly propagated right now.
*/
Graph!(N,E) reversedGraph(N,E)(Graph!(N,E) g)
{
    Graph!(N,E) result;
    result.addNodes(g.nodes);

    foreach(edge; g.edges)
    {
        result.addEdge(edge.to, edge.from);
    }
    return result;
}

/**
Explore a graph g from the node labeled l. The use of recursion makes it similar to depth-first
traversal.
Returns :
An array of labels, which are the nodes reachable from node l.
*/
Label!N[] explore(N,E,L)(Graph!(N,E) g, L l, bool[L] visited = (bool[L]).init) if (is(Label!N == L))
{
    Label!N[] result = [l];
    visited[l] = true;
    foreach(edge; g._edges[l])
    {
        if (!(edge.to in visited) || !visited[edge.to])
        {
            result ~= explore(g, edge.to, visited);
        }
    }
    return result;
}

/**
Returns:
As a list of list of labels, the undirected graph connected components: the groups of nodes that are connected together.

For example:
----
[["A","B"], ["C"], ["D", "E", "F"]]
----
means that A and B have a common edge, that C is alone and that D, E and F can be reached from one another.

BUG: UndirectedGraph is being redesigned.
*/
Label!N[][] connectedComponents(N,E)(UndirectedGraph!(N,E) g) {
    Label!N[][] result;
    bool[Label!N] visited;
    foreach(label; g.labels) visited[label] = false;

    Label!N[] explore(Label!N l)
    {
        Label!N[] result = [l];
        visited[l] = true;
        foreach(edge; g._edges[l])
        {
            if (!visited[edge.to]) result ~= explore(edge.to);
        }
        return result;
    }

    foreach(label; g.labels)
    {
        if (!visited[label]) result ~= explore(label);
    }
    return result;
}

/**
Returns:
In a tuple, the nodes sorted by decreasing post number and the pre and post-visit timings of g nodes, in associative arrays pre and post.
*/
Tuple!(Label!N[], int[Label!N], int[Label!N]) clock(N,E)(Graph!(N,E) g)
{
    bool[Label!N] visited;
    Label!N[] postOrdered;
    int[Label!N] pre, post;
    int clock = 1;
    foreach(label; g.labels) visited[label] = false;

    void explore(Label!N l)
    {
        visited[l] = true;
        pre[l] = clock; // pre-visit number
        clock++;
        foreach(edge; g._edges[l])
        {
            if (!visited[edge.to]) explore(edge.to);
        }
        post[l] = clock; // post-visit number
        clock++;
        postOrdered ~= l;
    }

    foreach(label; g.labels)
    {
        if (!visited[label]) explore(label);
    }

    return tuple(postOrdered.reverse, pre, post);
}

/**
Returns:
The list of strongly connected components of g. That is, the nodes of sub-graphs
where all nodes can be reached from one another.
*/
Label!N[][] stronglyConnectedComponents(N,E)(Graph!(N,E) g)
{
    Label!N[] postOrder = clock(reversedGraph(g))._0; // nodes sorted by decreasing post-order, for the inverted graph
    Label!N[][] scc;
    bool[Label!N] visited;
    foreach(label; postOrder) {visited[label] = false;}

    Label!N[] explore(Label!N l)
    {
        Label!N[] result = [l];
        visited[l] = true;
        foreach(edge; g._edges[l])
        {
            if (!visited[edge.to]) result ~= explore(edge.to);
        }
        return result;
    }

    foreach(label; postOrder)
    {
        if (!visited[label]) scc ~= explore(label);
    }
    return scc;
}

/**
Returns:
The subgraphs created by the strongly connected components of a graph.
*/
Graph!(N,E)[] subGraphs(N,E)(Graph!(N,E) g)
{
    auto components = stronglyConnectedComponents(g);
    Graph!(N,E)[] subgraphs;
    foreach(component; components)
    {
        Graph!(N,E) sg;
        foreach(label; component)
        {
            sg.addNode(g[label]);
        }
        foreach(label; component)
        {
            foreach(edge; g._edges[label]) {
                sg.addEdge(edge); // works because outward pointing edges won't be added (the link to invalid nodes)
            }                               // I could also test is edge.to points into component
        }
        subgraphs ~= sg;
    }
    return subgraphs;
}

/**
Returns:
The meta-graph associated to g. That's the graph whose nodes are the subgraphs of g
and the edges the edges between these subgraphs. The meta-graph nodes labels are the concatenation
of each subgraphs nodes labels (cast to strings). The subgraphs are stored as the nodes values. This operation
is also sometimes called the compaction, reduction or shrinking of a graph.

Note:
It could be coded more efficiently: all these successsive functions ($(M reversedGraph) - $(M clock)
- $(M stronglyConnectedComponents) - $(M subGraphs) - $(M metaGraph)) could be integrated into one metagraph function: some
work is duplicated: while we extract the scc, we could create the metanodes and their names, and
get the outgoing edge without having to painfully find them afterwards as is done there.
But I'm aiming at making it work first. For my graphs, it takes a fraction of second to find the MG.

Note:
I could also ask for a $(M labelize) function that'd creates the metagraph nodes labels from
the original labels, instead of casting them to string and concatenating them.
*/
Graph!(Node!(string, Graph!(N,E)), Edge!string) metaGraph(N,E)(Graph!(N,E) g) {
    auto subgraphs = subGraphs(g);
    Graph!(Node!(string, Graph!(N,E)), Edge!string) metagraph;
    string[Label!N] metaedges; // Helper array to find, when I have a node (extremities of an outgoing edge),
                                // which subgraph (and so, metanode -> node in the metagraph) has this particular node.

    foreach(subgraph; subgraphs) // Creating metanodes
    {
        string names;
        foreach(label; subgraph.labels) names ~= label;
        auto metanode = node(names, subgraph);

        foreach(label; subgraph.labels) metaedges[label] = metanode.label;

        metagraph.addNode(metanode);
    }

    foreach(subgraph; subgraphs) // finding edges between subgraphs
    {
        foreach(label; subgraph.labels)
        {
            if (subgraph._edges[label].length != g._edges[label].length) // This node has edges pointing to other subgraphs
            {
                foreach(edge; g._edges[label])
                {
                    if (!subgraph.isValidNode(edge.to)) // Node not existing in the subgraph, but existing in the original graph
                    {
                        metagraph.addEdge(metaedges[label], metaedges[edge.to]);
                    }
                }
            }
        }
    }

    return metagraph;
}

///
enum EdgeClassification {TreeForward, Back, Cross};

/**
Classify edges between Tree&Forward edges, back edges and cross edges, without distinguishing
between Tree and Forward. It returns this property map as an associative array.
*/
EdgeClassification[E] classifyEdges(N,E)(Graph!(N,E) g) {
    EdgeClassification[E] classification;
    auto clockedNodes = clock(g); // Tuple!(Node[], int[Node], int[Node])
    auto pre = clockedNodes._1; // pre-order number for g's nodes
    auto post = clockedNodes._2; // post-order number

    EdgeClassification classify(int u1, int u2, int v1, int v2) {
        if ((u1<v1) && (v2<u2)) { // v inside u
            return EdgeClassification.TreeForward; // could be Tree or Forward
        }
        else if ((v1<u1) && (u2<v2)) { // u inside v
            return EdgeClassification.Back;
        }
        else
        {
            return EdgeClassification.Cross;
        }

    }

    foreach(label; g.labels) {
        foreach(edge; g._edges[label]) {
            classification[edge] = classify(pre[label], post[label], pre[edge.to], post[edge.to]);
        }
    }
    return classification;
}

/**
Returns: True if the graph is acyclic, false otherwise.
*/
bool isAcyclic(N,E)(Graph!(N,E) g) {
    auto clockedNodes = clock(g); // Tuple!(Node[], int[Node], int[Node])
    auto pre = clockedNodes._1; // pre-order number for g's nodes
    auto post = clockedNodes._2; // post-order number

    foreach(label; g.labels) {
        foreach(edge; g._edges[label]) {
            if ((pre[edge.to] < pre[label]) && (post[label] < post[edge.to])) { // Back edge -> cyclic
                return false; // -> early out
            }
        }
    }
    return true;
}

/**
Returns:
The linearized version of a Directed Acyclic Graph (DAG). As there is no static way
to know if a Graph is a DAG, you can use the flag testForAcyclic to decide if
you want to test or not.
TODO: either a DAG struct, or an AssumeAcyclic!Graph template.
*/
Graph!(N,E) linearize(N,E)(Graph!(N,E) g, bool testForAcyclic = false)
{
    if (testForAcyclic && !isAcyclic(g)) {
        throw new Exception("The input graph has at least a cycle. I cannot linearize a cyclic graph.");
    }
    Graph!(N,E) linearized;
    foreach(label; clock(g)._0)
    {
        linearized ~= g[label];
    }
    foreach(int i, N node; linearized.nodes[0..$-1]) {
        linearized.addEdge(node.label, linearized.nodes[i+1].label);
    }
    return linearized;
}


/**
Returns:
The distance (in number of nodes) between node from and all other nodes, as an associative array.
The distance _from from to from is 0.
if node B is not reachable from node A, distanceFrom(g, A)[B] = int.max. Why not -1? Because
it's not correctly ordered with other distance and some functions here (like the radius or diameter
or a graph) sort node-distances.
Remark:
another solution would be not to include B as a key in the associative array, maybe.
*/
int[Label!N] numNodesFrom(N,E,L)(Graph!(N,E) g, L from) if (is(Label!N == L))
{
    int[Label!N] dist;
    foreach(label; g.labels) dist[label] = int.max;
    dist[from] = 0;

    Queue!(Label!N) queue = Queue!(Label!N)(g.size);
    queue.push(from);
    while (!queue.empty) {
        Label!N u = queue.pop;
        foreach(v; g._edges[u]) {
            if (dist[v.to] == int.max) {
                queue.push(v.to);
                dist[v.to] = dist[u] + 1;
            }
        }
    }
    return dist;
}

/**
Returns: the distance matrix for g: the distance (in number of nodes)
from node a to node b, far all nodes in the graph. It returns it as
a double associative array. result[label1][label2] is the distance from 1
to 2. If there is not path, the distance is $(D int.max).
TODO: make it more efficient. $(M numNodesFrom) already makes a big part of the job.
*/
int[Label!N][Label!N] distanceMatrix(N,E)(Graph!(N,E) g)
{
    int[Label!N][Label!N] matrix;
    foreach(label; g.labels)
    {
        matrix[label] = numNodesFrom(g, label);
    }
    return matrix;
}

/**
Implements Dijkstra's shortest path algorithm.
It takes for input a Graph g which edges must have a positive "length" property
which must be numerical (castable to $(D double)) and a beginning label. It's a $(D O(n+e)) algorithm, where
$(M n) is number of nodes in g and $(M e) its number of edges.

An optional parameter, checkForNegativeLength (defaults to $(D false), no check) forces
the function to verify that each encountered edge length is not negative. It will
throw an Exception if such an edge is found.

Returns:
As the other 'shortest path' algorithms in this module,
$(M _dijkstra) returns a tuple which has for first field an array containing
the shortest distance from begin to the other nodes (a $(D double[node]) associative array).
If a node cannot be reached, the distance is $(D double.infinity).
The second field contains the predecessor of each node in their path to begin: a Label!N[Label!N] array.

TODO: see to this internal index problem.
*/
Tuple!(double[Label!L], Label!N[Label!N]) dijkstra(N,E,L)(Graph!(N,E) g, L begin, bool checkForNegativeLength = false)
    if (   is(Label!N == L)
        && __traits(hasMember, E, "length"))
{
    double[Label!N] distancesFrom;
    Label!N[Label!N] previousLabel;
    double[size_t] dist; // Needed because Tuples of structs and my PQ implementation don't mix. Too bad.
    size_t[Label!N] indexOf; // ditto

    foreach(index, label; g.labels) {
        indexOf[label] = index;
        dist[index] = double.infinity;
        distancesFrom[label] = double.infinity;
        if (label == begin) {
            dist[index] = 0.0;
            distancesFrom[begin] = 0.0;
        }
    }

    auto H = priorityQueue(dist);
    foreach(u; H) {
        size_t indexOfFrom = u._1;
        Label!N from = g.nodes[indexOfFrom];
        foreach(edge; g._edges[from]) {
            Label!N to = edge.to;
            size_t indexOfTo = indexOf[to];
            double oldDist = dist[indexOfTo];
            double edgeLength = edge.length;

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
no condition on the graph, but it's a $(M O(n*e)) algorithm, where
$(M n) is the number of nodes, and $(M e) is the number of edges. As such,it could
be slower than $(M dijkstra) or $(M dagShortestPath) (my own timings on small
graphs show on the contrary Bellman-Ford to be the quickest of the three).

The only condition on the graph is that there must be no negative cycle
(cycles with a negative total length), but it's a general condition on shortest path algorithms:
if there is a negative cycle, you can take it many times in your path,
each time decreasing the path total length, without limit. An optional argument
checkForNegativeCycle (default value: $(D false)) will provoke such a test (it's done at the end
of the computation, so it does not change the global speed of bellmanFord).

Obviously, the graph edges must have a $(M .length) member. This length will be cast to $(D double),
two nodes not connected having a distance of $(D double.infinity).

As with other 'shortest path' algorithm ($(M dijkstra) and $(M dagShortestPath)), it takes for input
a $(M Graph) and the label of a node, and returns a tuple of distances from the node (a $(D double[Label])
associative array) and a previous node tree, in the form of a $(D Label[Label]) array.
*/
Tuple!(double[Label!N], Label!N[Label!N])
bellmanFord(N,E,L)(Graph!(N,E) g, L begin, bool checkForNegativeCycle = false)
    if (   is(Label!N == L)
        && __traits(hasMember, E, "length"))
{
    double[Label!N] distancesFrom;
    Label!N[Label!N] previousNode;

    foreach(label; g.labels) {
        distancesFrom[label] = double.infinity;
    }
    distancesFrom[begin] = 0.0;

    bool updated = true; // For an early exit if the algo converged before the end.
    for(int i = 0; (i < g.nodes.length-1) && (updated); ++i) {
        updated = false;
        foreach(label; g.labels) {
            foreach(edge; g._edges[label]) {
                double edgeLength = edge.length;
                if (distancesFrom[edge.to] > distancesFrom[label] + edgeLength) {
                    distancesFrom[edge.to] = distancesFrom[label] + edgeLength;
                    previousNode[edge.to] = node;
                    updated = true;
                }
            }
        }
    }
    if (checkForNegativeCycle) { // Do one more round of udpates. If some length change, there is a negative cycle.
        updated = false;
        foreach(label; g.labels) {
            foreach(edge; g._edges[label]) {
                double edgeLength = edge.length;
                if (distancesFrom[edge.to] > distancesFrom[label] + edgeLength) {
                    distancesFrom[edge.to] = distancesFrom[label] + edgeLength;
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

As with other 'shortest path' algorithm ($(D dijkstra) and $(D bellmanFord)), it takes for input
a $(D Graph) and a label inside the graph and returns a tuple of distances from the node (a $(D double[Label!N])
associative array) and a previous node tree, in the form of a $(D Node[Node]) array.
*/
Tuple!(double[Label!N], Label!N[Label!N]) dagShortestPath(N,E,L)(Graph!(N,E) g, L begin, bool checkForAcyclicity = false)
    if (   is(Label!N == L)
        && __traits(hasMembers, E, "length"))
{
    if (checkForAcyclicity && !isAcyclic(g)) throw new Exception("dagShortestPath: the input graph is not a DAG.");

    double[Label!N] distancesFrom;
    Label!N[Label!N] previousNode;

    foreach(label; g.labels) {
        distancesFrom[label] = double.infinity;
    }
    distancesFrom[begin] = 0.0;

    auto linearized = linearize(g);
    foreach(label; linearized.labels) {
        foreach(edge; g.edges[label]) {
            double edgeLength = edge.length;
            if (distancesFrom[edge.to] > distancesFrom[label] + edgeLength) {
                distancesFrom[edge.to] = distancesFrom[label] + edgeLength;
                previousNode[edge.to] = label;
            }
        }
    }
    return tuple(distancesFrom, previousNode);
}

/**
Gives the shortest path in g between g's nodes from and to. The algorithm
used is selected by the caller with the template parameter $(D algo). Just pass
the name of the function (it defaults to $(D bellmanFord), the most generic but also
in theory the slowest algorithm).

The optional argument check (default: false), if set to true, uses the 'with checks'
version of the algorithm.

Returns: a tuple of the distance (a $(D double)) and the path (a $(D Label[]) array) between from and to.
*/
Tuple!(Label!N[], double) shortestPath(alias algo = bellmanFord, N,E,L)(Graph!(N,E) g, L from, L to, bool check = false)
    if (   is(Label!N == L)
        && __traits(hasMember, E, "length"))
{
    if (from == to) return tuple([to][], 0.0);

    auto shortest = algo(g, from, check);
    double length = shortest._0[to];
    Label!N[] path;
    if (isInfinity(length)) return tuple(path, double.infinity);
    path = [to];
    Label!N current = to;
    do {
        current = shortest._1[current];
        path ~= current;
    }
    while (current != from);
    return tuple(length, path.reverse);
}

/// The order of a graph is the maximum valency of its nodes.
size_t order(N,E)(Graph!(N,E) g)
{
    size_t max = size_t.min;
    foreach(l; g.labels)
    {
        auto v = g.valency(l);
        if (max < v) max = v;
    }
    return max;
}

/**
Returns: the eccentricity of a node in a graph. That's
the longest path (in number of nodes) from this node to any other node in the graph.
*/
size_t eccentricity(N,E,L)(Graph!(N,E) g, L label)
    if (is(Label!N == L))
{
    enforce((label in g), "Inexistent Node: " ~ label);
    auto dist = numNodesFrom(g, label);
    return reduce!max(-1, dist);
}

/// the radius of a graph (the smallest excentricity among all nodes)
/// TODO: can probably coded in a more efficient way, I'll see.
size_t radius(N,E)(Graph!(N,E) g)
{
    size_t result = size_t.max;
    foreach(label; g.labels) {
        auto e = eccentricity(g, label);
        if (result > e) result = e;
    }
    return result;
}

/// the diameter of a graph, ie its highest excentricity among nodes.
size_t diameter(N,E)(Graph!(N,E) g)
{
    size_t result = size_t.min;
    foreach(label; g.labels) {
        auto e = eccentricity(g, label);
        if (result < e) result = e;
    }
    return result;
}


/**
Extracts the subgraph of g corresponding from the nodes array.
*/
Graph!(N,E) subgraph(N,E)(Graph!(N,E) g, L[] labels)
    if (is(Label!N == L))
{
    Graph!(N,E) result;
    foreach(label; labels) result.addNode(g[label]);
    foreach(label; labels) {
        foreach(edge; g._edges[labels])
        {
            if (edge.to in result) result.addEdge(edge);
        }
    }
    return result;
}

/**
Implements Kruskal's minimum spanning tree algorithm.
The minimum spanning tree of a graph is a tree that connects all the graph's nodes
using lowest possible length for all edges. The edges must have a $(M .length) member.
Returns: g's spanning tree, here as a Graph.
*/
Graph!(N,E) minimumSpanningTree(N,E)(Graph!(N,E) g)
    if (__traits(hasMember, T, "length"))
{
    Graph!(N,E) mst;
    Set!(Label!N)[] LabelSets;
    Edge[] edgesByLength;
    size_t[Label!N] find;

    foreach(edge; g.edges)
    {
        edgesByLength ~= edge;
        find[edge.from] = LabelSets.length;
        LabelSets ~= Set!(Label!N)(edge.from); // Begin with creating a new one-node set for each node
        find[edge.to] = LabelSets.length;
        LabelSets ~= Set!(Label!N)(edge.to);
    }

    sort!((Edge a,Edge b) {return (a.length < b.length);})(edgesByLength);

    foreach(edge; edgesByLength)
    {
        auto to = edge.to;
        auto from = edge.from;
        if (find[to] != find[from])
        {
            mst.addNode(to);
            mst.addNode(from);
            mst.addEdge(edge);
            LabelSets[find[to]] = dranges.set.fusion(LabelSets[find[to]], LabelSets[find[from]]);
            foreach(label; find.keys)
            {
                if (find[label] == find[from]) find[label] = find[to];
            }
        }
    }
    return mst;
}

/**
Returns:
a string giving the graph representation using the dot language, from Graphviz.

Also, writes the file $(M name).dot to the current directory.

Caution:
This is just a helper/debugging function to easily visualize the graphs. Use with caution.
*/
string toGraphviz(N,E)(Graph!(N,E) g, string name = "graph")
{
    string gv = "digraph G { ratio = 1.0;";
    foreach(e; g.edges)
    {
        gv ~= "\"" ~ to!string(e.from) ~ ":" ~ to!string(g[e.from].value) ~ "\" -> \""~ to!string(e.to) ~ ":" ~ to!string(g[e.to].value) ~ "\";";
    }
    gv ~= "}";
    std.file.write(name~".dot", gv);
    return gv;
}

/// ditto
string toGraphviz(N,E)(UndirectedGraph!(N,E) g, string name = "graph")
{
    string gv = "graph G { ratio = 1.0;";
    bool[Label!N[]] visited;
    foreach(e; g.edges)
    {

        if ([e.to, e.from] !in visited)
        {
            gv ~= "\"" ~ to!string(e.from) ~ ":" ~ to!string(g[e.from].value) ~ "\" -- \""~ to!string(e.to) ~ ":" ~ to!string(g[e.to].value) ~ "\";";
            visited[[e.from, e.to]] = true;
        }
    }
    gv ~= "}";
    std.file.write(name~".dot", gv);
    return gv;
}

/**
Given a module name, $(M _dependencyGraph) will explore its code, extract the import statements and recursively visit the corresponding modules.
If you don't want it to visit the $(D std.*) or $(D core.*) part, juste use:
----
auto dg = dependencyGraph("myModule");
----
If you want it to explore the std.* and core.* modules, you must give it the directory where $(D DMD) is installed. It will then calculate the dependency
graph of $(D Phobos) and the runtime along your own project's graph. Use like this:
----
auto dg = dependencyGraph("myModule", r"C:\dmd\");
toGraphviz(dg, "imports");
// then, in a command line: >> dot -Tpdf imports.dot -o imports.pdf
----
Returns: a $(M Graph), with nodes the modules names and edges pointing to imported modules.

BUG: I don't get how $(D core.*) is organized. For now, it doesn't visit the core modules. It create them in the graph, though.
*/
/*Graph!(Node!(string, string), Edge!string) dependencyGraph(string moduleName, string DMDPath = "")
{
    Graph!(Node!(string, string), Edge!string) g;
    auto ig = dependencyGraphImpl(moduleName, DMDPath);
    Node!(string,string)[string] toNode;
    foreach(n, edgeList; ig)
    {
        g.addNode(node(n,n));
        g.addEdges(n, edgeList);
    }
    return g;
}*/

enum string[string] dmdPaths = ["core":r"src\druntime\src\",
                                "std":r"src\phobos\"];

/* A problem with std.algorithm.startsWith in 2.050
string[][string] dependencyGraphImpl(string moduleName, string DMDPath = "",  string[][string] deps = (string[][string]).init)
{
    if (moduleName in deps) return deps; // already explored

    string path;
    auto withSlashes = replace(moduleName, ".", "\\") ~".d";
    if (startsWith(moduleName, "std."))
    {
        if (DMDPath == "")
        {
            deps[moduleName] = (string[]).init;
            return deps;
        }
        path = DMDPath ~ dmdPaths["std"] ~ withSlashes;
    }
    else if (moduleName.startsWith("core."))
    {
        deps[moduleName] = (string[]).init;
        return deps; // core.* : I don't get how it works and from where it imports.
//        path = DMDPath ~ dmdPaths["core"] ~ withSlashes;
    }
    else // local module
    {
        path = withSlashes;
    }

    string[] imports;
    auto F = File(path);
    auto bsc = F.byLine(F.KeepTerminator.no, ';'); // we will iterate on F by semicolon-delimited chunks

    immutable string[] importTypes = ["import ", "public import ", "static import "];

    foreach(block; bsc)
    {
        auto sblock = strip(block);
        foreach(it; importTypes)
        {
            if (startsWith(sblock, it)) // We have an import
            {
                sblock = sblock[it.length..$];
                auto spl = to!(string[])(split(sblock, ","));
                foreach(index, ref imp; spl)
                {
                    auto i = std.string.indexOf(imp,'=');
                    auto j = std.string.indexOf(imp,':');
                    if (i != -1) // import foo = std.stio, ...
                    {
                        imp = strip(imp[i+1..$]);
                    }
                    if (j != -1)  // import std.io: writeln, writefln; -> discard everithing after the ':', even beyond the first comma.
                    {
                        imp = imp[0..j];
                        spl = spl[0..index]; // Uh, but I got to break the iteration
                    }
                }
                imports ~= array(map!strip(spl));
                break; // no need to test the other import types
            }
        }
    }
    F.close; // not needed anymore.
    deps[moduleName] = imports;

    foreach(i, imp; imports) // recursive exploration
    {
        if (!(imp in deps)) // dependency found for the first time
        {
            auto deps2 = dependencyGraphImpl(imp, DMDPath, deps);
            if (deps2 != deps) foreach(mod, depList; deps2) deps[mod] = depList; // fusing AA
        }
    }
    return deps;
}*/
