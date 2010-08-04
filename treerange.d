// Written in the D programming language

/**
This module is just a test, to see how to iterate on a binary or n-ary tree.
This entire module will probably be fused with recursive.d and the graph modules, to make it a coherent whole.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.treerange;

import std.array,
       std.metastrings,
       std.range;

import dranges.functional : naryFun;

/**
The basic node for a binary tree.
*/
class Tree(T) {
    T t;/// Value stored on the node.
    Tree!T left; /// children
    Tree!T right; /// ditto

    this(T t) { this.t = t;}
    this(T t, Tree!T l, Tree!T r) { this.t = t; left = l; right = r;}

    bool hasValue() { return true;}
    T value() { return t;}

    Tree!T[] successors()
    {
        return (left is null) ? ((right is null) ? (Tree!T[]).init : [right]) : ((right is null) ? [left] : [left,right]);
    }

    bool isSink() { return (left is null) && (right is null);}
    alias isSink isLeaf;
}

/**
Helper function to create a Tree!T with no child (a leaf).
*/
Tree!T tree(T)(T t) {
    return new Tree!T(t);
}

/**
To create a Tree!T with children.
*/
Tree!T tree(T)(T t, Tree!T l, Tree!T r) {
    return new Tree!T(t, l, r);
}


/**
The basic node for a n-ary tree.
*/
class NTree(T) {
    T value;
    NTree!T[] children;

    this(T t) { value = t;}
    this(T t, NTree!T[] c) { value = t; children = c;}

    NTree!T[] successors() {
        return children;
    }
}

/**
Helper function to create a NTree!T with no child (a leaf).
*/
NTree!T ntree(T)(T t) {
    return new NTree!T(t);
}

/**
To create a NTree!T with children.
*/
NTree!T ntree(T,R)(T t, R c) if (isInputRange!R && is(ElementType!R == NTree!T) && !isInfinite!R) {
    return new NTree!T(t, array(c));
}

/**
predicate to see if a node is a leaf (a node without children).
*/
bool isLeaf(T)(Tree!T t) { return (t.left is null) && (t.right is null);}

/**
Reduce on a tree: recursively apply fun on the value and the children, to
obtain a unique result.
*/
I reduceTree(alias fun, I, T)(I ifNull, Tree!T tr) {
    return (tr is null) ? ifNull : naryFun!fun(tr.t,
                                       reduceTree!fun(ifNull, tr.left),
                                       reduceTree!fun(ifNull, tr.right));
}

/**
Small functions (one-liners) that use reduceTree, to calculate, respectively:
$(UL
  $(LI The height (depth) of a binary tree)
  $(LI The values in found in a depth-first pre-order iteration. They are returned as an array.)
  $(LI The values in found in a depth-first in-order iteration. They are returned as an array.)
  $(LI The values in found in a depth-first post-order iteration. They are returned as an array.)
  $(LI The maximum value held by a node.)
  $(LI The minimum value held by a node.)
  $(LI The result of applying an binary operation on the node's value
    and the values given by treeReduce on the children (see the examples))
  )

reduceTree is a greedy algorithm.

Examples:
----
auto t0 = tree(0);
auto t1 = tree(1, t0, tree(2));
auto t3 = tree(3, t1, tree(4));
//  t3 is:
//              3
//             / \
//            1   4
//           / \
//          0   2
assert(height(t3) == 3);
assert(preOrder(t3) == [3,1,0,2,4]);
assert(inOrder(t3) == [0,1,2,3,4]);
assert(postOrder(t3) == [0,2,1,4,3]);
assert(max(t3) == 4);
assert(min(t3) == 0);
assert(opTree!"+"(0,t3) == 3+1+4+2+0);
----
*/
int height(T)(Tree!T tr) { return reduceTree!"1 + max(b,c)"(0, tr);}
/// ditto
T[] preOrder(T)(Tree!T tr) { return reduceTree!"a ~ b ~ c"((T[]).init, tr);}
/// ditto
T[] inOrder(T)(Tree!T tr) { return reduceTree!"b ~ a ~ c"((T[]).init, tr);}
/// ditto
T[] postOrder(T)(Tree!T tr) { return reduceTree!"b ~ c ~ a"((T[]).init, tr);}
/// ditto
T max(T)(Tree!T tr) { return reduceTree!"max(a,b,c)"(T.min, tr);}
/// ditto
T min(T)(Tree!T tr) { return reduceTree!"min(a,b,c)"(T.max, tr);}
/// ditto
I opTree(string op, I, T)(I ifNull, Tree!T tr) { return reduceTree!(Format!("a %s b %s c", op,op))(ifNull, tr);}

unittest
{
    auto t0 = tree(0);
    auto t1 = tree(1, t0, tree(2));
    auto t3 = tree(3, t1, tree(4));
    //  t3 is:
    //              3
    //             / \
    //            1   4
    //           / \
    //          0   2
    assert(height(t3) == 3);
    assert(preOrder(t3) == [3,1,0,2,4]);
    assert(inOrder(t3) == [0,1,2,3,4]);
    assert(postOrder(t3) == [0,2,1,4,3]);
    assert(max(t3) == 4);
    assert(min(t3) == 0);
    assert(opTree!"+"(0,t3) == 3+1+4+2+0);
}

/**
Applies function fun to the values of node and then recursively to the children.
It transforms the Tree in place.
TODO:
Maybe another version that can act on the entire Node, modifying the tree's structure.
*/
void transform(alias fun, T)(ref Tree!T tr)
{
    tr.t = unaryFun!fun(tr.t);
    if (!(tr.left is null)) transform(tr.left);
    if (!(tr.right is null)) transform(tr.right);
}

/// A enum that control the mode of traversal on a tree
enum TraversalMode { depthfirst, breadthfirst};

struct Traversal(TraversalMode tm = TraversalMode.depthfirst, T)
{
    T[] nodes;

    this(T t) { nodes = [t];}
    bool empty() { return nodes.empty;}
    T front() { return nodes.front;}
    @property Traversal save() { return this;}
    void popFront() {
        if (!nodes.empty) {
            auto cn = nodes.front; // current node
            nodes.popFront;
            static if (tm == TraversalMode.depthfirst)
                nodes = cn.successors ~ nodes;
            else
                nodes ~= cn.successors;
        }
    }
}

/**
Returns a range to iterate on a tree nodes. The mode of traversal is a template
parameter and can be depthfirst (the default) or breadthfirst.
Note:
    it iterates on the tree nodes, not the content of the nodes. Maybe I should change this.
Usage:
----
auto depthf = traversal(t);
auto breadthf = travseral!(TraversalMode.breadthfirst)(t);
----
*/
Traversal!(tm, T) traversal(TraversalMode tm = TraversalMode.depthfirst, T)(T treelike)
{
    return Traversal!(tm, T)(treelike);
}

struct AsTrie(T)
{
    Tree!T tree;
    Tree!T[][] nodes; // array of paths from the root to the current node

    this(Tree!T t) { tree = t; nodes = [[t]];}
    bool empty() { return nodes.empty;}
    Tree!T[] front() { return nodes.front;}
    @property AsTrie save() { return this;}
    void popFront() {
        if (!nodes.empty) {
            auto pcn = nodes.front; // path to the current node
            nodes.popFront;
            Tree!T[][] ps; // paths to successors
            foreach(succ; pcn.back.successors) ps ~= (pcn ~ succ);
            nodes = ps ~ nodes;
        }
    }
}

/**
Produces a range to iterate in a standard tree as if it was a trie: the elements are
arrays of all elements traversed from the root to the current focus of iteration.
Example:
----
// t3 is the same tree used before for heigth/preorder, etc.
//
//              3
//             / \
//            1   4
//           / \
//          0   2
auto trie = asTrie(t3);
auto values = map!("array(map!\"a.t\"(a))")(trie); // The strange double map is to convert the nodes ot their values.
assert(equal(values, [[3], [3,1], [3,1,0], [3,1,2], [3,4]]));
----
*/
AsTrie!T asTrie(T)(Tree!T tree)
{
    return AsTrie!T(tree);
}
