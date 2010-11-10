// Written in the D programming language

/**
This is a module to deal with tuples as trees: polymorphic trees, like this:
----
Tuple!(int, Tuple!(string, char), double, Tuple!(string, Tuple!(string, char))) tree;
----
And then reducing them, mapping functions on them, etc. My goal is to link it with the pattern-matching modules.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.tupletree;

import std.functional,
       std.stdio,
       std.traits,
       std.typecons,
       std.typetuple;

import dranges.functional,
       dranges.templates,
       dranges.tuple,
       dranges.traits,
       dranges.tuple,
       dranges.typetuple;
//
//struct Empty {}
//struct Node(T, C...) if (allSatisfy!(isNode!T, C))
//{
//    T data;
//    C children;
//}
//
//template isNode(T)
//{
//    template isNode(N)
//    {
//        static if (is(N == Empty)
//               || (isInstanceOf!(N, Node) && is(TPTT!(N)[0] == T)))
//            enum bool isNode = true;
//        else
//            enum bool isNode = false;
//    }
//}
//
//template TPTT(T)
//{
//    mixin("alias TypeTuple!(" ~ between!('(',')',T.stringof)[1] ~ ") TPTT;");
//}
//
//Empty empt() { return Empty();}
//Node!(T,C) node(T, C...)(T payload, C children) if (allSatisfy!(isNode!T, C))
//{
//    return Node!(T,C)(payload, children);
//}
//

/**
A well-formed heterogeneous tree has the form $(M tuple(payload, children...)) where children
are trees themselves. $(M payload) can be of any type and is always there, except for the empty tree
(which is a PITA to deal with compared to normal/leaf trees and so may be discarded).
Here are some h-trees examples:
----
auto e  = tuple(); // an (the) empty tree.
auto l1 = tuple(1); // leaf (payload == 1), no children.
auto l2 = tuple("a"); // another leaf, with a string payload: "a".

auto t1 = tuple((int i, string s) { return i+s.length;}, l1, l2); // a tree. Its payload is an anonymous function.

auto t2 = tuple('a',               // Homogeneous tree encoded as a tuple-tree
                    tuple('b',
                                tuple('c'), tuple('d')),
                    tuple('e',
                                tuple('f')),
                    tuple('g'));

auto t3 = tuple( tuple(1), tuple(2), tuple(3) ); // t3 payload is tuple(1) (not particularly seen as a tree in this context), and two children (leaves)
----
*/
template isTree(T)
{
    static if (isEmptyTree!T || isLeaf!T
                         || (isTuple!T && allSatisfy!(isTree, T.Types[1..$]))) // tuple( _ , tupleList...), standard node, recursive check on the tuple list
        enum isTree = true;
    else
        enum isTree = false;
}

/// Is true iff T is an empty tree.
template isEmptyTree(T)
{
    static if (isTuple!(T) && T.Types.length == 0) // empty tree
        enum isEmptyTree = true;
    else
        enum isEmptyTree = false;
}

/// Is true iff T is a leaf.
template isLeaf(T)
{
    static if (isTuple!(T) && T.Types.length == 1) // leaf
        enum isLeaf = true;
    else
        enum isLeaf = false;
}

/**
Convenience functions to create trees.
*/
Tuple!() emptyTree() { return tuple();}

/// ditto
Tuple!(P) leaf(P)(P payload) { return tuple(payload);}

/// ditto
Tuple!(P, Ch) tree(P, Ch...)(P payload, Ch children) if (allSatisfy!(isTree, Ch))
{
    return tuple(payload, children);
}

/// Returns a tree's payload.
Tr.Types[0] payload(Tr)(Tr tree) if (isTree!Tr && !isEmptyTree!Tr)
{
    return tree[0];
}

/// Returns a tree's children. As D function cannot return naked tuples, the returned value is wrapped in a std.typecons.Tuple.
Tuple!(Tr.Types[1..$]) children(Tr)(Tr tr) if (isTree!Tr && !isEmptyTree!Tr)
{
    return tuple(tr.expand[1..$]);
}

/**
Maps a function $(M fun) on a tree. $(M fun) will be applied on all payloads, so must be a polymorphic function.
$(M mapTree) returns the transformed tree, which has the same shape than the original, but different values.
See_Also $(M dranges.functional.extendFun) to affect only some types and not the other ones, and $(M dranges.tuple.mapTuple).
Note: it's a greedy function, no lazy map here.
*/
template mapTree(alias fun)
{
    auto mapTree(Tr)(Tr tr) if (isTree!Tr)
    {
        static if (isEmptyTree!Tr)
            return emptyTree;
        else static if (isLeaf!Tr)
            return leaf( naryFun!fun(payload(tr)) );
        else // standard, non-leaf node
        {
            // calculating in advance the return type of all successive applications of mapTree!fun on the children
            StaticMap!(RT!(.mapTree!fun), Tr.Types[1..$]) res;
            auto ch = children(tr);
            foreach(i, Type; ch.Types) res[i] = .mapTree!fun(ch[i]);
            return tree(unaryFun!fun(payload(tr)), res);
        }
    }
}

/**
Reduces a tree down to one value (which may very well be a complicated structure in itself, like another tree).
You must provide two polymorphic functions: $(M onLeaf), which is called on all leaves and $(M onBranch) which
is called on all non-leaf values.
*/
template reduceTree(alias onLeaf, alias onBranch)
{
    auto reduceTree(Tr)(Tr tr) if (isTree!Tr)
    {
        static if (isLeaf!Tr)
            return unaryFun!onLeaf(payload(tr));
        else
        {
            StaticMap!(RT!(.reduceTree!(onLeaf, onBranch)), Tr.Types[1..$]) res;
            auto ch = children(tr);
            foreach(i, Type; ch.Types) res[i] = .reduceTree!(onLeaf, onBranch)(ch[i]);
            return naryFun!onBranch(payload(tr), res);
        }
    }
}
