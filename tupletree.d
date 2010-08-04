// Written in the D programming language

/**
To Be Documented. This will become a module to deal with trees as tuples: polymorphic trees, like this:
----
Tuple!(int, Tuple!(string, char), double, Tuple!(string, Tuple!(string, char))) tree;
----
And then reducing them, mapping functions on them, pattern matching with templates on them, etc.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module tupletree;

import std.traits,
       std.typetuple;

import dranges.templates;

struct Empty {}
struct Node(T, C...) if (allSatisfy!(isNode!T, C))
{
    T data;
    C children;
}

template isNode(T)
{
    template isNode(N)
    {
        static if (is(N == Empty)
               || (isInstanceOf!(N, Node) && is(TPTT!(N)[0] == T)))
            enum bool isNode = true;
        else
            enum bool isNode = false;
    }
}

template TPTT(T)
{
    mixin("alias TypeTuple!(" ~ between!('(',')',T.stringof)[1] ~ ") TPTT;");
}

Empty empt() { return Empty();}
Node!(T,C) node(T, C...)(T payload, C children) if (allSatisfy!(isNode!T, C))
{
    return Node!(T,C)(payload, children);
}

