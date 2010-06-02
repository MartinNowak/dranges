module tupletree;

import std.traits;
import std.typetuple;

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

