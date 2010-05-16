/**
This modules explores the possibility of '_recursive' or 'branching' ranges, like trees or graphs. It a work-in-progress,
as I'm not quite sure of the semantics yet (empty/hasValue..., should filter conserve the entire topology?)

$(T Ranges:)

A range defines $(M empty)/$(M front)/$(M popFront) as the standard way to iterate, possibly
completed by some other functions. Given an element as front, there no ambiguity as to where to
go next: there is only one next element, giving rise to a linear range of values (hence the name).
You could instead use other methods, like $(M hasNext)/$(M next) ($(M next) popping the front and returning
the successor). You can complete it with $(M front), if you want to cache the current element to access
it many times (calling $(M next) many times would advance the range).

$(T Recursive (or Branching) Ranges:)

A _recursive range is somewhat similar, but based on a tree: given an _recursive range,
the presence of a valid node is given by $(M hasValue). If OK, the current node's value
is returned by a method named $(M value). The $(M successors) method
then returns a range of children, each of these children being itself a _recursive range of the same type.
This range of children is traditionally an array, but it could be lazy and even infinite.
If $(M successors) returns an empty range, then the current node is a sink in the graph, or leaf in tree parlance. Note
that the classical end condition for algorithms crawling trees or graphs is to test for leaves, not for empty.
Indeed, $(M empty) is useful only at the very beginning to test for the validity of a _recursive range or
after filtering a recursive range (see $(M rfilter)).

There is no $(M popFront) equivalent: there is no natural next element, though depth-first (pre- or post-order)
and breadth-first iterations are standard.
You will find here traversal functions called $(M depthFirst) and $(M breadthFirst), that constructs a linear range
from a _recursive range. That way, you can use all the standard linear algorithms on a _recursive range.

These methods $(M hasValue)/$(M value)/$(M successors) are what defines an input _recursive range.
There is a corresponding template, $(M isInputRecursiveRange). From now on, I'll use
r-range as a shorter term for '_recursive range'.

Given a non-empty r-range, a method $(M isSink) is trivial:
----
bool isSink() { return successors.empty;}.
----
It's good practice to expose it in a r-range, as it's the terminating condition for many algorithms and is linked to infinite depth (see below).
Maybe it should be part of an r-range definition?

$(T Forward Recursive Ranges:)

If you can copy the r-range into a variable, to store its state and restore it later, you have the equivalent
of a forward range, here named a forward _recursive range, with its companion template $(M isForwardRecursiveRange).

$(T Infinity:)

These simple functions give rise to two kinds of infinity: infinite breadth if successors returns an infinite range,
infinite height if there is no leaf in the range: the range returned by $(M successors) always have at least one element.
As some part of the range may be finite,
while other parts are infinite (a situation not possible for an infinite linear range), this is somewhat complicated. As such,
the template $(M hasInfiniteBreadth) is global: it alias itself to true iff $(M successors) returns an infinite range. This
is local at first view, but since the return type of $(M successors) is defined in the node type, the infinity of this range
is deinfed at creation, and so is the same for all nodes inside the r-range. Use $(M hasInfiniteBreadth) before iterating on the children of a node.

As for $(M hasInfiniteHeight), it tests if $(M isSink) is statically false.

$(T Length, depth:)

There is no simple, generic $(M length) equivalent, though some _recursive ranges could know the total number of their nodes accessible
from the current node, with a method called $(M size).
As with linear ranges, a template $(M hasSize) tests for its presence, and a walkLength equivalent can be done. A r-range that's infinite
in any direction (downward, upward, or sideways) cannot have a $(M size) method.

In parallel, a $(M height) method can give the max number of successors levels downstream. Its companion template is $(M hasHeight). An infinite
depth range cannot have a $(M height) method, in the same way than an infinite range has no valid $(M length) member.

A $(M breadth) method is not required, as it's the length of the successors range, if it has one. So $(M hasBreadth) just test for $(M length)
member in $(M successors)' return type. Obviously, a r-range with infinite breadth has no valid $(M breadth) member.

$(T Cycles:)

Note that $(M successors) returns a range of nodes, so the current node can be in the list directly or somewhere downstream,
thus creating a cycle. Graphs can contain cycles, but trees must not.
I see no way to statically test for a r-range having cycles or not, and thus testing if a r-range is a graph or a tree
(there is another condition to be a tree: its predecessors range must have a length of at most 1). This kind of condition
must be enforced by factory functions.

$(T Going Up, With Bidirectional Recursive Ranges:)

Up to now, there has been no way to go upstream, to the root of the current node. A r-range can define a $(M predecessors) method returning
a range of predecessors (nodes with the current node in their successors ranges). A node with no predecessor is a source (or
root for a tree), tested with $(M isSource)/$(M isRoot). The (untestable at compile-time) contract is that
if a node n0 is in the ancestors range of a node n1, then n1 is in the successors range of n0.

A r-range defining $(M predecessors) is a bidirectional _recursive range, its associated template being $(M isBidirectionalRecursiveRange).
There is no equivalent to $(M back) for a r-range, as there are many (potentially an infinity) of 'extremity values'.
On the other hand, it's possible to code a generic $(M leaves)/$(M sinks) function that returns a range of all leaves accessible from a beginning node.
The same for a $(M roots)/$(M sources) function going upstream: it's simply a filtering on the nodes.

In complement of $(M height) with the successors of a node, one can define $(M depth) as being the highest number of levels upstream before reaching a source.
Also, we can imagine infinite height r-ranges, albeit this situation seems quite uncommon
(there is nevertheless a $(M hasInfiniteHeight) template).

Bidirectional ranges can be given to $(M retro) which reverses the sense of iteration. What could be the name for a r-range?
Maybe $(M reverse) or $(M upsideDown)?

$(T Output Recursive Ranges:)

Given a subjacent recursive container, a r-range can be used to update the values in the container, with a $(M put) method.
For output ranges, $(M put) puts the value at the front and advances the range, preparing it for the next value.
You cannot do exactly that with a r-range: $(M put) puts the value in the current node (in a range-dependant manner) and returns
$(M successors). A r-range defining $(M put) is an output _recursive range, with $(M isOutputRecursiveRange) as a testing template.

$(T What's Impossible:)

A linear range gives rise to a natural indexing: number the elements, starting from 0 and adding 1 for each call to $(M popFront).
It's nicely parallel to the indexing of arrays and some ranges expose indexing capabilities and slicing, tested by the $(M isRandomAccessRange)
and $(M hasSlicing) templates. No such natural indexing can be defined for recursive ranges, so we have no random-access _recursive range nor
slices on r-ranges. Maybe defining $(M opIndex()) could be interesting, as it's becoming a standard way to return a clone of a range.

And, as range do not (standardly) define an $(M opIndex[key]) like associative arrays do, there is no associative _recursive range, though the idea
could be tried, as associative containers are often implemented as trees. So, maybe there is something possibly interesting.

$(T Topology:)

All this machinery is for iterating on the r-range, accessing its <i>topology</i>, which is the shape encoded with $(M successors)/$(M predecessors).
The values accessible through the r-range are another matter: $(M current) returns a node, not a value. Typically a node will have a $(M value) member.
In parallel with $(M ElementType) for ranges, we can then distinguish the templates $(M NodeType) and $(M ValueType):
$(M NodeType) alias itself to the node type of the r-range (well, duh) and $(M ValueType) is typeof(NodeType.value).

The situation is then, once again, different than for ranges. In a range the topology is implicit, only the values are exposed.
That's what gives ranges their interest as abstractions for many different actions. R-ranges are quite another beast
and are more 'container-like' than ranges (indeed, I'm still trying to see whether they are a good idea or not).
But this separation between the shape and the values permits interesting actions because of the richer information
accessible to iterating functions:
$(UL
    $(LI You can map on the number of children, numbering a node not with its depth/height but with the number of its successors.)
    $(LI You can map and conserve the global shape or lazily expose a new topology.)
    $(LI You can filter on the topology, keeping only leaves for example.)
    $(LI You can test if two r-ranges have the same shape.)
    $(LI You can zip together two r-ranges with the same shape.)
    $(LI If you collapse the structure using reduce, the result will depend on the order of your iteration.)
)
$(T Nodes:)

So, should nodes be value or reference types? In $(D D), structs cannot contain values of the same type, but can contain references to
them. Arrays of $(D Node)s inside a $(D Node) struct are possible, or pointers to $(D Node)s. So, in the end, it's up to you.

$(T Range of ranges:)

Let's compare the situation with range of ranges: they also encode topology (albeit a simpler one), but are not recursive.
At each level of a r-range, the node type is the same and the successors also: it's quite homogeneous.
For ranges of ranges, each level has a different type. Nevertheless, similar actions can be done: you can zip
together ranges of ranges with the same shape, you can project them onto a linear range, etc. (* OK, what else can be said? *).

$(T Comparison with ranges:)

The following table compares the functions for ranges and r-ranges.

$(TABLE
  $(TR $(TH Ranges) $(TH Recursive ranges))
  $(TR $(TD isInputRange) $(TD isInputRecursiveRange))
  $(TR $(TD isForwardRange) $(TD isForwardRecursiveRange))
  $(TR $(TD isBidirectionalRange) $(TD isBidirectionalRecursiveRange))
  $(TR $(TD isRandomAccessRange) $(TD -))
  $(TR $(TD isOutputRange) $(TD isOutputRecursiveRange))
  $(TR $(TD front) $(TD value))
  $(TR $(TD popFront) $(TD successors))
  $(TR $(TD empty) $(TD hasValue/isSink))
  $(TR $(TD back) $(TD -))
  $(TR $(TD popBack) $(TD predecessors))
  $(TR $(TD -) $(TD isSource))
  $(TR $(TD hasLength) $(TD hasSize))
  $(TR $(TD length) $(TD size))
  $(TR $(TD -) $(TD height))
  $(TR $(TD -) $(TD depth))
  $(TR $(TD -) $(TD breadth))
  $(TR $(TD isInfinite) $(TD -))
  $(TR $(TD -) $(TD hasInfiniteBreadth))
  $(TR $(TD -) $(TD hasInfiniteDepth))
  $(TR $(TD -) $(TD hasInfiniteHeight))
)
*/
module dranges.recursive;


import std.algorithm,std.array,std.bigint,std.contracts,std.conv;
import std.functional,std.math,std.metastrings,std.perf;
import std.range,std.random,std.stdio,std.string,std.traits;
import std.typecons,std.typetuple,std.variant;

import dranges.traits2;
import dranges.typetuple2;
import dranges.templates;
import dranges.functional2;
import dranges.predicate;
import dranges.tuple2;
import dranges.range2;
import dranges.algorithm2;

///
template isInputRecursiveRange(T)
{
    enum bool isInputRecursiveRange = is(typeof({
                                               T t;
                                               if (t.hasValue) {};
                                               auto v = t.value;
                                               auto s = t.successors;
//                                               bool b = t.isSink;
                                               }())) && is(ElementType!(ReturnType!(typeof(T.init.successors))));
}

///
template isForwardRecursiveRange(T)
{
    enum bool isForwardRecursiveRange = isInputRecursiveRange!T
                                        && __traits(compiles, {
                                                               T t;
                                                               auto t2 = t;
                                                              });
}

///
template isBidirectionalRecursiveRange(T)
{
    enum bool isBidirectionalRecursiveRange = isForwardRecursiveRange!T
                                              && __traits(compiles, {
                                                                     T t;
                                                                     t.predecessors;
                                                                     bool s = t.isSource;
                                                                    });
}

///
template isOutputRecursiveRange(T,E)
{
    enum bool isOutputRecursiveRange = __traits(compiles, {
                                                           T t;
                                                           E e;
                                                           T.put(e);
                                                          });
}

///
template ValueType(T) if (isInputRecursiveRange!T)
{
    alias ReturnType!(typeof(T.init.value)) ValueType;
}

///
template SuccessorsType(T) if (isInputRecursiveRange!T)
{
    alias ReturnType!(typeof(T.init.successors)) SuccessorsType;
}

///
template hasSize(T) if (isInputRecursiveRange!T)
{
    enum bool hasSize = __traits(compiles, T.init.size);
}

///
template hasInfiniteBreadth(T) if (isInputRecursiveRange!T)
{
    enum bool hasInfiniteBreadth = isInfinite!(ReturnType!(T.successors));
}

///
template hasInfiniteDepth(T) if (isInputRecursiveRange!T)
{
    enum bool hasInfiniteDepth = T.init.isSink; // is that kosher?
}

///
template hasInfiniteHeight(T) if (isBidirectionalRecursiveRange!T)
{
    enum bool hasInfiniteHeight = T.init.isSource;
}

/// mapping functions on a r-range
struct RMap(alias fun, RR) if (isForwardRecursiveRange!RR)
{
    RR _rr;
    this(RR rRange) { _rr = rRange;}
    bool hasValue() { return _rr.hasValue;}
    typeof(unaryFun!fun(ValueType!RR.init)) value() { return unaryFun!fun(_rr.value);}
    Map!(rmap!fun, SuccessorsType!RR) successors() { return map!(rmap!fun)(_rr.successors);}
//    bool isSink() { return _rr.isSink;}
}


/// ditto
template rmap(alias fun)
{
    RMap!(fun, RR) rmap(RR)(RR rRange) if (isForwardRecursiveRange!RR)
    {
        return RMap!(fun, RR)(rRange);
    }
}


/// Reducing a recursive range
typeof(unaryFun!onSink(ValueType!RR.init)) rreduce(alias onSink, alias fun, RR)(RR rRange) if (isInputRecursiveRange!RR)
{
    if (rRange.successors.empty)
    {
        return unaryFun!(onSink)(rRange.value);
    }
    else
    {
        typeof(unaryFun!onSink(ValueType!RR.init))[] children;
        foreach(child; rRange.successors) children ~= rreduce!(onSink, fun, RR)(child);
        return binaryFun!fun(rRange.value, children);
    }

}

/+
/// filtering on the values of a r-range with predicate pred
struct RFilter(alias pred, RR) if (isForwardRecursiveRange!RR && !isInputRange!RR)
{
    RR _rr;
    this(RR rRange) { _rr = rRange;}
    bool hasValue() { return _rr.hasValue && unaryFun!pred(_rr.value());}
    ValueType!RR value() { return _rr.value;}
    Map!(rfilter!pred, SuccessorsType!RR) successors() { return map!(rfilter!pred)(_rr.successors);}
}

template rfilter(alias pred)
{
    RFilter!(pred, RR) rfilter(RR)(RR rRange) if (isForwardRecursiveRange!RR)
    {
        return RFilter!(pred, RR)(rRange);
    }
}
+/


///
T sumTree(T,R)(T a, R b) if (isInputRange!R && is(ElementType!R == T))
{
    return a + sum(b);
}


///
size_t heightTree(T)(T a, size_t[] b)
{
    return (b.empty) ? 1 : 1 + maxOf(b);
}


///
T maxTree(T)(T a, T[] b)
{
    return maxOf(a ~ b);
}


///
T[] preorder(T)(T a, T[][] b)
{
    return a ~ array(concat(b));
}


///
T[] postorder(T)(T a, T[][] b)
{
    return array(concat(b)) ~ a;
}


///
T[] leaves(T)(T a, T[][] b)
{
    return array(concat(b));
}


string tostring(T)(T a, string[] b)
{
    string result = to!string(a);
    foreach(s; b) result ~= s;
    return result;
}

///
int numNodes(T)(T a, int[] nums)
{
    return 1 + sum(nums);
}
