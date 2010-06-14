// Written in the D programming language

/**
To Be Documented.

An attempts to code generalization of folding/unfolding algorithms on branching structures, also
known under the delightful names of catamorphisms, anamorphisms, paramorphisms and hylomorphisms.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.morphism;

import std.algorithm, std.array, std.functional,std.range, std.traits;

import dranges.algorithm2;
import dranges.functional2;
import dranges.templates;
import dranges.traits2;
import dranges.tuple2;
import dranges.typetuple2;



/**
Catamorphism.

The equivalent of reduce, on recursive ranges: it collapses an entire recursive range into one value. Or,
if you will and if the propagated value is complex, recursively builds a value from a tree.

fun takes as arguments the front value of the recursive range and the range of results coming from
applying the catamorphism on the successors. That is, one step in the building is that you already
applied fun to the successors. From this range of temporary results and the current node's value,
you build the current result, which you return 'upward', to the preceding level of recursion.

So, if the node is a sink/leaf (no successors or the only successor is empty), the range of result is also empty.

This version take a standard function. It's the equivalent of reduce(range).
*/
ReturnType!fun cata(alias fun, T)(T tr)
{
    auto ch = array(map!(cata!(fun,T))(tr.successors)); // You have to get rid of array to have an infinite list of successors
    return fun(ch,tr.value);
}

int h(int[] heights, ...)
{
    return 1 + maxOf(0 ~ heights);
}

T m(T)(T[] maxs, T value) { return maxOf(maxs ~ value);}
T[] preord(T)(T[][] pos, T value) { return value ~ array(range2.flatten(pos));}
T[] postord(T)(T[][] pos, T value) { return array(range2.flatten(pos)) ~ value;}
NTree!T cons(T)(NTree!T[] trees, T value) { return ntree(value, trees);}
NTree!(Tuple!(T,int)) withDepth(T)(NTree!(Tuple!(T,int))[] trees, T value)
{
    int d = 1 + maxOf(0 ~ array(map!"a.value.field[1]"(trees))); // find current depth
    return ntree(tuple(value, d), trees);
}
int numNodes(int[] numnodes, ...) { return sum(1 ~ numnodes);}


/**
Anamorphism.

The equivalent of unfold for recursive ranges: creates a entire tree from
a generative function gen, a seed value, and a predicate (on the current value) as the stopping condition.
*/
class Ana(alias gen, alias pred, T) {
    T value;
    this(T t) { value = t;}

    Ana!(gen,pred,T)[] successors() {
        return unaryFun!pred(value) ? (typeof(return)).init : array(map!(ana!(gen,pred,T))(unaryFun!gen(value)));
    }
}

///
Ana!(gen,pred,T) ana(alias gen, alias pred, T)(T t) {
    return new Ana!(gen,pred,T)(t);
}

/**
Paramorphism

The equivalent of reduce, but with a ternary function constructor(front of the range, tail of the range, paramorphism on the tail)
*/
typeof(ifEmpty) para(alias ifEmpty, alias constructor, R)(R range) if (isInputRange!R)
{
    if (range.empty) return ifEmpty;
    auto f = range.front;
    range.popFront;
    return naryFun!constructor(f, range, para!(ifEmpty, constructor)(range));
}

/**
Hylomorphism, the composition of a catamorphism (which collapse a recursive range) with an anamorphism (which builds a recursive range).

Examples?
*/
typeof(ifTrue) hylo(alias ifTrue, alias constructor, alias predicate, alias next, T)(T t)
{
    if (unaryFun!predicate(t)) return ifTrue;
    auto state = unaryFun!next(t); // (b, a')
    return binaryFun!constructor(first(state), hylo!(ifTrue, constructor, predicate, next)(second(state)));
}

unittest
{
    int[] nums = [1,2,3,4,5];
    int[] e;

        auto t = para!(e, "(a ~ b) ~ c")(nums);
//    wr(t);
    auto fact = para!(1, "(a+1)*c")([5,4,3,2,1]);
//    writeln(fact);
    auto fact2 = hylo!(1, "a*b", "a==0", "tuple(a, a-1)")(5);
//    writeln(fact2);
    int[][] h;
    auto heads =reduce!"a~(a[$-1]~b)"(h ~ e,nums);
//    wr(heads);


    bool pred(int i) { return i > 3_000_000;}
    int[] gen(int i) { return [i+1,i*2];}
    int[] collatz(int i) { return ((i-4)%6 == 0 && (i > 4)) ? [i*2,(i-1)/3] : [i*2];}

    auto n5 = ana!(collatz, "a>=1_00")(1);
//    writeln(cata!numNodes(n5), " numbers found.");
//    writeln("Longest sequence contains ", cata!h(n5), " nodes.");
//    writeln(cata!(toS!int)(n5));

/* todo: isRecursiveContainer. do not ask for a NTree when you don't need one*/
//    wr(map!"a.value"(traversal(n5)));



//    writeln(cata!(preord!int)(n5));

}
