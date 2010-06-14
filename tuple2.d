// Written in the D programming language

/**
This module contains different functions acting on tuples (std.typeconsTuple, not
type-tuples): converting to and from arrays, inserting fields, rotating fields,
inverting them, mapping/reducing/filtering them.

In many ways, it's a way to act on tuples as if they were polymorphic ranges.

The corresponding typetuples templates can be found in typetuple2.d.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.tuple2;

import std.algorithm;
import std.contracts;
import std.conv;
import std.functional;
import std.metastrings;
import std.range;
import std.stdio;
import std.traits;
import std.typecons;
import std.typetuple;

import dranges.traits2;
import dranges.typetuple2;
import dranges.templates;
import dranges.functional2;
import dranges.predicate;
import dranges.variadic;



/**
Small helper functions to extract a field from a tuple. Mainly to make some expressions more readable.
*/
R[0] first(R...)(Tuple!R tup) if (R.length>0) { return tup.field[0];}
/// ditto
R[1] second(R...)(Tuple!R tup) if (R.length>1) { return tup.field[1];}
/// ditto
R[2] third(R...)(Tuple!R tup) if (R.length>2) { return tup.field[2];}

/**
n==0 -> tuple()
n=1 -> tuple(t)
n>1 -> tuple(t,t,...,t) n times
*/
Tuple!(TypeNuple!(T,n)) nuple(uint n, T)(T t)
{
    TypeNuple!(T,n) tn;
    foreach(i, Type; tn) tn[i] = t;
    return tuple(tn);
}

/**
The first function transforms a tuple into a static array, the second
into a dynamic array. For both functions, the resulting array's element
type is the common type of the tuple's elements (it doesn't compile if there is no common type).
Example:
----
auto t = tuple(1, 2.0, 10000000000);
auto sa = tupleToStaticArray(t);
auto da = tupleToDynamicArray(t);
assert(is(typeof(sa) == double[3]));
assert(is(typeof(da) == double[]));

assert(sa == [1.0,2.0,10000000000.0]);
assert(da == [1.0,2.0,10000000000.0][]);
----
*/
CommonType!R[R.length] tupleToStaticArray(R...)(Tuple!(R) t) if (!is(CommonType!R == void))
{
    alias CommonType!R CT;
    CT[R.length] result; // 2.036: now we can return static arrays
    foreach(i, Unused; R) { result[i] = t.field[i];}
    return result;
}

/// ditto
CommonType!R[] tupleToDynamicArray(R...)(Tuple!(R) t) if (!is(CommonType!R == void))
{
    alias CommonType!R CT;
    CT[] result = new CT[R.length];
    foreach(i, Unused; R) { result[i] = t.field[i];}
    return result;
}

unittest
{
    auto t = tuple(1, 2.0, 10000000000);
    auto sa = tupleToStaticArray(t);
    auto da = tupleToDynamicArray(t);
    assert(is(typeof(sa) == double[3]));
    assert(is(typeof(da) == double[]));

    assert(sa == [1.0,2.0,10000000000.0]);
    assert(da == [1.0,2.0,10000000000.0][]);
}

/**
The first function transforms a static array into a tuple, the second does
the same for a dynamic array. For the dynamic case, you must give it the array's length
at compile-time. There is no length-checking done, so be careful.
Example:
----
int[3] a = [1,2,3];
auto t1 = staticArrayToTuple(a);
assert(is(typeof(t1) == Tuple!(int,int,int)));
assert(t1 == tuple(1,2,3));

int[] b = [1,2,3];
auto t2 = dynamicArrayToTuple!3(b);
assert(is(typeof(t2) == Tuple!(int,int,int)));
assert(t2 == tuple(1,2,3));
----
*/
Tuple!(TypeNuple!(T,n)) staticArrayToTuple(size_t n, T)(T[n] arr) {
    Tuple!(TypeNuple!(T,n)) tup;
    foreach(i, Unused; TypeNuple!(T,n)) {
        tup.field[i] = arr[i];
    }
    return tup;
}

/// ditto
Tuple!(TypeNuple!(T,n)) dynamicArrayToTuple(size_t n, T)(T[] arr) {
    Tuple!(TypeNuple!(T,n)) tup;
    foreach(i, Unused; TypeNuple!(T,n)) {
        tup.field[i] = arr[i];
    }
    return tup;
}

unittest
{
    int[3] a = [1,2,3];
    auto t1 = staticArrayToTuple(a);
    assert(is(typeof(t1) == Tuple!(int,int,int)));
    assert(t1 == tuple(1,2,3));

    int[] b = [1,2,3];
    auto t2 = dynamicArrayToTuple!3(b);
    assert(is(typeof(t2) == Tuple!(int,int,int)));
    assert(t2 == tuple(1,2,3));
}

/**
Same as the previous functions: takes an input range and a length upTo
and converts the first upTo elements of the range into a tuple. The range
must have at least upTo elements.
Example:
----
auto r = [0,1,2,3,4,5];
auto f = filter!isOdd(r);
auto t = rangeToTuple!3(f);
assert(t == tuple(1,3,5));
// With an infinite range.
auto c = cycle(r[0..3]); // 0,1,2, 0,1,2, 0,1,2,...
auto t2 = rangeToTuple!7(c);
assert(t2 == tuple(0,1,2,0,1,2,0));
----
*/
Tuple!(TypeNuple!(ElementType!R,upTo)) rangeToTuple(size_t upTo, R)(R range) if (isInputRange!R)
{
    return dynamicArrayToTuple!upTo(array(take(range, upTo)));
}

unittest
{
    auto r = [0,1,2,3,4,5];
    auto f = filter!isOdd(r);
    auto t = rangeToTuple!3(f);
    assert(t == tuple(1,3,5));
    // With an infinite range.
    auto c = cycle(r[0..3]); // 0,1,2, 0,1,2, 0,1,2,...
    auto t2 = rangeToTuple!7(c);
    assert(t2 == tuple(0,1,2,0,1,2,0));

    auto t3 = rangeToTuple!0(r);
    assert(t3 == tuple());
}

/**
Small functions to imitate the range 'API' with tuples.
*/
R[0] front(R...)(Tuple!R tup)
{
    return tup.field[0];
}

/// ditto
Tuple!(R[1..$]) tail(R...)(Tuple!R tup)
{
    return tuple(tup.expand[1..$]);
}

/// ditto
R[$-1] back(R...)(Tuple!R tup)
{
    return tup.field[R.length-1];
}

/// ditto
size_t length(R...)(Tuple!R tup)
{
    return R.length;
}

/// ditto
bool empty(R...)(Tuple!R tup)
{
    return R.length == 0;
}

unittest
{
    auto t = tuple('a',1, 3.1415);
    assert(front(t)  == 'a');
    assert(tail(t)   == tuple(1, 3.1415));
    assert(back(t)   == 3.1415);
    assert(length(t) == 3);
}

/**
Inserts a new component into a tuple, at position n. Position 0 is before all other
components, position R.length is after all of them. n cannot be greater than R.length.
Example:
----
auto t = tuple(1,'a',3.14);
auto s0 = insertAtTuple!0(t, "qwer");
auto s1 = insertAtTuple!1(t, "qwer");
auto s2 = insertAtTuple!2(t, "qwer");
auto s3 = tupleInsertAt!3(t, "qwer");
assert(s0 == tuple("qwer",1,'a',3.14));
assert(s1 == tuple(1,"qwer",'a',3.14));
assert(s2 == tuple(1,'a',"qwer",3.14));
assert(s3 == tuple(1,'a',3.14, "qwer"));
----
*/
Tuple!(TypeTuple!(R[0..n],T,R[n..$])) insertAtTuple(size_t n, T, R...)(Tuple!R tup, T val) if (n <= R.length) {
    alias TypeTuple!(R[0..n],T,R[n..$]) R2;
    Tuple!R2 tup2;
    foreach(i, Unused; R2[0..n]) tup2.field[i] = tup.field[i];
    tup2.field[n] = val;
    foreach(i, Unused; R2[n+1..$]) tup2.field[i+n+1] = tup.field[i+n];
    return tup2;
}

unittest
{
    auto t = tuple(1,'a',3.14);
    auto s0 = insertAtTuple!0(t, "qwer");
    auto s1 = insertAtTuple!1(t, "qwer");
    auto s2 = insertAtTuple!2(t, "qwer");
    auto s3 = insertAtTuple!3(t, "qwer");
    assert(s0 == tuple("qwer",1,'a',3.14));
    assert(s1 == tuple(1,"qwer",'a',3.14));
    assert(s2 == tuple(1,'a',"qwer",3.14));
    assert(s3 == tuple(1,'a',3.14, "qwer"));
}

/**
Creates a new tuple by extracting the components of tup and reassembling them
according to an indices array. [0,1,2] means 'take the first, second and third component' and so on.
The indices can be in any order ([1,2,0]), can be repeated or omitted([0,2,2,0]) and the array
can be as long as you wish.
See_Also: shred in range2.d
Examples:
----
auto t = tuple(1, 'a', 3.14);

auto s1 = shredTuple!([0,2])(t);
assert(s1 == tuple(1, 3.14));

auto s2 = shredTuple!([2,0,0,1,1])(t);
assert(s2 == tuple(3.14,1,1,'a','a'));

auto s3 = shredTuple!([0])(t);
assert(s3 == tuple(1));
----
*/
ShredType!(array, R) shredTuple(alias array, R...)(Tuple!R tup) {
    alias ExtractType!(array, R) ET;
    Tuple!ET tup2;
    foreach(i, Unused; ET) tup2.field[i] = tup.field[array[i]];
    return tup2;
}

template ShredType(alias array, R...) {
    alias Tuple!(ExtractType!(array, R)) ShredType;
}

unittest
{
    auto t = tuple(1, 'a', 3.14);

    auto s1 = shredTuple!([0,2])(t);
    assert(s1 == tuple(1, 3.14));

    auto s2 = shredTuple!([2,0,0,1,1])(t);
    assert(s2 == tuple(3.14,1,1,'a','a'));

    auto s3 = shredTuple!([0])(t);
    assert(s3 == tuple(1));
}

/**
Takes a tuple and rotates its fields by n positions. If n>0, it rotates to the left (takes
the first n fields and put them at the end). If n<0, it rotate to the right (takes the last
n fields and put them at the beginning).
Example:
----
auto t = tuple(1, 'a', 3.14);

auto r1 = rotateTuple!1(t);
auto r5 = rotateTuple!5(t);
auto r0 = rotateTuple!0(t);
auto r_1 = rotateTuple!(-1)(t);
auto r_5 = rotateTuple!(-5)(t);

assert(r1 == tuple('a',3.14,1));
assert(r5 == tuple(3.14,1,'a'));
assert(r0 == t);
assert(r_1 == tuple(3.14,1,'a'));
assert(r_5 == tuple('a',3.14,1)); // equivalent to rotateTuple!(-2) and also to rotateTuple!1

assert(rotateTuple!1(tuple(1)) == tuple(1));
----
*/
Tuple!(RotateTypes!(n,R)) rotateTuple(int n, R...)(Tuple!R tup)
{
    enum size_t nn = n>=0 ? n%R.length : R.length - (-n)%R.length;

    RotateTypes!(n,R) vals;
    static if (nn != R.length) vals[0..(R.length-nn)] = tup.expand[nn..$];
    static if (nn != 0) vals[(R.length-nn)..$] = tup.expand[0..nn];
    return tuple(vals);
}

unittest
{
    auto t = tuple(1, 'a', 3.14);

    auto r1 = rotateTuple!1(t);
    auto r5 = rotateTuple!5(t);
    auto r0 = rotateTuple!0(t);
    auto r_1 = rotateTuple!(-1)(t);
    auto r_5 = rotateTuple!(-5)(t);

    assert(r1 == tuple('a',3.14,1));
    assert(r5 == tuple(3.14,1,'a'));
    assert(r0 == t);
    assert(r_1 == tuple(3.14,1,'a'));
    assert(r_5 == tuple('a',3.14,1)); // equivalent to rotateTuple!(-2) and also to rotateTuple!1

    assert(rotateTuple!1(tuple(1)) == tuple(1));
}

/**
Takes a tuple and reverse its fields.
Example:
----
auto t = tuple(1,'a',3.14);
auto r = reverseTuple(t);
assert(r == tuple(3.14,'a',1));
----
*/
Tuple!(ReverseTypes!R) reverseTuple(R...)(Tuple!R tup)
{
    ReverseTypes!R vals;
    foreach(i, Unused; R) vals[R.length-1-i] = tup.field[i];
    return tuple(vals);
}

unittest
{
    auto t = tuple(1,'a',3.14);
    auto r = reverseTuple(t);
    assert(r == tuple(3.14,'a',1));

    assert(reverseTuple(tuple(1)) == tuple(1));
}

/**
Stitches (glues) two tuples together, creating a larger one.
Example:
----
auto t1 = tuple(1, 'a', 3.14);
auto t2 = tuple("abc", true);
auto t3 = stitchTuples(t1,t2);
assert(is(typeof(t3) == Tuple!(int,char,double,string,bool)));
assert(t3 == tuple(1, 'a', 3.14, "abc", true));
----
*/
Tuple!(T1.Types, T2.Types) stitchTuples(T1, T2)(T1 tup1, T2 tup2) if (is(T1.Types) && is(T2.Types))
{
    return tuple(tup1.expand, tup2.expand);
}

unittest
{
    auto t1 = tuple(1, 'a', 3.14);
    auto t2 = tuple("abc", true);
    auto t3 = stitchTuples(t1,t2);
    assert(is(typeof(t3) == Tuple!(int,char,double,string,bool)));
    assert(t3 == tuple(1, 'a', 3.14, "abc", true));
}

/**
Returns: a new tuple with tup's fields and a new field at the end, containing 'element'.
Example:
----
auto t = tuple(1, 'a', 3.14);
auto t2 = append(t, "abc");
assert(is(typeof(t2) == Tuple!(int, char, double, string)));
assert(t2 == tuple(1, 'a', 3.14, "abc"));
----
*/
Tuple!(R, E) append(E, R...)(Tuple!R tup, E element)
{
    return tuple(tup.expand, element);
}

unittest
{
    auto t = tuple(1, 'a', 3.14);
    auto t2 = append(t, "abc");
    assert(is(typeof(t2) == Tuple!(int, char, double, string)));
    assert(t2 == tuple(1, 'a', 3.14, "abc"));
}

/**
Returns: a new tuple with element as first field and then tup's fields.
Example:
----
auto t = tuple(1, 'a', 3.14);
auto t2 = prepend("abc", t);
assert(is(typeof(t2) == Tuple!(string, int, char, double)));
assert(t2 == tuple("abc", 1, 'a', 3.14));
----
*/
Tuple!(E, R) prepend(E, R...)(E element, Tuple!R tup)
{
    return tuple(element, tup.expand);
}

unittest
{
    auto t = tuple(1, 'a', 3.14);
    auto t2 = prepend("abc", t);
    assert(is(typeof(t2) == Tuple!(string, int, char, double)));
    assert(t2 == tuple("abc", 1, 'a', 3.14));
}

/**
Swaps the fields at index i1 and index i2 in a tuple.
Example:
----
auto t = tuple(1, 'a', 3.14, "abc");
auto ts1 = swapTuple!(1,3)(t);
assert(ts1 == tuple(1, "abc", 3.14, 'a'));
auto ts2 = swapTuple!(3,1)(t);
assert(ts2 == tuple(1, "abc", 3.14, 'a'));
auto ts3 = swapTuple!(1,1)(t);
assert(ts3 == t);
----
*/
Tuple!(SwapTypes!(i1,i2,R)) swapTuple(size_t i1, size_t i2, R...)(Tuple!R tup)
{
    Tuple!(SwapTypes!(i1,i2,R)) tup2;
    foreach(i, Unused; R) {
        static if (i == i1) {
            tup2.field[i] = tup.field[i2];
        }
        else {
            static if (i == i2) {
                tup2.field[i] = tup.field[i1];
            }
            else {
                tup2.field[i] = tup.field[i];
            }
        }
    }
    return tup2;
}

unittest
{
    auto t = tuple(1, 'a', 3.14, "abc");
    auto ts1 = swapTuple!(1,3)(t);
    assert(ts1 == tuple(1, "abc", 3.14, 'a'));
    auto ts2 = swapTuple!(3,1)(t);
    assert(ts2 == tuple(1, "abc", 3.14, 'a'));
    auto ts3 = swapTuple!(1,1)(t);
    assert(ts3 == t);
}


template SumOfLength(alias zero, T)
{
    enum size_t SumOfLength = zero + (FlattenTuple!T).length;
}

template SumOfLengths(T...)
{
    alias StaticScan!(SumOfLength, 0, T) SumOfLengths;
}

///
Tuple!(FlattenTuple!T) flattenTuple(T...)(T tup)
{
    alias SumOfLengths!T lengths;
    Flatten!T flat;
    foreach(i, Type; T)
        static if (__traits(compiles, T[i].Types)) {
            static if (T[i].Types.length > 0) // Only if someone tries to flatten Tuple!() (aka Unit)
                flat[lengths[i]..lengths[i+1]] = flattenTuple(tup[i].expand).expand;}
        else
            flat[lengths[i]] = tup[i];
    return tuple(flat);
}

template NoEmptyTuple(alias zero, T)
{
    static if (__traits(compiles, T.Types) && T.Types.length == 0)
        enum NoEmptyTuple = zero;
    else
        enum NoEmptyTuple = zero + 1;
}

template NoEmptyList(T...)
{
    alias StaticScan!(NoEmptyTuple, 0, T) NoEmptyList;
}


typeof(fun(ifLeaf(T[0].init))) tupleReduce(alias fun, alias ifLeaf, T...)(T tup) if (T.length)
{
//    alias SumOfLengths!T lengths;
    alias NoEmptyList!T noempty;
    TypeNuple!(typeof(fun(ifLeaf(T[0].init))), noempty[$-1]) temp;
    foreach(i, Type; T)
       static if (__traits(compiles, T[i].Types)) {
            static if (T[i].Types.length)
                temp[noempty[i]] = tupleReduce!(fun,ifLeaf)(tup[i].expand);}
        else
            temp[noempty[i]] = ifLeaf(tup[i]); // = tup[i] ?
    return fun(temp);
}


typeof(fun(CommonType!(Flatten!T).init)) tupleReduce0(alias fun, alias ifLeaf, T...)(T tup)
{
    TypeNuple!(typeof(fun(ifLeaf(T[0].init))), T.length) temp;
    foreach(i, Type; T)
        static if (__traits(compiles, T[i].Types))
            temp[i] = tupleReduce0!(fun,ifLeaf)(tup[i].expand);
        else
            temp[i] = ifLeaf(tup[i]);
    return fun(temp);
}


private template Firsts(T...) if (allSatisfy!(isTuple, T))
{
    alias Tuple!(StaticMap!(T1!"a.Types[0]", T)) Firsts;
}

private template NthTypes(size_t n, T...)if (allSatisfy!(isTuple, T))
{
    alias StaticMap!(T1!("a.Types[" ~to!string(n) ~ "]"), T) NthTypes;
}

private template Rests(T...) if (allSatisfy!(isTuple, T))
{
    alias Tuple!(StaticMap!(T1!"Tuple!(a.Types[1..$])", T)) Rests;
}

private template RetTypeTuples(alias fun, T...) if (allSatisfy!(isTuple, T))
{
    static if(T[0].Types.length)
        alias TypeTuple!(typeof(fun(Firsts!T.init.expand)), RetTypeTuples!(fun, (Rests!T).Types)) RetTypeTuples;
    else
        alias TypeTuple!() RetTypeTuples;
}

template TupleLength(T) if (isTuple!T)
{
    enum size_t TupleLength = T.Types.length;
}

/// Maps on a tuple, using a polymorphic function. Produces another tuple.
Tuple!(StaticMap!(RT!fun, T)) mapTuple(alias fun, T...)(Tuple!T tup)
{
    StaticMap!(RT!fun, T) res;
    foreach(i, Type; T) res[i] = fun(tup.field[i]);
    return tuple(res);
}

/// Maps n tuples in paralle, using a polymorphing n-args function.
Tuple!(RetTypeTuples!(fun, T))
mapTuples(alias fun, T...)(T tuples)
if (allSatisfy!(isTuple, T) && allEqual!(StaticMap!(TupleLength, T)))
{
    alias RetTypeTuples!(fun, T) RTT;
    RTT result;
    foreach(i, Type; RTT)
    {
        alias NthTypes!(i, T) NF;
        NF nf;
        foreach(j, Type2; T)
        {
            nf[j] = tuples[j].field[i];
        }
        result[i] =fun(nf);
    }
    return tuple(result);
}

/// Folds a tuple using a polymorphic function.
StaticScan!(RT2!fun, T)[$-1] reduceTuple(alias fun, T...)(Tuple!T ts)
{
    alias StaticScan!(RT2!fun, T) RTS;
    RTS result;
    foreach(i, Type; RTS) {
        static if (i == 0)
            result[i] = ts.field[0];
        else
            result[i] = fun(result[i-1], ts.field[i]);
    }
    return result[$-1];
}

/// Scan on a tuple. See dranges.algorithm2.scan.
Tuple!(StaticScan!(RT2!fun, T)) scanTuple(alias fun, T...)(Tuple!T ts)
{
    alias StaticScan!(RT2!fun, T) RTS;
    RTS result;
    foreach(i, Type; RTS) {
        static if (i == 0)
            result[i] = ts.field[0];
        else
            result[i] = fun(result[i-1], ts.field[i]);
    }
    return tuple(result);
}

///
Tuple!(StaticStride!(n,T)) strideTuple(size_t n, T...)(Tuple!T tup) if (n > 0)
{
    return strideVariadic!n(tup.expand);
}

///
Tuple!(StaticIterate!(times, RT!fun, T)) iterateTuple(size_t times, alias fun, T)(T t)
{
    alias StaticIterate!(times, RT!fun, T) SuccessiveTypes;
    SuccessiveTypes st;

    foreach(i, Type; SuccessiveTypes) {
        static if (i == 0)
            st[i] = t;
        else
            st[i] = fun(st[i-1]);
    }
    return tuple(st);
}


template RTS2(alias fun)
{
    template RTS2(T...)
    {
        alias typeof(fun((Tuple!T).init.expand)).Types RTS2;
    }
}

template RTSState(alias fun)
{
    template RTSState(T...)
    {
        alias TypeTuple!(Tuple!(typeof(fun((Tuple!T).init.expand)).Types[1..$]), typeof(fun((Tuple!T).init.expand)).Types[1..$])  RTSState;
    }
}

///
Tuple!(StaticUnfold!(times, RTS2!fun, State)) unfoldTuple(size_t times, alias fun, State...)(State state)
{
    alias StaticUnfold!(times, RTS2!fun, State) SuccessiveTypes;
    alias StaticUnfold!(times, RTSState!fun, State) SuccessiveStates;
    SuccessiveTypes  st;
    SuccessiveStates ss;
    foreach(i, Type; SuccessiveTypes) {
        static if (i == 0)
        {
            st[i] = fun(state).field[0];
            ss[i] = tuple(fun(state).expand[1..$]);
        }
        else
        {
            st[i] = fun(ss[i-1].expand).field[0];
            static if (i < SuccessiveStates.length-1) ss[i] = tuple(fun(ss[i-1].expand).expand[1..$]);
        }
    }
    return tuple(st);
}

template FilterTupleTypes(alias pred, alias tup)
{
    static if (tup.field.length)
    {
        static if (pred(tup.field[0]))
            alias TypeTuple!(tup.Types[0], FilterTupleTypes!(pred, tuple(tup.expand[1..$]))) FilterTupleTypes;
        else
            alias FilterTupleTypes!(pred, tuple(tup.expand[1..$])) FilterTupleTypes;
    }
    else
    {
        alias TypeTuple!() FilterTupleTypes;
    }

}

template FilterTupleIndices(alias pred, alias tup, size_t ind)
{
    static if (tup.field.length)
    {
        static if (pred(tup.field[0]))
            alias TypeTuple!(ind, FilterTupleIndices!(pred, tuple(tup.expand[1..$]), ind+1)) FilterTupleIndices;
        else
            alias /+TypeTuple!(+/FilterTupleIndices!(pred, tuple(tup.expand[1..$]), ind+1)/+)+/ FilterTupleIndices;
    }
    else
    {
        alias TypeTuple!() FilterTupleIndices;
    }

}

/// Filter a tuple on its values.
Tuple!(FilterTupleTypes!(pred, tup)) filterTuple(alias pred, alias tup)()
{
    FilterTupleTypes!(pred, tup) result;
    alias FilterTupleIndices!(pred, tup, 0) indices;
    foreach(i, ind; indices)
    {
        result[i] = tup.field[ind];
    }
    return tuple(result);
}


template TakeWhileTupleTypes(alias pred, alias tup)
{
    static if (tup.field.length && pred(tup.field[0]))
        alias TypeTuple!(tup.Types[0], TakeWhileTupleTypes!(pred, tuple(tup.expand[1..$]))) TakeWhileTupleTypes;
    else
        alias TypeTuple!() TakeWhileTupleTypes;
}

///
Tuple!(TakeWhileTupleTypes!(pred, tup)) takeWhileTuple(alias pred, alias tup)()
{
    TakeWhileTupleTypes!(pred, tup) result;
    foreach(i, Type; result) {result[i] = tup.field[i];}
    return tuple(result);
}

template DropWhileTupleIndex(alias pred, alias tup, size_t ind)
{
    static if (tup.field.length && pred(tup.field[0]))
        enum size_t DropWhileTupleIndex = DropWhileTupleIndex!(pred, tuple(tup.expand[1..$]), ind+1);
    else
        enum size_t DropWhileTupleIndex = ind;
}

///
Tuple!(tup.Types[DropWhileTupleIndex!(pred, tup,0)..$]) dropWhileTuple(alias pred, alias tup)()
{
    enum size_t n = DropWhileTupleIndex!(pred, tup,0);
    tup.Types[n..$] result;
    foreach(i, Type; result) {result[i] = tup.field[i+n];}
    return tuple(result);
}

///
Tuple!(tup.Types[DropWhileTupleIndex!(pred, tup,0)..$], tup.Types[0..DropWhileTupleIndex!(pred,tup, 0)])
rotateWhileTuple(alias pred, alias tup)()
{
    enum size_t n = DropWhileTupleIndex!(pred, tup,0);
    TypeTuple!(tup.Types[n..$], tup.Types[0..n]) result;
    foreach(i, Type; result)
    {
        static if (i < result.length-n)
            result[i] = tup.field[i+n];
        else
            result[i] = tup.field[i+n-result.length];
    }
    return tuple(result);
}

///
bool contains(U, T...)(Tuple!T tup, U elem)
{
    static if (staticIndexOf!(U,T) == -1)
        return false;
    else
    {
        foreach(i, Type; tup.Types)
        {
            static if (is(Type == U))
                if (tup.field[i] == elem) return true;
        }
        return false;
    }
}
