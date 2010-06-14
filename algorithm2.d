// Written in the D programming language.

/**
This module contains functions akin to map and filter, found in std.algorithm.
You'll find there generalizations of these functions to act on a variadic numbers
of ranges in parallel (tmap, tfilter) or to map n-ary functions on a range (nmap, nfilter).
There are also many function inspired by the sequence/list/map libraries of other (functional) programming
languages (namely, Haskell, Clojure, Scala, Python) : a range comprehension,
zipping ranges, reduceR, fold/foldR, scan/scanR, and so on.

As far as possible, all higher-order ranges presented in this module
and in algorithm2.d are 'tight wrappers': they are bidirectional if their input range is bidirectional,
define opIndex, opIndexAssign, length if it's possible, etc. That way, a good input range (for example, a random-access range)
will see its properties propagated through a chain of calls.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.algorithm2;

import std.algorithm;
import std.array;
import std.bigint;
import std.contracts;
import std.conv;
import std.functional;
import std.math;
import std.metastrings;
import std.range;
import std.stdio;
import std.string;
import std.traits;
import std.typecons;
import std.typetuple;


import dranges.traits2;
import dranges.typetuple2;
import dranges.templates;
import dranges.functional2;
import dranges.predicate;
import dranges.tuple2;
import dranges.range2;

/**
Small one-liners to use reduce. Sum and product work on empty ranges (they return 0 and 1, respectively),
but not minOf and maxOf.
Example:
----
auto r1 = [1,2,3,4,5];
auto r2 = [-1.0,2.7818281828, 3.1415926];

assert(sum(r1) == 1+2+3+4+5);
assert(product(r1) == 1*2*3*4*5);
assert(minOf(r2) == -1.0);
assert(maxOf(r2) == 3.1415926);
----
*/
ElementType!R sum(R)(R range) if (isForwardRange!R) {
    return reduce!"a+b"(to!(ElementType!R)(0), range);
}

/// ditto
ElementType!R product(R)(R range) if (isForwardRange!R) {
    return reduce!"a*b"(to!(ElementType!R)(1), range);
}

/// ditto
ElementType!R maxOf(R)(R range) if (isForwardRange!R) {
    enforce(!range.empty, "Do not use maxOf on empty ranges.");
    return reduce!(std.algorithm.max)((ElementType!R).min, range);
}

/// ditto
ElementType!R minOf(R)(R range) if (isForwardRange!R) {
    enforce(!range.empty, "Do not use minOf on empty ranges.");
    return reduce!(std.algorithm.min)((ElementType!R).max,range);
}

unittest
{
    auto r1 = [1,2,3,4,5];
    auto r2 = [-1.0,2.7818281828, 3.1415926];
    int[] r3;

    assert(sum(r1) == 1+2+3+4+5);
    assert(product(r1) == 1*2*3*4*5);
    assert(minOf(r2) == -1.0);
    assert(maxOf(r2) == 3.1415926);
    assert(sum(r3) == 0.0);
    assert(product(r3) == 1.0);
}

/**
Returns an associative array containing the number of times each element
is present in the range. It's a greedy algorithm: it does not work
on infinite ranges.
Example:
----
auto r = "Mississippi";
auto f = frequency(r);
assert(f['i'] == 4);
assert(f['s'] == 4);
assert(f['M'] == 1);
----
*/
size_t[ElementType!R] frequency(R)(R range) if (isInputRange!R)
{
    size_t[ElementType!R] freq;
    foreach(elem; range) if (elem in freq) { freq[elem]++;} else { freq[elem]=1;}
    return freq;
}

unittest
{
    auto r = "Mississippi";
    auto f = frequency(r);
    assert(f['i'] == 4);
    assert(f['s'] == 4);
    assert(f['M'] == 1);
}

/**
Maps a n-ary function on a range, taking n-elements segment at a time. You can use
standard functions or 'string' functions. For string functions, it will automatically determine their arity.
Examples:
----
auto r1 = [0,1,2,3,4,5,6];
auto nm1 = nmap!"a*b"(r1); // Will map "a*b" on (0,1), (1,2), (2,3), (3,4), (4,5), (5,6)
assert(equal(nm1, [0,2,6,12,20,30][]));

// Will map "a*b*c"/"a+b+c" alternatively on (0,1,2), (1,2,3), (2,3,4), (3,4,5), (4,5,6)
auto nm2 = nmap!"a%2 == 0 ? a*b*c : a+b+c"(r1);
assert(equal(nm2, [0,6,24,12,120][]));

auto nm3 = nmap!"a"(r1); // Will map "a" on (0), (1), (2), ...
assert(equal(nm3, [0,1,2,3,4,5,6][])); // Completly equivalent to map!"a"(r1)

int[] e;
auto nm4 = nmap!"a%2 == 0 ? a*b*c : a+b+c"(e); // e is empty -> cannot map a ternary function on it
assert(nm4.empty);
----
*/
NMapType!(fun, R) nmap(alias fun, R)(R range) if (isForwardRange!R)
{
    auto s = segment!(arity!fun)(range);
    alias Prepare!(fun, TypeNuple!(ElementType!R, arity!fun)) pfun;
    return map!pfun(s);
}

template NMapType(alias fun, R)
{
    alias Map!(Prepare!(fun, TypeNuple!(ElementType!R, arity!fun)), Knit!(TypeNuple!(R, arity!fun))) NMapType;
}

unittest
{
    auto r1 = [0,1,2,3,4,5,6];
    auto nm1 = nmap!"a*b"(r1); // Will map "a*b" on (0,1), (1,2), (2,3), (3,4), (4,5), (5,6)
    assert(equal(nm1, [0,2,6,12,20,30][]));

    auto nm2 = nmap!"a%2 == 0 ? a*b*c : a+b+c"(r1); // Will map "a*b*c"/"a+b+c" alternatively on (0,1,2), (1,2,3), (2,3,4), (3,4,5), (4,5,6)
    assert(equal(nm2, [0,6,24,12,120][]));

    auto nm3 = nmap!"a"(r1); // Will map "a" on (0), (1), (2), ...
    assert(equal(nm3, [0,1,2,3,4,5,6][])); // Completly equivalent to map!"a"(r1)

    int[] e;
    auto nm4 = nmap!"a%2 == 0 ? a*b*c : a+b+c"(e); // e is empty -> cannot map a ternary function on it
    assert(nm4.empty);

}

/**
Maps a n-args function on either n ranges in parallel or on an n-tuple producing range.
Examples:
----
// With functions mapped on n ranges in parallel:
auto r1 = [1,2,3,4,5,6];
string s = "abcdefghijk";

auto tm1 = tmap!"replicate(a,b)"(r1,s); // [a], [b,b], [c,c,c], [d,d,d,d], ...
assert(equal(flatten(tm1), "abbcccddddeeeeeffffff")); // Note the use of flatten

auto tm2 = tmap!"a%2 == 0 ? b : '_'"(r1,s); // alternate between a char from s and '_'
assert(equal(tm2, "_b_d_f"));

auto tm3 = tmap!"a%2==0 ? b : c"(r1,s,flatten(tm1)); // ternary function mapped on three ranges in parallel
assert(equal(tm3, "abbdcf"));

string e = "";
assert(tmap!"a"(r1, s, e).empty); // e is empty -> tmap also
----

Examples:
----
// With functions mapped on a tuple-producing range:

auto tf = tfilter!"a%2"(r1, s); // keeps the odd elements from r1, produces 2-tuples (1,'a'),(3,'c'),(5,'e')
string foo(int a, char b) { return to!string(array(replicate(a,b)));}
auto tm4 = tmap!foo(tf); // maps a standard binary function on a 2-tuple range
assert(equal(tm4, ["a","ccc","eeeee"][]));

auto r2 = [1,2,3][];
// combinations(r2,r2) is equivalent to [(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)][]
auto combs = tmap!"a*b"(combinations(r2,r2));
assert(equal(combs, [1,2,3,2,4,6,3,6,9][]));
----
*/
TMapType!(fun, R) tmap(alias fun, R...)(R ranges) if (allSatisfy!(isForwardRange,R) && (R.length > 1) || (R.length == 1 && !is(ElementType!R.Types)))
{
    alias Prepare!(fun, staticMap!(Unqual, ElementTypes!R)) pfun;
    return map!pfun(knit(ranges));
}

/// ditto
TMapType!(fun, R) tmap(alias fun, R)(R r) if (isTupleRange!R)
{
    alias ElementType!R ET;
    alias Prepare!(fun, staticMap!(Unqual, ElementType!R.Types)) pfun;
    return map!pfun(r);
}


template TMapType(alias fun, R...) if (allSatisfy!(isForwardRange,R) && (R.length > 1) || (R.length == 1 && !is(ElementType!R.Types)))
{
    alias Map!(Prepare!(fun, staticMap!(Unqual, ElementTypes!R)), Knit!R) TMapType;
}

template TMapType(alias fun, R) if (isTupleRange!R)
{
    alias Map!(Prepare!(fun, /+staticMap!(Unqual,+/ ElementType!R.Types), R) TMapType;
}

unittest
{
    auto r1 = [1,2,3,4,5,6];
    auto s = cast(char[])"abcdefghijk";
    auto tm1 = tmap!"replicate(a,b)"(s,r1); // [a], [b,b], [c,c,c], [d,d,d,d], ...
    assert(equal(concat(tm1), cast(char[])"abbcccddddeeeeeffffff")); // Note the use of flatten
    auto tm2 = tmap!"a%2 == 0 ? b : '_'"(r1,s);
    assert(equal(tm2, "_b_d_f"));

    auto tm3 = tmap!"a%2==0 ? b : c"(r1,s,concat(tm1));
    assert(equal(tm3, "abbdcf"));

    string e = "";
    assert(tmap!"a"(r1, s, e).empty); // e is empty -> tmap also

    auto tf = tfilter!"a%2"(r1, s); // keeps the odd elements from r1, produces 2-tuples (1,'a'),(3,'c'),(5,'e')
    string foo(int a, dchar b) { return to!(string)(array(replicate(b,a)));}
    auto tm4 = tmap!foo(tf); // maps a standard binary function on a 2-tuple range
    assert(equal(tm4, ["a","ccc","eeeee"][]));

    auto r2 = [1,2,3][];
    // combinations(r2,r2) is equivalent to [(1,1),(1,2),(1,3),(2,1),(2,2),(2,3),(3,1),(3,2),(3,3)][]
    auto combs = tmap!"a*b"(combinations(r2,r2));
    assert(equal(combs, [1,2,3,2,4,6,3,6,9][]));
}


/**
nfilter takes a n-args predicate and a range and outputs the n-uplets that verify the predicate.
As with other n-args functions on ranges (dropWhile, takeWhile, nmap, ...) it accepts
'string' functions and adapts its behavior accordingly.
It also takes an optional step argument, defaulting to 1 (see the examples).

To use it easily with other ranges, nfilter produces tuples, not arrays.
That also means that if you use a unary predicate it will produce the same
values than std.algorithm.filter but wrapped in a tuple. (tuple(1), ...)


TODO:
Fuse the array-returning version and the tuple-returning version and control the behavior with a policy. Do that also
with the sibling functions: dropWhile, takeWhile, nmap.
Example:
----
auto r1 = [0,1,2,3,3,5,4,3,2,1,0];
int foo(int a, int b, int c) { return a<=b && b<=c;} // increase on three elements
auto nf1 = nfilter!(foo)(r1);
assert(equal(nf1, [tuple(0,1,2), tuple(1,2,3), tuple(2,3,3), tuple(3,3,5)][]));

auto nf2 = nfilter!"a<=b && b<=c"(r1); // The same with a string function.
                                       // Automatically deduces that the predicate is a 3-args function.
assert(equal(nf2, [tuple(0,1,2), tuple(1,2,3), tuple(2,3,3), tuple(3,3,5)][]));

auto nf3 = nfilter!("a == b-1 || a == b+1", 2)(r1); // step of 2, will test (0,1) (2,3), (3,5), (4,3), (2,1)
assert(equal(nf3, [tuple(0,1), tuple(2,3), tuple(4,3), tuple(2,1)][]));

auto nf4 = nfilter!"a>100"(r1); // this predicate is always false
assert(nf4.empty);              // the filtered range is empty.
----
*/
NFilterType!(fun, step, R) nfilter(alias fun, size_t step =1, R)(R range)
if (isForwardRange!R)
{
    alias Prepare!(fun, TypeNuple!(ElementType!R, arity!fun)) pfun;
    return filter!pfun(stride(segment!(arity!fun)(range), step));
}

template NFilterType(alias fun, size_t step, R) {
    alias Filter!(Prepare!(fun, TypeNuple!(ElementType!R, arity!fun)), Stride!(Knit!(TypeNuple!(R, arity!fun)))) NFilterType;
}

unittest
{
    auto r1 = [0,1,2,3,3,5,4,3,2,1,0];
    int foo(int a, int b, int c) { return a<=b && b<=c;} // increase on three elements
    auto nf1 = nfilter!(foo)(r1);
    assert(equal(nf1, [tuple(0,1,2), tuple(1,2,3), tuple(2,3,3), tuple(3,3,5)][]));
    auto nf2 = nfilter!"a<=b && b<=c"(r1);
    assert(equal(nf2, [tuple(0,1,2), tuple(1,2,3), tuple(2,3,3), tuple(3,3,5)][]));

    auto nf3 = nfilter!("a == b-1 || a == b+1", 2)(r1); // step of 2, will test (0,1) (2,3), (3,5), (4,3), (2,1)
    assert(equal(nf3, [tuple(0,1), tuple(2,3), tuple(4,3), tuple(2,1)][]));

    auto nf4 = nfilter!"a>100"(r1);
    assert(nf4.empty);

    int[] e;
    assert(nfilter!"a"(e).empty);
}

/**
tfilter stands for tuple-filter: it either filters a variadic list of ranges in lockstep,
with a n-args predicate spanning all ranges or filters a tuple-returning range with a function.
In all cases, it returns the n-tuples that satisfy the predicate.

It can take standard functions or 'string' functions.

The first arg will be filled with the front from the first field or range element, the second arg with the second field or range and so on.
That's a,b,c,d... for a string function.

Examples:
----
// Filtering n ranges in parallel
auto    r1 = [ 0,   1,   2,   3,   4,   5];
auto r2 = [ 3.0, 4.0, 5.0, 6.0];
string[] r3 = ["a", "b", "cc"];

// standard function
bool pred(int a, double b, string c) { return (a<b) && (c.length>1);}
auto tf1 = tfilter!(pred)(r1,r2,r3);
assert(equal(tf1, [tuple(2, 5.0, "cc")][]));       // tf1 is just (2, 5.0, "cc)

// string function
auto tf2 = tfilter!"a<b && c.length>1"(r1,r2,r3); // knows arity must be 3. Will instantiate the (int,double,string) version
assert(equal(tf2, [tuple(2, 5.0, "cc")][]));      // tf2 is equal to tf1

auto tf3 = tfilter!"a*a>b"(r1, r2);
assert(equal(tf3, [tuple(3, 6.0)][]));            // Only one tuple satisfies a*a>b before reaching the end of r2

// templated predicate
bool pred2(T,U)(T t, U u) { return t*t>u;}
auto tf4 = tfilter!(pred2!(int, double))(r1, r2); // it doesn't automatically instantiate the correct function from a template.
assert(equal(tf4, [tuple(3,6.0)][]));             // because tfilter has no way to know which types the template is waiting for.
----

Example:
----
// Filtering a tuple-returning range with a function:

// combinations(r1,r3) is equivalent to [(0,"a"),(0,"b"),(0,"cc"),(1,"a), ..., (5,"a),(5,"b),(5,"cc")][]
auto tf5 = tfilter!"a%2 && b.length>1"(combinations(r1,r3));

assert(equal(tf5, [tuple(1,"cc"),tuple(3,"cc"),tuple(5,"cc")][]));
----
*/
TFilterType!(fun, R) tfilter(alias fun, R...)(R ranges)
if (allSatisfy!(isForwardRange, R) && ((R.length > 1) || (R.length == 1 && !is(ElementType!R.Types))))
{
    alias Prepare!(fun, staticMap!(Unqual, ElementTypes!R)) pfun;
    return filter!pfun(knit(ranges));
}

/// ditto
TFilterType!(fun, R) tfilter(alias fun, R)(R range)
if (isForwardRange!R && is(ElementType!R.Types))
{
    alias ElementType!R ET;
    alias Prepare!(fun, staticMap!(Unqual, ET.Types)) pfun;
    return filter!pfun(range);
}

template TFilterType(alias fun, R...)
if (allSatisfy!(isForwardRange, R) && ((R.length > 1) || (R.length == 1 && !is(ElementType!R.Types))))
{
    alias Filter!(Prepare!(fun, staticMap!(Unqual, ElementTypes!R)), Knit!R) TFilterType;
}

template TFilterType(alias fun, R)
if (isForwardRange!R && is(ElementType!R.Types))
{
    alias Filter!(Prepare!(fun, staticMap!(Unqual, ElementType!R.Types)), R) TFilterType;
}

unittest
{
    auto    r1 = [ 0,   1,   2,   3,   4,   5];
    auto r2 = [ 3.0, 4.0, 5.0, 6.0];
    string[] r3 = ["a", "b", "cc"];
    // standard function test
    bool pred(int a, double b, string c) { return (a<b) && (c.length>1);}
    auto tf1 = tfilter!pred(r1,r2,r3);
    assert(equal(tf1, [tuple(2, 5.0, "cc")][]));       // tf1 is just (2, 5.0, "cc)

    // string function test
    auto tf2 = tfilter!"a<b && c.length>1"(r1,r2,r3); // knows arity must be 3.
    assert(equal(tf2, [tuple(2, 5.0, "cc")][]));      // tf2 is equal to tf1
    auto tf3 = tfilter!"a*a>b"(r1, r2);
    assert(equal(tf3, [tuple(3, 6.0)][]));            // Only one tuple satisfies a*a>b before reaching the end of r2

    // templated predicate
    bool pred2(T,U)(T t, U u) { return t*t>u;}
    auto tf4 = tfilter!(pred2!(int, double))(r1, r2);
    assert(equal(tf4, [tuple(3,6.0)][]));

    string[] e;
    assert(tfilter!pred(r1, r2, e).empty);            // one range empty => TFilter is empty also

    // combinations(r1,r3) is equivalent to [(0,"a"),(0,"b"),(0,"cc"),(1,"a), ..., (5,"a),(5,"b),(5,"cc")][]
    auto tf5 = tfilter!"a%2 && b.length>1"(combinations(r1,r3));
    assert(equal(tf5, [tuple(1,"cc"),tuple(3,"cc"),tuple(5,"cc")][]));
}

/+
/**
Another implementation of reduceR. It uses recursion so it's quite limited in its depth.
*/
ElementType!R reducer(alias fun,R)(R range) if (isInputRange!R && !isInfinite!R)
{
    auto f = range.front;
    range.popFront;
    alias naryFun!fun nfun;
    return range.empty ? f : nfun(f, reducer!fun(range));
}
+/

/**
The complementary function to reduce: it reduces a (bidirectional) range from the right
reduce!fun(seed, range) applies successively the binary function fun
to the left elements of range (beginning with seed)
and produces fun(fun(... fun(fun(seed, range.front), range[1])...)).

By comparison, reduceR!fun(seed, range) applies successively fun to the right elements of range (also beginning
with seed or range.back, if seed is not given) and produces: fun(fun(... fun(range[$-2], fun(range.back, seed)) ...)).
If fun is not a commutative operation (that is, if fun(a,b) != fun(b,a) in general), then reduceR will
produce different results from reduce. See for example the lines with reduce!"a/b" and reduceR!"a/b".

Like reduce, it accepts many functions at the same time. In that case, the result is a tuple of the different values.
Note:
It's completly based on std.algorithm.reduce's code.

Example:
----
auto a = [ 3, 4 ];
auto r = reduce!("a + b")(0, a);
assert(r == 7);
auto rR = reduceR!("a + b")(0, a); // a+b is commutative -> same result than reduce
assert(rR == 7);

r = reduce!"a+b"(a);
assert(r == 7);
rR = reduceR!"a+b"(a); // Without seed value
assert(rR == 7);

auto a2 = [1.0,2.0,3.0,4.0];
auto r2 = reduce!"a / b"(a2);
assert(r2 == (((1.0)/2.0)/3.0)/4.0 );
auto rR2 = reduceR!"a / b"(a2);
assert(rR2 == 1.0/(2.0/(3.0/(4.0))) ); // a/b is not a commutative operation

a = [ 1, 2, 3, 4, 5 ];
// Stringize with commas
// the function has been 'symmetrized' compared to reduce's unittest
string rep = reduce!("to!string(a) ~ `, ` ~ to!(string)(b)")("", a);
assert(rep[2 .. $] == "1, 2, 3, 4, 5");
string repR = reduceR!("to!string(a) ~ `, ` ~ to!string(b)")("", a);
assert(repR[0 .. $-2] == "1, 2, 3, 4, 5");

// Continued fraction
double continuedFraction(double a, double b) { return a + 1.0/b;}
auto piFrac = [3, 7, 15, 1, 292];         // pi continued fraction,
                                              // 3.141592 is approx. 3 + 1/(7 + 1/(15 + 1/(1 + 1/(292 + 1/...))))
auto pi2 = reduceR!continuedFraction(piFrac); // calculates the continued fraction: needs reduceR as reduce wouldn't make it
assert(approxEqual(pi2, PI));                 // check
----
*/
template reduceR(fun...)
{
    alias ReduceR!(fun).reduceR reduceR;
}

template ReduceR(fun...)
{
private:
    static if (fun.length > 1)
    {
        template TypeTupleN(E, int n)
        {
            static if (n == 1) alias E TypeTupleN;
            else alias TypeTuple!(E, TypeTupleN!(E, n - 1)) TypeTupleN;
        }
        enum L = fun.length;
        template ReturnType(E)
        {
            alias Tuple!(TypeTupleN!(E, L)) ReturnType;
        }
    }
    else
    {
        template ReturnType(E)
        {
            alias E ReturnType;
        }
    }

public:
    Unqual!E reduceR(E, R)(E seed, R r)
    {
        Unqual!E result = seed;
        foreach_reverse(e; r)
        {
            static if (fun.length == 1)
            {
                result = binaryFun!(fun[0])(e, result);
            }
            else
            {
                foreach (i, Unused; typeof(E.field))
                {
                    result.field[i] = binaryFun!(fun[i])(e, result.field[i]);
                }
            }
        }
        return result;
    }

    ReturnType!(ElementType!(Range))
    reduceR(Range)(Range r) if (isBidirectionalRange!Range)
    {
        enforce(!r.empty);
        static if (fun.length == 1)
        {
            auto e = r.back;
        }
        else
        {
            typeof(return) e;
            foreach (i, Unused; typeof(typeof(return).field))
            {
                e.field[i] = r.back;
            }
        }
        r.popBack;
        return reduceR(e, r);
    }
}

unittest // taken from std.algorithm.reduce unittest
{
    auto a = [ 3, 4 ];
    auto r = reduce!("a + b")(0, a);
    assert(r == 7);
    auto rR = reduceR!("a + b")(0, a);
    assert(rR == 7);

    r = reduce!("a + b")(a);
    assert(r == 7);
    rR = reduceR!("a + b")(a);
    assert(rR == 7);

    auto a2 = [1.0,2.0,3.0,4.0];
    auto r2 = reduce!("a / b")(a2);
    assert(r2 == ((1.0/2.0)/3.0)/4.0);
    auto rR2 = reduceR!("a / b")(a2);
    assert(rR2 == 1.0/(2.0/(3.0/4.0))); // a/b is not a commutative operation: it will give different results for reduce and reduceR

    r = reduce!(min)(a);
    assert(r == 3);
    rR = reduceR!(min)(a);
    assert(rR == 3);
/*
    auto b = [ 100 ];
    auto r1 = reduce!("a + b")(chain(a, b));
    assert(r1 == 107);
    auto rR1 = reduceR!("a + b")(chain(a, b));
    assert(rR1 == 107);
*/
    // two funs
    auto r3 = reduce!("a + b", "a - b")(tuple(0, 0), a);
    assert(r3.field[0] == 7 && r3.field[1] == -7);
    auto rR3 = reduceR!("a + b", "a - b")(tuple(0, 0), a);
    assert(rR3.field[0] == 7 && rR3.field[1] == -1);

    auto r4 = reduce!("a + b", "a - b")(a);
    assert(r4.field[0] == 7 && r4.field[1] == -1);
    auto rR4 = reduceR!("a + b", "a - b")(a);
    assert(rR4.field[0] == 7 && rR4.field[1] == -1);

    a = [ 1, 2, 3, 4, 5 ];
    // Stringize with commas
    string rep = reduce!("to!string(a) ~ `, ` ~ to!(string)(b)")("", a); // the function has been 'symmetrized' compare to reduce's unittest
    assert(rep[2 .. $] == "1, 2, 3, 4, 5");
    string repR = reduceR!("to!string(a) ~ `, ` ~ to!string(b)")("", a);
    assert(repR[0 .. $-2] == "1, 2, 3, 4, 5");

    // Continued fraction
    double continuedFraction(double a, double b) { return to!double(a) + 1.0/b;}
    double[] piFrac = [3, 7, 15, 1, 292]; // pi contined fraction (ie 3.141592 '=' 3 + 1/(7 + 1/(15 + 1/(1 + 1/(292))))
    auto pi2 = reduceR!continuedFraction(piFrac);
    assert(approxEqual(pi2, PI));
}


/**
Given a function fun and a seed value, iterate repeatedly applies fun
and produces the infinite range seed, fun(seed), fun(fun(seed)), fun(fun(fun(seed))), ...
opIndex is defined, but may take some time (if you ask for a high index).

Example:
----
// Generating the natural numbers
auto natural = iterate!"a+1"(0);    // 0,1,2,3,4,5, (as ints)
assert(equal(take(5, natural), [0,1,2,3,4][]));

// Generating powers of two
auto powersOf(size_t n)() { return iterate!(to!string(n) ~ "*a")(1L); // 1, n, n*n, n*n*n, n*n*n*n (as longs)
assert(equal(take(5, powersOf!2), [1,2,4,8,16][]));
assert(powersOf!2[10] == 1024); // opIndex is defined

// Converging on a value
// (x+n/x)/2 applied repeatedly converges towards sqrt(n)
auto sqrtOf(size_t n)() {
    return iterate!Format("(a + %s/a)/2", n)(1.0);
}
auto sqrt2 = sqrtOf!2; // Converges towards sqrt(2), 1.414
popFrontN(sqrt2, 4); // letting it converge
assert(approxEqual(sqrt2.front, sqrt(2.0), 0.0000001)); // 5 iterations, already quite good

// Conway's 'Look and Say' sequence
// http://en.wikipedia.org/wiki/Look_and_say_sequence
int[] LookAndSay(int[] r) {
    int[] e;
    return reduce!"a ~ b.field[1] ~ b.field[0]"(e, std.algorithm.group(r));
}

auto conwaySequence = iterate!LookAndSay([1][]);
assert(equal(take(6, conwaySequence), [[1][],          /+ One 1 +/
                                       [1,1][],        /+ Two 1s +/
                                       [2,1][],        /+ One 2, one 1+/
                                       [1,2,1,1][],    /+ One 1, one 2, two 1s+/
                                       [1,1,1,2,2,1][],/+ Three 1s, two 2s, one 1+/
                                       [3,1,2,2,1,1][]
                                       ][]));
----
*/
struct Iterate(alias fun, S) {
    S _seed;

    this(S seed) { _seed = seed;}
    enum bool empty = false; // Infinite range
    S front() { return _seed;}
    void popFront() { _seed = unaryFun!fun(_seed);}
    S opIndex(size_t n) {
        S result = _seed;
        foreach(i;0..n) result = unaryFun!fun(result);
        return result;
    }
}

/// ditto
Iterate!(fun, S) iterate(alias fun, S)(S seed)
{
    return Iterate!(fun, S)(seed);
}

unittest
{
    // Generating the natural numbers
    auto natural = iterate!"a+1"(1);    // 1,2,3,4,5, (as ints)
    assert(equal(take(natural, 5), [1,2,3,4,5][]));
    assert(isInfinite!(typeof(natural)));

    // Generating powers of two
    auto powersOf(size_t n)() { return iterate!(to!string(n) ~ "*a")(1L);} // 1, n, n*n, n*n*n, n*n*n*n (as longs)
    assert(equal(take(powersOf!2, 5), [1,2,4,8,16][]));
    assert(powersOf!2[10] == 1024); // opIndex is defined

    // Converging on a value
    // (x+n/x)/2 applied repeatedly converges towards sqrt(n)
    auto sqrtOf(size_t n)() {
        return iterate!(Format!("(a+%s/a)/2", n))(1.0);
    }
    auto sqrt2 = sqrtOf!2; // Converges towards sqrt(2), 1.414
    popFrontN(sqrt2, 4); // letting is converge
    assert(approxEqual(sqrt2.front, sqrt(2.0), 0.0000001)); // 5 iterations, already quite good

    // Conway's 'Look and Say' sequence
    // http://en.wikipedia.org/wiki/Look_and_say_sequence
    int[] LookAndSay(int[] r) {
        int[] e;
        return reduce!"a ~ b.field[1] ~ b.field[0]"(e, std.algorithm.group(r));
    }

    auto conwaySequence = iterate!LookAndSay([1][]);
    assert(equal(take(conwaySequence, 6), [[1][],          /+ One 1 +/
                                           [1,1][],        /+ Two 1s +/
                                           [2,1][],        /+ One 2, one 1+/
                                           [1,2,1,1][],    /+ One 1, one 2, two 1s+/
                                           [1,1,1,2,2,1][],/+ Three 1s, two 2s, one 1+/
                                           [3,1,2,2,1,1][]
                                           ][]));
}

/**
A range that produces the successive result of reduce!fun(seed, range).
[seed, fun(seed, range.front), fun(fun(seed, range.front), range[1]), ...]
It's useful to get moving calculations, like moving sums, products, minima, etc.
Taken from Haskell.

Note:
only the one-function version is implemented. scan!(max, min, foo)(r) is not possible right now,
though not difficult to code...

Example:
----
// moving sum
auto r1 = [1,2,3,4];
auto s = scan!"a+b"(0,r1);
assert(equal(s, [0,1,3,6,10][])); // 0, 0+1, 0+1+2, 0+1+2+3, 0+1+2+3+4
s = scan!"a+b"(r1);
assert(equal(s, [1,3,6,10][])); // 1, 1+2, 1+2+3, 1+2+3+4

// factorials
auto fac = scan!"a*b"(1L, numbers(1)); // numbers(1) is 1,2,3,4,5,6,...
assert(equal(take(fac,6), [1,1,2,6,24,120][])); // 1, 1*1, 1*1*2, 1*1*2*3, 1*1*2*3*4, 1*1*2*3*4*5

//Moving minima
auto r2 = [1,2, -1, -4, 0, 3, 4];
auto r = scan!min(0,r2);
assert(equal(r, [0,0,0,-1,-4,-4,-4,-4][]));
r = scan!min(r2);
assert(equal(r, [1,1,-1,-4,-4,-4,-4][]));
----
*/
struct Scan(alias fun, S, R) if (isForwardRange!R)// && CompatibilityFuncArgs!(fun, S, R))
{
    S _result;
    R _range;
    bool done;

    this(S seed, R range)
    {
        _range = range;
        _result = seed;
        if (range.empty) done = true;
    }

    bool empty() {return _range.empty && done;}

    S front() { return _result;}

    void popFront()
    {
        if (!_range.empty)
        {
            _result = binaryFun!(fun)(_result, _range.front);
            _range.popFront;
        }
        else
        {
            done = true;
        }
    }
}

/// ditto
Scan!(fun, S, R) scan(alias fun, S, R)(S seed, R range) if (isForwardRange!R)// && CompatibilityFuncArgs!(fun, S, R))
{
    return Scan!(fun, S, R)(seed, range);
}

/// ditto
Scan!(fun, ElementType!R, R) scan(alias fun, R)(R range) if (isForwardRange!R)// && CompatibilityFuncArgs!(fun, R))
{
    ElementType!R seed;
    if (!range.empty)
    {
        seed = range.front;
        range.popFront;
    } // if range is empty, seed == (ElementType!R).init, but Scan will be empty anyway
    return Scan!(fun, ElementType!R, R)(seed, range);
}

unittest
{
    // moving sum
    auto r1 = [1,2,3,4];
    auto s = scan!"a+b"(0,r1);
    assert(equal(s, [0,1,3,6,10][]));
    s = scan!"a+b"(r1);
    assert(equal(s, [1,3,6,10][]));

    // factorial
    auto f = scan!"a*b"(1L, drop(numbers(),1));
    assert(equal(take(f,6), [1,1,2,6,24,120][]));

    // moving minima
    auto r2 = [1,2, -1, -4, 0, 3, 4];
    auto r = scan!min(0,r2);
    assert(equal(r, [0,0,0,-1,-4,-4,-4,-4][]));
    r = scan!min(r2);
    assert(equal(r, [1,1,-1,-4,-4,-4,-4][]));

    int[] e;
    assert(scan!"a+b"(e).empty);
}

/**
A variation on scan: this range returns the same values than scan, but paired
with the rest of the range.

Example:
----
auto arr = [1,2,3,4];
// running sum
assert(equal(scan!"a+b"(0,arr),  [0,1,3,6,10]));
// sum with rest of range
assert(equal(scan2!"a+b"(0,arr), [tuple(0, [1,2,3,4][]),
                                  tuple(1, [2,3,4][]),
                                  tuple(3, [3,4][]),
                                  tuple(6, [4][]),
                                  tuple(10,(int[]).init)]));

----
*/
struct Scan2(alias fun, S, R) if (isForwardRange!R)// && CompatibilityFuncArgs!(fun, S, R))
{
    S _result;
    R _range;
    bool done;

    this(S seed, R range)
    {
        _range = range;
        _result = seed;
    }

    bool empty() {return _range.empty && done;}

    Tuple!(S,R) front() { return tuple(_result, _range);}

    void popFront()
    {
        if (!_range.empty)
        {
            _result = binaryFun!(fun)(_result, _range.front);
            _range.popFront;
        }
        else
        {
            done = true;
        }
    }
}

/// ditto
Scan2!(fun, S, R) scan2(alias fun, S, R)(S seed, R range) if (isForwardRange!R)// && CompatibilityFuncArgs!(fun, S, R))
{
    return Scan2!(fun, S, R)(seed, range);
}

/// ditto
Scan2!(fun, ElementType!R, R) scan2(alias fun, R)(R range) if (isForwardRange!R)// && CompatibilityFuncArgs!(fun, R))
{
    ElementType!R seed;
    if (!range.empty)
    {
        seed = range.front;
        range.popFront;
    }
    return Scan2!(fun, ElementType!R, R)(seed, range);
}


/**
The cousin of scan. A range that produces the successive result of reduceR!fun(seed, range):
[seed, fun(range.back, seed), fun(range[1], fun(range.back, seed)), ...]
Taken from Haskell.
See_Also: scan, reduce, reduceR
Example:
----
auto r1 = [1,2,3,4];
auto s = scanR!"a+b"(0,r1); // moving sum
assert(equal(s, [0,4,7,9,10][])); // 0, 4+0, 3+4+0, 2+3+4+0, 1+2+3+4+0
s = scanR!"a+b"(r1);
assert(equal(s, [4,7,9,10][]));
auto r2 = [1,2, -1, -4, 0, 3, 4];
auto r = scanR!min(0,r2); // moving minimum
assert(equal(r, [0,0,0,0,-4,-4,-4,-4][]));
r = scanR!min(r2);
assert(equal(r, [4,3,0,-4,-4,-4,-4][]));

int[] e;
assert(scanR!"a+b"(e).empty);
----
*/
struct ScanR(alias fun, S, R) if (isBidirectionalRange!R)// && CompatibilityFuncArgs!(fun, S, R))
{
    S _result;
    R _range;
    bool done;

    this(S seed, R range)
    {
        _range = range;
        _result = seed;
        if (range.empty) done = true;
    }

    bool empty() {return _range.empty && done;}

    S front() { return _result;}

    void popFront()
    {
        if (!_range.empty)
        {
            _result = binaryFun!(fun)(_range.back,_result);
            _range.popBack;
        }
        else
        {
            done = true;
        }
    }
}

/// ditto
ScanR!(fun, S, R) scanR(alias fun, S, R)(S seed, R range) if (isBidirectionalRange!R)// && CompatibilityFuncArgs!(fun, S, R))
{
    return ScanR!(fun, S, R)(seed, range);
}

/// ditto
ScanR!(fun, ElementType!R, R) scanR(alias fun, R)(R range) if (isBidirectionalRange!R)// && CompatibilityFuncArgs!(fun, R))
{
    ElementType!R seed;
    if (!range.empty)
    {
        seed = range.back;
        range.popBack;
    } // if range is empty, seed == (ElementType!R).init, but ScanR will be empty anyway
    return ScanR!(fun, ElementType!R, R)(seed, range);
}

unittest
{
    auto r1 = [1,2,3,4];
    auto s = scanR!"a+b"(0,r1); // moving sum
    assert(equal(s, [0,4,7,9,10][])); // 4, 3+4, 2+3+4, 1+2+3+4
    s = scanR!"a+b"(r1);
    assert(equal(s, [4,7,9,10][]));
    auto r2 = [1,2, -1, -4, 0, 3, 4];
    auto r = scanR!min(0,r2); // moving minimum
    assert(equal(r, [0,0,0,0,-4,-4,-4,-4][]));
    r = scanR!min(r2);
    assert(equal(r, [4,3,0,-4,-4,-4,-4][]));

    int[] e;
    assert(scanR!"a+b"(e).empty);
}

/**
To Be Documented.

The n-ranges-in-parallel version of scan.
*/
struct TScan(alias fun, S, R...) if (allSatisfy!(isForwardRange,R))
{
    S _result;
    Knit!R _ranges;
    bool done;

    this(S seed, R ranges)
    {
        _ranges = knit(ranges);
        _result = seed;
    }

    bool empty() {return _ranges.empty && done;}

    S front() { return _result;}

    void popFront()
    {
        if (!_ranges.empty)
        {
            _result = naryFun!(fun)(_result, _ranges.front.expand);
            _ranges.popFront;
        }
        else
        {
            done = true;
        }
    }
}

/// ditto
TScan!(fun, S, R) tscan0(alias fun, S, R...)(S seed, R ranges) if (allSatisfy!(isForwardRange,R))
{
    return TScan!(fun, S, R)(seed, ranges);
}

/// ditto
TScan!(fun, ElementType!(Knit!R), R) tscan(alias fun, R...)(R ranges) if (allSatisfy!(isForwardRange,R))
{
    auto _ranges = knit(ranges);
//    if (_ranges.empty) throw new Exception("tscan: one or more of the input ranges is empty."); // enforce(!_ranges.empty) doesn't work
    auto seed = _ranges.front;
    foreach(i, Type;R) ranges[i].popFront;
    return tscan0!fun(seed, ranges);
}

/**
To Be Documented.

The right-fold cousin of tscan.
*/
struct TScanR(alias fun, S, R...) if (allSatisfy!(isBidirectionalRange,R))
{
    S _result;
    Knit!R _ranges;
    bool done;

    this(S seed, R ranges)
    {
        _ranges = knit(ranges);
        _result = seed;
    }

    bool empty() {return _ranges.empty && done;}

    S front() { return _result;}

    void popFront()
    {
        if (!_ranges.empty)
        {
            _result = naryFun!(fun)(_ranges.back.expand, _result);
            _ranges.popBack;
        }
        else
        {
            done = true;
        }
    }
}

/// ditto
TScanR!(fun, S, R) tscanR0(alias fun, S, R...)(S seed, R ranges) if (allSatisfy!(isBidirectionalRange,R))
{
    return TScanR!(fun, S, R)(seed, ranges);
}

/// ditto
TScanR!(fun, ElementType!(Knit!R), R) tscanR(alias fun, R...)(R ranges) if (allSatisfy!(isBidirectionalRange,R))
{
    ElementType!(Knit!R) seed;
    _ranges = knit(ranges);
    enforce(!_ranges.empty);
    seed = _ranges.back;
    foreach(i, Type;R) ranges[i].popBack;
    return TScanR!(fun, ElementType!(Knit!R), R)(seed, ranges);
}

/**
flatMap is the concatenation of the results of a map on a range.
If the mapped function produces another range, flatMap concatenates all these ranges
into a unique range. If the function returns only a value, flatMap is not different from map.
Example:
----
string text = "this is just a test.\nI mean, I have no idea\nif this will work.";
auto lines = splitlines(text);
assert(equal(lines, ["this is just a test.", "I mean, I have no idea", "if this will work."][]));
auto words = map!split(lines); // With map: you obtain a range of ranges
assert(equal(words, [["this", "is", "just", "a", "test."],
                     ["I", "mean,", "I", "have", "no", "idea"],
                     ["if", "this", "will", "work."]][]));
auto words2 = flatMap!split(lines); // With flatMap, it gives a range
assert(equal(words2, ["this", "is", "just", "a", "test.",
                      "I", "mean,", "I", "have", "no", "idea",
                      "if", "this", "will", "work."][]));

auto r1 = [1,2,3,4];
auto f = flatMap!"replicate(a,a)"(r1); // stretching a range
assert(equal(f, [1,2,2,3,3,3,4,4,4,4][]));

auto f2 = flatMap!("take(a, iota(0,int.max))")(r1); // growing ramps of numbers
assert(equal(f2, [0,0,1,0,1,2,0,1,2,3][]));
----
*/
Concat!(Map!(unaryFun!fun, R)) flatMap(alias fun, R)(R range) {
    return concat(map!(unaryFun!fun)(range));
}

unittest {
    string text = "this is just a test.\nI mean, I have no idea\nif this will work.";
    auto lines = splitlines(text);
    assert(equal(lines, ["this is just a test.", "I mean, I have no idea", "if this will work."][]));
    auto words = map!split(lines);
    assert(equal(words, [["this", "is", "just", "a", "test."], ["I", "mean,", "I", "have", "no", "idea"], ["if", "this", "will", "work."]][]));
    auto words2 = flatMap!split(lines);
    assert(equal(words2, ["this", "is", "just", "a", "test.", "I", "mean,", "I", "have", "no", "idea", "if", "this", "will", "work."][]));

    auto r1 = [1,2,3,4];
    auto f = flatMap!"replicate(a,a)"(r1);
    assert(equal(f, [1,2,2,3,3,3,4,4,4,4][]));

}

/**
Equivalent to the unfold of functional programming, the 'inverse' (dual?) of reduce. Given a seed and a generative
function, it creates an entire range. The function must have a special signature: it takes T... for arguments
and returns a Tuple!(Result, T...). The first part is the value for the range, the second part is used
as argument for the next step.

Compared to reduce which takes two arguments and returns one value, unfold uses a function
that takes n arguments and returns n+1 values. Thus, the expansion and the generation of a range.
Compare also to iterate, for which the value produced and the current state (next args) are the same.

Note that this version of unfold produces an infinite range.

Example:
----
Tuple!(R,R,R) fibonacci(R)(R a, R b) { return tuple(a, b, a+b);} // value produced: a. Next state: (b,a+b)
auto fibs = unfold!fibonacci!int(0,1);
assert(equal(take(10, fibs), [0,1,1,2,3,5,8,13,21,34][])); // lazily computes the Fibonacci numbers.
assert(isInfinite!(typeof(fibs))); // It's an infinite range.

// And now with BigInts!
auto fibs2 = unfold!(fibonacci!BigInt)(BigInt(0),BigInt(1));
assert(drop(fibs2,100).front == "573147844013817084101"); // Yeah, rapid growth
----
You can use 'string' functions, as in many places in this module. In this case, the fibonacci sequence is
defined simply as:
----
auto fibs3 = unfold!"tuple(a,b,a+b)"(0,1); // value produced: a. Next state: (b,a+b)
// "tuple(a,b,a+b)" is templated, so this would work directly with BigInts too.
----
But calculating Fibonacci numbers could easily be done easily with std.range.recurrence,
because the state has a constant size (int, int).
Calculating prime numbers on the other hand, necessitates a growing state (the list of primes already calculated).

Example:
----
// Given a list of primes, finds the next prime number
Tuple!(ulong, ulong[]) nextPrime(ulong[] primeList) {
    ulong value = primeList.back + 2; // This could be done better with a wheel
    bool isPrime = false;
    while(!isPrime) {
        foreach(prime; primeList) {
            if (prime * prime > value) {
                isPrime = true;
                primeList ~= value;
                break; // reached sqrt(value), it's a prime, no need to go further
            }
            else {
                if (value % prime == 0) { // not a prime, test next one
                    isPrime = false;
                    value += 2;
                    break;
                }
            }
        }
    }
    return tuple(value, primeList);
}

ulong[] seed = [2UL,3][];
auto primesAfter3 = unfold!nextPrime(seed);

assert(equal(take(10, primesAfter3), [5,7,11,13,17,19,23,29,31,37][]));
----

Another example, to be compared to reduceR example: calculating the
<a href = "http://en.wikipedia.org/wiki/Continued_fraction">continued fraction</a> development
of a real.

Example:
----
Tuple!(int, real) toCF(real d) { return tuple(to!int(d), 1.0 / (d - trunc(d)));}

auto piCF = unfold!toCF(PI); // Continued fraction dvt for pi 3.1415926...
// taken from http://mathworld.wolfram.com/PiContinuedFraction.html
assert(equal(take(12, piCF), [3,7,15,1,292,1,1,1,2,1,3,1][]));

auto eCF = unfold!toCF(E);   // For e 2.7818281828...
                             // It can be proven to be 2,1, 2,1,1, 4,1,1, 6,1,1, 8,1,1, ... 2n,1,1 , ...
assert(equal(take(17, eCF), [2,1,2,1,1,4,1,1,6,1,1,8,1,1,10,1,1][]));

double GoldenRatio = 0.5 * (1 + sqrt(5.0)); // Phi, the golden mean/ratio, about 1.618033988...
auto GRCF = unfold!toCF(GoldenRatio); // Known to be 1,1,1,1,1,1,1,1,1,1, ... ad infinitum
assert(equal(take(30, GRCF), replicate(30,1))); // Check
----
This example has a problem: it doesn't stop. But a number can have a finite continued development. A trivial example is
1.25 = 1 + 1/4. There is no way with unfold to stop the process, see unfold2 to do that.

See_Also: unfold2, reduce, reduceR, iterate, scan, scanR, recurrence, sequence
*/
struct Unfold(alias fun, T...)
{
    alias naryFun!fun nfun;
    static if (__traits(compiles, nfun!T)) // Can I instantiate nfun!T?
        alias nfun!T infun;  // instantiates n-fun.
    else
        alias nfun infun;    // It's a function, do nothing.

    alias ReturnType!infun Tup; // fun must return a Tuple!(FrontValue, T...)
    Tup _state;

    this(Tup.Types[1..$] initialParameters) { _state = infun(initialParameters);}
    enum bool empty = false;
    Tup.Types[0] front() { return _state.field[0];}
    void popFront() { _state = infun(_state.field[1..$]);}
}

/// ditto
Unfold!(fun,T) unfold(alias fun, T...)(T initialParameters) {
    return Unfold!(fun,T)(initialParameters);
}

unittest
{
    // Generating Fibonacci numbers
    auto fibs = unfold!"tuple(a,b,a+b)"(0,1);
    assert(equal(take(fibs, 10), [0,1,1,2,3,5,8,13,21,34][]));
    assert(isInfinite!(typeof(fibs)));

    // And now with BigInts!
    auto fibs2 = unfold!"tuple(a,b,a+b)"(BigInt(0),BigInt(1));
    assert(drop(fibs2,100).front == BigInt("354224848179261915075"));

    // An example that cannot be done with recurrence?, a lazy range of prime numbers.
    Tuple!(ulong, ulong[]) nextPrime(ulong[] primeList) { // Given a list of primes, find the next prime number
        ulong value = primeList.back + 2; // This could be done better with a wheel
        bool isPrime;
        while(!isPrime) {
            foreach(prime; primeList) {
                if (prime * prime > value) {
                    isPrime = true;
                    primeList ~= value;
                    break; // reached sqrt(value), no need to go further
                }
                else {
                    if (value % prime == 0) { // not a prime
                        isPrime = false;
                        value += 2;
                        break;
                    }
                }
            }
        }
        return tuple(value, primeList);
    }

    ulong[] seed = [2UL,3][];
    auto primesAfter3 = unfold!nextPrime(seed);
    assert(equal(take(primesAfter3, 10), [5,7,11,13,17,19,23,29,31,37][]));

    // Continued fraction
    Tuple!(int, real) toCF(real d) { return tuple(to!int(floor(d)), 1.0 / (d - trunc(d)));}

    auto piCF = unfold!toCF(PI); // Continued fraction dvt for pi 3.1415926...
    assert(equal(take(piCF, 12), [3,7,15,1,292,1,1,1,2,1,3,1][])); // taken from http://mathworld.wolfram.com/PiContinuedFraction.html

    auto eCF = unfold!toCF(E);   // For e 2.7818281828... It can be proved to be 2,1, 2,1,1, 4,1,1, 6,1,1, 8,1,1, ... 2n,1,1 , ...
    assert(equal(take(eCF, 17), [2,1,2,1,1,4,1,1,6,1,1,8,1,1,10,1,1][]));

    double GoldenRatio = 0.5 * (1 + sqrt(5.0)); // Phi, the golden mean/ratio, about 1.618033988...
    auto GRCF = unfold!toCF(GoldenRatio); // Known to be 1,1,1,1,1,1,1,1,1,1, ... ad infinitum
    assert(equal(take(GRCF, 30), replicate(1,30))); // Check

/+
// Sequences from Hofstadter's "Godel, Escher & Bach"'
    Tuple!(Tuple!(int,int),int[],int[]) MaleFemale(int[] M, int[] F)
    {
        int n = M.length;
        int male = n - F[M[n-1]];
        M ~= male;
        int female = n - M[F[n-1]];
        F ~= female;
        return tuple(tuple(male,female), M, F);
    }

    auto mf = unfold!MaleFemale([0][],[1][]);
//    writeln(drop(3_00_000,mf).front);


    Tuple!(int, int[]) g(int[] G)
    {
        int n = G.length;
        auto gn = n - G[G[n-1]];
        return tuple(gn, G ~ gn);
    }

    auto gsequence = unfold!g([0][]);
//    wr(take(100, gsequence));

    Tuple!(int, int[]) q(int[] Q)
    {
        int n = Q.length;
        auto qn = Q[n - Q[n-1]] + Q[n - Q[n-2]];
        return tuple(qn, Q ~ qn);
    }

    auto qsequence = unfold!q([1,1]);
//    wr(take(10000, qsequence));
+/
}

/**
A generalization of unfold with a second function: a predicate telling it when to stop (it stops when pred(elem,state) is false).
The former unfold produces a infinite range, this version can stop when you decide it to.
It's also sometimes called an anamorphism (see Wikipedia). It's not an infinite range (in the 'enum bool empty == false' sense).

Note: the wikipedia example stops if pred(elem) is true and acts only on the generated value, not the global state.
As such it's equivalent to takeWhile!(not!pred)(unfold!fun) and so I decided here to use a more general predicate.

Example:
----
Tuple!(int, int, int) fibonacci(int a, int b) { return tuple(b, b, a+b);}
auto fibs = unfold2!(fibonacci, "a > 100")(0,1); // stops when you reach 100
assert(equal(fibs, [1,1,2,3,5,8,13,21,34,55,89][])); // Generates 89. Next value would be 55+89 > 100 -> stops.

// see unfold for the definition of nextPrime.
// stops when the internal array storing the primes is 10 elements long
auto primesAfter3 = unfold2!(nextPrime, "b.length == 10")(seed);
assert(equal(primesAfter3, [5,7,11,13,17,19,23][])); // Internally stores seed also, so the state is [2,3,5,7,11,13,17,19,23,29].
                                                      // 29 is the 10th element in the array, which stops the unfolding.
// Continued fraction
Tuple!(real, real) toCF(real d) { return tuple(floor(d), 1.0 / (d - floor(d)));}
auto cf = unfold2!(toCF, "isnan(a) || a > 1E+6")(3.245); // Continued fraction dvt for 3.245
// can be calculated to be 3 + 1/(4 + 1/(12 + 1/4))
assert(equal(cf, [3,4,12,3,1][])); // ends with 3,1 => 3+1/1 (ie. 4)
----
*/
struct Unfold2(alias fun, alias pred, T...)
{
    alias naryFun!fun nfun; // string preparation
    static if (__traits(compiles, nfun!T)) // Can I instantiate nfun!T?
        alias nfun!T infun;  // instantiates n-fun.
    else
        alias nfun infun;    // It's a function, do nothing.

    alias ReturnType!infun Tup; // fun must return a Tuple!(FrontValue, T...)
    Tup _state;

    this(Tup.Types[1..$] initialParameters) { _state = infun(initialParameters);}
    bool empty() { return Prepare!(pred, Tup.Types)(_state);}
    Tup.Types[0] front() { return _state.field[0];}
    void popFront() { _state = infun(_state.field[1..$]);}
}

/// ditto
Unfold2!(fun, pred, T) unfold2(alias fun, alias pred, T...)(T initialParameters) {
    return Unfold2!(fun, pred,T)(initialParameters);
}

unittest
{
//    Tuple!(int, int, int) fibonacci(int a, int b) { return tuple(a, b, a+b);}
    auto fibs = unfold2!("tuple(a,b,a+b)", "a > 100")(0,1); // stops when the generated value is > 100
    assert(equal(fibs, [0,1,1,2,3,5,8,13,21,34,55,89][]));

    // An example that cannot be done with recurrence, a lazy range of prime numbers.
    Tuple!(ulong, ulong[]) nextPrime(ulong[] primeList) { // Given a list of primes, find the next prime number
        ulong value = primeList.back + 2; // This could be done better with a wheel
        bool isPrime;
        while(!isPrime) {
            foreach(prime; primeList) {
                if (prime * prime > value) {
                    isPrime = true;
                    primeList ~= value;
                    break; // reached sqrt(value), no need to go further
                }
                else {
                    if (value % prime == 0) { // not a prime
                        isPrime = false;
                        value += 2;
                        break;
                    }
                }
            }
        }
        return tuple(value, primeList);
    }

    ulong[] seed = [2UL,3][];
    auto primesAfter3 = unfold2!(nextPrime, "b.length >= 10")(seed);
    assert(equal(primesAfter3, [5,7,11,13,17,19,23][])); // Internally store seed also, so state is [2,3,5,7,11,13,17,19,23,29].
                                                          // 29 is the 10th element in the array, which stops the unfolding.

    // Continued fraction
    Tuple!(real, real) toCF(real d) { return tuple(floor(d), 1.0 / (d - floor(d)));}
    auto cf = unfold2!(toCF, "isnan(a) || a > 1E+6")(3.245); // Continued fraction dvt for pi 3.1415926...
    assert(equal(cf, [3,4,12,3,1][]));
}

/**
A list comprehension for D. List comprehensions (also called for-comprehension
in some languages) are a powerful way to create sequences from input ranges, filters and a generative function.

Here, the syntax is:
----
comp!(generator, predicate)(inputs...);
----
It will then lazily generate the combination of all inputs, filter them through the predicate
and apply the generator to produce the values.

The generator and predicate can be written in a string form, as the functions in std.algorithm.map or .filter,
only generalized to 'a'-'z'. 'a' refers to elements from the first input, 'b' from the second and so on...
You can use other function like sin, cos, abs (or even tuple!) to generate values.

Example:
----
// find the pythagorean triplets for numbers between 1 and 10
// In set notation it's {(a,b,c) | a*a+b*b==c*c, a in [1,10], b in [1,10], c in [1,10]}
input = numbers(1, 11);
auto lc = comp!("tuple(a,b,c)", "a*a+b*b == c*c && a<b")(input, input, input);
// it finds the two triplets : Tuple!(int, int,int)(3,4,5) and (6,8,10)
assert(equal(lc, [tuple(3,4,5), tuple(6,8,10)][]));
----

Limitations:
It cannot directly do bindings (having one of the input ranges based on another one, like input2 = take(5, (range1.front))
successively for each range1.front).
In this case, you must fall back on a combination of map, filter and flatMap. Though it should be possible
to code this.
*/
CompType!(gen, pred, R) comp(alias gen, alias pred, R...)(R inputs)
if (allSatisfy!(isForwardRange, R))
{
    return tmap!gen(tfilter!pred(combinations(inputs)));
}

template CompType(alias gen, alias pred, R...) {
    alias TMapType!(gen, TFilterType!(pred, Combinations!R)) CompType;
}

unittest
{
    Tuple!(int, int, int) foo(int a, int b, int c) { return tuple(a,b,c);}
    int foo2(int a, int b, int c) { return a+b+c;}
    bool pythagorean(int a, int b, int c) { return a*a+b*b == 2*c*c && a<b;}
    auto input = numbers(1,11);

    auto lc = comp!(foo, "a*a+b*b == c*c && a<b")(input, input, input);
    assert(equal(lc, [tuple(3,4,5), tuple(6,8,10)][]));
}

/**
A small application of range comprehension ('comp'): outputs the 'intersection' of n ranges. That's the
elements present in all ranges. I say 'intersection' (with quotes) because if some ranges are not sets
there will be duplicates.
Example:
----
auto r1 = [0,1,2,3,2,3];
auto r2 = [2.0,4,5,3,7,1,0];
short[] r3 = [-2,-3,1,0];
auto i = intersection(r1,r2,r3); // i.front is a double
assert(equal(i, [0,1][]));

auto i2 = intersection(r1,r2);
assert(equal(i2, [0,1,2,3,2,3][]));
----
*/
IntersectionType!R intersection(R...)(R ranges) if (CompatibleRanges!R) {
    return comp!("to!" ~ CommonType!(ElementTypes!R).stringof ~ "(a)", allEqual!(staticMap!(Unqual,ElementTypes!R)))(ranges);
}

template IntersectionType(R...) {
    alias CompType!("to!" ~ CommonType!(ElementTypes!R).stringof ~ "(a)", allEqual!(staticMap!(Unqual, ElementTypes!R)), R) IntersectionType;
}

unittest
{
    auto r1 = [0,1,2,3,2,3];
    auto r2 = [2.0,4,5,3,7,1,0];
    short[] r3 = [-2,-3,1,0];
    auto i = intersection(r1,r2,r3); // i.front is a double
    assert(equal(i, [0,1][]));

    auto i2 = intersection(r1,r2);
    assert(equal(i2, [0,1,2,3,2,3][]));
}

/+
/**
As intersection, a small one-liner to join n ranges : the concatenation
of the ranges minus their intersection.
Example:
----
auto r1 = [0,1,2,3,4,5];
auto r2 = [3,4,5,6,7];
auto j = join(r1, r2);
assert(equal(j [0,1,2,3,4,5,6,7][]));
----
*/
Without!(Chain!R, IntersectionType!R) join(R...)(R ranges) {
    return without(chain(ranges), intersection(ranges));
}

unittest
{
    auto r1 = [0,1,2,3,4,5];
    auto r2 = [3,4,5,6,7];
    auto j = join(r1, r2);
    assert(equal(j, [0,1,2,3,4,5,6,7][]));
}
+/

/**
As intersection, a small one-liner to produce the symmetric difference between n ranges (ie the
elements in the ranges that are not in their intersection).
Example:
----
auto r1 = [0,1,2,3,7];
auto r2 = [1,2,5,6,0];
auto s = symmetricDifference(r1, r2);
assert(equal(s, [3,5,7,6][]));
----
*/
Without!(Chain!R, IntersectionType!R) symmetricDifference(R...)(R ranges) {
    return without(chain(ranges), intersection(ranges), true); // true means intersection(ranges) is cycled inside without
}

unittest
{
    auto r1 = [0,1,2,3,7];
    auto r2 = [1,2,5,6,0];
    auto s = symmetricDifference(r1, r2);
    assert(equal(s, [3,7,5,6][]));
}

/**
Another kind of list comprehension, based on a Haskell proposal for parallel list comprehension. The n ranges are iterated
in parallel (in lockstep) instead of generating all combinations. They are filtered with pred and the values
are generated by applying gen to the resulting tuples.

As for comprehension and setComprehension, you can use standard functions or 'string' functions, with
letters 'a'-'z' representing the current value for the first, second, etc. ranges.
Example:
----
auto r1 = numbers(1,100);
string sentence = "The quick brown fox jumped over the lazy dog.";
auto words = split(sentence);
// get the words that are longer than a growing value and capitalize them
auto plc = pComp!("capitalize(b)", "b.length > a")(r1, words);
assert(equal(plc, ["The", "Quick", "Brown", "Jumped"]));
----

One interesting use case is on indexed ranges. You can use pcomp to filter on the element's indices
and expose elements (and obtaining stride-like or drop-like behavior, see below), or filter on elements
and return indices (like do 'positions' and 'indices' in this module).
Example:
----
auto r2 = [0,1,2,3,4,5,6,7];
auto myDrop(size_t n, R)(R range) {
    return pComp!("b", "a>="~to!string(n))(indexed(range));
}
assert(equal(myDrop!3(r2), [3,4,5,6,7][]));

auto myStride(size_t n, R)(R range) {
    return pComp!("b", "a%"~to!string(n)~" == 0")(indexed(range));
}
assert(equal(myStride!3(r2), [0,3,6][]));

auto dropEvery(size_t n, R)(R range) {
    return pComp!("b", "a%"~to!string(n)~"!="~to!string(n)~"-1")(indexed(range));
}
assert(equal(dropEvery!3(r2), [0,1, 3,4, 6,7][]));
----

See_Also:
tfilter, tmap, comp, setComprehension, select, subranges.
*/
PCompType!(gen, pred, R) pComp(alias gen, alias pred, R...)(R inputs)
if (allSatisfy!(isForwardRange, R))
{
    return tmap!gen(tfilter!pred(inputs));
}

template PCompType(alias gen, alias pred, R...) {
    alias TMapType!(gen, TFilterType!(pred, R)) PCompType;
}

unittest
{
    auto r1 = numbers(1,100);
    string sentence = "The quick brown fox jumped over the lazy dog.";
    auto words = split(sentence);
    auto plc = pComp!("capitalize(b)", "b.length > a")(r1, words);
    assert(equal(plc, ["The", "Quick", "Brown", "Jumped"][]));

    auto r2 = [0,1,2,3,4,5,6,7];
    auto myDrop(size_t n, R)(R range) {
        return pComp!("b", "a>="~to!string(n))(indexed(range));
    }
    assert(equal(myDrop!3(r2), [3,4,5,6,7][]));

    auto myStride(size_t n, R)(R range) {
        return pComp!("b", "a%"~to!string(n)~" == 0")(indexed(range));
    }
    assert(equal(myStride!3(r2), [0,3,6][]));

    auto dropEvery(size_t n, R)(R range) {
        return pComp!("b", "a%"~to!string(n)~"!="~to!string(n)~"-1")(indexed(range));
    }
    assert(equal(dropEvery!3(r2), [0,1, 3,4, 6,7][]));
}


/**
A set comprehension for D, using asSet on comp.
----
auto input = numbers(1,5);
auto sc = setComp!("a+b+c", "a + b > c")(input, input, input);
assert(equal(sc, [3,4,5,6,7,8,9,10,11,12][])); // The equivalent comprehension is three times as long.
----
See_Also: comprehension, asSet.
*/
AsSet!(CompType!(gen,pred,R)) setComp(alias gen, alias pred, R...)(R inputs) {
    return asSet(comp!(gen, pred)(inputs));
}

unittest
{
    auto input = numbers(1,5);
    auto sc = setComp!("a+b+c", "a + b > c")(input, input, input);
    assert(equal(sc, [3,4,5,6,7,8,9,10,11,12][]));
    // The equivalent comprehension is three times as long.
}

/**
Given a variadic list of ranges and a predicate (default: "a<b"), merge will 'merge' the ranges
according to the following algorithm: it compare all fronts, finds the front
which verifies the predicate with all other fronts (the 'smallest') and outputs
it, advancing its range.
If all ranges are sorted with the predicate, it's equivalent to the call:
----
sortAsArray!pred(chain(ranges)); // Which may be exactly what you want instead of 'merge'
----
But if the ranges are not sorted, the results are different:
Example:
----
auto r = [0,2,3];
auto r2 = [1,4,5];
auto r3 = [1,6,7,0];
int[] e;
auto m = merge(r,e,r2,r3);
assert(equal(m, [0,1,1,2,3,4,5,6,7,0][]));
----
*/
struct Merge(alias pred, R...) if (allSatisfy!(isForwardRange, R) && CompatibleRanges!R)
{
    R _ranges;
    alias binaryFun!pred predicate;
    CommonElementType!R _front;
    size_t index;
    bool isEmpty;

    void findSmallest() {
        if (allEmpty(_ranges)) { isEmpty = true; return;}

        index = 0;
        foreach(i, Unused; R) {
            if (!_ranges[i].empty) {
                _front = _ranges[i].front;
                index = i;
                break;
            }
        }
        foreach(i, Unused; R) {
            if (!_ranges[i].empty && predicate(_ranges[i].front, _front)) {
                _front = _ranges[i].front;
                index = i;
            }
        }
        foreach(i, Unused; R) {
            if (i == index) _ranges[i].popFront;
        }
    }

    this(R ranges) { _ranges = ranges; findSmallest();}
    bool empty() { return isEmpty;}
    CommonElementType!R front() { return _front;}
    void popFront() { findSmallest();}
}

/// ditto
Merge!(pred, R) merge(alias pred = "a<b", R...)(R ranges) if (allSatisfy!(isForwardRange, R) && CompatibleRanges!R)
{
    return Merge!(pred, R)(ranges);
}

unittest
{
    auto r = [0,2,3];
    auto r2 = [1,4,5];
    auto r3 = [1,6,7,0];
    int[]e;
    auto m = merge(r,e,r2,r3);
    assert(equal(m, [0,1,1,2,3,4,5,6,7,0][]));
}

/**
Another version, for two ranges and with the predicate being automatically "a<b".
It's faster than the generic merge, and get rid of duplicates.
Example:
----
// Calculating Hamming numbers, numbers of the form 2^i * 3^j * 5^k
// see http://en.wikipedia.org/wiki/Regular_number
// Dijkstra's algorithm heavily uses merge.
T[] hamming(T)(T[] r)
{
    return 1 ~ merge2(map!"2*a"(r),merge2(map!"3*a"(r),map!"5*a"(r)));
}

auto hammingNumbers()
{
    return iterate!hamming([1UL][]); // develop the Hamming sequence at each iteration.
}
// 1,2,3,4,5,6,8,9,10,12,...
// For the i-th iteration, the sequence is complete only up to 2^i,
// but has much more numbers already calculated.
// The algorithm finds all Hamming numbers less than 1000_000_000_000 (1E+12) in 250 ms on my computer.
// There are 3428 of them and it takes 39 iterations to find them all. At this step the generated
// Hamming sequence has more than one million numbers already calculated.
// (most may be false due to reaching ulong.max).
----
*/
CommonElementType!(R1,R2)[] merge2(R1, R2)(R1 r1, R2 r2) {
    alias CommonElementType!(R1,R2) T;
    T[] result;
    while (!r1.empty && !r2.empty) {
        T a = r1.front;
        T b = r2.front;
        if (a<b) {
            result ~= a;
            r1.popFront;
        }
        else {
            if (a>b) {
                result ~= b;
                r2.popFront;
            }
            else {
                result ~= a;
                r1.popFront;
                r2.popFront;
            }
        }
    }
    if (r1.empty) return array(chain(result,r2));
    if (r2.empty) return array(chain(result,r1));
    assert(0);
}

/**
Internal helper function. Takes a number coded as
a dynamic array of bits (boolean), returns the next number.
The low-order bits are the first elements. That is, 8 is 0b1000 -> [false, false, false, true].
Example:
----
bool[] num; // equivalent to [false];
foreach(i; 0..4) { // 0 -> 1 -> 2 -> 3 -> 4
    num = nextBoolean(num);
}
assert(num == [false, false, true][]); // 4 is 0b100, here encoded as [false, false, true]
----
*/
bool[] nextBoolean(bool[] t) {
    bool carry = true;
    auto result = t.dup;
    foreach(ref elem; result) {
        if (elem && carry) {
            elem = false;
        }
        else {
            elem ^= carry;
            carry = false;
            break;
        }
    }
    return carry ? result ~ carry : result;
}

/**
Given a dynamic array of flags (boolean), extracts the corresponding elements
and returns the corresponding subrange as a comprehension (another lazy range).
If stops at whichever is shortest between flags and range.
It works for infinite ranges, too.
See_Also: fromIndex.
Example:
----
auto r = [0,1,2,3];
auto s01 = select([false, true][], r);
assert(equal(s01, [1][]));
auto s13 = select([false, true,false,true][], r);
assert(equal(s13, [1,3][]));
----
*/
PCompType!("b","a",bool[], R) select(R)(bool[] flags, R range) if (isForwardRange!R)
{
    return pComp!("b","a")(flags, range);
}

unittest
{
    auto r = [0,1,2,3];
    auto s01 = select([false, true][], r);
    assert(equal(s01, [1][]));
    auto s13 = select([false, true,false,true][], r);
    assert(equal(s13, [1,3][]));
}

/**
Lazily returns all subranges of a range: the ranges created
by taking only some elements of the range in the same order.

For this implementation, it begins with the empty range.
For a range of length n, subranges has 2^^n elements.

Note:
It works for infinite ranges.

Example:
----
auto r = [0,1,2];
auto sr = subranges(r);
int[][] witness = [[],
                   [0],
                   [1],
                   [0,1],
                   [2],
                   [0,2], [1,2],
                   [0,1,2]];

foreach(elem; sr) {
    assert(equal(elem, witness.front));
    witness.popFront;
}
----
*/
SubRanges!R subranges(R)(R range) if (isForwardRange!R)
{
    static if (isInfinite!R)
        return unfold!(nextSub!R)((bool[]).init, range);
    else static if (hasLength!R)
        return unfold2!(nextSub!R, endSubRange!R)((bool[]).init, range);
}

Tuple!(ElementType!R[]/*PCompType!("b","a",bool[], R)*/, bool[], R) nextSub(R)(bool[] flags, R range) if (isForwardRange!R)
{
   return tuple(array(select(flags, range)), nextBoolean(flags), range);
}

// helper function to make DMD happy with subRanges return type
bool endSubRange(R)(ElementType!R[]/*PCompType!("b","a",bool[], R)*/ p, bool[] b, R r) if (isForwardRange!R && hasLength!R)
{
    return (!r.empty && b[0] && b.length > r.length)
        || (r.empty && b == [false, true]); // awful hack to get subranges([]) == [[]]
}

template SubRanges(R) if (isForwardRange!R)
{
    static if (isInfinite!R)
        alias Unfold!(nextSub!R, bool[], R) SubRanges;
    else static if (hasLength!R)
        alias Unfold2!(nextSub!R, endSubRange!R, bool[], R) SubRanges;
}

unittest
{
    auto r = [0,1,2];
    auto sr = subranges(r);
    int[][] witness = [[], [0], [1], [0,1], [2], [0,2], [1,2], [0,1,2]];

    foreach(elem; sr) {
        assert(equal(elem, witness.front));
        witness.popFront;
    }

    int[] e;
    auto sre = subranges(e);
    assert(sre.front.empty);
    sre.popFront;
    assert(sre.empty);
}

/+ strange error with isInfinite on subranges...
/**
Returns the variations of a range: the permutations of all subranges (including the range itself).
Example:
----
auto r = [0,1,2];
auto v = variations(r);
assert(equal(v, [  [],   /+ empty range +/
                   [0],
                   [1],
                   [0,1], [1,0],
                   [2],
                   [0,2], [2,0],
                   [1,2], [2,1],
                   [0,1,2], [1,2,0], [2,0,1], [1,0,2], [0,2,1], [2,1,0]
                ][]));
----
*/
Variations!R variations(R)(R range) if (isForwardRange!R)
{
    return flatMap!permutations(subranges(range));
}

template Variations(R) if (isForwardRange!R)
{
    alias Concat!(Map!(permutations, Unfold2!(nextSub!R, endSubRange!R, bool[], R))) Variations;
}

unittest
{
    auto r = [0,1];
    auto v = variations(r);
//    assert(equal(v, [  [],   /+ empty range +/
//                       [0],
//                       [1],
//                       [0,1], [1,0],
//                       [2],
//                       [0,2], [2,0],
//                       [1,2], [2,1],
//                       [0,1,2], [1,2,0], [2,0,1], [1,0,2], [0,2,1], [2,1,0]
//                    ][]));

//    int[] e;
//    assert(equal(variations(e), [e][]));
}
+/

/**
std.algorithm.sort does an efficient in-place sort, but it requires the
input range to returns its elements by reference. As it's not the case for
most of the ranges here (mainly because they simply cannot), sortAsArray
is provided here if you need to sort a range with an ordering function.
It just calls array() on range, sorts it and return the sorted array.

See_Also:
indexSorted
Example:
----
auto r1 = [5,1,2,3,4];
auto r2 = [4.0,3.0,2.0,1.0,0.0];
auto r3 = ["abc","def","ghi"];
auto s = knit(r1,r2,r3); // sort(s) won't work
// sort with no ordering function defined, defaults to "a < b" (it's defined on tuples)
assert(equal(sortAsArray(s), [tuple(1,3.0,"def"),tuple(2,2.0,"ghi"),tuple(5,4.0,"abc")][]));
// specifying an ordering function: sorting according to the second field
assert(equal(sortAsArray!"a.field[1] < b.field[1]"(s), [tuple(2,2.0,"ghi"),tuple(1,3.0,"def"),tuple(5,4.0,"abc")][]));

// Another kind of range, with front&back not by ref
auto st = stutter(3, r2); // st is equivalent to [5,5,5,1,1,1,2,2,2,3,3,3,4,4,4][] but cannot be sorted by sort
assert(equal(sortAsArray(st), stutter(3, sortAsArray(r2))));
----
*/
ElementType!R[] sortAsArray(alias pred = "a < b", R)(R range) if (isForwardRange!R && !isInfinite!R)
{
    auto a = array(range);
    sort!pred(a);
    return a;
}

unittest
{
    auto r1 = [5,1,2,3,4];
    auto r2 = [4.0,3.0,2.0,1.0,0.0];
    auto r3 = ["abc","def","ghi"];
    auto s = knit(r1,r2,r3);
    assert(equal(sortAsArray(s), [tuple(1,3.0,"def"),tuple(2,2.0,"ghi"),tuple(5,4.0,"abc")][]));
    assert(equal(sortAsArray!"a.field[1] < b.field[1]"(s), [tuple(2,2.0,"ghi"),tuple(1,3.0,"def"),tuple(5,4.0,"abc")][]));

    auto st = stutter(3, r2); // st is equivalent to [5,5,5,1,1,1,2,2,2,3,3,3,4,4,4][] but cannot be sorted by sort
    auto sortedSt = sortAsArray(st);
    assert(equal(sortedSt, stutter(3, sortAsArray(r2))));

    int[] e;
    auto ae = sortAsArray(e);
    assert(ae.empty);
}

/**
Groups a range by values and returns the grouped values as an array. It's a bidirectional range.
Example:
----
auto test = [0,1,1,2,2,2,3,3,3,3,4,4,4,5,5,6];
assert(equal(group(test), [[0], [1,1], [2,2,2], [3,3,3,3], [4,4,4], [5,5], [6]][]));
assert(equal(group("Mississippi"), ["M", "i", "ss", "i", "ss", "i", "pp", "i"][]));
----
Update: A function with the same name already exists in std.algorithm, with a predicate, even.
No need to work further on this.
*/
struct Group(R) if (isForwardRange!R) {
    R _range;
    alias ElementType!R ET;
    ET[] groupFront, groupBack; // groupBack will be used only for bidir range

    ET[] generateFront(T)(T r) if (isInputRange!T) {
        ET[] f = [r.front];
        r.popFront;
        while(!r.empty && r.front == f[0]) {
            f ~= r.front;
            r.popFront;
        }
        return f;
    }

    this(R r) {
        _range = r;
        if (!_range.empty) groupFront = generateFront(_range);
        static if (isBidirectionalRange!R) {
            if (!_range.empty) groupBack = generateFront(retro(_range));
        }
    }

    bool empty() { return _range.empty;}
    ET[] front() { return groupFront;}
    void popFront() {
        auto f = _range.front;
        while(!_range.empty && _range.front == f) {
            _range.popFront;
        }
        if (!_range.empty) groupFront = generateFront(_range);
    }

    static if (isBidirectionalRange!R) {
        ET[] back() { return groupBack;}
        void popBack() {
            auto b = _range.back;
            while(!_range.empty && _range.back == b) {
                _range.popBack;
            }
            if (!_range.empty) groupBack = generateFront(retro(_range));
        }
    }
}

/// ditto
Group!(R) group(R)(R range) {
    return Group!(R)(range);
}

unittest {
    auto test = [0,1,1,2,2,2,3,3,3,3,4,4,4,5,5,6];
    auto g = group(test);
    assert(equal(g, [[0], [1,1], [2,2,2], [3,3,3,3], [4,4,4], [5,5], [6]][]));
    assert(equal(retro(g), [[6], [5,5], [4,4,4], [3,3,3,3], [2,2,2], [1,1], [0]][]));
    int[] e;
    assert(group(e).empty);
    // trouble with change in strings/dchar with DMD 2.041
//    assert(equal(group(cast(dchar[])"Mississippi"), cast(dchar[][])["M", "i", "ss", "i", "ss", "i", "pp", "i"][]));
}

Tuple!(ElementType!R, size_t) valueLength(R)(R r) if (isInputRange!R && hasLength2!R){
    return tuple(r.front, r.length);
}

/**
Given a range r, will return the run-length encoding of r, as a range of tuples(element, length).
Example:
----
auto test = [0,1,1,2,2,2,3,3,3,3,4,4,4,5,5,6][];
auto rle = runLengthEncode(test);
wr(rle); // will print Tuple!(int, size_t): (0,1) (1,2) (2,3) (3,4) (4,3) (5,2) (6,1)
----
*/
Map!(valueLength, Group!R) runLengthEncode(R)(R range) {
    return map!(valueLength)(group(range));
}

/**
Returns true iff range1 contains range2 (as one block, not separated elements). Do not presumes the ranges
are sorted (so, does a linear scan).
Range2 can also be just one element.

Note:
Another version could be possible, with one of the ranges as a template arg: contains!"bar"(r).
That way, it could be used a predicate by filtering function like dropWhile, takeWhile and filter.
TODO: maybe a predicate.d, containing predicates and predicate-constructing functions?
TODO: it can be more efficient for slice-able ranges.
TODO: maybe just use std.algo.find?

Examples:
----
assert("foobarbaz".contains("bar")); // true
assert("foobarbaz".contains("b"));   // true
assert("foobarbaz".contains('b'));   // true
//
assert(!("foobarbaz".contains("c")));// doesn't contain "c"
assert("foobarbaz".contains(""));    // "" (an empty range) is in any range
assert(!("".contains("abc")));       // an empty range contains nothing
----
*/
bool contains(R1, R2)(R1 range1, R2 range2) if (allSatisfy!(isInputRange, R1, R2))
{
    if (range1.empty) return false;
    if (range2.empty) return true;
    while(!range1.empty && !range2.empty && (range1.front != range2.front)) {
        range1.popFront;
    }
    bool containsIt = false;
    while(!containsIt && !range1.empty)
    {
        containsIt = (startsWith(range1, range2) == 1);
        if (!range1.empty) range1.popFront;
        while(!range1.empty && range1.front != range2.front) {
            range1.popFront;
        }
    }
    return containsIt;
}

/// ditto
bool contains(R1, E)(R1 range1, E element) if (isInputRange!R1 && !isInputRange!E && is(CommonType!(ElementType!R1, E)))
{
    if (range1.empty) return false;
    while(!range1.empty && (range1.front != element)) {
        range1.popFront;
    }
    return range1.empty ? false : true;
}

unittest
{
    assert("foobarbaz".contains("bar")); // true
    assert("foobarbaz".contains("b"));   // true
    assert("foobarbaz".contains('b'));   // true
    assert(!("foobarbaz".contains("c")));// doesn't contain "c"
    assert("foobarbaz".contains(""));    // "" (an empty range) is in any range
    assert(!("".contains("abc")));       // an empty range contains nothing
}

/**
To Be Documented.


rotates a range to the left by n positions (ie: take the first n elements and put them at the end).
R must be a forward range and have a length. If R is infinite, it just drops the first n terms.

If n is negative, it rotates it to the right.
*/
Rotate!R rotate(R)(R range, int n = 1) if (isForwardRange!R)
{
    return Rotate!R(range,n);
}

struct Rotate(R) if (isForwardRange!R && !isBidirectionalRange!R)
{
    int n;
    R _r;
    Take!R _end;

    this(R r, int n)
    {
        if (n<0) { throw new Exception("Cannot rotate to the right a non-bidirectional range."); }
        this.n = n;
        _r = r;
        static if (!isInfinite!R)
        {
            static if (hasLength!R)
                auto l = _r.length;
            else
                auto l = walkLength(_r, abs(n));
            if (l==0) n = 0;
            if (l<abs(n)) {n %= l;}
        }

        _end = take(_r, n);
        popFrontN(_r, n);
    }

    static if (isInfinite!R)
        enum bool empty = false;
    else
        bool empty() { return _r.empty && _end.empty; }

    ElementType!R front() { return (_r.empty) ? _end.front : _r.front;}

    void popFront()
    {
        if (!_r.empty)
        {
            _r.popFront;
        }
        else
        {
            _end.popFront;
        }
    }
}

struct Rotate(R) if (isBidirectionalRange!R)
{
    int n;
    R _r;
    ElementType!R[] _end;
    ElementType!R[] _beginning;

    this(R r, int n)
    {
        this.n = n;
        _r = r;
        static if (!isInfinite!R)
        {
            static if (hasLength!R)
                auto l = _r.length;
            else
                auto l = walkLength(_r, abs(n));
            if (l==0) n = 0;
            if (l<abs(n)) {n %= l;}
        }

        if (n >= 0)
        {
            _end.length = n;
            foreach(i; 0..n) // not lazy, because take(string s, n) has no back defined
            {                // (a string is bidir, but doesn't know its length, so take cannot be bidir)
                _end[i] = _r.front;
                _r.popFront;
            }
        }
        else
        {
            _beginning.length = -n;
            foreach(i; 0..(-n)) // not lazy, too bad. Due to a limitation in take... (Retro!(Take!(Retro!R)) is not always possible)
            {
                _beginning[-n-i-1] = _r.back;
                _r.popBack;
            }
        }
    }

    static if (isInfinite!R) // bidir and infinite is possible, though quite uncommon.
        enum bool empty = false;
    else
        bool empty() { return _r.empty && ((n>=0) ? _end.empty : _beginning.empty); }

    ElementType!R front()
    {
        if (n >=0)
        {
            return (_r.empty) ? _end.front : _r.front;
        }
        else
        {
            return (_beginning.empty) ? _r.front : _beginning.front;
        }
    }

    void popFront()
    {
        if (n >= 0)
        {
            if (!_r.empty)
            {
                _r.popFront;
            }
            else
            {
                _end.popFront;
            }
        }
        else
        {
            if (!_beginning.empty)
            {
                _beginning.popFront;
            }
            else
            {
                _r.popFront;
            }
        }
    }

    ElementType!R back()
    {
        if (n >=0)
        {
            return (_end.empty) ? _r.back : _end.back;
        }
        else
        {
            return (_r.empty) ? _beginning.back : _r.back;
        }
    }

    void popBack()
    {
        if (n >= 0)
        {
            if (!_end.empty)
            {
                _end.popBack;
            }
            else
            {
                _r.popBack;
            }
        }
        else
        {
            if (!_r.empty)
            {
                _r.popBack;
            }
            else
            {
                _beginning.popBack;
            }
        }
    }
}

/**
Rotates a range while the predicate holds. It works for infinite ranges also.

If the predicate is true for all elements, it will not cycle forever, but deliver a range equal
to the orginal range.

Note that the predicate can be unary, but also binary or whatever. rotateWhile!"a<b"(r) is possible.
See takeWhile.
Example:
----
auto arr = [0,1,2,3,4,3,2,1,0];
wr(rotateWhile!"true"(arr));    // 0,1,2,3,4,3,2,1,0
wr(rotateWhile!"a<2"(arr));     // 2,3,4,3,2,1,0,0,1
wr(rotateWhile!"a<b"(arr));     // 4,3,2,1,0,0,1,2,3
wr(rotateWhile!"a+b+c<10"(arr));// 3,4,3,2,1,0,0,1,2
----
*/
Chain!(R, TakeWhile!(pred,R)) rotateWhile(alias pred, R)(R range) if (isForwardRange!R)
{
    return chain(dropWhile!pred(range), takeWhile!pred(range));
}


/+ Old version. To be redone
unittest
{
    auto r1 = [0,1,2,3,4][];            // standard range: forward range, has a length, has slicing
    auto r2 = permutations([0,1,2][]);  // forward range, has a length, no slicing
    // r2 is [[0,1,2],[1,0,2], [0,2,1], [1,2,0], [2,1,0], [2,0,1]][];
    auto r3 = "abcdef";                 // Just to test with immutable(char)[]
    auto r4 = cycle([0,1,2][]);         // forward range, but infinite (and so, no length).

    assert(equal(rotate!0(r1), r1));   // Rotate by 0: leave range unchanged
    assert(equal(rotateL(0,r1), r1));   // Rotate by 0: leave range unchanged
    assert(equal(rotate!1(r1), r1[1..$] ~ r1[0]));
    assert(equal(rotate!3(r1), r1[3..$] ~ r1[0..3]));
    assert(equal(rotate!(-1)(r1), [4,0,1,2,3][]));
    assert(equal(rotate!(-3)(r1), [2,3,4,0,1][]));
    assert(equal(rotateL(r1.length, r1), r1)); // complete turn
    assert(equal(rotateR(r1.length, r1), r1)); // complete turn
    assert(equal(rotateL(r1.length +1, r1), rotateL(1, r1)));
    assert(equal(rotateR(r1.length +1, r1), rotateR(1, r1)));

    assert(equal(rotate!0(r2), r2));   // For a range with no slicing
    assert(equal(rotateL(6, r2), r2)); // complete turn
    assert(equal(rotate!0(r2), [[0,1,2], [1,2,0], [2,0,1], [1,0,2], [0,2,1], [2,1,0]][]));
    assert(equal(rotate!1(r2), [[1,2,0], [2,0,1], [1,0,2], [0,2,1], [2,1,0], [0,1,2]][]));
    assert(equal(rotate!2(r2), [[2,0,1], [1,0,2], [0,2,1], [2,1,0], [0,1,2], [1,2,0]][]));

    assert(equal(rotate!3(r3), "defabc")); // OK for strings
    assert(equal(rotate!(-3)(r3), "defabc")); // OK for strings
    assert(equal(take(rotate!1(r4), 5), [1,2,0,1,2][])); // infinite 0 1 2 0 1 2 0 1 2 ... -> 1 2 0 1 2 0 1 2 ...
    assert(equal(take(rotate!3(r4), 5), take(r4, 5)));   // cycle of period 3 -> a rotation of 3 steps leaves the range unchanged

    int[] r5;
    assert(r5.empty);
    assert(rotate!2(r5).empty);
}
+/

/**
Infinite range producing the successive rotations of the input range.
*/
TMapType!(rotate!R, Repeat!R, Numbers) rotations(R)(R range)
{
    return tmap!(rotate!R)(repeat(range), numbers());
}

E replacer(E)(E element, E[E] mapping)
{
    return (element in mapping) ? mapping[element] : element;
}

/**
To Be Documented.

Replaces the elementes of range present in the AA mapping by the values in mapping.
Example:
----
auto r = replace([0,1,2,3,4], [1:100, 2:200]);
----
*/
TMapType!(replacer!(ElementType!R), R, Repeat!(V[K]))
replace(R,V,K)(R range, V[K] mapping) if (isForwardRange!R && is(ElementType!R == K) && is(ElementType!R == V))
{
    return tmap!(replacer!(ElementType!R))(range, repeat(mapping));
}

/**
Takes a value as template parameter and a range as argument, returns a (lazy) range
containing the indices of 'value' in the range.
----
auto r1 = [0,1,2,3,4,2,2];
auto i1 = indices!2(r1); // 2,5,6. finding an int in a int[]
assert(equal(indicesOf!'a'("banana"), [1,3,5][])); // finding a char in a string
string sentence = "the quick brown fox jumped over the lazy dog.";
auto i2 = indices!' '(sentence); // finding spaces in the string
assert(equal(i2, [3, 9, 15, 19, 26, 31, 35, 40][]));
auto words = split(sentence);
auto i3 = indices!"the"(words); // finding a string in a string[]
assert(equal(i3, [0,6][]));
auto r2 = map!"a*a"(cycle([1,2,3]));
auto i4 = indices!4(take(10, r2)); // inside another kind of range
assert(equal(i4, [1,4,7][]));
----
*/
IndicesType!(value, R) indices(alias value, R)(R range) if (isForwardRange!R) {
    auto m = map!(equals!(value, ElementType!R))(range);
    return pComp!("a","b")(numbers(), m);
}

template IndicesType(alias value, R) {
    alias PCompType!("a","b",Numbers, Map!(unaryFun!(equals!(value, ElementType!R)), R)) IndicesType;
}

unittest
{
    auto r1 = [0,1,2,3,4,2,2];
    auto i1 = indices!2(r1);
    assert(equal(i1, [2,5,6][])); // finding an int in a int[]
    assert(equal(indices!'a'("banana"), [1,3,5][])); // finding a char in a string
    string sentence = "the quick brown fox jumped over the lazy dog.";
    auto i2 = indices!' '(sentence); // finding spaces in the string
    assert(equal(i2, [3, 9, 15, 19, 26, 31, 35, 40][]));
    auto words = split(sentence);
    auto i3 = indices!"the"(words); // finding a string in a string[]
    assert(equal(i3, [0,6][]));
    auto r2 = map!"a*a"(cycle([1,2,3][]));
    auto i4 = indices!4(take(r2, 10)); // inside another kind of range
    assert(equal(i4, [1,4,7][]));

    int[] e;
    assert(indices!1(e).empty);
}

/**
Takes a predicate as template parameter and a range as argument, returns a (lazy) range
containing the indices of the values verifying pred.
Example:
----
auto r1 = [0,1,2,3,4,5,6,1];
auto p1 = positions!"a%2==0"(r1);
assert(equal(p1, [0,2,4,6][]));
auto p2 = positions!"a<4"(r1);
assert(equal(p2, [0,1,2,3,7][]));
auto p3 = positions!"a>10"(r1); // predicate never verified -> empty
assert(p3.empty);

auto s = "banana";
auto p4 = positions!(isOneOf!"bn")(s);
assert(equal(p4, [0,2,4][]));

int[] e;
assert(positions!"a==0"(e).empty); // on an empty range -> empty
----
*/
PCompType!("a","b", Numbers, Map!(unaryFun!pred, R)) positions(alias pred, R)(R range) if (isForwardRange!R) {
    return pComp!("a", "b")(numbers(), map!pred(range));
}

unittest
{
    auto r1 = [0,1,2,3,4,5,6,1];
    auto p1 = positions!"a%2==0"(r1);
    assert(equal(p1, [0,2,4,6][]));
    auto p2 = positions!"a<4"(r1);
    assert(equal(p2, [0,1,2,3,7][]));
    auto p3 = positions!"a>10"(r1); // predicate never verified -> empty
    assert(p3.empty);

    auto s = "banana";
    auto p4 = positions!(isOneOf!"bn")(s);
    assert(equal(p4, [0,2,4][]));

    int[] e;
    assert(positions!"a==0"(e).empty); // on an empty range -> empty
}


Unqual!(ElementType!R) atIndex(R,I)(R r, I i) { return r[i];} // necessary to unqual R's elements

/**
Given a (possibly infinite) range of indices and a random-access range, it will lazily produce
the corresponding elements.
Example:
----
string s = "abcdefg";

auto i1 = map!"a%4"(numbers(10)); // 0,1,2,3,0,1,2,3,0,1
auto fi1 = fromIndex(i1, s);
assert(equal(fi1, "abcdabcdab")); // equivalent to take(10, cycle(take(4, s)))

auto i2 = map!"a/4"(numbers(10)); // 0,0,0,0,1,1,1,1,2,2
auto fi2 = fromIndex(i2, s);
assert(equal(fi2, "aaaabbbbcc")); // equivalent to take(10, stutter(4, s))
----
*/
TMapType!(atIndex!(R, ElementType!I), Combinations!(Once!R, I)) fromIndex(I, R)(I indices, R range) if (isRandomAccessRange!R && isForwardRange!I)
{
    // tmap!"a[b]" should work for ranges with mutable elements. But strings need to be unqualified with atIndex.
    return tmap!(atIndex!(R, ElementType!I))(combinations(once(range), indices));
}

unittest
{
    auto s = cast(immutable(dchar)[])"abcdefg";

    auto i1 = map!"a%4"(numbers(10)); // 0,1,2,3,0,1,2,3,0,1
    auto fi1 = fromIndex(i1, s);
    assert(equal(fi1, "abcdabcdab"));

    auto i2 = map!"a/4"(numbers(10)); // 0,0,0,0,1,1,1,1,2,2
    auto fi2 = fromIndex(i2, s);
    assert(equal(fi2, "aaaabbbbcc"));

    assert(fromIndex((size_t[]).init, s).empty);
}

/**
Given a range, it will lazily produce the element's indices. If an element has the same value
than a previous element, this previous element's index will be given.
Examples:
----
string s = "abcdefabcdefghab";
auto ti = toIndex(s);
assert(equal(ti, [0,1,2,3,4,5,0,1,2,3,4,5,12,13,0,1][]));
assert(equal(fromIndex(ti, s), s)); // toIndex is (sort of) the opposite of fromIndex

auto r = replicate(5,5); // 5,5,5,5,5
assert(equal(toIndex(r), [0,0,0,0,0][])); // Always the first element's index (0)
----
*/
struct ToIndex(R) if(isForwardRange!R)
{
    size_t[ElementType!R] indices;
    R _range;
    size_t index;

    this(R r) {
        _range = r;
        if (!_range.empty) {
            if (!(_range.front in indices)) {
                indices[_range.front] = index;
            }
        }
    }

    bool empty() { return _range.empty;};
    size_t front() { return indices[_range.front];}
    void popFront() {
        _range.popFront;
        index++;
        if (!_range.empty) {
            if (!(_range.front in indices)) {
                indices[_range.front] = index;
            }
        }
    }
}

/// ditto
ToIndex!R toIndex(R)(R range) if (isForwardRange!R)
{
    return ToIndex!R(range);
}

unittest
{
    auto s = cast(immutable(dchar)[])"abcdefabcdefghab";
    auto ti = toIndex(s);
    assert(equal(ti, [0,1,2,3,4,5,0,1,2,3,4,5,12,13,0,1][]));
    assert(equal(fromIndex(ti, s), s));

    auto r = replicate(5,5); // 5,5,5,5,5
    assert(equal(toIndex(r), [0,0,0,0,0][]));

    int[] e;
    assert(toIndex(e).empty);
}

/**
Separate a range in (in tuple of) two ranges according to predicate pred. The first field
will contain the values verifying pred, the second those that do not verify it. There
is an equivalent Haskell function.
See_Also:
span.
Example:
----
auto r = [0,1,2,3,4,5];
auto s = separate!"a<1 || a>3"(r);
assert(equal(first(s), [0,4,5][]));
assert(equal(second(s), [1,2,3][]));
----
*/
Tuple!(Filter!(unaryFun!pred, R), Filter!(Not!(unaryFun!pred), R)) separate(alias pred, R)(R range) if (isForwardRange!R)
{
	alias unaryFun!pred upred;
	return tuple(filter!(upred)(range), filter!(Not!upred)(range));
}

unittest
{
    auto r = [0,1,2,3,4,5];
    auto s = separate!"a<1 || a>3"(r);
    assert(equal(first(s),  [0,4,5][]));
    assert(equal(second(s), [1,2,3][]));
}

/**
Equivalent to Haskell's span: returns the tuple(takeWhile!pred(range), dropWhile!pred(range)).
See_Also:
separate.
Example:
----
auto r = map!"a*a"([0,1,2,3,4,5,4,3,2][]);
auto s = span!"a<10"(m);
assert(equal(first(s), [0,1,4,9][]));
assert(equal(second(s), [16,25,16,9,4][]));
----
*/
Tuple!(TakeWhile!(pred,R), R) span(alias pred, R)(R range)
{
    return tuple(takeWhile!pred(range), dropWhile!pred(range));
}

unittest
{
    auto r = map!"a*a"([0,1,2,3,4,5,4,3,2][]);
    auto s = span!"a<10"(r);
    assert(equal(first(s), [0,1,4,9][]));
    assert(equal(second(s), [16,25,16,9,4][]));
}

/**
Eliminates all duplicated occurences of 'element' from 'range'. Taken from Ruby by way of Clojure.
Useful to get rid of surnumerary spaces in strings.
Examples:
----
auto r1 = [0,1,2,2,3,4,5,2,2,2,3,5,6,8,3,2];
string r2 = "abcd  ef g h    ";
assert(equal(squeeze(2, r1), [0,1,2,3,4,5,2,3,5,6,8,3,2][]));
assert(equal(squeeze(' ', r2), "abcd ef g h "));
----
Note that it returns an array of ElementType!R, not a R.
*/
ElementType!R[] squeeze(E, R)(E element, R range) if (isForwardRange!R)
{
    ElementType!R[] squee(ElementType!R[] arr, ElementType!R elem){
        return (arr.back == element && elem == element) ? arr : arr ~ elem;
    }
    auto f = [range.front][];
    range.popFront;
    return reduce!squee(f, range);
}

unittest
{
    auto r1 = [0,1,2,2,3,4,5,2,2,2,3,5,6,8,3,2];
    string r2 = "abcd  ef g h    ";
    assert(equal(squeeze(2, r1), [0,1,2,3,4,5,2,3,5,6,8,3,2][]));
    assert(equal(squeeze(' ', r2), "abcd ef g h "));
}


/**
Gives the cartesian product of a variadic number of ranges: the sequence of all tuples
created by taking one element in each range.
The order of the input ranges is important: the rightmost one
will be incremented faster than the one before it and so on:
Combinations([0,1][], [2,3][], [4,5][]) will produce
Tuple!(int, int, int) (0,2,4), (0,2,5), (0,3,4), (0,3,5), (1,2,4), ...

If all the ranges have a length, Combinations also has a 'length' member
whose value is the product of all these lengths.

Example:
----
auto r1 = [0,1,2];
string r2 = "abcd";
auto r3 = map!"a + 3.0"(r1);
auto cb = combinations(r1,r2,r3);
assert(!is(cb.length)); // r3 has no length, so cb neither.
assert(equal(take(7, cb),
            [tuple(0, 'a', 3.0), tuple(0, 'a', 4.0), tuple(0, 'a', 5.0),
             tuple(0, 'b', 3.0), tuple(0, 'b', 4.0), tuple(0, 'b', 5.0), tuple(0, 'c', 3.0)][]
            ));
auto cb2 = combinations(r1,r2);
assert(cb2.length == r1.length * r2.length); // 12
cb2.popFront;
assert(cb2.length == r1.length * r2.length - 1); // 11
----
*/
struct Combinations(R...) if (allSatisfy!(isForwardRange, R)) {
    R _ranges, _currentRanges;
    alias Tuple!(staticMap!(Unqual, ElementTypes!R)) FrontTuple; // ElementTypes, not ElementType
    size_t _length, pops;

    this(R ranges) {
        _ranges = ranges;
        _currentRanges = ranges;
        static if (allSatisfy!(hasLength, R)) { // calculate _length once, at creation
            _length = 1;
            foreach(range; ranges) {
                _length *= range.length;
            }
        }
    }

    bool empty() { // We must check all of them because some may be empty at creation!
        return someEmpty(_currentRanges);
    }

    void popFront() {
        foreach_reverse(i, elem; _currentRanges) {
            _currentRanges[i].popFront;
            if (!_currentRanges[i].empty) {
                break; // exit the foreach
            }
            else {
                if (i != 0) _currentRanges[i] = _ranges[i];
            }
        }
        pops++; // For length
    }

    FrontTuple front() {
        FrontTuple f;
        foreach(i, r; _currentRanges) {
            f.field[i] = r.front;
        }
        return f;
    }

    static if (allSatisfy!(hasLength, R)) {
        size_t length() {
            return _length-pops;
        }
    }
}

/// ditto
Combinations!(R) combinations(R...)(R ranges) if (R.length && allSatisfy!(isForwardRange, R)) {
    return Combinations!(R)(ranges);
}

unittest {
    auto r1 = [0,1,2]; // Random-access range
    auto r2 = ["a","b","c","d"];
    auto r3 = map!"a + 3.0"(r1); // Forward range
    auto cb = combinations(r1,r2,r3);
    assert(cb.front == tuple(0, "a", 3.0));
    cb.popFront();
    assert(cb.front == tuple(0, "a", 4.0));
    assert(!is(cb.length)); // r3 has no length, so cb neither.
    assert(equal(take(cb, 6),
                [tuple(0, "a", 4.0), tuple(0, "a", 5.0), tuple(0, "b", 3.0), tuple(0, "b", 4.0), tuple(0, "b", 5.0), tuple(0, "c", 3.0)][]
                ));
    auto cb2 = combinations(r1,r2);
    assert(cb2.length == r1.length * r2.length); // 12
    cb2.popFront;
    assert(cb2.length == r1.length * r2.length - 1); // 11

    int[] e;
    assert(combinations(r1, e).empty);
}

/+ deprecated
/**
Takes a random-access range with a length and will lazily produce
all permutations of values from this range. Its length is factorial(input.length).
TODO:
the code is very C-like. Maybe someone can do a better job on this algo.
Example:
---
auto r1 = [0,1,2];
auto perm = permutations(r1);
assert(perm.length == 3*2);
assert(equal(perm, [[0,1,2], [1,0,2], [0,2,1], [1,2,0], [2,1,0], [2,0,1]][]));
string s = "abcd";
auto perm2 = permutations(s); // abcd, bacd, acbd, ...
assert(perm2.length == 4*3*2);
----
*/
struct Permutations(R) if (isRandomAccessRange!R && hasLength2!R) {
    size_t k, max;
    Unqual!(ElementType!R)[] _range;
    int[] _currentPermutation;

    this(R range) {
        k = 0;
        _range.length = range.length;
        copy(range, _range);
        _currentPermutation = array(numbers(_range.length));
        max = fact(_range.length);
    }

    ElementType!R[] front() {
        ElementType!R[] f;
        foreach(i, elem; _currentPermutation) f ~= _range[elem];
        return f;
    }

    void popFront() {
        k++;
        _currentPermutation = array(numbers(_range.length));

        int fact = 1;
        for (int i = 1 ;  i < _currentPermutation.length ; i++){
            fact = fact*i;
            int pos = i - ((k/fact) % (i+1));
            if (pos != i) swap(_currentPermutation[pos], _currentPermutation[i]);
        }
    }

    bool empty() {
        return (k == max);
    }

    size_t length() {
        return max;
    }
//
//    ElementType!R[] opIndex(size_t index) {
//        assert(index < max, "permutations.opIndex: index too large.");
//        auto perm = array(range);
//        int fact = 1;
//        for (int i = 1 ;  i < perm.length ; i++){
//            fact = fact*i;
//            int pos = i - ((index/fact) % (i+1));
//            if (pos != i) swap(perm[pos], perm[i]);
//        }
//        return perm;
//    }

    size_t fact(size_t n) {
        size_t f = 1;
        foreach(i; 2 .. n+1) {
            f = f *i;
        }
        return f;
    }
}

/// ditto
Permutations!R permutations(R)(R range) if(isForwardRange!R && hasLength2!R) {
    return Permutations!R(range);
}

unittest {
    auto r1 = [0,1,2];
    auto perm = permutations(r1);
    assert(perm.length == 3*2);
    assert(equal(perm, [[0,1,2], [1,0,2], [0,2,1], [1,2,0], [2,1,0], [2,0,1]][]));
    string s = "abcd";
    auto perm2 = permutations(s); // abcd, bacd, acbd, ...
    assert(perm2.length == 4*3*2);
}
+/

/**
Lazily generates the permutations of the first n elements in a range. By default
n is equal to the range's length, so it permutes the entire range.
It's completely based on algorithm C from Knuth's "the Art of Computer Programming", vol. IV
(found on the web <a href = "http://www-cs-faculty.stanford.edu/~knuth/fasc2b.ps.gz">here</a>),
fascicule 2b, section 7.2.1.2 "Generating all Permutations".
Internally it does not use any factorial, so it's quite safe to use it on long ranges.
Its length will be n!. So permutations(r,1) returns only array(r).
On the empty range, it returns an empty range and then stops.

BUG:
Do not work on infinite ranges. Not a bug, more a limitation of the algorithm as currently coded.
Note:
The front type is an array of ElementType!R, not an R, because most ranges
do not support the slicing operations needed there. Also, it's an array
and not a tuple as most ranges'd return here, because I gather the classical
use is indeed to treat each element (a permutation) as a range latter on. Tuples
wouldn't do it.
Note:
Another possibility would be to return a lazy extract, as do subranges and variations.
Note:
A possible update would be to get rid of internal arrays and to make it usable on infinite ranges.
Example:
----
auto r = [0,1,2]; // array
auto m = map!"a*a"(r); // not an array...

auto p1 = permutations(r); // on an array
assert(equal(p1, [[0,1,2], [1,2,0], [2,0,1], [1,0,2], [0,2,1], [2,1,0] ][]));

auto p2 = permutations(m); // on a forward range
assert(equal(p2, [[0,1,4], [1,4,0], [4,0,1], [1,0,4], [0,4,1], [4,1,0] ][]));

auto r2 = numbers(100); // 0..100
auto p3 = permutations(r2); // quite safe, but you'll probably never exhaust it...
p3.popFront;
assert(p3.front == array(numbers(1,100)) ~ [0]);
p3.popFront;
assert(p3.front == array(numbers(2,100)) ~ [0,1]); // begins by rotating the range

auto p4 = permutations(r2, 3); // permutes only the first 3 elements.
p4.popFront;
assert(p4.front == [1,2,0] ~ array(numbers(3,100)));
p4.popFront;
assert(p4.front == [2,0,1] ~ array(numbers(3,100)));
p4.popFront;
p4.popFront;
p4.popFront;
assert(p4.empty); // only 6 elements, as it acts only on the first 3 elements of r2.
----
*/
struct Permutations(R) {
    ElementType!R[] _input, _perm;
    size_t k, n;

    this(R r) {
        _input = array(r);
        _perm = array(r);
        n = _perm.length;
        k = n;
    }

    this(R r, size_t elems) {
        _input = array(r);
        _perm = array(r);
        n = min(elems, _perm.length);
        k = n;
    }

    ElementType!R[] front() { return _perm;}
    bool empty() { return (n == 1 && k == 0 )|| (n>1 && k <=1);}
    void popFront() {
        k = n;
        if (k==0) { n=1;} // permutation of an empty range or of zero elements
        else {
            C3: _perm = _perm[1..k] ~ _perm[0] ~ _perm[k..$];
            if (_perm[k-1] == _input[k-1]) {
                k--;
                if (k > 1) goto C3;
            }
        }
    }
}

/// ditto
Permutations!R permutations(R)(R r) if (isDynamicArray!R) {
    return Permutations!R(r);
}

/// ditto
Permutations!R permutations(R)(R r, size_t n) if (isDynamicArray!R) {
    return Permutations!R(r, n);
}

/// ditto
Permutations!(ElementType!R[]) permutations(R)(R r) if (!isDynamicArray!R && isForwardRange!R && !isInfinite!R) {
    return Permutations!(ElementType!R[])(array(r));
}

/// ditto
Permutations!(ElementType!R[]) permutations(R)(R r, size_t n) if (!isDynamicArray!R && isForwardRange!R && !isInfinite!R) {
    return Permutations!(ElementType!R[])(array(r), n);
}

unittest
{
    auto r = [0,1,2]; // array
    auto m = map!"a*a"(r); // not an array...

    auto p1 = permutations(r); // on an array
    assert(equal(p1, [[0,1,2], [1,2,0], [2,0,1], [1,0,2], [0,2,1], [2,1,0] ][]));

    auto p2 = permutations(m); // on a forward range
    assert(equal(p2, [[0,1,4], [1,4,0], [4,0,1], [1,0,4], [0,4,1], [4,1,0] ][]));

    auto r2 = numbers(100); // 0..100
    auto p3 = permutations(r2); // quite safe, but you'll probably never exhaust it...
    p3.popFront;
    assert(p3.front == array(numbers(1,100)) ~ [0]);
    p3.popFront;
    assert(p3.front == array(numbers(2,100)) ~ [0,1]); // begins by rotating the range

    auto p4 = permutations(r2, 3); // permutes only the first 3 elements.
    p4.popFront;
    assert(p4.front == [1,2,0] ~ array(numbers(3,100)));
    p4.popFront;
    assert(p4.front == [2,0,1] ~ array(numbers(3,100)));
    p4.popFront;
    p4.popFront;
    p4.popFront;
    p4.popFront;
    assert(p4.empty); // only 6 elements, as it acts only on the first 3 elements of r2.

    int[] e; // permutation of an empty range.
    assert(equal(permutations(e),[e][]));

    auto one = [1]; // permutation of a 1-element range.
    assert(equal(permutations(one), [[1]][])); // only one element, the input range.
}

/**
anonymous enum determining the behavior of choose.
See_Also:
choose.
*/
enum {withRepetition, withoutRepetition};


// Internal helper struct. It does all the work for choose,
// generating the index array.
struct ChooseIndex(uint repetition = withoutRepetition) {
    size_t n, among;
    size_t[] indice;
    bool atMax;

    this(size_t n, size_t among) {
        assert(n <= among, "ChooseIndex assertion: num elements chosen (" ~ to!string(n) ~ ") is higher than the array length (" ~ to!string(among) ~ ").");
        this.n = n;
        if (n==0) {
            atMax = true;
        }
        else {
            this.among = among;
            initialize(indice);
        }
    }

    size_t maxIndex(size_t i) {
        static if (repetition == withoutRepetition)
            return (i == n-1) ? among-1 : indice[i+1]-1;
        else
            return among-1;
    }

    size_t minIndex(size_t i) {
        static if (repetition == withoutRepetition)
            return (i == 0) ? 0 : indice[i-1]+1;
        else
            return 0;
    }

    void initialize(ref size_t[] indice) {
        indice.length = n;
        foreach(size_t i, ref elem; indice) elem = minIndex(i);
    }

    bool empty() { return atMax;}
    size_t[] front() { return indice;}

    void popFront() {
        size_t j = n-1;
        while (!atMax){
            if (indice[j] < maxIndex(j)) {
                indice[j] = indice[j] + 1;
                return;
            }
            else {
                if (j == 0) { atMax = true;}
                else {
                    static if (repetition == withoutRepetition) {
                        indice[j] = min(minIndex(j)+1, maxIndex(j));
                        foreach(jj; j+1 .. n) indice[jj] = min(minIndex(jj), maxIndex(jj));
                    }
                    else {
                        foreach(jj; j .. n) indice[jj] = min(minIndex(jj), maxIndex(jj));
                    }
                    j--;
                }
            }
        }
    }
}

ChooseIndex!(repetition) chooseIndex(uint repetition = withoutRepetition)(size_t n, size_t among)
{
    return ChooseIndex!repetition(n,among);
}

/**
Chooses n elements from a range. It lazily generates all combinations of n elements (as an array) taken from range.
There are two different behaviors determined by an anonymous enum : repetition {withRepetition, withoutRepetition}

Repetition tells the algorithm if you want to reuse the elements from the range or not.
Say you want to take 3 elements from [0,1,2,3]. You take '0'. If you selected withoutRepetition (the default state)
the second element will be taken from [1,2,3], and the third from [2,3] (for example). If you selected
withRepetition, all three elements will be taken from [0,1,2,3]. So repeated values like (2,3,3) are a possibility.
For a range of length l, choosing n elements among l will give C(n,l) = (choose n among l) = l!/(n! * (l-n)!) = l*(l-1)*(l-2)*...*(l-n+1) / n!

Without repetition, the generated arrays are always ordered as the range's elements: choosing 3 element among [0,1,2,3,4,5]
will generate [0,1,2], [0,1,3], ... but never [3,1,0]. If you want all the orderings, do flatMap!permutations on choose.

You can do the same with repetition, but in this case, you need to filter out the repeated patterns with asSet.

Examples:
----
// A poker hand is five cards without repetition among 52 cards.
// That makes 2,598,960 possible hands.
auto ranks = "A23456789TJQK";
auto suits = ["Hearts", "Spades", "Diamonds", "Clubs"];
auto cards = combinations(ranks, suits); // ('A', "Hearts"), ('A', "Spades"), ...
assert(walkLength(cards) == 52); // OK, 52 cards.

auto c = choose(5, cards); // default is withoutRepetition
assert(walkLength(c) == 52*51*50*49*48/(5*4*3*2)); // 2,598,960

// A DNA chain is made of one of four bases (here denoted as A, C, G or T)
// A codon is a 3-bases encoding for an amino-acid. How many codons are there?
auto DNA = "ACGT";
auto codons = choose!withRepetition(3, DNA);   // 4*4*4 == 64 elements
assert(walkLength(codons) == 64);
----
*/
ChooseType!(repetition, R) choose(uint repetition = withoutRepetition, R)(size_t n, R range) if (isForwardRange!R && !isInfinite!R)
{
    auto a = array(range); // to get a length
    return tmap!(fromIndex!(size_t[], ElementType!R[]))(chooseIndex!repetition(n, a.length), repeat(a));
}

template ChooseType(uint repetition, R) if (isForwardRange!R && !isInfinite!R)
{
    alias TMapType!(fromIndex!(size_t[], ElementType!R[]), ChooseIndex!repetition, Repeat!(ElementType!R[])) ChooseType;
}

unittest
{
    // A poker hand is five cards without repetition among 52 cards.
    // That makes 2,598,960 possible hands.
    auto ranks = cast(char[])"A23456789TJQK";
    auto suits = ["Hearts", "Spades", "Diamonds", "Clubs"];
    auto cards = combinations(ranks, suits); // ('A', "Heart'), ('A', "Spades"), ...
    assert(walkLength(cards) == 52); // OK, 52 cards.

    auto c = choose(5, cards); // default is withoutRepetition
    assert(walkLength(c) == 52*51*50*49*48/(5*4*3*2)); // 2,598,960

    // A DNA chain is made of one of four bases (here denoted as A, C, G or T)
    // A codon is a 3-bases encoding for an amino-acid. How many codon are there?
    auto DNA = cast(char[])"ACGT";
    auto codons = choose!withRepetition(3, DNA);   // 4*4*4 == 64 elements
    assert(walkLength(codons) == 64);
}

/**
A generic consumer of ranges. It will gobble as many elements as needed from the input range
to produce its next value, the number of input elements consumed can vary from
one call to popFront to the next. Taken from the Haskell code in
<a href = "http://www.comlab.ox.ac.uk/jeremy.gibbons/publications/spigot.pdf">this article</a>.

It takes as input a (possibly infinite) range with element type In and an initial internal state (of type St).
Let's call Out the type consumer outputs. The idea is that you incrementaly build a valid internal state while consuming the range.
When the state is complete, nextElement can produce the output element and renewState 'discharges' the state,
making it OK for rebuilding by buildState.

Params:
    nextElement = a callable taking a St (current state) and returning an Out. Produces the possible next element (of type Out).
    isSafe = takes the current state and the element produced by nextElement. Tells wether or not it's OK to output the element.
    renewState = if isSafe is true, then renewState takes (state, element) and returns the state resotred to a 'pristine' state (ready to grow again).
    buildState = if isSafe is false, buildState takes (state, range.front) and returns the new state. range.popFront is called.
    flush = is an optional callable that is used when the input range is exhausted (so, only for finite ranges). flush is called on the current state to produce the last few elements as an array of Out.

Example:
----
// to be documented.
----
*/
struct Consumer(alias nextElement, alias isSafe, alias renewState, alias buildState, alias flusher, R, St, Out)
{
    R _range;
    Out currentElem;
    St state;
    Out[] flush;
    bool flushed;

    this(R range, St initialState) { _range = range; state = initialState; popFront;}
    static if (isInfinite!R)
        enum bool empty = false;
    else
        bool empty()
        {
            return _range.empty && flushed && flush.empty;
        }

    Out front() { return currentElem;}
    void popFront()
    {
        static if (isInfinite!R)
        {
            auto e = unaryFun!nextElement(state);
            while (!binaryFun!isSafe(state, e))
            {
                state = binaryFun!buildState(state, _range.front);
                _range.popFront;
                e = naryFun!nextElement(state);
            }
            currentElem = e;
            state = binaryFun!renewState(state, e);
        }
        else
        {

            if (!_range.empty)
            {
                auto e = unaryFun!nextElement(state);
                while (!binaryFun!isSafe(state, e))
                {
                    state = binaryFun!buildState(state, _range.front);
                    _range.popFront;
                    e = naryFun!nextElement(state);
                }
                currentElem = e;
                state = binaryFun!renewState(state, e);
            }
            else // flushing the state. Changing iteration mode to consume flush.
            {
                if (!flushed)
                {
                    flush = naryFun!flusher(state);
                    flushed = true;
                }
                if (!flush.empty)
                {
                    currentElem = flush.front;
                    flush.popFront;
                }
            }
        }
    }
}

T id(T)(T t) { return t;}

/// ditto
Consumer!(nextElement, isSafe, renewState, buildState, flusher, R, St, typeof(unaryFun!nextElement(St.init)))
consumer(alias nextElement, alias isSafe, alias renewState, alias buildState, alias flusher = id, R, St)(R range, St initialState) if (isInputRange!R && isInfinite!R)
{
    alias typeof(unaryFun!nextElement(initialState)) Out; // what the range will produce
    return Consumer!(nextElement, isSafe, renewState, buildState, flusher, R, St, Out)(range, initialState);
}

/// ditto
Consumer!(nextElement, isSafe, renewState, buildState, flusher, R, St, typeof(unaryFun!nextElement(St.init)))
consumer(alias nextElement, alias isSafe, alias renewState, alias buildState, alias flusher, R, St)(R range, St initialState) if (isInputRange!R && !isInfinite!R)
{
    alias typeof(unaryFun!nextElement(initialState)) Out; // what the range will produce
    return Consumer!(nextElement, isSafe, renewState, buildState, flusher, R, St, Out)(range, initialState);
}

/+ does not work for finite range. Try it now with a flusher.
/**
Takes a range in base m, representing a number < 1. Converts it to base n.
*/
auto convert(R)(R range, int m, int n)
{
    alias Tuple!(real,real, int, int) S;
    int nextElement(S s) { return to!int(floor(first(s)*second(s)*s.field[3]));}
    bool isSafe(S s, int y) { return y == floor((first(s)+1)*second(s)*s.field[3]);}
    S renewState(S s, int y) { return tuple(first(s)-y/(second(s)*s.field[3]), second(s)*s.field[3],s.field[2], s.field[3]);}
    S buildState(S s, int x) { return tuple(x+first(s)*third(s), second(s)/third(s),s.field[2], s.field[3]);}
    return consumer!(nextElement, isSafe, renewState, buildState)(range, Tuple!(real,real, int,int)(0.0,1.0,m,n));
}
+/

/// generic inner product of a range.
typeof(binaryFun!plus(binaryFun!times(ElementType!(R1).init, ElementType!(R2).init), binaryFun!times(ElementType!(R1).init, ElementType!(R1).init)))
innerProduct(alias plus = "a+b", alias times = "a*b", R1, R2)(R1 r1, R2 r2) if (isInputRange!R1 && isInputRange!R2)
{
    return reduce ! plus (tmap ! times (r1,r2));
}

/// the dual of filter
Filter!(Not!pred, R) remove(alias pred, R)(R r) if (isForwardRange!R)
{
    return filter!(Not!pred)(r);
}

/// reduce a range while pred holds on the intermediary values.
template reduceWhile(alias fun, alias pred)
{
    alias ReduceWhile!(fun,pred).reduceWhile reduceWhile;
}

template ReduceWhile(alias fun, alias pred)
{
    Unqual!E reduceWhile(E, R)(E seed, R r)
    {
        Unqual!E result = seed;
        Unqual!E before = seed;
        enforce(unaryFun!pred(before), "the seed for reduceWhile must verify the predicate.");
        while (naryFun!pred(result) && !r.empty)
        {
            before = result;
            result = binaryFun!(fun)(result, r.front);
            r.popFront;
        }
        return before;
    }

    ReturnType!(ElementType!(Range))
    reduceWhile(Range)(Range r) if (isInputRange!Range)
    {
        enforce(!r.empty);
        auto e = r.front;
        r.popFront;
        return reduceWhile!(fun,pred)(e, r);
    }
}

/**
To Be Documented.

Reducing n ranges in parallel (in the same vein than tmap, tfilter).
*/
template treduce0(alias fun)
{
    Unqual!E treduce0(E, R...)(E seed, R rs) if (allSatisfy!(isForwardRange, R))
    {
        Unqual!E result = seed;
        foreach(e; knit(rs)) // e is a std.typecons.Tuple
        {
            result = naryFun!fun(result, e.expand);
        }
        return result;
    }
}

/// ditto
template treduce(alias fun)
{
    ElementType!(Knit!R)
    treduce(R...)(R rs) if (allSatisfy!(isForwardRange, R))
    {

        auto r = knit(rs);
        enforce(!r.empty);
        auto e = r.front;
        foreach(i, Type; R) rs[i].popFront;
        return treduce0!fun(e, rs);
    }
}

/// ditto
template treduceR0(alias fun)
{
    Unqual!E treduceR0(E, R...)(E seed, R rs) if (allSatisfy!(isBidirectionalRange, R))
    {
        Unqual!E result = seed;
        foreach_reverse(e; knit(rs)) // e is a std.typecons.Tuple
        {
            result = naryFun!fun(e.expand, result);
        }
        return result;
    }
}

/// The right-fold pendant of treduce.
template treduceR(alias fun)
{
    ElementType!(Knit!R)
    treduceR(R...)(R rs) if (allSatisfy!(isBidirectionalRange, R))
    {

        auto r = knit(rs);
        enforce(!r.empty);
        auto e = r.back;
        foreach(i, Type; R) rs[i].popBack;
        return treduceR0!fun(e, rs);
    }
}


template nreduce(alias fun)
{
    alias NReduce!(fun).nreduce nreduce;
}

template NReduce(alias fun)
{
    S nreduce(S,R)(S seed, R range) if (isInputRange!R)
    {
        S result = seed;
        auto s = stride(segment!(arity!fun-1)(range), arity!fun-1);
        foreach(elem; s)
        {
            result = naryFun!fun(result, elem.expand);
        }
        return result;
    }

    ElementType!R nreduce(R)(R range) if (isInputRange!R)
    {
        enforce(!range.empty);
        auto result = range.front;
        range.popFront;
        auto s = stride(segment!(arity!fun-1)(range), arity!fun-1);
        foreach(elem; s)
        {
            result = naryFun!fun(result, elem.expand);
        }
        return result;
    }
}

R init(R)(R range)
{
    return R.init;
}
