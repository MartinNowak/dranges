// Written in the D programming language

/**
This module defines new ranges or rather, higher-order ranges: ranges acting on ranges
to transform them or present a new view. As far as possible, all higher-order ranges presented in this module
and in $(M dranges.algorithm) are "tight wrappers": they are bidirectional if their input range is bidirectional,
define $(M opIndex), $(M opIndexAssign), $(M length) if it's possible, etc. That way, a good input range (for example, a random-access range)
will see its properties propagated through a chain of calls.
$(UL
  $(LI Some of these are usual in other languages (Haskell, Scala, Clojure, ...) and are quite useful: $(M drop), $(M dropWhile), $(M takeWhile), etc.)
  $(LI Some are extension of standard functions: $(M delay) as a generic way to segment a range.)
  $(LI Some are there just for fun and served as exercices when I wanted to "grok" ranges (like $(M torus), $(M bounce), $(M emptyRange), $(M once)).)
  )
Also, once we admit $(M std.typecons.tuples) as a common way to return many values, tuple-returning
ranges can be acted upon in various ways, splicing/shredding/rotating/stitching them. As many ranges and algorithms
presented in this package produce tuples, having a rich way to act upon them permits all kinds of reuse.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.range;

import std.algorithm,
       std.array,
       std.bigint,
       std.conv,
       std.exception,
       std.functional,
       std.math,
       std.metastrings,
       std.range,
       std.stdio,
       std.string,
       std.traits,
       std.typecons,
       std.typetuple;

import dranges.algorithm,
       dranges.functional,
       dranges.predicate,
       dranges.templates,
       dranges.tuple,
       dranges.traits,
       dranges.typetuple;

/**
Return:
the smallest length of all non-infinite ranges passed as inputs. All finite ranges must have a length member.
Example:
----
auto s = ["a","b","c","d","e","f"];
int[] r = [0,1,2,3];
auto c = repeat(5); // infinite
auto ml = minLength(s,r,c);
assert(ml == 4); // r length
----
*/
size_t minLength(R...)(R ranges) if (allSatisfy!(isForwardRange, R) && allHaveLength!R && !allAreInfinite!R)
{
    size_t minL = size_t.max;
    foreach(i,Range; R) {
        static if (hasLength!Range) {
            if (ranges[i].length < minL) minL = ranges[i].length;
        }
    }
    return minL;
}

unittest
{
    auto s = ["a","b","c","d","e","f"];
    int[] r = [0,1,2,3];
    auto c = repeat(5); // infinite
    auto ml = minLength(s,r,c);
    assert(ml == 4); // r length
}

/+
auto takeLast(R)(R range, size_t n) if (isBidirectionalRange!R)
{
//    static if (hasSlicing!R && hasLength!R) {
//        if (n > range.length) { n = range.length;}
//        return range[range.length-n .. range.length];
//    }
//    else
        return retro(take(retro(range),n)); // Not exactly right, as take may not be a bidir range
}
+/

/**
Returns a copy of r, with the first n elements dropped. Compare to
popFrontN which affects r. "n" is the first argument as in std.range.take
(which in turn takes this from Haskell)
----
auto r1 = [0,1,2,3,4,5];
auto d = drop(3, r1);
assert(equal(d, [3,4,5][]));
assert(equal(drop(0, r1), r1)); // drops 0 element -> equal to r1
assert(drop(6, r1).empty); // drops all elements -> empty range
assert(drop(100, r1).empty); // drops more than r1.length -> empty range.
----
Note:
It's not lazy: it drops all available elements during the call.
*/
R drop(R)(R r, size_t n) if (isForwardRange!(R))
{
    static if (hasSlicing!(R) && hasLength!(R))
    {
        n = min(n, r.length);
        return r[n .. r.length];
    }
    else
    {
        R rr = r;
        while(! rr.empty && n>0) {
            rr.popFront;
            --n;
        }
        return rr;
    }
}

unittest
{
    auto r1 = [0,1,2,3,4,5];
    assert(isInputRange!(int[]));
    auto d = drop(r1,3);
    assert(equal(d, [3,4,5][]));
    assert(equal(drop(r1,0), r1));
    assert(drop(r1,6).empty);
    assert(drop(r1,100).empty);
}

/**
To Be Documented.
*/
Take!R slice(R)(R range, int begin, int end)
{
    return take(drop(range, begin), end-begin);
}

/**
Drops the last n elements of range. R must be bidirectional.
*/
R dropLast(R)(R range, size_t n) if (isBidirectionalRange!R)
{
    return retro(drop(retro(range), n));
}

unittest
{
    auto r1 = [0,1,2,3,4,5];
    auto d = dropLast(r1,3);
    assert(equal(d, [0,1,2][]));
    assert(equal(dropLast(r1,0), r1));
    assert(dropLast(r1,6).empty);
    assert(dropLast(r1,100).empty);
}

/**
Returns a copy of r, with the first elements dropped as long as pred if verified. Compare to
popFrontWhile which affects r.

The predicate may be unary:
----
string s = "  , abcd  efg";
auto d1 = dropWhile!(isOneOf!" ,")(s); // isOneOf!" ," returns true for " " and for ","
assert(d1 == "abcd  efg");

auto r1 = [0,1,2,3,3,4,5];
auto d2 = dropWhile!"a<4"(r1);      // String predicate
assert(equal(d2, [4,5][]));
----

Or it can be binary (or ternary, or whatever), possibly a string, as "a<b".

The second (optional) argment is the step, which must be between 1 and the pred's arity. Step's default is 1.

If step == arity, it will drop the entire segment at each step.

Example:
----
auto d3 = dropWhile!"a<b"(r1);     // drop as long as r1 is strictly increasing, testing with binary predicate "a<b"
                                   // It will test [0,1] and drop 0. Then test [1,2] and drop 1, ...
assert(equal(d3, [3,3,4,5][]));    // the result begins with a couple for which a<b doesn"t hold

auto d4 = dropWhile!("a<b",2)(r1); // drop as long as r1 is strictly increasing, testing with binary predicate, step of 2
                                   // It will test [0,1] and drop [0,1]. Then test [2,3] and drop it also.
                                   // Then it will drop [3,4] and stop at 5.
assert(equal(d4, [5][]));

auto d5 = dropWhile!"a<b && b<c"(r1); // Growing range, with three args (step defaults to 1)
assert(equal(d5, [2,3,3,4,5][]));

bool foo(int a, int b) { return a*b < 3;}
auto d6 = dropWhile!foo(r1);            // binary fun as predicate
assert(equal(d6, [2,3,3,4,5][]));

auto d7 = dropWhile!"true"(r1); // 0-arg predicate, always true -> drops everything -> d7 is empty
assert(d7.empty);

int[] e;
assert(dropWhile!"a<4"(e).empty); // dropping on an empty range: always empty

auto r2 = [1];
auto d8 = dropWhile!"a<b"(r2); // binary predicate: cannot be true applied on [1] -> stops at once
assert(equal(d8, [1][]));
----
*/
R dropWhile(alias pred, size_t step = 1, R)(R r) if (isForwardRange!(R) && arity!pred > 0)
{
    R result = r;
    auto sr = stride(segment!(arity!pred)(r),step);

    alias Prepare!(pred, TypeNuple!(Unqual!(ElementType!R), arity!pred)) predicate;
    while(!sr.empty && predicate(sr.front)) {
        sr.popFront;
        popFrontN(result, step);
    }
    return result;
}

// special case for a 0-arg predicate: dropWhile!"true"(r).
R dropWhile(alias pred, R)(R r) if (isForwardRange!(R) && arity!pred == 0)
{
    R result = r;
    alias naryFun!pred predicate; // 0-arg predicate
    while(!result.empty && predicate()) result.popFront;
    return result;
}

unittest
{
// Unary predicate tests:
    string s = "  , abcd  efg";
    auto d1 = dropWhile!(isOneOf!" ,")(s);
    assert(d1 == "abcd  efg");

    auto r1 = [0,1,2,3,3,4,5];
    auto d2 = dropWhile!"a<4"(r1);      // String predicate
    assert(equal(d2, [4,5][]));

    assert(equal(dropWhile!("a<4",1)(r1), dropWhile!"a<4"(r1))); // Unary pred: you can tell dropWhile it's unary...

// N-ary predicate tests:
    auto d3 = dropWhile!("a<b")(r1);  // drop as long as r1 is strictly increasing, testing with binary predicate "a<b"
                                        // It will test [0,1] and drop 0. Then test [1,2] and drop 1, ...
    assert(equal(d3, [3,3,4,5][]));     // the result begins with a couple for which a<b doesn"t hold

    auto d4 = dropWhile!("a<b",2)(r1);// drop as long as r1 is strictly increasing, testing with binary predicate, step of 2
                                        // It will test [0,1] and drop [0,1]. Then test [2,3] and drop it also.
                                        // Then it will drop [3,4] and stop at 5.
    assert(equal(d4, [5][]));

    auto d5 = dropWhile!("a<b && b<c")(r1); // Growing range, with three args (step defaults to 1)
    assert(equal(d5, [2,3,3,4,5][]));

    bool foo(int a, int b) { return a*b < 3;}
    auto d6 = dropWhile!foo(r1);            // binary fun as predicate
    assert(equal(d6, [2,3,3,4,5][]));

    auto d7 = dropWhile!"true"(r1); // 0-arg predicate, always true -> drops everything -> d7 is empty
    assert(d7.empty);

    int[] e;
    assert(dropWhile!"a<4"(e).empty); // dropping on an empty range: always empty

    auto r2 = [1];
    auto d8 = dropWhile!"a<b"(r2); // binary predicate: cannot be true aplied on [1] -> stops at once
    assert(equal(d8, [1][]));
}

/**
Advances range while predicate pred is true. It will change range!
The predicate can be a function or a string. If it's a binary (or more) predicate,
it will test as many elements (2, 3...) in one step.

There is an optional argument: the step, defaulting to 1.
Returns: the number of elements popped.
See_Also: dropWhile.
Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = [0,1,2,3,4];
auto r3 = [0,1,2,1,0];
auto r4 = [0,1,2,3,2,1];
auto e;

auto a = popFrontWhile!"a<2"(r1); // standard use
assert(equal(r1, [2,3,4][]));
assert(a == 2);

a = popFrontWhile!"a>5"(r2);
assert(equal(r2, [0,1,2,3,4][])); // false predicate, nothing changed
assert(a == 0);

a = popFrontWhile!"a<b"(r3); // binary predicate, step defaults to 1.
assert(equal(r3, [2,1,0][]));
assert(a == 2);

a = popFrontWhile!("a<b",2)(r4); // binary predicate, step of 2.
assert(equal(r4, [2,1][]));
assert(a == 4);

a = popFrontWhile!"a>5"(e); // On an empty range, pops nothing.
assert(a == 0);
----
*/
size_t popFrontWhile(alias pred, size_t step = 1, R)(ref R r) if (isForwardRange!(R) && arity!pred > 0)
{
    auto sr = stride(segment!(arity!pred)(r),step);
    size_t pops;
    alias Prepare!(pred, TypeNuple!(Unqual!(ElementType!R), arity!pred)) predicate;
    while(!sr.empty && predicate(sr.front)) {
        sr.popFront;
        popFrontN(r, step);
        ++pops;
    }
    return pops*step;
}

// special case for a 0-arg predicate: popfrontWhile!"true"(r).
size_t popFrontWhile(alias pred, R)(ref R r) if (isForwardRange!(R) && arity!pred == 0)
{
    alias naryFun!pred predicate; // 0-arg predicate
    while(!r.empty && predicate()) {
        result.popFront;
        ++pops;
    }
    return pops*step;
}

unittest {
    auto r1 = [0,1,2,3,4];
    auto r2 = [0,1,2,3,4];
    auto r3 = [0,1,2,1,0];
    auto r4 = [0,1,2,3,2,1];
    int[] e;

    auto a = popFrontWhile!"a<2"(r1);
    assert(equal(r1, [2,3,4][]));
    assert(a == 2);

    a = popFrontWhile!"a>5"(r2);
    assert(equal(r2, [0,1,2,3,4][])); // false predicate, nothing changed
    assert(a == 0);

    a = popFrontWhile!"a<b"(r3); // binary predicate, step defaults to 1.
    assert(equal(r3, [2,1,0][]));
    assert(a == 2);

    a = popFrontWhile!("a<b",2)(r4); // binary predicate, step of 2.
    assert(equal(r4, [2,1][]));
    assert(a == 4);

    a = popFrontWhile!"a>5"(e); // On an empty range, pops nothing.
    assert(a == 0);
}

/**
Takes elements from range as long as pred is verified. Usually, the predicate
is a unary function. It can be a binary (or more) function, but only the first element is delivered.
Compared to dropWhile and such, there is no step option.
Example:
----
auto r1 = [0,1,2,3,4,4,6,1,1,1,0];
auto tw1 = takeWhile!"a<6"(r1); // unary predicate
assert(equal(tw1, [0,1,2,3,4,4][]));
auto tw2 = takeWhile!"a<b"(r1); // binary predicate
assert(equal(tw2, [0,1,2,3][]));
bool foo(int a, int b, int c) {return a<b && b<c;} // ternary predicate
auto tw3 = takeWhile!foo(r1);
assert(equal(tw3, [0,1,2][]));
----
*/
struct TakeWhile(alias pred, R) if (isForwardRange!R && arity!pred > 0)
{
    alias Prepare!(pred, TypeNuple!(ElementType!R, arity!pred)) predicate;
    Knit!(TypeNuple!(R, arity!pred)) _sr;
    R _range;

    this(R range) {
        _range = range;
        _sr = segment!(arity!pred)(range);
    }

    bool empty() @property {
        return _sr.empty || !predicate(_sr.front);
    }

    ElementType!R front() @property {
        return _range.front;
    }

    @property TakeWhile save() { return this;}

    void popFront() {
        _range.popFront;
        _sr.popFront;
    }
}

// special case: a 0-arg predicate, ie: takeWhile!"true"(r1) or takeWhile!"false"(r1)
/// ditto
struct TakeWhile(alias pred, R) if (isForwardRange!R && arity!pred ==0)
{
    alias naryFun!pred predicate;
    R _range;

    this(R range) {
        _range = range;
    }

    bool empty() {
        return _range.empty || !predicate();
    }

    ElementType!R front() {
        return _range.front;
    }

    @property TakeWhile save() { return this;}

    void popFront() {
        _range.popFront;
    }
}

/// ditto
TakeWhile!(pred,R) takeWhile(alias pred, R)(R range) if (isForwardRange!R)
{
    return TakeWhile!(pred, R)(range);
}

unittest {
    auto r1 = [0,1,2,3,4,4,6,1,1,1,0];
    auto tw1 = takeWhile!"a<6"(r1); // unary predicate
    assert(equal(tw1, [0,1,2,3,4,4][]));
    auto tw2 = takeWhile!"a<b"(r1); // binary predicate
    assert(equal(tw2, [0,1,2,3][]));
    bool foo(int a, int b, int c) {return a<b && b<c;} // ternary predicate
    auto tw3 = takeWhile!foo(r1);
    assert(equal(tw3, [0,1,2][]));
    auto tw4 = takeWhile!"true"(r1); // 0-arg predicate (seems silly, but may be generated by a template)
    assert(equal(tw4, r1));
    auto tw5 = takeWhile!"false"(r1);
    assert(tw5.empty);

    int[] e;
    assert(takeWhile!"a>b"(e).empty); // takeWhile on an empty range -> empty
}

/**
Like the eponymous function found in all functional languages.
Returns the range minus its first element. If range is empty
it just returns it.
Example:
----
auto r = [0,1,2,3];
auto tails = [r][];
foreach(i; 0..5) {
    r = tail(r);
    tails ~= r;
}
assert(equal(tails, [[0,1,2,3], [1,2,3], [2,3], [3], [], [] ][]));
----
*/
R tail(R)(R range) if (isInputRange!R)
{
    if (!range.empty) range.popFront;
    return range;
}

unittest
{
    auto r = [0,1,2,3];
    auto tails = [r][];
    foreach(i; 0..5) {
        r = tail(r);
        tails ~= r;
    }
    assert(equal(tails, [[0,1,2,3], [1,2,3], [2,3], [3], [], [] ][]));
}


// helper function for tails
Tuple!(R, R, bool) nextTail(R)(R range, bool empt = false) if (isInputRange!R)
{
    auto t = tail(range);
    return tuple(t, t, range.empty);
}

// helper function for tails. Needed to get DMD happy with the predicate type.
// unfold2!(nextTail!R, "c")(range, false) works perfectly well,
// but the compiler does not like the corresponding return type
bool isE(R)(R r, R r2, bool empt) { return empt;}

/**
Returns the successive application of tail on a range, up to the empty range.
If the input range is empty, tails is empty.
Example:
----
auto r = [0,1,2,3];
auto t = tails(r);
assert(equal(t, [[1,2,3], [2,3], [3], [] ][]));

int[] e;
auto t1 = tails(r[0..1]);
assert(equal(t1, [e][])); // One element -> [] and then stops.

auto te = tails(e);
assert(te.empty); // No element -> empty
----
*/

Tails!R tails(R)(R range) if (isForwardRange!R)
{
    return unfold2!(nextTail!R, isE!R)(range, false);
}

template Tails(R) if (isForwardRange!R)
{
    alias Unfold2!(nextTail!R, isE!R, R, bool) Tails;
}

unittest
{
    auto r = [0,1,2,3];
    auto t = tails(r);
    assert(equal(t, [[1,2,3], [2,3], [3], [] ][]));

    int[] e;                  // empty range
    auto t1 = tails(r[0..1]); // One element range
    assert(equal(t1, [e][])); // One element -> [] and then stops.

    auto te = tails(e);
    assert(te.empty); // No element -> empty
}


/**
Takes n successive elements from range, with n going from 0 (an empty range) to range.length included.
It's more efficient for a range with a length: heads knows when to stop. For a range
that doesn"t know its length, heads has to calculate for each new head if it's the entire range.
Example:
----
auto r = [0,1,2,3];
auto h = heads(r);
assert(equal(h, [[], [0], [0,1], [0,1,2], [0,1,2,3] ][])); // from [] up to r itself.

auto f = filter!"a<10"(r); // equivalent to r, but doesn"t know its own length
auto hf = heads(f);
foreach(elem; hf) { // Compare it to f
    assert(equal(elem, h.front)); // They are indeed the same
    h.popFront;
    l++; // accumulate length
}
popFrontN(hf, l); // get rid of all elements?
assert(hf.empty); // Yes, it's empty
----
*/
Heads!R heads(R)(R range) if (isForwardRange!R)
{
    static if (hasLength!R)
        return tmap!(take!R)(repeat(range), numberz(range.length+1));
    else
        return HeadsStruct!R(range);
}

template Heads(R) if (isForwardRange!R)
{
    static if (hasLength!R)
        alias TMapType!(take!R, Repeat!R, Numberz!size_t) Heads;
    else
        alias HeadsStruct!R Heads;
}

struct HeadsStruct(R) if (isForwardRange!R && !hasLength!R)
{
    R _range;
    size_t n;
    this(R range) { _range = range;}
    bool empty() {
        return (n>0 && drop(n-1,_range).empty && drop(n,_range).empty);
    }
    Take!R front() { return take(_range, n);}
    @property HeadsStruct save() { return this;}
    void popFront() {n++;}
}

unittest
{
    auto r = [0,1,2,3];
    auto h = heads(r);
    auto witness = [ [], [0], [0,1], [0,1,2], [0,1,2,3] ][];
    foreach(elem; h) {
        assert(equal(elem, witness.front));
        witness.popFront;
    }

    auto f = filter!"a<10"(r); // does not know its own length
//    auto hf = heads(f);
    size_t l;
//    foreach(elem; hf) { // Compare it to f
//        assert(equal(elem, h.front));
//        h.popFront;
//        l++; // accumulate length
//    }
//    popFrontN(hf, l); // get rid of all elements?
//    assert(hf.empty); // Yes, it's empty
}

/**
Inserts an element or an entire range into range1 at position n. Position 0 means before range1. If position >= range1.length,
element/range2 is just concatenated at the end.
Examples:
----
auto r1 = [0,1,2,3];
auto m = map!"a*a"(r1);

auto ia0 = insertAt(0, r1, m);
auto ia2 = insertAt(2, r1, m);
auto ia10 = insertAt(10, r1, m);

assert(equal(ia0, [0,1,4,9,  0,1,2,3][]));
assert(equal(ia2, [0,1,  0,1,4,9,  2,3][]));
assert(equal(ia10,[0,1,2,3,  0,1,4,9][]));

auto ia1 = insertAt(1, r1, 99);
assert(equal(ia1, [0,99,1,2,3][]));
----
*/
Chain!(typeof(take(R1.init, 0)), R2, R1) insertAt(R1, R2)(size_t n, R1 range1, R2 range2) if (allSatisfy!(isForwardRange, R1, R2))
{
    return chain(take(range1, n), range2, drop(range1, n));
}

/// ditto
Chain!(typeof(take(R.init,0)), E[], R) insertAt(R, E)(size_t n, R range, E element) if (isForwardRange!R && is(ElementType!R == E))
{
    return chain(take(range, n), [element][], drop(range, n));
}

unittest
{
    auto r1 = [0,1,2,3];
    auto m = map!"a*a"(r1);
    auto ia0 = insertAt(0, r1, m);
    auto ia2 = insertAt(2, r1, m);
    auto ia10 = insertAt(10, r1, m);
    assert(equal(ia0, [0,1,4,9,  0,1,2,3][]));
    assert(equal(ia2, [0,1,  0,1,4,9,  2,3][]));
    assert(equal(ia10,[0,1,2,3,  0,1,4,9][]));

    auto ia1 = insertAt(1, r1, 99);
    assert(equal(ia1, [0,99,1,2,3][]));
}

/**
Cuts a range in two parts, separating them at _index index. It returns the parts as a tuple.
The second part will begin with range[index].
If slicing is available, it will use it and return a Tuple!(R,R). If not, it iterates the range
and returns a Tuple!( (ElementType!R)[], R ).
----
auto r1 = [0,1,2,3,4,5]; // Cutting an array (range with length and slicing)
auto c1 = cutAt(3, r1);
assert(first(c1) == [0,1,2][]);     // first part
assert(second(c1) == [3,4,5][]);    // second part
assert(equal(r1, [0,1,2,3,4,5][])); // r1 is unchanged
auto c2 = cutAt(0, r1);             // Cuts at position 0
assert(first(c2).empty);
assert(second(c2) == r1);
auto c3 = cutAt(1000, r1);          // Cuts farther than range.length. No exception is thrown, it returns (range, [])
assert(first(c3) == r1);
assert(second(c3).empty);
auto c4 = cutAt(5, stutter(3, r1)); // Cutting a range with a length but no slicing
assert(equal(first(c4), [0,0,0,1,1][]));
assert(is(typeof(first(c4)) == int[]));           // The first part is an int[] (nothing more can be done generically)
assert(equal(second(c4), [1,2,2,2,3,3,3,4,4,4,5,5,5][]));
assert(is(typeof(second(c4)) == Stutter!(int[]))); // The second part is still a Stutter
----
*/
Tuple!(R, R) cutAt(R)(size_t index, R range) if (isForwardRange!R && hasSlicing!R && hasLength!R)
{
    if (index > range.length) index = range.length;
    return tuple(range[0 .. index], range[index .. range.length]);
}

/// ditto
Tuple!(ElementType!R[], R) cutAt(R)(size_t index, R range) if (isForwardRange!R && (!hasSlicing!(R) || !hasLength!(R)))
{
    ElementType!R[] firstPart;
    R secondPart = range;
    foreach(i; 0 .. index) {
        if (secondPart.empty) break;
        firstPart ~= secondPart.front();
        secondPart.popFront();
    }
    return tuple(firstPart, secondPart);
}

unittest
{
    auto r1 = [0,1,2,3,4,5]; // Cutting an array (range with length and slicing)
    auto c1 = cutAt(3, r1);
    assert(first(c1) == [0,1,2][]);     // first part
    assert(second(c1) == [3,4,5][]);    // second part
    assert(equal(r1, [0,1,2,3,4,5][])); // r1 is unchanged
    auto c2 = cutAt(0, r1);             // Cuts at position 0
    assert(first(c2).empty);
    assert(second(c2) == r1);
    auto c3 = cutAt(1000, r1);          // Cuts farther than range.length. No exception is thrown, it returns (range, [])
    assert(first(c3) == r1);
    assert(second(c3).empty);

    auto c4 = cutAt(5, stutter(3, r1)); // Cutting a range with a length but no slicing
    assert(equal(first(c4), [0,0,0,1,1][]));
    assert(is(typeof(first(c4)) == int[]));           // The first part is an int[] (nothing more can be done generically)
    assert(equal(second(c4), [1,2,2,2,3,3,3,4,4,4,5,5,5][]));
    assert(is(typeof(second(c4)) == Stutter!(int[]))); // The second part is still a Stutter

    // Cutting an empty range
    int[] e;
    auto c5 = cutAt(4, e); // Cutting an empty range results in two empty ranges of same nature
    assert(first(c5).empty);
    assert(is(ElementType!(typeof(first(c5))) == int));
    assert(second(c5).empty);
    assert(is(ElementType!(typeof(second(c5))) == int));
}

/**
Iterates on range as long as pred(elem) is verified. Then returns a tuple containing the first part as an array
and the second part as a truncated range.

Note: It cannot return a Tuple!(R,R) as sometimes we cannot construct a R from the popped elements: if
R is a Map!() for example, there is no easy and generic way for the first part to be created as a Map also.

Example:
----
auto r1 = [0,1,2,3,4];
auto cut = cutWhen!"a<3"(r1);
assert(equal(cut.field[0], [0,1,2][]));
assert(equal(cut.field[1], [3,4][]));

assert(equal(r1, [0,1,2,3,4][])); // r1 is unchanged
----
*/
Tuple!(ElementType!(R)[], R) cutWhen(alias pred, R)(R range) if (isForwardRange!R)
{
    alias unaryFun!(pred) predicate;
    ElementType!(R)[] firstPart;
    R secondPart = range;
    while (!range.empty && predicate(secondPart.front)) {
        firstPart ~= secondPart.front();
        secondPart.popFront();
    }
    return Tuple!(ElementType!(R)[], R)(firstPart, secondPart);
}

unittest {
    auto r1 = [0,1,2,3,4];
    auto cut = cutWhen!"a<3"(r1);
    assert(equal(cut.field[0], [0,1,2][]));
    assert(equal(cut.field[1], [3,4][]));

    assert(equal(r1, [0,1,2,3,4][])); // r1 is unchanged
}


/**
An alternate (simpler) form of std.range.zip: produce a range of std.typecons.Tuples from
a variadic list. Used mainly to interact with other ranges, as Tuples are more generic
than Proxy. It will stops as soon as one of the input ranges is empty.
If only one range is given as input, it will still produce a tuple. So knit(r) != r

It's an extensible range: opIndex, back, popBack, length, opIndex, opIndexAssign and opSlice
are defined if possible (though some improvement could be made on dealing with infinite ranges).
If all ranges are infinite, Knit sees it and defines itself as infinite also.

Note:
it unqualifies the element types (ie: a string has immutable(char) for element type,
but the tuple will use only char).

Example:
----
auto r1 = [0,1,2,3,4,5];
auto r2 = [3.14, 2.78, 0.25, -1.0, 0.0];
auto s = ["a","b","c","d"];

auto k = knit(r1,s,r2);
assert(k.front == tuple(0,"a",3.14));
assert(equal(k, [tuple(0,"a",3.14), tuple(1,"b",2.78), tuple(2,"c",0.25), tuple(3,"d",-1.0)][]));

// Defining more operations:
assert(k.length == s.length); // length is defined
// back and popBack are defined
assert(equal(retro(k),
            [tuple(3,"d",-1.0), tuple(2,"c",0.25), tuple(1,"b",2.78), tuple(0,"a",3.14)][]));
assert(k[2] == tuple(2, "c", 0.25)); // opIndex is defined
assert(equal(k[1..3], [tuple(1, "b", 2.78), tuple(2, "c", 0.25)][])); // opSlice is defined

// More operations impossible:
auto m = map!"a*a"(r2); // no .length, .back, ... (except if you use phobos_extension.d)
auto k2 = knit(r1, r2, m);
assert(k2.front == tuple(0, 3.14, 3.14*3.14));
assert(!is(typeof(k2.length))); // so no .length defined for k2. Nor .back, etc.

// OpIndexAssign: needs ranges which are assignable (ie: no string, map...)
auto k3 = knit(r1, r2);
k3[2] = tuple(0, 0.0);
assert(equal(k3, [tuple(0, 3.14), tuple(1,2.78), tuple(0,0.0), tuple(3, -1.0), tuple(4, 0.0)][]));

// On empty ranges: empty
assert(knit(r1, emptyRange!int, r2).empty);
----
Limitation:
It cannot be sorted, as front/back do not return by ref. std.range.Zip sort of cheats, inserting a
special proxySwap method inside its Proxy, which is treated specially by std.algo.sortImpl. If you
need a Knit to be sorted, you can call sortAsArray on it.
Example:
----
auto ak = sortAsArray(k);
----
*/
struct Knit(R...) if (allSatisfy!(isForwardRange,R)) {
    R _ranges;
    alias Tuple!(staticMap!(Unqual, ElementTypes!R)) FrontTuple;
//    alias Tuple!(ElementTypes!R) FrontTuple;

    this(R ranges) {
        _ranges = ranges;
        static if (allHaveLength!R && !allAreInfinite!R && allSatisfy!(hasSlicing, R))
            truncate(_ranges);
    }

    static if (allAreInfinite!R) {
        enum bool empty = false; // Then Knit is also infinite
    }
    else {
        bool empty() {
            return someEmpty(_ranges);
        }
    }

    FrontTuple front() {
        FrontTuple f;
        foreach(i, r; _ranges) {
            f.field[i] = r.front;
        }
        return f;
    }

    @property Knit save() { return this;}

    void popFront() {
        foreach(i, r; _ranges) {
            _ranges[i].popFront;
        }
    }

    static if (allSatisfy!(isRandomAccessRange, R)) {
        FrontTuple opIndex(size_t n) {
            FrontTuple result;
            foreach(i, r; _ranges) {
                result.field[i] = r[n];
            }
            return result;
        }
    }

    static if (allSatisfy!(hasAssignableElements, R)) {
        void opIndexAssign(FrontTuple ft, size_t n) {
            foreach(i, r; _ranges) {
                _ranges[i][n] = ft.field[i];
            }
        }
    }

    static if(allSatisfy!(hasSlicing, R)) {
        Knit!R opSlice(size_t index1, size_t index2) {
            R _sliced;
            _sliced = _ranges;
            foreach(i, elem; _sliced) _sliced[i] = _sliced[i][index1 .. index2];
            return knit(_sliced);
        }
    }

    static if(allHaveLength!(R) && !allAreInfinite!(R))
        size_t length() {
            return minLength(_ranges);
        }

    static if(allHaveLength!(R) && !allAreInfinite!(R) && allSatisfy!(hasSlicing, R)) {
        static if (allSatisfy!(isBidirectionalRange, R)) {
            FrontTuple back() {
                FrontTuple f;
                foreach(i, r; _ranges) {
                    f.field[i] = r.back;
                }
                return f;
            }

            void popBack() {
                foreach(i, r; _ranges) {
                    _ranges[i].popBack;
                }
            }
        }
    }

//    mixin Chainable!();
}

Knit!(R) knit(R...)(R ranges) if (allSatisfy!(isForwardRange, R))
{
    return Knit!(R)(ranges);
}

unittest {
    auto r1 = [0,1,2,3,4,5];
    auto r2 = [3.14, 2.78, 0.25, -1.0, 0.0];
    auto s = ["a","b","c","d"];

    auto k = knit(r1,s, r2);
    assert(k.front == tuple(0,"a", 3.14));
    assert(equal(k, [tuple(0,"a", 3.14), tuple(1, "b", 2.78), tuple(2, "c", 0.25), tuple(3, "d", -1.0)][]));

    assert(k._ranges[1] == s);

// Defining more operations:
    assert(k.length == s.length); // length is defined
    assert(equal(retro(k), [tuple(3,"d", -1.0), tuple(2, "c", 0.25), tuple(1, "b", 2.78), tuple(0, "a", 3.14)][])); // back and popBack are defined
    assert(k[2] == tuple(2, "c", 0.25)); // opIndex is defined
    assert(equal(k[1..3], [tuple(1, "b", 2.78), tuple(2, "c", 0.25)][])); // opSlice is defined
    assert(k[0..0].empty);

// More operations impossible:
    auto m = map!"a*a"(r2); // no .length, .back, ...
    auto k2 = knit(r1, r2, m);
    assert(k2.front == tuple(0, 3.14, 3.14*3.14));
//    assert(!is(typeof(k2.length))); // so no .length defined for k2. Nor .back, etc.
    // Would Map have a length, back and such, k2 would have them also.

// OpIndexAssign: needs ranges which are assignable (ie: no string, map...)
    auto k3 = knit(r1, r2);
    k3[2] = tuple(0, 0.0);
    assert(equal(k3, [tuple(0, 3.14), tuple(1,2.78), tuple(0,0.0), tuple(3, -1.0), tuple(4, 0.0)][]));

// On empty ranges: empty
    int[] e;
    assert(knit(r1, e, r2).empty);
}

/**
Create a tuple-returning range from a variadic list of tuple-returning ranges by outputting their elements
all in parallel in one tuple.
(it's a bit like Knit, but it acts only on tuple-ranges and with auto-flattening of the tuples).
Tuple-returning ranges are knit, tmap, tfilter, segment, delay, ...
and obviously any map-like range with a tuple-returning function: map, comprehension, parallelComprehension, ...
Examples:
----
auto r1 = [0,1,2,3,4,5];
auto r2 = [0.1, 0.2, 0.3, 0.4];
auto r3 = ["abc", "def", "", "g"];
auto r4 = ["a", "b", "c", "d", "e", "f"];

auto k1 = knit(r1,r2); // returns Tuple!(int, double)
auto k2 = knit(r3,r4); // returns Tuple!(string, char)
auto tf = tfilter!"b<2"(r3,r1); // returns Tuple!(string, int);

auto s = stitch(k1,k2,tf); // returns Tuple!(int,double,string,char,string,int)

assert(s.front == tuple(0, 0.1, "abc", "a", "abc", 0));
s.popFront;
assert(s.front == tuple(1, 0.2, "def", "b", "def", 1));
s.popFront;
assert(s.empty); // tf stops there because now r1's elements are not less than 2. So s stops there also.
----
*/
StitchType!R stitch(R...)(R ranges) if (allSatisfy!(isTupleRange, R))
{
    // fun is "tuple(a.expand, b.expand, c.expand)", for example for 3 ranges.
    enum string fun = "tuple(" ~ Loop!(0, R.length, Stitcher); // Loop is found in dranges.functional.d
    return tmap!fun(ranges);
}

string Stitcher(uint n, uint max) { return az(n) ~ ".expand"~ (n < max-1 ? ", " : ")");}

template StitchType(R...) if (allSatisfy!(isTupleRange, R))
{
    alias TMapType!("tuple(" ~ Loop!(0, R.length, Stitcher), R) StitchType;
}

unittest
{
    auto r1 = [0,1,2,3,4,5];
    auto r2 = [0.1, 0.2, 0.3, 0.4];
    auto r3 = ["abc", "def", "", "g"];
    auto r4 = ["a", "b", "c", "d", "e", "f"];

    auto k1 = knit(r1, r2); // returns Tuple!(int, double)
    auto k2 = knit(r3,r4);  // returns Tuple!(string, char)
    auto tf = tfilter!"b<2"(r3,r1); // returns Tuple!(string, int);

    auto s = stitch(k1,k2,tf); // returns Tuple!(int,double,string,char,string,int)

    assert(s.front == tuple(0, 0.1, "abc", "a", "abc", 0));
    s.popFront;
    assert(s.front == tuple(1, 0.2, "def", "b", "def", 1));
    s.popFront;
    assert(s.empty); // tf stops there because now r1's elements are not less than 2. So s stops there also.
}

/**
Takes a tuple-producing range and rotate each tuple by n positions. If n>0,
it rotates to the left: takes the first n fields and put them at the end.
If n<0 it rotates to the right: takes the last n fields and put them at the beginning.

Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = [3.14, 2.78, 1.414];
auto s = ["a","b","c","d","e","f"];

// Let's create a tuple-returning range.
auto k = knit(r1,r2,s);
assert(is(ElementType!(typeof(k)) == Tuple!(int,double,string)));
assert(equal(k, [tuple(0,3.14,"a"), tuple(1,2.78,"b"), tuple(2,1.414,"c")][]));

auto rot1 = twist!1(k);
assert(is(ElementType!(typeof(rot1)) == Tuple!(double,string,int)));
assert(equal(rot1, [tuple(3.14,"a",0), tuple(2.78,"b",1), tuple(1.414,"c",2)][]));

auto rot_1 = twist!(-1)(k);
assert(is(ElementType!(typeof(rot_1)) == Tuple!(string,int,double)));
assert(equal(rot_1, [tuple("a",0,3.14), tuple("b",1,2.78), tuple("c",2,1.414)][]));
----
*/
Map!(naryFun!(rotateTuple!(n,ElementType!R.Types)),R)
twist(int n, R)(R range) if (isTupleRange!R)
{
    return map!(rotateTuple!(n,ElementType!R.Types))(range);
}

unittest
{
    auto r1 = [0,1,2,3,4];
    auto r2 = [3.14, 2.78, 1.414];
    auto s = ["a","b","c","d","e","f"];

    auto k = knit(r1,r2,s);
    assert(is(ElementType!(typeof(k)) == Tuple!(int,double,string)));
    assert(equal(k, [tuple(0,3.14,"a"), tuple(1,2.78,"b"), tuple(2,1.414,"c")][]));

    auto rot1 = twist!1(k);
    assert(is(ElementType!(typeof(rot1)) == Tuple!(double,string,int)));
    assert(equal(rot1, [tuple(3.14,"a",0), tuple(2.78,"b",1), tuple(1.414,"c",2)][]));

    auto rot_1 = twist!(-1)(k);
    assert(is(ElementType!(typeof(rot_1)) == Tuple!(string,int,double)));
    assert(equal(rot_1, [tuple("a",0,3.14), tuple("b",1,2.78), tuple("c",2,1.414)][]));
}

/**
Takes a tuple-producing range and reverse each tuple: the first field
becomes the last one, and so on.
Note: I"d like another name. twist?

Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = [3.14, 2.78, 1.414];
auto s = ["a","b","c","d","e","f"];

auto k = knit(r1,r2,s);
assert(is(ElementType!(typeof(k)) == Tuple!(int,double,string)));
assert(equal(k, [tuple(0,3.14,"a"), tuple(1,2.78,"b"), tuple(2,1.414,"c")][]));

auto rev = reverse(k);
assert(is(ElementType!(typeof(rev)) == Tuple!(string,double,int)));
assert(equal(rev, [tuple("a",3.14,0), tuple("b",2.78,1), tuple("c",1.414,2)][]));
----
*/
Map!(naryFun!(reverseTuple!(ElementType!R.Types)),R)
reverse(R)(R range) if (isTupleRange!R)
{
    return map!(reverseTuple!(ElementType!R.Types))(range);
}

unittest
{
    auto r1 = [0,1,2,3,4];
    auto r2 = [3.14, 2.78, 1.414];
    auto s = ["a","b","c","d","e","f"];

    auto k = knit(r1,r2,s);
    assert(is(ElementType!(typeof(k)) == Tuple!(int,double,string)));
    assert(equal(k, [tuple(0,3.14,"a"), tuple(1,2.78,"b"), tuple(2,1.414,"c")][]));

    auto rev = reverse(k);
    assert(is(ElementType!(typeof(rev)) == Tuple!(string,double,int)));
    assert(equal(rev, [tuple("a",3.14,0), tuple("b",2.78,1), tuple("c",1.414,2)][]));
}

/**
Takes a tuple-producing range, range1, and another range, range2 and creates a new tuple-returning range
which inserts the elements of range2 at position n into range1's elements. As for an array, index 0
is before all other elements, etc.

Example:
----
auto r1 = [0,1,2,3,4];
auto s = ["a","b","c","d","e","f"];
auto k = knit(r1,s); // k returns Tuple!(int,string)

auto r2 = [-2.1, 0.0, 3.14];

auto spl = splice!1(k,r2); // splices r2 in the middle of k's elements.
assert(is(ElementType!(typeof(spl)) == Tuple!(int,double,string)));
assert(equal(spl, [tuple(0,-2.1,"a"), tuple(1,0.0,"b"), tuple(2, 3.14, "c")][]));

auto spl2 = splice!0(spl,k); // splices k before all spl's elements.
assert(is(ElementType!(typeof(spl2)) == Tuple!(Tuple!(int,string), int,double,string))); // non-flattening
assert(equal(spl2, [tuple(tuple(0,"a"), 0,-2.1,"a"), tuple(tuple(1,"b"),1,0.0,"b"), tuple(tuple(2,"c"),2, 3.14, "c")][]));
----

As std.typecons.Tuple is not auto-flattening, you can splice tuple-producing ranges into one another.
Example:
----
auto spl2 = splice!0(spl,k); // splices k before all spl's elements.
assert(is(ElementType!(typeof(spl2)) == Tuple!(Tuple!(int,char), int,double,char))); // non-flattening
assert(equal(spl2, [tuple(tuple(0,"a"), 0,-2.1,"a"), tuple(tuple(1,"b"),1,0.0,"b"), tuple(tuple(2,"c"),2, 3.14, "c")][]));
----
*/
SpliceType!(n,R1,R2) splice(size_t n, R1, R2)(R1 range1, R2 range2)
if (allSatisfy!(isForwardRange, R1, R2) && is(ElementType!R1.Types) && (n <= ElementType!R1.Types.length)) {
    enum string splicer = "insertAtTuple!" ~ to!string(n) ~ "(a,b)";
    return tmap!splicer(range1,range2);
}

template SpliceType(size_t n, R1, R2)
{
    alias TMapType!("insertAtTuple!" ~ to!string(n) ~ "(a,b)", R1, R2) SpliceType;
}

unittest
{
    auto r1 = [0,1,2,3,4];
    auto s = ["a","b","c","d","e","f"];
    auto k = knit(r1,s);

    auto r2 = [-2.1, 0.0, 3.14];

    auto spl = splice!1(k,r2); // splices r2 in the middle of k's elements.
    assert(is(ElementType!(typeof(spl)) == Tuple!(int,double,string)));
    assert(equal(spl, [tuple(0,-2.1,"a"), tuple(1,0.0,"b"), tuple(2, 3.14, "c")][]));

    auto spl2 = splice!0(spl,k); // splices k before all spl's elements.
    assert(is(ElementType!(typeof(spl2)) == Tuple!(Tuple!(int,string), int,double,string))); // non-flattening
    assert(equal(spl2, [tuple(tuple(0,"a"), 0,-2.1,"a"), tuple(tuple(1,"b"),1,0.0,"b"), tuple(tuple(2,"c"),2, 3.14, "c")][]));
}

/**
Takes a tuple-producing range and an array of indices ([0,1,2] for example, meaning "first, second and third fields")
and returns a tuple-producing range whose elements" fields are those indicated by array.
The indices can be repeated, omitted, put in any order and the array can be longer than the input tuple ([0,1,2,3,2,1,3,1,0]).
Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = [3.14, 2.78,1.414];
string s = "abcdef";

auto k = knit(r1,r2,s);

auto shr1 = shred!([1,0])(k); // inverting the order
assert(equal(shr1, [tuple(3.14,0), tuple(2.78,1), tuple(1.414,2)][]));

auto shr2 = shred!([1])(k); // taking only one field
assert(equal(shr2, [tuple(3.14), tuple(2.78), tuple(1.414)][]));

auto shr3 = shred!([2,0,1,1])(k); // repating some fields
assert(equal(shr3, [tuple("a",0,3.14,3.14), tuple("b",1,2.78,2.78), tuple("c",2,1.414,1.414)][]));

auto shr4 = shred!([1,2,0])(shr3); // re-inverting the fields
assert(equal(shr4, k)); // this re-creates k
----
*/
ShredType!(array, R) shred(alias array, R)(R range)
if (isTupleRange!R && hasLength!(typeof(array)))
{
    return map!(naryFun!(shredTuple!(array, ElementType!R.Types)))(range);
}

/**
Another version of shred that takes only one index. It extracts the corresponding field
from a tuple-producing range's elements and returns that as a range, 'un-tuplified'.
That is, where shred!([1])(k) will produce a tuple-returning range (one-element tuples,
but tuples nonetheless), shred!1(k) will produce a standard range.
Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = [3.14, 2.78,1.414];
auto s = ["a","b","c","d","e","f"];

auto k = knit(r1,r2,s);

auto shr1 = shred!([1,0])(k); // inverting the order
assert(equal(shr1, [tuple(3.14,0), tuple(2.78,1), tuple(1.414,2)][]));

auto shr2 = shred!([1])(k); // taking only one field
assert(equal(shr2, [tuple(3.14), tuple(2.78), tuple(1.414)][]));

auto shr3 = shred!([2,0,1,1])(k); // repating some fields
assert(equal(shr3, [tuple("a",0,3.14,3.14), tuple("b",1,2.78,2.78), tuple("c",2,1.414,1.414)][]));

auto shr4 = shred!([1,2,0])(shr3); // re-inverting the fields
assert(equal(shr4, k)); // this re-creates k

auto shr5 = shred!1(k);
assert(equal(shr5, r2));
----
*/
ShredType!(n,R) shred(size_t n, R)(R range) if (isTupleRange!R)
{
    enum string shredder = "a.field[" ~ to!string(n) ~ "]";
    return map!(naryFun!shredder)(range);
}

template ShredType(alias array, R) if (isTupleRange!R && hasLength!(typeof(array)))
{
    alias Map!(naryFun!(shredTuple!(array, ElementType!R.Types)), R) ShredType;
}

template ShredType(size_t n, R) if (isTupleRange!R)
{
    alias Map!(naryFun!("a.field[" ~ to!string(n) ~ "]"), R) ShredType;
}
unittest
{
    auto r1 = [0,1,2,3,4];
    auto r2 = [3.14, 2.78,1.414];
    auto s = ["a","b","c","d","e","f"];

    auto k = knit(r1,r2,s);

    auto shr1 = shred!([1,0])(k); // inverting the order
    assert(equal(shr1, [tuple(3.14,0), tuple(2.78,1), tuple(1.414,2)][]));

    auto shr2 = shred!([1])(k); // taking only one field
    assert(equal(shr2, [tuple(3.14), tuple(2.78), tuple(1.414)][]));

    auto shr3 = shred!([2,0,1,1])(k); // repating some fields
    assert(equal(shr3, [tuple("a",0,3.14,3.14), tuple("b",1,2.78,2.78), tuple("c",2,1.414,1.414)][]));

    auto shr4 = shred!([1,2,0])(shr3); // re-inverting the fields
    assert(equal(shr4, k)); // this re-creates k

    auto shr5 = shred!1(k);
    assert(equal(shr5, r2));
}

/**
Takes a tuple-producing range whose elements are 1-element tuples (mainly, this can happen as the result
of some extracting, shredding, filtering, etc.) and "untuplify" it, extracting the tuples values.
Example:
----
auto r1 = [0,1,2,3,4];

auto k = knit(r1);
assert(equal(k, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4)]));
auto u = untuple(k);
assert(equal(u, r1)); // u is [0,1,2,3,4]
----
See_Also: shred.
*/
TMapType!("a", R) untuplify(R)(R range) if (isTupleRange!R && ElementType!R.Types.length == 1)
{
    return tmap!("a")(range);
}

unittest
{
    auto r1 = [0,1,2,3,4];

    auto k = knit(r1);
    assert(equal(k, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4)][]));
    auto u = untuplify(k);
    assert(equal(u, r1));
}


/**
A range that iterates alternatively on the ranges given at creation. It's related
to std.range.Transversal, but will iterated on all "columns" and will stop
as soon as one of them is empty.
Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = repeat(5);
auto r3 = [-2.0, -1.0, 0.0, 1.0];

auto t = transverse(r1, r2, r3);
assert(is(ElementType!(typeof(t)) == double)); // double is the common type for (int, int, double)
assert(equal(t, [0.0,5,-2,1,5,-1,2,5,0,3,5,1,4,5][])); // after 4,5, (the internal copy of) r3 is exhausted.

auto t2 = transverse(r1, emptyRange!double, emptyRange!short);
assert(is(ElementType!(typeof(t2)) == double));
assert(equal(t2, [0][])); // 0, then stops because it reaches emptyRange!double
----
*/
struct Transverse(R...) if (allSatisfy!(isForwardRange,R) && CompatibleRanges!R) {
    R _ranges;
    alias CommonElementType!R  ET;
    ET[] globalFront;
    bool willBeEmpty;

    this(R ranges) {
        _ranges = ranges;
        willBeEmpty = false;
        calculateFront;
    }

    private void calculateFront() {
        foreach(elem; _ranges) {
            if (!elem.empty) {
                globalFront ~= elem.front;
            }
            else {
                willBeEmpty = true;
                break;
            }
        }
    }

    bool empty() {
        return willBeEmpty && globalFront.empty;
    }

    @property Transverse save() { return this;}

    void popFront() {
        globalFront.popFront;
        if (globalFront.empty && !willBeEmpty) {
            foreach(i, elem; _ranges) _ranges[i].popFront;
            calculateFront;
        }
    }

    ET front() {
        return globalFront.front;
    }
}

/// ditto
Transverse!R transverse(R...)(R ranges) {
    return Transverse!(R)(ranges);
}

unittest {
    auto r1 = [0,1,2,3,4];
    auto r2 = repeat(5);
    auto r3 = [-2.0, -1.0, 0.0, 1.0];

    auto t = transverse(r1, r2, r3);
    assert(is(ElementType!(typeof(t)) == double)); // double is the common type for (int, int, double)
    assert(equal(t, [0.0,5,-2,1,5,-1,2,5,0,3,5,1,4,5][])); // after 4,5, (the internal copy of) r3 is exhausted.

    double[] e1;
    short[] e2;
    auto t2 = transverse(r1, e1, e2);
    assert(is(ElementType!(typeof(t2)) == double));
    assert(equal(t2, [0][])); // 0, then stops because it reaches emptyRange!double
}

/**
Simple use of transverse.
Alternates between bigRange and smallRange, rolling smallRange into a cycle.
Example:
----
auto i1 = interleave("abcdef", ",");    // -> a,b,c,d,e,f,
auto i2 = interleave("abcdef", ",;.");  // -> a,b;c.d,e;f.
auto r1 = [0,1,2,3,4];
auto i3 = interleave(r1,r1);
assert(equal(i3, [0,0,1,1,2,2,3,3,4,4][]));
----
*/
Transverse!(B,Cycle!S) interleave(B, S)(B bigRange, S smallRange) {
    return transverse(bigRange, cycle(smallRange));
}

unittest {
    auto i = interleave("abcdef", ",");
    assert(asString(i) == "a,b,c,d,e,f,"); // Yes, there is a "," at the end.
    auto i2 = interleave("abcdef", ",;.");
    assert(asString(i2) == "a,b;c.d,e;f.");
    auto r1 = [0,1,2,3,4];
    auto i3 = interleave(r1,r1);
    assert(equal(i3, [0,0,1,1,2,2,3,3,4,4][]));
}

template MaxArray(alias array, alias theMax = 0) {
    static if (array.length > 0) {
        alias MaxArray!(array[1..$], max(theMax, array[0])) MaxArray;
    }
    else {
        alias theMax MaxArray;
    }
}

/**
Cuts a range into segments of length segLength. segLength must be stricly positive.

To be compatible with other ranges, it produces tuples, not arrays. It's based on Knit
so if the original range defines back/popBack, length, opIndex or opIndexAssign, it will do so also.

It's used heavily internally by all ranges mapping a function or a predicate on a range.

See_Also: delay, parallel.

Examples:
----
auto r1 = [0,1,2,3,4,5];
auto s = segment!2(r1);
assert(equal(s, [tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][]));
assert(s.length == 5);         // .length
// back/popBack:
assert(equal(retro(s), retro([tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][])));
assert(s[3] == tuple(3,4));    // opIndex
s[3] = tuple(0,0);             // opIndexAssign
assert(s[2] == tuple(2,0));    // it affects its neighbors.
assert(s[4] == tuple(0,5));
assert(r1 == [0,1,2,0,0,5][]); // affects r1 back (no .dup internally)

auto st = ["a","b","c","d","e","f"]; // initial example with a string. Change due to DMD 2.041
auto s2 = segment!3(st);
assert(s2.front == tuple("a","b","c"));

r1 = [0,1,2,3,4,5]; // regenerates r1
auto s3 = segment!1(r1);
assert(equal(s3, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4), tuple(5)][]));

auto r2 = map!"a*a"(r1);
auto s4 = segment!2(r2); // On a forward range
assert(equal(s4, [tuple(0,1), tuple(1,4), tuple(4,9), tuple(9,16), tuple(16,25)][]));
----
*/
Knit!(TypeNuple!(R, segLength)) segment(size_t segLength, R)(R range) if (isForwardRange!R && segLength > 0)
{
    TypeNuple!(R, segLength) _ranges;
    foreach(i, Unused; _ranges) {
        _ranges[i] = range;
        popFrontN(_ranges[i], i);
        static if (isBidirectionalRange!R) {
            popBackN(_ranges[i], segLength-1-i);
        }
    }
    return knit(_ranges);
}

unittest
{
    auto r1 = [0,1,2,3,4,5];
    auto s = segment!2(r1);
    assert(equal(s, [tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][]));
    assert(s.length == 5);         // .length
    // back/popBack:
    assert(equal(retro(s), retro([tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][])));
    assert(s[3] == tuple(3,4));    // opIndex
    s[3] = tuple(0,0);             // opIndexAssign
    assert(s[2] == tuple(2,0));    // it affects its neighbors.
    assert(s[4] == tuple(0,5));
    assert(r1 == [0,1,2,0,0,5][]); // affects r1 back (no .dup internally)

    auto st = ["a","b","c","d","e","f"];
    auto s2 = segment!3(st);
    assert(s2.front == tuple("a","b","c"));

    r1 = [0,1,2,3,4,5]; // regenerates r1
    auto s3 = segment!1(r1);
    assert(equal(s3, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4), tuple(5)][]));

    auto r2 = map!"a*a"(r1);
    auto s4 = segment!2(r2); // On a forward range
    assert(equal(s4, [tuple(0,1), tuple(1,4), tuple(4,9), tuple(9,16), tuple(16,25)][]));

    int[] e;
    auto s5 = segment!2(e);
    assert(s5.empty);
}

/**
A generalization of segment: given an array of indices (as template argument) and a range,
it will produce the corresponding "extracts" (disjointed segments, as tuples).
segment!n(r) is equivalent to delay!([0,1,2, ...,n])(r).

But delay is much more powerful than segment.
----
delay!([2,1,0])(r);  // You can invert the values
delay!([4,9,2,0])(r); // take them from everywhere in the range
delay!([0,0,1])(r); // repeat some values
----

See_Also: segment, parallel.
Example:
----
auto r1 = [0,1,2,3,4,5];
auto d = delay!([0,1])(r1); // will iterate on the pair ([0,1,2,3,4,5], [1,2,3,4,5]).
                            // It's equivalent to segment!2(r1)
assert(equal(d, [tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][]));
assert(d.length == 5);         // .length
// back/popBack:
assert(equal(retro(d), retro([tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][])));

auto d2 = delay!([1,0])(r1); // inverting
assert(equal(d2, [tuple(1,0), tuple(2,1), tuple(3,2), tuple(4,3), tuple(5,4)][]));

auto d3 = delay!([0])(r1);   // one element
assert(equal(d3, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4), tuple(5)][]));

auto d4 = delay!([4,1,3,2])(r1); // disjoint extracts
assert(d4.front == tuple(4,1,3,2));
assert(d4.length == 2); // d4 is [(4,1,3,2),(5,2,4,3)]

auto d5 = delay!([0,0,1])(r1); // repeated values
assert(d5.front == tuple(0,0,1));

auto d6 = delay!([9,0])(r1);
assert(d6.empty);

int[] e;
assert(delay!([0,1])(e).empty);
----
*/
Knit!(TypeNuple!(R, array.length)) delay(alias array, R)(R range) if (isForwardRange!R && isArray!(typeof(array)) && array.length > 0)
{
    enum size_t l = array.length;
    TypeNuple!(R, l) _ranges;
    enum m = MaxArray!array;

    foreach(i, Unused; _ranges) {
        _ranges[i] = range;
       popFrontN( _ranges[i], array[i]);
        static if (isBidirectionalRange!R) {
            popBackN(_ranges[i], m-array[i]);
        }
    }
    return knit(_ranges);
}

unittest
{
    auto r1 = [0,1,2,3,4,5];
    auto d = delay!([0,1])(r1); // will iterate on the pair ([0,1,2,3,4,5], [1,2,3,4,5]).
                                // It's equivalent to segment!2(r1)
    assert(equal(d, [tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][]));
    assert(d.length == 5);         // .length
    // back/popBack:
    assert(equal(retro(d), retro([tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][])));

    auto d2 = delay!([1,0])(r1); // inverting
    assert(equal(d2, [tuple(1,0), tuple(2,1), tuple(3,2), tuple(4,3), tuple(5,4)][]));

    auto d3 = delay!([0])(r1);   // one element
    assert(equal(d3, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4), tuple(5)][]));

    auto d4 = delay!([4,1,3,2])(r1); // disjoint extracts
    assert(d4.front == tuple(4,1,3,2));
    assert(d4.length == 2); // d4 is [(4,1,3,2),(5,2,4,3)]

    auto d5 = delay!([0,0,1])(r1); // repeated values
    assert(d5.front == tuple(0,0,1));

    auto d6 = delay!([9,0])(r1);
    assert(d6.empty);

    int[] e;
    assert(delay!([0,1])(e).empty);
}

/**
Another "delay" cousin: takes a number (as template argument) and a range, and produces
a "knit" of n times the same range in parallel.
See_Also: segment, delay.
Example:
----
auto r1 = [0,1,2,3,4,5];
auto p = parallel!4(r1);
assert(equal(p, [tuple(0,0,0,0), tuple(1,1,1,1), tuple(2,2,2,2), tuple(3,3,3,3), tuple(4,4,4,4), tuple(5,5,5,5)][]));
----
*/
Knit!(TypeNuple!(R, n)) parallel(size_t n, R)(R range) if (isForwardRange!R && n > 0){
    TypeNuple!(R, n) temp;
    foreach(i, Unused; temp) temp[i] = range;
    return knit(temp);
}

unittest
{
    auto r1 = [0,1,2,3,4,5];
    auto p = parallel!4(r1);
    assert(equal(p, [tuple(0,0,0,0), tuple(1,1,1,1), tuple(2,2,2,2), tuple(3,3,3,3), tuple(4,4,4,4), tuple(5,5,5,5)][]));
}

/**
A simple wrapper to concatenate elements of a range of ranges.
It's equivalent to flatten!1(range), but it's only a forward range.

On a simple range, it has no effect (it's the identity function).

Example:
----
int[][] r1 = [[0,1,2], [3,4], [5]];
auto c = concat(r1);
assert(equal(c, [0,1,2,3,4,5][]));  // from an int[][] to an int[]
assert(equal(retro(c), retro([0,1,2,3,4,5][]))); // bidir range

auto r2 = [0,1,2,3];
auto ror = map!"take(a+1, repeat(a))"(r2); // Equivalent to [[0], [1,1], [2,2,2], [3,3,3,3]]
assert(equal(concat(ror), [0,1,1,2,2,2,3,3,3,3][]));

string sentence = "the quick brown fox jumped over the lazy dog.";
auto words = split(sentence); // a string[], so also a immutable(char)[][]
auto sentence2 = concat(words);
assert(array(sentence2) == "thequickbrownfoxjumpedoverthelazydog.");

assert(equal(concat(c), c));        // c is a simple range, concat(c) has no effect.
----
BUG: doesn"t play so nice with retro. retro.popBack calls concat.popFront, but it seems to have no effect.
*/
struct Concat(R) if (isRangeOfRanges!R)
{
    R _range;
    alias ElementType!R ET0;
    alias ElementType!ET0 ET1;
    ET0 _subrange, _backSubrange;

    this(R range) {
        _range = range;
        if (!_range.empty) {
            _subrange = _range.front;
            while (_subrange.empty && !_range.empty) {
                _range.popFront;
                if (!_range.empty) _subrange = _range.front;
            }
            static if (isBidirectionalRange!R && isBidirectionalRange!ET0) {
                _backSubrange = _range.back;
                while (_backSubrange.empty && !_range.empty) {
                    _range.popBack;
                    if (!_range.empty) _backSubrange = _range.back;
                }
            }
        }
    }

    bool empty() {
        return _range.empty;
    }

    ET1 front() {
        return _subrange.front;
    }

    @property Concat save() { return this;}

    void popFront() {
        if (!_subrange.empty) _subrange.popFront;

        while (_subrange.empty && !_range.empty) {
            _range.popFront;
            if (!_range.empty) _subrange = _range.front;
        }
    }

    static if (isBidirectionalRange!R && isBidirectionalRange!ET0) {
        ET1 back() {
            return _backSubrange.back;
        }

        void popBack() {
            if (!_backSubrange.empty) _backSubrange.popBack;

            while (_backSubrange.empty && !_range.empty) {
                _range.popBack;
                if (!_range.empty) _backSubrange = _range.back;
            }
        }
    }
}

/// ditto
Concat!R concat(R)(R range) if (isRangeOfRanges!R) {
    return Concat!R(range);
}

/// ditto
R concat(R)(R range) if (isSimpleRange!R) {
    return range;
}

unittest
{
    int[][] r1 = [[0,1,2], [3,4], [5]];
    auto c = concat(r1);
    assert(equal(c, [0,1,2,3,4,5][]));
    assert(equal(retro(c), retro([0,1,2,3,4,5][]))); // bidir range

    assert(equal(concat(c), c));

    auto r2 = [0,1,2,3];
    auto ror = map!"take(repeat(a), a+1)"(r2); // -> [[0], [1,1], [2,2,2], [3,3,3,3]]
    assert(equal(concat(ror), [0,1,1,2,2,2,3,3,3,3][]));

    string sentence = "the quick brown fox jumped over the lazy dog.";
    auto words = split(sentence); // a string[], so also a immutable(char)[][]
    auto sentence2 = concat(words);
    assert(array(sentence2) == "thequickbrownfoxjumpedoverthelazydog.");

    int[][] ee;
    int[] e;
    assert(concat(ee).empty);
    assert(concat(e).empty);
}

/**
Flatten a range of ranges (of ranges, etc.) n levels deep. n==0 does nothing. n == 1 is just concat(range),
n == 2 is concat(concat(range)), etc. The default is to go for the maximum flattening.
Example:
----
int[][] r1 = [[0,1,2], [3,4], [5]];
auto f = flatten(r1);
assert(equal(f, [0,1,2,3,4,5][]));

int[][][] r2 = [r1, [[6]], r1];
auto f2 = flatten!2(r2);
assert(equal(f2, [0,1,2,3,4,5,6,0,1,2,3,4,5][]));
assert(equal(retro(f2), [5,4,3,2,1,0,6,5,4,3,2,1,0][])); // bidir range

auto f3 = flatten!0(r2); // No flattening -> range unchanged.
assert(equal(f3, r2));

auto f4 = flatten(r2); // go for max flattening. Equals to flatten!2(r2)
assert(equal(f2, f4));

auto f5 = flatten!1(r2); // flatten one level
assert(equal(f5, [[0,1,2], [3,4], [5], [6], [0,1,2], [3,4], [5]][]));
assert(equal(retro(f5), [[5], [3,4], [0,1,2], [6], [5], [3,4], [0,1,2]][]));
----
*/
FlattenType!(n,R) flatten(size_t n = size_t.max, R)(R range) if (isForwardRange!R) {
    static if(n > rank!R)
        return wrapCode!(concat, rank!R, R)(range);
    else
        return wrapCode!(concat, n, R)(range);
}

template FlattenType(size_t n,R)
{
    static if (n > rank!R)
        alias FlattenType!(rank!R,R) FlattenType;
    else static if (n == 0)
        alias R FlattenType;
    else static if (n == rank!R)
        alias FlattenType!(n-1, R) FlattenType;
    else
        alias Concat!(FlattenType!(n-1, R)) FlattenType;
}

unittest
{
    auto r1 = [[0,1,2], [3,4], [5]];
    auto f = flatten(r1);
    assert(equal(f, [0,1,2,3,4,5][]));
    int[][] r6 = [[6]];

    auto r2 = [r1, r6, r1];
    auto f2 = flatten!2(r2);
    assert(equal(f2, [0,1,2,3,4,5,6,0,1,2,3,4,5][]));
    assert(equal(retro(f2), [5,4,3,2,1,0,6,5,4,3,2,1,0][])); // bidir range

    auto f3 = flatten!0(r2); // No flattening -> range unchanged.
    assert(equal(f3, r2));

    auto f4 = flatten(r2); // go for max flattening. Equals to flatten!2(r2)
    assert(equal(f2, f4));

    auto f5 = flatten!1(r2); // flatten one level
    assert(equal(f5, [[0,1,2], [3,4], [5], [6], [0,1,2], [3,4], [5]][]));
    assert(equal(retro(f5), [[5], [3,4], [0,1,2], [6], [5], [3,4], [0,1,2]][]));
}

/**
Small helper function: given a variadic list of ranges, truncates them to the shortest range's length.
This will modify the input ranges!
Example:
----
auto r1 = [0,1,2,3];
string s = "abcdefghijk";
truncate(r1, s);
assert(r1.length == s.length);
assert(equal(r1, [0,1,2,3][]));
assert(s == "abcd");
----
BUG:
Does not work since DMD 2.04x, when strings were modified. Maybe by using byCodePoint or somesuch?
*/
void truncate(R...)(ref R r) if (allHaveLength!R && !allAreInfinite!R && allSatisfy!(hasSlicing, R))
{
    auto l = minLength(r);
    foreach(i, elem; r) {
        if (!r[i].empty) r[i] = r[i][0..l];
    }
}


unittest {
    auto r1 = [0,1,2,3];
    auto s = ["a","b","c","d","e","f","g","h","i","j","k"];
    truncate(r1, s);
    assert(r1.length == s.length);
    assert(equal(r1, [0,1,2,3][]));
    assert(s == ["a","b","c","d"]);
}


/**
Emulates the standard Clojure/Python/Ruby function: given a range r,
it will produce an indexed range, with elements tuples(index, element).

If possible, indexed defines back, popBack, length, opIndex and opSlice.
----
auto s = ["a", "b", "c", "d", "e", "f"];
auto e = indexed(s); // (0,"a"), (1,"b"), (2,"c"), (3,"d"), (4, "e"), (5, "f")
assert(e.front == tuple(0, "a"));
assert(e.length == s.length);
e.popFront;
assert(e.front == tuple(1, "b"));
assert(e[3]    == tuple(4, "e")); // opIndex
assert(e.back  == tuple(5, "f")); // back
----
*/
Knit!(Numbers, R) indexed(R)(R range) {
    return knit(numbers(0,int.max,1), range);
}

unittest {
    auto s = ["a", "b", "c", "d", "e", "f"];
    auto e = indexed(s); // (0,"a"), (1,"b"), (2,"c"), (3,"d"), (4, "e"), (5, "f")
    assert(e.front == tuple(0, "a"));
    assert(e.length == s.length);
    e.popFront;
    assert(e.front == tuple(1, "b"));
    assert(e[3]    == tuple(4, "e")); // opIndex
    assert(e.back  == tuple(5, "f")); // back

    int[] empt;
    assert(indexed(empt).empty);
}

/**
A small range to get the numbers _from from _to to (open at to, it's never reached) with _step step.
0-, 1-, 2- and 3-args version exist, see the examples.
Examples:
----
auto n0 = numbers();            // -> 0,1,2,3,4, ... ,int.max
auto n1 = numbers(10);          // -> 0,1,2,3,4,5,6,7,8,9
auto n2 = numbers(5,10);        // -> 5,6,7,8,9
auto n3 = numbers(1,10,3);      // -> 1,4,7
auto n4 = numbers(1,10,100);    // -> 1
auto n5 = numbers(20,10, -1);   // -> 20,19,18,17,16,15,14,13,12,11
auto n6 = numbers(20,10);       // step defaults to 1 -> empty range
assert(n1[3] == 3);             // opIndex
assert(equal(n1[5..10], n2));   // opSlice
assert(equal(retro(n1), [9,8,7,6,5,4,3,2,1,0][])); // It's a bidirectional range
----
*/
struct Numbers {
    int _num, _max, _step;

    this(int to) { _num = 0; _max = to; _step = 1;}
    this(int from, int to) { _num = from; _max = to; _step = 1;}
    this(int from, int to, int step) { _num = from; _max = to; _step = step;}

    bool empty() { return (_step > 0) ? _num >= _max : _num <= _max;}
    int front() {return _num;}
    @property Numbers save() { return this;}
    void popFront() { _num = _num + _step;}
    int back() { return _max-1;}
    void popBack()  { _max = _max - _step;}

    int opIndex(size_t index) {
        if ((_step > 0) && (index*_step + _num >= _max) || (_step < 0) && (index*_step + _num <= _max))
            throw new Exception("Numbers.opIndex: Out of bound with index: " ~ to!string(index));
        return cast(int)(index*_step + _num);
    }

    Numbers opSlice() { return this;}

    Numbers opSlice(size_t index1, size_t index2) {
        if ((_step > 0) && (index1*_step + _num > _max) || (_step < 0) && (index1*_step + _num <= _max))
            throw new Exception("Numbers.opSlice: first index out of bound " ~ to!string(index1*_step) ~ " + " ~ to!string(_num) ~ " >= " ~ to!string(_max));
        if ((_step > 0) && (index2*_step + _num > _max) || (_step < 0) && (index2*_step + _num <= _max))
            throw new Exception("Numbers.opSlice: second index out of bound " ~ to!string(index2*_step) ~ " + " ~ to!string(_num) ~ " >= " ~ to!string(_max));
        return Numbers(index1*_step + _num, index2*_step + _num);
    }

    @property size_t length() { return (this.empty ? 0 : cast(size_t)((_max-_num)/_step));}
}

/// ditto
Numbers numbers(int to = int.max) {
    return Numbers(0, to, 1);
}
/// ditto
Numbers numbers(int from, int to, int step = 1) {
    return Numbers(from, to, step);
}

unittest
{
    auto n0 = numbers();
    assert(equal(take(n0, 5), [0,1,2,3,4][]));

    auto n1 = numbers(10);
    assert(equal(n1, [0,1,2,3,4,5,6,7,8,9][]));
    assert(n1[3] == 3); // opIndex
    assert(equal(retro(n1), [9,8,7,6,5,4,3,2,1,0][])); // retro

    auto n2 = numbers(5,10);
    assert(equal(n2, [5,6,7,8,9][]));
    assert(equal(n1[5..10], n2)); // slicing

    auto n3 = numbers(1,10,3);
    assert(equal(n3, [1,4,7][]));

    auto n4 = numbers(1,10,100);
    assert(equal(n4, [1][]));

    auto n5 = numbers(20,10, -1);
    assert(equal(n5, [20,19,18,17,16,15,14,13,12,11][]));

    auto n6 = numbers(20,10); // step defaults to 1 -> empty range
    assert(n6.empty);
}

/**
A templated struct for a range of numbers. It can be used with std.bigint, for example.
There is no argument-less version: numberz!BigInt() does not exists (as there is no BigInt.max).
----
auto n1 = numberz(BigInt("1000000000000000"), BigInt("2000000000000000"));
    // -> 1000000000000000, 1000000000000001, 1000000000000002, 1000000000000003, ..., 1000000000000010
assert(n1[3] == BigInt("1000000000000003")); // opIndex with standard index
assert(n1[BigInt("500000000000000")] == BigInt("1500000000000000")); // Indexed with BigInt too
assert(n1.length == BigInt("1000000000000000")); // .length returns a BigInt
----
*/
struct Numberz(T) {
    T _num, _max, _step;

    this(T to) { _num = 0; _max = to; _step = 1;}
    this(T from, T to) { _num = from; _max = to; _step = 1;}
    this(T from, T to, T step) { _num = from; _max = to; _step = step;}

    bool empty() { return (_step > 0) ? _num >= _max : _num <= _max;}
    T front() {return _num;}
    @property Numberz save() { return this;}
    void popFront() { _num = _num + _step;}
    T back() { return _max - _step;}
    void popBack()  { _max = _max - _step;}

    static if (!is(T == size_t)) T opIndex(size_t index) { T i = index; return opIndex(i);}

    T opIndex(T index) {
        T i = index*_step + _num;
        if ((i < 0) || (_step > 0) && (i >= _max) || (_step < 0) && (i <= _max))
            throw new Exception("Numberz!" ~ T.stringof ~ ".opIndex: Out of bound with index: " ~ to!string(index));
        return i;
    }

    Numberz!T opSlice() { return this;}

    Numberz!T opSlice(T index1, T index2) {
        T i1 = index1*_step + _num;
        T i2 = index2*_step + _num;
        if ((i1 < 0) || (_step > 0) && (i1 > _max) || (_step < 0) && (i1 < _max))
            throw new Exception("Numberz!" ~ T.stringof ~ ".opSlice: first index out of bound " ~ to!string(i1) ~ " >= " ~ to!string(_max));
        if ((i2 < 0) || (_step > 0) && (i2 > _max) || (_step < 0) && (i2 < _max))
            throw new Exception("Numberz!" ~ T.stringof ~ ".opSlice: second index out of bound " ~ to!string(i2) ~ " >= " ~ to!string(_max));
        return Numberz!T(i1, i2, _step);
    }

    T length() { return (empty ? T.init : (_max-_num)/_step);}
}

/// ditto
Numberz!T numberz(T)(T to) {
    return Numberz!T(cast(T)0, to, cast(T)1);
}

/// ditto
Numberz!T numberz(T)(T from, T to, T step) {
    return Numberz!T(from, to, step);
}

/+
unittest
{
    auto n1 = numberz(BigInt("1000000000000000"), BigInt("2000000000000000"), BigInt("1"));
    // -> 1000000000000000, 1000000000000001, 1000000000000002, 1000000000000003, ..., 1000000000000010
    assert(n1[3] == BigInt("1000000000000003"));
    assert(n1[BigInt("500000000000000")] == BigInt("1500000000000000"));
    assert(n1.length == BigInt("1000000000000000"));
}
+/

/**
Simple range producing all natural numbers, alternating
between positive and negative numbers: 0, 1, -1, 2, -2, 3, -3, ...
*/
struct NaturalNumbers {
    long _num = 0;
    bool _positive = true;
    enum bool empty = false;
    long front() { return _num;}
    @property NaturalNumbers save() { return this;}
    void popFront() {
        if (_num == 0) {
            _num = 1;
            return;
        }
        if (_positive) {
            _num *= -1;
            _positive= false;
        }
        else {
            _num = -_num +1;
            _positive = true;
        }
    }
}

unittest {
    assert(equal(take(NaturalNumbers(), 7), [0,1,-1,2,-2,3,-3][]));
}

/**
An empty range. Its element type is parameterized by T, to enable compatibility
(for ranges which check front's type).

----
auto e = emptyRange!int; //uses the helper function. Otherwise: auto e = EmptyRange!int();
assert(e.empty);
assert(e.length == 0);
assert(asString(e) == "");
assert(is(ElementType!(typeof(e)) == int));
assert(isInputRange!(typeof(e)));
assert(isForwardRange!(typeof(e)));
assert(isBidirectionalRange!(typeof(e)));
assert(isRandomAccessRange!(typeof(e)));
assert(hasLength!(typeof(e)));
assert(hasSlicing!(typeof(e)));
----
*/
struct EmptyRange(T) {
    enum bool empty = true;
    enum size_t length = 0;
    @property EmptyRange save() { return this;}
    void popFront() {throw new Exception("EmptyRange is empty: do not call popFront");}
    T front() {throw new Exception("EmptyRange is empty: do not call front");}
    void popBack() {throw new Exception("EmptyRange is empty: do not call popBack");}
    T back() {throw new Exception("EmptyRange is empty: do not call back");}
    T opIndex(uint index) {throw new Exception("EmptyRange is empty: do not call opIndex");}
    EmptyRange!T opSlice(uint index1, uint index2) {return this;}

    R opCat(R)(R range) if (isForwardRange!R && is(ElementType!R == T)) { return range;}
    R opCat_r(R)(R range) if (isForwardRange!R && is(ElementType!R == T)) { return range;}
}

/// ditto
EmptyRange!T emptyRange(T)() {
    return EmptyRange!T();
}

unittest {
    auto e = emptyRange!int; //uses the helper function. Otherwise: auto e = EmptyRange!int();
    assert(e.empty);
    assert(e.length == 0);
    assert(asString(e) == "");
    assert(is(ElementType!(typeof(e)) == int));

    assert(isInputRange!(typeof(e)));
    assert(isForwardRange!(typeof(e)));
    assert(isBidirectionalRange!(typeof(e)));
    assert(isRandomAccessRange!(typeof(e)));
    assert(hasLength!(typeof(e)));
    assert(hasSlicing!(typeof(e)));
}

/**
A one-element range. This element is defined at creation and will be produced once. The range is then empty.
----
auto e = once(1.1);
assert(e.front == 1.1);
assert(e.length == 1);
assert(asString(e) == "1.1");
e.popFront;
assert(e.empty);
----
*/
struct Once(T) {
    T[] elem;
    this(T value) {elem = [value][];}

    bool empty() { return elem.empty;}
    T front() { return elem.front;}
    @property Once save() { return this;}
    void popFront() { elem.popFront;}
    T back() { return elem.front;}
    void popBack() { elem.popFront;}
    ulong length() { return elem.length;}
    T opIndex(size_t index) { assert(index == 0); return elem[0];}
    void opIndexAssign(T value, size_t index) { assert(index == 0); elem[0] = value;}
    Once!T opSlice() { return this;}
/+    Once!T opSlice(ulong i1, ulong i2) // strange, I had to put ulong to satisfy std.range.ChainImpl
    {
        assert(i1 <= this.length()); // It was originally == 0, but [1..1] seems authorized for arrays. I thought it wasn"t.
        assert(i2 <= this.length());
        auto slice = this;
        if (i1 == i2 && !slice.empty) slice.popFront;
        return slice;
    }+/

    mixin Chainable!();
}

/// ditto
Once!T once(T)(T value) {
    return Once!T(value);
}

unittest {
    auto e = once(1.1);
    assert(e.front == 1.1);
    assert(e.length == 1);
    assert(asString(e) == "1.1");
    e.popFront;
    assert(e.empty);
}

/**
An infinite range giving the digits of pi, in base 10 (as ints).
Example:
----
auto pi = take(piDigits, 10);
assert(equal(pi, [3,1,4,1,5,9,2,6,5,3]));
----
It has a reasonable speed up to a few thousands digits, but slows down sharply afterwards.
On my machine: 1000 digits: 100 ms, 3000 digits: 300 ms, 10_000 digits: 2.4 s, 30_000 digits: 22 s
*/
struct Pi
{
    BigInt q,r,t,i,u,y;
    enum bool empty = false;
    int front() { return to!int(y.toInt);}
    @property Pi save() { return this;}
    void popFront()
    {
        r = BigInt(10)*u*(q*(BigInt(5)*i-BigInt(2)) +r-y*t);
        q = BigInt(10)*q*i*(BigInt(2)*i-BigInt(1));
        t = t*u;
        i = i + BigInt(1);
        u = BigInt(3)*(BigInt(3)*i+BigInt(1))*(BigInt(3)*i+BigInt(2));
        y = (q*(BigInt(27)*i-BigInt(12))+BigInt(5)*r)/(BigInt(5)*t);
    }
}

/// ditto
Pi piDigits()
{
    return Pi(BigInt(1),BigInt(180),BigInt(60),BigInt(2),BigInt(3*7*8),BigInt(3));
}

/**
It's an infinite bidirectional range: a range that has infinitely many values,
but knows its end:

n0 n1 n2 ... (infinitely many values)  ... m2 m1 m0

It's in fact a completly standard infinite bidirectional range, modelized with two (non-bidir) infinite ranges.
*/
struct InfiniteBiDir(R1, R2) if (isForwardRange!R1 && isForwardRange!R1
                                 && isInfinite!R1 && isInfinite!R2
                                 && !isBidirectionalRange!R1 && !isBidirectionalRange!R2
                                 && CompatibleRanges!(R1,R2))
{
    R1 _r1;
    R2 _r2;
    alias CommonElementType!(R1,R2) ET;

    this(R1 r1, R2 r2) { _r1 = r1; _r2 = r2;}

    enum bool empty = false;

    ET front() { return _r1.front;}
    @property InfiniteBiDir save() { return this;}
    void popFront() { _r1.popFront;}
    ET back() { return _r2.front;}
    void popBack() { _r2.popFront;}

    static if (isRandomAccessRange!R1 && isRandomAccessRange!R2)
    {
        ET opIndex(int i)
        {
            return (i>=0) ? _r1[i] : _r2[-i-1];
        }
    }

    typeof(this) opSlice() { return this;}

    // slicing like s[2..10] or even s[2..-2] would be nice, but there is a type pb: the types are different
    // (R1 for the first, InfBiDir!(R1,R2) for the second. And it's not possible to change types on the run-time values of indices.

}

InfiniteBiDir!(R1,R2) infiniteBiDir(R1,R2)(R1 r1, R2 r2)
{
    return InfiniteBiDir!(R1,R2)(r1,r2);
}

/**
Replicates a range n times. back, popBack, length and opIndex will be defined
if the subjacent R permits it.
Example:
----
auto r1 = [0,1,2,3];
auto r2 = replicateRange(r1, 3);
assert(equal(r2, [0,1,2,3,0,1,2,3,0,1,2,3][]));
assert(r2.length == r1.length * 3);
assert(r2[3] == 3);

r2.popFront;
r2.popBack;
assert(equal(r2, [1,2,3,0,1,2,3,0,1,2][])); // You can truncate it at both ends
assert(r2.length == r1.length * 3 - 2); // length update
assert(r2[3] == 0); // Indexing is always 0-based, of course.

assert(replicateRange(r1, 0).empty); // if n == 0, replicateRange is an empty range
assert(equal(replicateRange(r1, 1), r1));
----
*/
struct ReplicateRange(R) if (isForwardRange!R) {
    R _range, _copy, _backCopy; // _backCopy is used only with bidirectional ranges
    uint _times;

    this(R range, uint n) {
        _range = range;
        _copy = range;
        _backCopy = range;
        _times = n;
    }

    bool empty() { return (_times == 0 || _range.empty);}

    @property ReplicateRange save() { return this;}

    void popFront() {
        _copy.popFront;
        if (_copy.empty) {
            _times--;
            _copy = _range;
            if (_times <= 1) { // the two extremities are working on the same sub-range: need to coordinate them
                static if (isBidirectionalRange!R) { // back exists, _copyBack is used
                    _copy = _backCopy;
                }
            }
        }
    }

    ElementType!R front() { return _copy.front;}

    static if (isBidirectionalRange!R) {
        void popBack() {
            if (_times > 1) {
                _backCopy.popBack;
                if (_backCopy.empty) {
                    _times--;
                    _backCopy = _range;
                }
            }
            else { // the two extremities are working on the same sub-range: we need to coordinate them
                _copy.popBack;
                if (_copy.empty) {
                    _times--;
                    _copy = _range;
                }
                _backCopy = _copy;
            }
        }

        ElementType!R back() { return _backCopy.back;}
    }

    static if (hasLength!R) {
        size_t length() {
            switch (_times) {
                case 0:
                    return 0;
                case 1:
                    return _range.length * _times + (_copy.length - _range.length);
                default:
                    return _range.length * _times + (_copy.length - _range.length) + (_backCopy.length - _range.length);
            }
        }
    }

    static if (isRandomAccessRange!R && hasLength!R) { // and hasLength...
        ElementType!R opIndex(size_t index) {
            int i = (index + _range.length - _copy.length) / _range.length;
            if (i == 0) return _copy[index];
            if (i == _times -1) return _backCopy[(index + _range.length - _copy.length) % _range.length];
            return _range[(index + _range.length - _copy.length) % _range.length];
        }
    }
}

/// ditto
auto replicateRange(R)(R range, uint n = 1) if (isForwardRange!R) {
    return ReplicateRange!(R)(range, n);
}

unittest {
    auto r1 = [0,1,2,3];
    auto r2 = replicateRange(r1, 3);
    assert(equal(r2, [0,1,2,3,0,1,2,3,0,1,2,3][]));
    assert(r2.length == r1.length * 3);
    assert(r2[3] == 3);

    r2.popFront;
    r2.popBack;
    assert(equal(r2, [1,2,3,0,1,2,3,0,1,2][])); // You can truncate it at both ends
    assert(r2.length == r1.length * 3 - 2); // length update
    assert(r2[3] == 0); // Indexing is always 0-based, of course.

    assert(replicateRange(r1, 0).empty); // if n == 0, replicateRange is an empty range
    assert(equal(replicateRange(r1, 1), r1));

    auto e = emptyRange!int();
    assert(replicateRange(e, 10).empty); // Replicating an empty range: still just an empty range.
}

/**
Repeat n times each element of a range. If the input is a bidirectional range,
stutter will also be one (defines back and popBack), the same for a random-access range.
Also, if input has a length, stutter will have one.
Example:
----
auto r1 = [0,1,2,3];
string s = "abc";
auto st1 = stutter(r1, 3);
auto st2 = stutter(s, 2);
assert(st1.length == r1.length * 3);
assert(equal(st1, [0,0,0,1,1,1,2,2,2,3,3,3][]));
assert(equal(st2, "aabbcc")); // Works on strings, too.
//
st1.popFront;
st1.popBack;
assert(equal(st1, [0,0,1,1,1,2,2,2,3,3][]));
assert(st1.length == r1.length * 3 - 2);            // length update
assert(equal(retro(st1), [3,3,2,2,2,1,1,1,0,0][])); // Bidirectional range
assert(st1[2] == 1);                                // Random-access range
//
assert(stutter(r1, 0).empty);                       // stutter(_,0) -> empty
auto e = emptyRange!int;
assert(stutter(e, 3).empty);                        // stutter(empty, n) -> empty
assert(equal(stutter(r1,1), r1));                   // stutter(r,1) -> r
----
*/
struct Stutter(R) if (isForwardRange!R){
    R _range;
    uint _times, _frontCount, _backCount;

    this(uint times, R range) {
        _range = range;
        _times = times;
        _frontCount = times;
        _backCount = times;
    }

    bool hasOneElement() {
        return walkLength(_range, 2) == 1;
    }

    bool empty() {
        return (_range.empty || _frontCount == 0 || _backCount == 0); // If _count is zero at creation -> empty range.
                                                      // Else it will become zero once _range is empty.
    }

    @property Stutter save() { return this;}

    void popFront() {
        if (_frontCount <= 1) {
            if (!_range.empty) _range.popFront;
            // One-element -> 0 element:
            _frontCount = _range.empty ? 0 : _times;
            if (hasOneElement()) _frontCount = _backCount;
        }
        else {
           _frontCount--;
        }
    }

    ElementType!R front() {
        return _range.front;
    }

    static if (hasLength!R) {
        size_t length() {
            return   _range.length * _times
                   - (_times - _frontCount)
                   - (_times - _backCount);
        }
    }

    static if (isBidirectionalRange!R) {
        void popBack() {
            if (_backCount <= 1) {
                if (!_range.empty) _range.popBack;
                // One-element -> 0 element:
                _backCount = _range.empty ? 0 : _times;
                if (hasOneElement()) _backCount = _frontCount;
            }
            else {
                _backCount--;
            }
        }

        ElementType!R back() {
            return _range.back;
        }
    }

    static if (isRandomAccessRange!R) {
        ElementType!R opIndex(size_t index) {
            size_t idx = (index + _times - _frontCount);
            static if (hasLength!R) {
                if (idx > this.length +1) {
                    throw new Exception("stutter.opIndex: Out of range. index: " ~ to!string(idx) ~ " max: " ~ to!string(this.length +1));
                }
            }
            return _range[idx / _times];
        }
    }
}

/// ditto
Stutter!(R) stutter(R)(uint n, R range)
{
    return Stutter!(R)(n, range);
}

/**
Another version, based on flatMap.
----
flatMap!(Format!("array(replicate(%s,a))", n))(r);
----
It's a one-liner, but it's a forward range, no more (no opIndex, back, etc)
*/
Concat!(Map!(unaryFun!(Format!("array(replicate(%s,a))", n)), R)) stutter2(size_t n, R)(R r) if (isForwardRange!R)
{
    return flatMap!(Format!("array(replicate(%s,a))", n))(r);
}

unittest {
    auto r1 = [0,1,2,3];
    string s = "abc";
    auto st1 = stutter(3, r1);
    auto st2 = stutter(2, s);
    assert(st1.length == r1.length * 3);
    assert(equal(st1, [0,0,0,1,1,1,2,2,2,3,3,3][]));
    assert(equal(st2, "aabbcc")); // Works on strings, too.

    st1.popFront;
    st1.popBack;
    assert(equal(st1, [0,0,1,1,1,2,2,2,3,3][]));
    assert(st1.length == r1.length * 3 - 2); // length update
    assert(equal(retro(st1), [3,3,2,2,2,1,1,1,0,0][])); // Bidirectional range
    assert(st1[2] == 1); // Random-access range

    assert(stutter(0, r1).empty); // stutter(_,0) -> empty
    int[] e;
    assert(stutter(3, e).empty);
    assert(equal(stutter(1, r1), r1)); // stutter(r,1) -> r
}

/**
A forward range which alternates between input's two extremities. It's a kind of dual to std.range.radial.
Example:
----
auto r1 = [0,1,2,3,4,5,6];
auto ext = extremities(r1);
assert(ext.length == r1.length); // length is defined
assert(equal(ext, [0,6,1,5,2,4,3][]));
assert(extremities(emptyRange!int).empty); // extremities on an empty range -> empty
----
*/
struct Extremities(R) if (isBidirectionalRange!R) {
    R _range;
    uint _state;

    this(R range) {
        _range = range;
        _state = 0;
    }

    bool empty() {
        return _range.empty;
    }

    ElementType!R front() {
        return _state == 0 ? _range.front : _range.back;
    }

    @property Extremities save() { return this;}

    void popFront() {
        if (_state == 0) {
            _range.popFront;
        }
        else {
            _range.popBack;
        }
        _state = 1 - _state;
    }

    static if (hasLength!R) {
        size_t length() {
            return _range.length;
        }
    }
}

/// ditto
Extremities!R extremities(R)(R range) {
    return Extremities!(R)(range);
}

unittest {
    auto r1 = [0,1,2,3,4,5,6];
    auto ext = extremities(r1);
    assert(ext.length == r1.length); // length is defined
    assert(equal(ext, [0,6,1,5,2,4,3][]));
    assert(equal(extremities(r1[0..1]), r1[0..1])); // One element range -> One element range
    int[] e;
    assert(extremities(e).empty); // extremities on an empty range -> empty
}


/**
Iterate on a bidirectional range by going back and forth between its extremities.
Example:
----
auto r = [0,1,2,3];
auto b = bounce(r);
assert(equal(take(b, 10), [0,1,2,3,2,1,0,1,2,3][]));

auto r2 = [1];
assert(equal(take(bounce(r2), 10), replicate(10, 1))); // 1,1,1,1,...
----
*/
Cycle!(Chain!(R, Retro!R)) bounce(R)(R range) if (isBidirectionalRange!R)
{
    auto r = range;
    if (!r.empty) r.popFront;
    if (!r.empty) r.popBack;
    return cycle(chain(range, retro(r)));
}

unittest
{
    auto r = [0,1,2,3];
    auto b = bounce(r);
    assert(equal(take(b, 10), [0,1,2,3,2,1,0,1,2,3][]));

    auto r2 = [1];
    assert(equal(take(bounce(r2), 10), replicate(1,10)));
}

/**
Produces a range with elements of r1 without those of r2. Equivalent to Haskell (\\).
By default, each element of r2 is used only once. With the boolean option cyclic set to true,
you get without(r1, cycle(r2)) and all occurences of an element of r2 in r1 are dropped.
Example:
----
auto r1 = [0,1,2,3,4,5,6,2,3,4];

without(r1, [2,3,4][]);         // [0,1,5,6,2,3,4][] getting rid of 2,3,4. Those at the end are still there
without(r1, [2,3,4,2,3][]);     // [0,1,5,6,4][] 2,3 at the end are eliminated
without(r1, [2,3,4][], true);   // [0,1,5,6][] eliminate all 2, 3 and 4 from r1.
without("banana", "a", true);   // "bnn"
without(r1, numbers(), true);   // (int[]).init (empty range) all are numbers eliminated from r1

r1.without([2,3,4][]);          // For arrays, you can also use an infix syntax
"banana".without("a", true);
----
*/
struct Without(R1, R2)
{
    R1 _range1;
    R2 _range2;
    bool _cyclic;

    this(R1 range1, R2 range2, bool cyclic = false) {
        _range1 = range1;
        _range2 = range2;
        _cyclic = cyclic;
        while (!_range1.empty && !_range2.empty && isOneOf!(_range2)(_range1.front)) {
            _range1.popFront;
            if (!_cyclic) _range2.popFront;
        }
    }

    bool empty() { return _range1.empty;}

    ElementType!R1 front() { return _range1.front;}

    @property Without save() { return this;}

    void popFront() {
        _range1.popFront;
        while (!_range1.empty && !_range2.empty && isOneOf!(_range2)(_range1.front)) {
            _range1.popFront;
            if (!_cyclic) _range2.popFront;
        }
    }
}

/// ditto
Without!(R1,R2) without(R1, R2)(R1 range1, R2 range2, bool cyclic = false) {
    return Without!(R1,R2)(range1, range2, cyclic);
}

unittest
{
    auto r1 = [0,1,2,3,4,5,6,2,3,4];

    assert(equal(without(r1, [2,3,4][]),[0,1,5,6,2,3,4][])); // getting rid of 2,3,4. Those at the end are still there
    assert(equal(without(r1, [2,3,4,2,3][]),[0,1,5,6,4][])); // 2,3 at the end are eliminated
    assert(equal(without(r1, [2,3,4][], true),[0,1,5,6][])); // eliminate all 2, 3 and 4 from r1.
    assert(equal(without("banana", "a", true), "bnn"));
    assert(without(r1, numbers(), true).empty);

    int[] e;
    assert(equal(without(r1, e), r1)); // eliminating nothing -> get r1 back
    assert(without(e, [2,3,4][]).empty); // eminating something from an empty range -> get an empty range
}


/**
Helper struct to transform a range into a set. Each value is memoized when first output
and then filtered. AsSet has no way to know if all values have been created, so on an infinite range
it may never stop, looking for a nth new value which will never come. AsSet does know
about std.range periodic ranges (Cycle and Repeat) and extract the internal value.
Example:
----
asSet([0,1,2,2,3,3,4,5,5,6,9,1,2,4,9][]); // 0,1,2,3,4,5,6,9, OK.
asSet(cycle([4,5,6][])); // 4,5,6
----
*/
struct AsSet(R) if (isForwardRange!R) {
    R _range;
    bool[ElementType!R] elements;

    this(R range) { _range = range;}
    bool empty() {return _range.empty;}
    @property AsSet save() { return this;}
    void popFront() { while(!_range.empty && (_range.front in elements) ) _range.popFront;}

    ElementType!R front() {
        auto f = _range.front;
        elements[f] = true;
        return f;
    }
}

/// ditto
struct AsSet(R : Cycle!U, U)
{
    bool[ElementType!U] elements; // Necessary, as the original range may have repeated values
    U _range;

    this(R range) { _range = range._original;}
    bool empty() {return _range.empty;}
    @property AsSet save() { return this;}
    void popFront() {
        _range.popFront;
        while(!_range.empty && (_range.front in elements)) _range.popFront;
    }

    ElementType!R front() {
        auto f = _range.front;
        elements[f] = true;
        return f;
    }
}

/// ditto
struct AsSet(R : Repeat!U, U)
{
    U[] _range;

    this(R range) { if (!range.empty) _range = [range.front][];} // or else range is an empty Repeat. I don"t think that's even possible.
    bool empty() {return _range.empty;}
    @property AsSet save() { return this;}
    void popFront() { _range.popFront;}
    ElementType!R front() { return _range.front;}
}

/// ditto
AsSet!R asSet(R)(R range)
{
    return AsSet!(R)(range);
}

unittest {
    assert(equal(asSet([0,0,1,2,2,3,3,4,5,5,6,9,1,2,4,9][]), [0,1,2,3,4,5,6,9][]));
    assert(equal(asSet(take(cycle([4,5,6][]), 1000)), [4,5,6][]));
    assert(equal(asSet(cycle([4,5,6][])), [4,5,6][]));
    assert(equal(asSet(cycle([4,5,6,5][])), [4,5,6][]));
    assert(equal(asSet(repeat(4)), [4][]));
    int[] e;
    assert(asSet(e).empty);
}

/+
/**
Calculates the smallest length on a variadic list of ranges. Any range not defining
length is skipped.
Usage:
----
auto r1 = [0,1,2,3,4];
string s = "abc";
auto c = cycle([0,1,2,3]);
auto l = smallestLength(r1,s,c);
assert(l == s.length); // c doesn"t count, it's infinite.
----
*/
size_t smallestLength(R, Rest...)(R range0, Rest rest) {
    return smallestLengthImpl(size_t.max, range0, rest);
}

size_t smallestLengthImpl(R, Rest...)(size_t currentLength, R range0, Rest rest) {
    static if (hasLength!R) {
        size_t r0Length = range0.length;
        if (r0Length < currentLength) currentLength = r0Length;
    }
    static if (Rest.length > 0) {
        return smallestLengthImpl(currentLength, rest);
    }
    else {
        return currentLength;
    }
}

unittest {
    auto r1 = [0,1,2,3,4];
    string s = "abc";
    auto c = cycle([0,1,2,3][]);
    auto l = smallestLength(r1,s,c);
    assert(l == s.length); // c doesn"t count, it's infinite.
}
+/

/**
Simple wrapper range to cache the front and back elements of another range.
*/
struct Cache(R) if (isForwardRange!R)
{
    R _input;
    ElementType!R _front, _back;

    this(R input) {
        _input = input;
        if (!_input.empty) _front = _input.front;
        static if (isBidirectionalRange!R)
            if (!_input.empty) _back = _input.back;
    }

    bool empty() { return _input.empty;}
    ElementType!R front() { return _front;}
    @property Cache save() { return this;}
    void popFront() { _input.popFront; if (!_input.empty) _front = _input.front;}
    static if (isBidirectionalRange!R) {
        ElementType!R back() { return _back;}
        void popBack() { _input.popBack; if (!_input.empty) _back = _input.back;}
    }

    static if (hasLength!R)
        size_t length() { return _input.length;}
}

/// ditto
Cache!R cache(R)(R r) if (isForwardRange!R) {
    return Cache!(R)(r);
}

/**
To iterate on range using a function with side-effects. It doesn"t use the return values,
so it acts only through fun's side-effects. Mainly used to print a range.
----
auto r1 = [0,1,2,3,4];
forEach!(write)(r1); // writes "01234"
int sum;
forEach!((int a){sum += a;})(r1);
assert(sum == reduce!"a+b"(r1)); // sum contains 0+1+2+3+4
----
*/
void forEach(alias fun, R)(R range) if (isInputRange!R) {
    alias unaryFun!fun func;
    foreach(ref elem; range) func(elem);
}

unittest {
    auto r1 = [0,1,2,3,4];
    int sum;
    forEach!((int a){sum += a;})(r1);
    assert(sum == reduce!"a+b"(r1)); // sum now contains 0+1+2+3+4
}

/**
Greedily iterates on range and returns a string with all range elements
separated by sep. An overload exists, with three string parameters controlling
the beginning of the string, the separator and the end.
Example:
----
auto r1 = [0,1,2,3];
string r2 = "abcdef";
assert(asString(r1) == "0123");
assert(asString(r2) == r2);
assert(asString(r2, ",") == "a,b,c,d,e,f");
assert(asString(r2, "[", "-", "]") == "[a-b-c-d-e-f]");
----
*/
string asString(R)(R range, string sep = "") if (isInputRange!R) {
    if (range.empty) {
        return "";
    }
    else {
        string res;
        foreach(elem; range) res ~= to!string(elem) ~ sep;
        popBackN(res, sep.length);
        return res; // getting rid of the last sep
//        return reduce!((a,b){ return a ~ sep ~ b;})(map!"to!string(a)"(range));
    }
}

/// ditto
string asString(R)(R range, string pre, string sep, string post) if (isInputRange!R) {
    if (range.empty) {
        return pre ~ post;
    }
    else {
        string res = pre;
        foreach(elem; range) res ~= to!string(elem) ~ sep;
        popBackN(res, sep.length); // getting rid of the last sep
        return res ~ post;
    }
}

unittest {
    auto r1 = [0,1,2,3];
    string r2 = "abcdef";
    double[] r3;
    assert(asString(r1) == "0123");
    assert(asString(r2) == r2);
    assert(asString(r3) == "");
    assert(asString(r2, ",") == "a,b,c,d,e,f");
    assert(asString(r2, "[", "-", "]") == "[a-b-c-d-e-f]");
    assert(asString("", "[", "-", "]") == "[]");
    assert(asString("a", "[", "-", "]") == "[a]");
}

/**
Small utility function to print a range. Mainly used for debugging/testing purposes.
*/
void wr(R)(R range, string sep = " ") if (isInputRange!R && !isRangeOfRanges!R) {
    writeln((ElementType!(typeof(range))).stringof, ": ", asString(range, sep));
}

/// ditto
void wr(R)(R range, string pre, string sep, string post) if (isInputRange!R && !isRangeOfRanges!R) {
    writeln((ElementType!(typeof(range))).stringof, ": ", asString(range, pre, sep, post));
}

/// ditto
void wr(R)(R range, string sep = " ") if (isRangeOfRanges!R) {
    writeln((ElementType!(typeof(range))).stringof, ":");
    foreach(elem; range) wr(elem, sep);
}

/**
A template to mixin to get some catenation operations defined on a range, based
on std.range.chain. If r1 is a range with mixin(Chainable!()), r2 a range with
the same element type, and e an element, you can do:
----
r1 ~ r2; // Concatenation on the right.
e[] ~ r1;// Concatenation on the left with an array of elements.
r1 ~ e;  // concatenation on the right with a new element.
e ~ r1;  // concatenation on the left with a new element.
----
What you don"t get is:
----
r2 ~ r1; // No, r2 must define opCat. A templated opCat_r does not work if r1 and r2 both define it and opCat.
----
Note: it detects Chain!R and reacts accordingly. That is, it does not build Chain!(R, Chain!(U)), but Chain!(R,U).
Note: to be really interesting, it needs some modifications of std.range.Chain, to give it opCat capabilities.
*/
template Chainable() /+if (isInputRange!T)+/ {
    alias ElementType!(typeof(this)) ETthis;

    // Concat to the right with another range.
    Chain!(typeof(this), R) opCat(R)(R r) if (!is(ETthis == R) && isInputRange!R && !is(R.RvalueElementType) && is(ETthis == ElementType!R)) {
        return chain(this, r);
    }

    // Concat to the right with a chain.
    Chain!(typeof(this), U) opCat(U...)(ChainImpl!U r) if (is(ETthis == ElementType!(ChainImpl!U))) {
        return chain(this, r._input.expand);
    }
    // Concat to the left with an array
    auto opCat_r(ETthis[] t) {
        return chain(t, this);
    }
    // Concat to the right with an element
    Chain!(typeof(this), R[]) opCat(R)(R e) if (is(ETthis == R)) {
        return chain(this, [e][]);
    }
    // Concat to the left with an element
    auto opCat_r(ETthis e) {
        return chain([e][], this);
    }
}

///
T[] append(T,E)(T[] array, E elem) if (isImplicitlyConvertibleTo!(E,T))
{
    return array ~ elem;
}

///
T[] prepend(T,E)(T[] array, E elem) if (isImplicitlyConvertibleTo!(E,T))
{
    return elem ~ array;
}

///
auto distribute(alias operation = tuple, R1, R2)(R1 r1, R2 r2) if (isForwardRange!R1 && isForwardRange!R2)
{
    return tmap!operation(combinations(r1,r2));
}

///
auto mapFunRange(R, E)(R rangeOfFuns, E elem) if (isForwardRange!R && is(ParameterTypeTuple!(ElementType!R) == TypeTuple!E))
{
    return tmap!("a(b)")(rangeOfFuns, repeat(elem));
}

/**
A sort-of extension of standard ranges that remembers the previous values output through
front and back and can deliver them anew. The front can go back with retreat and the back
can "go forward" with advance. Use asNew/backAsNew to see if you can still retreat/advance.
BUG: doesn"t quite work. I"m getting fed up with this: too many internal states to consider. I should
tackle this anew.
*/
struct Store(R) if (isInputRange!R)
{
    R _range;
    ElementType!R[] store;
    int index;
    // For Bidirectional ranges only:
    ElementType!R[] backStore;
    int backIndex;

    this(R range) { _range = range;}

    static if (isInfinite!R)
        enum bool empty = false;
    else
        bool empty() { return _range.empty && (index == store.length && backIndex == backStore.length);}

    ElementType!R front()
    {
        if (usingStore)
        {
            return store[index];
        }
        else
        {
            return (exhausted) ? backStore.front : _range.front;
        }
    }

    @property Store save() { return this;}

    void popFront()
    {
        if (usingStore)
        {
            if (index == store.length) // "empty store". If we are using popFront, it means Store is not empty. So backStore is not empty.
            {
                store ~= backStore.back; // transfer one element from backStore to store.
                backStore.popBack;
                ++index;
                if (backIndex == backStore.length -1) --backIndex;
            }
            else
            {
                ++index;
            }
        }
        else
        {
            store ~= _range.front;
            ++index;
            _range.popFront;
        }
    }

    bool asNew() { return (index == 0 && store.length == 0) || index < 0;}
    bool usingStore() { return 0 <= index && index < store.length;}
    void retreat() { --index;}

    bool usingBackStore() { return 0 <= backIndex && backIndex < backStore.length;}
    bool backAsNew() { return (backIndex == 0 && backStore.length == 0) || backIndex < 0;}
    void advance() { backIndex--;} // backRetreat?
    bool exhausted() { return _range.empty;}

    static if (hasLength!R)
        size_t length() { return _range.length + (store.length - index) + (backStore.length - backIndex);}

    static if (isBidirectionalRange!R) {

// Mmm, what if I call back, popBack and back again? Same value?
        ElementType!R back() {
            if (usingBackStore)
            {
                return backStore[backIndex];
            }
            else
            {
                return (exhausted) ? store.back : _range.back;
            }
        }

        void popBack()
        {
            if (usingBackStore)
            {
                if (backIndex == backStore.length - 1) // relay passing. Take one element from store, give it to backStore
                {
                    backStore ~= store.back;
                    store.popBack;
                    ++backIndex;
                    if (index == store.length) --index; // invariant conservation
                }
                else
                {
                    ++backIndex;
                }
            }
            else
            {
                backStore ~= _range.back;
                backIndex++;
                _range.popBack;
            }
        }

    }

    static if (isRandomAccessRange!R) {
        ElementType!R opIndex(size_t i) {
            return (usingStore) ? store[index+i] : _range[i];
        }

        static if (hasAssignableElements!R) {
            void opIndexAssign(ElementType!R e, size_t i) {
                if (usingStore) {
                    store[index+i] = e;
                }
                else {
                    _range[i] = e;
                }
            }
        }
    }

}

Store!R store(R)(R range) if (isInputRange!R)
{
    return Store!R(range);
}
