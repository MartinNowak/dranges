/**
This module is a grab-bag of templates used by the other modules, mostly
as guards by other templates (isRangeOfRanges, isTupleRange, ...).
*/
module dranges.traits2;

import std.contracts;
import std.conv;
import std.functional;
import std.metastrings;
import std.range;
import std.stdio;
import std.traits;
import std.typecons;
import std.typetuple;

/**
Returns true iff F is a function type (a function, a delegate or something definining opCall as a function).
*/
template isFunctionType(F) {
    enum bool isFunctionType = (is(F == function) || is(F == delegate) || __traits(hasMember, F, "opCall"));
}

/**
Is true iff fun is a function/delegate or defines opCall.
*/
template isFunction(alias fun) {
    static if (is(typeof(fun)))
        enum bool isFunction = isFunctionType!(typeof(fun));
    else
        enum bool isFunction = false;
}

template isFunction(F)
{
    enum bool isFunction = (is(F == function) || is(F == delegate) || __traits(hasMember, F, "opCall"));
}

unittest
{
    int a;
    int foo() { return 0;}
    int bar(int a, int b) { return 0;}
    struct F { int opCall() { return 0;}}
    assert(!isFunction!a);
    assert(isFunction!foo);
    assert(isFunction!bar);
    F f;
    assert(isFunction!f);
}

// doesn't work.
template isVariadic(alias fun) {
    enum bool isVariadic = isFunction!fun && !is(ParameterTypeTuple!fun);
}


/**
Extract the element types from a variadic list of ranges.
*/
template ElementTypes(R, Rest...) {
    static if (Rest.length > 0) {
        alias TypeTuple!(ElementType!R, ElementTypes!(Rest)) ElementTypes;
    }
    else {
        alias ElementType!R ElementTypes;
    }
}

unittest {
    auto r1 = [0,1];
    auto r2 = [2.0, 3.1];
    auto r3 = cycle("abc");
    assert(is(ElementTypes!(typeof(r1), typeof(r2), typeof(r3)) == TypeTuple!(int, double, dchar)), "ElementTypes!R test.");
}


/**
Given a variadic list of ranges, find the common type to all their element types.
If no common type is found, CommonElementType is void.
*/
template CommonElementType(R...) if (allSatisfy!(isInputRange, R)) {
    alias CommonType!(staticMap!(ElementType, R)) CommonElementType;
}

unittest
{
    auto r1 = [0,1,2,3,4];
    auto r2 = [0.0,1.0,2.0];
    auto s = cast(dchar[])"abc";
    assert(is(CommonElementType!(typeof(r1), typeof(r2)) == double));
    assert(is(CommonElementType!(typeof(r1), typeof(s)) == uint)); // because dchar is implictly converted into an uint
    assert(is(CommonElementType!(typeof(r1), typeof(r2), typeof(s)) == double));
    assert(isImplicitlyConvertible!(immutable(char), double));
}

/**
Is true iff the ranges R... have a common element type.
*/
template CompatibleRanges(R...) {
    enum bool CompatibleRanges = !is(CommonElementType!R == void);
}

unittest
{
    auto r1 = [0,1,2,3,4];
    auto r2 = [0.0,1.0,2.0];
    string s = "abc";
    auto ss = ["abc", "def", "fgh"];
    int[][] r3 = [[0,1], [2,3]];
    assert(CompatibleRanges!(typeof(r1), typeof(r2), typeof(s)));
    assert(!CompatibleRanges!(typeof(r1), typeof(ss)));
    assert(!CompatibleRanges!(typeof(r1), typeof(r3)));
}

/**
Is true iff all the R either have a length or are infinite.
TODO: replace it.
*/
template allHaveLength(R, Rest...) {
    static if (Rest.length > 0) {
        enum bool allHaveLength = (hasLength!R || isInfinite!R) && allHaveLength!Rest;
    }
    else {
        enum bool allHaveLength = (hasLength!R || isInfinite!R);
    }
}

/**
Could be replaced by allSatisfy!(isInfinite, R)?
TODO: replace it.
*/
template allAreInfinite(R, Rest...) {
    static if (Rest.length > 0) {
        enum bool allAreInfinite = isInfinite!R && allAreInfinite!Rest;
    }
    else {
        enum bool allAreInfinite = isInfinite!R;
    }
}

/**
Is true iff R is a tuple-producing range (ie its elements are std.typecons.tuples).
*/
template isTupleRange(R)
{
    enum bool isTupleRange = isForwardRange!R && is(ElementType!R.Types);
}

/**
Is true if R is a range of ranges: a (forward) range whose elements
are themselves forward ranges.
*/
template isRangeOfRanges(R) {
    enum bool isRangeOfRanges = isForwardRange!R && isForwardRange!(ElementType!R);
}

/**
Is true if R is a simple range: a (forward) range whose elements are not (forward) ranges.
*/
template isSimpleRange(R) {
    enum bool isSimpleRange = isForwardRange!R && !isForwardRange!(ElementType!R);
}

/**
Is true iff R is an array of arrays (ie T[][] for some T).
*/
template isArrayOfArrays(R) {
    enum bool isArrayOfArrays = isArray!R && isArray!(ElementType!(R));
}

/**
Is true iff R is a simple array T[] and not deeper (no U such that
U[][] == T[] == R).
*/
template isSimpleArray(R) {
    enum bool isSimpleArray = isArray!R && !isArray!(ElementType!(R));
}

/**
Alternate template to std.range.hasLength, as hasLength doesn't work
if R has length defined inside a static if.
*/
template hasLength2(R) {
    enum bool hasLength2 = __traits(compiles, R.length);
}

unittest
{
    assert(hasLength!(int[]));
    assert(hasLength!(int[3]));
    assert(hasLength!(string));
    assert(!hasLength!(int));
}

/**
Gives the rank of an array or a range. For a simple (flat, non-nested) range
of array, rank is 1. A range of ranges is depth 2 and so on...
A non-range is considered to be an element and is rank 0.
Example:
----
int[] r1 = [0,1,2,3];
int[][] r2 = [r1, [4], r1];
int[][][] r3 = [r2, [[5,6]], r2];
assert(rank!(typeof(r1)) == 1); // No nesting, flat range
assert(rank!(typeof(r2)) == 2); // range of ranges
assert(rank!(typeof(r3)) == 3); // range of ranges of ranges
----
*/
template rank(R) if (isSimpleRange!R)
{
    enum size_t rank = 1;
}

/// ditto
template rank(R) if (isRangeOfRanges!R)
{
    enum size_t rank = 1 + rank!(ElementType!R);
}

template rank(R) if (!isForwardRange!R)
{
    enum size_t rank = 0;
}

unittest {
    int[] r1 = [0,1,2,3][];
    int[][] r2 = [r1, [4][], r1];
    int[][][] r3 = [r2, [[5,6][]][], r2];
    assert(rank!(typeof(r1)) == 1); // No nesting, flat range
    assert(rank!(typeof(r2)) == 2); // range of ranges
    assert(rank!(typeof(r3)) == 3); // range of ranges of ranges
}


/**
alias itself to the innermost type of a nested array.
For example BaseElementType!(int[][][]) is int, in constrast with std.range.ElementType!(R) which would become int[][].
*/
template BaseElementType(R) if(isSimpleRange!(R)) {
    alias ElementType!(R) BaseElementType;
}

/// ditto
template BaseElementType(R) if(isRangeOfRanges!(R)) {
    alias BaseElementType!(ElementType!(R)) BaseElementType;
}

unittest {
    int[][] arr = [[0,1][], [2,3][]];
    auto arr2 = [arr, [[4][]][], arr][];
    assert(is(BaseElementType!(typeof(arr)) == int), "BaseElementType test int[][] array.");
    assert(is(BaseElementType!(typeof(arr2)) == int), "BaseElementType test nested arrays.");
    assert(is(BaseElementType!(int[]) == int));
}

/**
Alias itself to the inner array type of a nested array, up to some maximum depth.
If no maximum depth is given, it goes down to the innermost type, as BaseElementType.
Example:
----
int[][][][] array4;
BaseElementTypeUpTo!(typeof(array4), 0) == int[][][][]
BaseElementTypeUpTo!(typeof(array4), 1) == int[][][]
BaseElementTypeUpTo!(typeof(array4), 2) == int[][]
BaseElementTypeUpTo!(typeof(array4), 3) == int[]
BaseElementTypeUpTo!(typeof(array4))    == int
----
*/
template BaseElementTypeUpTo(R, int maxDepth : 0) if (isForwardRange!R) {
    alias R BaseElementTypeUpTo;
}

/// ditto
template BaseElementTypeUpTo(R, int maxDepth = int.max) if (isSimpleRange!(R)) {
    alias ElementType!(R) BaseElementTypeUpTo;
}

/// ditto
template BaseElementTypeUpTo(R, int maxDepth = int.max) if(isRangeOfRanges!(R)) {
    alias BaseElementTypeUpTo!(ElementType!(R), maxDepth-1) BaseElementTypeUpTo;
}

unittest {
    int[][][][] array4;
    assert(is(BaseElementTypeUpTo!(typeof(array4), 0) == int[][][][]));
    assert(is(BaseElementTypeUpTo!(typeof(array4), 1) == int[][][]  ));
    assert(is(BaseElementTypeUpTo!(typeof(array4), 2) == int[][]    ));
    assert(is(BaseElementTypeUpTo!(typeof(array4), 3) == int[]      ));
    assert(is(BaseElementTypeUpTo!(typeof(array4), 4) == int        ));
    assert(is(BaseElementTypeUpTo!(typeof(array4))    == int        ));
}


/**
The complementary template of std.traits.allSatisfy: is true
iff some types in R satisfy predicate pred.
*/
template someSatisfy(alias pred, R...) {
    static if (R.length == 0)
        enum bool someSatisfy = false;
    else
        enum bool someSatisfy = pred!(R[0]) || someSatisfy!(pred, R[1..$]);
}

unittest
{
    static assert(someSatisfy!(isIntegral, int, double));
    static assert(someSatisfy!(isIntegral, int, long));
    static assert(someSatisfy!(hasLength2, int[], int[2])); // does not work with std.range.hasLength
    static assert(someSatisfy!(hasLength2, int, string)); // strings have a length
    static assert(!someSatisfy!(hasLength2, int, real));
}

/**
The complementary template of std.traits.Unsigned. Gives the signed
counterpart of integral types (byte, short, int, long, char, dchar, wchar).
Does nothing with floating-point types, as these are already signed.
Completly based on std.traits.Unsigned.
Example:
----
alias TypeTuple!(int, uint, ulong, double, ushort) Test;
assert(is(staticMap!(Signed, Test) == TypeTuple!(int,int,long,double,short)));
----
*/
template Signed(T) {
    static if (is(T == byte)) alias byte Signed;
    else static if (is(T == short)) alias short Signed;
    else static if (is(T == int)) alias int Signed;
    else static if (is(T == long)) alias long Signed;
    else static if (is(T == ubyte)) alias byte Signed;
    else static if (is(T == ushort)) alias short Signed;
    else static if (is(T == uint)) alias int Signed;
    else static if (is(T == ulong)) alias long Signed;
    else static if (is(T == char)) alias char Signed;
    else static if (is(T == wchar)) alias wchar Signed;
    else static if (is(T == dchar)) alias dchar Signed;
    else static if (is(T == float)) alias float Signed;
    else static if (is(T == double)) alias double Signed;
    else static if (is(T == real)) alias real Signed;
    else static if(is(T == enum))
    {
        static if (T.sizeof == 1) alias byte Signed;
        else static if (T.sizeof == 2) alias short Signed;
        else static if (T.sizeof == 4) alias int Signed;
        else static if (T.sizeof == 8) alias long Signed;
        else static assert(false, "Type " ~ T.stringof
                           ~ " does not have an Signed counterpart");
    }
    else static if (is(T == immutable))
    {
        alias immutable(Signed!(Unqual!T)) Signed;
    }
    else static if (is(T == const))
    {
        alias const(Signed!(Unqual!T)) Signed;
    }
    else static assert(false, "Type " ~ T.stringof
                       ~ " does not have an Signed counterpart");
}

unittest
{
    alias TypeTuple!(int, uint, ulong, double, ushort) Test;
    assert(is(staticMap!(Signed, Test) == TypeTuple!(int,int,long,double,short)));
}

///
template isInstanceOfTemplate(T, alias templ)
{
    static if (T.stringof.length >= __traits(identifier, templ).length && T.stringof[0..__traits(identifier, templ).length] == __traits(identifier, templ))
        enum bool isInstanceOfTemplate = true;
    else
        enum bool isInstanceOfTemplate = false;
}

///
template isTuple(T)
{
    enum bool isTuple = isInstanceOf!(T.init, Tuple);
}

