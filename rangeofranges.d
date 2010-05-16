/**
To Be Documented.

This module contains functions creating or acting upon range of ranges (of whatever rank): mapping them, transforming
a linear range into a range of ranges, zipping them, creating them by tensorial product, etc.
*/
module dranges.rangeofranges;

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

/**
Maps fun at depth downToRank inside a range of ranges.
*/
typeof(unaryFun!fun(E.init)) depthMap(alias fun, int downToRank = 0, E)(E elem) if (downToRank >= rank!E) // Elem can very well be a range
{
    return unaryFun!fun(elem);
}

/// ditto
Map!(unaryFun!(depthMap!(fun, downToRank, ElementType!R)),R) depthMap(alias fun, int downToRank = 0, R)(R range) if (0<= downToRank && downToRank < rank!R)
{
    return map!(depthMap!(fun, downToRank, ElementType!R))(range);
}

/**
Maps fun from the bottow (down to rank downToRank) up, calling fun at each level on the result of the previous (innermost) level.
*/
RecursiveMapType!(fun, downToRank, R) recursiveMap(alias fun, int downToRank = 1, R)(R range)
{
    static if (downToRank >= rank!R)
        return unaryFun!fun(range);
    else if (0<= downToRank && downToRank < rank!R)
        return fun(map!(recursiveMap!(fun, downToRank, ElementType!R))(range));
}

template RecursiveMapType(alias fun, int downToRank, R) if (isForwardRange!R)
{
    static if (downToRank >= rank!R)
        alias typeof(unaryFun!fun(R.init)) RecursiveMapType;
    else static if (0<= downToRank && downToRank < rank!R)
        alias typeof(fun(Map!(unaryFun!(recursiveMap!(fun, downToRank, ElementType!R)),R)(R.init))) RecursiveMapType;
    else
        static assert(false);
}

/**
A n-dimensional generalization of take: given a range of ranges of rank k and n<k indices n0, n1, n2, ... , nn, it
will lazily take the first n0 elements of the range, the first n1 elements for each range inside the first, and so on.
It's a 'hypercubic' take, if you want.

So, given a rank-3 range (a range of ranges of ranges) of length 3*4*5, nTake(range, 2, 10, 2) will produce
a rank-3 range of length 2*4*2.

You can give it less indices than the rank of the range: it will left untouched the innermost ranges. So, given the previous
3*4*5 rank-3 range, nTake(range, 2,2) will produce a rank-3 range of dimension 2*2*5 and nTake(range, 2)
is the same than take(range,2) (and returns a rank-3 2*4*5 range).
*/
NTake!(R, Indices) nTake(R, Indices...)(R range, Indices indices) if (isForwardRange!R
                                                                           && allSatisfy!(isIntegral, Indices) // maybe just size_t?
                                                                           && rank!R >= Indices.length)
{
    return NTake!(R, Indices)(range, indices);
}

struct NTake(R, Indices...) if (isForwardRange!R && rank!R >= Indices.length)
{
    Indices _indices;
    Take!R _range;

    this(R range, Indices indices)
    {
        _range = take(range,indices[0]);
        foreach(i,Type; Indices) _indices[i] = indices[i];
    }

    bool empty() { return _range.empty;}

    static if (Indices.length > 1)
        NTake!(ElementType!R, Indices[1..$]) front() { return nTake(_range.front, _indices[1..$]);}
    else
        ElementType!R front() { return _range.front;}

    void popFront() { _range.popFront;}
}

/// The same, for drop.
NDrop!(R, Indices) nDrop(R, Indices...)(R range, Indices indices) if (isForwardRange!R
                                                                           && allSatisfy!(isIntegral, Indices) // maybe just size_t?
                                                                           && rank!R >= Indices.length)
{
    return NDrop!(R, Indices)(range, indices);
}

struct NDrop(R, Indices...) if (isForwardRange!R && rank!R >= Indices.length)
{
    Indices _indices;
    R _range;

    this(R range, Indices indices)
    {
        _range = drop(range,indices[0]);
        foreach(i,Type; Indices) _indices[i] = indices[i];
    }

    bool empty() { return _range.empty;}

    static if (Indices.length > 1)
        NDrop!(ElementType!R, Indices[1..$]) front() { return nDrop(_range.front, _indices[1..$]);}
    else
        ElementType!R front() { return _range.front;}

    void popFront() { _range.popFront;}
}

///
NTake!(NDrop!(R,Indices[$/2..$]),Indices[0..$/2]) nSlice(R, Indices...)(R range, Indices indices) if (isForwardRange!R
                                                 && allSatisfy!(isIntegral, Indices)
                                                 && Indices.length%2 == 0
                                                 && Indices.length/2 == rank!R)
{
    Indices[$/2..$] span;
    foreach(i,Type; Indices[$/2..$]) span[i] = indices[i+Indices.length/2]-indices[i];
    return nTake(nDrop(range, indices[0..$/2]), span);
}

/// maps two range of ranges together.
TMapType!(fun, R1,R2) recursiveBiMap(alias fun, R1, R2)(R1 r1, R2 r2) if (isSimpleRange!R1 && isSimpleRange!R2)
{
    return tmap!fun(r1, r2);
}

/// ditto
TMapType!(recursiveBiMap!(fun,R1, ElementType!R2), Repeat!R1, R2) recursiveBiMap(alias fun, R1, R2)(R1 r1, R2 r2) if (isSimpleRange!R1 && isRangeOfRanges!R2)
{
    return tmap!(recursiveBiMap!(fun, R1, ElementType!R2))(repeat(r1), r2);
}

/// ditto
TMapType!(recursiveBiMap!(fun,ElementType!R1, R2), R1, Repeat!R2) recursiveBiMap(alias fun, R1, R2)(R1 r1, R2 r2) if (isRangeOfRanges!R1 && isSimpleRange!R2)
{
    return tmap!(recursiveBiMap!(fun, ElementType!R1, R2))(r1, repeat(r2));
}

/// ditto
TMapType!(recursiveBiMap!(fun,ElementType!R1, ElementType!R2), R1, R2) recursiveBiMap(alias fun, R1, R2)(R1 r1, R2 r2) if (isRangeOfRanges!R1 && isRangeOfRanges!R2)
{
    return tmap!(recursiveBiMap!(fun, ElementType!R1, ElementType!R2))(r1,r2);
}

///
auto recursiveKnit(R1, R2)(R1 r1, R2 r2) if (isRangeOfRanges!R1 && isRangeOfRanges!R2)
{
    return recursiveBiMap!tuple(r1,r2);
}

///
auto grid(uint n)()
{
    auto indices = nuple!n(numbers());
    return tensorProduct(indices.expand);
}

/// power of a range: a range multiplied (by tensorial product) by itself n times. Generates a range of ranges, of rank n from a range of rank 1 (flat).
TensorProduct!(tuple, TypeNuple!(R, n)) power(size_t n, R)(R range) if (n && isForwardRange!R)
{
    return tensorProduct(nuple!n(range).expand);
}

/// The product of n ranges, creating a rank-n range of ranges at the same time.
struct TensorProduct(alias fun = tuple, R...) if (R.length && isForwardRange!(R[$-1])){
    alias ReverseType!(StaticTakeWhile!(isForwardRange, ReverseType!R)) Ranges;
    alias R[0..$-Ranges.length]                                         Elems;
    Ranges _ranges;
    Elems _elems;
    ElementTypes!Ranges et;

    this(R ranges) {
        static if (Elems.length)
            _elems = ranges[0..Elems.length];
        _ranges = ranges[Elems.length..$];}

    bool empty() { return _ranges[0].empty;}
    static if (Ranges.length > 1 && isForwardRange!(Ranges[$-2]))
        TensorProduct!(fun, Elems, ElementType!(Ranges[0]), Ranges[1..$]) front() {
            return tensorProduct!fun(_elems, _ranges[0].front, _ranges[1..$]);}
    else static if (Ranges.length == 1 && isRangeOfRanges!(Ranges[$-1]))
        TensorProduct!(fun, Elems, ElementType!(Ranges[0])) front() {
            return tensorProduct!fun(_elems, _ranges[0].front);}
    else
        typeof(naryFun!fun(_elems, et)) front() {
            return naryFun!fun(_elems, _ranges[0].front);}

    void popFront() {
        _ranges[0].popFront;}
}

/// ditto
TensorProduct!(fun, R) tensorProduct(alias fun = tuple, R...)(R ranges) if (isForwardRange!(R[$-1]))
{
    return TensorProduct!(fun, R)(ranges);
}

///
struct RecursiveIndex(R...) if (R.length && isForwardRange!(R[$-1])){
    alias R[$-1]    Range;
    alias R[0..$-1] Elems;
    Range _range;
    Elems _elems;
    size_t index;

    this(R ranges)
    {
        static if (Elems.length)
            _elems = ranges[0..$-1];
        _range = ranges[$-1];
    }

    bool empty() { return _range.empty;}
    static if (isRangeOfRanges!Range)
        RecursiveIndex!(Elems, size_t, ElementType!Range) front()
        {
            return typeof(return)(_elems, index, _range.front);
        }
    else
        Tuple!(Elems, size_t, ElementType!Range) front()
        {
            return tuple(_elems, index, _range.front);
        }

    void popFront()
    {
        _range.popFront;
        index++;
    }
}

/**
Indexes a range of ranges (of whatever rank): each element is transformed into a tuple(#,#,#, value), the numbers being
the 0-based coordinates. It's a n-dim generalization of indexed.
*/
RecursiveIndex!R recursiveIndex(R)(R range) if (isForwardRange!R)
{
    return RecursiveIndex!R(range);
}

/// gives the complete length of a range of ranges.
size_t rlength(R)(R r) if (isForwardRange!R)
{
    static if (isRangeOfRanges!R)
        return sum(map!(rlength!(ElementType!R))(r));
    else static if (hasLength2!R)
        return r.length;
    else
        return walkLength(r, size_t.max);
}

/**
Something aking to a Haskell functor: deconstuctor opens the T, mapper mapped the resulting range, constructor put it
back into another form.
*/
auto mapInside(alias deconstructor, alias mapper, alias constructor, T)(T t)
{
    auto opened = naryFun!deconstructor(t);
    auto mapped = array(tmap!mapper(opened));
    return naryFun!constructor(mapped);
}

///
struct AsRangeOfRanges(R) if (isForwardRange!R)
{
    R r;
    int n;

    this(R rr, int nn) { r = rr; n = nn;}

    bool empty() { return r.empty;}
    Take!R front() { return take(r,n);}
    void popFront() { popFrontN(r,n);}
}

/// ditto
AsRangeOfRanges!R asRangeOfRanges(R)(R r, int n) if (isForwardRange!R)
{
    return AsRangeOfRanges!R(r,n);
}

///
NDRangeType!(R, Indices) asNDimRange(R, Indices...)(R r, Indices indices) if (isForwardRange!R && allSatisfy!(isIntegral, Indices))
{
    static if (Indices.length == 0)
        return r;
    else
        return asNDimRange(asRangeOfRanges(r, indices[0]), indices[1..$]);
}

template NDRangeType(R, Indices...)
{
    static if (Indices.length == 0)
        alias R NDRangeType;
    else
        alias NDRangeType!(AsRangeOfRanges!R, Indices[1..$]) NDRangeType;
}

/// Returns the nthElement of each subrange in a range of range. A transversal slice, if you will.
ElementType!R nthElement(R)(R range, size_t n) if (isInputRange!R)
{
    static if (isRandomAccessRange!R)
        return range[n];
    else
    {
        while(!range.empty && n > 0) { range.popFront; --n;}
        if (range.empty) throw new Exception("nthElement: range exhausted before reaching nth element.");
        return range.front;
    }
}

/// ditto
auto nthSlice(RoR)(RoR ror, size_t n) if(isRangeOfRanges!RoR)
{
    auto nth = flipn!nthElement(n);
    return map!nth(ror);
}
