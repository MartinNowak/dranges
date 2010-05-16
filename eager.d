/**
To Be Documented.

This module is a test to code eager versions of some lazy functions
seen elsewhere, and eager algorithm, acting only on finite ranges.
*/
module dranges.eager;

import std.array, std.algorithm, std.range;

/// An eager version of map.
template map(alias fun)
{
    typeof(unaryFun!fun(ElementType!R.init))[] map(R)(R r) if (isInputRange!R)
    {
        typeof(unaryFun!fun(ElementType!R.init))[] mapped;
        static if (hasLength!R)
        {
            mapped.length = r.length;
            foreach(i, ref elem; mapped) {
                mapped[i] = unaryFun!fun(r.front);
                r.popFront;
            }
        }
        else
        {
            foreach(elem; r) mapped ~= unaryFun!fun(elem);
        }
        return mapped;
    }
}

/// An eager version of filter.
template filter(alias pred)
{
    typeof(unaryFun!pred(ElementType!R.init))[] filter(R)(R r) if (isInputRange!R)
    {
        typeof(unaryFun!pred(ElementType!R.init))[] filtered;
        foreach(elem; r) if (unaryFun!pred(elem)) mapped ~= elem;
        return mapped;
    }
}

/// All the ways to cut an array in two parts.
T[][][] bipartitions(T)(T[] array)
{
    T[][][] biparts;
    biparts.length = array.length+1;
    foreach(i; 0..array.length+1) {
        biparts[i] = [array[0..i], array[i..$]][];}
    return biparts;
}

/// All the way to cut an array into k parts.
T[][][] kpartitions(T)(uint k, T[] array)
{
    assert(k <= array.length, "kpartitions error: trying to partition an array of length " ~ to!string(array.length) ~ " into " ~ to!string(k) ~ " parts.");
    T[][][] parts;
    T[][][] mergePrefixSuffixes(T[] prefix, T[][][] suffixes){
        T[][][] merged = new T[][][suffixes.length];
        foreach(i,elem; suffixes) merged[i] = prefix ~ suffixes[i];
        return merged;
    }
    switch (k) {
        case 0:
            return parts;
        case 1:
            return [[array]];
        default:
            // I could probably calculate parts.length in advance. It's something like ((k n))
            foreach(i; 1..array.length-k+2) {
                auto subparts = kpartitions(k-1, array[i..$]);
                parts ~= mergePrefixSuffixes(array[0..i], subparts);
            }
    }
    return parts;
}

/// All the way to cut an n-elements array into 1-to-n parts. I mean, just for the fun of writing T[][][][].
T[][][][] allPartitions(T)(T[] array)
{
    T[][][][] allParts = new T[][][][array.length]; // From partition!1 to partition!(array.length)
    foreach(i, ref elem; allParts) elem = kpartitions(i+1, array);
    return allParts;
}

///
T[] addOneToSorted(T)(T[] sorted, T element)
{
    if (!sorted.empty)
    {
        if (element < sorted[0]) return element ~ sorted;
        if (element > sorted[$-1]) return sorted ~ element;
        if (element == sorted[$/2]) return sorted[0..$/2] ~ element ~ sorted[$/2..$];

        return (element < sorted[$/2]) ?
            addOneToSorted(sorted[0..$/2], element) ~ sorted[$/2..$] :
            sorted[0..$/2] ~ addOneToSorted(sorted[$/2..$], element);
    }
    else
    {
        return [element];
    }
}
