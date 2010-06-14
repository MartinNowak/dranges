// Written in the D programming language

/**
To Be Documented.

This module defines some range-like templates on variadic lists : mapping, filtering, etc.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.variadic;

import dranges.typetuple2;
import dranges.templates;
import dranges.functional2;

///
CommonType!T max(T...)(T t) if (T.length) { // I should test for a correct type: one that defines min and opCmp
    CommonType!T result = CommonType!T.min;
    foreach(i, Type; T) if (result < t[i]) result = t[i];
    return result;
}

///
CommonType!T min(T...)(T t) if (T.length) { // I should test for a correct type: one that defines min and opCmp
    CommonType!T result = CommonType!T.max;
    foreach(i, Type; T) if (result > t[i]) result = t[i];
    return result;
}

///
Tuple!(StaticMap!(RT!fun, T)) mapVariadic(alias fun, T...)(T tup)
{
    StaticMap!(RT!fun, T) res;
    foreach(i, Type; T) res[i] = fun(tup[i]);
    return tuple(res);
}

///
StaticScan!(RT2!fun, T)[$-1] reduceVariadic(alias fun, T...)(T ts)
{
    alias StaticScan!(RT2!fun, T) RTS;
    RTS result;
    foreach(i, Type; RTS) {
        static if (i == 0)
            result[i] = ts[0];
        else
            result[i] = fun(result[i-1], ts[i]);
    }
    return result[$-1];
}

///
Tuple!(StaticScan!(RT2!fun, T)) scanVariadic(alias fun, T...)(T ts)
{
    alias StaticScan!(RT2!fun, T) RTS;
    RTS result;
    foreach(i, Type; RTS) {
        static if (i == 0)
            result[i] = ts[0];
        else
            result[i] = fun(result[i-1], ts[i]);
    }
    return tuple(result);
}

///
Tuple!(StaticStride!(n,T)) strideVariadic(size_t n, T...)(T ts) if (n > 0)
{
    alias StaticStride!(n,T) StridedTypes;
    StridedTypes result;
    foreach(i, Type; StridedTypes) result[i] = ts[i*n];
    return tuple(result);
}

/**
Finds the maximum value of a variadic list, at compile-time.
Example:
----
assert(Max!1 == 1);
assert(Max!(1,2) == 2);
assert(Max!(1,2,4,3,0) == 4);
----
*/
template Max(alias a, Rest...) {
    static if (Rest.length > 0) {
        alias Max!(dranges.templates.Max!(a, Rest[0]), Rest[1..$]) Max;
    }
    else {
        alias a Max;
    }
}

/**
Finds the minimum value of a variadic list, at compile-time.
Example:
----
assert(Min!1 == 1);
assert(Min!(1,2) == 2);
assert(Min!(1,2,4,3,0) == 4);
----
*/
template Min(alias a, Rest...) {
    static if (Rest.length > 0) {
        alias Min!(dranges.templates.Min!(a, Rest[0]), Rest[1..$]) Min;
    }
    else {
        alias a Min;
    }
}

unittest
{
    assert(Max!1 == 1);
    assert(Max!(1,2) == 2);
    assert(Max!(1,2,4,3,0) == 4);

    assert(Min!1 == 1);
    assert(Min!(1,2) == 1);
    assert(Min!(1,2,4,3,0) == 0);
}
