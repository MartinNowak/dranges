// Written in the D programming language

/**
To Be Documented.

I put in this module some not-quite-ranges, and some plays on the concept of ranges.
Some of these ideas have been promoted to modules: tuple2, variadic2.


License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.experiments;

import std.range;

import dranges.traits2;

/**
Not really a standard range, used to modelize:
 ... infinitely many values ... -2 -1 0 1 2 ... infinitely many values ...
                                      ^
As such, it has no real center, only a current element.

Difference with InfiniteBiDir: IBD consumes the inner ranges with popFront/popBack. Here no, the
range is infinite at both ends and front is in fact only an index. popFront advances the index,
popBack get it back one position. Back is not really useful in this case (but defined all the same)
and is just the element one position before (left of) front.

It uses the standard front/back/popX methods, but it's not really a range and doesn't respect the
semantics of popFront/popBack.
There is also a reset() method, to get back to the initial (as creation) position.

It's implemented either with two non-bidir infinite ranges or a generative function.
*/
struct BiInfiniteRange(R1, R2) if (isForwardRange!R1 && isForwardRange!R1
                                 && isInfinite!R1 && isInfinite!R2
                                 && !isBidirectionalRange!R1 && !isBidirectionalRange!R2
                                 && CompatibleRanges!(R1,R2))
{
    R1 _r1;
    R2 _r2;
    alias CommonElementType!(R1,R2) ET;
    ET[] center;
    size_t index;

    this(R1 r1, R2 r2) {
        _r1 = r1; _r2 = r2;
        center = [_r2.front,_r1.front];
        _r1.popFront; _r2.popFront;
        index = 1;
    }

    enum bool empty = false;

    ET front() { return center[index];}
    void popFront()
    {
        if (index == center.length-1)
        {
            center ~= _r1.front;
            _r1.popFront;
        }
        ++index;
    }

    ET back() { return center[index-1];}
    void popBack()
    {
        if (index == 0)
        {
            center = _r2.front ~ center; // Yeah, I know.
            _r2.popFront;
        }
        else
        {
            --index; // asymetry with popFront. index cannot be < 0
        }
    }

    static if (isRandomAccessRange!R1 && isRandomAccessRange!R2)
    {
        ET opIndex(int i)
        {
            if (index+i >= center.length) return _r1[index+i-center.length]; // beyond center
            if (index+i < 0) return _r2[-index-i];
            return center[index+i];
        }
    }

    typeof(this) opSlice() { return this;}

    void reset() { index = 0;}
}

BiInfiniteRange!(R1,R2) biInfiniteRange(R1,R2)(R1 r1, R2 r2)
{
    return BiInfiniteRange!(R1,R2)(r1, r2);
}

/**
Generating a bi-infinite range with a function.
*/
struct BiInfiniteRange(G)
{
    G _gen;
    alias typeof(_gen(0)) ET;
    ET[] center;
    size_t index;

    this(G gen) { _gen = gen;}

    enum bool empty = false;
    ET front() { return _gen(index);}
    void popFront() { ++index;}
    ET back() { return _gen(index-1);}
    void popBack() { --index;}
    ET opIndex(int i) { return _gen(index+i);}
    typeof(this) opSlice() { return this;}
    void reset() { index = 0;}
}

BiInfiniteRange!(G) biInfiniteRange(G)(G gen) if (isFunctionType!G)
{
    return BiInfiniteRange!(G)(gen);
}

