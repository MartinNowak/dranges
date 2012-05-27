//Written in the D programming language

/**
This module provides modified versions of std.algorithm and std.range functions.
If you're interested, they should be put in your local copy of std.

The most simple/solid ones are map and filter. Chain and take are much more 'fragile'.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.phobos_extension;

import std.c.string; // to give the templates access to c.string as template parameters
import std.algorithm,
       std.array,
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

import dranges.templates,
       dranges.traits,
       dranges.typetuple;

/+
/**
Alternate template to std.range.hasLength, as hasLength doesn't work
if R has its length method defined inside a static if.
*/
template hasLength(R) {
    enum bool hasLength = __traits(compiles, R.length);
}
+/

/**
An extended version of std.algorithm.Map, that makes it propagate the
input range properties (bidirectional, etc.)
$(UL
$(LI it defines back/popBack if the input range is bidirectional.)
$(LI it defines opIndex if the range offers random-access.)
$(LI it has a length if the input range has one.)
$(LI it's infinite if the input range is infinite.)
$(LI it can be sliced if the input range can also.)
)
Examples:
----
auto r = [0,1,2,3,4]; // random-access range with a length and slicing.
auto m = map!"a*a"(r);

assert(equal(retro(m), [16,9,4,1,0][])); // bidirectional range
assert(m[3] == 9); // random-access range
assert(m.length == 5); // length
assert(equal(m[1..3], [1,4][])); // slicing

auto m2 = map!"a*a"(cycle(r)); // cycle(r) is infinite
assert(isInfinite(typeof(m2))); // m2 is infinite also.
assert(!is(m2.length)); // cycle(r) doesn't have a length, so neither has m2.
----
Note:
map caches its front and back. So be prudent if you use callable classes/structs
with an internal state (and why would you use a class as a callable if not to manage
state?).
*/
struct Map(alias fun, Range) if (isInputRange!(Range))
{
    alias typeof(fun(.ElementType!(Range).init)) ElementType;
    Range _input;
    ElementType _cache, _backCache;

    private void fillCache() { if (!_input.empty) _cache = fun(_input.front); }
    static if (isBidirectionalRange!Range) {
        private void fillBackCache() { if (!_input.empty) _backCache = fun(_input.back);}
    }

    this(Range input) {
        _input = input; fillCache;
        static if (isBidirectionalRange!Range) fillBackCache;
    }
    static if (isInfinite!Range) {
        enum bool empty = false; // infinite also
    }
    else  {
        bool empty() { return _input.empty; }
    }
    void popFront() { _input.popFront; fillCache; }
    ElementType front() { return _cache; }

    static if (isBidirectionalRange!Range) {
        void popBack() { _input.popBack; fillBackCache; }
        ElementType back() { return _backCache; }
    }

    static if (hasLength!Range)
        size_t length() { return _input.length;}

    static if (isRandomAccessRange!Range)
        ElementType opIndex(size_t i) { return fun(_input[i]);}

    static if (hasSlicing!Range) {
        Map!(fun, Range) opSlice(size_t i1, size_t i2) {
            return map!fun(_input[i1..i2]);
        }
    }

    typeof(this) opSlice() {
        return this;
    }
}

/+
unittest
{
    auto r = [0,1,2,3,4]; // random-access range with a length and slicing.
    auto m = map!"a*a"(r);

    assert(equal(retro(m), [16,9,4,1,0][])); // bidirectional range
    assert(m[3] == 9); // random-access range
    assert(m.length == 5); // length
    assert(equal(m[1..3], [1,4][])); // slicing

    auto m2 = map!"a*a"(cycle(r)); // cycle(r) is infinite
    assert(isInfinite!(typeof(m2))); // m2 is infinite also.
    assert(!is(m2.length)); // cycle(r) doesn't have a length, so neither has m2.
}
+/

/**
An extended version of std.algorithm.Filter that defines
back/popBack if the input range is bidirectional.
Example:
----
auto r = [0,1,2,3,4];
auto f = filter!"a%2==0"(r);
assert(equal(retro(f), [4,2,0])); // f is a bidirectional range
----
*/
struct Filter(alias pred, Range) if (isInputRange!(Range))
{
    Range _input;

    this(Range r)
    {
        _input = r;
        while (!_input.empty && !pred(_input.front)) _input.popFront;
        static if (isBidirectionalRange!Range)
            while (!_input.empty && !pred(_input.back)) _input.popBack;
    }

    ref Filter opSlice()
    {
        return this;
    }

    bool empty() { return _input.empty; }
    void popFront()
    {
        do
        {
            _input.popFront;
        } while (!_input.empty && !pred(_input.front));
    }

    ElementType!(Range) front() { return _input.front;}

    static if (isBidirectionalRange!Range) {
        void popBack()
        {
            do
            {
                _input.popBack;
            } while (!_input.empty && !pred(_input.back));
        }

        ElementType!(Range) back() { return _input.back;}
    }
}

/+
unittest
{
    auto r = [0,1,2,3,4];
    auto f = filter!"a%2==0"(r);
    assert(equal(retro(f), [4,2,0][])); // f is a bidirectional range
    assert(equal(retro(f), [4,2,0][])); // f is a bidirectional range
}
+/

/**
std.range.Repeat should have popBack defined.
*/
struct Repeat(T)
{
    private T _value;
    ref T front() { return _value; }
    ref T back() { return _value; }
    enum bool empty = false;
    void popFront() {}
    void popBack() {}
    ref T opIndex(uint) { return _value; }
}

/**
std.range.Stride assumes a bidirectional range. This slight modification
just add the necessary 'isBidirectionalRange!R' throughout the code.
*/
struct Stride(R) if (isInputRange!(R))
{
private:
    R _input;
    size_t _n;

public:
    this(R input, size_t n)
    {
        _input = input;
        _n = n;
        static if (hasLength!(R))
        {
            auto slack = _input.length % _n;
            if (slack) slack--;
            if (!slack) return;
            static if (isRandomAccessRange!(R) && hasSlicing!(R))
            {
                _input = _input[0 .. _input.length - slack];
            }
            else
            {
                foreach (i; 0 .. slack)
                {
                    if (_input.empty) break;
                    _input.popBack;
                }
            }
        }
    }

    Stride opSlice()
    {
        return this;
    }

    bool empty()
    {
        return _input.empty;
    }

    void popFront()
    {
        static if (isRandomAccessRange!(R) && hasLength!(R) && hasSlicing!(R))
        {
            _input = _input[
                _n < _input.length ? _n : _input.length
                .. _input.length];
        }
        else
            foreach (i; 0 .. _n)
            {
                _input.popFront;
                if (_input.empty) break;
            }
    }

    static if (hasLength!(R) && isBidirectionalRange!R)
        void popBack()
        {
            enforce(_input.length >= _n);
            static if (isRandomAccessRange!(R) && hasSlicing!(R))
            {
                _input = _input[0 .. _input.length - _n];
            }
            else
            {
                foreach (i; 0 .. _n)
                {
                    if (_input.empty) break;
                    _input.popBack;
                }
            }
        }

    ref ElementType!(R) front()
    {
        return _input.front;
    }

    static if (isBidirectionalRange!R) {
        ref ElementType!(R) back()
        {
            return _input.back;
        }
    }

    static if (isRandomAccessRange!(R) && hasLength!(R))
        ref ElementType!(R) opIndex(uint n)
        {
            return _input[_n * n];
        }

    static if (hasLength!(R))
        size_t length()
        {
            return (_input.length + _n - 1) / _n;
        }
}

/**
A corrected version of std.range.take.

/+It uses slicing when possible, to get (hopefully) a better performance.+/

The std version has problems with its back/popBack methods, they simply do not work.
It seems these do work (to be thoroughly tested, though), but they depend on rather
strict conditions on the input range: back/popBack needs a random-access range
with a length.
*/
struct Take(R) if (isInputRange!(R))
{
private:
    size_t _maxAvailable;
    R _input;
    enum bool byRef = is(typeof(&(R.init[0])));

public:
    alias R Source;

    static if (byRef)
        alias ref .ElementType!(R) ElementType;
    else
        alias .ElementType!(R) ElementType;

    bool empty()
    {
        return _maxAvailable == 0 || _input.empty;
    }

    void popFront()
    {
        enforce(_maxAvailable > 0);
        _input.popFront;
        --_maxAvailable;
    }

    // @@@@@@@@@@@ UGLY @@@@@@@@@@@@@@@
    mixin(
        (byRef ? "ref " : "")~
        q{ElementType front()
        {
            enforce(_maxAvailable > 0);
            return _input.front;
        }});

    static if (isInfinite!(R))
    {
        size_t length() const
        {
            return _maxAvailable;
        }

        void popBack()
        {
            enforce(_maxAvailable);
            --_maxAvailable;
        }
    }
    else static if (hasLength!(R))
    {
        size_t length()
        {
            return min(_maxAvailable, _input.length);
        }

        static if (isRandomAccessRange!(R))
        {
            void popBack()
            {
                if (_maxAvailable < _input.length) // changed from > to <
                {
                    --_maxAvailable;
                }
                else
                {
                    _input.popBack;
                }
            }
        }
    }

    static if (isRandomAccessRange!(R))
    {
        mixin(
            (byRef ? "ref " : "")~
            q{ElementType opIndex(uint index)
                {
                    enforce(_maxAvailable > index);
                    return _input[index];
                }
            });
    }

/+    static if (isBidirectionalRange!(R))
    {
        mixin(
            (byRef ? "ref " : "")~
            q{ElementType back()
                {
                    return _input[_maxAvailable];
                }
            });
    }
    else+/ static if (isRandomAccessRange!(R) /+&& isInfinite!(R)+/)
    {
        // Random access but not bidirectional could happen in the
        // case of e.g. some infinite ranges
        mixin(
            (byRef ? "ref " : "")~
            q{ElementType back()
                {
                    return _input[this.length() - 1];
                }
            });
    }

    Take opSlice() { return this; }
}

/// Ditto
Take!R take(R)(size_t n, R input) if (isInputRange!R)
{
/+    static if (hasSlicing!R && hasLength!R)
    {
        auto nn = min(n,input.length);
        return input[0..nn];
    }
    else
    {+/
        return Take!(R)(n, input);
    /+}+/
}

template TakeType(R) if (isInputRange!R)
{
    static if (hasSlicing!R)
        alias R TakeType;
    else
        alias Take!R TakeType;
}

/**
An extended version of std.range.ChainImpl.

In DMD 2.037, chain has some problems:

$(UL
$(LI opIndex doesn't deal correctly with infinite ranges)
$(LI the same for opIndexAssign))

----
auto c = chain([0,1,2][], cycle([4,5,6][]), [7,8,9][]); // infinite range inside.
auto c7 = c[7]; // doesn't work with std.range.chain.
----

This version also provides some concatenation capabilities on the right
with another chain (with flattening), with another range and with an element.
*/
struct ChainImpl(R...)
{
private:
    alias CommonType!(staticMap!(.ElementType, R)) RvalueElementType;
    template sameET(A)
    {
        enum sameET = is(.ElementType!(A) == RvalueElementType);
    }
    enum bool allSameType = allSatisfy!(sameET, R);

public:
    Tuple!(R) _input;
    // This doesn't work yet
    static if (allSameType)
        alias ref RvalueElementType ElementType;
    else
        alias RvalueElementType ElementType;

    this(R input)
    {
        foreach (i, v; input)
        {
            _input.field[i] = v;
        }
    }

    bool empty()
    {
        foreach (i, Unused; R)
        {
            if (!_input.field[i].empty) return false;
        }
        return true;
    }

    void popFront()
    {
        foreach (i, Unused; R)
        {
            if (_input.field[i].empty) continue;
            _input.field[i].popFront;
            return;
        }
    }

    //@@@BUG 2597@@@
    //auto front()
    //@@@AWKWARD!!!@@@
    mixin(
        /+(allSameType ? "ref " : "")~+/
        q{ElementType front()
            {
                foreach (i, Unused; R)
                {
                    if (_input.field[i].empty) continue;
                    return _input.field[i].front;
                }
                assert(false);
            }
        });

    static if (allSatisfy!(isBidirectionalRange, R))
    {
        mixin(
            /+(allSameType ? "ref " : "")~+/
            q{ElementType back()
                {
                    foreach_reverse (i, Unused; R)
                    {
                        if (_input.field[i].empty) continue;
                        return _input.field[i].back;
                    }
                    assert(false);
                }
            });

        void popBack()
        {
            foreach_reverse (i, Unused; R)
            {
                if (_input.field[i].empty) continue;
                _input.field[i].popBack;
                return;
            }
        }
    }

    static if (allSatisfy!(hasLength, R))
        size_t length()
        {
            size_t result;
            foreach (i, Unused; R)
            {
                result += _input.field[i].length;
            }
            return result;
        }

    static if (allSatisfy!(isRandomAccessRange, R))
    {
        mixin(
            /+(allSameType ? "ref " : "")~+/
            q{ElementType opIndex(uint index)
                {
                    foreach (i, Unused; R)
                    {
                        static if (hasLength!Unused) {
                            immutable length = _input.field[i].length;
                            if (index < length) return _input.field[i][index];
                            index -= length;
                        }
                        else {
                            static if (isInfinite!Unused) {
                                return _input.field[i][index];
                            }
                        }
                    }
                    assert(false);
                }
            });

        static if (allSameType && allSatisfy!(hasAssignableElements, R)) void opIndexAssign(ElementType v, uint index)
        {
            foreach (i, Unused; R)
            {
                static if (hasLength!Unused) {
                    immutable length = _input.field[i].length;
                    if (index < length)
                    {
                        _input.field[i][index] = v;
                        return;
                    }
                    index -= length;
                }
                else {
                    static if (isInfinite!Unused) {
                        _input.field[i][index] = v;
                        return;
                    }
                }
            }
            assert(false);
        }
    }

    static if (allSatisfy!(hasLength, R) && allSatisfy!(hasSlicing, R))
        ChainImpl opSlice(size_t begin, size_t end)
        {
            auto result = this;
            foreach (i, Unused; R)
            {
                immutable len = result._input.field[i].length;
                if (len < begin)
                {
                    result._input.field[i] = result._input.field[i]
                        [len .. len];
                    begin -= len;
                }
                else
                {
                    result._input.field[i] = result._input.field[i]
                        [begin .. len];
                    break;
                }
            }
            auto cut = length;
            cut = cut <= end ? 0 : cut - end;
            foreach_reverse (i, Unused; R)
            {
                immutable len = result._input.field[i].length;
                if (cut > len)
                {
                    result._input.field[i] = result._input.field[i]
                        [0 .. 0];
                    cut -= len;
                }
                else
                {
                    result._input.field[i] = result._input.field[i]
                        [0 .. len - cut];
                    break;
                }
            }
            return result;
        }


// with another Chain -> groups the internal ranges into on common Chain
    Chain!(R, U) opCat(U...)(ChainImpl!U range) /+if (!is(CommonType!(.ElementType!(ChainImpl!U), ElementType) == void))+/
    {
        return chain(_input.expand, range._input.expand);
    }

// standard ranges. Ugly hack to find is range is a chain...
    Chain!(R, R2) opCat(R2)(R2 range) if (isInputRange!R2 && !is(R2.RvalueElementType) && !is(CommonType!(.ElementType!R2, ElementType) == void))
    {
        return chain(_input.expand, range);
    }

// with an element
    Chain!(R, CommonType!(E,ElementType)[]) opCat(E)(E element) if (!is(CommonType!(E,ElementType) == void))
    {
        return chain(_input.expand, [cast(CommonType!(E,ElementType))element][]);
    }

//// with a standard range
//    Chain!(R2, R) opCat_r(R2)(R2 range) if (isInputRange!R2 && !is(CommonType!(.ElementType!R2, ElementType) == void))
//    {
//        return chain(range, _input.expand);
//    }
//
//// with a Chain (works because DMD tries to instantiate opCat_r befre trying to instantiate opCat
//    Chain!(U, R) opCat_r(U...)(ChainImpl!U range) if (!is(CommonType!(.ElementType!(ChainImpl!U), ElementType) == void))
//    {
//        return chain(range._input.expand, _input.expand);
//    }

//// With an element
//    /+static if (!__traits(hasMember, ElementType, "opCat"))+/
//        Chain!(ElementType[],R) opCat_r(ElementType element)
//        {
//            return chain([element][], _input.expand);
//        }
}

