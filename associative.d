// Written in the D programming language.

/**
Functions acting upon associative arrays: filtering them, etc.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.associative;

import std.algorithm,
       std.range,
       std.typecons;


/**
Simple helper function to duplicate an associative array.
*/
V[K] dup(K,V)(V[K] aa)
{
    V[K] _aa;
    foreach(k,v; aa) _aa[k] = v;
    return _aa;
}

/**
There may be a need for an 'asRange' function that takes a container
and returns a range iterating over the entire content. In this particular case, asRange takes
an associative array of type V[K] and returns (K,V) tuples.
It's a random-access range, with a length. opIndexAssign is defined and will
change the original associative array.
Note:
I'm a bit ambivalent on this one. front/back returns tuples, because that's the
entire content and because if you only want keys or values, you can use the homonym
properties. But for opIndex (indexed on keys) you already know the key, so it returns
only a value. The same for opIndexApply. I'm wondering if that's OK or not.
Example:
----
auto aa = ["Hello":5, "World!":6, "a":99, "":0, "Howdy":6];
auto aa_range = aa.asRange;
assert(equal(aa_range, [tuple("a",99), tuple("",0), tuple("Hello",5), tuple("World!",6), tuple("Howdy",6)][]));
assert(aa_range.length == 5); // has a length
assert(aa_range["Hello"] == 5); // opIndex. Returns a value.
aa_range["Hello"] = 100; // opIndexAssign.
assert(aa["Hello"] == 100); // changes the original AA.
aa["Howdy"] = 66; // If we change the original AA after .asRange was called
assert(aa_range["Howdy"] == 66); // The range presents the udpated view.
----
*/
struct AsRange(K,V)
{
    V[K] _aa;
    K[] _keys;

    this(V[K] aa) { _aa = aa/+.dup+/; _keys = _aa.keys;}

    bool empty() { return _keys.empty;}
    Tuple!(K,V) front() { return tuple(_keys.front, _aa[_keys.front]);}
    @property AsRange save() { return this;}
    void popFront() { _keys.popFront;}
    Tuple!(K,V) back() { return tuple(_keys.back, _aa[_keys.back]);}
    void popBack() { _keys.popBack;}
    size_t length() { return _keys.length;}
    V opIndex(K key) { return _aa[key];}
    void opIndexAssign(V value, K key) { _aa[key] = value;}
}

/// ditto
AsRange!(K,V) asRange(K,V)(V[K] aa) {
    return AsRange!(K,V)(aa);
}

unittest
{
    auto aa = ["Hello":5, "World!":6, "a":99, "":0, "Howdy":6];
    auto aa_range = aa.asRange;
    assert(is(ElementType!(typeof(aa_range)) == Tuple!(string, int)));
//    assert(equal(aa_range, [tuple("a",99), tuple("",0), tuple("Hello",5), tuple("World!",6), tuple("Howdy",6)][]));
    assert(aa_range.length == 5); // has a length
    assert(aa_range["Hello"] == 5); // opIndex. Returns a value.
    aa_range["Hello"] = 100; // opIndexAssign.
    assert(aa["Hello"] == 100); // changes the original AA.
    aa["Howdy"] = 66; // If we change the original AA after .asRange was called
    assert(aa_range["Howdy"] == 66); // The range presents the udpated view.
}

///
Unqual!(ElementType!VR)[ElementType!KR]
toAssoc(KR, VR)(KR keysRange, VR valuesRange)
if (isInputRange!KR && isInputRange!VR)
{
    typeof(return) aa;
    foreach(key; keysRange) {
        if (valuesRange.empty) break;
        aa[key] = valuesRange.front;
        valuesRange.popFront;
    }
    return aa;
}

///
Unqual!(ElementType!VR)[ElementType!KR]
addToAssoc(KR, VR)(Unqual!(ElementType!VR)[ElementType!KR] aa, KR keysRange, VR valuesRange)
if (isInputRange!KR && isInputRange!VR)
{
    foreach(key; keysRange) {
        if (valuesRange.empty) break;
        aa[key] = valuesRange.front;
        valuesRange.popFront;
    }
    return aa;
}

///
Unqual!(ElementType!VR)[ElementType!KR]
addToAssoc(KR, VR)(Unqual!(ElementType!VR)[ElementType!KR] aa, KR keysRange, VR valuesRange, ElementType!VR delegate(ElementType!VR, ElementType!VR) onCollision)
if (isInputRange!KR && isInputRange!VR)
{
    foreach(key; keysRange) {
        if (valuesRange.empty) break;
        if (key in aa) {
            aa[key] = onCollision(aa[key], valuesRange.front); // (old,new)
        }
        else {
            aa[key] = valuesRange.front;
        }
        valuesRange.popFront;
    }
    return aa;
}

///
V[K] append(K,V)(V[K] aa, K key, V value)
{
    aa[key] = value;
    return aa;
}
///
V[K] prepend(K,V)(V[K] aa, K key, V value)
{
    aa[key] = value;
    return aa;
}

/// Filtering on keys
V[K] filterOnKeys(alias pred,K,V)(V[K] aa)
{
    V[K] result;
    foreach(k,v; aa) if (unaryFun!pred(k)) { result[k] = v;}
    return result;
}

/**
A constraint template to detect associative arrays of a certain type. It's a curried (nested) template:
isKV!(int,string) is itself a template.
Example:
----
alias isKV(int,string) IntString;
assert(IntString!(string[int]));
assert(!IntString!(double[int]));
----
*/
template isKV(K,V)
{
    template isKV(T) {
        static if (is(T == V[K]))
            enum bool isKV = true;
        else
            enum bool isKV = false;
    }
}

/// Merge AA.
V[K] merge(K,V,T...)(V[K] aa, T aas) if(allSatisfy!(isKV!(K,V), T))
{
    auto result = aa;
    foreach(i,Type; T)
    {
        foreach(k,v; aas[i])
        {
            result[k] = v;
        }
    }
    return result;
}

/// Merge AA, with a merging function if some keys exist on more than one array.
V[K] mergeWith(alias fun = "c", K,V,T...)(V[K] aa, T aas) if(allSatisfy!(isKV!(K,V), T))
{
    auto result = aa;
    foreach(i,Type; T)
    {
        foreach(k,v; aas[i])
        {
            if (k in result) {
                result[k] = naryFun!fun(k,result[k],v);
            }
            else {
                result[k] = v;
            }
        }
    }
    return result;
}

///
ElementType!R.Types[1][ElementType!R.Types[0]] toAA(R)(R r) if (isForwardRange!R && is(ElementType!R KV == Tuple!(K,V), V,K))
{
    typeof(return) aa;
    foreach(elem; r) aa[elem.field[0]] = elem.field[1];
    return aa;
}
///
ElementType!VR[ElementType!KR] toAA(KR, VR)(KR keyRange, VR valueRange) if (isForwardRange!KR && isForwardRange!VR)
{
    typeof(return) aa;
    foreach(elem; keyRange) {
        if (valueRange.empty) break;
        aa[elem] = valueRange.front;
        valueRange.popFront;
    }
    return aa;
}
