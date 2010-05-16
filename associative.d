/**
To Be Documented.

Functions acting upon associative arrays: filtering them, etc.
*/
module dranges.associative;

import std.range;

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
V[K] filter(alias pred,K,V)(V[K] aa)
{
    V[K] result;
    foreach(k,v; aa) if (unaryFun!pred(k)) { result[k] = v;}
    return result;
}

///
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
