// Written in the D programming language

/**
To Be Documented.


License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.patternmatch;

import std.conv;
import std.stdio;
import std.functional;
import std.range;
import std.traits;
import std.typecons;
import std.typetuple;
//import std.variant;

import dranges.traits2;
import dranges.typetuple2;
import dranges.templates;
import dranges.reftuple;

struct Switch(T, R)
{
    T object;
    bool hasValue;
    R value;

    this(T o)
    {
        object = o;
    }

    void Set(R value)
    {
        this.value = value;
        hasValue = true;
    }

    Switch!(T, R) Case(alias t, alias f)() if (is(typeof(t) == T))
    {
        if (!hasValue && t == object)
        {
            Set(unaryFun!f(object));
        }
        return this;
    }

    Switch!(T, R) Case(alias pred, alias f)() if (!is(typeof(pred) == T))
    {
        if (!hasValue && unaryFun!pred(object))
        {
            Set(unaryFun!f(object));
        }
        return this;
    }

    R Default(alias f)()
    {
        if (!hasValue)
        {
            Set(unaryFun!f(object));
        }

        return value;
    }
}

Switch!(T,R) sswitch(R,T)(T o) {
    return Switch!(T,R)(o);
}

template toPointer(T) { alias T* toPointer;}


template ConvertibleTypeTuples(T...) if (T.length % 2 == 0)
{
    static if (T.length == 0)
        enum bool ConvertibleTypeTuples = true;
    else
        enum bool ConvertibleTypeTuples = isImplicitlyConvertible!(T[0], T[T.length/2])
                                       && ConvertibleTypeTuples!(T[1 .. T.length/2], T[T.length/2+1 .. T.length]);
}

class NoMatchException : Exception {
    this(string msg) { super(msg);}
}

struct Matcher(alias fun, size_t n, Rest...) /*if (n>1)*/ {
    TypeTuple!(Rest[0..n]) _m;
    this(TypeTuple!(Rest[0..n]) m) { _m = m;}
    auto opCall() {
        static if (is(typeof(fun(_m))))
            return fun(_m);
        else static if (n == 1 && is(typeof(fun(_m[0]))))
            return fun(_m[0]);
        else static if (Rest.length > n) {
            return Matcher!(Rest[n], n, Rest[0..n], Rest[n+1..$])(_m)();
        }
        else {
            string s;
            foreach(i, Type; TypeTuple!(Rest[0..n])) s ~= to!string(_m[i]);
            throw new NoMatchException("No match for " ~ s ~ " of type " ~ typeof(_m).stringof);
        }
    }
}

template MatcherType(alias fun, size_t n, Rest...)
{
    static if (is(typeof(fun(Init!(Rest[0..n])))))
        alias typeof(fun(Init!(Rest[0..n]))) MatcherType;
    else static if (n == 1 && is(typeof(fun(Rest[0].init))))
        alias typeof(fun(Rest[0].init)) MatcherType;
    else static if (Rest.length > n)
        alias MatcherType!(Rest[n],n, Rest[0..n], Rest[n+1..$]) MatcherType;
    else
        static assert(false, "MatcherType: couldn't find a match for types " ~ Rest[0..n].stringof);
}


template match(alias fun, Rest...) {
    MatcherType!(fun, M.length, M, Rest) match(M...)(M m) {
        return Matcher!(fun, M.length, M, Rest)(m)();
    }
}

ReturnType!F cond(M,P,F,Rest...)(M m, P pred, F fun, Rest rest) {
    if (pred(m)) {
        return fun(m);
    }
    else static if (Rest.length > 0) {
        return cond(m, rest);
    }
}

/+
Algebraic!(ParameterTypeTuples!Funs) amatch(AType, Funs...)(AType alg) if (__traits(compiles, AType.AllowedTypes) && is(ParameterTypeTuples!Funs == AType.AllowedTypes))
{
    Algebraic!(ParameterTypeTuples!Funs) result;
    foreach(fun; Funs)
    {
        auto p = alg.peek!(ParameterTypeTuple!fun[0]);
        if (p !is null)
        {
            result = fun(*p);
            break;
        }
    }
    return result;
}
+/

string any(T...)(T t) { return "any: " ~ typeof(t).stringof;}

template byDefault(alias dg) {
    auto byDefault(...) {
        static if (__traits(compiles, dg()))
            return dg();
        else
            return dg;
    }
}


T one(T)(T t)
    { return t;}

T[] twoEqual(T)(T t1, T t2)
    { return [t1,t2];}

Tuple!(T,U) twoDiff(T,U)(T t, U u)
    { return tuple(t,u);}

string three(T)(T t1, T t2, T t3)
    { return T.stringof ~ " thrice";}

string threeDiff(T,U,V)(T t, U u, V v)
    { return T.stringof ~ " " ~ U.stringof ~ " " ~ V.stringof;}

