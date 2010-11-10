// Written in the D programming language

/**
This module leverages the pattern-matching nature of templates to provide a basic pattern-matching
function. The main function here is $(M match), the engine behind ($ dranges.functional.eitherFun).
See below for more doc.

My goal is to link into a coherent whole all the pattern-matching modules in dranges: this one, $(dranges.typepattern),
($M dranges.tuplepattern), $(M drange.ctre) and maybe use them to map and transform tuple-trees. A far-away
but inspirational goal is to get an AST from D code, transform it and recombine it into another AST, reducing it down
to (a string reprensenting) D code. That is, a sort of macro system for D. It's but a dream, but it's a also a fun journey.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.patternmatch;

import std.conv,
       std.functional,
       std.range,
       std.stdio,
       std.traits,
       std.typecons,
       std.typetuple;

import dranges.reftuple,
       dranges.templates,
       dranges.traits,
       dranges.typetuple;

// An old version.
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

/**
$(M match) is a pattern taking any number of function, templated or not, as input. When you then pass it a value,
$(M match) will test the value with the passed-in functions in the order they were passed-in,
see if they match or not and return the result of the first function that matches.
If no function matches, $(M match) will throw a $(M NoMatchException).

The provided functions are template parameters and so must be known at compile-time.

The interesting part is that, being a template and acting on templated functions, $(M match) can potentially accept any type
and return any other type. It uses the inherent pattern-matching done by templates to find a match. All the type-patterns and template constraints
you're used to can be used there.

For example:
----
T one(T)(T t) { return t;} // matches any lone type

T[] twoEqual(T)(T t1, T t2) { return [t1,t2];} // matches if the input is twice the same type

Tuple!(T,U) twoDiff(T,U)(T t, U u) { return tuple(t,u);} // Matches any two types

string three(T)(T t1, T t2, T t3) { return T.stringof ~ " thrice";} // Thrice the same type

string threeDiff(T,U,V)(T t, U u, V v) // Any three types.
    { return T.stringof ~ " " ~ U.stringof ~ " " ~ V.stringof;}

alias match!(one,
             twoEqual,
             twoDiff,
             three,
             threeDiff,
             any) m;

assert(m(1) == 1);              // one type
assert(m('a','b') = ['a','b']);  // twice the same type. twoEqual is tested before two
assert(m('a', 2.34) == tuple('a',2.34)); // two different types. twoEqual is not activated, but twoDiff is.
m("aha", 1, 3.1415, 'a'); // no match!
----

See_Also: $(dranges.functional.eitherFun).
*/
template match(alias fun, Rest...) {
    MatcherType!(fun, M.length, M, Rest) match(M...)(M m) {
        return Matcher!(fun, M.length, M, Rest)(m)();
    }
}

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

string any(T...)(T t) { return "any: " ~ typeof(t).stringof;}


ReturnType!F cond(M,P,F,Rest...)(M m, P pred, F fun, Rest rest) {
    if (pred(m)) {
        return fun(m);
    }
    else static if (Rest.length > 0) {
        return cond(m, rest);
    }
}

/+
Algebraic!(ParameterTypeTuples!Funs) amatch(AType, Funs...)(AType alg)
if (__traits(compiles, AType.AllowedTypes)
&& is(ParameterTypeTuples!Funs == AType.AllowedTypes))
{
    Algebraic!(ReturnTypeTuples!Funs) result;
    foreach(fun; Funs)
    {
        auto p = alg.peek!(ReturnTypeTuple!fun[0]);
        if (p !is null)
        {
            result = fun(*p);
            break;
        }
    }
    return result;
}
+/


