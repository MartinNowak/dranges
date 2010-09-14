// Written in the D programming language

/**
This module contains all the function-related templates.
Its main use used to be to generate functions from strings, with the $(M naryFun) template,
an extension of $(M std.functional.unaryFun) and $(M binaryFun). Now, it presents a nice collection
of adaptors and transformers: functions or templates acting on functions to transform them.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.functional;

import std.algorithm,
       std.array,
       std.bigint,
       std.contracts,
       std.conv,
       std.functional,
       std.math,
       std.metastrings,
       std.range,
       std.stdio,
       std.string,
       std.traits,
       std.typecons,
       std.typetuple;

import dranges.algorithm,
       dranges.patternmatch,
       dranges.predicate,
       dranges.range,
       dranges.templates,
       dranges.traits,
       dranges.tuple,
       dranges.typetuple;
/**
Gives the _arity of a function: unary, binary, etc. A 0-args function has an _arity of 0.

----
int foo0() { return 0;}
int foo1(int a) { return a;}
int foo2(int a, int b) { return a+b;}

assert(arity!foo0 == 0);
assert(arity!foo1 == 1);
assert(arity!foo2 == 2);
----

It does not work on non-instantiated template functions (because they
are not functions) and gives an _arity of 1 for variadic functions, because
their variadic list is considered as one arg.
----
T foo(T)(T t) { ...};
auto a = arity!foo; // error !
auto b = arity!(foo!int); // OK.
//
int foov(int a...) { return 0;}
assert(arity!foov == 1);
----

See_Also: $(M dranges.templates.TemplateFunArity).
*/
template arity(alias fun) if (isFunction!fun) {
    enum size_t arity = ParameterTypeTuple!(fun).length;
}

template arity(string fun)
{
    alias aritySImpl!(" " ~ fun ~ " ",0).result arity;
}

unittest {
    int foo0() { return 0;}
    int foo1(int a) { return a;}
    int foo2(int a, int b) { return a+b;}
    T foo3(T, U)(T t, T tt, U u) { return t;} // templated
    assert(arity!foo0 == 0);
    assert(arity!foo1 == 1);
    assert(arity!foo2 == 2);
    assert(!__traits(compiles, arity!foo3)); // does not work on non-instantiated functions
    assert(arity!(foo3!(int,double)) == 3);  // foo3!(int, double) is a 3-args function

    int foov(int a...) { return 0;}
    assert(arity!foov == 1);
}

/// Given a bunch of functions names, gives the typetuple of their return types. Used by $(M juxtapose).
template ReturnTypes(Funs...)
{
    alias MapOnAlias!(ReturnType, Funs) ReturnTypes;
}

/// Given a bunch of functions names, gives the (flattened) typetuple of their return values. Used by $(M juxtapose).
template ParameterTypeTuples(alias fun, Rest...)
{
    alias MapOnAlias!(ParameterTypeTuple, fun, Rest) ParameterTypeTuples;
}

template SumOfArity(size_t zero, alias fun)
{
    enum size_t SumOfArity = zero + arity!fun;
}

template SumOfArities(F...)
{
    alias StaticScan!(SumOfArity, 0, F) SumOfArities;
}

template SumOfReturn(size_t zero, alias fun)
{
    static if (is(ReturnType!fun == void))
        enum size_t SumOfReturn = zero;
    else
        enum size_t SumOfReturn = zero + 1;
}

template SumOfReturns(Funs...)
{
    alias StaticScan!(SumOfReturn, 0, Funs) SumOfReturns;
}


/**
Takes n functions and create a new one, taking as arguments the concatenation of all input functions
arguments and returning a tuple of their results. It will deal correctly with nullary (0-arg) functions
by inserting their return value at the right place and with void-returning functions.
Do not use variadic functions, though.

This template is very useful when dealing with tuple-returning ranges.

Example:
----
int foo(int i) { return i*i;}       // int -> int
int bar() { return 0;}              // ()  -> int
void baz(string s) {}               // string -> ()
double[] quux(double d, double[] f) // (double,double[]) -> double[]
    { return f ~ d;}

alias juxtapose!(foo,bar,baz,quux) jux; // jux takes (int,string, double, double[]), returns Tuple!(int,int,double[]);

auto ir = [0,1,2,3,4,5];
auto sr = ["abc", "def","ghijk"];
auto dr = [3.14,2.78,1.00,-1.414];
auto fr = [[0.1,0.2], [0.0,-1.0,-2.0]];

auto m = tmap!jux(ir,sr,dr,fr);
----

Note: another, more mathematical way, to look at it is that $(M _juxtapose) creates a function whose type is the product the input functions' types.
In D, product of types are tuples.
*/
template juxtapose(Funs...)
{
    Tuple!(StaticFilter!(isNotVoid, ReturnTypes!Funs)) juxtapose(ParameterTypeTuples!Funs params) {
        typeof(return) result;
        alias SumOfArities!Funs arities;
        alias SumOfReturns!Funs returns;
        foreach(i, Fun; Funs) {
            enum firstParam = arities[i];
            enum lastParam = firstParam + arity!(Fun);
            static if (returns[i] != returns[i+1])
                result.field[returns[i]] = Fun(params[firstParam..lastParam]);
        }
        return result;
    }
}

unittest
{
    int foo(int i) { return i*i;}       // int -> int
    int bar() { return 0;}              // ()  -> int
    void baz(string s) {}               // string -> ()
    double[] quux(double d, double[] f) // (double,double[]) -> double[]
        { return f ~ d;}

    alias juxtapose!(foo,bar,baz,quux) jux; // jux takes (int,string, double, double[]), returns Tuple!(int,int,double[]);

    auto ir = [0,1,2,3,4,5];
    auto sr = ["abc", "def","ghijk"];
    auto dr = [3.14,2.78,1.00,-1.414];
    auto fr = [[0.1,0.2], [0.0,-1.0,-2.0]];

    auto m = tmap!jux(ir,sr,dr,fr);
}
/+
template juxtapose2(F...)
{
    Tuple!(ReturnTypes!F) juxtapose2(Tuple!(ParameterTypeTuples!F) params) {
        typeof(return) result;
        alias SumOfArities!F arities;
        foreach(i, Unused; F) {
            enum firstParam = arities[i];
            enum lastParam = firstParam + arity!(F[i]);
            result.field[i] = F[i](params.expand[firstParam..lastParam]);
        }
        return result;
    }
}
+/

template isNotVoid(T)
{
    enum bool isNotVoid = !is(T == void);
}

struct FlipnR(alias fun)
{
    size_t n;
    typeof(fun(R.init, 0)) opCall(R)(R r) if (isForwardRange!R)// && is(typeof(fun(r,n))))
    {
        return fun(r,n);
    }
}

/**
Flip and curry range functions, like $(M take), $(M drop), etc. These take a range and a size_t arguments, like $(M take(r,3)), etc.
But sometimes, you just want to create a curried function that will act on any range.

Example:
----
alias flipn!take takeN; // takeN is a generic function, waiting for a number of elements to take.
auto take3 = takeN(3);  // take3 is a generic function, taking 3 elements on any range (returns take(range,3))

auto threes = map!take3([[0,1,2,3,4,5],[6,7,8,9], [10]]); // get the first three elements of each range
auto witness =          [[0,1,2],      [6,7,8],   [10]];
foreach(i, elem; witness)  {assert(equal(elem, threes.front)); threes.popFront;}
----
*/
FlipnR!fun flipn(alias fun)(size_t n)
{
    FlipnR!(fun) tnr;
    tnr.n = n;
    return tnr;
}

unittest
{
    auto rr = [[0,1,2,3,4,5],[6,7,8,9], [10]];

    alias flipn!take takeN; // takeN is a higher-order function, waiting for a number of elements to take.
    auto take3 = takeN(3);  // take3 is a generic function, taking 3 elements on any range (returns take(range,3))

    auto threes = map!take3(rr); // get the first three elements of each range
    auto witness = [[0,1,2],[6,7,8],[10]];
    foreach(elem; witness)
    {
        assert(equal(elem, threes.front));
        threes.popFront;
    }

    auto take0 = takeN(0);
    auto zeroes = map!take0(rr);
    foreach(elem; zeroes) assert(elem.empty);

    auto take100 = takeN(100);
    auto all = map!take100(rr);
    foreach(elem; rr) {assert(equal(elem, all.front)); all.popFront;}
}


/**
Flips (reverses) the arguments of a function. It also works for template functions, even
variadic ones. Do not use it on standard variadic functions, though.

Example:
----
int sub(int i, int j) { return i-j;}
int one(int i) { return i;}
double three(double a, int b, string c) { return a;}

alias flip!sub fsub;
alias flip!one fone;
alias flip!three fthree;

assert(fsub(1,2) == sub(2,1));
assert(fone(1) == one(1));
assert(fthree("abc", 0, 3.14) == three(3.14, 0, "abc"));

string conj(A,B)(A a, B b)
{
    return to!string(a)~to!string(b);
}

string conjAll(A...)(A a) // variadic template function
{
    string result;
    foreach(i,elem;a) result ~= to!string(elem);
    return result;
}

alias flip!conj fconj;
alias flip!conjAll fconjAll;

assert(fconj(1,2) == "21");
assert(fconjAll(1,2,3,4) == "4321");
----
*/
template flip(alias fun)
{
    static if (isFunctionType!(typeof(fun)))
        ReturnType!fun flip(ReverseTypes!(ParameterTypeTuple!fun) rargs)
        {
            return fun(reverseTuple(tuple(rargs)).expand);
        }
    else
        typeof(fun(Init!(ReverseTypes!T))) flip(T...)(T rargs)
        {
            return fun(reverseTuple(tuple(rargs)).expand);
        }
}

version(unittest)
{
    string conj(A,B)(A a, B b)
    {
        return to!string(a)~to!string(b);
    }

    string conjAll(A...)(A a)
    {
        string result;
        foreach(i,elem;a) result ~= to!string(elem);
        return result;
    }
}

unittest
{
    int sub(int i, int j) { return i-j;}
    int one(int i) { return i;}
    int none() { return 0;}
    double three(double a, int b, string c) { return a;}

    alias flip!sub fsub;
    alias flip!one fone;
    alias flip!none fnone;
    alias flip!three fthree;

    assert(fsub(1,2) == sub(2,1));
    assert(fone(1) == one(1));
    assert(fnone() == none());
    assert(fthree("abc", 0, 3.14) == three(3.14, 0, "abc"));

    alias flip!conj fconj;
    alias flip!conjAll fconjAll;

    assert(fconj(1,2) == "21");
    assert(fconjAll(1,2,3,4) == "4321");
}

/**
Takes a D function, and curries it (in the Haskell sense, not as Phobos' $(M std.functional._curry)): given
a n-args function, it creates n 1-arg functions nested inside one another. When
all original arguments are reached, it returns the result. It's useful to make 'incomplete'
functions to be completed by ranges elements.

Example:
----
int add(int i, int j) { return i+j;}
alias curry!add cadd; // cadd waits for an int, will return an int delegate(int)
auto add3 = cadd(3); // add3 is a function that take an int and return this int + 3.

auto m = map!add3([0,1,2,3]);
assert(equal(m, [3,4,5,6]));

bool equals(int i, int j) { return i==j;}
alias curry!equals cequals;
auto equals4 = cequals(4); // equals4 is a function taking an int and return true iff this int is 4.
auto f = filter!equals4([2,3,4,5,4,3,2,2,3,4]);
assert(equal(f, [4,4,4]));
----

What's fun is that it'll work for template functions too.

Example:
----
string conj(A, B)(A a, B b)
{
    return to!string(a)~to!string(b);
}

alias curry!conj cconj;
auto c1 = cconj(1); // c1 is a template function waiting for any type.
assert(c1('a') == "1a");
----
BUG:
for now, it does not verify the compatibility of types while you give it the arguments. It's only
at the end that it sees whether or not it can call the function with these arguments.
Example:
----
// given a function like this, with dependencies between the arguments' types:
A foo(A,B,C)(A a, Tuple!(B,A) b, Tuple!(C,B,A) c) { return a+b.field[1]+c.field[2];}
// if you curries it and gives it an int as first argument, the returned template function should really be:
int foo2(B,C)(Tuple!(B,int) b) { return anotherFunction;}
// because we now know A to be an int...
----
*/
template curry(alias fun)
{
    static if (isFunction!fun)
        enum curry =  mixin(curryImpl!(fun, "", ParameterTypeTuple!fun));
    else // template function
        enum curry = curriedFunction!(fun)();
}

template curryImpl(alias fun, string xs, T...)
{
    static if (T.length == 0)
        enum curryImpl = "&fun";
    else static if (T.length == 1)
        enum curryImpl = "(" ~ T[0].stringof  ~ " x1) { return fun(" ~ xs ~ "x1);}";
    else
        enum curryImpl = "(" ~ T[0].stringof  ~ " x" ~ to!string(T.length) ~ ") { return "
                            ~ curryImpl!(fun,xs ~ "x" ~ to!string(T.length) ~ ", ", T[1..$]) ~ ";}";
}

struct CurriedFunction(alias fun, T...) /+if (T.length)+/
{
    T _t;
    static if (T.length)
        void initialize(T t) { _t = t;}

    template OpCallType(U...)
    {
        static if (is (typeof(fun(Init!T, Init!U))))
            alias typeof(fun(Init!T, Init!U)) OpCallType;
        else
            alias CurriedFunction!(fun, T, U) OpCallType;
    }

    OpCallType!U opCall(U...)(U u)
    {
        static if(is(typeof(fun(_t, u))))
            return fun(_t,u);
        else
        {
            CurriedFunction!(fun, T, U) cf;
            static if (U.length) cf.initialize(_t, u);
            return cf;
        }
    }
}

CurriedFunction!(fun, TypeTuple!()) curriedFunction(alias fun)()
{
    CurriedFunction!(fun, TypeTuple!()) cf;
    return cf;
}

unittest
{
    int add(int i, int j) { return i+j;}
    alias curry!add cadd; // cadd waits for an int, will return an int delegate(int)
    auto add3 = cadd(3); // add3 is a function that take an int and return this int + 3.

    auto m = map!add3([0,1,2,3]);
    assert(equal(m, [3,4,5,6]));

    bool equals(int i, int j) { return i==j;}
    alias curry!equals cequals;
    auto equals4 = cequals(4); // equals4 is a function taking an int and return true iff this int is 4.
    auto f = filter!equals4([2,3,4,5,4,3,2,2,3,4]);
    assert(equal(f, [4,4,4]));
}

struct InvertibleFun(A, B)
{
    B delegate(A) fun;
    A delegate(B) funInv;

    AB!(A,B,T) opCall(T)(T t) if (is(T == A) || is(T == B))
    {
        static if (is(T == A))
            return fun(t);
        else
            return funInv(t);
    }
}

/**
Takes two delegates: one from $(M A) to $(M B), the other from $(M B) to $(M A). $(M A) and $(M B) must be different types.
The functions are supposed to be the inverse of one another (that is: f(g(x)) == x), but that's not checked.
$(M _invertibleFun) is then a function that accepts either a $(M A) or a $(M B) and then returns a $(M B) or a $(M A).
*/
InvertibleFun!(A,B) invertibleFun(A, B)(B delegate(A) fun, A delegate(B) funInv)
{
    InvertibleFun!(A,B) ifun;
    ifun.fun = fun;
    ifun.funInv = funInv;
    return ifun;
}

struct Apply(T...)
{
    T value;

    typeof(F.init(Init!T)) opCall(F)(F fun)
    {
        return fun(value);
    }
}

/**
Takes a value argument and creates a function (in fact, a struct with an opCall) that will accept any delegate
and _apply it to the original value. It's useful when you want to map a certain value on a range of functions:
just map $(M _apply!value) to the range.

Example:
----
int f0(int i) { return i;}
int f1(int i) { return i*i;}
int f2(int i) { return i*i*i;}

auto apply4 = apply(4); // will call any function with '4' as argument.
auto rangeFun = [&f0, &f1, &f2];
auto map4 = map!apply4(rangeFun);
assert(equal(map4, [4, 4*4, 4*4*4]));

// This works for n-args functions too:
double g0(int i, double d) { return i+d;}

auto apply123 = apply(1, 2.30);
assert(apply123(&g0) == 3.30);
----
*/
Apply!T apply(T...)(T value)
{
    Apply!T app;
    foreach(i, Type; T) app.value[i] = value[i];
    return app;
}

unittest
{
    int f0(int i) { return i;}
    int f1(int i) { return i*i;}
    int f2(int i) { return i*i*i;}

    auto apply4 = apply(4); // will call any function with '4' as argument.
    auto rangeFun = [&f0, &f1, &f2];
    auto map4 = map!apply4(rangeFun);
    assert(equal(map4, [4, 4*4, 4*4*4]));

    // This works for n-args functions too:
    double g0(int i, double d) { return i+d;}

    auto apply123 = apply(1, 2.30);
    assert(apply123(&g0) == 3.30);
}

/**
Transforms a standard function into a destructuring one. Given:
----
int foo(int a, int b, int c) {}
----
then, $(M _destructured!foo) is a function that accepts three $(M int)s as arguments, but also $(M Tuple!(int,int,int))
or $(M int[]) or $(M int[3]) or even any class $(M C) or struct $(M S) if $(M C.tupleof)/$(M S.tupleof) gives three $(M int)s. In effect,
$(M _destructured!foo) will try to destructure (decompose, crack open, if you will) anything passed to it, to find three $(M int)s in a row to give
to $(M foo).

Note: It's still 'in construction', as it depends on the $(M __()) function from $(M dranges.reftuple). The doc
should be extended.
TODO: also if t is itself a tuple __(params) = t;
*/
template destructured(alias fun)
{
    ReturnType!fun destructured(T...)(T t)
        if(__traits(compiles, {
                                ParameterTypeTuple!fun params;
                                _(params) = tuple(t);
                                return fun(params);
                              }))
    {
        ParameterTypeTuple!fun params;
        _(params) = tuple(t);
        return fun(params);
    }
}

/**
Transforms a function $(M foo) taking a $(M T) into a function accepting a $(M T[]) as an argument
and which applies $(M foo) to each element of the array, returning the resulting array.

Example:
----
int foo(int i) { return i*i;}
alias mapper!foo mfoo;

assert(mfoo([0,1,2,3,4]) == [0,1,4,9,16]);
----

If $(M foo) takes more than one argument, $(M _mapper!foo) waits for a $(M Tuple!(Args)[]) or accepts
a variadic number of arguments, as long as the types and their numbers correspond.

Example:
----
int bar(int i, double j, string s) { return (to!int(i*j));}
alias mapper!bar mbar;

assert(mbar(1,3.14,"ab", 2,-0.5,"hello!", 0,0,"") == [3,-3,0]);
----
TODO: expand tuples [tuple(a,b), tuple(a,b), ...]
*/
template mapper(alias fun)
{
    auto mapper(T...)(T args) {
        static if (T.length >1 || (T.length == 1 && !isDynamicArray!(T[0]))) // args as tuple
        {
            static if (is(ParameterTypeTuple!fun)
                       && (ParameterTypeTuple!fun).length > 1
                       && T.length % (ParameterTypeTuple!fun).length == 0) // more than one param
            {
                enum nargs = (ParameterTypeTuple!fun).length;
                ReturnType!fun[] result = new ReturnType!fun[T.length / nargs];
                foreach(i, Arg; T) {
                    static if (i % nargs == 0) result[i/nargs] = fun(args[i..i+nargs]);
                }
                return result;
            }
            else // one param or we cannot determine it (template function, for example)
            {
                alias typeof(fun(CommonType!T.init)) RT;
                RT[] result = new RT[args.length];
                foreach(i,Arg; T) result[i] = fun(args[i]);
                return result;
            }
        }
        else    // args as array
        {
            alias typeof(fun(T[0][0].init)) RT;
            RT[] result = new RT[args[0].length];
            foreach(i,arg; args[0]) result[i] = fun(arg);
            return result;
        }
    }
}

unittest
{
    int foo(int i) { return i*i;}
    alias mapper!foo mfoo;

    assert(mfoo([0,1,2,3,4]) == [0,1,4,9,16]);

    int bar(int i, double j, string s) { return (to!int(i*j));}
    alias mapper!bar mbar;

    assert(mbar(1,3.14,"ab", 2,-1.5,"hello!", 0,0,"") == [3,-3,0]);
}

/**
Transforms a function $(M foo) accepting a $(M T) into a function accepting
a $(M Tuple!(T,T,T,...T)) (or any tuple with compatible types). It will apply
$(M foo) to all elements of the tuple and return the tuple of these results.

Example:
----
int foo(int i) { return i*i;}
alias tupler!foo tfoo;
auto t = tuple(0,1,2,3,4);

assert(tfoo(t) == tuple(0,1,4,9,16));
----
*/
template tupler(alias fun)
{
    auto tupler(T)(T tup) if (is(typeof(fun(CommonType!(T.Types).init))))
    {
        alias typeof(fun(CommonType!(T.Types).init)) RT;
        alias TypeNuple!(RT, T.Types.length) TRT;
        TRT result;
        foreach(i, Type; TRT) result[i] = fun(tup.field[i]);
        return tuple(result);
    }
}

unittest
{
    int foo(int i) { return i*i;}
    alias tupler!foo tfoo;
    auto t = tuple(0,1,2,3,4);

    assert(tfoo(t) == tuple(0,1,4,9,16));
}

/// The void function: takes any arguments, returns $(M void).
void voidFun(...) {}

/// The _null function: takes no argument, returns $(M void).
void nullFun() {}

/**
Takes any value, returns a constant function: one that accepts any arguments and will always return
the initial value. If called with no argument, it will produce the equivalent of $(M voidFun).

Example:
----
auto one = constantFun(1);
assert(equal(map!one(["a","b","abc"]), [1,1,1]));
----
*/
T[0] delegate(...) constantFun(T...)(T t) if (T.length == 1)
{
    return (...) { return t[0];};
}

/// ditto
Tuple!T delegate(...) constantFun(T...)(T t) if (T.length > 1)
{
    return (...) { return tuple(t);};
}
/// ditto
void delegate(...) constantFun(T...)(T t) if (T.length == 0)
{
    return (...) { return;};
}

unittest
{
    auto one = constantFun(1);
    assert(equal(map!one(["a","b","abc"]), [1,1,1]));
}

//template ExtendFunType(alias fun, T...)
//{
//    static if (is(typeof(fun(T.init))))
//        alias typeof(fun(T.init)) ExtendFunType;
//    else
//        alias T[0] ExtendFunType;
//}

struct ExtendFun(alias fun)
{
    typeof(fun(Init!T)) opCall(T...)(T t) if (T.length && is(typeof(fun(t))))
    {
        return fun(t);
    }

    T[0] opCall(T...)(T t) if (T.length && !is(typeof(fun(t))))
    {
        return t[0];
    }
}

/**
Takes a function $(M foo) and 'extends' it, allowing it to accept any type of argument.
If the arguments types are compatible with $(M foo), returns foo(args) otherwise, it just returns
the argument.

That may seem a strange template to define, but it's quite useful for mapping a tuple (see $(M dranges.tuple2.mapTuple)).
Suppose you have a tuple and what to change only the strings in it. Define $(M foo) to act on strings, extend it with
$(M _extendFun!foo) and voila, you can then map $(M _extendFun!foo) on your tuple: the strings will be transformed, leaving the
other types untouched. I learnt the trick from a Haskell article.

Example:
----
import dranges.tuple;

auto t = tuple("bin", 1024, 3.14159,
               "src", 0,    1.0,
               "myDirectory/foo", 100, -2.3);

string foo(string s) { return "std/" ~ s;}

auto efoo = extendFun!foo; // beware: it's not alias extendFun!foo efoo;, as for other templates around here.

auto t2 = mapTuple ! efoo (t);

assert(t2 == tuple("std/bin", 1024, 3.14159,
                   "std/src", 0,    1.0,
                   "std/myDirectory/foo", 100, -2.3));
----
*/
ExtendFun!fun extendFun(alias fun)()
{
    ExtendFun!(fun) efun;
    return efun;
}

version(unittest)
{
    import dranges.tuple;
    string foo(string s) { return "std/" ~ s;}
}

unittest
{
    auto t = tuple("bin", 1024, 3.14159,
                   "src", 0,    1.0,
                   "myDirectory/foo", 100, -2.3);

    auto efoo = extendFun!foo;

    auto t2 = mapTuple ! efoo (t);

    assert(t2 == tuple("std/bin", 1024, 3.14159,
                       "std/src", 0,    1.0,
                       "std/myDirectory/foo", 100, -2.3));
}

struct ExtendFun0(alias fun, D)
{
    D defaultValue;

    typeof(fun(Init!T)) opCall(T...)(T t) if (is(typeof(fun(t))))
    {
        return fun(t);
    }


    D opCall(T...)(T t) if (!is(typeof(fun(t))))
    {
        return defaultValue;
    }
}

/**
Same as before, but with a default value returned when extendFun is offered
an arg that $(M foo) cannot accept. The default value can be of any type.

Example:
----
import dranges.tuple;

auto t = tuple("bin", 1024, 3.14159,
               "src", 0,    1.0,
               "myDirectory/foo", 100, -2.3);

string foo(string s) { return "std/" ~ s;}

auto efoo = extendFun0!foo(0);

auto t2 = mapTuple ! efoo (t);

assert(t2 == tuple("std/bin",               0, 0,
                   "std/src",               0, 0,
                   "std/myDirectory/foo",   0, 0));
----
*/
ExtendFun0!(fun, D) extendFun0(alias fun, D)(D defaultValue)
{
    ExtendFun0!(fun,D) efun;
    efun.defaultValue = defaultValue;
    return efun;
}

unittest
{
    auto t = tuple("bin", 1024, 3.14159,
                   "src", 0,    1.0,
                   "myDirectory/foo", 100, -2.3);

    auto efoo0 = extendFun0!foo(0); // foo is defined in a version(unittest) statement higher up in the code

    auto t2 = mapTuple ! efoo0 (t);

    assert(t2 == tuple("std/bin",               0, 0,
                       "std/src",               0, 0,
                       "std/myDirectory/foo",   0, 0));
}

/**
This is just a wrapper around the $(M match) function found in $(M dranges.pattermatch), here to emphasize
the way $(M match) is just a many-types-to-many-types 'function'. Explained a bit more clearly, $(M _eitherFun)
takes any number of functions and keep them near its hot little heart. When passed an argument, it will
successively test each function and returns the result of the first one that matches. No match means it will
throw a NoMatch exception. Functions are tested the same order they were passed as arguments.

How is this different from overloading, will you ask? I'm glad you did:

$(UL
  $(LI first, you can use it to 'group' many different functions, from different origins and different names.)
  $(LI second (and that may be the most important point), it's a template, so the return
type of $(M _eitherFun) can be different for each argument type. So you can use it to map a range, but also a tuple, with $(M dranges.tuple2.mapTuple)).
  $(LI third, it accepts template functions. In fact, it even accepts 'string' functions, as in "a+b*c-d.expand". See the $(M patternmatch)
module documentation for more explanations.)
  $(LI fourth, once it's defined, you can pass it around as one entity. Most notably, it can becomes the argument
    of another meta-function there or even the argument to another $(M _eitherFun!))
)

So, in functional languages terms, it's a sum of functions (just as $(M juxtapose) is a product).

Example:
----
int    f1(int i) { return i;}
double f2(double d) { return d*d;}
int    f3(int i, string s) { return i;}
string f4(string s, int i) { return s;}

alias eitherFun!(f1,f2,f3,f4) efun; // efun accepts either an int, or a double, or a (int,string) or a (string, int)

assert(efun(1) == 1);
assert(efun(1.5) == 2.25);
assert(efun(1,"abc") == 1);
assert(efun("abc",1) == "abc");

// Let's extend it, then.
int[] f5(int[] i) { return i.reverse;}

alias eitherFun!(efun, f5) efun5;   // efun5 will test f1, then f2, ... and f5 at last resort.
// alias eitherFun(f5, efun) efun5bis would have tested f5 first, then f1, ...

assert(efun5(1) == 1);              // efun5 is like efun
assert(efun5(1.5) == 2.25);
assert(efun5(1,"abc") == 1);
assert(efun5("abc",1) == "abc");
assert(efun5([0,1,2]) == [2,1,0]);  // except it also accepts an array of ints as argument.
----

Note: as said before, functions are tested in the same order they were passed as arguments. So a function can 'swallow' arguments
that could have been accepted by another, downstream function.
*/
template eitherFun(F...)
{
    alias match!(StaticMap!(naryFun, F)) eitherFun;
}

unittest
{
    int f1(int i) { return i;}
    double f2(double d) { return d*d;}
    int f3(int i, string s) { return i;}
    string f4(string s, int i) { return s;}

    int[] f5(int[] i) { return i.reverse;}

    alias eitherFun!(f1,f2,f3,f4) efun;
    assert(efun(1) == 1);
    assert(efun(1.5) == 2.25);
    assert(efun(1,"abc") == 1);
    assert(efun("abc",1) == "abc");

    alias eitherFun!(efun, f5) efun5;

    assert(efun5(1) == 1);
    assert(efun5(1.5) == 2.25);
    assert(efun5(1,"abc") == 1);
    assert(efun5("abc",1) == "abc");
    assert(efun5([0,1,2]) == [2,1,0]);
}

/**
A simple adapter, when you have a complicated function you do not (or cannot) want to touch. It
applies the $(M pre) preprocessing to the arguments, calls fun and then postprocess the result. The
default for post is "a", that is the identity string function. So the two args version of $(M _adaptFun)
just deals with adapting the arguments.
*/
template adaptFun(alias pre, alias fun, alias post = "a")
{
    typeof(naryFun!post(naryFun!fun(naryFun!pre(Init!T)))) adaptFun(T...)(T t)
    {
        return naryFun!post(naryFun!fun(naryFun!pre(t)));
    }
}


/**
The composition 'power' of a function: $(M fun(fun(fun(x)...))), n times. n == 1 is the same
as $(M fun) and n = 0 is the identity function (just returns the arguments).

Example:
----
int inc(int i) { return i+1;}
string conc(string s) { return s ~ s;}

alias powerFun!(inc, 5) plus5; // calls inc(inc(inc(inc(inc(t))))), so returns t+5
alias powerFun!(inc, 1) plus1;
alias powerFun!(inc, 0) plus0;

assert(plus5(4) == 9);
assert(plus1(4) == 5);
assert(plus0(4) == 4);

alias powerFun!(conc, 2) conc2;

assert(conc("abc") == "abcabc");
assert(conc2("abc") == "abcabcabcabc");
assert(conc2("abc") == conc(conc("abc")));
----
*/
template powerFun(alias fun, size_t n)
{
    auto powerFun(T...)(T args)
    {
        return wrapCode!(fun, n)(args);
    }
}

unittest
{
    int inc(int i) { return i+1;}
    string conc(string s) { return s ~ s;}

    alias powerFun!(inc, 5) plus5;
    alias powerFun!(inc, 1) plus1;
    alias powerFun!(inc, 0) plus0;

    assert(plus5(4) == 9);
    assert(plus1(4) == 5);
    assert(plus0(4) == 4);

    alias powerFun!(conc, 2) conc2;

    assert(conc("abc") == "abcabc");
    assert(conc2("abc") == "abcabcabcabc");
    assert(conc2("abc") == conc(conc("abc")));
}

/**
Takes a function and store default values for its last arguments. For a n-arg function,
you can provided d default values, d being between 0 and n. These values will be applied
to the last d arguments.

Example:
----
int foo(int i, int j, double k) { return i+j+to!int(k);}
auto dfoo = withDefaultValues!(foo)(2,1.5); // two default values provided -> 2 for j and 1.5 for k
                                            // so dfoo can accept 1, 2 or 3 arguments.

assert(dfoo(1)         == foo(1, 2, 1.5)); // 1 arg given -> dfoo use two defaults
assert(dfoo(1, 1)      == foo(1, 1, 1.5)); // 2 args -> one default
assert(dfoo(1, 1, 0.5) == foo(1, 1, 0.5)); // 3 args -> no default
----

Most of the time, $(M _withDefaultValues) will determine the arity of your function. In case of doubt, you can provide it as
a second template argument, like this:
----
A bar(A,B)(A a0, A a1, B a2, Tuple!(A,B) a3) { return a0;} // template function, withDefaultValues cannot determine the arity is 4
auto dbar = withDefaultValues!(bar, 4)(2, tuple(2, 3.14));
----

TODO: No, that should be possible now that I have a template to determine the arity even of template functions.
*/
DefaultValues!(fun, arity!fun, D) withDefaultValues(alias fun, D...)(D defaults) if (D.length <= arity!fun)
{
    DefaultValues!(fun, arity!fun, D) def;
    def._defaults = defaults; // to avoid some conflict between this() and opCall() in the struct
    return def;
}

/// ditto
DefaultValues!(fun, arity, D) withDefaultValues(alias fun, size_t arity, D...)(D defaults) if (D.length <= arity)
{
    DefaultValues!(fun, arity, D) def;
    def._defaults = defaults; // to avoid some conflict between this() and opCall() in the struct
    return def;
}

struct DefaultValues(alias fun, size_t arity, D...)
{
    D _defaults;
    auto opCall(T...)(T t)
    {
        static if ( arity - D.length <= T.length && T.length <= arity )
            return naryFun!fun(t,_defaults[D.length+T.length-arity..$]);
        else
            static assert(false, "withDefaultValues: bad number of arguments. Need between "
                                ~ to!string(arity - D.length) ~ " and " ~ to!string(arity) ~ " arguments, got " ~ to!string(T.length)~".");
    }
}

version(unittest)
{
    int foo3(int i, int j, double k) { return i+j+to!int(k);}
}

unittest
{
    auto dfoo = withDefaultValues!(foo3)(2,1.5); // two default values provided -> for j and for k
                                                // so dfoo can accept 1, 2 or 3 arguments.

    assert(dfoo(1)         == foo3(1, 2, 1.5)); // 1 arg given -> dfoo use two defaults
    assert(dfoo(1, 1)      == foo3(1, 1, 1.5)); // 2 args -> one default
    assert(dfoo(1, 1, 0.5) == foo3(1, 1, 0.5)); // 3 args -> no default
}

/**
Accepts a $(M class) or $(M struct) name as template argument and creates a factory function that creates
the corresponding $(M class)/$(M struct). It allows one to map a constructor on a range, to create a
range of classes. It's not possible normally.

Example:
----
class C {
    int i;
    this(int _i) { i = _i;}
}

auto arr = [0,1,2,3];

// auto m = map!C(arr); // does not work.
alias construct!C CC;
auto m = map!CC(arr); // works;
// m is like [new C(0), new C(1), new C(2), new C(3)]
----

What's fun is when you use it on many-args constructors or structs:
----
struct S { int i; double d;}

alias construct!S CS;

auto s = tmap!CS([0,1,2,3], [-1.1,-2.2,3.3,4.]); // Yeah, tmap
assert(equal(s, [S(0,-1.1), S(1, -2.2), S(2, 3.3), S(3, 4.0)]));
----
*/
template construct(Struct) if (is(Struct == struct))
{
    Struct construct(T...)(T t)
    {
        return Struct(t);
    }
}

/// ditto
template construct(Class) if (is(Class == class))
{
    Class construct(T...)(T t)
    {
        return new Class(t);
    }
}

version(unittest)
{
    class C {
        int i;
        this(int _i) { i = _i;}
    }
}

unittest
{

    auto arr = [0,1,2,3];

    // auto m = map!C(arr); // does not work.
    alias construct!C CC;
    auto m = map!CC(arr); // works;

    struct S { int i; double d;}

    alias construct!S CS;

    auto s = tmap!CS([0,1,2,3], [-1.1,-2.2,3.3,4.]); // Yeah, tmap
    assert(equal(s, [S(0,-1.1), S(1, -2.2), S(2, 3.3), S(3, 4.0)]));
}

/**
Transforms a function accepting $(M (T, T, T, ...)) into a function accepting $(M (T[])). The new function
will consume as many arguments as needed, but won't throw if there are more.

Example:
----
int foo(int i, int j, int k) { return i+j+k;}

alias arrayify!foo afoo;
assert(afoo([1,2,3]) == 1+2+3);
----
*/
template arrayify(alias fun) if (isFunction!fun && is(CommonType!(ParameterTypeTuple!fun)))
{
    ReturnType!fun arrayify(CommonType!(ParameterTypeTuple!fun)[] args)
    {
        alias TypeNuple!(CommonType!(ParameterTypeTuple!fun), ParameterTypeTuple!fun.length) TN;
        TN tn;
        foreach(i, Type; TN) tn[i] = args[i];
        return fun(tn);
    }
}

/**
Transforms a function accepting a $(M (T,T,T,...)) into a function accepting a range of $(M T)s.
*/
template rangify(alias fun) if (isFunction!fun && is(CommonType!(ParameterTypeTuple!fun)))
{
    ReturnType!fun rangify(R)(R range) if (isForwardRange!R && is(ElementType!R == CommonType!(ParameterTypeTuple!fun)))
    {
        alias TypeNuple!(CommonType!(ParameterTypeTuple!fun), ParameterTypeTuple!fun.length) TN;
        TN tn;
        foreach(i, Type; TN) { tn[i] = range.front; range.popFront;}
        return fun(tn);
    }
}

/**
Transforms a function into a tuple-accepting function. Useful to map a standard function
on a tuple-producing range. A parameterless function (zero args) is left untouched.

See_Also: $(M tmap), $(M tfilter), $(M comp) and $(M pComp) in $(M dranges.algorithm).

Example:
----
string foo3(int a, string b, double c) {
    return to!string(a) ~ "+" ~ b ~ "+" ~ to!string(c);
}

auto tfoo3 = tuplify!foo3;
auto t = tuple(1, "a", 3.0);
auto result = tfoo3(t);
assert(result == "1+a+3");

string foo() {
    return "aha";
}
auto tfoo = tuplify!foo;
assert(tfoo() == "aha");
----
*/
template tuplify(alias fun) {
    static if(isFunction!fun)
        alias tuplifyImpl!(fun).result tuplify;
//    else static if (is(fun = struct)) // struct name -> constructor
//        alias construct!fun
}

template tuplifyImpl(alias fun) if (isFunction!fun) {
    alias ReturnType!fun R;
    alias ParameterTypeTuple!fun A;
    static if (A.length > 0) {
        R result(Tuple!(A) tup) {
                return fun(tup.field);
        }
    }
    else {
        R result() {
            return fun();
        }
    }
}


//
//auto tuplify(R, A...)(R delegate(A) fun) {
//    static if (A.length == 0) {
//        return fun;
//    }
//    else {
//        R tuplified(Tuple!(A) tup) {
//            return tupleApply!fun(tup);
//        }
//        return &tuplified;
//    }
//}
//
unittest {
    string foo3(int a, string b, double c) {
        return to!string(a) ~ "+" ~ b ~ "+" ~ to!string(c);
    }

    alias tuplify!foo3 tfoo3;
    auto t = tuple(1, "a", 3.0);
    auto result = tfoo3(t);
    assert(result == "1+a+3");

    string foo() { return "aha";}
    alias tuplify!foo tfoo;
    assert(tfoo == "aha");
}

/**
A simple adaptor for $(M fun), making it accept supplementary arguments of type $(M T...).
See_Also: $(M makeVariadic).
*/
template addArgs(alias fun, T...)
{
    ReturnType!fun addArgs(ParameterTypeTuple!fun args, T newArgs)
    {
        return fun(args);
    }
}


/**
Takes a standard function, and makes it variadic: it will accept any number of surnumerary arguments of any type
after the 'normal' ones that it had before. It's useful to 'adapt' a function to a range (with
automatic unpacking of tuples, like for $(M tmap)).

Example:
----
int foo(int i) { return i;}
alias makeVariadic!foo vfoo;
auto i = vfoo(1, 2,3,'a', "hello there!");
assert(i == 1);
----
*/
template makeVariadic(alias fun)
{
    ReturnType!fun makeVariadic(ParameterTypeTuple!fun args, ...) { return fun(args);}
}

template RT(alias fun)
{
    template RT(T)
    {
        alias typeof(fun(T.init)) RT;
    }
}

template RT2(alias fun)
{
    template RT2(T,U)
    {
        alias typeof(fun(T.init, U.init)) RT2;
    }
}

template RTS(alias fun)
{
    template RTS(Ts...)
    {
        alias typeof(fun(Ts.init)) RTS;
    }
}

template IsBetween(char c, char a, char b) {
    static if ((to!int(c) >= to!int(a)) && (to!int(c) <= to!int(b) )) {
        enum bool IsBetween = true;
    }
    else {
        enum bool IsBetween = false;
    }
}

template IsOneChar(char a, char b, char c)
{
    static if(!(IsBetween!(a, 'A', 'Z') || IsBetween!(a, 'a', 'z'))
           &&   IsBetween!(b, 'a', 'z')
           && !(IsBetween!(c, 'A', 'Z') || IsBetween!(c, 'a', 'z')))
    {
        enum bool IsOneChar = true;
    }
    else
    {
        enum bool IsOneChar = false;
    }
}

template CharArity(char a)
{
    enum int CharArity = to!int(a) - 96;
}

template aritySImpl(string s, size_t index)
{
    static if (s.length > 3)
    {
        static if (IsOneChar!(s[0], s[1], s[2]) && (CharArity!(s[1])>index))
            alias aritySImpl!(s[1..$], CharArity!(s[1])).result result;
        else
            alias aritySImpl!(s[1..$], index).result result;
    }
    else
    {
        static if (s.length == 3) {
            static if (IsOneChar!(s[0], s[1], s[2]) && (CharArity!(s[1])>index))
                alias CharArity!(s[1]) result;
            else
                alias index result;
        }
        else
            enum size_t result = 0;
    }
}

/**
Is true iff $(M fun) can be applied on the TypeTuple $(M ARGS).
Example:
----
assert(CompatibilityFuncArgs!("a+b", int, int)); // 'string' function are templated by unaryFun or binaryFun
                                                 // They will always be compatible with their args
assert(CompatibilityFuncArgs!(binaryFun!"a+b", int, int));

int foo(int a, double b) { return a;}
assert(CompatibilityFuncArgs!(foo, int, double));
assert(CompatibilityFuncArgs!(foo, int, int)); // You can pass an int as second argument for foo, as it will be converted
assert(!CompatibilityFuncArgs!(foo, double, double));  // But not a double as first arg.
assert(!CompatibilityFuncArgs!(foo, int, string));

int bar() { return 0;}
assert(CompatibilityFuncArgs!bar); // For bar, no args...
assert(CompatibilityFuncArgs!(bar, TypeTuple!())); // For bar, no args...

assert(CompatibilityFuncArgs!((int a) { return -a;}, int)); // Works for anonymous functions
----
*/
template CompatibilityFuncArgs(alias fun, ARGS...) if (isFunction!(fun)) {
    enum bool CompatibilityFuncArgs = __traits(compiles, {
                                                            ARGS args;
                                                            fun(args);
                                                         }
                                              );
}

template CompatibilityFuncArgs(alias fun, ARGS...) if (!isFunction!(fun)) {
   static if (is(typeof(fun) : string)) {
        enum bool CompatibilityFuncArgs = true;
    }
    else {
        enum bool CompatibilityFuncArgs = __traits(compiles, {
                                                                ARGS args;
                                                                fun!(ARGS)(args);
                                                            }
                                                   );
    }
}

unittest {
    assert(CompatibilityFuncArgs!("a+b", int, int)); // 'string' function are templated by unaryFun or binaryFun
                                                     // They will always be compatible with their args
    assert(CompatibilityFuncArgs!(binaryFun!"a+b", int, int));

    int foo(int a, double b) { return a;}
    assert(CompatibilityFuncArgs!(foo, int, double));
    assert(CompatibilityFuncArgs!(foo, int, int)); // You can pass an int as second argument for foo, as it will be converted
    assert(!CompatibilityFuncArgs!(foo, double, double));  // But not a double as first arg.
    assert(!CompatibilityFuncArgs!(foo, int, string));

    int bar() { return 0;}
    assert(CompatibilityFuncArgs!bar); // For bar, no args...
    assert(CompatibilityFuncArgs!(bar, TypeTuple!())); // For bar, no args...

    assert(CompatibilityFuncArgs!((int a) { return -a;}, int)); // Works for anonymous functions
}


template Loop(uint n, uint max, alias Action)
{
    static if (n < max) {
        enum string Loop = Action(n, max) ~ Loop!(n+1, max, Action);
    }
    else{
        enum string Loop = "";
    }
}

string PTL(uint n, uint max) { return "ElementType" ~ to!string(n) ~ (n < max-1 ? ", " : "");}
string PNL(uint n, uint max) { return " ElementType" ~ to!string(n) ~ " " ~ az(n) ~ ";";}
string BNL(uint n, uint max) { return " ElementType" ~ to!string(n) ~ " __" ~ az(n) ~ (n < max-1 ? ", " : "");}
string AL(uint n, uint max)  { return " alias __" ~ az(n) ~ " " ~ az(n) ~ ";";}

/**
A generalization of $(M std.functional.unaryFun) and $(M .binaryFun) for as many params as you need, in the 'a' - 'z' (included)
range. You can indicate the desired final arity if you want, but otherwise a compile-time heuristics
tries to determine the string's 'arity'.
As for $(M unaryFun) and $(M binaryFun), 'a' means first argument, 'b' the second and so on.
As for $(M unaryFun) and $(M binaryFun), it creates a templated function, with the type of each parameter left undecided.
As for $(M unaryFun) and $(M binaryFun), it does not change $(M fun) if it's already a function.

Examples:
----
alias naryFun!("a+b*c-d") test4;  // Creates a templated 4-args function test4(A, B, C, D)(A a, B b, C c, D d) { return a+b*c-d;}
assert(test4(1,2,3,4) == 3);        // instantiate test4!(int, int, int, int)
assert(test4(1.0,2.0,3,4) == 3.0);  // instantiate test4!(double, double, int, int)

alias naryFun!("a+b",3) test3;      // You can create a fun with more args than necessary, if you wish
assert(test3(1,2,100) == 3);        // without the 3, naryFun!"a+b" would create a binary function.
assert(test3(1.0,2.0,100) == 3.0);

alias naryFun!"sin(a)+cos(b)*c" testsincos; // functional.d imports a lot of other D modules, to have their functions accessible.

alias naryFun!"tuple(a,a,a)" toTuple;
assert(toTuple(1) == tuple(1,1,1));

alias naryFun!"a.expand[1]" tuple1; // tuple1 will be created, but can be used only on types defining a .expand field.
assert(tuple1(toTuple(1)) == 1);

alias naryFun!"[b,a,c]" arrayTwister; // will return a static array
assert(arrayTwister(0,1,2) == [1,0,2]);

alias naryFun!"f" projection6; // 'a' -> 1 arg, 'b' -> binary, ..., 'f' -> 6-args function. In this case, returning only its sixth argument.
assert(projection6(0,1,2,3,4,5) == 5);

alias naryFun!"3" test0;               // A 0-arg function. It's exactly: int test0() { return 3;}
assert(test0 == 3);                    // Constant return
assert(is(typeof(test0) == function)); // But it's a function, not a constant.

int foo(int a, int b) { return a*b;}
alias naryFun!(foo) nfoo;           // function test
assert(nfoo(2,3) == 6);

int bar() { return 1;}
alias naryFun!bar nbar;             // 0-arg function test
assert(nbar == 1);
----
*/
template naryFun(string fun, uint Nparam)
{
    alias naryFunImpl!(fun, Nparam).result naryFun;
}
/// ditto
template naryFun(string fun)
{
    alias naryFunImpl!(fun, arity!fun).result naryFun;
}

// Works OK, but only at runtime. I need to code this for compile-time.
// OK, done.
// may 2010: CTFE got better with recent DMD version. I should give it a try again.
/*
size_t arityHeuristics(string s) {
    auto padded = " " ~ s ~ " ";
    char[] paddedchars = cast(char[])padded; // To get rid of those pesky immutable(char)
    bool isaz(char c) { return isOneOf!lowercase(c);} // lowercase is defined in std.string
    bool isazAZ(char c) { return isOneOf!letters(c);} // letters is defined in std.string
    bool isOneChar(char a, char b, char c) { return !isazAZ(a) && isaz(b) && !isazAZ(c);}
    size_t charArity(char c) { return to!int(c)-96;} // 1 for 'a', 2 for 'b'
    size_t loneIndex(char a, char b, char c) { return isOneChar(a,b,c) ? charArity(b) : 0;}
    auto loneIndices = nMap!loneIndex(paddedchars);
    return reduce!max(loneIndices);
}
*/

template naryFunImpl(alias fun, uint Nparam) if (is(typeof(fun) : string))
{
    static if (Nparam > 0)
    {
        enum string paramTypeList = Loop!(0, Nparam, PTL);
        enum string paramNameList = Loop!(0, Nparam, PNL);
        enum string bodyNameList  = Loop!(0, Nparam, BNL);
        enum string aliasList     = Loop!(0, Nparam, AL);
        enum string code = "typeof({" ~ paramNameList ~ " return (" ~ fun ~ ");}()) result(" ~ paramTypeList ~ ")(" ~ bodyNameList ~ ") { " ~ aliasList ~ " return (" ~ fun ~ ");}";
    }
    else
    {
        enum string code = "typeof((){return " ~ fun ~ ";}()) result() {return " ~fun ~ ";}";
    }

    mixin(code);
}

/// ditto
template naryFun(alias fun, uint Nparam) if (!is(typeof(fun): string))// && (arity!(fun) == Nparam))
{
    static if (is(fun == struct) || is(fun == class)) // class or struct constructor
        alias construct!fun naryFun;
    else
        alias fun naryFun;
}

/// ditto
template naryFun(alias fun) if (!is(typeof(fun): string))
{
    alias fun naryFun;
}

unittest
{
    alias naryFun!("a+b*c-d") test4;  // Creates a templated 4-args function test4(A, B, C, D)(A a, B b, C c, D d) { return a+b*c-d;}
    assert(test4(1,2,3,4) == 3);        // instantiate test4!(int, int, int, int)
    assert(test4(1.0,2.0,3,4) == 3.0);  // instantiate test4!(double, double, int, int)

    alias naryFun!("a+b",3) test3;      // You can create a fun with more args than necessary, if you wish
    assert(test3(1,2,100) == 3);        // without the 3, naryFun!"a+b" would create a binary function.
    assert(test3(1.0,2.0,100) == 3.0);

    alias naryFun!"sin(a)+cos(b)*c" testsincos; // functional.d imports a lot of other D modules, to have their functions accessible.

    alias naryFun!"tuple(a,a,a)" toTuple;
    assert(toTuple(1) == tuple(1,1,1));

    alias naryFun!"a.expand[1]" tuple1; // tuple1 will be created, but can be used only on types defining a .expand field.
    assert(tuple1(toTuple(1)) == 1);

    alias naryFun!"[b,a,c]" arrayTwister; // will return a static array
    assert(arrayTwister(0,1,2) == [1,0,2]);

    alias naryFun!"f" projection6; // 'a' -> 1 arg, 'b' -> binary, ..., 'f' -> 6-args function. In this case, returning only its sixth argument.
    assert(projection6(0,1,2,3,4,5) == 5);

    alias naryFun!"3" test0;               // A 0-arg function. It's exactly: int test0() { return 3;}
    assert(test0 == 3);                    // Constant return
    assert(is(typeof(test0) == function)); // But it's a function, not a constant.

    int foo(int a, int b) { return a*b;}
    alias naryFun!(foo) nfoo;           // function test
    assert(nfoo(2,3) == 6);

    int bar() { return 1;}
    alias naryFun!bar nbar;             // 0-arg function test
    assert(nbar == 1);
}

/+ deprecated
/**
Fills a TypeTuple of T's (T,T,T, ...) from a T[] array of values. It's
the TypeTuple's length which drives the transfer: it
Used to convert the elements of a Segment (ie: T[]) into a TypeTuple to be used
in a function.
*/
void fillFromArray(Arr : T[], T, Tup...)(Arr arr, ref Tup tup) {
    static if (Tup.length > 0) {
        tup[0] = arr[0];
        fillFromArray(arr[1..$], tup[1..$]);
    }
}

unittest {
    double[] d = [0.0, 1.0, 2.0];
    TypeTuple!(double, double, double) td;
    fillFromArray(d, td);
    assert(td[0] == 0.0);
    assert(td[1] == 1.0);
    assert(td[2] == 2.0);
}
+/

/+
/**
For a function fun with arguments types (T, T, T, ...) calls the function
from a T[] array of arguments.
Example:
----
int foo(int a, int b, int c) {
    return a*b*c;
}

auto arr = [1,2,3];

// not possible:
// foo(arr);
// so we do:
arrayApply!(foo)(arr); // return 1*2*3 -> 6.
----
*/
auto arrayApply(alias fun, T : U[], U)(T args) if (CompatibilityFuncArgs!(fun, TypeNuple!(U, arity!fun))) {
    TypeNuple!(U, arity!fun) at;
    fillFromArray(args, at);
    return fun(at);
}

unittest {
    int foo(int a, int b, int c) {
        return a*b*c;
    }

    auto arr = [1,2,3];

    // foo(arr); // not possible
    // so we do:
    arrayApply!foo(arr); // return 1*2*3 -> 6.
}

/**
Transforms a function with parameters of same type: foo(T, T, T, ...) into an
array-accepting function afoo(T[]). Useful to map a function on a Segment range:
to map a binary or n-ary function on a range. See below.
*/
template arrayify(alias fun) {
    alias arrayifyImpl!(fun).result arrayify;
}

template arrayify(alias fun, T) {
    alias TypeNuple!(T, arity!fun) TN;
    alias fun!(TN) fun2;
    alias arrayifyImpl!(fun2).result arrayify;
}

template arrayifyImpl(alias fun) {
    alias ReturnType!fun R;
    alias ParameterTypeTuple!fun A;
    static if (A.length > 0) {
        R result(A[0][] arr) {
            return arrayApply!fun(arr);
        }
    }
    else {
        R result() {
            return fun();
        }
    }
}

unittest {
    int foo(int a, int b, int c) {
        return a*b*c;
    }

    auto arr = [1,2,3];
    alias arrayify!foo afoo; // afoo is now an int[3] or int[] accepting function
    assert(is(typeof(&afoo) == int delegate(int[])));
    assert(arity!afoo == 1); // afoo is indeed a unary function now.
    assert(afoo(arr) == 6); // We can apply afoo on arr.
    assert(afoo([2,3,4]) == 24); // Works on int[3] arrays also
    assert(!is(afoo([1,2]))); // But afoo rejects int[2] arrays.

    auto r1 = [1,2,3,4,5,6];

    double average(int a, int b, int c) {
        return (a+b+c)/3.0;
    }
    alias arrayify!average mean;
    assert(is(typeof(&mean) == double delegate(int[])));
//    auto s = segment!3(r1); // We cannot map 'average' on s
//    auto m = map!mean(s); // But we can map 'mean'
//    assert(asString(m, " ") == "2 3 4 5");
}
+/

/+ deprecated
/**
Fills a TypeTuple of different types from a std.typecons.Tuple of values.
Used to convert the result of a TupleRange into a TypeTuple to be used
in a function.
*/
void fillFromTuple(size_t n = 0, T : Tuple!(TT), TT...)(T tup, ref TT typetup) {
    static if (n < TT.length) {
        typetup[n] = tup.field[n];
        fillFromTuple!(n+1)(tup, typetup);
    }
}

unittest {
    auto tup = tuple(0, 'a', 1.23);
    TypeTuple!(int, char, double) tt;
    fillFromTuple(tup, tt);
    assert(tt[0] == 0);
    assert(tt[1] == 'a');
    assert(tt[2] == 1.23);
}

/**
Given a std.typecons.Tuple of values args, expand the Tuple and _apply fun to it.
It's useful to map a n-ary function on a Tuple-outputting range.
Note that apply will check that the Tuple can indeed be used
as parameters for the function. If args is longer than
ParameterTypeTuple!fun, any remaining values will be ignored.

Example:
----
string foo3(int a, string b, double c) {
    return to!string(a) ~ "+" ~ b ~ "+" ~ to!string(c);
}
auto t = tuple(1, "a", 3.0);
writeln(tupleApply!foo3(t)); // Write "1+a+3"
----
*/
auto tupleApply(alias fun, T : Tuple!(R), R...)(T args) if (CompatibilityFuncArgs!(fun, R)) {
    TypeTuple!R tt;
    fillFromTuple(args, tt);
    return fun!(R)(tt[0 .. R.length]);
}

unittest {
    string foo3(int a, string b, double c) {
        return to!string(a) ~ "+" ~ b ~ "+" ~ to!string(c);
    }
    auto t = tuple(1, "a", 3.0);
    assert(tupleApply!foo3(t) == "1+a+3"); // Applies foo3 to t
}
+/


/**
Internal template to transform a function or a 'string' function
to be applied on a tuple. The $(M T...) part must contains the information
about the args types. It's used to instantiate the correct function
from the template function created by $(M naryFun).

It's used internally by all the tuple-mapping functions: $(M tmap), $(M tfilter), etc.
*/
template Prepare(alias fun, T...)
{
    alias PrepareImpl!(fun, T).result Prepare;
}

template PrepareImpl(alias fun, T...)
{
    alias naryFun!(fun, T.length) nfun; // transforms string as n-args templated function.
    static if (__traits(compiles, nfun!T)) // Can I instantiate nfun!T?
        alias nfun!T infun;  // instantiates n-fun.
    else
        alias nfun infun;    // It's a function, do nothing.
    alias tuplify!infun result;
}
