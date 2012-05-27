/**
This module is a small expression template library to create anonymous functions (aka, lambdas)
in a syntax reminiscent of std.* 'string' functions or what is used in other programming
languages (like Scala, for example).

Future arguments are represented as $(M __0), $(M __1), $(M __2), or simply $(M __).
Anonymous functions are automatically constructed by putting them in arithmetic expressions.
Here are a few examples:
----
auto l1 = _ + 1;
auto l2 = _0 + _1;
auto l3 = _2[_0.length-1.._1.length+1];
auto l4 = _2 ~ _3;

auto head = _[0]; // Or _.front
auto tail = _[1.._.length];
----
Their main point is to be used in map/reduce/filter calls in lieu of 'string' functions:
----
auto arr = [0,1,2,3,4];
auto plusOne = map!(_ + 1)(arr);
auto sum = reduce!(_0 + _1)(arr); // instead of reduce!("a + b")(arr);
----

$(M __0 + __1) is a completly templated function that waits for two arguments and return their sum. Lambdas
are always generic in all their arguments and are automatically curried. $(M __0 + __1) can be called
with two arguments, but also with one. In that case $(M (__0 + __1)(1)) puts the 1 in place of all $(M __0)s in
the expression and returns the resulting _lambda: $(M 1 + __0). This new _lambda can itself be called
with another argument to give the sum.
This allows for some nifty tricks like:
----
// create a range of functions: [ _+0, _+1, _+2, ...]
auto funRange = map!(_0 + _1)(arr);
foreach(fun; funRange) writeln(fun(10)); // writes 10,11,12,13,14.
----

Features and authorized expressions:
$(UL
    $(LI Any basic binary and unary expression should work.)
    $(LI == is OK. != is not, though (see below).)
    $(LI opIndex is there, and slices too.)
    $(LI opDispatch is used to allow expressions like : $(M _.length).)
    $(LI Compared to 'string' functions, they can be passed around, are real callable objects
      and so should be compatible with all your usual idioms concerning functions.)
    $(LI compared to template anonymous function, like $(M (i) { return i+1;}) they can be
      passed around, returned as results from other functions, etc. In D, closures can be returned
      but not templated closures. Here you can, at least for the expressions described above.)
    $(LI They are composable. If you have two lambdas, you can sum them, call one with another, etc. You cannot
      do that with 'string' functions.)
    $(LI They are not limited to two arguments. In fact, the real syntax for $(M __0) &co is $(M Arg!0), $(M Arg!1), etc.
      The $(M __x) shown here are just alias for your convenience.
      There is no limit to the number of arguments. And remember: the resulting expression will be fully generic
      and curried.)
)

It's just an afternoon work really, so be prepared for bugs and such. As of this writing, the main limitations are:
$(UL
  $(LI No $(M opCmp) ($(M <), $(M <=), $(M >), $(M >=)). I couldn't find a way to do them that doesn't produce infinite template
    expansion, due to the way DMD rewrites $(M a < b) as $(M a.opCmp(b) < 0): the $(M < 0) part triggers another expansion,etc.
    This *really* annoys me, as it severely limits the interest of the library: you cannot do $(M filter!(__ < 1)(range)),
    which was one of the main motivations for writing this module. Any help would be appreciated.)
  $(LI No $(M opCall). That is, you cannot do $(M __0(__1)). This is by design, because all the lambdas are callable structs: $(M _0(_1)) gets $(M _0)
    called with $(M __1), it does not construct another lamda. I could easily introduce a CallExpr constructor, but that'd mean calling lambdas
    with another syntax that the call operator $(M ()), which rather defeats the goal of this module.
    Maybe I could test for the arguments being expressions or not...)
  $(LI No $(M !=), because $(M a!=b) is rewritten as $(M !(a.opEquals(b))). But $(M a.opEquals(b)) is a _lambda, not a boolean. That
    makes the compiler chokes because it cannot implicitly convert the _lambda to a boolean. As there is no $(M opImplicitCast) in D, I'm stuck.)
  $(LI No $(M opCast(type)). It seems that in $(M cast(type)_lambda), the compiler does not construct the CastExpr I want it too, but try to directly
    cast _lambda into a type...)
  $(LI No expression with standard functions. That is, no _lambda like: $(M sin(__)+cos(__)). That's because $(M sin) and $(M cos) want a $(M real),
    not a _lambda. A nasty workaround would be to use the method call syntax: $(M __.sin + __.cos) and play with $(M opDispatch). But I find the resulting
    syntax quite ugly.)
)
*/
module dranges.lambda;

import std.typetuple : staticMap;
import dranges.typetuple : Init;

// The following imports are only to ease the use of opDispatch. They are not necessary for lambdas.
import std.array, std.string;

template isExpr(T)
{
    static if (__traits(hasMember, T, "opCall")) // not a good test, really.
        enum bool isExpr = true;
    else
        enum bool isExpr = false;
}

template Terminalize(T)
{
    static if (isExpr!T)
        alias T Terminalize;
    else
        alias Terminal!T Terminalize;
}

template RetType(U...)
{
    template RetType(Callable)
    {
        alias typeof(Callable.init(Init!U)) RetType;
    }
}

mixin template ExprOperators()
{
    auto opBinary(string op, U)(U u)
    {
        return binExpr!op(this, terminal(u));
    }

    auto opBinaryRight(string op, U)(U u) if (!isExpr!U)
    {
        return binExpr!op(terminal(u), this);
    }

    auto opUnary(string op)()
    {
        return unExpr!op(this);
    }

    auto opEquals(U)(U u)
    {
        return binExpr!"=="(this, terminal(u));
    }

    auto opIndex(I)(I i)
    {
        return indexExpr(this, terminal(i));
    }

    auto opSlice(I...)(I i) if (I.length == 0)
    {
        return sliceExpr(this);
    }

    auto opSlice(I...)(I i) if (I.length == 2)
    {
        return sliceExpr(this, terminal(i[0]), terminal(i[1]));
    }

    auto opDispatch(string s, U...)(U u)
    {
        staticMap!(Terminalize, U) tu;
        foreach(i, Type; U) tu[i] = terminal(i);
        return dispatchExpr!s(this, tu);
    }


//    auto opCmp(U)(U u) if (!(is(U == uint)))
//    {
//        static if (isExpr!U)
//            return cmpExpr(this, u);
//        else
//            return cmpExpr(this, terminal(u));
//    }
//
//    auto opCmp(U)(U u) if ((is(U == uint)))
//    {
//        if (u == 0)
//        {
//            return cmpExpr(this); // special case
//        }
//        else
//        {
//            return cmpExpr(this, terminal(u));
//        }
//    }
}

struct Terminal(T) if (!isExpr!(T))
{
    T t;

    T opCall(U...)(U u) { return t;}

    mixin ExprOperators;
}

//template Terminal(T) if (isExpr!T)
//{
//    alias T Terminal;
//}

Terminal!T terminal(T)(T t) if (!isExpr!(T))
{
    Terminal!T res;
    res.t = t;
    return res;
}

T terminal(T)(T t) if (isExpr!T)
{
    return t;
}

struct BinExpr(string op, L,R) if (isExpr!L && isExpr!R)
{
    L l;
    R r;

    auto opCall(U...)(U u) { mixin("return l(u) " ~ op ~ " r(u);");}

    mixin ExprOperators;
}

BinExpr!(op,L,R) binExpr(string op, L,R)(L left, R right) if (isExpr!L && isExpr!R)
{
    BinExpr!(op,L,R) res;
    res.l = left;
    res.r = right;
    return res;
}

struct UnExpr(string op, A) if (isExpr!A)
{
    A a;

    auto opCall(U...)(U u) { mixin("return " ~ op ~ "a(u);");}

    mixin ExprOperators;
}

UnExpr!(op,A) unExpr(string op, A)(A a) if (isExpr!A)
{
    UnExpr!(op,A) res;
    res.a = a;
    return res;
}

struct IndexExpr(A, I)
{
    A a;
    I i;

    auto opCall(U...)(U u) { return a(u)[i(u)];}

    mixin ExprOperators;
}

IndexExpr!(A, I) indexExpr(A, I)(A a, I i) if (isExpr!A)
{
    IndexExpr!(A,I) res;
    res.a = a;
    res.i = i;
    return res;
}

struct SliceExpr(A, I...) if (I.length == 0 || I.length == 2)
{
    A a;

    static if (I.length == 0)
        auto opCall(U...)(U u) { return a(u)[]; }
    else
    {
        I i;
        auto opCall(U...)(U u) { return a(u)[i[0](u)..i[1](u)];}
    }

    mixin ExprOperators;
}

SliceExpr!(A, I) sliceExpr(A, I...)(A a, I i) if (I.length == 0 || I.length == 2)
{
    SliceExpr!(A,I) res;
    res.a = a;
    static if (I.length == 2)
        res.i = i;
    return res;
}

struct DispatchExpr(string s, A, T...)
{
    A a;
    T t;

    auto opCall(U...)(U u) {
        static if (T.length)
        {
            staticMap!(RetType!U, T) rt;
            foreach(i, Type; T) rt[i] = t(u);
            mixin("return a(u)." ~ s ~ "(rt);" );
        }
        else
            mixin("return a(u)." ~ s ~ ";" );
    }

    mixin ExprOperators;
}

DispatchExpr!(s,A,T) dispatchExpr(string s, A, T...)(A a, T t)
{
    DispatchExpr!(s,A,T) res;
    res.a = a;
    static if (T.length) res.t = t;
    return res;
}

struct Arg(int i) if (i>=0)
{
    auto opCall(U...)(U u)
    {
        static if (i < U.length)
            return u[i];
        else
            return arg!(i-U.length)();
    }

    mixin ExprOperators;
}

Arg!i arg(int i)() if (i >= 0)
{
    Arg!i res;
    return res;
}

enum Arg!0 _ = arg!0();

enum Arg!0 _0 = arg!0();
enum Arg!1 _1 = arg!1();
enum Arg!2 _2 = arg!2();
enum Arg!3 _3 = arg!3();
enum Arg!4 _4 = arg!4();
enum Arg!5 _5 = arg!5();
enum Arg!6 _6 = arg!6();
enum Arg!7 _7 = arg!7();
enum Arg!8 _8 = arg!8();
enum Arg!9 _9 = arg!9();

