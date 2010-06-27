// Written in the D programming language

/**
This module defines some useful _templates for the other modules and some 'meta-_templates'. Templates
transforming other _templates, currying them, flipping their arguments, etc.


License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud and Simen Kj&aelig;r&aring;s

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.templates;

import std.conv: to;
import std.functional;
import std.metastrings;
import std.typecons;
import std.typetuple;
import std.traits;

import std.stdio;

import dranges.traits2;
import dranges.typetuple2;
import dranges.functional2: arity, Loop;

/+
///
template isInstanceOf(alias t, alias templ)
{
    static if (typeof(t).stringof.length >= __traits(identifier, templ).length
            && typeof(t).stringof[0..__traits(identifier, templ).length] == __traits(identifier, templ))
        enum bool isInstanceOf = true;
    else
        enum bool isInstanceOf = false;
}
+/

/**
Alias itself to true if $(M T) is an instance of $(M templ). To obtain the template parameters,
see TemplateParametersTypeTuple.
Example:
----
auto cy = cycle([0,1,2,3]); // cy is a Cycle!(int[])
alias typeof(cy) Cy;
assert(isInstanceOf!(Cy, Cycle));
----
*/
template isInstanceOf(T, alias templ)
{
    static if (T.stringof.length >= __traits(identifier, templ).length
            && T.stringof[0..__traits(identifier, templ).length] == __traits(identifier, templ))
        enum bool isInstanceOf = true;
    else
        enum bool isInstanceOf = false;
}

/**
Switches between template instantiations depending on the parameters passed.
Author:
Simen Kj&aelig;r&aring;s.

Example:

----
alias staticSwitch( foo, 1, 2, 3 ).With callFoo;
callFoo( 2 ); // Actually calls foo!(2)( )
----
*/
template staticSwitch( alias F, T... ) if ( allSatisfy!( isAlias, T ) ) {
   auto With( CommonType!T index, ParameterTypeTuple!( F!( T[0] ) ) args ) {
       switch ( index ) {
           foreach ( i, e; T ) {
               mixin( Format!( q{case %s:}, e ) );
               return F!( e )( args );
           }
           default:
                assert(false);
       }
       assert( false );
   }
}

version( unittest ) {
   int foo(int p)( int n ) {
       return p*n;
   }
}

unittest {
   assert( staticSwitch!( foo, 1, 2 ).With( 2,3 ) == 6 );
}

/**
Bind $(M Param0) as the first parameter of $(M Template).
See_Also:
CurryTemplate, for a more powerful and up-to-date version.
*/
template BindT(alias Template, alias Param0)
{
    template BindT(U...)
    {
        alias Template!(Param0, U) BindT;
    }
}

// for BindT unit test: map a BindT!(CT, int) on a TypeTuple
template CT2(T, U)
{
    alias CommonType!(T,U) CT2;
}

/**
Bind $(M Param0) as the first template parameter of a function template.
*/
template BindF(alias FunctionTemplate, alias Param0)
{
    ReturnType!(FunctionTemplate!(Param0, T)) BindF(T)(T t)
    {
        return FunctionTemplate!(Param0, T)(t);
    }
}

int[] AliasIndices(alias templ)()
{
    enum string name = templ.stringof;
    int level, index;
    int[] indices;
    foreach(i,c; name[0..$-7])
    {
        if (c == '(') level++;
        if (c == ')') level--;
        if (level == 1 && c == ',') index++;
        if (level == 1 && name[i..i+6] == "alias ") indices ~= index;
    }
    return indices;
}

/**
Takes a n-args template and transforms it into n 1-arg templates inside each other.
Very useful for templates with many arguments, when you only have one arg right now, or want
to bind this arg. CurryTemplate also works with template alias parameters (and will
wait for an alias, not a type).

Example:
----
// StaticMap takes a template and typetuple as parameters.
alias CurryTemplate!(StaticMap) CStaticMap; // CStaticMap takes a template and then a T... (typetuple)
alias CStaticMap!Unqual SMU; // SMU is now an independant template taking a T... and mapping Unqual on it.

assert(is(SMU!(int, const int, immutable double, string) == TypeTuple!(int, int, double, string)));
----
*/
template CurryTemplate(alias templ)
{
    mixin(CurryTemplateImpl!(templ,TemplateArity!templ, "")(AliasIndices!templ));
}

string CurryTemplateImpl(alias templ, int n, string Ts)(int[] aliasIndices)
{
    static if (n == 0)
        return "alias templ CurryTemplate;";
    else static if (n > 0)
    {
        static if (n == 1)
            if (!aliasIndices.length == 0 && aliasIndices[0] + n == TemplateArity!templ)
            {
                return "template CurryTemplate (alias T1) { alias templ!(" ~ Ts ~ "T1) CurryTemplate;}";
            }
            else
            {
                return "template CurryTemplate( T1 ) { alias " ~ __traits(identifier, templ) ~ "!(" ~ Ts ~ "T1) CurryTemplate;}";
            }
        else
            if (!aliasIndices.length == 0 && aliasIndices[0] + n == TemplateArity!templ)
            {
                return "template CurryTemplate (alias T" ~to!string(n) ~ ") {"
                                ~ CurryTemplateImpl!(templ, n-1, Ts ~ "T"~to!string(n) ~ ", ")(aliasIndices[1..$]) ~ "}";            }
            else
            {
                return "template CurryTemplate( T" ~ to!string(n)  ~ ") {"
                                ~ CurryTemplateImpl!(templ, n-1, Ts ~ "T"~to!string(n) ~ ", ")(aliasIndices) ~ "}";
            }
    }
    else  // n < 0 : variadic template T(A,B,C...)
    {
        static if (n == -1) // Variadic T(C...). We accept any number of parameters for the last one.
            return "template CurryTemplate( T1... ) { alias " ~ __traits(identifier, templ) ~ "!(" ~ Ts ~ "T1) CurryTemplate;}";
        else
        {
            if (!aliasIndices.length == 0 && aliasIndices[0] - n == -TemplateArity!templ)
            {
                return "template CurryTemplate(alias T" ~ to!string(-n)  ~ ") {"
                                    ~ CurryTemplateImpl!(templ, n+1, Ts ~ "T"~to!string(-n) ~ ", ")(aliasIndices[1..$]) ~ "}";
            }
            else
            {
                return "template CurryTemplate( T" ~ to!string(-n)  ~ ") {"
                                    ~ CurryTemplateImpl!(templ, n+1, Ts ~ "T"~to!string(-n) ~ ", ")(aliasIndices) ~ "}";
            }
        }
    }
}

/**
Takes a complex type (ie:Cycle!R, Retro!R) and get rid of the external type indicated
as a string. That is UnWrap!("Cycle", Cycle!U) aliases itself to U. It's useful
to get some return types, when you extract internal values in a range and need to get their types.

Example:
----
auto c = cycle([1,2,3][]);
assert(is(typeof(c) == Cycle!(int[]))); // A cycle around an array of int
alias UnWrap!("Cycle", typeof(c)) InternalType;
assert(is(InternalType == int[]));
----
Deprecated:
use TemplateParameterTypeTuple instead.
*/
template UnWrap(string Wrapper, T) {
    mixin("static if (is(T T1 == " ~ Wrapper ~ "!U, U)) { alias U UnWrap; }");
}

/**
The converse of UnWrap.
*/
template Wrap(string Wrapper, T) {
    mixin("alias " ~ Wrapper ~ "!T Wrap;");
}

version(unittest)
{
    import std.range;
}

unittest
{
    auto c = cycle([1,2,3][]);
    assert(is(typeof(c) == Cycle!(int[]))); // A cycle around an array of int
    alias UnWrap!("Cycle", typeof(c)) InternalType;
    assert(is(InternalType == int[]));
    Wrap!("Cycle", InternalType) c2;
    assert(is(typeof(c2) == typeof(c)));
}

/**
Takes a template and flips its arguments.
So, given:
----
template Foo(A,B) {}
----
Then FlipTemplate!Foo is equivalent to:
----
template FlippedFoo(B,A) { alias Foo!(A,B) FlippedFoo;}
----

Example:
----
template Pair(A,B)
{
    alias Tuple!(A,B) Pair;
}

alias FlipTemplate!Pair FPair;

assert(is( Pair!(int,double) == Tuple!(int,double)));
assert(is(FPair!(int,double) == Tuple!(double,int)));
----

This works for any number of parameters.
Example:
----
alias FlipTemplate!Tuple FTuple;
assert(is(FTuple!(char,int,double,void delegate(string)) == Tuple!(void delegate(string),double,int,char)));
----
*/
template FlipTemplate(alias templ)
{
    template FlipTemplate(T...)
    {
        alias templ!(FlipType!T) FlipTemplate; // FlipType is a template defined in dranges.typetuple2
    }
}

/**
A generalized version of FlipTemplate: takes a target template and
a transformation on types (another template). It will then apply
the transformation on the parameters before passing the result to the input
template.
Example:
----
template Foo(A) {}; // Foo takes one type as param.
// First is template defined in dranges.typetuple2 that takes a TypeTuple and alias itself to the first type.
alias TransformTemplate!(Foo, First) TFoo; // TFoo is a variadic template. Any T... passed to it is transformed
                                           // by First!T into T[0], before serving as parameter for Foo.
                                           // So, TFoo is now a variadic version of Foo.
assert(is(TFoo!(int, double, string) == Foo!(int)));
----
*/
template TransformTemplate(alias templ, alias transformTypes)
{
    template TransformTemplate(T...)
    {
        alias templ!(transformTypes!T) TransformTemplate;
    }
}

/**
The template equivalent of unaryFun: takes a string as template argument and creates a simple template aliasing
the string. As for unaryFun, the resulting template argument is 'a'.

Example:
----
alias T1!"Tuple!(ReturnType!a, ParameterTypeTuple!a)" FunTypes;

assert(is(FunTypes!(int delegate(double, string)) == Tuple!(int, double, string)));
----
*/
template T1(string s)
{
    alias T1Impl!(s).result T1;
}

template T1Impl(string s)
{
    template result(alias a) {
        mixin("alias TypeTuple!(" ~ s ~ ") result;");
    }
}

/**
The binaryFun equivalent for templates: given a string with 'a' and 'b', generates a template from it.
It's useful to quickly make a template, for example for a StaticMap or template composition.
Example:
----
alias T2!"a delegate(b)" MkDelegate; // MkDelegate is a template taking two types a and b and becoming
                                     // the type of delegates from b to a.
----
*/
template T2(string s)
{
    alias T2Impl!(s).result T2;
}

template T2Impl(string s)
{
    template result(alias a, alias b) {
        mixin("alias TypeTuple!(" ~ s ~ ") result;");
    }
}


string az(uint n)  { return "abcdefghijklmnopqrstuvwxyz"[n..n+1];}
string AliasList(uint n, uint max) { return "alias " ~ az(n) ~ (n < max-1 ? ", " : "");}

/**
The n-types generalization of T1 and T2: given a string in 'a', 'b', ... (up to 'z'), creates
a template from it. It will automatically determine the corresponding number of parameters
by using the same heuristics than for naryFun in dranges.functional2: it looks for lone letters
and takes the higher one

Example:
----
alias TN!"a delegate(b,c,d)" MkDelegate3; // finds a 'd', arity = 4, MkDelegate3 is a four parameters template
assert(is(MkDelegate!(int,double,char,string) == int delegate(double,char,string)));
----
*/
template TN(string s)
{
    alias TNImpl!(s, arity!s).result TN;
}

template TNImpl(string s, size_t NParams)
{
    enum string aliasList = Loop!(0, NParams, AliasList);
    enum string code = "template result(" ~ aliasList ~ ") { alias TypeTuple!(" ~ s ~ ") result; }";
    mixin(code);
}


/**
Aliases itself to the max of a and b.
*/
template Max(alias a, alias b) {
    static if (a < b) {
        alias b Max;
    }
    else {
        alias a Max;
    }
}

/**
Aliases itself to the min of a and b.
*/
template Min(alias a, alias b) {
    static if (a > b) {
        alias b Min;
    }
    else {
        alias a Min;
    }
}

/**
Wraps 'code' n times around value. It's used to defined flatten2 by way of concat, as
a simple way to flatten a range up to n levels is to apply concat n times to it.
Example:
----
int[] appendZero(int[] a) { return a ~ [0];}
int[] r = [1,2,3];
auto w = wrap!(appendZero, 3)(r);
assert(w == [1,2,3,0,0,0][]);
----
*/
auto wrapCode(alias code, size_t n = 1, T)(T value) {
    static if (n == 0)
        return value;
    else
        return code(wrapCode!(code, n-1)(value));
}

unittest
{
    int[] appendZero(int[] a) { return a ~ [0];}
    int[] r = [1,2,3];
    auto w = wrapCode!(appendZero, 3)(r);
    assert(w == [1,2,3,0,0,0][]);
}

string[3] between(char b, char e, string s)()
{
    int foundb;
    int ib;
    string notFound = "";
    foreach(i,c; s)
    {
        if (c==b)
        {
            if (foundb == 0)
            {
                foundb = 1;
                ib = i+1;
                continue;
            }
            else
            {
                ++foundb;
            }
        }
        if (c==e)
        {
            if (foundb == 1)
            {
                return [s[0..ib-1], s[ib..i], s[i+1..$]];
            }
            else
            {
                --foundb;
            }
        }
    }
    return [s, notFound,notFound];
}

int countCommas(string s)
{
    int count, level;
    foreach(i,c; s)
    {
        switch(c) {
            case '(':
                ++level;
                break;
            case ')':
                --level;
                break;
            case ',':
                if (level == 0) ++count;
                break;
            default:
                break;
        }
    }
    return count;
}

/**
Alias itself to true iff templ is a template (standard, function, class or struct template).
*/
template isTemplate(alias templ)
{
    static if (is(typeof(templ) == void) && is(typeof(templ.stringof)))
        enum bool isTemplate = true;
    else
        enum bool isTemplate = false;
}

/**
Alias itself to the number of parameters needed to instantiate template $(M templ).
To represent variadic template, returns a negative number.
Example:
----
template Foo0()    {}
template Foo1(A)   {}
template Foo2(A,B) {}
template FooVar(A,B,C...) {}

assert(TemplateArity!Foo0 == 0);
assert(TemplateArity!Foo1 == 1);
assert(TemplateArity!Foo2 == 2);
assert(TemplateArity!Foo3 == -3); // Three params, the last being variadic.
----
*/
template TemplateArity(alias templ) if (isTemplate!templ)
{
    enum int TemplateArity = TAImpl!templ();
}

int TAImpl(alias templ)()
{
    enum string st = templ.stringof;
    enum string str = between!('(',')',st)[1];
    static if (str.length == 0)
        enum int sign = 0;
    else static if (str.length >3 && str[$-3 .. $] == "...")
        enum int sign = -1;
    else
        enum int sign = 1;
    return (1 + countCommas(str))*sign;
}

/**
Takes a type instantiating a template (that is, T == A!(someTypes...) for some A)
and becomes the template's parameters typetuple: TypeTuple!(someTypes) in the previous example.
It won't work for alias parameters, because they're not imported by this module.
Example:
----
assert(is(TemplateParametersTypeTuple!(Cycle!(int[])) == TypeTuple!(int[])));
----

*/
template TemplateParametersTypeTuple(T)
{
    mixin("alias TypeTuple!(" ~ between!('(',')',T.stringof)[1] ~ ") TemplateParametersTypeTuple;");
}

string structsList(size_t n)
{
    string result;
    foreach(i; 0..n) result ~= "struct T"~to!(string)(i)~ " {};";
    return result;
}

string paramsList(size_t n)
{
    string result;
    foreach(i; 0..n-1) result ~= "T"~to!(string)(i)~ ", ";
    return result ~ "T"~to!string(n-1);
}

template PTT(alias templ)
{
    enum size_t a = TemplateArity!(templ);
    mixin(structsList(a));
    enum string Ts = "alias ParameterTypeTuple!(templ!(" ~ paramsList(a) ~ ")) PT;";
    mixin(Ts);
}

/**
Gives the parameters typetuple from a non-instantiated template function. It creates
a list of structs T0, T1, ..., Tn (n being TemplateArity!fun) and instantiates fun
to do that. So the resulting TypeTuple is defined for inexistant types!

Limitation:
Does not work if there are constraints on the types.

BUG:
Should be modified to work with variadic templates.

Example:
----
A foo(A,B)(A a, B b, Tuple!(B,A) c, B d) { return a;}
alias TemplateFunctionPTT!foo PTTfoo; // PTTfoo is TypeTuple!(T0, T1, Tuple!(T1,T0), T1)
----
*/
template TemplateFunctionPTT(alias fun)
{
    alias PTT!fun.PT TemplateFunctionPTT;
}


/**
Gives the number of args of a non-instantiated template function. Not to be confused with
$(M TemplateArity) which gives the number of parameters for the template.

Example:
----
A foo(A,B)(A a, B b, Tuple!(B,A) c, B d) { return a;}

assert(TemplateFunArity!foo == 4);
assert(TemplateArity!foo    == 2);
----
*/
int TemplateFunArity(alias templ)()
{
    enum string TFPTT = TemplateFunctionPTT!templ.stringof;
    enum string str = between!('(',')',TFPTT)[1];
    static if (str.length == 0)
        enum int sign = 0;
    else static if (str[$-3 .. $] == "...")
        enum int sign = -1;
    else
        enum int sign = 1;
    return (1 + countCommas(str))*sign;
}

/**
A small template to sort types.
See_Also:
dranges.typetuple.SortTypes
*/
template CompareTypes(T, U)
{
    static if (is(T == U))
        enum int CompareTypes = 0;
    else static if (T.stringof < U.stringof)
        enum int CompareTypes =-1;
    else static if (T.stringof > U.stringof)
        enum int CompareTypes = 1;
    else static assert(false);
}

/**
Returns the constraints of a template (the guard $(D if (...)) after the template name), if any. If there is
no constraint, returns the empty string.
Example:
----
template Foo(alias A, B, C)
{
    alias A!(B,C) Foo;
}

template Bar(A,B,C) if (isIntegral!B && is(C == CommonType!(A,B)))
{
    alias Tuple!(A,B,C) Bar;
}

assert(TemplateConstraints!Bar == "isIntegral!(B) && is(C == CommonType!(A,B))");
assert(TemplateConstraints!Foo == "");
----
*/
string TemplateConstraints(alias templ)()
{
    enum string name = templ.stringof;              // strangely, I can make these a one-liner.
    enum string tail = between!('(',')',name)[2];
    enum string constr = between!('(',')',tail)[1];
    return constr;
}

/**
Is true if a is an alias (_a symbol bound by an alias template parameter). It's useful when you have
_a variadic type (T...) and some of its components may be aliases instead of types.
*/
template isAlias(alias a)
{
    enum bool isAlias = true;
}

/// ditto
template isAlias(T)
{
    enum bool isAlias = false;
}

/**
Is true if T is a type and not an alias. It's useful when you have
a variadic type (T...) and some of its components may be types or aliases..
*/
template isType(T)
{
    enum bool isType = true;
}

/// ditto
template isType(alias a)
{
    enum bool isType = false;
}

/**
The constant template (akin to the constant function).
Once instantiated with a type, its next instantiation will gives the original type.
It's sometimes useful while mapping templates, composing templates or acting on types in general.

Example:
----
alias Constant!int CInt;
assert(is(StaticMap!(CInt,double,int,string,char) == TypeTuple!(int,int,int,int)));
----
*/
template Constant(T)
{
    template Constant(U...)
    {
        alias T Constant;
    }
}

/// The void template: whatever types you give it, it's void.
template Void(T...) {}

/// The null template: takes no type, is void (seems strange, but sometime useful)
template Null() {}

/**
The identity template: becomes the types you gives it as parameters. If you give
it one type, it alias itself to this type, not TypeTuple!type.
*/
template Id(T...)
{
    static if (T.length > 1) // to avoid (int) (ie: a TypeTuple), when I want int
        alias T Id;
    else
        alias T[0] Id;
}

string composeImpl(Templ...)()
{
    string b = "template Compose(T...) { alias ";
    string e = " Compose;}";
    string m = TemplateList!Templ ~ "T" ~ ParensList!Templ;

    return b ~ m ~ e;
}

// I couldn't get it to work with CTFE...
template TemplateList(alias templ1, Rest...)
{
    static if (Rest.length)
        enum string TemplateList = __traits(identifier, templ1) ~ "!(" ~ TemplateList!Rest;
    else
        enum string TemplateList = __traits(identifier, templ1) ~ "!(";
}

template ParensList(alias templ1, Rest...)
{
    static if (Rest.length)
        enum string ParensList = ")" ~ ParensList!Rest;
    else
        enum string ParensList = ")";
}

/**
_Compose n templates together. This is one very powerful meta-template, if
I may say so...

Example:
----
alias Compose!(Cycle, ArrayType) MkCycle; // Takes a T, makes a Cycle!(T[]).
----
*/
template Compose(Templates...)
{
    mixin(composeImpl!(Templates));
}

/// Alias itself to T[]. Useful for template composition.
template ArrayType(T)
{
    alias T[] ArrayType;
}


/**
_Apply types $(M T) on successive templates (that is, instantiate them with $(M T)) and makes a TypeTuple from it.
It's the complement of $(M StaticMap), which takes a template an applies it on successive types.
Usage:
----
Apply!(SomeTypes).On!(Templates).
----

Example:
----
alias Apply!(int,double) Applier;
alias Applier.On!(MkDelegate, Tuple, Doubler, CommonType) Result;
assert(is(Result == TypeTuple!(int delegate(double), Tuple!(int,double), int, double, int, double, double)));
----
*/
template Apply(T...)
{
    /// ditto
    template On(alias templ1, Rest...)
    {
        static if (Rest.length)
            mixin("alias TypeTuple!(" ~ __traits(identifier, templ1) ~ "!(T), On!(Rest)) On;");
        else
            mixin("alias " ~ __traits(identifier,templ1) ~ "!(T) On;");
    }
}

/**
Like $(M Apply.On), but reversed: first, the templates, then the type.
Usage:
----
Instantiate!(SomeTemplates).With!(SomeTypes).
----
*/
template Instantiate(alias templ1, Rest...)
{
    template With(T...)
    {
        static if (Rest.length)
            mixin("alias TypeTuple!(" ~ __traits(identifier, templ1) ~ "!T, Instantiate!(Rest).With!T) With;");
        else
            mixin("alias " ~__traits(identifier, templ1) ~ "!T With;");
    }
}
/// The type of a delegate with corresponding parameters.
template MkDelegate(ReturnType, ParameterTypes...)
{
    alias ReturnType delegate(ParameterTypes) MkDelegate;
}

/**
Usage:
----
TransferParamsTo!(someTemplate).From!(someTemplatedType).
----
It will extract the template parameters from $(M someTemplatedType) and instantiate $(M someTemplate) with them.

Example:
----
alias TransferParamsTo!Repeat MkRepeat;
alias MkRepeat.From!(Cycle!(int[])) R; // takes a Cycle!(Range), extracts Range, makes a Repeat from it.
assert(is(R == Repeat!(int[]))); // R is a Repeat!(int[])
----

Note: so, $(M TransferParamsTo) can be seen as a 'function' from a domain of types to another domain. It's a functor,
in a mathematical/Haskell sense (which has nothing to do with a C++ functor).
*/
template TransferParamsTo(alias templ)
{
    template From(T)
    {
        mixin("alias " ~ __traits(identifier, templ) ~ "!(" ~ between!('(',')',T.stringof)[1] ~ ") From;");
    }
}


/**
An small switch-like template to produce different code depending on the type of value. The Default class
is used to indicate (wait for it) a default value.
----
int i; double d; string s;
alias SwitchOnType!(i, int, "It's an int", double, "It's a double", Default, "It's something else") switchi;
alias SwitchOnType!(d, int, "It's an int", double, "It's a double", Default, "It's something else") switchd;
alias SwitchOnType!(s, int, "It's an int", double, "It's a double", Default, "It's something else") switchs;
assert(switchi == "It's an int");
assert(switchd == "It's a double");
assert(switchs == "It's something else");
----
BUG:
Well, not a bug really, but a severe limitation: the 'Action' alias are all evaluated at compile-time, there are not lazy.
I found out it drastically limits the interest of this template: it cannot be used as a way to mixin different pieces of code
based on a directing type.
Example:
----
// Different predicate strings based on value's type.
alias SwitchOnType!(value,
                    char,    "a.field[1] == '" ~ value ~ "'",         /+ Incorrect if value is an int +/
                    string,  Format!("a.field[1] == \"%s\" ", value), /+ Incorrect if value is a char +/
                    Default, "a.field[1] == " ~ to!string(value)
                    ) predicate;
----
*/
class Default {};
/// ditto
template SwitchOnType(alias value, Type, alias Action, Rest...) {
    static if (is(typeof(value) == Type)) {
        alias Action SwitchOnType;
    }
    else {
        static if (Rest.length >0) {
            alias SwitchOnType!(value, Rest) SwitchOnType;
        }
    }
}
/// ditto
template SwitchOnType(alias value, Type : Default, alias Action) {
    alias Action SwitchOnType;
}

unittest
{
    int i; double d; string s;
    alias SwitchOnType!(i, int, "It's an int", double, "It's a double", Default, "It's something else") switchi;
    alias SwitchOnType!(d, int, "It's an int", double, "It's a double", Default, "It's something else") switchd;
    alias SwitchOnType!(s, int, "It's an int", double, "It's a double", Default, "It's something else") switchs;
    assert(switchi == "It's an int");
    assert(switchd == "It's a double");
    assert(switchs == "It's something else");
}
