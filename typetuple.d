// Written in the D programming language

/**
This module defines templates on typetuples (complementary, sometimes similar to std.typetuple/std.traits):
reversing, rotating, extracting, filtering, unfolding, etc, all on typetuples.


License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud and Simen Kj&aelig;r&aring;s.

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.typetuple;

import std.traits,
       std.typecons,
       std.typetuple;

import dranges.templates,
       dranges.traits;

version(unittest)
{
    import std.stdio;
}

/**
Alias itself to the .init value of a typetuple. When you have a typetuple (T...)
inside a template, you cannot do (T.init), DMD does not accept it. Use Init!T instead.
*/
template Init(T...)
{
    static if (T.length == 1 && is(T == class))
        T Init = new T;
    else
        T Init;

}

/**
Compares tuples that might contain a mixture of types and values.
Author:
Simen Kj&aelig;r&aring;s.

Usage:
----
SameTuple!(FirstTuple).As!(SecondTuple);
----

Example:
----
static assert(SameTuple!(int, int).As!(int, int));
static assert(SameTuple!(int, "foo").As!(int, "foo"));
static assert(!SameTuple!(int, "foo").As!("foo", int));
----
*/
template SameTuple(T...) {
    template As(U...) {
        enum As = is( SameTupleImpl!T == SameTupleImpl!U );
    }
}

struct SameTupleImpl(T...) {}

unittest {
    static assert(SameTuple!(int, int).As!(int, int));
    static assert(SameTuple!(float).As!(float));
    static assert(SameTuple!("foo").As!("foo"));
    static assert(!SameTuple!("foo").As!("bar"));
    static assert(!SameTuple!(int ).As!("bar"));
    static assert(!SameTuple!(int ).As!(float));
    static assert(SameTuple!(int, "foo").As!(int, "foo"));
    static assert(!SameTuple!(int, "foo").As!("foo", int));
    static assert(SameTuple!().As!());
    static assert(!SameTuple!(int).As!());
    static assert(!SameTuple!().As!(int));
    static assert(!SameTuple!("foo").As!());
    static assert(!SameTuple!().As!("foo"));
}

/**
Checks if one tuple contains another.
Author:
Simen Kj&aelig;r&aring;s.

Usage:
----
Contained!(SmallTuple).In!(BigTuple);
----

Example:
----
static assert(Contained!(int).In!(float, int));
static assert(!Contained!(int).In!(float, "foo"));
static assert(Contained!(int,"foo").In!(float, int, "foo", "bar"));
----
 */
template Contained(T...) {
   template In(U...) {
       static if (T.length == 0) {
           enum In = true;
       } else static if (U.length >= T.length) {
           enum In = SameTuple!(T).As!( U[0..T.length]) ||
               Contained!(T).In!(U[1..$]);
       } else {
           enum In = false;
       }
   }
}

unittest {
   static assert(Contained!(int).In!(float, int));
   static assert(!Contained!(int).In!(float, "foo"));
   static assert(Contained!(int,"foo").In!(float, int, "foo", "bar"));
   static assert(!Contained!(int,"foo").In!(float, int, "bar", "foo"));
   static assert(Contained!().In!(float, int, "bar", "foo"));
}


/**
Evaluates to $(D F!(T[0..tupleLength]) && F!(T[tupleLength..2*tupleLength]) && ... && F[T[$-tupleLength..$]]).
Author:
Simen Kj&aelig;r&aring;s.

Example:
----
static assert(allTuplesSatisfy!(Contained!(int).In, 2, int, float, "foo", int));
static assert(!allTuplesSatisfy!(Contained!(int).In, 2, int, float, "foo",string));
----
 */
template allTuplesSatisfy( alias F, uint tupleLength, T... ) {
   static assert( !( T.length % tupleLength ) );

   static if ( T.length == tupleLength ) {
       enum allTuplesSatisfy = F!( T );
   } else {
       enum allTuplesSatisfy = F!( T[0..tupleLength] ) && allTuplesSatisfy!( F, tupleLength, T[tupleLength..$] );
   }
}

unittest {
   static assert(allTuplesSatisfy!(Contained!(int).In, 2, int, float, "foo", int));
   static assert(!allTuplesSatisfy!(Contained!(int).In, 2, int, float, "foo",string));
}

/**
Repeats a type or typetuple $(D num) times.
Author:
Simen Kj&aelig;r&aring;s.

Example:
----
static assert(SameTuple!(RepeatTuple!(4, int)).As!(int, int, int, int));
static assert(SameTuple!(RepeatTuple!(4, "foo")).As!("foo", "foo", "foo", "foo"));
static assert(SameTuple!(RepeatTuple!(2, int, "foo")).As!(int, "foo", int, "foo"));
static assert(!SameTuple!(RepeatTuple!(2, int)).As!());
----
 */
template RepeatTuple( uint num, T... ) {
   static if ( num > 1 ) {
       alias TypeTuple!( T, RepeatTuple!( num -1, T ) ) RepeatTuple;
   } else {
       alias T RepeatTuple;
   }
}

unittest {
   static assert(SameTuple!(RepeatTuple!(4, int)).As!(int, int, int, int));
   static assert(SameTuple!(RepeatTuple!(4, "foo")).As!("foo", "foo", "foo", "foo"));
   static assert(SameTuple!(RepeatTuple!(2, int, "foo")).As!(int, "foo", int, "foo"));
   static assert(!SameTuple!(RepeatTuple!(2, int)).As!());
}

/**
Extracts some types from the variadic type tuple R according to the indices given by array (a static array).
[0,1,2] means 'the first, second and third types'. The indices can be repeated or omitted and the array
can be longer than R ([0,1,2,2,3,0,0,2,3]...). In the latter case, the resulting type tuple will obviously be longer
than R.
Examples:
----
alias TypeTuple!(int,double,string) TT;
alias ExtractType!([0,1],TT) E1;
alias ExtractType!([1,0],TT) E2;
alias ExtractType!([1],TT) E3;
alias ExtractType!([1,0,2,2,0],TT) E4;

assert(is(E1 == TypeTuple!(int,double)));
assert(is(E2 == TypeTuple!(double,int)));
assert(is(E3 == TypeTuple!(double)));
assert(is(E4 == TypeTuple!(double,int,string,string,int)));
----
Note: why a static array instead of free parameters like this: $(M ExtractType!(0,2,3,1, TT))? Because the type tuple and the
index list are both of variable length, and the tuple can contain any template parameter, including ints. A simplified version
working only on pure types tuples could use $(M StaticTakeWhile) to get the parameters that are of integral type and then deduce
the rest is the type tuple.
*/
template ExtractType(alias array, R...) {
    static if (array.length == 1) {
        alias TypeTuple!(R[array[0]]) ExtractType;
    }
    else {
        alias TypeTuple!(R[array[0]], ExtractType!(array[1..$], R)) ExtractType;
    }
}

unittest
{
    alias TypeTuple!(int,double,string) TT;
    alias ExtractType!([0,1],TT) E1;
    alias ExtractType!([1,0],TT) E2;
    alias ExtractType!([1],TT) E3;
    alias ExtractType!([1,0,2,2,0],TT) E4;

    assert(is(E1 == TypeTuple!(int,double)));
    assert(is(E2 == TypeTuple!(double,int)));
    assert(is(E3 == TypeTuple!(double)));
    assert(is(E4 == TypeTuple!(double,int,string,string,int)));
}

/**
If n>0, it rotate a TypeTuple on the left by n positions (it takes the first n types and puts them at the end).
for n== 0, it does nothing (it's the identity template).
If n<0, it rotates on the right (takes the last n types and puts them at the beginning).
Example:
----
alias TypeTuple!(int,double,string) TT;
alias RotateTypes!(1,TT) R1;   // (double, string, int)
alias RotateTypes!(0,TT) R0;   // (int, double, string)
alias RotateTypes!(5,TT) R5;   // (string, int, double)
alias RotateTypes!(-1,TT) R_1; // (string, int, double)
alias RotateTypes!(-5,TT) R_5; // (double, string, int)

assert(is(R1 == TypeTuple!(double,string,int)));
assert(is(R0 == TT));
assert(is(R5 == TypeTuple!(string,int,double))); // equivalent to Rotate!(2,TT)
assert(is(R_1 == TypeTuple!(string,int,double)));
assert(is(R_5 == TypeTuple!(double,string,int))); // equivalent to Rotate!(-2,TT) and also to Rotate!(1,TT)

alias TypeTuple!(int) TT2;
assert(is(RotateTypes!(1,TT2) == TT2)); // one type: unchanged by rotation

alias StaticFilter!(isIntegral, TT2) F; // double is not an integral type -> F is empty
assert(is(RotateTypes!(1,F) == F)); // zero type: also unchanged by rotation.
----

To Be Documented: curried version: alias RotateTypes!1 R1;
*/
template RotateTypes(int n, R...) if (R.length>0 && n>=0)
{
    alias TypeTuple!(R[(n%R.length)..$],R[0..(n%R.length)]) RotateTypes;
}

/// ditto
template RotateTypes(int n, R...) if (R.length>0 && n<0)
{
    alias TypeTuple!(R[$-((-n)%R.length)..$],R[0..$-((-n)%R.length)]) RotateTypes;
}

// useless: is R == TypeTuple!(), it's the curried template that gets instantiated.
template RotateTypes(int n, R...) if (R.length == 0)
{
    alias R RotateTypes;
}

/// ditto
template RotateTypes(int n)
{
    template RotateTypes(R...)
    {
        static if (R.length > 0)
        {
            static if (n == 0)
                alias R RotateTypes; // Identity template on types
            else static if (n > 0)
                alias TypeTuple!(R[(n%R.length)..$],R[0..(n%R.length)]) RotateTypes;
            else //         n <0
                alias TypeTuple!(R[$-((-n)%R.length)..$],R[0..$-((-n)%R.length)]) RotateTypes;
        }
        else // R.length == 0 ie, R is TypeTuple!()
            alias R RotateTypes;
    }
}

unittest
{
    alias TypeTuple!(int,double,string) TT;
    alias RotateTypes!(1,TT) R1;
    alias RotateTypes!(0,TT) R0;
    alias RotateTypes!(5,TT) R5;
    alias RotateTypes!(-1,TT) R_1;
    alias RotateTypes!(-5,TT) R_5;

    assert(is(R1 == TypeTuple!(double,string,int)));
    assert(is(R0 == TT));
    assert(is(R5 == TypeTuple!(string,int,double))); // equivalent to Rotate!(2,TT)
    assert(is(R_1 == TypeTuple!(string,int,double)));
    assert(is(R_5 == TypeTuple!(double,string,int))); // equivalent to Rotate!(-2,TT) and also to Rotate!(1,TT)

    alias TypeTuple!(double) TT2;
    assert(is(RotateTypes!(1,TT2) == TT2)); // one type: unchanged by rotation.
}

/**
Takes a type tuple and reverses it.
Example:
----
alias TypeTuple!(int,double,string) TT;
alias ReverseTypes!TT R;
assert(is(R == TypeTuple!(string,double,int)));

alias TypeTuple!(double) TT2;
assert(is(ReverseTypes!TT2 == TT2)); // one type: unchanged by inversion.

alias StaticFilter!(isIntegral, TT2) F; // double is not an integral type -> F is empty
assert(is(ReverseTypes!F == F)); // no type: unchanged by inversion.
----
*/
template ReverseTypes(T...) {
    static if (T.length)
        alias TypeTuple!(T[$-1], ReverseTypes!(T[0..$-1])) ReverseTypes;
    else
        alias TypeTuple!() ReverseTypes;
}

unittest
{
    alias TypeTuple!(int,double,string) TT;
    alias ReverseTypes!TT R;
    assert(is(R == TypeTuple!(string,double,int)));

    alias TypeTuple!(double) TT2;
    assert(is(ReverseTypes!TT2 == TT2)); // one type: unchanged by inversion.

    alias StaticFilter!(isIntegral, TT2) F; // double is not an integral type -> F is empty
    assert(is(ReverseTypes!F == F)); // no type: unchanged by inversion.
}

/**
Swap the types at index i1 and index i2 in a TypeTuple.
Example:
----
alias TypeTuple!(int, double, string, short) Test;

assert(is(SwapTypes!(1,3,Test) == TypeTuple!(int,short,string,double)));
assert(is(SwapTypes!(3,1,Test) == TypeTuple!(int,short,string,double)));

assert(is(SwapTypes!(1,1,Test) == Test));
----
*/
template SwapTypes(size_t i1, size_t i2, R...)
{
    static if (i1 < R.length && i2 < R.length)
    {
        static if (i1 == i2) {
            alias R SwapTypes;
        }
        else {
            alias TypeTuple!(R[0..Min!(i1,i2)],R[Max!(i1,i2)], R[Min!(i1,i2)+1..Max!(i1,i2)], R[Min!(i1,i2)], R[Max!(i1,i2)+1..$]) SwapTypes;
        }
    }
    else
        static assert(false, "SwapTypes index out of range");
}

unittest
{
    alias TypeTuple!(int, double, string, short) Test;

    assert(is(SwapTypes!(1,3,Test) == TypeTuple!(int,short,string,double)));
    assert(is(SwapTypes!(3,1,Test) == TypeTuple!(int,short,string,double)));

    assert(is(SwapTypes!(1,1,Test) == Test));
}

/**
Cut a typetuple into segments of length n. The segments are $(M std.typecons.Tuple)s, not type tuples,
to avoid auto-flattening. It will not compile if n == 0 or if n do not cut the typetuple in equal parts.
Example:
----
alias TypeTuple!(int, double, string, int delegate()) Types;
alias SegmentTypes!(2, Types) Segments;
assert(is(Segment == TypeTuple!(Tuple!(int,double), Tuple!(string, int delegate())) ));
----
*/
template SegmentTypes(int n, T...) if (n > 0 && T.length % n == 0)
{
    static if (T.length)
        alias TypeTuple!(Tuple!(T[0..n]), SegmentTypes!(n, T[n..$])) SegmentTypes;
    else
        alias TypeTuple!() SegmentTypes;
}

/// Is true iff all elements of the variadic list are equal (as tested by ==).
template AllEqual(alias a, Rest...)
{
    static if (Rest.length)
        enum bool AllEqual = (a == Rest[0]) && AllEqual!(Rest);
    else
        enum bool AllEqual = true;
}

/// Is true iff all types in the typetuple are equal.
template AllEqual(Types...)
{
    static if (Types.length > 1)
        enum bool AllEqual = is(Types[0] == Types[1]) && AllEqual!(Types[1..$]);
    else
        enum bool AllEqual = true;
}

/**
creates a TypeTuple of n T's, repeated. If n == 0, it becomes the empty TypeTuple: TypeTuple!().
----
alias TypeNuple!(int, 3) TN3;
assert(is(TN3 == TypeTuple!(int,int,int)));
alias TypeNuple!(int, 1) TN1;
assert(is(TN1 == TypeTuple!(int)));
assert(!is(TN1 == int)); // TypeTuple!int is not an int.
----
*/
template TypeNuple(T, size_t n)
{
    static if(n == 0)
        alias TypeTuple!() TypeNuple;
    else
        alias TypeTuple!(T,TypeNuple!(T, n-1)) TypeNuple;
}

///// ditto
//template TypeNuple(string s, size_t n) {
//    static if(n == 0) {
//        alias TypeTuple!() TypeNuple;
//    }
//    else {
//        alias TypeTuple!(s,TypeNuple!(s, n-1)) TypeNuple;
//    }
//}

/// ditto
template TypeNuple(alias a, size_t n)
{
    static if(n == 0)
        alias TypeTuple!() TypeNuple;
    else
        alias TypeTuple!(a,TypeNuple!(a, n-1)) TypeNuple;
}

unittest
{
    alias TypeNuple!(int, 3) TN3;
    assert(is(TN3 == TypeTuple!(int,int,int)));
    alias TypeNuple!(int, 1) TN1;
    assert(is(TN1 == TypeTuple!(int)));
    assert(!is(TN1 == int)); // TypeTuple!int is not an int.
}

/**
Transforms a static array into a TypeTuple.
Example:
----
alias Expansion!(int[3]) E; // Gives TypeTuple!(int, int, int).
----

Note: int[1] gives TypeTuple!(int), which is not of type int.
*/
template Expansion(T : U[n], U, size_t n) {
    alias TypeNuple!(U, n) Expansion;

}
unittest {
    assert(is(Expansion!(int[3]) == TypeTuple!(int, int, int)));
    assert(is(Expansion!(int[1]) == TypeTuple!(int)));
    assert(!is(Expansion!(int[1]) == int));
    assert(is(Expansion!(int[0]) == TypeTuple!()));
    assert(!is(Expansion!(int[]) == TypeTuple!(int)));
    assert(!is(Expansion!(int) == TypeTuple!(int)));
}

/**
D's typetuple automatically flatten, which is interesting on certain occasions, but not when you're
trying to create a deeply nested structure, such as a tree of types. For those occasions, using std.Typecons.Tuple
is a possibility. This template is for going back: given a typetuple, possibliy containing nested tuples, it flattens
them all and returns a flat typetuple.

Example:
----
alias TypeTuple!(int, double, string) Flat;
alias TypeTuple!(Tuple!(int,double), string, Tuple!Flat, Tuple!(int, Tuple!int)) Nested;

assert(is(FlattenTuple!Flat == Flat));
assert(is(FlattenTuple!Nested == TypeTuple!(int,double,string,int,double,string,int,int)));
----
*/
template FlattenTuple(T...)
{
    static if (T.length)
        static if (isTuple!(T[0]))
            alias TypeTuple!(FlattenTuple!(T[0].Types), FlattenTuple!(T[1..$])) FlattenTuple;
        else
            alias TypeTuple!(T[0], FlattenTuple!(T[1..$])) FlattenTuple;
    else
        alias TypeTuple!() FlattenTuple;
}

unittest
{
    alias TypeTuple!(int, double, string) Flat;
    alias TypeTuple!(Tuple!(int,double), string, Tuple!Flat, Tuple!(int, Tuple!int)) Nested;

    assert(is(FlattenTuple!Flat == Flat));
    assert(is(FlattenTuple!Nested == TypeTuple!(int,double,string,int,double,string,int,int)));
}

/**
Usage:
----
Interleave!(FirstTypeTuple).With!(SecondTypeTuple):
----
Given T0, T1, T2, ..., Ti and U0, U1, ... Uj, it will interleavs the types and becomes T0, U0, T1, U1, ...
If one of the tuples is longer than the other, its tail will be appended.
Example:
----
alias TypeTuple!(byte,short,int,long,ubyte,ushort,uint,ulong) IntegralTypes;
alias TypeTuple!(float,double,real) FloatTypes;
alias Interleave!IntegralTypes.With!FloatTypes NumericalTypes;

assert(is(NumericalTypes == TypeTuple!(byte,float,short,double,int,real,long,ubyte,ushort,uint,ulong)));
----
*/
template Interleave(T...)
{
    template With(U...)
    {
        static if(T.length)
            static if(U.length)
                alias TypeTuple!(T[0],U[0], Interleave!(T[1..$]).With!(U[1..$])) With;
            else
                alias T With;
        else
            alias U With;
    }
}

unittest
{
    alias TypeTuple!(byte,short,int,long,ubyte,ushort,uint,ulong) IntegralTypes;
    alias TypeTuple!(float,double,real) FloatTypes;
    alias Interleave!IntegralTypes.With!FloatTypes NumericalTypes;

    assert(is(NumericalTypes == TypeTuple!(byte,float,short,double,int,real,long,ubyte,ushort,uint,ulong)));

    assert(is(Interleave!().With!() == TypeTuple!()));
    assert(is(Interleave!IntegralTypes.With!() == IntegralTypes));
    assert(is(Interleave!().With!IntegralTypes == IntegralTypes));

    assert(Interleave!(0,2,4,6).With!(1,3,5,7).stringof == TypeTuple!(0,1,2,3,4,5,6,7).stringof);
}

/**
Just an exercice: blind-coding std.traits.staticMap. Aliases
itself to the TypeTuple (F!T0, F!T1, ...)
*/
template StaticMap(alias F, T...)
{
    static if (T.length == 0) {
        alias TypeTuple!() StaticMap;
    }
    else {
        alias TypeTuple!(F!(T[0]), StaticMap!(F, T[1 .. $])) StaticMap;
    }
}

unittest
{
    alias TypeTuple!(int, uint, short) TT;
    alias StaticMap!(Unsigned, TT) MTT;
    assert(is(MTT == TypeTuple!(uint,uint,ushort)));
}

/**
The filter equivalent to StaticMap: alias itself to a TypeTuple
containing the types in T that verify the predicate Pred
----
alias TypeTuple!(int, double, string, long) TT;
assert(is(StaticFilter!(isIntegral, TT) == TypeTuple!(int, long)));
assert(is(StaticFilter!(hasLength2, int[], int[3], int) == TypeTuple!(int[], int[3])));
----
*/
template StaticFilter(alias Pred, T...)
{
    static if (T.length == 0)
    {
        alias TypeTuple!() StaticFilter;
    }
    else
    {
        static if (Pred!(T[0])) {
            alias TypeTuple!(T[0], StaticFilter!(Pred, T[1 .. $])) StaticFilter;
        }
        else {
            alias StaticFilter!(Pred, T[1 .. $]) StaticFilter;
        }
    }
}

version(unittest)
{
    import std.range: hasLength;
}

unittest
{
    alias TypeTuple!(int, double, string, long) TT;
    assert(is(StaticFilter!(isIntegral, TT) == TypeTuple!(int, long)));
    assert(is(StaticFilter!(hasLength, int[], int[3], int) == TypeTuple!(int[], int[3])));
}

/**
Aliases itself to a repeated application of the binary template F on the types of T, like reduce
does on ranges.
Example:
----
template CT(T,T2) {
    alias CommonType!(T,T2) CT;
}

template Tup(T1,T2) {
    alias Tuple!(T1, T2) Tup; // That's std.typecons.Tuple, NOT std.typetuple.TypeTuple
}

alias StaticReduce!(CT, int, double, int, long) SR1; // Equivalent to CommonType!(int,double,int,long)
assert(is(SR1 == double));
alias StaticReduce!(Tup, int, double, int, long) SR2;
assert(is(SR2 == Tuple!(int, Tuple!(double, Tuple!(int, long))))); // Non-flattening tuples
----
*/
template StaticReduce(alias F, T...) {
    static if (T.length == 0)
        static assert(false, "StaticReduce used on an empty typetuple.");
    static if (T.length == 1)
        alias T[0] StaticReduce;
    static if (T.length > 1)
        alias F!(T[0], StaticReduce!(F, T[1..$])) StaticReduce;
}

template CT(T,T2) {
    alias CommonType!(T,T2) CT;
}

template Tup(T1,T2) {
    alias Tuple!(T1, T2) Tup; // That's std.typecons.Tuple, NOT std.typetuple.TypeTuple
}

unittest {
    alias StaticReduce!(CT, int, double, int, long) SR1;
    assert(is(SR1 == double));
    alias StaticReduce!(Tup, int, double, int, long) SR2;
    assert(is(SR2 == Tuple!(int, Tuple!(double, Tuple!(int, long)))));
}

/// alias itself to the type of alias a.
template TypeOf(alias a)
{
    alias typeof(a) TypeOf;
}

/**
Maps the $(M Mapper) template on the alias list.
*/
template MapOnAlias(alias Mapper, alias current, Rest...)
{
    static if (Rest.length)
        alias TypeTuple!(Mapper!current, MapOnAlias!(Mapper, Rest)) MapOnAlias;
    else
        alias Mapper!current MapOnAlias;
}

template MapOnAlias(alias Mapper)
{
    alias TypeTuple!() MapOnAlias;
}

/// Same as $(M StaticReduce), but on an alias list.
template ReduceOnAlias(alias Reducer, alias current, Rest...)
{
    alias StaticReduce0!(Reducer, current, Rest) ReduceOnAlias;
}

/**
Folds (reduces) the T list, given a reducing template F and an initial accumulator value.
F must be a binary template and accumulator a value accepted by F as first parameter.
*/
template StaticReduce0(alias F, alias accumulator, T...) {
    static if (T.length == 0)
        alias accumulator StaticReduce0;
    else
        alias StaticReduce0!(F, F!(accumulator, T[0]), T[1..$]) StaticReduce0;
}

/**
Gives the TypeTuple resulting from the sucessive applications of F to reduce
the T list.
See_Also: $(M dranges.algorithm.scan).
*/
template StaticScan(alias F, T...)
{
    static if (T.length == 0)
        alias TypeTuple!() StaticScan; // This case should never happen with normal use
    static if (T.length == 1)
        alias TypeTuple!(T[0]) StaticScan;
    else
        alias TypeTuple!(T[0], StaticScan!(F, F!(T[0], T[1]), T[2..$])) StaticScan;
}

/**
Gives the typetuple (T, F!(T), F!(F!(T)), F!(F!(F!(T))), ...), up to times applications of F.
*/
template StaticIterate(size_t times, alias F, T...)
{
    static if (times == 0)
        alias TypeTuple!(T) StaticIterate;
    else
        alias TypeTuple!(T, StaticIterate!(times-1, F, F!T)) StaticIterate;
}

/// The same, but on an alias list. Useful for iterating on values: 0,1,2,3...
template StaticIterateOnAlias(size_t times, alias F, alias value)
{
    static if (times == 0)
        alias value StaticIterate;
    else
        alias TypeTuple!(value, StaticIterate!(times-1, F, F!value)) StaticIterate;
}

/**
Given a template F and a state State, unfolds F times _times.
Applying F on a type must give a typetuple whose first element is the result and the rest
the next state.
See_Also: $(M dranges.algorithm2.unfold), to get some grip on this.
*/
template StaticUnfold(size_t times, alias F, State...)
{
    static if (times == 0)
        alias TypeTuple!() StaticUnfold;
    else
        alias TypeTuple!(F!(State)[0], StaticUnfold!(times-1, F, F!State[1..$])) StaticUnfold;
}

/// Given a typetuple T, gives (T[0], T[step], T[2*step], T[3*step],...)
template StaticStride(alias step, T...) if (step > 0)
{
   static if (T.length == 0)
       alias TypeTuple!() StaticStride;
   else static if (T.length <= step)
       alias TypeTuple!(T[0]) StaticStride;
   else
       alias TypeTuple!(T[0], StaticStride!(step, T[step..$])) StaticStride;
}

/+ See SegmentTypes
template StaticGroup(alias size, T...)
{
    static if (T.length == 0)
        alias TypeTuple!() StaticGroup;
    else
        alias TypeTuple!(Tuple!(T[0..size]), StaticGroup!(size, T[size..$])) StaticGroup;
}
+/

/**
Takes elements in a typetuple as long as the predicate template $(M pred) is true
for the current element.
Example:
----
alias TypeTuple!(int, short, byte, double, int, long) Types;
alias StaticTakeWhile!(isIntegral, Types) FirstIntegrals;
asser(is( FirstIntegrals == TypeTuple!(int,short,byte))); // stopped when double was encountered
----
*/
template StaticTakeWhile(alias pred, Types...)
{
    static if (Types.length && pred!(Types[0]))
        alias TypeTuple!(Types[0], StaticTakeWhile!(pred, Types[1..$])) StaticTakeWhile;
    else
        alias TypeTuple!() StaticTakeWhile;
}

/// The cousin of $(M StaticTakeWhile). Drops types from a typetuple as long as the predicate is true.
template StaticDropWhile(alias pred, Types...)
{
    static if (Types.length && pred!(Types[0]))
        alias StaticDropWhile!(pred, Types[1..$]) StaticDropWhile;
    else
        alias Types StaticDropWhile;
}

/**
Rotates a typetuple as long as the predicate template $(M pred) is true for the first element.
If a complete rotation is done ($(M pred) gives true for all elements of T), $(M _StaticRotateWhile) recognizes this and aliases itself to Types
instead of cycling forever...
*/
template StaticRotateWhile(alias pred, Types...)
{
    alias StaticRotateWhileImpl!(pred, 0, Types) StaticRotateWhile;
}

template StaticRotateWhileImpl(alias pred, size_t n, Types...)
{
    static if (n < Types.length && pred!(Types[0]))
        alias StaticRotateWhileImpl!(pred, n+1, Types[1..$], Types[0]) StaticRotateWhileImpl;
    else
        alias Types StaticRotateWhileImpl;
}

template AddOne(alias value) {
    enum AddOne = value+1;
}

/// The TypeTuple (0,1,2, ..., to) (to is included)
template StaticRange(alias to)
{
    alias StaticIterateOnAlias!(to, AddOne, 0) StaticRange;
}

/// The TypeTuple (from, from+1, ..., to) (to is included)
template StaticRange(alias from, alias to)
{
    alias StaticIterateOnAlias!(to - from, AddOne, from) StaticRange;
}

/// The TypeTuple (from, from+step, from+2*step, ... to). to is not necessarily included if step 'jumps' above it.
template StaticRange(alias from, alias to, alias step)
{
    alias StaticStride!(step, StaticRange!(from, to)) StaticRange;
}



// add Types[0] to Types[1..$]
template AddToSorted(alias Pred, Types...)
{
    static if (Types.length < 2)                            // 0 or 1 type: already sorted.
        alias Types AddToSorted;
    else static if (Pred!(Types[0], Types[1]) <= 0) // test left extremity
        alias Types AddToSorted;
    else static if (Pred!(Types[0], Types[$-1]) > 0)// test right extremity
        alias TypeTuple!(Types[1..$], Types[0]) AddToSorted;
    else static if (Pred!(Types[0], Types[($+1)/2]) == 0)    // test with pivot (middle)
        alias TypeTuple!(Types[1..($+1)/2], Types[0], Types[($+1)/2..$]) AddToSorted;
    else static if (Pred!(Types[0], Types[($+1)/2]) < 0)    // test with pivot (middle): left hand branch
        alias TypeTuple!(AddToSorted!(Pred, Types[0..($+1)/2]), Types[($+1)/2..$]) AddToSorted;
    else static if (Pred!(Types[0], Types[($+1)/2]) > 0)    // test with pivot (middle): right hand branch
        alias TypeTuple!(Types[1..($+1)/2], AddToSorted!(Pred, Types[0], Types[($+1)/2..$])) AddToSorted;
    else static assert(false);
}

template SortTypesImpl(alias Pred, Types...)
{
    template AddType(Sorted, NewType) // Sorted is sorted inside a Tuple, to propagate it
    {
        alias Tuple!(AddToSorted!(Pred, NewType, Sorted.Types)) AddType;
    }

    alias StaticReduce0!(AddType, Tuple!(Types[0]), Types[1..$]).Types result;
}

/**
Sort types in $(M Types), according to predicate $(M Pred). $(M Pred) is a binary template
that must alias itself to 0 if types are equal, to -1 if T1 < T2 and +1 if T1 > T2.
If you do not care for the precise ordering (such as when you just want to verify that two tuples
are the same), $(M you can use dranges.templates.CompareTypes) as a predicate.
*/
template SortTypes(alias Pred, Types...)
{
    alias SortTypesImpl!(Pred, Types).result SortTypes;
}

/// Alias itself to the nth field/type in a TypeTuple. Useful for template composition.
template NthType(size_t n)
{
    template NthType(T...) if (T.length > n)
    {
        alias T[n] NthType;
    }
}

/// Same as NthType. Alias itself to the first type in a typetuple.
template First(T...) if (T.length)
{
    alias T[0] First;
}

/// Same as NthType. Alias itself to the second type in a typetuple.
template Second(T...) if (T.length > 1)
{
    alias T[1] Second;
}

/**
Alias itself to the last type in a TypeTuple. As the previous template, it's sometimes useful
while composing templates.
*/
template Last(T...) if (T.length)
{
    alias T[$-1] Last;
}

/**
Alias itself to all types except the first in a TypeTuple.
*/
template Tail(T...) if (T.length)
{
    alias T[1..$-1] Tail;
}

/// Doubles a TypeTuple. ie: from (int, double), makes a (int,double,int,double).
template Doubler(T...)
{
    alias TypeTuple!(T,T) Doubler;
}
