// Written in the D programming language

/**
To Be Documented. Lots of warts still.

This module defines a _ function that takes lvalues and assign them, while deconstructing.

----
int a, b;
_(a,b) = tuple(b,a); // swap
_(a,b) = tuple(b,a+b); // fibonacci

int[] arr = [0,1,2,3,4];
int [] c;
_(a,b,c) = arr; // a = 0, b = 1, c = [2,3,4]
----

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.reftuple;

import std.range;
import std.traits;
import std.typetuple;
import std.typecons;
import std.variant;
import std.stdio;

template toPointer(T) { alias T* toPointer;}

struct AssignTuple(T...) {
    alias TypeTuple!(staticMap!(toPointer, T)) PT;
    PT pFields;
    this(ref T fields) { foreach(i, Unused; PT) pFields[i] = &fields[i];}

    void opAssign(TT...)(Tuple!TT newFields) /*if (TT.length > 1) {
            foreach(i, Type; PT) *(pFields[i]) = newFields.field[i];}*/
            {
//                writeln("calling Tuple!TT ", TT.stringof);
                static if (TT.length > 1)
                    this.opAssign(newFields.expand);
                else
                    this.opAssign(newFields.expand[0]);
            }

/*    void opAssign(TT...)(TT tup) if (TT.length == 1)
    {
        opAssign(tup[0]);
    }*/

    /*void opAssign(U)(Tuple!U newField) {
        opAssign(newField.field[0]);
    }*/


    void opAssign(U)(U newField) if (T.length ==1
                                     && !isInputRange!U && !is(U == class) && !is(U == struct)
                                     && !__traits(compiles, U.Types)  && !__traits(compiles, U.AllowedTypes)) {
//        writeln("Calling opAssign U");
        *(pFields[0]) = newField;
    }


    void opAssign(TT...)(TT tup) if (TT.length > 1 && TT.length >= T.length)
                                     /*&& ConvertibleTypeTuples!(TT[0..T.length], T)*/ {
//        writeln("Calling opAssign TT... > 1");
        foreach(i, Type; PT) *(pFields[i]) = tup[i];
    }
/+
    void opAssign(TT...)(TT tup) if (TT.length == 1 && T.length == 1
                                     && !isInputRange!TT && !is(TT == class) && !is(TT == struct)
                                     && !__traits(compiles, TT.Types)  && !__traits(compiles, TT.AllowedTypes)) {
        writeln("Calling opAssign TT... == 1");
        this.opAssign(tup.field[0]);
    }
+/
    void opAssign(C)(C theClass) if (is(C == class) && !isInputRange!C) {
        foreach(i, Type; PT) *(pFields[i]) = theClass.tupleof[i];
    }

    void opAssign(S)(S theStruct) if (is(S == struct) && !isInputRange!S && !__traits(compiles, S.Types) && !__traits(compiles, S.AllowedTypes)) {
//        writeln("Calling opAssign struct");
        foreach(i, Type; PT) *(pFields[i]) = theStruct.tupleof[i];
    }

    void opAssign(V)(V var) if (T.length == 1
                                && __traits(compiles, V.AllowedTypes)) {
//        writeln("Calling opAssign Variant");
        if (var.convertsTo!(T[0])) {
            *(pFields[0]) = var.get!T();
        }
        else {
            throw new Exception("Trying to assign from a bad Variant.");
        }
    }

    void opAssign(U, size_t n)(U[n] arr) if (n>=T.length) {
        foreach(i, Type; PT[0..$-1]) { *(pFields[i]) = arr[i];}
        static if (is(T[$-1] == U[]))
            *(pFields[PT.length-1]) = arr[PT.length-1..$].dup;
        else
            *(pFields[PT.length-1]) = arr.dup[PT.length-1];
    }

    void opAssign(R)(R range) if (isInputRange!R) {
        /*write("calling opAssign range on "); foreach(elem; range) write(elem, " "); writeln();
        writeln("range.empty is ", range.empty);
        assert(!range.empty);*/
        foreach(i, Type; PT[0..$-1]) { /*enforce(!range.empty);*/ *(pFields[i]) = range.front; range.popFront;}
        static if (is(T[$-1] == R))
            *(pFields[PT.length-1]) = range;
        else
            {
//                static assert(!range.empty);
                *(pFields[PT.length-1]) = range.front;
            }
    }

//    void opAssign(T...)(T t) { static assert(false, "Bad assignment.");}
}

AssignTuple!R _(R...)(ref R _fields) { return AssignTuple!R(_fields);}


