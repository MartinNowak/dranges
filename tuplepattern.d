/**
To Be Documented. It will become the tuple/variadic equivalent to $(M dranges.typepattern).
*/
module dranges.tuplepattern;

import std.typetuple;
import std.typecons;

import dranges.templates;

struct NoBacktrack {}

struct MatchResult(bool successOrFailure, Result, Post) if (isTuple!Result && isTuple!Post)
{
    enum bool hasMatched =  successOrFailure;
    Result.Types            result;
    Post.Types              post;
}

struct Failure(Post...)
{
    enum bool hasMatched =  false;
    TypeTuple!()            result;
    Post                    post;
}

Failure!(Post) failure(Post...)(Post post)
{
    Failure!Post f;
    static if (Post.length) f.post = post;
    return f;
}

struct Success(Result, Post) if (isTuple!Result && isTuple!Post)
{
    enum bool hasMatched =  true;
    Result.Types            result;
    Post.Types              post;
}

struct Success1(Result...)
{
    Result result;
    Success!(Tuple!Result, Tuple!Post) opCall(Post...)(Post post)
    {
        Success!(Tuple!Result, Tuple!Post) res;
        static if(Result.length) res.result = result;
        static if(Post.length) res.post = post;
        return res;
    }
}

Success1!(Result) success(Result...)(Result result)
{
    Success1!(Result) res;
    static if (Result.length) res.result = result;
    return res;
}

template isBacktracker(T)
{
    static if (__traits(hasMember, T, "Backtrack"))
        enum bool isBacktracker = true;
    else
        enum bool isBacktracker = false;
}

auto match(Pattern, Types...)(Types t)
{
    Pattern p;
    static if (is(typeof(p(t))))
        return p(t);
    else static if (Types.length > 0 && is(Pattern == Types[0])) // Pattern is a normal type
        return success(t[0])(t[1..$]);
    else
        return failure(t);
}

struct _
{
    auto opCall(T...)(T t)
    {
        static if (T.length > 0)
            return success(t[0])(t[1..$]);
        else
            return failure(t);
    }
}

struct End
{
    auto opCall(T...)(T t)
    {
        static if (T.length == 0)
        {
            pragma(msg, "true");
            return success(t[0..0])(t[0..0]);
        }
        else
            return failure(t);
    }
}

struct Or(Pattern1, Pattern2)
{
    bool canBacktrack;

    auto opCall(T...)(T t)
    {
        static if (match!(Pattern1)(t).hasMatched)
//        {
//            canBacktrack = true;
            return match!(Pattern1)(t);
//        }
        else static if (match!(Pattern2)(t).hasMatched)
//        {
//            canBacktrack = false;
            return match!(Pattern2)(t);
//        }
        else
            return failure(t);
    }

    template Backtrack(T...)
    {
//        pragma(msg, "backtracking Or, ", T.stringof);
        static if (match!(Pattern1)(Init!T).hasMatched)
            alias Pattern2 Backtrack;
        else
            alias NoBacktrack Backtrack;
    }
}

struct And(Pattern1, Pattern2)
{
    auto opCall(T...)(T t)
    {
        static if (match!(Pattern1)(t).hasMatched)
        {
            static if (match!(Pattern2)(match!(Pattern1)(t).post).hasMatched)
                return success(match!(Pattern1)(t).result, match!(Pattern2)(match!(Pattern1)(t).post).result)
                              (match!(Pattern2)(match!(Pattern1)(t).post).post);
            else static if (isBacktracker!Pattern1 && !is(Pattern1.Backtrack!(T) == NoBacktrack))
                 return match!(And!(Pattern1.Backtrack!(T), Pattern2))(t);
            else
                return failure(t);
        }
        else
            return failure(t);
    }

    template Backtrack(T...)
    {
        static if (isBacktracker!Pattern2 && !is(Pattern2.Backtrack!(T) == NoBacktrack))
            alias And!(Pattern1, Pattern2.Backtrack!(T)) Backtrack;
        else static if (isBacktracker!Pattern1 && !is(Pattern1.Backtrack!(T) == NoBacktrack))
            alias And!(Pattern1.Backtrack!(T), Pattern2) Backtrack;
        else
            alias NoBacktrack Backtrack;
    }
}


template Successively(Patterns...) if(Patterns.length > 0)
{
    static if (Patterns.length > 1)
        alias And!(Patterns[0], Successively!(Patterns[1..$])) Successively;
    else
        alias Patterns[0] Successively;
}


template Either(Patterns...) if(Patterns.length > 0)
{
    static if (Patterns.length > 1)
        alias Or!(Patterns[0], Either!(Patterns[1..$])) Either;
    else
        alias Patterns[0] Either;
}

private template TypeNuple(T, int n)
{
    static if (n > 0)
        alias TypeTuple!(T, TypeNuple!(T, n-1)) TypeNuple;
    else
        alias TypeTuple!() TypeNuple;
}

///**
//Greedily matches Pattern at least min times up to (included) max times. If forced to backtrack, it will try one match less.
//*/
//template Repeat(Pattern, int min, int max) if (min >= 0 && max >= 0 && min <= max)
//{
//    static if (min > 0)
//        alias Successively!(TypeNuple!(Pattern, min), RepeatImpl!(Pattern, max-min)) Repeat;
//    else
//        alias RepeatImpl!(Pattern, max) Repeat;
//}
//
//template Repeat(Pattern, int max) if (max >= 0)
//{
//    alias Repeat!(Pattern, 0, max) Repeat;
//}
//
//struct RepeatImpl(Pattern, int max) //if (max >= 0)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (.Match!(Pattern, T).hasMatched)
////        {
//            static if (max > 0)
//                alias And!(Pattern, RepeatImpl!(Pattern, max-1)).Match!(T) Match;
//            else
//                alias Success!().Next!(T) Match;
////        }
//        else
//            alias Success!().Next!(T) Match;
//    }
//
//    template Backtrack()
//    {
//        static if (max > 0)
//            alias RepeatImpl!(Pattern, max-1) Backtrack;
//        else
//            alias NoBacktrack Backtrack;
//    }
//}
//
///**
//Repeat Pattern min times. If forced to backtrack, it will try one more match, up to max.
//*/
//template LazyRepeat(Pattern, int min, int max) if (min <= max)
//{
//    static if (min > 0)
//        alias Successively!(TypeNuple!(Pattern, min), .LazyRepeat!(Pattern, max-min)) LazyRepeat;
//    else
//        alias .LazyRepeat!(Pattern, max) LazyRepeat;
//}
//
//struct LazyRepeat(Pattern, int max)
//{
//    auto opCall(T...)(T t)
//    {
//        alias TypeTuple!() Match;
//    }
//
//    template Backtrack()
//    {
//        static if (max > 0)
//            alias And!(Pattern, LazyRepeat!(Pattern, max-1)) Backtrack;
//        else
//            alias NoBacktrack Backtrack;
//    }
//}
//
///// Tests for 0 or more Pattern. I stopped at 128 max due to template instantiation limits.
//template ZeroOrMore(Pattern)
//{
//    alias Repeat!(Pattern, 128) ZeroOrMore;
//}
//
///// Tests for 1 or more Pattern. I stopped at 128 max due to template instantiation limits.
//template OneOrMore(Pattern)
//{
//    alias Repeat!(Pattern, 1, 128) OneOrMore;
//}
//
///// 0 or 1 Pattern
//template Option(Pattern)
//{
//    alias Repeat!(Pattern, 0, 1) Option;
//}
//
///// Invert the pattern.
//struct Not(Pattern)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (.Match!(Pattern, T).hasMatched)
//            alias Failure!(T) Match;
//        else
//            alias .Match!(_, T) Match; // What should it do?
//    }
//}
//
///// Matches only iff none of the Patterns match.
//template None(Patterns...)
//{
//    alias Not!(Either!Patterns) None;
//}
//
//
//private template isInstanceOf(alias templ, T)
//{
//    static if (T.stringof.length >= __traits(identifier, templ).length
//            && T.stringof[0..__traits(identifier, templ).length] == __traits(identifier, templ))
//        enum bool isInstanceOf = true;
//    else
//        enum bool isInstanceOf = false;
//}
//
//private string[3] between(char b, char e, string s)()
//{
//    int foundb;
//    int ib;
//    string notFound = "";
//    foreach(i,c; s)
//    {
//        if (c==b)
//        {
//            if (foundb == 0)
//            {
//                foundb = 1;
//                ib = i+1;
//                continue;
//            }
//            else
//            {
//                ++foundb;
//            }
//        }
//        if (c==e)
//        {
//            if (foundb == 1)
//            {
//                return [s[0..ib-1], s[ib..i], s[i+1..$]];
//            }
//            else
//            {
//                --foundb;
//            }
//        }
//    }
//    return [s, notFound,notFound];
//}
//
//private template TemplateParametersTypeTuple(T)
//{
//    mixin("alias TypeTuple!(" ~ between!('(',')',T.stringof)[1] ~ ") TemplateParametersTypeTuple;");
//}
//
///**
//isA is a very powerful pattern: it matches if the input type is an instance of templ (a templated type) with the inner types matching Patterns:
//----
//alias isA!(Tuple, _, _) Tuple2; // matches any Tuple!(_,_): a Tuple with two types
//alias isA!(Tuple, OneOrMore!_) Tuple1; // matches any Tuple with one or more type inside.
//                                       // So, it matchesTuple!(int, string, double) but not Tuple!()
//alias isA!(Tuple, int, ZeroOrMore!_) Tuple3; // matches Tuple!(int, double) or Tuple!(int, double, string) or even Tuple!(int)
//----
//*/
//struct isA(alias templ, Patterns...)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (   T.length > 0
//                   && isInstanceOf!(templ, T[0])  // is T[0] a templ?
//                   && .Match!(Successively!Patterns, TemplateParametersTypeTuple!(T[0])).hasMatched // is T[0] type params the good ones?
//                   && .Match!(Successively!Patterns, TemplateParametersTypeTuple!(T[0])).Post.length == 0 // is there nothing left to consume?
//                  )
//            alias Success!(T[0]).Next!(T[1..$]) Match;
//        else
//            alias Failure!(T) Match;
//    }
//}
//
///**
//Inside is like isA, but the match result is the inner types, *not* the global type:
//----
//alias isA!(Tuple, _, _)    Tuple2;  // matches Tuple!(int, string), produces Tuple!(int, string)
//alias Inside!(Tuple, _, _) Inside2; // matches Tuple!(int, string), but produces (int, string)
//----
//*/
//struct Inside(alias templ, Patterns...)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (   T.length > 0
//                   && isInstanceOf!(templ, T[0])  // is T[0] a templ?
//                   && .Match!(Successively!Patterns, TemplateParametersTypeTuple!(T[0])).hasMatched // are T[0]'s type params the good ones?
//                   && .Match!(Successively!Patterns, TemplateParametersTypeTuple!(T[0])).Post.length == 0 // is there nothing left to consume?
//                  )
//            alias Success!(.Match!(Successively!Patterns, TemplateParametersTypeTuple!(T[0])).Result).Next!(T[1..$]) Match;
//        else
//            alias Failure!(T) Match;
//    }
//}
//
///**
//Matches if T[0] verifies the condition (ie if condition!(T[0]) is statically true)
//----
//alias If!(isIntegral) Integer; // will match int, byte, short, long, etc.
//----
//*/
//struct If(alias condition)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (T.length && condition!(T[0]))
//            alias Success!(T[0]).Next!(T[1..$]) Match;
//        else
//            alias Failure!(T) Match;
//    }
//}
//
//
///**
//An extended version of the previous If. If T[0] verifies the condition (ie if condition!(T[0]) is statically true),
//it'll use the Then pattern on T. Else, it'll use the Else pattern.
//*/
//struct If(alias condition, Then, Else)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (T.length && condition!(T[0]))
//            alias .Match!(Then, T) Match;
//        else
//            alias .Match!(Else, T) Match;
//    }
//}
//
///**
//Variation on the same theme: Then is here a template that will be applied on the If match result.
//That is, if condition!(T[0]), returns Then!(T[0]), else return Else.
//*/
//struct If(alias condition, alias Then, Else)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (T.length && condition!(T[0]))
//            alias Success!(Then!(T[0])).Next!(T[1..$]) Match;
//        else
//            alias .Match!(Else, T) Match;
//    }
//}
//
///**
//The same, with Else being an alias.
//*/
//struct If(alias condition, Then, alias Else)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (T.length && condition!(T[0]))
//            alias .Match!(Then, T) Match;
//        else
//            alias Success!(Else!(T[0])).Next!(T[1..$]) Match;
//    }
//}
//
///**
//The same, with Then and Else being aliases.
//*/
//struct If(alias condition, alias Then, alias Else)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (T.length && condition!(T[0]))
//            alias Success!(Then!(T[0])).Next!(T[1..$]) Match;
//        else
//            alias Success!(Else!(T[0])).Next!(T[1..$]) Match;
//    }
//}
//
///**
//Transforms a pattern such that, if it matches, it puts back its match in the input tuple, for the next pattern
//to consume.
//See_Also: LookAhead.
//*/
//struct ReleaseMatch(Pattern)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (.Match!(Pattern, T).hasMatched)
//            alias Success!().Next!(.Match!(Pattern, T).Result, .Match!(Pattern, T).Post) Match;
//        else
//            alias Failure!(T) Match;
//    }
//}
//
///**
//Transforms a pattern such that, if it matches, it discards its match: the match result is the empty typetuple.
//See_Also: Left, Right, LeftMost, RightMost.
//*/
//struct DiscardMatch(Pattern)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (.Match!(Pattern, T).hasMatched)
//            alias Success!().Next!(.Match!(Pattern, T).Post) Match;
//        else
//            alias Failure!(T) Match;
//    }
//}
//
///**
//Matches iff Pattern1 and then Pattern2 match, but returns only Pattern1's match result.
//*/
//template Left(Pattern1, Pattern2)
//{
//    alias And!(Pattern1, DiscardMatch!Pattern2) Left;
//}
//
///**
//Matches iff Pattern1 and then Pattern2 match, but returns only Pattern2's match result.
//*/
//template Right(Pattern1, Pattern2)
//{
//    alias And!(DiscardMatch!Pattern1, Pattern2) Right;
//}
//
///**
//Matches iff all Patterns match, but returns only the first (leftmost) pattern match result.
//*/
//template LeftMost(Patterns...)
//{
//    alias Successively!(Patterns[0], staticMap!(DiscardMatch, Patterns[1..$])) LeftMost;
//}
//
///**
//Matches iff all Patterns match, but returns only the last (rightmost) pattern match result.
//*/
//template RightMost(Patterns...)
//{
//    alias Successively!(staticMap!(DiscardMatch, Patterns[0..$-1]), Patterns[$-1]) RightMost;
//}
//
///**
//Matches iff all Patterns match, returns the leftmost pattern match result, without consuming the rest.
//*/
//template LookAhead(Patterns...)
//{
//    alias Successively!(Patterns[0], staticMap!(ReleaseMatch, Patterns[1..$])) LookAhead;
//}
//
///**
//Tests the first pattern. If it matches, it releases its match and then tests the second pattern in the same manner. All
//patterns will be tested in this way, getting them to match on the same input (more or less). Only if all of them match
//simultaneously will Simultaneously returns a match: the last pattern's match. Not to be confused with And or Successively
//that test for matches while consuming the first patterns matches.
//----
//alias Simultaneously!(And!(_,_), int) S; // S matches if there are two types in a row and the first one is an int. Returns 'int'.
//----
//Note: I'm not sure this is interesting in any way as there is frequently a way to express the same pattern in another way.
//I'm just playing along with ReleaseMatch, really.
//*/
//template Simultaneously(Patterns...)
//{
//    alias Successively!(staticMap!(ReleaseMatch, Patterns[0..$-1]), Patterns[$-1]) Simultaneously;
//}
//
///**
//Transforms a pattern so that it'll consume input until it finds a match. Only if it never matches does it return NoMatch.
//*/
//struct UnAnchored(Pattern)
//{
//    auto opCall(T...)(T t)
//    {
//        static if (.Match!(Pattern,T).hasMatched)
//            alias .Match!(Pattern, T) Match;
//        else static if (T.length)
//            alias UnAnchored!(Pattern).Match!(T[1..$]) Match;
//        else
//            alias Failure!(T) Match;
//    }
//}
//
///**
//Returns a tuple of all matches of a pattern in an input tuple. Tp distinguish them from one another, the matches are wrapped in Tuples.
//Usage:
//----
//alias AllMatches!(Pattern).In!(InputTuple) AM;
//----
//
//Example:
//----
//alias AllMatches!(And!(_,int)).In!(int,double,int,string,int*,int,int) Ints; // finds all couples where a type is followed by an int.
//assert(is(AM == TypeTuple!(
//                           Tuple!(double,int),
//                           Tuple!(int*,int),
//                           Tuple!(int,int)
//                          )));
//----
//*/
//template AllMatches(Pattern)
//{
//    template In(T...)
//    {
//        static if (Match!(Pattern, T).hasMatched)
//            alias TypeTuple!(
//                             Tuple!(Match!(Pattern, T).Result),
//    //                         AllMatches!(Pattern, Match!(Pattern, T).Post) // ?
//                             AllMatches!(Pattern).In!(T[1..$])
//                            ) In;
//        else static if (T.length)
//            alias AllMatches!(Pattern).In!(T[1..$]) In;
//        else
//            alias TypeTuple!() In;
//    }
//}
//
///**
//Replaces the first instance of Pattern with WithThis in an input typetuple.
//Example:
//----
//alias Replace!(And!(_,int), float).In!(double,int, string,string,int) Rep;
//assert(is( Rep == TypeTuple!(float, string, string, int)));
//----
//*/
//template Replace(Pattern, WithThis)
//{
//    template In(T...)
//    {
//        static if (Match!(Pattern, T).hasMatched)
//            alias TypeTuple!(
//                             WithThis,
//                             Match!(Pattern, T).Post
//                            ) In;
//        else static if (T.length)
//            alias TypeTuple!(
//                             T[0],
//                             Replace!(Pattern, WithThis).In!(T[1..$])
//                            ) In;
//        else
//            alias TypeTuple!() In;
//    }
//}
//
///**
//Replaces every instance of Pattern with WithThis in an input typetuple.
//Example:
//----
//alias ReplaceAll!(And!(_,int), float).In!(double,int, string,string,int) Rep;
//assert(is( Rep == TypeTuple!(float, string, float)));
//----
//*/
//template ReplaceAll(Pattern, WithThis)
//{
//    template In(T...)
//    {
//        static if (Match!(Pattern, T).hasMatched)
//            alias TypeTuple!(
//                             WithThis,
//                             ReplaceAll!(Pattern, WithThis).In!(Match!(Pattern, T).Post)
//                            ) In;
//        else static if (T.length)
//            alias TypeTuple!(
//                             T[0],
//                             ReplaceAll!(Pattern, WithThis).In!(T[1..$])
//                            ) In;
//        else
//            alias TypeTuple!() In;
//    }
//}
//
///**
//A cousin of Replace: finds the first match of Pattern in an input typetuple and replaces it with WithThis!(Match).
//Example:
//----
//alias Transform!(If!(isIntegral), Unsigned).In!(int,double,float,byte,ulong,string) T; // transforms the first integral type with its unsigned equivalent
//assert(is( T == TypeTuple!(uint,double,float,byte,ulong,string)));
//----
//*/
//template Transform(Pattern, alias WithThis)
//{
//    template In(T...)
//    {
//        static if (Match!(Pattern, T).hasMatched)
//            alias TypeTuple!(
//                             WithThis!(Match!(Pattern, T).Result),
//                             Match!(Pattern, T).Post
//                            ) In;
//        else static if (T.length)
//            alias TypeTuple!(
//                             T[0],
//                             Transform!(Pattern, WithThis).In!(T[1..$])
//                            ) In;
//        else
//            alias TypeTuple!() In;
//    }
//}
//
///**
//A cousin of ReplaceAll: finds all successive matches of Pattern in an input typetuple and replaces them with WithThis!(Match).
//Example:
//----
//alias TransformAll!(If!(isIntegral), Unsigned).In!(int,double,float,byte,ulong,string) T; // transforms all integral types with their unsigned equivalent
//assert(is( T == TypeTuple!(uint,double,float,ubyte,ulong,string)));
//----
//*/
//template TransformAll(Pattern, alias WithThis)
//{
//    template In(T...)
//    {
//        static if (Match!(Pattern, T).hasMatched)
//            alias TypeTuple!(
//                             WithThis!(Match!(Pattern, T).Result),
//                             TransformAll!(Pattern, WithThis).In!(Match!(Pattern, T).Post)
//                            ) In;
//        else static if (T.length)
//            alias TypeTuple!(
//                             T[0],
//                             TransformAll!(Pattern, WithThis).In!(T[1..$])
//                            ) In;
//        else
//            alias TypeTuple!() In;
//    }
//}
//
//template match(Pattern, alias action, Rest...)
//{
//    auto match(T...)(T t)
//    {
//        static if (Match!(Pattern, T).hasMatched)
//        {
//            Match!(Pattern, T).Result extract;
//            foreach(i, Type; Match!(Pattern, T).Result)
//            {
//                extract[i] = t[i];
//            }
//            return action(extract);
//        }
//        else static if (Rest.length)
//        {
//            alias .match!(Rest) matchTheRest;
//            return matchTheRest(t);
//        }
//        else
//        {
//            static assert(false, "Cannot match input of type " ~ T.stringof);
//        }
//    }
//}

