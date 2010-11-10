/**
This module implements a basic pattern matching engine for type tuples. Think regexes, but for types:
"one or more int, followed by a string or a double, and then anything but a float".

Pattern expressions are built by aliasing the basic building blocks provided here and tested with the Match!(Pattern, Tuple...)
template. A match result is a struct exposing three fields:

$(UL
  $(LI hasMatched: a boolean that tells us whether or not the typetuple matched the pattern)
  $(LI Result: a typetuple holding the match result. If hasMatched is false, it will be empty.)
  $(LI Post: the rest of the input typetuple, the part that was not consumed by the pattern.)
)

Usage:
----
// Let's define some basic patterns first:
alias OneOrMore!(int) Ints;
alias Either!(int, double) IOrD;
alias _ Any; // Predefined '_' pattern, matching any type.
alias And!(_,_) Two; // Match any two types in succession. Will fail if passed 0 or 1 type.

// A more complicated example:
alias Successively!(
                    int,
                    None!(int,double,string),
                    _,
                    Repeat!(int, 2, 4),
                    Not!int,
                    End) Pattern;

// To match, use Match!(Pattern, TypeTuple):
alias Match!(Ints, int, int, int, double)    Res1;
alias Match!(IOrD, double, int, int, double) Res2;
alias Match!(Any,  double, int, int, double) Res3;
alias Match!(Two,  double, int, int, double) Res4;
alias Match!(Pattern, int, float, string, int,int,int, string) Res5;

// All is done at compile-time, of course.
pragma(msg, Res1.Result.stringof, " // ", Res1.Post.stringof);
pragma(msg, Res2.Result.stringof, " // ", Res2.Post.stringof);
pragma(msg, Res3.Result.stringof, " // ", Res3.Post.stringof);
pragma(msg, Res4.Result.stringof, " // ", Res4.Post.stringof);
pragma(msg, Res5.Result.stringof, " // ", Res5.Post.stringof);
----

Features:
$(UL
  $(LI Any type is its own pattern. 'int' matches an int and so on.)
  $(LI Patterns can be tested in succession (And) or in alternation (Or). Predefined compositions like Successively and Either are there to help you.).
  $(LI You can Repeat patterns min times, up to max times. There are predefined ZeroOrMore, OneOrMore, Option (aka ZeroOrOne) for your convenience.)
  $(LI Patterns can (and will) backtrack to find a match.)
  $(LI All patterns are tested only from the beginning of the tuple. In regex terms, it's as if they all begin with '^'. Use UnAnchored!Pattern to
    make a pattern consume input until it finds something.)
  $(LI You can easily extend the module by defining your own patterns: just define a Match(T...) template inside a struct that alias itself to a correct
    match result.)
)

TODO:
$(UL
  $(LI Maybe extend that to all template parameters, and not only types.)
  $(LI No capture is implemented yet. That would mean passing an entire state around, to remember previous captures to give them to
    a BackReference!(ref number) template. It's doable, but a bit to much for me right now.)
  $(LI No named captures either...)
)
*/
module dranges.typepattern;
import std.typetuple;
import std.typecons;

import dranges.templates,
       dranges.typetuple;

struct NoBacktrack {}

template MatchResult(bool successOrFailure, Types...)
{
    struct Next(Rest...)
    {
        enum bool hasMatched =  successOrFailure;
        alias TypeTuple!(Types) Result;
        alias TypeTuple!(Rest)  Post;
    }
}

template Failure(Rest...)
{
    enum bool hasMatched =  false;
    alias TypeTuple!()      Result;
    alias TypeTuple!(Rest)  Post;
}

template Success(Types...)
{
    struct Next(Rest...)
    {
        enum bool hasMatched =  true;
        alias TypeTuple!(Types) Result;
        alias TypeTuple!(Rest)  Post;
    }
}

template isMatchResult(T)
{
    static if (T.hasMatched && is(T.Result) && is(T.Post))
        enum bool isMatchResult = true;
    else
        enum bool isMatchResult = false;
}

/// The match engine, driving the entire pattern evaluation.
template Match(Pattern, Types...)
{
    static if (is(Pattern.Match!Types))// && isMatchResult!(Pattern.Match!Types))
        alias Pattern.Match!Types Match;
    else static if (Types.length > 0 && is(Pattern == Types[0])) // Pattern is a normal type
        alias Success!(Types[0]).Next!(Types[1..$]) Match;
    else
        alias Failure!(Types) Match;
}

template Match(alias Pattern, Types...)
{
//    pragma(msg, "Testing ", Pattern.stringof, " with ", Types.stringof);
    static if (is(Pattern.Match!Types))// && isMatchResult!(Pattern.Match!Types))
        alias Pattern.Match!Types Match;
    else
        alias Failure!(Types) Match;
}

/**
Returns a tuple of all matches of a pattern in an input tuple. To distinguish them from one another, the matches are wrapped in Tuples.
Usage:
----
alias AllMatches!(Pattern).In!(InputTuple) AM;
----

Example:
----
alias AllMatches!(And!(_,int)).In!( int,double,int,string,int*,int,int ) Ints; // finds all couples where a type is followed by an int.
assert(is(AM == TypeTuple!(
                           Tuple!(double,int),
                           Tuple!(int*,int),
                           Tuple!(int,int)
                          )));
----
*/
template AllMatches(Pattern)
{
    template In(T...)
    {
        static if (Match!(Pattern, T).hasMatched)
            alias TypeTuple!(
                             Tuple!(Match!(Pattern, T).Result),
    //                         AllMatches!(Pattern, Match!(Pattern, T).Post) // ?
                             AllMatches!(Pattern).In!(T[1..$])
                            ) In;
        else static if (T.length)
            alias AllMatches!(Pattern).In!(T[1..$]) In;
        else
            alias TypeTuple!() In;
    }
}

/**
Replaces the first instance of $(M Pattern) with (M WithThis) in an input typetuple.
Example:
----
alias Replace!(And!(_,int), float).In!(double,int, string,string,int) Rep;
assert(is( Rep == TypeTuple!(float, string, string, int)));
----
*/
template Replace(Pattern, WithThis)
{
    template In(T...)
    {
        static if (Match!(Pattern, T).hasMatched)
            alias TypeTuple!(
                             WithThis,
                             Match!(Pattern, T).Post
                            ) In;
        else static if (T.length)
            alias TypeTuple!(
                             T[0],
                             Replace!(Pattern, WithThis).In!(T[1..$])
                            ) In;
        else
            alias TypeTuple!() In;
    }
}

/**
Replaces every instance of (M Pattern) with (M WithThis) in an input typetuple.
Example:
----
alias ReplaceAll!(And!(_,int), float).In!(double,int, string,string,int) Rep;
assert(is( Rep == TypeTuple!(float, string, float)));
----
*/
template ReplaceAll(Pattern, WithThis)
{
    template In(T...)
    {
        static if (Match!(Pattern, T).hasMatched)
            alias TypeTuple!(
                             WithThis,
                             ReplaceAll!(Pattern, WithThis).In!(Match!(Pattern, T).Post)
                            ) In;
        else static if (T.length)
            alias TypeTuple!(
                             T[0],
                             ReplaceAll!(Pattern, WithThis).In!(T[1..$])
                            ) In;
        else
            alias TypeTuple!() In;
    }
}

/**
A cousin of (M Replace): finds the first match of (M Pattern) in an input typetuple and replaces it with (M WithThis!(Match)).
Example:
----
alias Transform!(If!(isIntegral), Unsigned).In!( int,double,float,byte,ulong,string ) T; // transforms the first integral type with its unsigned equivalent
assert(is( T == TypeTuple!(uint,double,float,byte,ulong,string)));
----
*/
template Transform(Pattern, alias WithThis)
{
    template In(T...)
    {
        static if (Match!(Pattern, T).hasMatched)
            alias TypeTuple!(
                             WithThis!(Match!(Pattern, T).Result),
                             Match!(Pattern, T).Post
                            ) In;
        else static if (T.length)
            alias TypeTuple!(
                             T[0],
                             Transform!(Pattern, WithThis).In!(T[1..$])
                            ) In;
        else
            alias TypeTuple!() In;
    }
}

/**
A cousin of (M ReplaceAll): finds all successive matches of (M Pattern) in an input typetuple and replaces them with (M WithThis!(Match)).
Example:
----
alias TransformAll!(If!(isIntegral), Unsigned).In!( int,double,float,byte,ulong,string ) T; // transforms all integral types with their unsigned equivalent
assert(is( T == TypeTuple!(uint,double,float,ubyte,ulong,string)));
----
*/
template TransformAll(Pattern, alias WithThis)
{
    template In(T...)
    {
        static if (Match!(Pattern, T).hasMatched)
            alias TypeTuple!(
                             WithThis!(Match!(Pattern, T).Result),
                             TransformAll!(Pattern, WithThis).In!(Match!(Pattern, T).Post)
                            ) In;
        else static if (T.length)
            alias TypeTuple!(
                             T[0],
                             TransformAll!(Pattern, WithThis).In!(T[1..$])
                            ) In;
        else
            alias TypeTuple!() In;
    }
}

/**
Another take on pattern-matching. It takes couples of a pattern and a function (maybe a templated function)
as template parameters. When given a value as input, it will test the value type against all patterns
in succession. When a pattern matches, it will return the associated function's return.
Example:
----
alias match!(
             OneOrMore!int,     fun1,
             And!(double, int), fun2,
             _,                 fun3,
             ) matcher;
----

See_Also: $(M dranges.patternmatch), $(M dranges.functional.eitherFun).
*/
template match(Pattern, alias action, Rest...)
{
    auto match(T...)(T t)
    {
        static if (Match!(Pattern, T).hasMatched)
        {
            Match!(Pattern, T).Result extract;
            foreach(i, Type; Match!(Pattern, T).Result)
            {
                extract[i] = t[i];
            }
            return action(extract);
        }
        else static if (Rest.length)
        {
            alias .match!(Rest) matchTheRest;
            return matchTheRest(t);
        }
        else
        {
            static assert(false, "Cannot match input of type " ~ T.stringof);
        }
    }
}

/// Matches any type. Think '.' for regexes. Does not match the empty typetuple.
struct _
{
    template Match(T...)
    {
        static if (T.length > 0)
            alias Success!(T[0]).Next!(T[1..$]) Match;
        else
            alias Failure!(T) Match;
    }
}

/// Matches the end of a tuple (aka, the empty typetuple). Think '$' for regexes.
struct End
{
    template Match(T...)
    {
        static if (T.length == 0)
            alias Success!().Next!(T) Match;
        else
            alias Failure!(T) Match;
    }
}

/**
It matches if $(M Pattern1) or $(M Pattern2) matches. More precisely, it tests $(M Pattern1).
If it matches, $(M Or) returns the match result.
If it fails, $(M Or) will try the second pattern and return its match result (which may be a failure).
If it tested only the first pattern, it can backtrack when asked to, by testing the second pattern.
*/
struct Or(Pattern1, Pattern2)
{
    template Match(T...)
    {
        static if (.Match!(Pattern1, T).hasMatched)
            alias .Match!(Pattern1, T) Match;
        else static if (.Match!(Pattern2, T).hasMatched)
            alias .Match!(Pattern2, T) Match;
        else
            alias Failure!(T) Match;
    }

    template Backtrack()
    {
        static if (.Match!(Pattern1, T).hasMatched)
            alias Pattern2 Backtrack;
        else
            alias NoBacktrack Backtrack;
    }
}

/**
Will match if and only if $(M Pattern1) matches and $(M Pattern2) matches after $(M Pattern1).
It's the basic building block for all type patterns, since it threads them in succession.
When you need to test P1 and then P2 and then P3, it's $(M And) you need.
If the second pattern fails, it will ask the first pattern to backtrack (if possible) and test the second pattern again.

See_Also: $(M Successively).
*/
struct And(Pattern1, Pattern2)
{
    template Match(T...)
    {
        static if (.Match!(Pattern1, T).hasMatched)
        {
            static if (.Match!(Pattern2, .Match!(Pattern1, T).Post).hasMatched)
                alias Success!(.Match!(Pattern1, T).Result, .Match!(Pattern2, .Match!(Pattern1, T).Post).Result).Next!(.Match!(Pattern2, .Match!(Pattern1, T).Post).Post) Match;
            else static if (is(Pattern1.Backtrack!()) && !is(Pattern1.Backtrack!() == NoBacktrack))
                alias And!(Pattern1.Backtrack!(), Pattern2).Match!(T) Match;
            else
                alias Failure!(T) Match;
        }
        else
            alias Failure!(T) Match;
    }

    template Backtrack()
    {
        static if (is(Pattern2.Backtrack!()) && !is(Pattern2.Backtrack!() == NoBacktrack))
            alias And!(Pattern1, Pattern2.Backtrack!()) Backtrack;
        else static if (is(Pattern1.Backtrack!()) && !is(Pattern1.Backtrack!() == NoBacktrack))
            alias And!(Pattern1.Backtrack!(), Pattern2) Backtrack;
        else
            alias NoBacktrack Backtrack;
    }
}

/**
Convenience template, equivalent to $(M And!(P1, And!(P2, And!(P3, ...)))). It will try to match all the Pi:
if one fails, the entire template fails. It's composed of $(M And)s, so it will backtrack internally
as much as necessary to match all patterns.
*/
template Successively(Patterns...) if(Patterns.length > 0)
{
    static if (Patterns.length > 1)
        alias And!(Patterns[0], Successively!(Patterns[1..$])) Successively;
    else
        alias Patterns[0] Successively;
}

/**
Convenience template, equivalent to $(M Or!(P1, Or!(P2, Or!(...)))). It will try $(M P1), and stop there if it matches.
Else, it will test $(M P2) and so on. If forced to backtrack, it will continue with the yet untested patterns.
*/
template Either(Patterns...) if(Patterns.length > 0)
{
    static if (Patterns.length > 1)
        alias Or!(Patterns[0], Either!(Patterns[1..$])) Either;
    else
        alias Patterns[0] Either;
}


/**
Greedily matches $(M Pattern) at least $(M min) times up to (included) $(M max) times. If forced to backtrack, it will try one match less.
*/
template Repeat(Pattern, int min, int max) if (min >= 0 && max >= 0 && min <= max)
{
    static if (min > 0)
        alias Successively!(TypeNuple!(Pattern, min), RepeatImpl!(Pattern, max-min)) Repeat;
    else
        alias RepeatImpl!(Pattern, max) Repeat;
}

template Repeat(Pattern, int max) if (max >= 0)
{
    alias Repeat!(Pattern, 0, max) Repeat;
}

struct RepeatImpl(Pattern, int max) //if (max >= 0)
{
    template Match(T...)
    {
        static if (.Match!(Pattern, T).hasMatched)
//        {
            static if (max > 0)
                alias And!(Pattern, RepeatImpl!(Pattern, max-1)).Match!(T) Match;
            else
                alias Success!().Next!(T) Match;
//        }
        else
            alias Success!().Next!(T) Match;
    }

    template Backtrack()
    {
        static if (max > 0)
            alias RepeatImpl!(Pattern, max-1) Backtrack;
        else
            alias NoBacktrack Backtrack;
    }
}

/**
Repeat $(M Pattern min) times. If forced to backtrack, it will try one more match, up to $(M max).
*/
template LazyRepeat(Pattern, int min, int max) if (min <= max)
{
    static if (min > 0)
        alias Successively!(TypeNuple!(Pattern, min), .LazyRepeat!(Pattern, max-min)) LazyRepeat;
    else
        alias .LazyRepeat!(Pattern, max) LazyRepeat;
}

struct LazyRepeat(Pattern, int max)
{
    template Match(T...)
    {
        alias TypeTuple!() Match;
    }

    template Backtrack()
    {
        static if (max > 0)
            alias And!(Pattern, LazyRepeat!(Pattern, max-1)) Backtrack;
        else
            alias NoBacktrack Backtrack;
    }
}

/// Tests for 0 or more $(M Pattern). I stopped at 128 max due to template instantiation limits.
template ZeroOrMore(Pattern)
{
    alias Repeat!(Pattern, 128) ZeroOrMore;
}

/// Tests for 1 or more $(M Pattern). I stopped at 128 max due to template instantiation limits.
template OneOrMore(Pattern)
{
    alias Repeat!(Pattern, 1, 128) OneOrMore;
}

/// 0 or 1 $(M Pattern)
template Option(Pattern)
{
    alias Repeat!(Pattern, 0, 1) Option;
}

/// Invert the pattern.
struct Not(Pattern)
{
    template Match(T...)
    {
        static if (.Match!(Pattern, T).hasMatched)
            alias Failure!(T) Match;
        else
            alias .Match!(_, T) Match; // What should it do?
    }
}

/// Matches only iff none of the $(M Patterns) match.
template None(Patterns...)
{
    alias Not!(Either!Patterns) None;
}

/**
$(M isA) is a very powerful pattern: it matches if the input type is an instance of $(M templ) (a templated type) with the inner types matching $(M Patterns):
----
alias isA!(Tuple, _, _) Tuple2; // matches any Tuple!(_,_): a Tuple with two types
alias isA!(Tuple, OneOrMore!_) Tuple1; // matches any Tuple with one or more type inside.
                                       // So, it matchesTuple!(int, string, double) but not Tuple!()
alias isA!(Tuple, int, ZeroOrMore!_) Tuple3; // matches Tuple!(int, double) or Tuple!(int, double, string) or even Tuple!(int)
----
*/
struct isA(alias templ, Patterns...)
{
    template Match(T...)
    {
        static if (   T.length > 0
                   && isInstanceOf!(templ, T[0])  // is T[0] a templ?
                   && .Match!(Successively!Patterns, TemplateParametersTypeTuple!(T[0])).hasMatched // is T[0] type params the good ones?
                   && .Match!(Successively!Patterns, TemplateParametersTypeTuple!(T[0])).Post.length == 0 // is there nothing left to consume?
                  )
            alias Success!(T[0]).Next!(T[1..$]) Match;
        else
            alias Failure!(T) Match;
    }
}

/**
$(M Inside) is like $(M isA), but the match result is the inner types, *not* the global type:
----
alias isA!(Tuple, _, _)    Tuple2;  // matches Tuple!(int, string), produces Tuple!(int, string)
alias Inside!(Tuple, _, _) Inside2; // matches Tuple!(int, string), but produces (int, string)
----
*/
struct Inside(alias templ, Patterns...)
{
    template Match(T...)
    {
        static if (   T.length > 0
                   && isInstanceOf!(templ, T[0])  // is T[0] a templ?
                   && .Match!(Successively!Patterns, TemplateParametersTypeTuple!(T[0])).hasMatched // are T[0]'s type params the good ones?
                   && .Match!(Successively!Patterns, TemplateParametersTypeTuple!(T[0])).Post.length == 0 // is there nothing left to consume?
                  )
            alias Success!(.Match!(Successively!Patterns, TemplateParametersTypeTuple!(T[0])).Result).Next!(T[1..$]) Match;
        else
            alias Failure!(T) Match;
    }
}

/**
Matches if $(M T[0]) verifies the condition (ie if $(M condition!(T[0])) is statically true)
----
alias If!(isIntegral) Integer; // will match int, byte, short, long, etc.
----
*/
struct If(alias condition)
{
    template Match(T...)
    {
        static if (T.length && condition!(T[0]))
            alias Success!(T[0]).Next!(T[1..$]) Match;
        else
            alias Failure!(T) Match;
    }
}


/**
An extended version of the previous $(M If). If $(M T[0]) verifies the condition (ie if $(M condition!(T[0])) is statically true),
it'll use the $(M Then) pattern on $(M T). Else, it'll use the $(M Else) pattern.
*/
struct If(alias condition, Then, Else)
{
    template Match(T...)
    {
        static if (T.length && condition!(T[0]))
            alias .Match!(Then, T) Match;
        else
            alias .Match!(Else, T) Match;
    }
}

/**
Variation on the same theme: $(M Then) is here a template that will be applied on the $(M If) match result.
That is, if $(M condition!(T[0])), returns $(M Then!(T[0])), else return $(M Else).
*/
struct If(alias condition, alias Then, Else)
{
    template Match(T...)
    {
        static if (T.length && condition!(T[0]))
            alias Success!(Then!(T[0])).Next!(T[1..$]) Match;
        else
            alias .Match!(Else, T) Match;
    }
}

/**
The same, with $(M Else) being an alias.
*/
struct If(alias condition, Then, alias Else)
{
    template Match(T...)
    {
        static if (T.length && condition!(T[0]))
            alias .Match!(Then, T) Match;
        else
            alias Success!(Else!(T[0])).Next!(T[1..$]) Match;
    }
}

/**
The same, with $(M Then) and $(M Else) being aliases.
*/
struct If(alias condition, alias Then, alias Else)
{
    template Match(T...)
    {
        static if (T.length && condition!(T[0]))
            alias Success!(Then!(T[0])).Next!(T[1..$]) Match;
        else
            alias Success!(Else!(T[0])).Next!(T[1..$]) Match;
    }
}

/**
Transforms a pattern such that, if it matches, it puts back its match in the input tuple, for the next pattern
to consume.
See_Also: $(M LookAhead).
*/
struct ReleaseMatch(Pattern)
{
    template Match(T...)
    {
        static if (.Match!(Pattern, T).hasMatched)
            alias Success!().Next!(.Match!(Pattern, T).Result, .Match!(Pattern, T).Post) Match;
        else
            alias Failure!(T) Match;
    }
}

/**
Transforms a pattern such that, if it matches, it discards its match: the match result is the empty typetuple.
See_Also: $(M Left), $(M Right), $(M LeftMost), $(M RightMost).
*/
struct DiscardMatch(Pattern)
{
    template Match(T...)
    {
        static if (.Match!(Pattern, T).hasMatched)
            alias Success!().Next!(.Match!(Pattern, T).Post) Match;
        else
            alias Failure!(T) Match;
    }
}

/**
Matches iff $(M Pattern1) and then $(M Pattern2) match, but returns only $(M Pattern1)'s match result.
*/
template Left(Pattern1, Pattern2)
{
    alias And!(Pattern1, DiscardMatch!Pattern2) Left;
}

/**
Matches iff $(M Pattern1) and then $(M Pattern2) match, but returns only $(M Pattern2)'s match result.
*/
template Right(Pattern1, Pattern2)
{
    alias And!(DiscardMatch!Pattern1, Pattern2) Right;
}

/**
Matches iff all $(M Patterns) match, but returns only the first (leftmost) pattern match result.
*/
template LeftMost(Patterns...)
{
    alias Successively!(Patterns[0], staticMap!(DiscardMatch, Patterns[1..$])) LeftMost;
}

/**
Matches iff all $(M Patterns) match, but returns only the last (rightmost) pattern match result.
*/
template RightMost(Patterns...)
{
    alias Successively!(staticMap!(DiscardMatch, Patterns[0..$-1]), Patterns[$-1]) RightMost;
}

/**
Matches iff all $(M Patterns) match, returns the leftmost pattern match result, without consuming the rest.
*/
template LookAhead(Patterns...)
{
    alias Successively!(Patterns[0], staticMap!(ReleaseMatch, Patterns[1..$])) LookAhead;
}

/**
Tests the first pattern. If it matches, it releases its match and then tests the second pattern in the same manner. All
patterns will be tested in this way, getting them to match on the same input (more or less). Only if all of them match
simultaneously will $(M Simultaneously) returns a match: the last pattern's match. Not to be confused with $(M And) or $(M Successively)
that test for matches while consuming the first patterns matches.
----
alias Simultaneously!(And!(_,_), int) S; // S matches if there are two types in a row and the first one is an int. Returns 'int'.
----
Note: I'm not sure this is interesting, as there is frequently a way to express the same pattern in another way.
I'm just playing along with $(M ReleaseMatch), really.
*/
template Simultaneously(Patterns...)
{
    alias Successively!(staticMap!(ReleaseMatch, Patterns[0..$-1]), Patterns[$-1]) Simultaneously;
}

/**
Transforms a pattern so that it'll consume input until it finds a match.
Only if it reaches the end of the typetuple without matching does it return (M NoMatch).
*/
struct UnAnchored(Pattern)
{
    template Match(T...)
    {
        static if (.Match!(Pattern,T).hasMatched)
            alias .Match!(Pattern, T) Match;
        else static if (T.length)
            alias UnAnchored!(Pattern).Match!(T[1..$]) Match;
        else
            alias Failure!(T) Match;
    }
}

