// Written in the D programming language

/**
A simple set module.


License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.set;

import std.contracts;
import std.conv;

///
struct Set(T) {
    bool[T] data;

    ///
    this(T t) {
        put(t);
    }

    ///
    void put(T t) { data[t] = true;}

    ///
    void put(T[] tarr) { foreach(t; tarr) put(t);}

    ///
    bool opIn_r(T t) {
        return (t in data) ? true : false;
    }

    ///
    size_t length() {
        return data.length;
    }

    ///
    void remove(T t) {
        enforce((t in data), "Value: " ~ to!string(t) ~ " is not in the set.");
        data.remove(t);
    }

    ///
    string toString() {
        return to!string(data.keys);
    }

    ///
    T[] array() {
        return data.keys;
    }
}

///
Set!(T) fusion(T)(Set!(T) s1, Set!(T) s2) {
    auto result = s1;
    foreach(t; s2.array) result.put(t);
    result.data.rehash;
    return result;
}
