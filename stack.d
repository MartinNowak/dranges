// Written in the D programming language

/**
A simple stack module.


License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.stack;

///
struct Stack(T) {
    T[] data;
    size_t index;

    ///
    @disable this();

    ///
    static Stack opCall(int initialLength = 1000) {
        Stack s = void;
        s.data = new T[](initialLength);
        s.index = 0;
        return s;
    }

    ///
    void push(T value) {
        if (index == data.length) {
            data.length = data.length*2;
        }
        data[index] = value;
        index++;
    }

    ///
    T top() {
        return data[index-1];
    }

    ///
    T pop() {
        T pop = data[index-1];
        index--;
        return pop;
    }

    ///
    bool empty() {
        return (index == 0);
    }

    ///
    size_t length() {
        return index;
    }
}
