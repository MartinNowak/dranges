/**
A simple stack module.
*/
module dranges.stack;

import std.stdio:writeln;

///
struct Stack(T) {
    T[] data;
    size_t index;

    ///
    this(int initialLength = 1000) {
        data.length = initialLength;
        index = 0;
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
