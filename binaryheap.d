// Written in the D programming language.

/**
A simple binary heap implementation, used as a basis for a priority queue in dranges.priorityqueue, itself
used in the dranges.graph algorithms.

This module is old (august 2009), I will clean it up to follow the changes in D containers and ranges.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.binaryheap;

import std.stdio;
import std.algorithm : swap;
import std.functional : binaryFun;
import std.math: sgn;
import std.typecons;
import std.contracts;
import std.conv;

///
struct BinaryHeap(alias predicate = "a < b", T) {
    T[] data;
    size_t[T] position; // supposition: keys are unique. Only used for priority queues,
                        // for which this assumption holds true : Tuple!(Priority, Value) are keys
    size_t end;
    alias binaryFun!(predicate) pred;

    ///
    this(T[] _data) {
        end = 0;
        data.length = _data.length;
        put(_data);
    }

    ///
    bool empty() {return (end == 0);}

    ///
    void put(T)(T t) {
        data[end] = t;
        position[t] = end;
        bubbleUp(end);
        end++;
        if (end == data.length) data.length = data.length * 2;
    }

    ///
    void put(U: T[])(U array) {
        foreach(t; array) put(t);
    }

    ///
    void put(P,V)(V value, P priority) if(is(T == Tuple!(P, V))) {
        put(tuple(priority, value));
    }

    ///
    T front() {
        return data[0];
    }

    ///
    @property BinaryHeap save() { return this;}

    ///
    void popFront() {
        end--;
        data[0] = data[end];
        data[end] = T.init;
        siftDown(0);
    }

    ///
    void swapKeys(size_t i1, size_t i2) {
        position[data[i1]] = i2;
        position[data[i2]] = i1;
        swap(data[i1], data[i2]);
    }

    /**
    Changes a key value in the heap. In case of many keys with
    the same value, one of them will bubble up or sift down according
    to its new value.
    */
    void changeKey(T oldKey, T newKey) {
        enforce(oldKey in position,
                "changeKey error: the key: " ~ to!string(oldKey) ~ " does not exist in the heap.");
        size_t index = position[oldKey];
        auto old = data[index];
        data[index] = newKey;
        position.remove(oldKey);
        position[newKey] = index;
        if (pred(data[index], old)) {
            bubbleUp(index);
        }
        else {
            siftDown(index);
        }
    }

    /**
    This will change a value priority (used for priority queues). Works only for priority queues:
    binary heap with tuples(priority, value) for keys.
    Throws: RangeError (Range violation) if the key/value does not exist.
    See_Also: PriorityQueue.changePriority()
    */
    void changePriority(P, V)(V value, P oldPriority, P newPriority) if(is(T == Tuple!(P,V))) {
        enforce(tuple(oldPriority, value) in position,
                "changePriority error: no value '" ~ to!string(value) ~ "' with priority: " ~ to!string(oldPriority) ~ " exists in this queue.");
        changeKey(tuple(oldPriority, value), tuple(newPriority, value));
    }

    void bubbleUp(size_t index) {
        if (index > 0) {
            size_t parent = (index-1)/2; // parent index
            if (pred(data[index], data[parent])) { // index < parent
                swapKeys(index, parent);
                bubbleUp(parent);
            }
        }
    }

    void siftDown(size_t index) {
        size_t first = 2*index+1; // first child index
        size_t second = first+1; // second child index
        int numChildren = sgn(cast(int)end-cast(int)second) + 1; // 0, 1 or 2
        switch (numChildren) {
            case 0: // No child, can't get lower
                break;
            case 1: // One child (the left one, first one).
                if (pred(data[first], data[index])) swapKeys(index, first); // first < index -> first<=>index
                break;
            case 2:
                if (pred(data[first], data[index]) && !pred(data[second], data[index])) { // first < index <= second -> first<=>index
                    swapKeys(first, index);
                    siftDown(first);
                    break;
                }
                if (pred(data[second], data[index]) && !pred(data[first], data[index])) { // second < index <= first -> second<=>index
                    swapKeys(second, index);
                    siftDown(second);
                    break;
                }
                if (pred(data[first], data[index]) && pred(data[second], data[index])) { // first&second < index
                    if (pred(data[first],data[second])) { // first is smallest -> first<=>index
                        swapKeys(first, index);
                        siftDown(first);
                        break;
                    }
                    else {                               // second is smallest (or equal) -> second<=>index
                        swapKeys(second, index);
                        siftDown(second);
                        break;
                    }
                }
                break;
            default:
                throw new Exception("We have a problem, Jim.");
        }
    }
}

/**
Helper function to infer type for T and to create a heap from an array of values
*/
BinaryHeap!(predicate, T) binaryHeap(alias predicate = "a < b", T)(T[] data) {
    return BinaryHeap!(predicate, T)(data);
}
