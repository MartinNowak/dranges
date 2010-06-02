/**
A simple priority queue module.
*/
module dranges.priorityqueue;

import std.typecons;
import std.conv;
import std.contracts;

import dranges.binaryheap;

/**
Thin wrapper around a BinaryHeap!(predicate, Tuple!(Priority, Value)).
Otherwise acts as a bona fide priority queue: you enter value/priority pairs, you
can change priority with changePriority(), insert elements with put and output them
with foreach() (or empty/front/popFront if you wish).
*/
struct PriorityQueue(alias predicate = "a < b", V, P) {

    ///
    alias Tuple!(P,V) PV;

    BinaryHeap!(predicate, PV) heap;

    /// forward most calls to the underlying binary heap.
    BinaryHeap!(predicate, PV)* opDot() {
        return &heap;
    }

    /// Defined so that foreach can infer element type.
    PV front() {
        return heap.front;
    }

    /**
    This will change a value priority.
    Throws: RangeError (Range violation) if the key/value does not exist.
    Note: It cannot just be (V value, P newPriority) and deduce the oldPriority by looking
    for value in the heap, because there may be many values (of same value...) with different
    priorities.
    */
    void changePriority(V value, P oldPriority, P newPriority) {
        enforce(tuple(oldPriority, value) in heap.position,
                "changePriority error: no value '" ~ to!string(value) ~ "' with priority: " ~ to!string(oldPriority) ~ " exists in this queue.");
        heap.changeKey(tuple(oldPriority, value), tuple(newPriority, value));
    }
}

/**
Helper function to infer types and put them in the queue.
Data is given in the argument list as value,priority pairs.
*/
PriorityQueue!(predicate, V, P) priorityQueue(alias predicate = "a < b", V, P, R...)(V value, P priority, R rest) {
    PriorityQueue!(predicate, V, P) pq;
    auto pvlist = toPairArrayInverted(value, priority, rest); // Creates a Tuple!(P,V) array

    pq.heap = binaryHeap!(predicate, Tuple!(P,V))(pvlist);
    return pq;
}

/**
Helper function to infer types and put them in the queue.
The argument is an associative array of values and priorities: ["a":0, "b":1, "qwerty":-100]

Values are keys, priority are values. It makes for a more readable list IMO, but
does not allow the existence of many times the same value, but entered in the queue with varying
priorities (it would erase the first pair). Use the preceding version for that.
*/
PriorityQueue!(predicate, V, P) priorityQueue(alias predicate = "a < b", V, P)(P[V] valuePriorityArray) {
    PriorityQueue!(predicate, V, P) pq;
    auto pvlist = toPairArrayInverted(valuePriorityArray); // Creates a Tuple!(P,V) array

    pq.heap = binaryHeap!(predicate, Tuple!(P,V))(pvlist);
    return pq;
}

// These should be cleaned up and put inside templates.d or associative.d

Tuple!(K,V)[] toPairArrayInverted(K, V, R...)(V value1, K key1, V value2, K key2, R rest) {
   if (rest.length > 0) {
        return [tuple(key1, value1)] ~ toPairArrayInverted(value2, key2, rest);
    }
    else {
        return [tuple(key1, value1), tuple(key2, value2)];
    }
}

Tuple!(K,V)[] toPairArrayInverted(K, V)(V value1, K key1) {
   return [tuple(key1, value1)];
}

Tuple!(V, K)[] toPairArrayInverted(K, V)(V[K] associativeArray) {
    Tuple!(V, K)[] result;
    foreach(key, value; associativeArray) {
        result ~= tuple(value, key);
    }
    return result;
}
