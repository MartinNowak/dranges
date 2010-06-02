/**
A simple queue module. It's from an old codebase and will be transformed, maybe fused with stack.
*/
module dranges.queue;

///
struct Queue(T) {
    T[] queue;
    size_t begin, end;

    ///
    this(int initialLength = 1000) {
        queue.length = initialLength;
        begin = 0;
        end = 0;
    }

    ///
    void push(T value) {
        if (end == queue.length) {
            queue.length = queue.length*2;
        }
        queue[end] = value;
        end++;
    }

    ///
    T top() {
        return queue[begin];
    }

    ///
    T pop() {
        T pop = queue[begin];
        begin++;
        if (begin>(queue.length/2)) { // Half-empty -> put the values at the beginning.
            int l = queue.length;
            queue = queue[begin..$].dup;
            queue.length = l;
            end -= begin;
            begin = 0;
        }
        return pop;
    }

    ///
    bool empty() {
        return (begin == end);
    }

    ///
    size_t length() {
        return end-begin;
    }
}
