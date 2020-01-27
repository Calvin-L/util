/*

Java memory model (JMM) info.
Chapter 17 of spec:
    https://docs.oracle.com/javase/specs/jls/se11/html/index.html

DOUBLE-CHECKED LOCKING EXAMPLE

    Double-checked locking doesn't work.  Consider:

    initially:
        global non-volatile T x = null;

    thread A:
        synchronized (lock) {
            newVal = new T(); // non-final intField is initially 0
            newVal.intField = 1;
        }
        synchronized (lock) {
            x = newVal;
        }

    thread B:
        System.out.println(x.intField);

    observable behaviors in thread B:
        - NullPointerException (B runs before write to x)
        - 1 (B runs after write to x and write to intField)
        - 0 (UNEXPECTED!)
            + write to intField happens-before write to x
            + read of x happens-before read of intField
            + there are no happens-before relationships between actions of
              threads A and B
            + spec says:
              > if two actions share a happens-before relationship, they do
              > not necessarily have to appear to have happened in that order
              > to any code with which they do not share a happens-before
              > relationship. Writes in one thread that are in a data race
              > with reads in another thread may, for example, appear to
              > occur out of order to those reads.
            + Therefore, from B's perspective, A's writes may happen
              out-of-order.
            + More info:
              https://www.cs.umd.edu/~pugh/java/memoryModel/BidirectionalMemoryBarrier.html
              https://www.cs.umd.edu/~pugh/java/memoryModel/DoubleCheckedLocking.html
              https://www.cs.umd.edu/~pugh/java/memoryModel/AlphaReordering.html

    If x is volatile, then only the first two behaviors are possible, due to
    the additional constraints:
        + if B's read of x follows A's write to x, then B's raead synchronizes-with A's write
        + thus A's write to x happens-before B's read of x
        + thus by transitivity, A's write to intField happens-before B's read of intField

    But in that case, the locks have no benefit and can be removed.

FINAL FIELDS DEMYSTIFIED

    Final fields have a different semantics from normal fields.  Example 17.5-1
    in the JLS helps to clarify the situation.  As a real-world example, Google
    Guava's nonvolatile `entrySet` field is thread-safe, despite lazy
    initialization:
      https://github.com/google/guava/blob/74fc49f/guava/src/com/google/common/collect/ImmutableMap.java#L716

    In short:

        - If the PROGRAM ORDER enforces that a thread can only observe an
          object after its constructor finishes, then that thread must observe
          the correct values for that object's final fields.
        - This is true even if the object was shared with the thread over a
          non-synchronized channel.

    Or, in even-shorter terms:

        - If you have a non-null reference to a fully-constructed object, then
          your reads of its final fields will be correct.

    Note that the property is not transitive: your reads of the fields' fields
    may not be correct unless those are also final.
    ^^^^^^^^^^^^^
    I am actually having trouble determining whether what I wrote about
    transitivity is true or not.  The official spec is very complexly worded!

    Based on the language about strings and final fields, I think it actually
    DOES need to be transitive so that reads of the characters in the string's
    array are safe.

    Note:
      > It [a reader of a final field] will also see versions of any object or
      > array referenced by those final fields that are at least as up-to-date
      > as the final fields are.

    So it IS recursive, or at least one level deep.

*/
