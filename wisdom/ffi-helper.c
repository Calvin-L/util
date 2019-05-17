// Helper file for ffi.hs, which illustrates
// how to call a C function from Haskell.

#include <stdio.h>

int fizzbuzz(int x) {
    return printf("fizzbuzz: %d\n", x);
}
