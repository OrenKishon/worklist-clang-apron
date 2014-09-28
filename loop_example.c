#include <stdio.h>

static void loop_example(void)
{
    /* B[7] = T (top) */

    /* B[6] */
    int x;
    x = 7;
    /* B[6] = [x := 7]#R[0] = x ∈ [7, 7] */

    /* B[5] = B[6] U B[3] */
    while (x < 1000)
    {
        /* Concrete: B[4] = intersect(B[5], {s | s(x) < 1000}) */
        /* Abstract: B[4] = meet(B[5], [-inf, 999]) */
        ++x;
        
        /* Concrete: B[3] = [x := x+1]B[4] */
        /* abstract: B[3] = B[4] + [1, 1] */
    }

    /* Concrete: B[2] = intersect(B[5], {s | s(x) >= 1000}) */
    /* Abstract: B[2] = meet(B[5], [1000, inf]) */
    if (x != 1000)
    {
        /* Concrete: B[1] = intersect(B[2], x != 1000) */
        /* Concrete: B[1] = intersect(B[2],x<=999) U intersect(B[2],x>=1001) */
        /* Abstract: B[1] = Join(Meet(B[2],[-inf,999]),Meet(B[2],[1001,inf])) */
        printf("Unable to prove x == 1000!\n");
    }

    /* B[0] */
}

int main(void)
{
    loop_example();

    return 0;
}
