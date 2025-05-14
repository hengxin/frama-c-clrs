/*@
  predicate Sorted(int *t, integer lo, integer hi) =
    \forall integer i, j; lo <= i <= j < hi ==> t[i] <= t[j];
*/

/*@ requires \valid(t+(0..n-1));
    requires n > 0;
    ensures Sorted(t, 0, n-1);
    assigns t[0..n-1];
 */
void insert_sort(int t[], int n) {
    int i = 1, j = 1;
    int mv;
    
    /*@
        loop assigns i, j, mv, t[0..n-1];
        loop invariant 1 <= i <= n;
        loop invariant Sorted(t, 0, i);
        loop variant n - i;
     */
    for (i = 1; i < n; i++) {
        mv = t[i];
        /*@
            loop assigns j, t[0..i];
            loop invariant 0 <= j <= i;
            loop invariant j == i ==> Sorted(t, 0, i);
            loop invariant j < i ==> Sorted(t, 0, i+1);
            loop invariant \forall integer k; j <= k < i ==> t[k] > mv;
            loop variant j;
         */
        for (j = i; j > 0; j--) {
            if (t[j - 1] <= mv) break;
            t[j] = t[j - 1];
        }
        t[j] = mv;
    }
}