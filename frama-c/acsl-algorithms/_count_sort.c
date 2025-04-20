/*@
  predicate sorted{L}(int* a, integer lo, integer hi) =
    \forall integer i, j; lo <= i < j < hi ==> a[i] <= a[j];
*/

/*@
  requires n > 0;
  requires k >= 0;
  requires \valid_read(a+(0..n-1));
  requires \valid(b+(0..n-1));
  requires \valid(count+(0..k));
  requires \forall integer i; 0 <= i < n ==> 0 <= a[i] <= k;
  assigns a[0..n-1], count[0..k];
  ensures sorted(b, 0, n);
*/
void counting_sort(int a[], int n, int b[], int count[], int k) {
    int i;

    /*@
        loop invariant 0 <= i <= k+1;
        loop invariant \forall integer j; 0 <= j < i ==> count[j] == 0;
        loop assigns count[0..k];
        loop variant k+1 - i;
    */
    for (i = 0; i <= k; i++) {
        count[i] = 0;
    }

    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall integer x; 0 <= x <= k ==>
                count[x] == \sum(0, i-1, \lambda integer j; (a[j] == x ? 1 : 0));
        loop assigns count[a[i]];
        loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        count[a[i]]++;
    }

    /*@
        loop invariant 1 <= i <= k+1;
        loop invariant count[0] == \sum(0, n - 1, \lambda integer j; (a[j] == 0 ? 1 : 0));
        loop invariant \forall integer x; 1 <= x < i ==>
            count[x] == \sum(0, n - 1, \lambda integer j; (a[j] == 0 ? 1 : 0))
                        + \sum(0, n - 1, \lambda integer j; (a[j] == x ? 1 : 0));
        loop assigns count[i];
        loop variant k+1 - i;
    */
    for (i = 1; i <= k; i++) {
        count[i] = count[i] + count[i - 1];
    }

    /*@
        loop invariant -1 <= i && i < n;
        loop assigns count[a[i]], b[count[a[i]]];
        loop variant i + 1;
    */
    for (i = n - 1; i >= 0; i--) {
        int key = a[i];
        count[key]--;
        b[count[key]] = key;
    }
}