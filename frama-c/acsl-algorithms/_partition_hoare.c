/*@
  requires \valid(x) && \valid(y);
  assigns *x, *y;
  ensures *x == \old(*y) && *y == \old(*x);
*/
void swap(int *x, int *y) {
    int tmp = *x;
    *x = *y;
    *y = tmp;
}

/*@
  requires lo < hi;
  requires \valid(a + (lo .. hi));
  assigns a[lo..hi];
  ensures lo <= \result && \result < hi;
  ensures \forall integer i; lo <= i <= \result ==> a[i] <= \old(a[lo]);
  ensures \forall integer i; \result+1 <= i <= hi ==> a[i] >= \old(a[lo]);
*/
int partition_hoare(int a[], int lo, int hi) {
    int pivot = a[lo];
    int i = lo - 1;
    int j = hi + 1;
    /*@
    loop invariant lo <= i && i <= hi+1;
    loop invariant lo-1 <= j && j <= hi;
    loop invariant i <= j + 1;
    loop invariant \forall integer k; lo <= k < i ==> a[k] <= pivot;
    loop invariant \forall integer k; j < k <= hi ==> a[k] >= pivot;
    loop assigns a[lo..hi];
    loop variant j - i;
    */
    while (i < j) {
        /*@
            loop assigns i;
        */
        do {
            i++;
        } while (a[i] < pivot);
        /*@
            loop assigns j;
        */
        do {
            j--;
        } while (a[j] > pivot);
        swap(&a[i], &a[j]);
    }
    return j;
}