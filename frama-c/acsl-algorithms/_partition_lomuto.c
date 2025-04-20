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
  requires lo <= hi;
  requires \valid(a + (lo .. hi));
  assigns a[lo..hi];
  ensures lo <= \result <= hi;
  ensures \forall integer i; lo <= i < \result ==> a[i] <= a[\result];
  ensures \forall integer i; \result < i <= hi ==> a[i] >= a[\result];
*/
int partition(int a[], int lo, int hi) {
    int pivot = a[hi];
    int i = lo - 1;
    int j;

    /*@
    loop invariant lo <= j <= hi;
    loop invariant -1 <= i < j;
    loop invariant \forall integer k; lo <= k <= i ==> a[k] <= pivot;
    loop invariant \forall integer k; i+1 <= k < j ==> a[k] > pivot;
    loop assigns a[lo..hi];
    loop variant hi - j;
    */
    for (j = lo; j < hi; j++) {
        if (a[j] <= pivot) {
            i++;
            swap(&a[i], &a[j]);
        }
    }
    swap(&a[i + 1], &a[hi]);
    return i + 1;
}