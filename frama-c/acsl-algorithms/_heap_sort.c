/*@
  predicate sorted{L}(int* a, integer lo, integer hi) =
    \forall integer i, j; lo <= i < j < hi ==> a[i] <= a[j];
*/

/*@
  predicate max_heap{L}(int* a, integer n, integer i) =
    (2*i+1 >= n) ||
    (2*i+1 < n && a[i] >= a[2*i+1] &&
     (2*i+2 >= n || a[i] >= a[2*i+2]) &&
     max_heap(a, n, 2*i+1) &&
     (2*i+2 < n ==> max_heap(a, n, 2*i+2)));
*/

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
    requires n >= 0;
    requires \valid(a+(0..n-1));
    decreases n - i;
    assigns a[0..n-1];
    ensures max_heap(a, n, i);
*/
void heapify(int a[], int n, int i) {
    int largest = i;
    int left = 2 * i + 1;
    int right = 2 * i + 2;
    if (left < n && a[left] > a[largest])
        largest = left;
    if (right < n && a[right] > a[largest])
        largest = right;
    if (largest != i) {
        swap(&a[i], &a[largest]);
        heapify(a, n, largest);
    }
}

/*@
   requires n > 0;
   requires \valid(a+(0..n-1));
   assigns a[0..n-1];
   ensures sorted(a, 0, n);
*/
void heap_sort(int a[], int n) {
    int i;
    /*@
        loop assigns a[0..n-1];
        loop variant n/2 - 1 - i;
    */
    for (i = n / 2 - 1; i >= 0; i--) {
        heapify(a, n, i);
    }
    /*@
        loop assigns a[0..n-1];
        loop variant n - 1 - i;
    */
    for (i = n - 1; i > 0; i--) {
        swap(&a[0], &a[i]);
        heapify(a, i, 0);
    }
}