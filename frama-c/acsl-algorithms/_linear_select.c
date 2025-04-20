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
  assigns a[0..n-1];
  ensures \forall integer i, j; 0 <= i < j < n ==> a[i] <= a[j];
*/
void insertion_sort_small(int a[], int n) {
    int i, j, key;
    /*@
      loop invariant 1 <= i <= n;
      loop assigns a[0..n-1];
      loop variant n - i;
    */
    for (i = 1; i < n; i++) {
        key = a[i];
        j = i - 1;
        /*@
          loop invariant -1 <= j < i;
          loop assigns a[0..n-1];
          loop variant j + 1;
        */
        while (j >= 0 && a[j] > key) {
            a[j + 1] = a[j];
            j--;
        }
        a[j + 1] = key;
    }
}

/*@
  requires lo <= hi;
  requires \valid(a+(lo .. hi));
  requires \exists integer p; lo <= p <= hi && a[p] == pivot;
  assigns a[lo..hi];
  ensures lo <= \result && \result <= hi;
  ensures a[\result] == pivot;
  ensures \forall integer i; lo <= i < \result ==> a[i] < pivot;
  ensures \forall integer i; \result < i <= hi ==> a[i] >= pivot;
*/
int partition_select(int a[], int lo, int hi, int pivot) {
    int pivot_index = lo;
    int i;
    /*@
      loop invariant lo <= i <= hi;
      loop assigns \nothing;
      loop variant hi - lo - i;
    */
    for (i = lo; i <= hi; i++) {
        if (a[i] == pivot) {
            pivot_index = i;
            break;
        }
    }
    swap(&a[pivot_index], &a[hi]);
    int p = lo - 1;
    int j;
    /*@
      loop invariant lo <= j <= hi;
      loop invariant lo - 1 <= p < j;
      loop invariant \forall integer k; lo <= k <= p ==> a[k] < pivot;
      loop invariant \forall integer k; p+1 <= k < j ==> a[k] >= pivot;
      loop assigns a[lo..hi];
      loop variant hi - j;
    */
    for (j = lo; j < hi; j++) {
        if (a[j] < pivot) {
            p++;
            swap(&a[p], &a[j]);
        }
    }
    p++;
    swap(&a[p], &a[hi]);
    return p;
}

int linear_select(int a[], int lo, int hi, int k);

/*@
  requires lo <= hi;
  requires \valid(a+(lo .. hi));
  assigns \nothing;
*/
int select_pivot(int a[], int lo, int hi) {
    int n = hi - lo + 1;
    if (n <= 5) {
        insertion_sort_small(a + lo, n);
        return a[lo + n / 2];
    }
    int num_groups = (n + 4) / 5;
    int medians[num_groups];
    int i;
    /*@
      loop invariant 0 <= i <= num_groups;
      loop assigns \nothing;
      loop variant num_groups - i;
    */
    for (i = 0; i < num_groups; i++) {
        int group_lo = lo + i * 5;
        int group_hi = group_lo + 4;
        if (group_hi > hi) {
            group_hi = hi;
        }
        int group_n = group_hi - group_lo + 1;
        insertion_sort_small(a + group_lo, group_n);
        medians[i] = a[group_lo + group_n / 2];
    }
    return linear_select(medians, 0, num_groups - 1, num_groups / 2);
}

/*@
  requires lo <= hi;
  requires \valid(a+(lo .. hi));
  requires 0 <= k <= hi - lo;
  assigns a[lo..hi];
  ensures \result == (\old(a))[lo + k]; // Informal: returns the kth smallest element of a[lo..hi]
*/
int linear_select(int a[], int lo, int hi, int k) {
    if (lo == hi) {
        return a[lo];
    }
    int pivot = select_pivot(a, lo, hi);
    int p = partition_select(a, lo, hi, pivot);
    int rank = p - lo;
    if (rank == k) {
        return a[p];
    } else if (k < rank) {
        return linear_select(a, lo, p - 1, k);
    } else {
        return linear_select(a, p + 1, hi, k - rank - 1);
    }
}