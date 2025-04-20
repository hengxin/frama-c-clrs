/*@
  predicate sorted{L}(double* a, integer lo, integer hi) =
    \forall integer i, j; lo <= i < j < hi ==> a[i] <= a[j];
*/

/*@ axiomatic Array_Sum {
    logic integer array_sum{L}(int *a, integer b);

    axiom array_sum_init{L}:
       \forall int *a, integer b; b <= 0 ==> array_sum(a, b) == 0;

    axiom array_sum_step_dec{L}:
       \forall int *a, integer b; array_sum(a, b) == array_sum(a, b-1) + a[b];
    }
*/

/*@
  requires n >= 0;
  requires \valid(a+(0..n-1));
  assigns a[0..n-1];
  ensures sorted(a, 0, n);
*/
void insertion_sort(double a[], int n) {
    int i, j;
    double key;
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
          loop invariant \forall integer k; 0 <= k <= j ==> a[k] > key ==> a[k+1] == a[k];
          loop assigns a[0..i];
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
  requires n > 0;
  requires \valid(a+(0..n-1));
  requires \forall integer i; 0 <= i < n ==> 0.0 <= a[i] < 1.0;
  assigns a[0..n-1];
  ensures sorted(a, 0, n);
*/
void bucket_sort(double a[], int bucket_count[], double buckets[][100],int n) {
    int i, j, b;

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < i ==> bucket_count[k] == 0;
      loop assigns bucket_count[0..n-1];
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        bucket_count[i] = 0;
    }

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer k; 0 <= k < n ==> bucket_count[k] >= 0 && bucket_count[k] <= n;
      loop assigns bucket_count[0..n-1], buckets[0..n-1][0..n-1];
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
      b = (int)(a[i] * n);
      buckets[b][bucket_count[b]] = a[i];
      bucket_count[b]++;
    }

    /*@
        loop assigns \nothing;
    */
    for (i = 0; i < n; i++) {
        insertion_sort(buckets[i], bucket_count[i]);
    }

    j = 0;
    /*@
      loop invariant 0 <= i < n;
      loop invariant j == 0 || j == array_sum(bucket_count, i-1);
      loop assigns a[0..n-1];
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        int cnt = bucket_count[i];
        /*@
          loop invariant 0 <= b <= cnt;
          loop invariant j <= array_sum(bucket_count, n-1);
          loop assigns a[0..n-1];
          loop variant cnt - b;
        */
        for (b = 0; b < cnt; b++) {
            a[j] = buckets[i][b];
            j++;
        }
    }
}