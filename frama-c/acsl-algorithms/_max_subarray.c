/*@
  logic integer subarray_sum(int* a, integer i, integer j) =
    i > j ? 0 : a[i] + subarray_sum(a, i+1, j);
*/

/*@
  requires n > 0;
  requires \valid_read(a+(0..n-1));
  assigns \nothing;
  ensures \forall integer i, j; 0 <= i <= j < n ==> subarray_sum(a, i, j) <= \result;
  ensures \exists integer i, j; 0 <= i <= j < n && \result == subarray_sum(a, i, j);
*/
int kadane(int a[], int n) {
    int current_sum = a[0];
    int max_sum = a[0];
    int i;

    /*@
      loop invariant 1 <= i <= n;
      loop invariant \forall integer p, q; 0 <= p <= q < i ==> subarray_sum(a, p, q) <= max_sum;
      loop invariant \exists integer p, q; 0 <= p <= q < i && max_sum == subarray_sum(a, p, q);
      loop invariant current_sum <= max_sum;
      loop assigns current_sum, max_sum;
      loop variant n - i;
    */
    for (i = 1; i < n; i++) {
        if (current_sum < 0)
            current_sum = a[i];
        else
            current_sum = current_sum + a[i];
        if (current_sum > max_sum)
            max_sum = current_sum;
    }
    return max_sum;
}