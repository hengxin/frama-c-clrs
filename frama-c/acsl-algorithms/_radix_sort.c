/*@
  predicate sorted{L}(int* a, integer lo, integer hi) =
    \forall integer i, j; lo <= i < j < hi ==> a[i] <= a[j];
*/

/*@
  requires n > 0;
  requires \valid_read(a+(0..n-1));
  assigns \nothing;
  ensures \forall integer i; 0 <= i < n ==> \result >= a[i];
  ensures \exists integer i; 0 <= i < n && \result == a[i];
*/
int find_max(int a[], int n) {
    int max = a[0];
    int i;
    /*@
      loop invariant 1 <= i <= n;
      loop invariant max == \max(0, i-1, \lambda integer k; a[k]);
      loop assigns \nothing;
      loop variant n - i;
    */
    for (i = 1; i < n; i++) {
        if (a[i] > max)
            max = a[i];
    }
    return max;
}

/*@
  requires n >= 0;
  requires exp > 0;
  requires \valid(a+(0..n-1));
  requires \forall integer i; 0 <= i < n ==> a[i] >= 0;
  assigns a[0..n-1];
*/
void counting_sort_digit(int a[], int n, int exp) {
    int i;
    int count[10];
    int output[1007];

    /*@
      loop invariant 0 <= i <= 10;
      loop invariant \forall integer j; 0 <= j < i ==> count[j] == 0;
      loop assigns count[i];
      loop variant 10 - i;
    */
    for (i = 0; i < 10; i++) {
        count[i] = 0;
    }

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer d; 0 <= d < 10 ==> count[d] == \numof(0, i-1, \lambda integer j; (a[j]/exp)%10 == d);
      loop assigns count[(a[i]/exp)%10];
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        int d = (a[i] / exp) % 10;
        count[d]++;
    }

    /*@
      loop invariant 1 <= i <= 10;
      loop invariant \forall integer d; 0 <= d < i ==> count[d] >= 0;
      loop assigns count[i];
      loop variant 10 - i;
    */
    for (i = 1; i < 10; i++) {
        count[i] += count[i - 1];
    }

    /*@
      loop invariant -1 <= i && i < n;
      loop assigns output[count[(a[i] / exp) % 10]-1], count[(a[i] / exp) % 10];
      loop variant i + 1;
    */
    for (i = n - 1; i >= 0; i--) {
        int d = (a[i] / exp) % 10;
        output[count[d] - 1] = a[i];
        count[d]--;
    }

    /*@
      loop invariant 0 <= i <= n;
      loop assigns a[i];
      loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        a[i] = output[i];
    }
}

/*@
  requires n > 0;
  requires \valid(a+(0..n-1));
  requires \forall integer i; 0 <= i < n ==> a[i] >= 0;
  assigns a[0..n-1];
  ensures sorted(a, 0, n);
*/
void radix_sort(int a[], int n) {
    int m = find_max(a, n);
    int exp = 1;
    /*@
      loop invariant exp > 0;
      loop invariant m/exp >= 0;
      loop invariant \forall integer i; 0 <= i < n ==> a[i] >= 0;
      loop assigns a[0..n-1];
      loop variant m / exp;
    */
    while (m / exp > 0) {
        counting_sort_digit(a, n, exp);
        exp = exp * 10;
    }
}