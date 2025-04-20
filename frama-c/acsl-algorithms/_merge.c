/*@
  requires \valid_read(A+(left..right-1));
  requires \valid(B+(left..right-1));
  requires left <= mid <= right;
  requires \forall integer i, j; left <= i < j < mid ==> A[i] <= A[j];
  requires \forall integer i, j; mid <= i < j < right ==> A[i] <= A[j];
  assigns B[left..right-1];
  ensures \forall integer i, j; left <= i < j < right ==> B[i] <= B[j];
  ensures \forall integer v; (\exists integer i; left <= i < right && B[i] == v) <==> ((\exists integer i; left <= i < mid && A[i] == v) || (\exists integer i; mid <= i < right && A[i] == v));
*/
void merge(const int A[], int left, int mid, int right, int B[]) {
    int i = left, j = mid, k = left;

    /*@
      loop invariant left <= i <= mid;
      loop invariant mid <= j <= right;
      loop invariant k == i + j - mid;
      loop invariant \forall integer r; left <= r < k ==>
           (\exists integer p; left <= p < i && B[r] == A[p] ||
            \exists integer q; mid <= q < j && B[r] == A[q]);
      loop invariant \forall integer r, s; left <= r < s < k ==> B[r] <= B[s];
      loop assigns B[k..right-1];
      loop variant (mid - i) + (right - j);
    */
    while (i < mid && j < right) {
        if (A[i] <= A[j]) {
            B[k++] = A[i++];
        } else {
            B[k++] = A[j++];
        }
    }

    /*@
      loop invariant i >= left && i <= mid;
      loop invariant k == i + j - mid;
      loop invariant \forall integer r; left <= r < k ==>
           (\exists integer p; left <= p < i && B[r] == A[p] ||
            \exists integer q; mid <= q < j && B[r] == A[q]);
      loop invariant \forall integer r, s; left <= r < s < k ==> B[r] <= B[s];
      loop assigns B[k..right-1];
      loop variant mid - i;
    */
    while (i < mid) {
        B[k++] = A[i++];
    }

    /*@
      loop invariant j >= mid && j <= right;
      loop invariant k == i + j - mid;
      loop invariant \forall integer r; left <= r < k ==>
           (\exists integer p; left <= p < i && B[r] == A[p] ||
            \exists integer q; mid <= q < j && B[r] == A[q]);
      loop invariant \forall integer r, s; left <= r < s < k ==> B[r] <= B[s];
      loop assigns B[k..right-1];
      loop variant right - j;
    */
    while (j < right) {
        B[k++] = A[j++];
    }
}