/*@
  predicate sorted{Here}(int* a, integer start_index, integer end_index) =
    \forall integer k1, k2;
    start_index <= k1 <= k2 <= end_index ==> a[k1] <= a[k2];
*/

/*@
  predicate swapped{L1,L2}(int* a, integer i, integer j) =
  \at(a[i],L1) == \at(a[j],L2) &&
  \at(a[j],L1) == \at(a[i],L2) &&
  \forall integer k; k != i && k != j
     ==> \at(a[k],L1) == \at(a[k],L2);
  */

/*@
  requires \valid(t+i) && \valid(t+j);
  assigns t[i],t[j];
  ensures \forall integer k; 0 <= k < n && k != i && k != j ==> t[k] == \old(t[k]);
  ensures swapped{Old,Here}(t,i,j);
  */
 void sort_swap3(int t[], int i, int j, int n) {
  int tmp = t[i];
  t[i] = t[j];
  t[j] = tmp;
}

/*@
requires 1 < length;
requires \valid(a+(0..length-1));
assigns a[0..length-1];
ensures sorted(a, 0, length-1);
*/
void bubble_sort(int *a, int length) {
  int up = 1;
  int down;

  /*@
      loop assigns a[0..length-1];
      loop assigns down, up;
      loop invariant 0 < up <= length;
      loop invariant sorted(a, 0, up-1);
      loop invariant \forall integer k; up < k < length ==> a[k] == \at(a[k], Pre);
  */
  for (; up < length; up++) {
      down = up;
      /*@
        loop assigns a[0..up];
        loop assigns down;
        loop invariant 0 <= down <= up < length;
        loop invariant sorted(a, 0, down-1);
        loop invariant sorted(a, down, up);
        loop invariant \forall integer k; up < k < length ==> a[k] == \at(a[k], Pre);
        loop invariant  0 < down < up ==> a[down-1] <= a[down+1];
      */
      while (0 < down && a[down] < a[down - 1]) {
          sort_swap3(a, down, down - 1, length);
          down = down - 1;
      }
  }
}