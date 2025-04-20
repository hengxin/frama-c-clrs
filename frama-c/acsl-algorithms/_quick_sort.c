/*@ predicate Swap{L1,L2}(int *a, integer i, integer j) =
       \at(a[i],L1) == \at(a[j],L2) &&
       \at(a[j],L1) == \at(a[i],L2) &&
       \forall integer k; k != i && k != j
          ==> \at(a[k],L1) == \at(a[k],L2);
 */

/*@ inductive Permut{L1,L2}(int *a, integer l, integer h) {
    case Permut_refl{L}:
      \forall int *a, integer l, h; Permut{L,L}(a, l, h);
    case Permut_sym{L1,L2}:
      \forall int *a, integer l, h;
        Permut{L1,L2}(a, l, h) ==> Permut{L2,L1}(a, l, h);
    case Permut_trans{L1,L2,L3}:
      \forall int *a, integer l, h;
        Permut{L1,L2}(a, l, h) && Permut{L2,L3}(a, l, h) ==>
          Permut{L1,L3}(a, l, h);
    case Permut_swap{L1,L2}:
      \forall int *a, integer l, h, i, j;
         l <= i <= h && l <= j <= h && Swap{L1,L2}(a, i, j) ==>
       Permut{L1,L2}(a, l, h);
   }
 */

/*@ predicate Sorted{L}(int *a, integer l, integer h) =
       \forall integer i,j; l <= i <= j < h ==> a[i] <= a[j];
 */

/*@ requires \valid(t+i);
    requires \valid(t+j);
    assigns t[i],t[j];
    ensures Swap{Old,Here}(t,i,j);
 */
void sort_swap(int t[], int i, int j) {
    int tmp = t[i];
    t[i] = t[j];
    t[j] = tmp;
}

/*@ requires \valid(t + (l..r));
    requires r >= 0;
    requires l >= 0;
    decreases r - l;
    assigns t[l..r];
    ensures Sorted(t, l, r + 1);
    ensures Permut{Old,Here}(t, l, r);
 */
void quick_rec(int t[], int l, int r) {
    int v, m, i;
    if (l >= r) return;
    v = t[l];
    m = l;
    /*@
      loop invariant \forall integer j; l < j <= m ==> t[j] < v;
      loop invariant \forall integer j; m < j <  i ==> t[j] >= v;
      loop invariant Permut{Pre,Here}(t, l, r);
      loop invariant t[l] == v && l <= m < i <= r + 1;
      loop assigns t[l..r];
      loop variant r - i;
    */
    for (i = l + 1; i <= r; i++) {
        if (t[i] < v) {
        L1:
            sort_swap(t, i, ++m);
        }
    }
L:
    sort_swap(t, l, m);
    quick_rec(t, l, m - 1);
    quick_rec(t, m + 1, r);
}

/*@ requires n >= 0;
    requires \valid(t + (0..n-1));
    assigns t[0..n-1];
    ensures Sorted(t, 0, n);
    ensures Permut{Old,Here}(t, 0, n-1);
*/
void quick_sort(int t[], int n) {
    quick_rec(t, 0, n - 1);
}