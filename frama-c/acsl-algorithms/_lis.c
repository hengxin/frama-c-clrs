/*@ logic integer max(integer a, integer b) =
          a > b ? a : b;
 */

/*@
  axiomatic LIS {
    logic integer LIS(int* a, integer n);

    axiom base_case:
      \forall int* a, integer n; n == 1 ==> LIS(a, n) == 1;

    axiom step_case:
      \forall int* a, integer n; n > 1 ==>
        \exists integer i; 0 <= i < n-1 && a[i] < a[n-1] ==>
          LIS(a, n) == max(LIS(a, n-1), LIS(a, i) + 1);
  }
*/

/*@
    requires n >= 0;
    requires n == 0 || \valid_read(arr+(0..n-1));
    requires \valid(dp+(0..n-1));
    assigns dp[0..n-1];
    ensures \result >= 0;
*/
int lis(int arr[], int n, int dp[]) {
    if (n == 0) return 0;
    int i, j;

    /*@
        loop assigns i, dp[0..n-1];
        loop invariant 0 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> dp[k] == 1;
        loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        dp[i] = 1;
    }

    /*@
        loop assigns i, j, dp[0..n-1];
        loop invariant 1 <= i <= n;
        loop invariant \forall integer k; 0 <= k < i ==> dp[k] >= 1;
        loop invariant \forall integer k; 0 <= k < i ==> dp[k] <= n;
        loop variant n - i;
    */
    for (i = 1; i < n; i++) {
        /*@
            loop invariant 0 <= j <= i;
            loop invariant dp[i] >= 1;
            loop invariant \forall integer k; 0 <= k < j ==>
                    (arr[k] < arr[i] ==> dp[i] >= dp[k] + 1);
            loop assigns dp[0..n-1];
            loop variant i - j;
        */
        for (j = 0; j < i; j++) {
            if (arr[j] < arr[i] && dp[j] + 1 > dp[i]) {
                dp[i] = dp[j] + 1;
            }
        }
    }

    int ans = dp[0];
    /*@
        loop invariant 1 <= i <= n;
        loop invariant ans == LIS(arr, i);
        loop assigns ans;
        loop variant n - i;
    */
    for (i = 1; i < n; i++) {
        if (dp[i] > ans) {
            ans = dp[i];
        }
    }
    return ans;
}