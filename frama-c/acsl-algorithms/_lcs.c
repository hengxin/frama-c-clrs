/*@
  requires m >= 0 && n >= 0;
  requires \valid_read(X+(0..m-1));
  requires \valid_read(Y+(0..n-1));
  requires \valid(dp+(0..m-1));
  assigns dp[0..m][0..n];
  ensures \result >= 0;
*/
int lcs(char *X, char *Y, int m, int n, int dp[][1007]) {
    int i, j;

    /*@
      loop invariant 0 <= i <= m;
      loop invariant \forall integer k; 0 <= k < i ==> dp[k][0] == 0;
      loop assigns dp[0..m][0];
      loop variant m - i;
    */
    for (i = 0; i <= m; i++) {
        dp[i][0] = 0;
    }

    /*@
      loop invariant 0 <= j <= n;
      loop invariant \forall integer k; 0 <= k < j ==> dp[0][k] == 0;
      loop assigns dp[0][0..n];
      loop variant n - j;
    */
    for (j = 0; j <= n; j++) {
        dp[0][j] = 0;
    }

    /*@
      loop invariant 1 <= i <= m;
      loop invariant \forall integer u, v; 1 <= u < i && 0 <= v <= n ==> dp[u][v] >= 0;
      loop assigns dp[0..m][0..n];
      loop variant m - i;
    */
    for (i = 1; i <= m; i++) {
        /*@
          loop invariant 1 <= j <= n;
          loop invariant \forall integer v; 1 <= v < j ==> dp[i][v] >= dp[i-1][v] && dp[i][v] >= dp[i][v-1];
          loop invariant dp[i][0] == 0;
          loop assigns dp[0..m][0..n];
          loop variant n - j;
        */
        for (j = 1; j <= n; j++) {
            if (X[i - 1] == Y[j - 1]) {
                dp[i][j] = dp[i - 1][j - 1] + 1;
            } else {
                if (dp[i - 1][j] >= dp[i][j - 1])
                    dp[i][j] = dp[i - 1][j];
                else
                    dp[i][j] = dp[i][j - 1];
            }
        }
    }
    return dp[m][n];
}