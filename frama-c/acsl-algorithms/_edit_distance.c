#include <string.h>

/*@
  requires \valid_read(s);
  requires \valid_read(t);
  assigns dp[0..m][0..n];
  ensures \result >= 0;
*/
int edit_distance(const char *s, const char *t, int m, int n, int dp[][1007]) {
    int i, j;
    /*@
      loop invariant 0 <= j <= n;
      loop invariant \forall integer k; 0 <= k < j ==> dp[0][k] == k;
      loop assigns dp[0][0..n];
      loop variant n - j;
    */
    for (j = 0; j <= n; j++) {
        dp[0][j] = j;
    }

    /*@
      loop invariant 0 <= i <= m;
      loop invariant \forall integer k; 0 <= k < i ==> dp[k][0] == k;
      loop assigns dp[0..m][0];
      loop variant m - i;
    */
    for (i = 0; i <= m; i++) {
        dp[i][0] = i;
    }

    /*@
      loop invariant 1 <= i <= m;
      loop assigns dp[1..m][1..n];
      loop variant m - i;
    */
    for (i = 1; i <= m; i++) {
        /*@
          loop invariant 1 <= j <= n;
          loop assigns dp[1..m][1..n];
          loop variant n - j;
        */
        for (j = 1; j <= n; j++) {
            if (s[i - 1] == t[j - 1])
                dp[i][j] = dp[i - 1][j - 1];
            else {
                int sub = dp[i - 1][j - 1] + 1;
                int del = dp[i - 1][j] + 1;
                int ins = dp[i][j - 1] + 1;
                dp[i][j] = sub;
                if (del < dp[i][j])
                    dp[i][j] = del;
                if (ins < dp[i][j])
                    dp[i][j] = ins;
            }
        }
    }
    return dp[m][n];
}