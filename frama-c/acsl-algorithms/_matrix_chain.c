/*@
  requires n > 0 && n <= 1007;
  requires \valid_read(p+(0..n));
  assigns \nothing;
  ensures \result >= 0;
*/
int matrix_chain_order(int p[], int n, int m[][1007]) {
    int i, j, l, k;

    /*@
      loop invariant 1 <= i <= n+1;
      loop invariant \forall integer r; 1 <= r < i ==> m[r][r] == 0;
      loop assigns m[i][i];
      loop variant n + 1 - i;
    */
    for (i = 1; i <= n; i++) {
        m[i][i] = 0;
    }

    /*@
      loop invariant 2 <= l <= n+1;
      loop assigns m[0..n-1][0..n-1];
      loop variant n+1 - l;
    */
    for (l = 2; l <= n; l++) {
        /*@
          loop invariant 1 <= i <= n - l + 2;
          loop invariant j == i + l - 1;
          loop assigns m[0..n-1][0..n-1];
          loop variant n - l - i + 1;
        */
        for (i = 1; i <= n - l + 1; i++) {
            j = i + l - 1;
            m[i][j] = 2147483647; 
            /*@
              loop invariant i <= k <= j;
              loop assigns m[0..n-1][0..n-1];
              loop variant j - k;
            */
            for (k = i; k < j; k++) {
                int q = m[i][k] + m[k + 1][j] + p[i - 1] * p[k] * p[j];
                if (q < m[i][j]) {
                    m[i][j] = q;
                }
            }
        }
    }
    return m[1][n];
}