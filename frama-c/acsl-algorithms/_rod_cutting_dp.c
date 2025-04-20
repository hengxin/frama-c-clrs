/*@
  requires n >= 0;
  requires \valid_read(price+(1..n));
  requires \valid(r+(0..n));
  assigns \nothing;
  ensures \result == 0 || \result == \max(1, n, \lambda integer i; price[i]+r[n-i]);
*/
int rod_cutting_dp(int price[], int r[], int n) {
    r[0] = 0;
    int j, i, q;
    /*@
      loop invariant 0 <= j <= n;
      loop invariant r[j] == \max(1, j - 1, \lambda integer k; price[k] + r[j-k]);
      loop assigns r[1..n];
      loop variant n - j;
    */
    for (j = 1; j <= n; j++) {
        q = -2147483648;
        /*@
            loop invariant 1 <= i <= j+1;
            loop invariant q == \max(1, i - 1, \lambda integer k; price[k] + r[j-k]);
            loop assigns \nothing;
            loop variant j - i + 1;
        */
        for (i = 1; i <= j; i++) {
            int temp = price[i] + r[j - i];
            if (temp > q) {
                q = temp;
            }
        }
        r[j] = q;
    }
    return r[n];
}