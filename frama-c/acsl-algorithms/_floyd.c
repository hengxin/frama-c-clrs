#define MAX_VERTICES 100
#define INF 1000000000

/*@
  requires n > 0;
  requires \valid_read(graph+(0..n-1));
  requires \forall integer i; 0 <= i < n ==> \valid_read(graph[i] + (0..n-1));
  requires \valid(dist+(0..n-1));
  requires \forall integer i; 0 <= i < n ==> \valid(dist[i] + (0..n-1));
  assigns dist[0..n-1][0..n-1];
*/
void floyd(int n, int graph[][MAX_VERTICES], int dist[][MAX_VERTICES]) {
    int i, j, k;

    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall integer r; 0 <= r < i ==> (\forall integer s; 0 <= s < n ==> dist[r][s] == graph[r][s]);
        loop assigns i, j, dist[0..n-1][0..n-1];
        loop variant n - i;
    */
    for (i = 0; i < n; i++) {
        /*@
            loop invariant 0 <= j <= n;
            loop invariant \forall integer s; 0 <= s < j ==> dist[i][s] == graph[i][s];
            loop assigns j, dist[i][0..n-1];
            loop variant n - j;
        */
        for (j = 0; j < n; j++) {
            dist[i][j] = graph[i][j];
        }
    }

    /*@
        loop invariant 0 <= k <= n;
        loop invariant \forall integer i, j; 0 <= i < n && 0 <= j < n ==> dist[i][j] <= INF;
        loop assigns k;
        loop variant n - k;
    */
    for (k = 0; k < n; k++) {
        /*@
            loop invariant 0 <= i <= n;
            loop invariant \forall integer r; 0 <= r < i ==> (\forall integer s; 0 <= s < n ==> dist[r][s] <= INF);
            loop assigns i;
            loop variant n - i;
        */
        for (i = 0; i < n; i++) {
            /*@
                loop invariant 0 <= j <= n;
                loop invariant \forall integer s; 0 <= s < j ==> dist[i][s] <= INF;
                loop assigns dist[i][0..n-1];
                loop variant n - j;
            */
            for (j = 0; j < n; j++) {
                if (dist[i][k] < INF && dist[k][j] < INF && dist[i][k] + dist[k][j] < dist[i][j])
                    dist[i][j] = dist[i][k] + dist[k][j];
            }
        }
    }
}