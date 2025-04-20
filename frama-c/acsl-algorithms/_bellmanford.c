#include <limits.h>
#define MAX_VERTICES 100
#define INF INT_MAX
struct Edge {
    int u, v, weight;
};

/*@
  requires e > 0;
  requires \valid(edges+(0..e-1));
  requires n > 0;
  requires \valid(dist+(0..n-1));
  requires \valid(parent+(0..n-1));
  assigns dist[0..n-1], parent[0..n-1];
  ensures \forall integer i; 0 <= i < n ==> dist[i] >= 0;
  ensures \forall integer i; 0 <= i < n ==> parent[i] == -1 || (dist[parent[i]] + edges[parent[i]].weight == dist[i]);
*/
int bellmanFord(int n, int e, struct Edge edges[], int start, int dist[], int parent[]) {
    /*@
      loop invariant 0 <= i <= n-1;
      loop invariant \forall integer k; 0 <= k < i ==> dist[k] == INF;
      loop invariant \forall integer k; 0 <= k < i ==> parent[k] == -1;
      loop assigns dist[0..n-1], parent[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        dist[i] = INF;
        parent[i] = -1;
    }
    dist[start] = 0;

    /*@
      loop invariant 0 <= i <= n-1;
      loop invariant \forall integer k; 0 <= k < i ==> dist[k] <= dist[k];
      loop assigns dist[0..n-1], parent[0..n-1];
      loop variant n - i;
    */
    for (int i = 1; i < n; i++) {
        /*@
          loop invariant 0 <= j < e;
          loop invariant \forall integer k; 0 <= k < j ==> dist[edges[k].v] <= dist[edges[k].v];
          loop assigns dist[0..n-1], parent[0..n-1];
          loop variant e - j;
        */
        for (int j = 0; j < e; j++) {
            int u = edges[j].u;
            int v = edges[j].v;
            int weight = edges[j].weight;
            if (dist[u] != INF && dist[u] + weight < dist[v]) {
                dist[v] = dist[u] + weight;
                parent[v] = u;
            }
        }
    }

    return 0;
}