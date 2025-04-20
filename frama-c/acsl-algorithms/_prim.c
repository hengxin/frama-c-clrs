#define MAX_V 1007
#define INF 0x7fffffff

/*@
  requires n > 0 && n <= MAX_V;
  requires \valid(key + (0..n - 1));
  requires \valid(visited + (0..n - 1));
  assigns \nothing;
  ensures 0 <= \result < n || \result == -1;
  behavior no_node:
    assumes \forall integer i; 0 <= i < n ==> visited[i] || key[i] == INF;
    ensures \result == -1;
  behavior has_node:
    assumes \exists integer i; 0 <= i < n && !visited[i] && key[i] < INF;
    ensures !visited[\result];
    ensures \forall integer i; 0 <= i < n && !visited[i] ==> key[\result] <= key[i];
*/
int extract_min(int key[], int visited[], int n) {
    int min = INF;
    int min_index = -1;

    /*@
        loop invariant 0 <= v <= n;
        loop invariant 0 <= min_index < n || min_index == -1;
        loop invariant \forall integer i; 0 <= i < v && !visited[i] ==> key[min_index] <= key[i];
        loop assigns \nothing;
        loop variant n - v;
    */
    for (int v = 0; v < n; v++) {
        if (!visited[v] && key[v] < min) {
            min = key[v];
            min_index = v;
        }
    }
    return min_index;
}

/*@
  requires n > 0 && n <= MAX_V;
  requires \valid(parent + (0..n-1));
  requires \valid(graph + (0..n-1));
  requires \forall integer i; 0 <= i < n ==> \valid(graph[i] + (0..n-1));
  requires \forall integer i, j; 0 <= i < n && 0 <= j < n ==> graph[i][j] >= 0;
  assigns parent[0..n-1];
  ensures parent[0] == -1;
  ensures \forall integer i; 1 <= i < n ==> 0 <= parent[i] < n;
*/
void prim(int graph[MAX_V][MAX_V], int n, int parent[]) {
    int key[MAX_V];
    int visited[MAX_V];

    /*@
        loop invariant 0 <= i <= n;
        loop invariant \forall integer j; 0 <= j < i ==> key[j] == INF && visited[j] == 0 && parent[j] == -1;
        loop assigns visited[i], parent[i];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        key[i] = INF;
        visited[i] = 0;
        parent[i] = -1;
    }

    key[0] = 0;

    /*@
        loop invariant 0 <= count <= n;
        loop invariant \forall integer i; 0 <= i < n ==> 0 <= key[i] <= INF;
        loop invariant \forall integer i; 0 <= i < n ==> 0 <= parent[i] < n || parent[i] == -1;
        loop assigns visited[0..n-1], parent[0..n-1], key[0..n-1]; 
        loop variant n - count;
    */
    for (int count = 0; count < n - 1; count++) {
        int u = extract_min(key, visited, n);
        if (u == -1) break;

        visited[u] = 1;

        /*@
            loop invariant 0 <= v <= n;
            loop invariant \forall integer i; 0 <= i < n ==> key[i] >= 0 && key[i] <= INF;
            loop assigns key[0..n-1], parent[0..n-1];
            loop variant n - v;
        */
        for (int v = 0; v < n; v++) {
            if (graph[u][v] && !visited[v] && graph[u][v] < key[v]) {
                key[v] = graph[u][v];
                parent[v] = u;
            }
        }
    }
}