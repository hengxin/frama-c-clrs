#define INT_MAX 0x7fffffff
#define MAX_VERTICES 100
/*@
  requires \valid(graph + (0..n - 1));
  requires \valid(result + (0..n - 1));
  requires \valid(queue + (0..n - 1));
  requires \valid(in_degree + (0..n - 1));
  assigns result[0..n - 1];
  assigns in_degree[0..n - 1];
  assigns queue[0..n - 1];
  ensures \forall integer i; 0 <= i < n ==> \exists integer j; 0 <= j < n && result[j] == i;
*/
void topo_sort(int graph[][MAX_VERTICES], int result[], int in_degree[], int queue[], int n) {
    int front = 0, rear = 0;
    int ptr = 0;
    /*@
      loop assigns in_degree[0..n - 1];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        /*@
          loop assigns in_degree[0..n - 1];
        */
        for (int j = 0; j < n; j++) {
            if (graph[j][i] == 1) {
                in_degree[i]++;
            }
        }
    }

    /*@
      loop assigns result[0..ptr];
      loop assigns queue[0..rear];
      loop invariant \forall integer k; 0 <= k < rear ==> queue[k] >= 0;
      loop invariant \forall integer l; 0 <= l < ptr ==> result[l] >= 0;
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        if (in_degree[i] == 0) {
            queue[rear++] = i;
            result[ptr++] = i;
        }
    }

    /*@
      loop assigns result[0..ptr];
      loop assigns queue[front..rear];
      loop assigns in_degree[0..n - 1];
      loop invariant front <= rear <= n;
      loop invariant \forall integer j; 0 <= j < front ==> \exists integer k; 0 <= k < ptr && queue[j] == result[k];
      loop variant rear - front;
    */
    while (front < rear) {
        int node = queue[front++];
        result[ptr++] = node;
        /*@
          loop assigns in_degree[0..n - 1];
          loop assigns queue[front..rear];
          loop variant n - i;
        */
        for (int i = 0; i < n; i++) {
            if (graph[node][i] == 1) {
                in_degree[i]--;
                if (in_degree[i] == 0)
                    queue[rear++] = i;
            }
        }
    }
}