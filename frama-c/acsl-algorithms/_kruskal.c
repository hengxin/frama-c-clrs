#define MAX_VERTICES 100
#define MAX_EDGES 1000

struct Edge {
    int u, v, weight;
};

/*@
  requires n > 0;
  requires \valid(parent+(0..n-1)) && \valid(rank+(0..n-1));
  assigns parent[0..n-1], rank[0..n-1];
  ensures \forall integer i; 0 <= i < n ==> parent[i] == i && rank[i] == 0;
*/
void makeSet(int parent[], int rank[], int n) {
    /*@
        loop invariant 0 <= i <= n;
        loop assigns parent[i], rank[i];
        loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        parent[i] = i;
        rank[i] = 0;
    }
}

/*@
    requires parent != \null;
    requires \exists integer i; 0 <= i < n ==> parent[i] == i;
    assigns parent[0..n-1];
    ensures \result == parent[x];
*/
int find(int parent[], int x, int n) {
    if (x != parent[x]) {
        parent[x] = find(parent, parent[x], n);
    }
    return parent[x];
}

/*@
  requires parent != \null && rank != \null;
  requires 0 <= x < n && 0 <= y < n;
  assigns parent[0..n-1], rank[0..n-1];
  ensures \result == 1 <==> parent[x] != parent[y];
*/
int unionSets(int parent[], int rank[], int x, int y, int n) {
    int rootX = find(parent, x, n);
    int rootY = find(parent, y, n);
    if (rootX != rootY) {
        if (rank[rootX] > rank[rootY]) {
            parent[rootY] = rootX;
        } else if (rank[rootX] < rank[rootY]) {
            parent[rootX] = rootY;
        } else {
            parent[rootY] = rootX;
            rank[rootX]++;
        }
        return 1;
    }
    return 0;
}

/*@
    requires n > 0 && e > 0;
    requires \valid(edges+(0..e-1));
    requires \valid(mst+(0..n-1));
    assigns mst[0..n-1], edges[0..e-1];
    ensures \forall integer i; 0 <= i < n ==> mst[i] >= 0;
*/
int kruskal(int n, int e, struct Edge edges[], int mst[], int parent[], int rank[]) {
    makeSet(parent, rank, n);
    int mstWeight = 0, edgeCount = 0;

    /*@
        loop invariant 0 <= i <= e;
        loop invariant \forall integer j; 0 <= j < i ==> edges[j].weight <= edges[i].weight;
        loop assigns edges[0..e-1];
        loop variant e - i;
    */
    for (int i = 0; i < e; i++) {
        /*@
            loop invariant i + 1 <= j <=e;
            loop assigns edges[0..e-1];
            loop variant e - j;
        */
        for (int j = i + 1; j < e; j++) {
            if (edges[i].weight > edges[j].weight) {
                struct Edge temp = edges[i];
                edges[i] = edges[j];
                edges[j] = temp;
            }
        }
    }

    /*@
        loop invariant edgeCount >= 0 && edgeCount <= n - 1;
        loop invariant \forall integer i; 0 <= i < edgeCount ==> mst[i] == edges[i].u;
        loop assigns mst[0..n-1];
        loop variant n - edgeCount;
    */
    for (int i = 0; i < e && edgeCount < n - 1; i++) {
        struct Edge edge = edges[i];
        if (unionSets(parent, rank, edge.u, edge.v, n)) {
            mst[edgeCount++] = edge.u;
            mstWeight += edge.weight;
        }
    }

    return mstWeight;
}