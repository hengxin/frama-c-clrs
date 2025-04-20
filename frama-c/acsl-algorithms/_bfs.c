#define MAX_VERTICES 100

struct Queue {
    int items[MAX_VERTICES];
    int front, rear;
};

/*@
  requires \valid(queue);
  assigns queue->front, queue->rear;
  ensures queue->front == -1 && queue->rear == -1;
*/
void initQueue(struct Queue *queue) {
    queue->front = -1;
    queue->rear = -1;
}

/*@
  requires \valid(queue);
  requires queue->front != -1;
  assigns \nothing;
  ensures \result == queue->items[queue->front];
*/
int front(struct Queue *queue) {
    return queue->items[queue->front];
}

/*@
  requires \valid(queue);
  requires queue->front != -1;
  assigns queue->front;
*/
void dequeue(struct Queue *queue) {
    if (queue->front == queue->rear) {
        queue->front = queue->rear = -1; // Queue is empty
    } else {
        queue->front++;
    }
}

/*@
  requires \valid(queue);
  requires queue->rear < MAX_VERTICES - 1;
  assigns queue->rear, queue->items[queue->rear + 1];
*/
void enqueue(struct Queue *queue, int value) {
    if (queue->rear == -1) {
        queue->front = 0;
        queue->rear = 0;
    } else {
        queue->rear++;
    }
    queue->items[queue->rear] = value;
}

/*@
  requires n > 0;
  requires \valid_read(graph+(0..n-1));
  requires \valid(dist+(0..n-1));
  requires \valid(visited+(0..n-1));
  assigns dist[0..n-1], visited[0..n-1];
  ensures \forall integer i; 0 <= i < n ==> visited[i] == 1;
  ensures \forall integer i; 0 <= i < n ==> dist[i] >= 0;
*/
void bfs(int graph[MAX_VERTICES][MAX_VERTICES], int dist[], int visited[],int n, int start) {
    struct Queue queue;
    initQueue(&queue);
    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer j; 0 <= j < i ==> visited[j] == 0 && dist[j] == -1;
      loop assigns visited[0..n-1], dist[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        visited[i] = 0;
        dist[i] = -1;
    }

    visited[start] = 1;
    dist[start] = 0;
    enqueue(&queue, start);

    /*@
      loop invariant 0 <= queue.front <= queue.rear;
      loop invariant \forall integer i; 0 <= i < n ==> visited[i] == 1 || visited[i] == 0;
      loop assigns queue.front;
      loop variant queue.rear - queue.front;
    */
    while (queue.front != -1) {
        int node = front(&queue);
        dequeue(&queue);

        /*@
          loop invariant 0 <= i < n;
          loop invariant visited[i] == 1 ==> dist[i] >= 0;
          loop assigns queue, dist[0..n-1], visited[0..n-1];
          loop variant n - i;
        */
        for (int i = 0; i < n; i++) {
            if (graph[node][i] == 1 && visited[i] == 0) { 
                visited[i] = 1;
                dist[i] = dist[node] + 1;
                enqueue(&queue, i);
            }
        }
    }
}