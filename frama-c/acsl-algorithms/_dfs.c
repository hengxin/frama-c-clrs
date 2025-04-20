#include <stdlib.h>
#define MAX_VERTICES 100

struct Stack {
    int items[MAX_VERTICES];
    int top;
};

/*@
  requires \valid(stack);
  assigns stack->top;
  ensures stack->top == -1;
*/
void initStack(struct Stack *stack) {
    stack->top = -1;
}

/*@
  requires \valid(stack);
  requires stack->top != -1;
  assigns \nothing;
  ensures \result == stack->items[stack->top];
*/
int peek(struct Stack *stack) {
    return stack->items[stack->top];
}

/*@
  requires \valid(stack);
  requires stack->top != -1;
  assigns stack->top;
*/
void pop(struct Stack *stack) {
    if (stack->top != -1) {
        stack->top--;
    }
}

/*@
  requires \valid(stack);
  requires stack->top < MAX_VERTICES - 1;
  assigns stack->top, stack->items[stack->top + 1];
*/
void push(struct Stack *stack, int value) {
    stack->top++;
    stack->items[stack->top] = value;
}

/*@
  requires n > 0;
  requires \valid(graph+(0..n-1));
  requires \valid(visited+(0..n-1));
  assigns visited[0..n-1];
  ensures \forall integer i; 0 <= i < n ==> visited[i] == 1;
*/
void dfs(int graph[MAX_VERTICES][MAX_VERTICES], int visited[], int n, int start) {
    struct Stack stack;
    initStack(&stack);

    /*@
      loop invariant 0 <= i <= n;
      loop invariant \forall integer j; 0 <= j < i ==> visited[j] == 0;
      loop assigns visited[0..n-1];
      loop variant n - i;
    */
    for (int i = 0; i < n; i++) {
        visited[i] = 0;
    }

    push(&stack, start);
    visited[start] = 1;

    /*@
      loop invariant stack.top >= -1;
      loop invariant \forall integer i; 0 <= i < n ==> visited[i] == 1 || visited[i] == 0;
      loop assigns stack, visited[0..n-1];
      loop variant stack.top;
    */
    while (stack.top != -1) {
        int node = peek(&stack);
        pop(&stack);

        /*@
          loop invariant 0 <= i < n;
          loop invariant visited[i] == 1 ==> visited[i] == 1;
          loop assigns visited[0..n-1];
          loop variant n - i;
        */
        for (int i = 0; i < n; i++) {
            if (graph[node][i] == 1 && visited[i] == 0) {
                visited[i] = 1;
                push(&stack, i);
            }
        }
    }
}