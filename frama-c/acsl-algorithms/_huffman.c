#include <stdlib.h>

struct Node {
    char ch;
    int freq;
    struct Node *left;
    struct Node *right;
};

/*@
  requires freq > 0;
  assigns \nothing;
  ensures \result != \null;
  ensures \result->ch == ch;
  ensures \result->freq == freq;
  ensures \result->left == left && \result->right == right;
*/
struct Node *newNode(char ch, int freq, struct Node *left, struct Node *right) {
    struct Node *node = (struct Node *)malloc(sizeof(struct Node));
    node->ch = ch;
    node->freq = freq;
    node->left = left;
    node->right = right;
    return node;
}

/*@
  requires n > 0;
  requires \valid_read(arr+(0..n-1));
  assigns \nothing;
  ensures \result != \null;
*/
struct Node *buildHuffman(struct Node *arr[], int n) {
    int i;
    /*@
      loop invariant n >= 1;
      loop assigns \nothing;
      loop variant n;
    */
    while (n > 1) {
        int min1 = 0;
        /*@
          loop invariant 1 <= i <= n;
          loop invariant 0 <= min1 < n;
          loop assigns min1;
          loop variant n - i;
        */
        for (i = 1; i < n; i++) {
            if (arr[i]->freq < arr[min1]->freq)
                min1 = i;
        }
        struct Node *node1 = arr[min1];
        arr[min1] = arr[n - 1];
        n--;

        int min2 = 0;
        /*@
          loop invariant 1 <= i <= n;
          loop invariant 0 <= min2 < n;
          loop assigns min2;
          loop variant n - i;
        */
        for (i = 1; i < n; i++) {
            if (arr[i]->freq < arr[min2]->freq)
                min2 = i;
        }
        struct Node *node2 = arr[min2];
        struct Node *merged = newNode('\0', node1->freq + node2->freq, node1, node2);
        arr[min2] = merged;
    }
    return arr[0];
}