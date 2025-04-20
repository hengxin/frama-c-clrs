struct Node {
    int key;
    struct Node *left;
    struct Node *right;
};

/*@
  predicate BST{L}(struct Node* t) =
    t == \null || (\valid(t) &&
      (t->left == \null || t->left->key <= t->key) &&
      (t->right == \null || t->right->key >= t->key) &&
      BST(t->left) && BST(t->right));

  logic integer height(struct Node* t) =
    t == \null ? 0 : 1 + \max(height(t->left), height(t->right));
*/

/*@
  requires BST(root);
  assigns \nothing;
  ensures \result == \null || \result->key == key;
*/
struct Node *bst_search_iter(struct Node *root, int key) {
    struct Node *cur = root;
    /*@
      loop invariant cur == \null || cur->key != key;
      loop invariant BST(cur);
      loop assigns \nothing;
      loop variant height(cur);
    */
    while (cur && cur->key != key) {
        if (key < cur->key)
            cur = cur->left;
        else
            cur = cur->right;
    }
    return cur;
}