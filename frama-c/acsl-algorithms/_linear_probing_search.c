/*@
  requires \valid(table+(0..size-1));
  requires size > 0;
  assigns table[0..size-1];
  ensures \result == -1 || (\result >= 0 && \result < size);
  ensures \result != -1 ==> table[\result] == key;
  ensures \result == -1 ==> (\forall integer j; 0 <= j < size ==> table[j] == \old(table[j]));
*/
int linear_probing_insert(int table[], int size, int key) {
    int start = key % size;
    int index = start;
    int count = 0;
    /*@
      loop invariant index == (start + count) % size;
      loop invariant (\forall integer i; 0 <= i < count ==> table[(start + i) % size] != -1);
      loop assigns index, count;
      loop variant size - count;
    */
    while (table[index] != -1 && count < size) {
        index = (index + 1) % size;
        count++;
    }
    if (count == size) {
        return -1;
    }
    table[index] = key;
    return index;
}

/*@
  requires \valid_read(table+(0..size-1));
  requires size > 0;
  assigns \nothing;
  ensures \result == -1 <==> (\forall integer j; 0 <= j < size ==> table[j] != key);
  ensures \result != -1 ==> (0 <= \result < size && table[\result] == key);
*/
int linear_probing_search(int table[], int size, int key) {
    int start = key % size;
    int index = start;
    int count = 0;
    /*@
      loop invariant index == (start + count) % size;
      loop invariant (\forall integer i; 0 <= i < count ==> table[(start + i) % size] != key);
      loop assigns index, count;
      loop variant size - count;
    */
    while (table[index] != key && count < size) {
        index = (index + 1) % size;
        count++;
    }
    if (count == size) {
        return -1;
    }
    return index;
}