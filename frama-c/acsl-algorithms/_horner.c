/*@
  logic real poly_val2(double* coeff, integer i, integer degree, real x) =
    i > degree ? 0.0 : coeff[i] + x * poly_val2(coeff, i+1, degree, x);
*/

/*@
  requires \valid_read(coeff+(0..degree));
  ensures \result == poly_val2(coeff, 0, degree, x);
  assigns \nothing;
*/
double horner(double coeff[], int degree, double x) {
    double res = coeff[degree];
    int i = degree - 1;

    /*@
      loop assigns \nothing;
      loop invariant -1 <= i && i <= degree - 1;
      loop invariant res == poly_val2(coeff, i+1, degree, x);
      loop variant i + 1;
    */
    while (i >= 0) {
        res = coeff[i] + x * res;
        i--;
    }
    return res;
}