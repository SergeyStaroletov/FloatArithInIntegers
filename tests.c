#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include <fpu.h>


/*
 *
 *  Tests
 *
 */
int main(void) {
  printf("test - = %f\n", pseudo2double(double2pseudo(-123)));

  int fail = 0;

  printf("testing ...\n");

  for (int i = 0; i < 1000; i++) {
    float a = 1.0 * (rand() % 100000) / (rand() % 1000);
    float b = 1.0 * (rand() % 100000) / (rand() % 1000);

    // if (i < 157) continue;

    if (a == INFINITY) continue;
    if (b == INFINITY) continue;

    // float c = a / b;
    float c = b - a;
    // float c = a * b;

    // pseudofloat cc = (div_pseudo(double2pseudo(a), double2pseudo(b)));
    pseudofloat cc = sub_two_pseudo(double2pseudo(b), double2pseudo(a), 0);

    // myfloat cc = (mfadd(double2mf(a), double2mf(b)));

    float c1 = pseudo2double(cc);

    print_pseudo_as_float("a=", double2pseudo(a));
    print_pseudo_as_float("b=", double2pseudo(b));

    print_pseudo_as_float("our result", cc);
    double diff = fabs(c - c1);
    print_pseudo_as_float("diff=", double2pseudo(diff));

    printf("testing %f / %f = %e vs %e -> diff=%f....", a, b, c, c1, diff);

    print_pseudo_as_float("etalon", double2pseudo(c));

    if (diff < 0.126 || isnan(diff))
      printf("passed!\n");
    else {
      printf("FAILED!\n");
      // printfloat("-",cc);
      // mfshow(cc);
      fail++;
    }
  }

  // printf("500 + 3 = %e\n", mf2double(mfadd(double2mf(500),double2mf(0))));
  // printf("1e18 * 1e-18 = %e\n",
  // mf2double(mfmul(double2mf(1e18),double2mf(1e-18)))); printf("1e-18 +
  // 2e-18 = %e\n", mf2double(mfadd(double2mf(1e-18),double2mf(2e-18))));
  // printf("1e-16 + 1e-18 = %e\n",
  // mf2double(mfadd(double2mf(1e-16),double2mf(1e-18))));

  printf("\n %d failed\n", fail);

  pseudofloat fnew = pseudo_from_int(20, 0);
  print_pseudo_representation(fnew);
  print_pseudo_representation(double2pseudo(-0.125));

  // for (float x = -3.14; x <= 3.14; x += 0.01) {
  //  printf("x = %f  sin(x) = %f    we_sin(x) = %f\n", x, sin(x), SIN(x));
  // }

  return 0;
}
