#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "fpu.h"

#include "testfpu.h"

void TestFPU::testMul() {
  QSKIP("after");

  printf("testing mul...\n");

  int fail = 0;
  for (int i = 0; i < 100; i++) {
    float a = 1.0 * (rand() % 100000) / (rand() % 1000);
    float b = 1.0 * (rand() % 100) / (rand() % 1000);
    if (rand() % 2 == 0) a = -a;
    if (rand() % 2 == 0) b = -b;

    float c = a * b;

    pseudofloat cc = (mul_pseudo(double2pseudo(a), double2pseudo(b)));

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
      fail++;
    }
  }

  printf("%d muls failed\n", fail);
  QVERIFY(fail == 0);
}

void TestFPU::testDiv() {
  QSKIP("after");

  printf("testing div...\n");

  int fail = 0;
  for (int i = 0; i < 100; i++) {
    float a = 1.0 * (rand() % 100000) / (rand() % 1000);
    float b = 1.0 * (rand() % 100) / (rand() % 1000);
    if (rand() % 2 == 0) a = -a;
    if (rand() % 2 == 0) b = -b;

    float c = a / b;

    pseudofloat cc = (div_pseudo(double2pseudo(a), double2pseudo(b)));

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
      fail++;
    }

    QVERIFY(diff < 0.126 || isnan(diff));
  }
  printf("%d divs failed\n", fail);

  QVERIFY(fail == 0);
}

void TestFPU::testAdd() {
  // QSKIP("after");

  printf("testing add...\n");

  int fail = 0;
  for (int i = 0; i < 10000; i++) {
    float a = 1.0 * (rand() % 100000) / (rand() % 100);
    float b = 1.0 * (rand() % 10) / (rand() % 100000);
    if (rand() % 2 == 0) a = -a;
    if (rand() % 2 == 0) b = -b;

    if (a == 0 && b == 0) continue;      //!!
    if (isinf(a) || isinf(b)) continue;  //!!

    float c = a + b;

    if (a == -97408) {
      a = a;
    }
    pseudofloat cc = (add_pseudo(double2pseudo(a), double2pseudo(b)));

    float c1 = pseudo2double(cc);

    print_pseudo_as_float("a=", double2pseudo(a));
    print_pseudo_as_float("b=", double2pseudo(b));

    print_pseudo_as_float("our result", cc);
    double diff = fabs(c - c1);
    print_pseudo_as_float("diff=", double2pseudo(diff));
    printf("testing %f / %f = %e vs %e -> diff=%f....", a, b, c, c1, diff);
    print_pseudo_as_float("etalon", double2pseudo(c));
    if (diff < 0.01 || isnan(diff))
      printf("passed!\n");
    else {
      printf("FAILED!\n");
      fail++;
    }

    QVERIFY(diff < 0.126 || isnan(diff));
  }
  printf("%d adds failed\n", fail);

  QVERIFY(fail == 0);
}

void TestFPU::testSub() {
  QSKIP("after");

  printf("testing sub...\n");

  int fail = 0;
  for (int i = 0; i < 1000; i++) {
    float a = 1.0 * (rand() % 10000) / (rand() % 1000);
    float b = 1.0 * (rand() % 100000) / (rand() % 10);
    if (rand() % 2 == 0) a = -a;
    if (rand() % 2 == 0) b = -b;

    if (a == 0 && b == 0) continue;      //!!
    if (isinf(a) || isinf(b)) continue;  //!!
    float c = a - b;

    pseudofloat cc = (sub_pseudo(double2pseudo(a), double2pseudo(b)));

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
      fail++;
    }

    QVERIFY(diff < 0.126 || isnan(diff));
  }
  printf("%d subs failed\n", fail);

  QVERIFY(fail == 0);
}

void TestFPU::testSin() {
  QSKIP("after");

  // for (float x = -2.46; x <= 3.14; x += 0.01) {
  for (float x = -2.4615; x <= 3.1415; x += 0.01) {
    printf("TEST x = %f\n", x);

    float actual = pseudo2double(Sin(double2pseudo(x)));
    float etalon = sin(x);

    float diff = fabs(actual - etalon);

    printf("x = %f  sin(x) = %f    we_sin(x) = %f\n", x, etalon, actual);

    QVERIFY(diff < 0.01);
  }
}

QTEST_MAIN(TestFPU)
