#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "fpu.h"

#include "testfpu.h"

#define EPS 0.126

void TestFPU::testMul() {
  // QSKIP("skipping, comment me to run this test");

  printf("testing mul...\n");

  int fail = 0;
  for (int i = 0; i < 100; i++) {
    float a = 1.0 * (rand() % 100000) / (rand() % 1000);
    float b = 1.0 * (rand() % 100) / (rand() % 1000);
    if (rand() % 2 == 0) a = -a;
    if (rand() % 2 == 0) b = -b;

    float c_real = a * b;

    pseudofloat c_our = (mulFloat(realDouble2Float(a), realDouble2Float(b)));

    float c_our_float = float2RealDouble(c_our);

    printFloatAsFloat("a=", realDouble2Float(a));
    printFloatAsFloat("b=", realDouble2Float(b));

    printFloatAsFloat("our result", c_our);
    double diff = fabs(c_real - c_our_float);
    printFloatAsFloat("diff=", realDouble2Float(diff));
    printf("testing %f / %f = %e vs %e -> diff=%f....", a, b, c_real,
           c_our_float, diff);
    printFloatAsFloat("etalon", realDouble2Float(c_real));
    if (diff < EPS || isnan(diff))
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
  QSKIP("skipping, comment me to run this test");

  printf("testing div...\n");

  int fail = 0;
  for (int i = 0; i < 100; i++) {
    float a = 1.0 * (rand() % 100000) / (rand() % 1000);
    float b = 1.0 * (rand() % 100) / (rand() % 1000);
    if (rand() % 2 == 0) a = -a;
    if (rand() % 2 == 0) b = -b;

    float c_real = a / b;

    pseudofloat c_our = (divFloat(realDouble2Float(a), realDouble2Float(b)));

    float c_our_float = float2RealDouble(c_our);

    printFloatAsFloat("a=", realDouble2Float(a));
    printFloatAsFloat("b=", realDouble2Float(b));

    printFloatAsFloat("our result", c_our);
    double diff = fabs(c_real - c_our_float);
    printFloatAsFloat("diff=", realDouble2Float(diff));
    printf("testing %f / %f = %e vs %e -> diff=%f....", a, b, c_real,
           c_our_float, diff);
    printFloatAsFloat("etalon", realDouble2Float(c_real));
    if (diff < EPS || isnan(diff))
      printf("passed!\n");
    else {
      printf("FAILED!\n");
      fail++;
    }

    QVERIFY(diff < EPS || isnan(diff));
  }
  printf("%d divs failed\n", fail);

  QVERIFY(fail == 0);
}

void TestFPU::testAdd() {
  // QSKIP("skipping, comment me to run this test");

  printf("testing add...\n");

  int fail = 0;
  for (int i = 0; i < 10000; i++) {
    float a = 1.0 * (rand() % 100000) / (rand() % 100);
    float b = 1.0 * (rand() % 10) / (rand() % 100000);
    if (rand() % 2 == 0) a = -a;
    if (rand() % 2 == 0) b = -b;

    if (a == 0 && b == 0) continue;      //!!
    if (isinf(a) || isinf(b)) continue;  //!!

    float c_real = a + b;

    pseudofloat c_our = (addFloat(realDouble2Float(a), realDouble2Float(b)));

    float c_our_float = float2RealDouble(c_our);

    printFloatAsFloat("a=", realDouble2Float(a));
    printFloatAsFloat("b=", realDouble2Float(b));

    printFloatAsFloat("our result", c_our);
    double diff = fabs(c_real - c_our_float);
    printFloatAsFloat("diff=", realDouble2Float(diff));
    printf("testing %f / %f = %e vs %e -> diff=%f....", a, b, c_real,
           c_our_float, diff);
    printFloatAsFloat("etalon", realDouble2Float(c_real));
    if (diff < 0.01 || isnan(diff))
      printf("passed!\n");
    else {
      printf("FAILED!\n");
      fail++;
    }

    QVERIFY(diff < EPS || isnan(diff));
  }
  printf("%d adds failed\n", fail);

  QVERIFY(fail == 0);
}

void TestFPU::testSub() {
  // QSKIP("skipping, comment me to run this test");

  printf("testing sub...\n");

  int fail = 0;
  for (int i = 0; i < 1000; i++) {
    float a = 1.0 * (rand() % 10000) / (rand() % 1000);
    float b = 1.0 * (rand() % 100000) / (rand() % 10);
    if (rand() % 2 == 0) a = -a;
    if (rand() % 2 == 0) b = -b;

    if (a == 0 && b == 0) continue;      //!!
    if (isinf(a) || isinf(b)) continue;  //!!
    float c_real = a - b;

    pseudofloat c_our = (subFloat(realDouble2Float(a), realDouble2Float(b)));

    float c_our_real = float2RealDouble(c_our);

    printFloatAsFloat("a=", realDouble2Float(a));
    printFloatAsFloat("b=", realDouble2Float(b));

    printFloatAsFloat("our result", c_our);
    double diff = fabs(c_real - c_our_real);
    printFloatAsFloat("diff=", realDouble2Float(diff));
    printf("testing %f / %f = %e vs %e -> diff=%f....", a, b, c_real,
           c_our_real, diff);
    printFloatAsFloat("etalon", realDouble2Float(c_real));
    if (diff < EPS || isnan(diff))
      printf("passed!\n");
    else {
      printf("FAILED!\n");
      fail++;
    }

    QVERIFY(diff < EPS || isnan(diff));
  }
  printf("%d subs failed\n", fail);

  QVERIFY(fail == 0);
}

void TestFPU::testSin() {
  // QSKIP("skipping, comment me to run this test");

  for (float x = -3.1415; x <= 3.1415; x += 0.01) {
    printf("TEST x = %f\n", x);

    float actual = float2RealDouble(sinus(realDouble2Float(x)));
    float etalon = sin(x);

    float diff = fabs(actual - etalon);

    printf("x = %f  sin(x) = %f    we_sin(x) = %f\n", x, etalon, actual);

    QVERIFY(diff < 0.01);
  }
}

void TestFPU::testCos() {
  // QSKIP("skipping, comment me to run this test");

  for (float x = -3.1415; x <= 3.1415; x += 0.01) {
    printf("TEST x = %f\n", x);

    float actual = float2RealDouble(cosinus(realDouble2Float(x)));
    float etalon = cos(x);

    float diff = fabs(actual - etalon);

    printf("x = %f  cos(x) = %f    we_cos(x) = %f\n", x, etalon, actual);

    QVERIFY(diff < 0.01);
  }
}

QTEST_MAIN(TestFPU)
