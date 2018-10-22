#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

typedef unsigned int pseudofloat;

#define EXP_BIAS 0x80
#define MAX_NUMBER 8388608  // 2^23
#define MANTISSA_BITS 23
#define EXP_SIZE 8
#define EXP_MASK 0xff
#define MASK (MAX_NUMBER - 1)
#define MAX_NUMBER_FIT (0xffffffff / 2)  // 2^32 - sign

pseudofloat mfadd(pseudofloat first, pseudofloat second) {
  unsigned exp_first = first >> MANTISSA_BITS,
           exp_second = second >> MANTISSA_BITS;

  char sign_first = first >> (MANTISSA_BITS + EXP_SIZE);
  char sign_second = second >> (MANTISSA_BITS + EXP_SIZE);

  char sign = 0;

  exp_first &= EXP_MASK;  // clear the sign
  exp_second &= EXP_MASK;

  if (exp_first > exp_second) {
    first &= MASK;
    second = (second & MASK) >> (exp_first - exp_second);
    if ((first += second) > MASK) {
      first >>= 1;
      ++exp_first;
    }

    exp_first = (sign << EXP_SIZE) + exp_first;
    return first | ((pseudofloat)exp_first << MANTISSA_BITS);

  } else if (exp_second > exp_first) {
    second &= MASK;
    first = (first & MASK) >> (exp_second - exp_first);
    if ((second += first) > MASK) {
      second >>= 1;
      ++exp_second;
    }
    exp_second = (sign << EXP_SIZE) + exp_second;
    return second | ((pseudofloat)exp_second << MANTISSA_BITS);

  } else {
    exp_first++;
    exp_first = (sign << EXP_SIZE) + exp_first;
    return (((first & MASK) + (second & MASK)) >> 1) |
           (exp_first << MANTISSA_BITS);
  }
}

void printfraction(pseudofloat f) {
  char sign = f >> (MANTISSA_BITS + EXP_SIZE);
  int e = f >> MANTISSA_BITS;
  e &= EXP_MASK;
  e -= EXP_BIAS;
  unsigned ff = f & MASK;
  printf("[%d %d %d] = ", sign, e, ff);
  while ((ff % 2) == 0) {
    ff >>= 1;
    e++;
  }
  e -= MANTISSA_BITS;
  printf("%d*2^%d\n", ff, e);
}

void printfloat(const char* str, pseudofloat f) {
  printf("%s = ", str);
  char sign = f >> (MANTISSA_BITS + EXP_SIZE);
  int e = f >> MANTISSA_BITS;
  e &= 0xff;
  e -= EXP_BIAS;
  unsigned ff = f & MASK;
  printf("[%d %d %d] = ", sign, e, ff);
  float fl = ff;
  if (ff == 0) {
    printf("0");
    return;
  }
  if (e > 0)
    while (e > 0) {
      fl *= 2;
      e--;
    }
  else {
    while (e < 0) {
      fl /= 2;
      e++;
    }
  }
  fl /= MAX_NUMBER;  // 2^23
  printf("%e", fl);
  printf("\n");
}

// div
pseudofloat mfdivvv(pseudofloat first, pseudofloat second) {
  pseudofloat we_return = 0;
  int reminder = 0;
  int new_exponent;
  int exponent_reminder;

  do {
    char sign_first = first >> (MANTISSA_BITS + EXP_SIZE);
    char sign_second = second >> (MANTISSA_BITS + EXP_SIZE);
    unsigned exp_first = first >> MANTISSA_BITS,
             exp_second = second >> MANTISSA_BITS;
    first &= MASK;
    second &= MASK;
    exp_first &= EXP_MASK;  // clear the sign
    exp_second &= EXP_MASK;
    new_exponent = MANTISSA_BITS + ((exp_first - exp_second) + EXP_BIAS);
    int ee = 0;
    while (first < MAX_NUMBER_FIT) {
      first <<= 1;
      ++ee;
    }
    new_exponent -= ee;

    if (first == 0 && second == 0)
      return -1;  // nan = (0xfffff...)
    else if (second == 0) {
      if (first > 0)
        return (0x80 << MANTISSA_BITS);  //+inf
      else
        return (0xff << MANTISSA_BITS);  //-inf
    }

    while ((second % 2) == 0) {
      second >>= 1;
      new_exponent--;
    }  // hack: уменьшаем делимое

    unsigned div_result = first / second;

    printf("res=%d\n", div_result);

    while (div_result >= MAX_NUMBER) {
      div_result >>= 1;
      new_exponent++;
    }

    reminder = first - second * div_result;

    int curr_exp = 0;

    pseudofloat rem_div_number1 = 0, rem_div_number2 = 0;
    exponent_reminder = new_exponent;
    // check the reminder and create a number1/number2 solution
    if ((reminder > 0)) {
      rem_div_number1 = reminder;
      curr_exp = new_exponent;
      while (rem_div_number1 < MAX_NUMBER / 2) {
        rem_div_number1 <<= 1;
        curr_exp--;
      }
      rem_div_number1 = rem_div_number1 | (curr_exp << MANTISSA_BITS);

      rem_div_number2 = second;
      curr_exp = EXP_BIAS + MANTISSA_BITS;
      while (rem_div_number2 < MAX_NUMBER / 2) {
        rem_div_number2 <<= 1;
        curr_exp--;
      }
      rem_div_number2 = rem_div_number2 | (curr_exp << MANTISSA_BITS);
    }

    first = div_result;

    while (first <= MAX_NUMBER / 2) {
      first <<= 1;
      new_exponent--;
    }

    if (first == MAX_NUMBER) {
      first >>= 1;
      new_exponent++;
    }

    char sign = (sign_first + sign_second) % 2;
    new_exponent = (sign << EXP_SIZE) + new_exponent;
    first = first | ((pseudofloat)(new_exponent) << MANTISSA_BITS);

    we_return = mfadd(we_return, first);

    first = rem_div_number1;
    second = rem_div_number2;

  } while ((reminder > 0) && (exponent_reminder >= 142));
  return we_return;
}

pseudofloat mfmul(pseudofloat a, pseudofloat b) {
  unsigned ea = a >> MANTISSA_BITS, eb = b >> MANTISSA_BITS;
  char signA = a >> (MANTISSA_BITS + EXP_SIZE);
  char signB = b >> (MANTISSA_BITS + EXP_SIZE);
  ea &= EXP_MASK;  // clear the sign
  eb &= EXP_MASK;
  char e = ea + eb - EXP_BIAS;
  pseudofloat p = ((a & MASK) * (b & MASK)) >> MANTISSA_BITS;
  char sign = (signA + signB) % 2;
  e = (sign << EXP_SIZE) + e;
  return p | ((pseudofloat)e << MANTISSA_BITS);
}

pseudofloat double2mf(double x);

pseudofloat fromInt(int x, int rateofminus10) {
  int zz = 1;
  for (int a = 0; a < rateofminus10; a++) zz *= 10;

  pseudofloat first, second;
  unsigned e = EXP_BIAS + MANTISSA_BITS;
  char sign = 0;
  if (x < 0) {
    sign = 1;
    x = x * (-1);
  }
  if (x == 0) first = 0;
  while (x < MAX_NUMBER / 2) x *= 2, --e;
  while (x >= MAX_NUMBER && e <= 255) x /= 2, ++e;
  e = (sign << EXP_SIZE) + e;

  first = x | ((pseudofloat)e << (MANTISSA_BITS));

  e = EXP_BIAS + MANTISSA_BITS;
  sign = 0;

  x = zz;
  while (x < MAX_NUMBER / 2) {
    x *= 2;
    --e;
  }
  while (x >= MAX_NUMBER && e <= 255) {
    x /= 2, ++e;
  }
  e = (sign << EXP_SIZE) + e;
  second = x | ((pseudofloat)e << (MANTISSA_BITS));

  return mfdivvv(first, second);
}

pseudofloat double2mf(double x) {
  pseudofloat f;
  unsigned e = EXP_BIAS + MANTISSA_BITS;
  char sign = 0;
  if (x < 0) {
    sign = 1;
    x = x * (-1);
  }
  if (x == 0) return 0;
  while (x < MAX_NUMBER / 2) x *= 2, --e;
  while (x >= MAX_NUMBER && e <= 255) x /= 2, ++e;
  f = x;
  e = (sign << EXP_SIZE) + e;
  return f | ((pseudofloat)e << (MANTISSA_BITS));
}

double mf2double(pseudofloat f) {
  char sign = f >> (MANTISSA_BITS + EXP_SIZE);
  int e = f >> (MANTISSA_BITS);
  e &= EXP_MASK;
  e -= EXP_BIAS;
  int ff = f & MASK;
  float fl = ff;
  if (sign == 0 && e == 0 && ff == 0) return INFINITY;
  if (sign == 1 && e == 0 && ff == 0) return -INFINITY;
  if (e == 127) return NAN;  //?

  if (e > 0)
    while (e > 0) {
      fl = fl * 2;
      e--;
    }
  else {
    while (e < 0) {
      fl = fl / 2;
      e++;
    }
  }
  fl /= MAX_NUMBER;  // 2^MANTISSA_BITS
  if (sign) fl *= -1;
  return fl;
}

/*
 *
 *  Tests
 *
 */
int main(void) {
  float a = 1;
  float b = 3;
  bool run = true;

  // printfloat("TEST 500=", double2mf(-123));

  printf("test - = %f\n", mf2double(double2mf(-123)));
  /*
  int fail = 0;

  for (int i = 0; i < 10000; i++) {
    float a = 1.0 * (rand() % 100000) / (rand() % 1000);
    float b = 1.0 * (rand() % 10) / (rand() % 1000);

    float aa = mf2double(double2mf(a));

    if (fabs(aa - a) > 0.00000001) {
      fail++;
      printf("bug got= %f  ideal=%f\n", aa, a);
    }
  }

  printf("!!! fails = %d\n", fail);

 */

  int fail = 0;
  // unsigned flo = double2mf(2.0);
  // printfloat("2^1", flo);
  // float b = 56.7787878676765666;

  /*for (i = 0; i < sizeof(testConvData) / sizeof(testConvData[0]); i++)
    printf("%e -> 0x%06lX -> %e\n",
           testConvData[i],
           (unsigned long)double2mf(testConvData[i]),
           mf2double(double2mf(testConvData[i])));*/

  // printf("300 * 5 = %e\n", mf2double(mfmul(double2mf(300),double2mf(5))));
  // printf("300 / 5 = %e  0x%06lX\n",
  // mf2double(mfdivvv(double2mf(a),double2mf(b))), (unsigned long)mf2double
  // (mfdivvv(double2mf(a),double2mf(b))));
  // printf("*1 / 3 = %e  0x%06lX\n", (float)(a / b), (unsigned long)a / b);
  // printfloat("TEST 500=", double2mf(56.7));
  // printfloat("TEST myfloat=", mfdivvv(double2mf(a), double2mf(b)));

  printf("testing ...\n");

  // int fail = 0;
  for (int i = 0; i < 1000; i++) {
    float a = 1.0 * (rand() % 100000) / (rand() % 1000);
    float b = 1.0 * (rand() % 10) / (rand() % 1000);

    // if (i < 157) continue;

    if (a == INFINITY) continue;
    if (b == INFINITY) continue;

    float c = a / b;
    // float c = a + b;

    pseudofloat cc = (mfdivvv(double2mf(a), double2mf(b)));
    // myfloat cc = (mfadd(double2mf(a), double2mf(b)));

    float c1 = mf2double(cc);

    printfloat("a=", double2mf(a));
    printfloat("b=", double2mf(b));

    printfloat("our result", cc);
    double diff = fabs(c - c1);
    printfloat("diff=", double2mf(diff));

    printf("testing %f / %f = %e vs %e -> diff=%f....", a, b, c, c1, diff);

    printfloat("etalon", double2mf(c));

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

  pseudofloat fnew = fromInt(5, 3);

  printfraction(fnew);

  printfraction(double2mf(-0.125));

  return 0;
}

/*

#define DIGITS 256
#define EPS \
  20  // константа устанавливающая границы приближенности вычисления корня

#include <stdio.h>
#include <stdlib.h>

using namespace std;
typedef signed int __int32_t;

class Fixed {
  signed int x;

  Fixed(signed int a) { x = a; }

 public:
  Fixed() { x = 0; }
  static Fixed fromInt(signed int val) { return Fixed(val * DIGITS); }
  static Fixed fromFloat(float val) {
    return Fixed((signed int)(val * DIGITS));
  }
  float fixed2float() { return ((float)x) / DIGITS; }
  Fixed sum(Fixed a, Fixed b) { return Fixed(a.x + b.x); }
  Fixed diff(Fixed a, Fixed b) { return Fixed(a.x - b.x); }
  static Fixed mul(Fixed a, Fixed b) {
    signed int c = a.x * b.x;
    if (c / b.x != a.x) {
      // Overflow!
      signed int i1 = a.x / DIGITS;
      signed int i2 = b.x / DIGITS;
      signed int f1 = (a.x & (DIGITS - 1));
      signed int f2 = (b.x & (DIGITS - 1));
      return Fixed((i1 * i2) * DIGITS + (f1 * f2) / DIGITS + i1 * f2 + i2 *
f1); } else { return Fixed(c / DIGITS);
    }
  }
  static Fixed div(Fixed a, Fixed b) {
    if (a.x > (1 << 21)) {
      // Overflow!
      signed int i = a.x / DIGITS;
      signed int f = (a.x & (DIGITS - 1));
      return Fixed(((i * DIGITS) / b.x) * DIGITS + (f * DIGITS) / b.x);
    } else {
      return Fixed((a.x * DIGITS) / b.x);
    }
  }
  Fixed sqrt(Fixed k) {
    Fixed tmp(0);
    tmp.x = k.x / 2;
    signed int min = 0;
    signed int max = k.x;
    Fixed quick(0);
    do {
      tmp.x = (min + max) / 2;
      quick = Fixed::mul(tmp, tmp);
      if (abs(quick.x - k.x) < EPS) return Fixed(tmp);
      if (quick.x > k.x) {
        max = tmp.x;
      } else {
        min = tmp.x;
      }
    } while (true);
  }
};

int main() {
  Fixed me = Fixed::fromFloat(633.33);
  Fixed me2 = Fixed::fromFloat(3.2);

  printf("%f\n", Fixed::div(me, me2).fixed2float());
}


*/
