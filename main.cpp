#include <limits.h>
#include <math.h>
#include <stdio.h>
#include <stdlib.h>

typedef unsigned int myfloat;

#define EXP_BIAS 0x80
#define MAX_NUMBER 8388608  // 2^23
#define MANTISSA_BITS 23
#define MASK (MAX_NUMBER - 1)

myfloat mfadd(myfloat a, myfloat b) {
  unsigned ea = a >> MANTISSA_BITS, eb = b >> MANTISSA_BITS;

  char signA = a >> 31;
  char signB = b >> 31;

  char sign = 0;

  ea &= 0xff;  // clear the sign
  eb &= 0xff;

  if (ea > eb) {
    a &= MASK;
    b = (b & MASK) >> (ea - eb);
    if ((a += b) > MASK) {
      a >>= 1;
      ++ea;
    }

    ea = (sign << 8) + ea;

    return a | ((myfloat)ea << MANTISSA_BITS);

  } else if (eb > ea) {
    b &= MASK;
    a = (a & MASK) >> (eb - ea);
    if ((b += a) > MASK) {
      b >>= 1;
      ++eb;
    }
    eb = (sign << 8) + eb;
    return b | ((myfloat)eb << MANTISSA_BITS);

  } else {
    ea++;
    ea = (sign << 8) + ea;
    return (((a & MASK) + (b & MASK)) >> 1) | (ea << MANTISSA_BITS);
  }
}

void printfraction(myfloat f) {
  char sign = f >> 31;
  int e = f >> MANTISSA_BITS;
  e &= 0xff;
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

void printfloat(const char* str, myfloat f) {
  printf("%s = ", str);
  char sign = f >> 31;
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
myfloat mfdivvv(myfloat a, myfloat b) {
  myfloat wereturn = 0;
  int d = 0;
  int newe;
  int e_d;

  do {
    char signA = a >> 31;
    char signB = b >> 31;
    unsigned ea = a >> MANTISSA_BITS, eb = b >> MANTISSA_BITS;
    a &= MASK;
    b &= MASK;
    ea &= 0xff;  // clear the sign
    eb &= 0xff;
    newe = MANTISSA_BITS + ((ea - eb) + EXP_BIAS);
    int ee = 0;
    unsigned int k = 0xffffffff / 2;  // MAXINT32 /2
    while (a < k) {
      a <<= 1;
      ++ee;
    }
    newe -= ee;

    if (a == 0 && b == 0)
      return -1;  // nan = (0xfffff...)
    else if (b == 0) {
      if (a > 0)
        return (0x80 << MANTISSA_BITS);  //+inf
      else
        return (0xff << MANTISSA_BITS);  //-inf
    }

    while ((b % 2) == 0) {
      b >>= 1;
      newe--;
    }  // hack: уменьшаем делимое

    unsigned res = a / b;

    printf("res=%d\n", res);

    while (res >= MAX_NUMBER) {
      res >>= 1;
      newe++;
    }

    d = a - b * res;

    int st2 = 0;

    // if (newe <= 142) d = 0;  // 2^-10 -> stop recursive add

    // d = 0;
    myfloat a1 = 0, a2 = 0;
    e_d = newe;
    if ((d > 0)) {
      a1 = d;
      st2 = newe;
      while (a1 < MAX_NUMBER / 2) {
        a1 <<= 1;
        st2--;
      }
      a1 = a1 | (st2 << MANTISSA_BITS);

      a2 = b;
      st2 = EXP_BIAS + MANTISSA_BITS;
      while (a2 < MAX_NUMBER / 2) {
        a2 <<= 1;
        st2--;
      }
      a2 = a2 | (st2 << MANTISSA_BITS);
    }

    a = res;

    while (a <= MAX_NUMBER / 2) {
      a <<= 1;
      newe--;
    }

    if (a == MAX_NUMBER) {
      a >>= 1;
      newe++;
    }

    char sign = (signA + signB) % 2;
    newe = (sign << 8) + newe;
    a = a | ((myfloat)(newe) << MANTISSA_BITS);

    wereturn = mfadd(wereturn, a);

    a = a1;
    b = a2;

  } while ((d > 0) && (e_d >= 142));
  return wereturn;
}

myfloat mfmul(myfloat a, myfloat b) {
  unsigned ea = a >> MANTISSA_BITS, eb = b >> MANTISSA_BITS;
  char signA = a >> 31;
  char signB = b >> 31;
  ea &= 0xff;  // clear the sign
  eb &= 0xff;
  char e = ea + eb - EXP_BIAS;
  myfloat p = ((a & MASK) * (b & MASK)) >> MANTISSA_BITS;
  char sign = (signA + signB) % 2;
  e = (sign << 8) + e;
  return p | ((myfloat)e << MANTISSA_BITS);
}

myfloat double2mf(double x);

myfloat fromInt(int x, int rateofminus10) {
  int zz = 1;
  for (int a = 0; a < rateofminus10; a++) zz *= 10;

  myfloat first, second;
  unsigned e = EXP_BIAS + MANTISSA_BITS;
  char sign = 0;
  if (x < 0) {
    sign = 1;
    x = x * (-1);
  }
  if (x == 0) first = 0;
  while (x < MAX_NUMBER / 2) x *= 2, --e;
  while (x >= MAX_NUMBER && e <= 255) x /= 2, ++e;
  e = (sign << 8) + e;

  first = x | ((myfloat)e << (MANTISSA_BITS));

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
  e = (sign << 8) + e;
  second = x | ((myfloat)e << (MANTISSA_BITS));

  return mfdivvv(first, second);
}

myfloat double2mf(double x) {
  myfloat f;
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
  e = (sign << 8) + e;
  return f | ((myfloat)e << (MANTISSA_BITS));
}

double mf2double(myfloat f) {
  char sign = (f >> 31);
  int e = f >> (MANTISSA_BITS);
  e &= 0xff;
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

    myfloat cc = (mfdivvv(double2mf(a), double2mf(b)));
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

  myfloat fnew = fromInt(5, 3);

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
