/*
@brief Floating point calculations implementation in plain C for integer
processors
@author Sergey Staroletov serg_soft@mail.ru
@license GNU GPL
*/

#include <math.h>
#include <stdio.h>
#include <stdlib.h>

#include "fpu.h"

#define EXP_BIAS 0x80
#define MAX_NUMBER 8388608  // 2^23
#define MANTISSA_BITS 23
#define EXP_SIZE 8
#define EXP_MASK 0xff
#define MASK (MAX_NUMBER - 1)
#define MAX_NUMBER_FIT (1073741824)  // 2^32 - sign

pseudofloat subTwoFloat(pseudofloat first, pseudofloat second, char sign) {
  int exp_first = first >> MANTISSA_BITS, exp_second = second >> MANTISSA_BITS;

  if (exp_first == 0) exp_first = EXP_BIAS;
  if (exp_second == 0) exp_second = EXP_BIAS;

  exp_first &= EXP_MASK;  // clear the sign
  exp_second &= EXP_MASK;

  if (exp_first - exp_second >= 32) {
    // first number too mush bigger than next one
    return first | (sign >> (MANTISSA_BITS + EXP_SIZE));
  }
  if (exp_second - exp_first >= 32) {
    // second number too mush bigger than next one
    return second | (sign >> (MANTISSA_BITS + EXP_SIZE));
  }

  first &= MASK;
  second &= MASK;

  int res = 0;
  pseudofloat ret = 0;
  int exp;

  if (exp_first > exp_second && first != 0) {
    exp = exp_first;
    res = first - (second >> (exp_first - exp_second));
    if (res < 0) {
      res = -res;
      sign = !sign;
    }
  } else {
    exp = exp_second;
    res = (first >> (exp_second - exp_first)) - second;
    if (res < 0) {
      res = -res;
      sign = !sign;
    }
  }

  if (res == 0) return 0;
  while (res < MAX_NUMBER / 2) {
    res <<= 1;
    exp--;
  }
  ret = res;

  exp = (sign << EXP_SIZE) + exp;

  return ret | ((pseudofloat)exp << MANTISSA_BITS);
}

pseudofloat addTwoFloat(pseudofloat first, pseudofloat second, char sign) {
  int exp_first = first >> MANTISSA_BITS, exp_second = second >> MANTISSA_BITS;

  exp_first &= EXP_MASK;
  exp_second &= EXP_MASK;

  if (exp_first - exp_second >= 32) {
    // first number too mush bigger than next one
    return first | (sign >> (MANTISSA_BITS + EXP_SIZE));
  }
  if (exp_second - exp_first >= 32) {
    // second number too mush bigger than next one
    return second | (sign >> (MANTISSA_BITS + EXP_SIZE));
  }

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
    pseudofloat res = (((first & MASK) + (second & MASK)) >> 1);

    exp_first = (sign << EXP_SIZE) + exp_first;
    return res | (exp_first << MANTISSA_BITS);
  }
}

pseudofloat addFloat(pseudofloat first, pseudofloat second) {
  char sign_first = first >> (MANTISSA_BITS + EXP_SIZE);
  char sign_second = second >> (MANTISSA_BITS + EXP_SIZE);

  if (sign_first == 0 && sign_second == 0)  // A+B
    return addTwoFloat(first, second, 0);

  if (sign_first == 1 && sign_second == 1) {  //-A-B=>-(A+B)
    return addTwoFloat(first, second, 1);
  }

  if (sign_first == 0 && sign_second == 1) {  // A-B
    return subTwoFloat(first, second, 0);
  }

  if (sign_first == 1 && sign_second == 0) {  // -A+B
    return subTwoFloat(second, first, 0);
  }

  return 0;
}

pseudofloat subFloat(pseudofloat first, pseudofloat second) {
  char sign_first = first >> (MANTISSA_BITS + EXP_SIZE);
  char sign_second = second >> (MANTISSA_BITS + EXP_SIZE);

  if (sign_first == 0 && sign_second == 0)  // A-B
    return subTwoFloat(first, second, 0);

  if (sign_first == 1 && sign_second == 1) {  //-A--B=>-A+B=>B-A
    return subTwoFloat(second, first, 0);
  }

  if (sign_first == 0 && sign_second == 1) {  // A--B=>A+B
    return addTwoFloat(first, second, 0);
  }

  if (sign_first == 1 && sign_second == 0) {  // -A-B=> -(A+B)
    return addTwoFloat(first, second, 1);
  }
  return 0;
}

void printFloatRepresentation(pseudofloat f) {
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

void printFloatAsFloat(const char *str, pseudofloat f) {
  printf("%s = ", str);
  char sign = f >> (MANTISSA_BITS + EXP_SIZE);
  int e = f >> MANTISSA_BITS;
  e &= EXP_MASK;
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
  if (sign) printf("-");
  printf("%e", fl);
  printf("\n");
  fflush(stdin);
}

// TODO: check the accuracy again
pseudofloat divFloat(pseudofloat first, pseudofloat second) {
  pseudofloat we_return = 0;
  int reminder = 0;
  int new_exponent;
  int exponent_reminder;
  char sign_first = first >> (MANTISSA_BITS + EXP_SIZE);
  char sign_second = second >> (MANTISSA_BITS + EXP_SIZE);

  if (first == 0 && second == 0)
    return -1;  // nan = (0xfffff...)
  else if (second == 0) {
    if (first > 0)
      return (0x80 << MANTISSA_BITS);  //+inf
    else
      return (0xff << MANTISSA_BITS);  //-inf
  }

  do {
    int exp_first = first >> MANTISSA_BITS,
        exp_second = second >> MANTISSA_BITS;
    first &= MASK;
    second &= MASK;
    exp_first &= EXP_MASK;  // clear the sign
    exp_second &= EXP_MASK;
    new_exponent = MANTISSA_BITS + ((exp_first - exp_second) + EXP_BIAS);
    int ee = 0;
    if (first > 0)
      while (first < MAX_NUMBER_FIT) {
        first <<= 1;
        ++ee;
      }
    else
      return we_return;

    new_exponent -= ee;

    if (second > 0)
      while ((second % 2) == 0) {
        second >>= 1;
        new_exponent--;
      }  // hack: уменьшаем делимое

    unsigned div_result = first / second;
    printf("res=%d\n", div_result);
    reminder = first - second * div_result;

    while (div_result >= MAX_NUMBER) {
      div_result >>= 1;
      new_exponent++;
    }

    int curr_exp = 0;

    pseudofloat rem_div_number1 = 0, rem_div_number2 = 0;
    exponent_reminder = new_exponent;
    // check the reminder and create a number1/number2 solution
    if ((reminder > 0)) {
      rem_div_number1 = reminder;
      curr_exp = new_exponent;
      while (rem_div_number1 >= MAX_NUMBER) {
        rem_div_number1 >>= 1;
        curr_exp++;
      }
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

    if (first > 0)
      while (first < MAX_NUMBER / 2) {
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
    // print_pseudo_as_float("addind to div sum: ", first);
    we_return = addFloat(we_return, first);
    // print_pseudo_as_float("got current div: ", we_return);
    if ((new_exponent == EXP_BIAS + MANTISSA_BITS - 1) ||
        (new_exponent == EXP_BIAS - (MANTISSA_BITS - 1)))
      break;
    first = rem_div_number1;
    second = rem_div_number2;
    // continue to divide, get the reminder and add it to the result
  } while ((reminder > 0) && (exponent_reminder >= 142));

  return we_return;
}

pseudofloat mulFloat(pseudofloat a, pseudofloat b) {
  unsigned ea = a >> MANTISSA_BITS, eb = b >> MANTISSA_BITS;
  char signA = a >> (MANTISSA_BITS + EXP_SIZE);
  char signB = b >> (MANTISSA_BITS + EXP_SIZE);
  ea &= EXP_MASK;  // clear the sign
  eb &= EXP_MASK;
  int e = ea + eb - EXP_BIAS;
  a &= MASK;
  b &= MASK;

  pseudofloat p =
      ((a >> 8) * (b >> 8)) >> (MANTISSA_BITS - 16);  // or we overflow it

  char sign = (signA + signB) % 2;

  e = (sign << EXP_SIZE) + e;
  return p | ((pseudofloat)e << MANTISSA_BITS);
}

/* @param x - number
 * @param rate_of_minus_10 - power of 10  to divide the number
 * @return x * pow(10, -rate_of_minus10)
 */
pseudofloat floatFromInt(int x, int rate_of_minus10) {
  int pow_of_10 = 1;
  for (int i = 0; i < rate_of_minus10; i++) pow_of_10 *= 10;

  pseudofloat first, second;
  int e = EXP_BIAS + MANTISSA_BITS;
  char sign = 0;
  if (x < 0) {
    sign = 1;
    x = -x;
  }
  if (x == 0) first = 0;
  while (x < MAX_NUMBER / 2) x *= 2, --e;
  while (x >= MAX_NUMBER && e <= 255) x /= 2, ++e;

  first = x;

  e = (sign << EXP_SIZE) + e;

  first = first | ((pseudofloat)e << (MANTISSA_BITS));

  e = EXP_BIAS + MANTISSA_BITS;
  sign = 0;

  x = pow_of_10;
  while (x < MAX_NUMBER / 2) {
    x *= 2;
    --e;
  }
  while (x >= MAX_NUMBER && e <= 255) {
    x /= 2, ++e;
  }

  second = x;

  e = (sign << EXP_SIZE) + e;
  second = second | ((pseudofloat)e << (MANTISSA_BITS));

  return divFloat(first, second);
}

pseudofloat realDouble2Float(double x) {
  pseudofloat f;
  int e = EXP_BIAS + MANTISSA_BITS;
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

double float2RealDouble(pseudofloat f) {
  char sign = f >> (MANTISSA_BITS + EXP_SIZE);
  int e = f >> (MANTISSA_BITS);
  e &= EXP_MASK;
  e -= EXP_BIAS;
  int ff = f & MASK;
  float fl = ff;
  if (sign == 0 && e == 0 && ff == 0) return INFINITY;
  if (sign == 1 && e == 0 && ff == 0) return -INFINITY;
  // if (e == 127) return NAN;  //?

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

pseudofloat absFloat(pseudofloat x) {
  char sign = x >> (MANTISSA_BITS + EXP_SIZE);
  int e = x >> (MANTISSA_BITS);
  e &= EXP_MASK;
  int ff = x & MASK;

  e = (sign << EXP_SIZE) + e;

  return ff | ((pseudofloat)e << (MANTISSA_BITS));
}

pseudofloat sinus(pseudofloat x) {
  printFloatAsFloat("current x", x);
  int i = 1;
  pseudofloat current_sin = x;
  pseudofloat seq_n = floatFromInt(1, 0);

  pseudofloat fact = seq_n;
  pseudofloat pow = x;
  pseudofloat p00000001 = floatFromInt(1, 5);
  pseudofloat xx = mulFloat(x, x);
  printFloatAsFloat("xx = ", xx);

  xx = subFloat(0, xx);
  printFloatAsFloat("1-xx = ", xx);

  /// sinx = x - x^3/3! + x^5/5! ...
  while ((absFloat(seq_n) > p00000001) && i < 10) {
    // while (i < 10) {
    pseudofloat fac_part_new = floatFromInt(((2 * i) * (2 * i + 1)), 0);
    fact = mulFloat(fact, fac_part_new);
    printFloatAsFloat("fact part = ", fact);

    pow = mulFloat(xx, pow);
    printFloatAsFloat("pow part = ", pow);

    seq_n = divFloat(pow, fact);
    printf("%d", i);
    printFloatAsFloat(" -> seq[i]  = ", seq_n);

    printFloatAsFloat("---- old sin = ", current_sin);

    current_sin = addFloat(current_sin, seq_n);

    printFloatAsFloat(" -> current sin = ", current_sin);
    i++;
  }

  printFloatAsFloat(":: resturn sin = ", current_sin);

  return current_sin;
}

pseudofloat cosinus(pseudofloat x) {
  pseudofloat demie_pi = floatFromInt(3141592 / 2, 6);
  pseudofloat x1 = subFloat(demie_pi, x);
  return sinus(x1);
}
