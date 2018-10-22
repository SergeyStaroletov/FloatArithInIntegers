
/*
@brief Floating point calculations implementation in Promela
@autor Sergey Staroletov serg_soft@mail.ru
@license GNU GPL
*/
#define EXP_BIAS 128
#define MAX_NUMBER 8388608  // 2^23
#define MANTISSA_BITS 23
#define EXP_SIZE 8
#define EXP_MASK 255
#define MASK (MAX_NUMBER - 1)
#define MAX_NUMBER_FIT 2147483647  // 2^32 - sign



inline print_pseudo_representation(f) {
  byte sign = f >> (MANTISSA_BITS + EXP_SIZE);
  int e = f >> MANTISSA_BITS;
  e = e & EXP_MASK;
  e = e - EXP_BIAS;
  int ff = f & MASK;
  printf("[%d %d %d] = ", sign, e, ff);
  do 
    ::((ff % 2) == 0) -> {
        ff = ff >> 1;
        e++; 
    }
    ::else -> break;
  od
  e = e - MANTISSA_BITS;
  printf("%d*2^%d\n", ff, e);
}


inline mul_pseudo(result, a, b) {
  int ea = a >> MANTISSA_BITS, eb = b >> MANTISSA_BITS;
  byte signA = a >> (MANTISSA_BITS + EXP_SIZE);
  byte signB = b >> (MANTISSA_BITS + EXP_SIZE);
  ea = ea & EXP_MASK;  // clear the sign
  eb = eb & EXP_MASK;
  byte e = ea + eb - EXP_BIAS;
  int p = ((a & MASK) * (b & MASK)) >> MANTISSA_BITS;
  byte sign = (signA + signB) % 2;
  e = (sign << EXP_SIZE) + e;
  result = p | (e << MANTISSA_BITS);
}


// TODO: only works for both positives
inline add_pseudo(result,  first,  second) {
  int exp_first = first >> MANTISSA_BITS,
           exp_second = second >> MANTISSA_BITS;

  //byte sign_first = first >> (MANTISSA_BITS + EXP_SIZE);
  //byte sign_second = second >> (MANTISSA_BITS + EXP_SIZE);

  // TODO: check the signs
 
  byte sign = 0;

  exp_first = exp_first & EXP_MASK;
  exp_second = exp_second & EXP_MASK;

  if ::(exp_first > exp_second) -> {
    first = first & MASK;
    second = (second & MASK) >> (exp_first - exp_second);
    first = first + second;
    if  ::(first > MASK) -> {
      first = first >> 1;
      exp_first = exp_first + 1;
    }
    ::else -> skip;
    fi
    exp_first = (sign << EXP_SIZE) + exp_first;
    result = first | (exp_first << MANTISSA_BITS);
  } ::else -> 
        if ::(exp_second > exp_first) -> {
            second = second & MASK;
            first = (first & MASK) >> (exp_second - exp_first);
            second = second + first;
            if ::(second > MASK) -> {
                second = second >> 1;
                 exp_second = exp_second + 1;
             }
            ::else -> skip;
            fi
        exp_second = (sign << EXP_SIZE) + exp_second;
        result =  second | (exp_second << MANTISSA_BITS);
        } 
        ::else -> {
            exp_first = exp_first + 1;
            exp_first = (sign << EXP_SIZE) + exp_first;
            result =  (((first & MASK) + (second & MASK)) >> 1) |(exp_first << MANTISSA_BITS);
        }
        fi
    fi    
}






active proctype main() {

int num1 = 0;

print_pseudo_representation(num1);

int one = 1;
int two = 2;
int three;
add_pseudo(three, one, two);


}