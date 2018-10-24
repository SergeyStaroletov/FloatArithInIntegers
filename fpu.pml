
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
inline add_pseudo(result,  add_first,  add_second) {
  int exp_first_ = add_first >> MANTISSA_BITS,
           exp_second_ = add_second >> MANTISSA_BITS;

  //byte sign_first = first >> (MANTISSA_BITS + EXP_SIZE);
  //byte sign_second = second >> (MANTISSA_BITS + EXP_SIZE);

  // TODO: check the signs
 
  byte add_sign = 0;

  exp_first_ = exp_first_ & EXP_MASK;
  exp_second_ = exp_second_ & EXP_MASK;

  if ::(exp_first_ > exp_second_) -> {
    add_first = add_first & MASK;
    add_second = (add_second & MASK) >> (exp_first_ - exp_second_);
    add_first = add_first + add_second;
    if  ::(add_first > MASK) -> {
      add_first = add_first >> 1;
      exp_first_ = exp_first_ + 1;
    }
    ::else -> skip;
    fi
    exp_first_ = (add_sign << EXP_SIZE) + exp_first_;
    result = add_first | (exp_first << MANTISSA_BITS);
  } ::else -> 
        if ::(exp_second_ > exp_first_) -> {
            add_second = add_second & MASK;
            add_first = (add_first & MASK) >> (exp_second_ - exp_first_);
            add_second = add_second + add_first;
            if ::(add_second > MASK) -> {
                add_second = add_second >> 1;
                 exp_second_ = exp_second_ + 1;
             }
            ::else -> skip;
            fi
        exp_second_ = (add_sign << EXP_SIZE) + exp_second_;
        result =  add_second | (exp_second_ << MANTISSA_BITS);
        } 
        ::else -> {
            exp_first_ = exp_first_ + 1;
            exp_first_ = (add_sign << EXP_SIZE) + exp_first_;
            result =  (((add_first & MASK) + (add_second & MASK)) >> 1) |(exp_first_ << MANTISSA_BITS);
        }
        fi
    fi    
}

// TODO: check the accuracy again
 inline div_pseudo(result,  first, second) {
  int we_return = 0;
  int reminder = 0;
  int new_exponent;
  int exponent_reminder;

  do :: true -> {
    byte sign_first = first >> (MANTISSA_BITS + EXP_SIZE);
    byte sign_second = second >> (MANTISSA_BITS + EXP_SIZE);
    int exp_first = first >> MANTISSA_BITS,
             exp_second = second >> MANTISSA_BITS;
    first = first & MASK;
    second = second & MASK;
    exp_first = exp_first & EXP_MASK;  // clear the sign
    exp_second = exp_second & EXP_MASK;
    new_exponent = MANTISSA_BITS + ((exp_first - exp_second) + EXP_BIAS);
    int ee = 0;
    do ::(first < MAX_NUMBER_FIT) -> {
      first = first << 1;
      ee = ee + 1;
      }
      ::else -> break; 
    od
    new_exponent = new_exponent - ee;

    /*if (first == 0 && second == 0)
      result = -1;  // nan = (0xfffff...)
    else if (second == 0) {
      if (first > 0)
        return (0x80 << MANTISSA_BITS);  //+inf
      else
        return (0xff << MANTISSA_BITS);  //-inf
    }*/

    // hack: уменьшаем делимое
    do ::((second % 2) == 0) -> {
      second = second >> 1;
      new_exponent = new_exponent - 1;
    }  
       :: else -> break;
    od
    int div_result = first / second;

    printf("res=%d\n", div_result);

    do ::(div_result >= MAX_NUMBER) -> {
      div_result = div_result >> 1;
      new_exponent = new_exponent + 1;
    } 
      :: else -> break;
    od 

    reminder = first - second * div_result;

    int curr_exp = 0;

    int rem_div_number1 = 0, rem_div_number2 = 0;
    exponent_reminder = new_exponent;
    // check the reminder and create a number1/number2 solution
    if ::(reminder > 0) -> {
      rem_div_number1 = reminder;
      curr_exp = new_exponent;
      do
        ::(rem_div_number1 < MAX_NUMBER / 2) -> {
        rem_div_number1 = rem_div_number1 << 1;
        curr_exp = curr_exp - 1;}
        ::else -> break;
      od
      rem_div_number1 = rem_div_number1 | (curr_exp << MANTISSA_BITS);

      rem_div_number2 = second;
      curr_exp = EXP_BIAS + MANTISSA_BITS;
      do ::(rem_div_number2 < MAX_NUMBER / 2) -> {
        rem_div_number2 = rem_div_number2 << 1;
        curr_exp = curr_exp - 1;
      } ::else -> break;
      od

      rem_div_number2 = rem_div_number2 | (curr_exp << MANTISSA_BITS);
    } ::else -> skip;
    fi

    first = div_result;

    do ::(first <= MAX_NUMBER / 2) -> {
      first = first << 1;
      new_exponent = new_exponent - 1;
    } ::else -> break;
    od

    if ::(first == MAX_NUMBER) -> {
      first = first >> 1;
      new_exponent = new_exponent + 1;
    } ::else -> skip;
    fi

    byte sign = (sign_first + sign_second) % 2;
    new_exponent = (sign << EXP_SIZE) + new_exponent;
    first = first | (new_exponent << MANTISSA_BITS);

    add_pseudo(we_return, we_return, first);

    first = rem_div_number1;
    second = rem_div_number2;

    // continue to divide, get the reminder and add it to the result
  } :: !((reminder > 0) && (exponent_reminder >= 142)) -> break;
  od

  result = we_return;
}


inline pseudo_from_int(result, xx, rate_of_minus10) {
  int x = xx;  
  int pow_of_10 = 1;
  int i = 0;
  do
    ::(i < rate_of_minus10) -> {pow_of_10 = pow_of_10 * 10; i = i + 1;}
    ::else -> break;
  od

  int first, second;

  int e = EXP_BIAS + MANTISSA_BITS;
  byte sign_ = 0;
  if ::(x < 0) -> {
    sign_ = 1;
    x = 0 - x;
  }  :: else -> skip;
  fi


  if ::(x == 0) -> first = 0;
  ::else -> {
  do    
  ::(x < MAX_NUMBER / 2) -> { 
  x = x * 2; 
  e = e - 1; 
  }:: else -> break;  
  od
  do
   ::((x >= MAX_NUMBER) && (e <= 255)) -> { 
    x = x / 2; e = e + 1;
    } :: else -> break;
  od
  } 
  fi

  e = (sign_ << EXP_SIZE) + e;
  first = x | (e << MANTISSA_BITS);
  e = EXP_BIAS + MANTISSA_BITS;
  sign_ = 0;
  x = pow_of_10;

  do
  ::(x < (MAX_NUMBER / 2)) -> {
    x = x * 2;
    e = e - 1;
  } ::else -> break;
  od

  do 
  ::((x >= MAX_NUMBER) && (e <= 255)) -> {
    x = x / 2;
    e = e + 1;
  } ::else -> break;
  od

  e = (sign_ << EXP_SIZE) + e;
  second = x | (e << (MANTISSA_BITS));

  div_pseudo(result, first, second);
}


active proctype main() {

int one;
int two;
int three;

pseudo_from_int(one, 1, 1);
//pseudo_from_int(two, 2, 1);

//div_pseudo(three, one, two);


//print_pseudo_representation(three);

 


}