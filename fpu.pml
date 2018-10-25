
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
#define MAX_NUMBER_FIT 1073741824  // 2^32 - sign



inline print_pseudo_representation(f){ 
  byte sign = f >> (MANTISSA_BITS + EXP_SIZE);
  int e_rep = f >> MANTISSA_BITS;
  e_rep = e_rep & EXP_MASK;
  e_rep = e_rep - EXP_BIAS;
  int ff = f & MASK;
  printf("[%d %d %d] = ", sign, e_rep, ff);
  if ::(ff == 0) -> skip;
   ::else ->
  do 
    ::((ff % 2) == 0) -> {
        ff = ff >> 1;
        e_rep++; 
    }
    ::else -> break;
  od
  fi
  e_rep = e_rep - MANTISSA_BITS;
  printf("%d*2^%d\n", ff, e_rep);
}


inline mul_pseudo(result, a, b) {
  int ea = a >> MANTISSA_BITS, eb = b >> MANTISSA_BITS;
  byte signA = a >> (MANTISSA_BITS + EXP_SIZE);
  byte signB = b >> (MANTISSA_BITS + EXP_SIZE);
  ea = ea & EXP_MASK;  // clear the sign
  eb = eb & EXP_MASK;
  byte e = ea + eb - EXP_BIAS;
  int p = (((a & MASK) >> 8) * ((b & MASK)>>8)) >> 7; //8+8+7 = MANTISSA_BITS
  byte sign = (signA + signB) % 2;
  e = (sign << EXP_SIZE) + e;
  result = p | (e << MANTISSA_BITS);
}


// TODO: only works for both positives
inline add_pseudo(result,  add_first,  add_second) {
  int exp_first_ = add_first >> MANTISSA_BITS,
           exp_second_ = add_second >> MANTISSA_BITS;

  result = 0;

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
    result = add_first | (exp_first_ << MANTISSA_BITS);
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
 inline div_pseudo(divresult,  first, second) {
  int we_return = 0;
  int reminder = 1;
  int new_exponent;
  int exponent_reminder = 150;

  do :: ((reminder > 0) && (exponent_reminder >= 142)) -> {
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

    byte sign_div = (sign_first + sign_second) % 2;
    new_exponent = (sign_div << EXP_SIZE) + new_exponent;
    first = first | (new_exponent << MANTISSA_BITS);

    int res_add;
    add_pseudo(res_add, we_return, first);
    we_return = res_add;

    first = rem_div_number1;
    second = rem_div_number2;

    // continue to divide, get the reminder and add it to the result
  } ::else -> break;
  od

  divresult = we_return;
}


inline pseudo_from_int(result, xx, rate_of_minus10) {
int first_n = 1086324736;
int second_n = 1112539136;
  
  int x = xx;  
  int pow_of_10 = 1;
  int i = 0;
  do
    ::(i < rate_of_minus10) -> {pow_of_10 = pow_of_10 * 10; i = i + 1;}
    ::else -> break;
  od

  int e = EXP_BIAS + MANTISSA_BITS;
  byte sign_ = 0;
  if ::(x < 0) -> {
    sign_ = 1;
    x = 0 - x;
  }  :: else -> skip;
  fi

  if ::(x == 0) -> first_n = 0;
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
  first_n = x | (e << MANTISSA_BITS);
  
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
  
  second_n = x | (e << (MANTISSA_BITS));
  
 //div_pseudo(result, first_n, second_n);

//print_pseudo_representation(first_n);
//print_pseudo_representation(second_n);
int res = 0;
div_pseudo(res, first_n, second_n);

result = res;
//print_pseudo_representation(result);

}


active proctype main() {

int one = 1086324736;
int two = 1112539136;
int three = 1112539136;
pseudo_from_int(one, 20, 0);
pseudo_from_int(two, 3, 0);
//div_pseudo(three, one, two);
mul_pseudo(three, one, two);


print_pseudo_representation(three);

}
