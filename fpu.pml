
/*
@brief Floating point calculations implementation in Promela
@author Sergey Staroletov serg_soft@mail.ru
@license GNU GPL
*/
#define EXP_BIAS 128
#define MAX_NUMBER 8388608  // 2^23
#define MANTISSA_BITS 23
#define EXP_SIZE 8
#define EXP_MASK 255
#define MASK (MAX_NUMBER - 1)
#define MAX_NUMBER_FIT 1073741824  // 2^32 - sign bit, /2 for promela, IDK

int three = 1112539136;

//-----------------------------------------------------------------
inline print_pseudo_representation(f) { 
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


//-----------------------------------------------------------------
inline sub_two_pseudo(result_sub_two, first_sub_two_pass, second_sub_two_pass, sign_sub_two_pass) {
  int first_sub_two = first_sub_two_pass;
  int second_sub_two = second_sub_two_pass;
  int exp_first_sub_two = first_sub_two >> MANTISSA_BITS, exp_second_sub_two = second_sub_two >> MANTISSA_BITS;

  byte sign_sub_two = sign_sub_two_pass;

  if ::(exp_first_sub_two == 0) -> exp_first_sub_two = EXP_BIAS;
    ::else -> skip; 
  fi
  if ::(exp_second_sub_two == 0) -> exp_second_sub_two = EXP_BIAS;
    ::else -> skip;
  fi

  exp_first_sub_two = exp_first_sub_two & EXP_MASK;  // clear the sign
  exp_second_sub_two = exp_second_sub_two & EXP_MASK;

  if ::((exp_first_sub_two - exp_second_sub_two) >= 32) -> {
    // first number too mush bigger than next one
    result_sub_two =  first_sub_two | (sign_sub_two >> (MANTISSA_BITS + EXP_SIZE));
  } :: else ->
    if ::(exp_second_sub_two - exp_first_sub_two >= 32) -> {
      // second number too mush bigger than next one
      result_sub_two = second_sub_two| (sign_sub_two >> (MANTISSA_BITS + EXP_SIZE));
    } :: else -> { 
      //normal sub
      first_sub_two = first_sub_two & MASK;
      second_sub_two = second_sub_two & MASK;

      int res_sub_two = 0;
      int exp_sub_two;

      if ::((exp_first_sub_two > exp_second_sub_two) && (first_sub_two != 0)) -> {
        exp_sub_two = exp_first_sub_two;
        res_sub_two = first_sub_two - (second_sub_two >> (exp_first_sub_two - exp_second_sub_two));
        if ::(res_sub_two < 0) -> {
          res_sub_two = -res_sub_two;
          sign_sub_two = (1 - sign_sub_two); //not
        } ::else -> skip;
        fi
      } ::else -> {
        exp_sub_two = exp_second_sub_two;
        res_sub_two = (first_sub_two >> (exp_second_sub_two - exp_first_sub_two)) - second_sub_two;
        if ::(res_sub_two < 0) -> {
          res_sub_two = -res_sub_two;
          sign_sub_two = (1 - sign_sub_two); //not
        } ::else -> skip;
        fi
      }
      fi

      if ::(res_sub_two == 0) -> result_sub_two = 0; 
      ::else -> {
        do ::(res_sub_two < MAX_NUMBER / 2) -> {
          res_sub_two = res_sub_two << 1;
          exp_sub_two = exp_sub_two - 1;
        } ::else -> break;
        od
        //fixOverflow(ret, exp);
        exp_sub_two = (sign_sub_two << EXP_SIZE) + exp_sub_two;
        result_sub_two =  res_sub_two | (exp_sub_two << MANTISSA_BITS);
      } 
      fi
    } 
    fi
  fi
}
//-----------------------------------------------------------------

inline add_two_pseudo(result_add_two, first_add_two_pass,  second_add_two_pass, sign_add_two) {
  int first_add_two = first_add_two_pass;
  int second_add_two = second_add_two_pass;
  int exp_first_add_two = first_add_two >> MANTISSA_BITS, exp_second_add_two = second_add_two >> MANTISSA_BITS;

  exp_first_add_two = exp_first_add_two & EXP_MASK;
  exp_second_add_two = exp_second_add_two & EXP_MASK;

  if ::(exp_first_add_two - exp_second_add_two >= 32) -> {
    // first number too mush bigger than next one
    result_add_two = first_add_two | (sign_add_two >> (MANTISSA_BITS + EXP_SIZE));
  } ::else -> 
  if ::(exp_second_add_two - exp_first_add_two >= 32) -> {
    // second number too mush bigger than next one
    result_add_two =  second_add_two | (sign_add_two >> (MANTISSA_BITS + EXP_SIZE));
  } ::else -> {

    if ::(exp_first_add_two > exp_second_add_two) -> {
      first_add_two = first_add_two & MASK;
      second_add_two = (second_add_two & MASK) >> (exp_first_add_two - exp_second_add_two);
      first_add_two = first_add_two + second_add_two;
      if ::(first_add_two > MASK) -> {
        first_add_two = first_add_two >> 1;
        exp_first_add_two = exp_first_add_two + 1;
      } ::else -> skip;
      fi
      //fixOverflow(first, exp_first);
      exp_first_add_two = (sign_add_two << EXP_SIZE) + exp_first_add_two;
      result_add_two = first_add_two | (exp_first_add_two << MANTISSA_BITS);

    } :: else -> if ::(exp_second_add_two > exp_first_add_two) -> {
        second_add_two = second_add_two & MASK;
        first_add_two = (first_add_two & MASK) >> (exp_second_add_two - exp_first_add_two);

        second_add_two = second_add_two + first_add_two;

        if ::(second_add_two > MASK) -> {
          second_add_two = second_add_two >> 1;
          exp_second_add_two = exp_second_add_two + 1;
        } :: else -> skip;
        fi
        //fixOverflow(second, exp_second);

        exp_second_add_two = (sign_add_two << EXP_SIZE) + exp_second_add_two;
        result_add_two = second_add_two | (exp_second_add_two << MANTISSA_BITS);
      } :: else -> {
        exp_first_add_two = exp_first_add_two + 1;
        result_add_two = (((first_add_two & MASK) + (second_add_two & MASK)) >> 1);
        //fixOverflow(&res, &exp_first);
        exp_first_add_two = (sign_add_two << EXP_SIZE) + exp_first_add_two;
        result_add_two = result_add_two | (exp_first_add_two << MANTISSA_BITS);
      }
      fi
    fi  
  }
  fi 
fi 
}

//-----------------------------------------------------------------
inline add_pseudo(result_add, first_add, second_add) {
  byte sign_first_add = first_add >> (MANTISSA_BITS + EXP_SIZE);
  byte sign_second_add = second_add >> (MANTISSA_BITS + EXP_SIZE);
  result_add = 0;
  if ::(sign_first_add == 0 && sign_second_add == 0) -> { // A+B 
     add_two_pseudo(result_add, first_add, second_add, 0)
  }
  ::else ->
    if ::(sign_first_add == 1 && sign_second_add == 1) ->{  //-A-B=>-(A+B)
       add_two_pseudo(result_add, first_add, second_add, 1);
    } ::else ->
      if ::(sign_first_add == 0 && sign_second_add == 1) -> {  // A-B
        sub_two_pseudo(result_add, first_add, second_add, 0);
      } ::else ->
        if ::(sign_first_add == 1 && sign_second_add == 0) -> {  // -A+B
           sub_two_pseudo(result_add, second_add, first_add, 0);
        }
        fi
      fi
    fi
   fi
}

//-----------------------------------------------------------------
inline sub_pseudo(result_sub, first_sub, second_sub) {
  byte sign_first_sub = first_sub >> (MANTISSA_BITS + EXP_SIZE);
  byte sign_second_sub = second_sub >> (MANTISSA_BITS + EXP_SIZE);
  result_sub = 0;
  if ::(sign_first_sub == 0 && sign_second_sub == 0) -> {  // A-B
     sub_two_pseudo(result_sub, first_sub, second_sub, 0);
  } ::else -> 
    if ::(sign_first_sub == 1 && sign_second_sub == 1) -> {  //-A--B=>-A+B=>B-A
       sub_two_pseudo(result_sub, second_sub, first_sub, 0);
    } ::else ->
      if ::(sign_first_sub == 0 && sign_second_sub == 1) -> {  // A--B=>A+B
         add_two_pseudo(result_sub, first_sub, second_sub, 0);
      } :: else ->
        if ::(sign_first_sub == 1 && sign_second_sub == 0) -> {  // -A-B=> -(A+B)
           add_two_pseudo(result_sub, first_sub, second_sub, 1);
        }
        fi
      fi
    fi
  fi
}

//-----------------------------------------------------------------
inline div_pseudo(result_div, first_div_pass, second_div_pass) {
  int we_return = 0;
  int reminder = 1;
  int new_exponent;
  int exponent_reminder = 150;
  int first_div = first_div_pass;
  int second_div = second_div_pass;
  byte sign_first_div = first_div >> (MANTISSA_BITS + EXP_SIZE);
  byte sign_second_div = second_div >> (MANTISSA_BITS + EXP_SIZE);

  if ::(first_div == 0 && second_div == 0) -> 
    result_div = -1;  // nan = (0xfffff...)
  ::else -> if ::(second_div == 0) -> {
    if ::(first_div > 0) -> 
      result_div = (128 << MANTISSA_BITS);  //0x80, +inf
       ::else ->
      result_div = (255 << MANTISSA_BITS);  //0xff, -inf
    fi
  } ::else -> {
    //normal div
  do ::((reminder > 0) && (exponent_reminder >= 142)) -> {//?
    int exp_first = first_div >> MANTISSA_BITS,
        exp_second = second_div >> MANTISSA_BITS;
    first_div = first_div & MASK;
    second_div = second_div & MASK;
    exp_first = exp_first & EXP_MASK;  // clear the sign
    exp_second = exp_second & EXP_MASK;
    new_exponent = MANTISSA_BITS + ((exp_first - exp_second) + EXP_BIAS);
    int ee_div = 0;
    if ::(first_div > 0) -> {
      do ::(first_div < MAX_NUMBER_FIT) -> {
        first_div = first_div << 1;
        ee_div = ee_div + 1;
      } ::else -> break;
      od
    }
    ::else -> {
      result_div = we_return;
      break;
    } 
    fi

    new_exponent = new_exponent - ee_div;

    if ::(second_div > 0) -> { 
      do ::((second_div % 2) == 0) -> {
        second_div = second_div >>  1;
        new_exponent = new_exponent - 1;
        }  // hack: уменьшаем делимое
        ::else -> break;
      od 
      }
      ::else -> skip;
    fi

    int div_result = first_div / second_div;
    printf("res=%d\n", div_result);
    reminder = first_div - second_div * div_result;

    do ::(div_result >= MAX_NUMBER) -> {
      div_result =  div_result >> 1;
      new_exponent = new_exponent + 1;
    } ::else -> break;
    od
    int curr_exp = 0;
    int rem_div_number1 = 0, rem_div_number2 = 0;

    exponent_reminder = new_exponent;
    // check the reminder and create a number1/number2 solution
    if ::(reminder > 0) -> {
      rem_div_number1 = reminder;
      curr_exp = new_exponent;
      do ::(rem_div_number1 >= MAX_NUMBER) -> {
        rem_div_number1 = rem_div_number1 >> 1;
        curr_exp = curr_exp + 1;
      } ::else -> break;
      od
      do ::(rem_div_number1 < MAX_NUMBER / 2) -> {
        rem_div_number1 = rem_div_number1 << 1;
        curr_exp = curr_exp - 1;
      } ::else -> break;
      od

      rem_div_number1 = rem_div_number1 | (curr_exp << MANTISSA_BITS);

      rem_div_number2 = second_div;
      curr_exp = EXP_BIAS + MANTISSA_BITS;
      do ::(rem_div_number2 < MAX_NUMBER / 2) -> {
        rem_div_number2 = rem_div_number2 << 1;
        curr_exp = curr_exp - 1;
      } ::else -> break;
      od
      rem_div_number2 = rem_div_number2 | (curr_exp << MANTISSA_BITS);
    }::else -> skip;
    fi

    first_div = div_result;

    if ::(first_div > 0) -> {
      do ::(first_div < MAX_NUMBER / 2) -> 
      {
        first_div = first_div << 1;
        new_exponent = new_exponent - 1;
      } ::else -> break;
      od
    } ::else -> skip;
    fi

    if ::(first_div == MAX_NUMBER) -> {
      first_div = first_div >> 1;
      new_exponent = new_exponent + 1;
    } ::else -> skip;
    fi

    byte sign = (sign_first_div + sign_second_div) % 2;
    //fixOverflow(&first, &new_exponent);
    new_exponent = (sign << EXP_SIZE) + new_exponent;
    first_div = first_div | (new_exponent << MANTISSA_BITS);
    add_pseudo(we_return, we_return, first_div);

    if ::((new_exponent == EXP_BIAS + MANTISSA_BITS - 1) ||
        (new_exponent == EXP_BIAS - (MANTISSA_BITS - 1))) ->
      break;
    :: else -> skip;
    fi
    first_div = rem_div_number1;
    second_div = rem_div_number2;
    // continue to divide, get the reminder and add it to the result
  } ::else -> break;
  od

  result_div = we_return;
  }
  fi
fi
}

//-----------------------------------------------------------------
inline mul_pseudo(mul_result, a_mul_pass, b_mul_pass) {
  int a_mul = a_mul_pass; //create copies
  int b_mul = b_mul_pass; 
  int ea_mul = a_mul >> MANTISSA_BITS, eb_mul = b_mul >> MANTISSA_BITS;
  byte signA_mul = a_mul >> (MANTISSA_BITS + EXP_SIZE);
  byte signB_mul = b_mul >> (MANTISSA_BITS + EXP_SIZE);
  ea_mul = ea_mul & EXP_MASK;  // clear the sign
  eb_mul = eb_mul & EXP_MASK;
  int e_mul = ea_mul + eb_mul - EXP_BIAS;
  a_mul = a_mul & MASK;
  b_mul = b_mul & MASK;
  int p_mul = ((a_mul >> 8) * (b_mul >> 8)) >> 7;  // or we overflow it
  byte sign_mul = (signA_mul + signB_mul) % 2;
  //fixOverflow(&p, &e);
  e_mul = (sign_mul << EXP_SIZE) + e_mul;
  mul_result =  p_mul | (e_mul << MANTISSA_BITS);
}

//-----------------------------------------------------------------
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
  
//print_pseudo_representation(first_n);
//print_pseudo_representation(second_n);
int res = 0;
div_pseudo(res, first_n, second_n);
result = res;
}
//-----------------------------------------------------------------
inline abs_pseudo(result_abs, x_abs) {
  byte sign_abs = x_abs >> (MANTISSA_BITS + EXP_SIZE);
  int e_abs = x_abs >> (MANTISSA_BITS);
  e_abs = e_abs & EXP_MASK;
  int ff_abs = x_abs & MASK;
  e_abs = (sign_abs << EXP_SIZE) + e_abs;
  result_abs =  ff_abs | (e_abs << MANTISSA_BITS);
}


//-----------------------------------------------------------------
inline sinus(result_sinus, x) {
  int i_sin = 1;
  int current_sin = x;
  int seq_n;
  pseudo_from_int(seq_n, 1, 0);

  int fact = seq_n;
  int pow = x;
  int p00000001;
  pseudo_from_int(p00000001, 1, 5);//1 * 10^-5
  
  int xx = 0; 
  mul_pseudo(xx, x, x);
  sub_pseudo(xx, 0, xx);
  //print_pseudo_as_float("1-xx = ", xx);

  /// sinx = x - x^3/3! + x^5/5! ...
  int abs_seq_n;
  abs_pseudo(abs_seq_n, seq_n);
  do ::((abs_seq_n > p00000001) && i_sin < 10) -> {
    int fac_part_new;
    pseudo_from_int(fac_part_new, ((2 * i_sin) * (2 * i_sin + 1)), 0);
    mul_pseudo(fact, fact, fac_part_new);

    mul_pseudo(pow, xx, pow);

    div_pseudo(seq_n, pow, fact);
    //printf("%d", i);
    add_pseudo(current_sin, current_sin, seq_n);
    //print_pseudo_as_float(" -> current sin = ", current_sin);
    i_sin++;
  } 
  ::else -> break;
  od

  result_sinus = current_sin;
}

//-----------------------------------------------------------------
inline cosinus(result_cos, x) {
  int cos_val = 0;
  int demie_pi;
  pseudo_from_int(demie_pi, 3141592 / 2, 6);
  int x1_cos;
  sub_pseudo(x1_cos, demie_pi, x);
  sinus(cos_val, x1_cos);
  result_cos = cos_val;
}

//-----------------------------------------------------------------
//   RoundAbout Manevuer CPS
//-----------------------------------------------------------------

/* The solution for
              (x1') = (d1),
              (x2') = (d2),
              (d1') = ((-(om)) * (d2)),
              (d2') = ((om) * (d1)),
              (y1') = (e1),
              (y2') = (e2),
              (e1') = ((-(omy)) * (e2)),
              (e2') = ((omy) * (e1)),
              ((((x1) - (y1)) ^ (2)) + (((x2) - (y2)) ^ (2))) >=
   ((protectedzone) ^ (2))
*/
inline X1(result_X1, t, om, C1, C3, C4) {
  //return C1 + C4 * (cos(om * t) - 1) / om + C3 * sin(om * t) / om;
  result_X1 = C1;
  int temp_X1;
  int odin; 
  int omt;
  pseudo_from_int(odin, 1, 0); //1
  mul_pseudo(omt, om, t); //om * t
  cosinus(temp_X1, omt); //cos(om * t)
  sub_pseudo(temp_X1, temp_X1, odin);//cos(om * t)-1
  mul_pseudo(temp_X1, temp_X1, C4);//C4 * (cos(om * t) - 1)
  div_pseudo(temp_X1, om);//C4 * (cos(om * t) - 1) / om 
  add_pseudo(result_X1, result_X1, temp_X1);
  
  sinus(temp_X1, omt); //sin(om * t)
  mul_pseudo(temp_X1, temp_X1, C3); //C3 * sin(om * t) 
  div_pseudo(temp_X1, om); //C3 * sin(om * t) / om

  add_pseudo(result_X1, result_X1, temp_X1);

}
inline X2(result_X2, om, cos_omt, sin_omt, C2, C3, C4) {
  //return C2 + C3 * (1 - cos(om * t)) / om + C4 * sin(om * t) / om;
  result_X2 = C2;
  int temp_X2;
  int odin; 
  //int omt;mul_pseudo(omt, om, t); //om * t
  pseudo_from_int(odin, 1, 0); //1
  
  temp_X2 = cos_omt;
  //cosinus(temp_X2, omt); //cos(om * t)
  sub_pseudo(temp_X2, odin, temp_X2);//1-cos(om * t)
  mul_pseudo(temp_X2, temp_X2, C3);//C3 * (1-cos(om * t))
  div_pseudo(temp_X2, om);//C4 * (1-cos(om * t)) / om 
  add_pseudo(result_X2, result_X2, temp_X2);
  
  temp_X2 = sin_omt;
  //sinus(temp_X2, omt); //sin(om * t)
  mul_pseudo(temp_X2, temp_X1, C4); //C4 * sin(om * t) 
  div_pseudo(temp_X2, om); //C4 * sin(om * t) / om

  add_pseudo(result_X2, result_X2, temp_X1);

}
inline D1(result_D1, cos_omt, sin_omt,  C3,  C4) {
  //return C3 * cos(om * t) - C4 * sin(om * t);
  int temp_D1;
  temp_D1 = cos_omt;
  //cosinus(temp_D1, omt); //cos(om * t)
  mul_pseudo(result_D1, temp_D1, C3); //C3 * cos(om * t)
  
  temp_D1 = sin_omt
  //sinus(temp_D1, omt); //sin(om * t);
  mul_pseudo(temp_D1, temp_D1, C4); //C4 * sin(om * t)
  sub_pseudo(result_D1, result_D1, temp_D1); //-
}
inline D2(result_D2, cos_omt, sin_omt, C3, C4) {
  //return C4 * cos(om * t) + C3 * sin(om * t);
  int temp_D2;
  temp_D2 = cos_omt;
  //cosinus(temp_D2, omt); //cos(om * t)
  mul_pseudo(result_D2, temp_D2, C4); //C4 * cos(om * t)
  
  temp_D2 = sin_omt;
  //sinus(temp_D2, omt); //sin(om * t);
  mul_pseudo(temp_D2, temp_D2, C3); //C3 * sin(om * t)
  add_pseudo(result_D2, result_D2, temp_D2); //+
}

inline Y1(result_Y1, t, e1,  C5) { 
  int temp_Y1;
  mul_pseudo(temp_Y1, e1, t);
  add_pseudo(result_Y1, temp_Y1, C5);
  //return e1 * t + C5; 
}

inline Y2(result_Y2, t, e2, C6) { 
  int temp_Y1;
  mul_pseudo(temp_Y1, e1, t);
  add_pseudo(result_Y1, temp_Y1, C5);
  //return e2 * t + C6; 
}

inline E1(result_E1, cos_omyt, sin_omyt,  C7,  C8) {
  int temp_E1 = cos_omyt;
  mul_pseudo(temp_E1, temp_E1, C7);
  result_E1 = temp_E1;

  int temp_E1 = sin_omyt;
  mul_pseudo(temp_E1, temp_E1, C8);

  sub_pseudo(result_E1, result_E1, temp_E1);
  //return C7 * cos(omy * t) - C8 * sin(omy * t);
}

inline E2(result_E2, cos_omyt, sin_omyt, C7, C8) {
  int temp_E2 = cos_omyt;
  mul_pseudo(temp_E2, temp_E2, C8);
  result_E2 = temp_E2;

  int temp_E2 = sin_omyt;
  mul_pseudo(temp_E2, temp_E2, C7);

  add_pseudo(result_E2, result_E2, temp_E2);
  //return C8 * cos(omy * t) + C7 * sin(omy * t);
}

inline check_safety(isSafe, x1, x2, y1, y2, protectedzone) {
  int x1y1; 
  sub_pseudo(x1y1, x1, y1);
  mul_pseudo(x1y1, x1y1, x1y1); //:)
  int x2y2;
  sub_pseudo(x2y2, x2, y2);
  mul_pseudo(x2y2, x2y2, x2y2); //:)
  add_pseudo(x1y1, x1y1, x2y2);

  mul_pseudo(x2y2, protectedzone, protectedzone);

  if ::(x1x1 >= x2y2) -> isSafe = 1; 
     ::else -> isSafe = 0;
  fi
 // return ((x1 - y1) * (x1 - y1) + (x2 - y2) * (x2 - y2) >=  protectedzone * protectedzone);
}

inline MODEL() {

  int t = 0;

  int dt; pseudo_from_int(dt, 1, 2);//dt = 0.01;
  int c1; pseudo_from_int(c1, -15, 1);//= -1.5
  int c2; pseudo_from_int(c1, -2, 1);//= -0.2, 
  
  c3 = -10.1, c4 = 0.1, c5 = 1.5, c6 = 0.1,
         c7 = 0.1, c8 = 8;
  double om = 1, omy = 1;

  double x1 = c1, x2 = c2, y1 = c5, y2 = c6, d1 = 0.5, d2 = +0.0105, e1 = 0,
         e2 = 0;


}


//-----------------------------------------------------------------
active proctype main() {

int one = 1086324736;
int two = 1112539136;

pseudo_from_int(one, 20, 0);
pseudo_from_int(two, 35, 1);
//div_pseudo(three, one, two);
print_pseudo_representation(one);
print_pseudo_representation(two);


byte signsign = 0;

sub_two_pseudo(three, one, two, signsign);
add_two_pseudo(three, one, two, signsign);

add_pseudo(three, one, two);
sub_pseudo(three, one, two);
mul_pseudo(three, one, two);

sinus(three, one);
cosinus(three, one);


print_pseudo_representation(three);


}
