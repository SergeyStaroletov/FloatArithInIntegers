
/*
@brief Floating point calculations implementation in Promela
@author Sergey Staroletov serg_soft@mail.ru
@license GNU GPL
*/



#define EXP_BIAS 128
#define MAX_NUMBER  4194304 // 2^22
//#define MAX_NUMBER 8388608  // 2^23
#define MANTISSA_BITS 22
//#define MANTISSA_BITS 23
#define EXP_SIZE 8
#define EXP_MASK 255
#define MASK (MAX_NUMBER - 1)
#define MAX_NUMBER_FIT (1073741824/2)  // 2^32 - sign bit, /2 for promela

int three = 1112539136;

//-----------------------------------------------------------------
inline print_float_representation(float_num) { 
  byte sign = float_num >> (MANTISSA_BITS + EXP_SIZE);
  int e_rep = float_num >> MANTISSA_BITS;
  e_rep = e_rep & EXP_MASK;
  e_rep = e_rep - EXP_BIAS;
  int f_mask = float_num & MASK;
  printf("[%d %d %d] = ", sign, e_rep, f_mask);
  if ::(f_mask == 0) -> skip;
   ::else ->
  do 
    ::((f_mask % 2) == 0) -> {
        f_mask = f_mask >> 1;
        e_rep++; 
    }
    ::else -> break;
  od
  fi
  e_rep = e_rep - MANTISSA_BITS;
  printf("%d*2^%d\n", f_mask, e_rep); //useful for inserting to google and watch the numerical result
}


//-----------------------------------------------------------------
inline sub_two_float(result_sub_two, first_sub_two_pass, second_sub_two_pass, sign_sub_two_pass) {
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

      if ::(second_sub_two == 0) -> {
        res_sub_two = first_sub_two;
        exp_sub_two = exp_first_sub_two;
      } ::else -> 
        if ::(first_sub_two == 0) -> {
          res_sub_two = second_sub_two;
          sign_sub_two = (1 - sign_sub_two);
          exp_sub_two = exp_second_sub_two;
        } ::else -> 
          if ::(exp_first_sub_two > exp_second_sub_two) -> {
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
        fi
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

inline add_two_float(result_add_two, first_add_two_pass,  second_add_two_pass, sign_add_two) {
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
inline add_float(result_add, first_add_pass, second_add_pass) {

  int first_add = first_add_pass;
  int second_add = second_add_pass;

  byte sign_first_add = first_add >> (MANTISSA_BITS + EXP_SIZE);
  byte sign_second_add = second_add >> (MANTISSA_BITS + EXP_SIZE);
  result_add = 0;

  if ::(first_add == 0) -> result_add = second_add; 
    ::else -> 
    if ::(second_add == 0) -> result_add = first_add;
      :: else -> {
      if ::(sign_first_add == 0 && sign_second_add == 0) -> { // A+B 
        add_two_float(result_add, first_add, second_add, 0)
      }
      ::else ->
        if ::(sign_first_add == 1 && sign_second_add == 1) -> {  //-A-B=>-(A+B)
          add_two_float(result_add, first_add, second_add, 1);
        } ::else ->
          if ::(sign_first_add == 0 && sign_second_add == 1) -> {  // A-B
            sub_two_float(result_add, first_add, second_add, 0);
          } ::else ->
            if ::(sign_first_add == 1 && sign_second_add == 0) -> {  // -A+B
              sub_two_float(result_add, second_add, first_add, 0);
            }
            fi
          fi
        fi
      fi
      }
   fi
  fi
}

//-----------------------------------------------------------------
inline sub_float(result_sub, first_sub_pass, second_sub_pass) {
 
  int first_sub = first_sub_pass;
  int second_sub = second_sub_pass;

  byte sign_first_sub = first_sub >> (MANTISSA_BITS + EXP_SIZE);
  byte sign_second_sub = second_sub >> (MANTISSA_BITS + EXP_SIZE);
 
  result_sub = 0;
  if ::(sign_first_sub == 0 && sign_second_sub == 0) -> {  // A-B
     sub_two_float(result_sub, first_sub, second_sub, 0);
  } ::else -> 
    if ::(sign_first_sub == 1 && sign_second_sub == 1) -> {  //-A--B=>-A+B=>B-A
       sub_two_float(result_sub, second_sub, first_sub, 0);
    } ::else ->
      if ::(sign_first_sub == 0 && sign_second_sub == 1) -> {  // A--B=>A+B
         add_two_float(result_sub, first_sub, second_sub, 0);
      } :: else ->
        if ::(sign_first_sub == 1 && sign_second_sub == 0) -> {  // -A-B=> -(A+B)
           add_two_float(result_sub, first_sub, second_sub, 1);
        }
        fi
      fi
    fi
  fi
}

//-----------------------------------------------------------------
inline div_float(result_div, first_div_pass, second_div_pass) {
  int we_return = 0;
  int reminder = 1;
  int new_exponent;
  int exponent_reminder = 150;
  int first_div = first_div_pass;
  int second_div = second_div_pass;
  byte sign_first_div = first_div >> (MANTISSA_BITS + EXP_SIZE);
  byte sign_second_div = second_div >> (MANTISSA_BITS + EXP_SIZE);

  result_div = 0;


  if ::(first_div == 0 && second_div == 0) -> 
    result_div = -1;  // nan = (0xfffff...)
  ::else ->
    if ::(first_div == 0 && second_div != 0) -> 
      result_div = 0;  // 0 / x = 0
    ::else ->
    if ::(second_div == 0) -> {
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

      int div_result = 0;
      div_result = first_div / second_div;

      //printf("%d / %d res=%d\n",first_div, second_div, div_result);
      reminder = first_div - second_div * div_result;

      reminder = 0;
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
      add_float(we_return, we_return, first_div);
      //we_return = first_div;
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
fi

}

//-----------------------------------------------------------------
inline mul_float(mul_result, a_mul_pass, b_mul_pass) {
  int a_mul = a_mul_pass; //create copies
  int b_mul = b_mul_pass; 
  if ::(a_mul == 0 || b_mul == 0) -> mul_result = 0;
    ::else -> {
      int ea_mul = a_mul >> MANTISSA_BITS, eb_mul = b_mul >> MANTISSA_BITS;
      byte signA_mul = a_mul >> (MANTISSA_BITS + EXP_SIZE);
      byte signB_mul = b_mul >> (MANTISSA_BITS + EXP_SIZE);
      ea_mul = ea_mul & EXP_MASK;  // clear the sign
      eb_mul = eb_mul & EXP_MASK;
      int e_mul = ea_mul + eb_mul - EXP_BIAS;
      a_mul = a_mul & MASK;
      b_mul = b_mul & MASK;
      int p_mul = ((a_mul >> 8) * (b_mul >> 8)) >> (MANTISSA_BITS - 16);  // or we overflow it
      byte sign_mul = (signA_mul + signB_mul) % 2;
      //fixOverflow(&p, &e);
      e_mul = (sign_mul << EXP_SIZE) + e_mul;
      mul_result =  p_mul | (e_mul << MANTISSA_BITS);
    }
  fi
}

//-----------------------------------------------------------------
inline float_from_int(result, xx, rate_of_minus10) {
int first_n = 1086324736;//test
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
  
  //print_float_representation(first_n);
  //print_float_representation(second_n);
  int res = 0;
  div_float(res, first_n, second_n);
  result = res;
}

//-----------------------------------------------------------------
inline abs_float(result_abs, x_abs) {
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
  float_from_int(seq_n, 1, 0);

  int fact = seq_n;
  int pow = x;
  int p00000001;
  float_from_int(p00000001, 1, 5);//1 * 10^-5
  
  int xx = 0; 
  mul_float(xx, x, x);
  sub_float(xx, 0, xx);

  /// sinx = x - x^3/3! + x^5/5! ...
  int abs_seq_n = 0;
  abs_float(abs_seq_n, seq_n);
  do ::((abs_seq_n > p00000001) && i_sin < 2) -> {
    
    
    int fac_part_new;
    float_from_int(fac_part_new, ((2 * i_sin) * (2 * i_sin + 1)), 0);
    
    mul_float(fact, fact, fac_part_new);

    mul_float(pow, xx, pow);
    //printf("div->"); 
    //print_float_representation(pow);
    //printf("/"); 
    //print_float_representation(fact);

    div_float(seq_n, pow, fact);
    
    add_float(current_sin, current_sin, seq_n);
    
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
  float_from_int(demie_pi, 3141592 / 2, 6);
  int x1_cos;
  sub_float(x1_cos, demie_pi, x);
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
inline X1(result_X1, cos_omt, sin_omt, Om, C1, C3, C4) {
  //return C1 + C4 * (cos(om * t) - 1) / om + C3 * sin(om * t) / om;
  result_X1 = C1;
  int temp_X1;
  int odin; 
  //int omt;
  float_from_int(odin, 1, 0); //1
  //mul_float(omt, om, t); //om * t
  //cosinus(temp_X1, omt); //cos(om * t)
  temp_X1 = cos_omt;
  sub_float(temp_X1, temp_X1, odin);//cos(om * t)-1
  mul_float(temp_X1, temp_X1, C4);//C4 * (cos(om * t) - 1)
  div_float(temp_X1, temp_X1, Om);//C4 * (cos(om * t) - 1) / om 
  add_float(result_X1, result_X1, temp_X1);
  
  temp_X1 = sin_omt;
  //sinus(temp_X1, omt); //sin(om * t)
  mul_float(temp_X1, temp_X1, C3); //C3 * sin(om * t) 
  div_float(temp_X1, temp_X1, Om); //C3 * sin(om * t) / om

  add_float(result_X1, result_X1, temp_X1);
}

inline X2(result_X2, Om, cos_omt, sin_omt, C2, C3, C4) {
  //return C2 + C3 * (1 - cos(om * t)) / om + C4 * sin(om * t) / om;
  result_X2 = C2;
  int temp_X2;
  int odin; 
  //int omt;mul_float(omt, om, t); //om * t
  float_from_int(odin, 1, 0); //1
  
  temp_X2 = cos_omt;
  //cosinus(temp_X2, omt); //cos(om * t)
  sub_float(temp_X2, odin, temp_X2);//1-cos(om * t)
  mul_float(temp_X2, temp_X2, C3);//C3 * (1-cos(om * t))
  div_float(temp_X2, temp_X2, Om);//C4 * (1-cos(om * t)) / om 
  add_float(result_X2, result_X2, temp_X2);
  
  temp_X2 = sin_omt;
  //sinus(temp_X2, omt); //sin(om * t)
  mul_float(temp_X2, temp_X2, C4); //C4 * sin(om * t) 
  div_float(temp_X2, temp_X2, Om); //C4 * sin(om * t) / om

  add_float(result_X2, result_X2, temp_X2);
}

inline D1(result_D1, cos_omt, sin_omt, C3, C4) {
  //return C3 * cos(om * t) - C4 * sin(om * t);
  int temp_D1;
  temp_D1 = cos_omt;
  //cosinus(temp_D1, omt); //cos(om * t)
  mul_float(result_D1, temp_D1, C3); //C3 * cos(om * t)
  
  temp_D1 = sin_omt;
  //sinus(temp_D1, omt); //sin(om * t);
  mul_float(temp_D1, temp_D1, C4); //C4 * sin(om * t)
  sub_float(result_D1, result_D1, temp_D1); //-
}

inline D2(result_D2, cos_omt, sin_omt, C3, C4) {
  //return C4 * cos(om * t) + C3 * sin(om * t);
  int temp_D2;
  temp_D2 = cos_omt;
  //cosinus(temp_D2, omt); //cos(om * t)
  mul_float(result_D2, temp_D2, C4); //C4 * cos(om * t)
  
  temp_D2 = sin_omt;
  //sinus(temp_D2, omt); //sin(om * t);
  mul_float(temp_D2, temp_D2, C3); //C3 * sin(om * t)
  add_float(result_D2, result_D2, temp_D2); //+
}

inline Y1(result_Y1, t, e1, C5) { 
  int temp_Y1;
  mul_float(temp_Y1, e1, t);
  add_float(result_Y1, temp_Y1, C5);
  //return e1 * t + C5; 
}

inline Y2(result_Y2, t, e2, C6) { 
  int temp_Y1;
  mul_float(temp_Y1, e1, t);
  add_float(result_Y2, temp_Y1, C6);
  //return e2 * t + C6; 
}

inline E1(result_E1, cos_omyt, sin_omyt,  C7,  C8) {
  int temp_E1 = cos_omyt;
  mul_float(temp_E1, temp_E1, C7);
  result_E1 = temp_E1;

  temp_E1 = sin_omyt;
  mul_float(temp_E1, temp_E1, C8);

  sub_float(result_E1, result_E1, temp_E1);
  //return C7 * cos(omy * t) - C8 * sin(omy * t);
}

inline E2(result_E2, cos_omyt, sin_omyt, C7, C8) {
  int temp_E2 = cos_omyt;
  mul_float(temp_E2, temp_E2, C8);
  result_E2 = temp_E2;

  temp_E2 = sin_omyt;
  mul_float(temp_E2, temp_E2, C7);

  add_float(result_E2, result_E2, temp_E2);
  //return C8 * cos(omy * t) + C7 * sin(omy * t);
}

inline check_safety(isSafe, x1, x2, y1, y2, protectedzone) {
  int x1y1; 
  sub_float(x1y1, x1, y1);
  mul_float(x1y1, x1y1, x1y1); //:)
  int x2y2;
  sub_float(x2y2, x2, y2);
  mul_float(x2y2, x2y2, x2y2); //:)
  add_float(x1y1, x1y1, x2y2);

  mul_float(x2y2, protectedzone, protectedzone);

  if ::(x1y1 >= x2y2) -> isSafe = 1; 
     ::else -> isSafe = 0;
  fi
 // return ((x1 - y1) * (x1 - y1) + (x2 - y2) * (x2 - y2) >=  protectedzone * protectedzone);
}


bit OK = 1;//to check it

inline MODEL() {

  // time
  int t = 0;
  int t_max; float_from_int(t_max, 1, 0);// t_max = 1
  int dt; float_from_int(dt, 1, 2);    //dt = 0.01
  
  // diff eq constants
  int c1; float_from_int(c1, -15, 1);  //= -1.5
  int c2; float_from_int(c1, -2, 1);   //= -0.2
  int c3; float_from_int(c3, -101, 1); //= -10.1 
  int c4; float_from_int(c4, 1, 1);    //= 0.1
  int c5; float_from_int(c5, 15, 1);   //= 1.5, 
  int c6; c6 = c4;   //= 0.1
  int c7; c7 = c4;   //= 0.1
  int c8; float_from_int(c8, 8, 0);   //c8 = 8;

  // ommm
  int om; float_from_int(om, 1, 0);    // = 1 
  int omy; omy = om;//float_from_int(omy, 1, 0);// = 1 

  int x1 = c1;
  int x2 = c2;
  int y1 = c5;
  int y2 = c6;

  // d, e
  int d1; float_from_int(d1, 5, 1);    // = 0.5 
  int d2; float_from_int(d1, 105, 4);  // = 0.0105
  int e1 = 0;
  int e2 = 0;


  int pz; float_from_int(pz, 1, 1);  //protectedzone = 0.1
  int safe = 1;
  check_safety(safe, x1, x2, y1, y2, pz);

  if ::(safe) -> {
    do:: (t < t_max) -> {
      int e1_old = e1;
      int e2_old = e2;
      int omt, cos_omt_, sin_omt_;

      mul_float(omt, om, t); //om * t

      cosinus(cos_omt_, omt); //cos(om * t)


      sinus(sin_omt_, omt);   //sin(om * t)

      //printf("...X1 \n "); 

      X1(x1, cos_omt_, sin_omt_, om, c1, c3, c4);

            //printf("...X2 \n "); 

      X2(x2, cos_omt_, sin_omt_, om, c2, c3, c4);

            //printf("...Y1 \n "); 

      Y1(y1, t, e1_old, c5);

            //printf("...Y2 \n "); 

      Y2(y2, t, e2_old, c6);

            //printf("...D1 \n "); 

      D1(d1, cos_omt_, sin_omt_, c3, c4);

            //printf("...D2 \n "); 

      D2(d2, cos_omt_, sin_omt_, c3, c4);

            //printf("...E1 \n "); 

      E1(e1, cos_omt_, sin_omt_, c7, c8);

            //printf("...E2 \n "); 

      E2(e2, cos_omt_, sin_omt_, c7, c8);

            //printf("...check \n "); 

      
      check_safety(safe, x1, x2, y1, y2, pz);

      if ::(safe == 0) -> {
        printf("Safety check violtion!");
      } ::else -> skip;
      fi

      printf("\n-----------------------------\n");
      printf("t = "); 
      print_float_representation(t);
      printf("\n X1 = ");
      print_float_representation(x1);
      printf("\n X2 = ");
      print_float_representation(x2);
      printf("\n Y1 = ");
      print_float_representation(y1);
      printf("\n Y2 = ");
      print_float_representation(y2);

      
      



      add_float(t, t, dt);
    } ::else -> break;
    od
  } else -> skip;
  fi


}


//-----------------------------------------------------------------
active proctype main() {

int one = 1086324736;
int two = 1112539136;

float_from_int(one, 20, 0);
float_from_int(two, 35, 1);
//div_float(three, one, two);
print_float_representation(one);
print_float_representation(two);


byte signsign = 0;

//sub_two_float(three, one, two, signsign);
//add_two_float(three, one, two, signsign);

//add_float(three, one, two);
//sub_float(three, one, two);
//mul_float(three, one, two);

//int pi; float_from_int(pi, 3141592/3, 6);

//int pi  = 4194304;
//sinus(three, pi);
//cosinus(three, pi);

MODEL();

//print_float_representation(three);



}
