
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


//-----------------------------------------------------------------
inline sub_two_pseudo(result_sub_two, first_sub_two, second_sub_two, sign_sub_two_pass) {
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

inline add_two_pseudo(result_add_two, first_add_two,  second_add_two, sign_add_two) {
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
//div_pseudo(res, first_n, second_n);
result = res;
}


//-----------------------------------------------------------------

active proctype main() {

int one = 1086324736;
int two = 1112539136;

pseudo_from_int(one, 20, 0);
pseudo_from_int(two, 35, 1);
//div_pseudo(three, one, two);

byte signsign = 0;

sub_two_pseudo(three, one, two, signsign);
add_two_pseudo(three, one, two, signsign);

add_pseudo(three, one, two);
sub_pseudo(three, one, two);

print_pseudo_representation(three);

}
