/*
@brief Floating point calculations implementation in plain C for integer
processors
@author Sergey Staroletov serg_soft@mail.ru
@license GNU GPL
*/

#ifndef FPU_H
#define FPU_H

typedef unsigned int pseudofloat;

void fixOverflow(pseudofloat *mantissa, int *exp);

pseudofloat sub_two_pseudo(pseudofloat first, pseudofloat second, char sign);

pseudofloat add_two_pseudo(pseudofloat first, pseudofloat second, char sign);

pseudofloat add_pseudo(pseudofloat first, pseudofloat second);

pseudofloat sub_pseudo(pseudofloat first, pseudofloat second);

void print_pseudo_representation(pseudofloat f);

void print_pseudo_as_float(const char *str, pseudofloat f);

pseudofloat div_pseudo(pseudofloat first, pseudofloat second);

pseudofloat mul_pseudo(pseudofloat a, pseudofloat b);

pseudofloat pseudo_from_int(int x, int rate_of_minus10);

pseudofloat double2pseudo(double x);

double pseudo2double(pseudofloat f);

pseudofloat Sin(pseudofloat x);

#endif  // FPU_H
