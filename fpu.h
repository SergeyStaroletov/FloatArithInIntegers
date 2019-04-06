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

pseudofloat subTwoFloat(pseudofloat first, pseudofloat second, char sign);

pseudofloat addTwoFloat(pseudofloat first, pseudofloat second, char sign);

pseudofloat addFloat(pseudofloat first, pseudofloat second);

pseudofloat subFloat(pseudofloat first, pseudofloat second);

void printFloatRepresentation(pseudofloat f);

void printFloatAsFloat(const char *str, pseudofloat f);

pseudofloat divFloat(pseudofloat first, pseudofloat second);

pseudofloat mulFloat(pseudofloat a, pseudofloat b);

pseudofloat floatFromInt(int x, int rate_of_minus10);

pseudofloat realDouble2Float(double x);

double float2RealDouble(pseudofloat f);

pseudofloat sinus(pseudofloat x);

pseudofloat cosinus(pseudofloat x);

#endif  // FPU_H
