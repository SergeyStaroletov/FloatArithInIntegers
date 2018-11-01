# FPU Arithmetics In Integers
Floating point operations implemented in software way using only integers (32 bit). 

- add
- sub
- mul
- div
- cos
- sin

Negatives are supported.
NAN and +=Inf are not implemented now. 

Tests provided.
May be useful for implementing fpu computaions for integer only processors. 

The goal of the project is to write a C code for floating point fpu and than port it to Promela/Spin language to be able to verify CPSs. See notes in http://spinroot.com/spin/Man/float.html. This project is to solve this. 
