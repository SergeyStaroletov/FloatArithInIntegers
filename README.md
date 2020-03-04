# FPU Arithmetics In Integers
Floating point operations implemented in software way using only integers (32 bit). 
- add
- sub
- mul
- div
- cos
- sin

Not very strict, just for education.

Negatives are supported.
NAN and +=Inf are not implemented now. 

Tests provided.
May be useful for implementing FPU computaions for integer only processors. 

The goal of the project is to write a C code for floating point fpu and then port it to Promela/SPIN language to be able to verify CPSs. See notes in http://spinroot.com/spin/Man/float.html. This project is to solve this. 

[![DOI](https://zenodo.org/badge/154152198.svg)](https://zenodo.org/badge/latestdoi/154152198)

Publication in SPIN 2019: https://link.springer.com/chapter/10.1007/978-3-030-30923-7_11
