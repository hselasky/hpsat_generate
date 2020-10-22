# hpsat_generate
3-SAT CNF file generator for testing SAT solvers

## Example 1: Solve multiplication of two variables which is equal to 15
hpsat_generate -f 6 -b 8 -v 15 | picosat

## Example 2: Solve addition of two variables which is equal to 15
hpsat_generate -f 1 -b 8 -v 15 | picosat
