# hpsat_generate
3-SAT CNF file generator for testing SAT solvers

## Dependencies
- LibGMP

## Example 1: Solve multiplication of two 4-bit variables which is equal to 15
hpsat_generate -f 6 -b 8 -v 15 | picosat | hpsat_generate -f 6 -b 8 -p

## Example 2: Solve addition of two 8-bit variables which is equal to 15
hpsat_generate -f 1 -b 8 -v 15 | picosat | hpsat_generate -f 1 -b 8 -p

## Example 3: Solve custom expression
hpsat_generate -i "(a & b)|(a & c)|(b & c)" | picosat --all | hpsat_generate -i "abc" -p
