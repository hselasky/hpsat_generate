# hpsat_generate
3-SAT CNF generator for testing SAT solvers

## Dependencies
- LibGMP

## Example 1
<pre>
# Solve multiplication of two 4-bit variables which is equal to 15
hpsat_generate -f 6 -b 8 -v 15 | picosat | hpsat_generate -f 6 -b 8 -p
</pre>

## Example 2
<pre>
# Solve addition of two 8-bit variables which is equal to 15
hpsat_generate -f 1 -b 8 -v 15 | picosat | hpsat_generate -f 1 -b 8 -p
</pre>

## Example 3
<pre>
# Solve custom expression
hpsat_generate -i "(a & b)|(a & c)|(b & c)" | picosat --all | hpsat_generate -i "abc" -p
</pre>

