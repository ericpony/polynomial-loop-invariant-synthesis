# Polynomial loop invariant synthesis
This node.js script tries to verify a flat probabilistic while-loop annotated with a pre-expectation and a post-expectation. You will need node.js with version ≥ 0.10 to run this script. Besides, the following tools must be accessible in the shell:
* Octave
* Redlog
* Z3py

## Example

Consider a probabilistic loop that models a symmetric bounded random walk (see `random-walk.js` in folder `test-cases` for details):

    n = 0; 
    while(0<x && x<y) { 
        (x++)[0.5](x--);
        n++; 
    }

The following command will generate a polynomial loop invariant with degree ≤ 2, pre-expectation `x*(y-x)`, and post-expectation `n` for the above loop, assuming that all variables range over non-negative integers:

    node main.js deg=2 'pre=x*(y-x)' post=n test=random-walk

The existence of loop invariant asserts that when the loop terminates, the *expected* value of program variable `n` (i.e. the post-expectation) is no less than the value of expression `x*(y-x)` (i.e. the pre-expectation) evaluated right before the loop is entered. 

Note that the output of this script is meaningful only if the provided loop terminates with probability 1. You may have to verify this condition manually.

## Todo

Implement a parser to generate test cases from annotated pCGL source code

## License

GPL v3
