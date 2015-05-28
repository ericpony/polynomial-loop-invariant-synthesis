# Polynomial loop invariant synthesis
This node.js script tries to verify a flat probabilistic while-loop annotated with a pre-expectation and a post-expectation. You will need node.js with ver ≥ 0.10 to run this script. Besides, the following tools must be accessible in the shell:
* Octave
* Redlog
* Z3py

## Example

Consider a probabilistic loop that models a symmetric bounded random walk:

    n = 0; 
    while(0<x && x<y) { 
        (x++)[0.5](x--); 
        n++; 
    }

For this loop (see `random-walk.js` in folder `test-cases`), the following command generates a polynomial loop invariant with degree ≤ 2 and variables `x`, `y` and `n`:

    node main.js deg=2 'pre=x*(y-x)' post=n test=random-walk

The existence of loop invariant asserts that when the loop terminates, the *expected* value of program variable `n` is no less than the value of the expression `x*(y-x)` evaluated right before the loop is entered. Note that the output of this script is meaningful only if the loop terminates with probability 1, which has to be verified separately (e.g., by finding a loop variant).

## Todo

Implement a parser to generate test cases from annotated pCGL source code

## License

GPL v3
