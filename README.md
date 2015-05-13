# Polynomial loop invariant synthesis
This node.js script tries to verify a flat probabilistic while-loop written in [pCGL](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.42.1798), the probabilistic Guarded Command Language, and annotated with a pre-expectation and a post-expectation. You will need node.js with ver ≥ 0.10 to run this script. Besides, the following tools must be accessible in the shell:
* Octave
* Redlog
* Z3py

## Example

Consider a pCGL loop which models a symmetric bounded random walk  (see `random-walk.js` in folder `test-cases`):

    n = 0; 
    while(0<x && x<y) { 
        (x++)[0.5](x--); 
        n++; 
    }

The following command generates for the above loop a polynomial loop invariant with degree ≤ 2 and variables `x`, `y` and `n`:

    node main.js var=x,y,n deg=2 'pre=x*(y-x)' post=n test=random-walk

The existence of loop invariant asserts that when the loop terminates, the expected value of program variable `n` is no less than the value of the expression `x*(y-x)` evaluated right before the loop is entered. Note that the output of this script is meaningfult only if the loop terminates with probability 1, which has to be verified separately (e.g., by finding a loop variant).

## Todo

Implement a parser to generate test cases from annotated pCGL source code

## License

GPL v3
