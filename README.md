# Polynomial loop invariant synthesis
This node.js script tries to verify a flat probabilistic while-loop (written in [pCGL](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.42.1798)) annotated with a pre-expectation and a post-expectation. You will need node.js with ver ≥ 0.10 to run this script. Besides, the following tools must be accessible in the shell:
* GNU Octave
* Redlog
* Z3py

## Example

The following command generates a polynomial loop invariant for the random walk example (see `random-walk.js` in folder `test-cases`) with degree ≤ 2 and variables `x`, `y` and `n`. In this case, the existence of loop invariant asserts that when the loop terminates, the expected value of program variable `n` is no less than the value of the expression `x*(y-x)` evaluated before the loop is entered and after the variables are initialized. 

    node ./main.js var=x,y,n deg=2 'pre=x*(y-x)' post=n test=random-walk

Note that this script doesn't check the termination of the test case. The output of the script is meaningful only if the loop terminates almost surely, which has to be verified manually.
