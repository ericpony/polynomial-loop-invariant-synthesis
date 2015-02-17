# Polynomial loop invariant synthesis
This node.js script tries to verify a simple loop (written in [pCGL](http://citeseerx.ist.psu.edu/viewdoc/summary?doi=10.1.1.42.1798)) annotated with a pre-expectation and a post-expectation. You will need node.js with ver ≥ 0.10 to run this script. Besides, the following tools must be accessible in the shell:
* GNU Octave
* Redlog
* Z3py

## Example

The following code generates a polynomial loop invariant for the random walk example (in folder `test-cases`) with degree ≤ 2 and program variables x, y and n. The existence of loop invariant verifies that when the loop terminates, the expected value of variable n is no less than the value of the expression x*(y-x) evaluated right before the loop.

    node ./main.js var=x,y,n deg=2 'pre=x*(y-x)' post=n test=random-walk
