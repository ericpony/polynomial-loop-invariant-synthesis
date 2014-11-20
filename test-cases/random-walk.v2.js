module.exports = {
    /**
     * Program: x=0; y=0; z=0; while(y-x+1<n) { (z++)[p](z--); if(z>y) y=z; if(z<x) x=z; }
     * Domain:  n>=2, x<=y
     * Param:   p=0.5
     * Rule: pre-condition <= I(x,y,z,n)
     */
    domain: '0<=x<=y and n>=0',
    check: function(x,y,n,constraints) {
               if(x<0 || y<0 || x>y || n<0) return null;
               var lower = precond(x,y,n);
               var upper = undefined;
               constraints.push(lower + '<=' + I(x,y,n));
               if(0<x && x<y) constraints.push('2*' + I(x,y,n) + '<=' + I(x+1,y,n-1) + '+' + I(x-1,y,n+1)); // rule 2
               if(x==0 || x==y) {
                   upper = postcond(x,y,n);
                   constraints.push(I(x,y,n) + '<=' + upper);
               }
               return lower>upper? null : [lower, upper];
           },
    rule: function(pre, post) {
              return AND(
                  'I[x,y,n]>=' + pre, // Rule 1.1
                  IMP(AND('0<x', 'x<y'), '2*I[x,y,n]<=I[x-1,y,n+1]+I[x+1,y,n+1]'),  // Rule 2
                  IMP(OR('x<=0', 'x>=y'),'I[x,y,n]<=' + post)
              ); // TODO: Generate rule AST from a text file
          }
};
