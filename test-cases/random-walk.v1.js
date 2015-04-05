module.exports = {
    /**
     * Program: n=0; while(0<x) { (x++)[p](x--); n++; }
     * Domain:  x>=0, n>=0
     * Param:   p=0.5
     * Rule: pre-condition <= I(x,n)
     *       0<x impl 2*I(x,n)<=I(x-1,n+1)+I(x+1,n+1)
     *       x==0 impl I(x,n) <= post-condition
     */
    name: 'random-walk-v1',
    vars:   'x,y,n',
    domain: '0<=x and 0<=y and 0<=n',
    check: function(x,y,n,constraints) {
               if(x<0 || y<0 || n<0) return null;
               var lower = precond(x,y,n);
               var upper = undefined;
               constraints.push(lower + '<=' + I(x,y,n));
               if(0<x) constraints.push('2*' + I(x,y,n) + '<=' + I(x+1,y,n-1) + '+' + I(x-1,y,n+1)); // rule 2
               if(x<=0) {
                   upper = postcond(x,y,n);
                   constraints.push(I(x,y,n) + '<=' + upper);
               }
               return lower>upper? null : [lower, upper];
           },
    rule: function(pre, post) {
              return AND(
                  'I[x,y,n]>=' + pre,
                  IMP('0<x', '2*I[x,y,n]<=I[x-1,y,n+1]+I[x+1,y,n+1]'),
                  IMP('x<=0','I[x,y,n]<=' + post)
              );
          },
};
