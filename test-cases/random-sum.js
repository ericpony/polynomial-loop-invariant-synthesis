module.exports = {
   /**
     * Program: x=0; while(0<n){ (x=x)[p](x=x+n); n=n-1; }
     * Domain:  n>=0, x>=0
     * Param:   p=0.5
     * Rule: pre-condition <= I(x,n)
     *       n>0  impl 2*I(x,n) <= I(x+n,n-1) + I(x,n-1)
     *       n<=0 impl I(x,n) <= post-condition
     */
    vars:   'x,y,n',
    domain: 'x>=0 and n>=0',
    check: function(x,n,constraints) {
               if(n<0 || x<0) return null;
               var lower = precond(x,n);
               var upper = undefined;
               constraints.push(lower + '<=' + I(x,n));
               if(n>0) constraints.push('2*' + I(x,n) + '<=' + I(x+n,n-1) + '+' + I(x,n-1));
               if(n<=0) {
                   var upper = postcond(x,n);
                   constraints.push(I(x,n) + '<=' + upper);
               }
               return lower>upper? null : [lower, upper];
           },
    rule:  function(pre, post) {
               return AND(
                   pre + '<=I[x,n]',
                   IMP('n>0', '2*I[x,n]<=I[x+n,n-1]+I[x,n-1]'),
                   IMP('n<=0','I[x,n]<=' + post)
               );
           }
};
