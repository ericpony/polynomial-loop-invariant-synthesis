module.exports = {
        /**
         * Program: x=0; y=0; while(0<n){ (x=x)[p](x=x+n*n;y=y+n); n=n-1; }
         * Domain:  n>=0, x>=0; y>=0;
         * Param:   p=0.5
         * Rule: pre-condition <= I(x,y,n)
         *       n>0  impl 2*I(x,y,n) <= I(x+n*n,y+n,n-1) + I(x,y,n-1)
         *       n<=0 impl I(x,y,n) <= post-condition
         *
         * Example: var=x,y,n 'pre=y*(2*n+1)' 'post=3*x' test=random-square-sum2 theory=pasf skew=.65
         */
        vars:   'x,y,n',
        domain: 'x>=y and y>=0 and n>=0',
        check: function(x,y,n,constraints) {
                   if(n<0 || x<0 || x<y) return null;
                   var lower = precond(x,y,n);
                   var upper = undefined;
                   constraints.push(lower + '<=' + I(x,y,n));
                   if(n>0) constraints.push('2*' + I(x,y,n) + '<=' + I(x+n*n,y+n,n-1) + '+' + I(x,y,n-1));
                   if(n<=0) {
                       var upper = postcond(x,y,n);
                       constraints.push(I(x,y,n) + '<=' + upper);
                   }
                   return lower>upper? null : [lower, upper];
               },
        rule:  function(pre, post) {
                   return AND(
                       pre + '<=I[x,y,n]',
                       IMP('n>0', '2*I[x,y,n]<=I[x+n*n,y+n,n-1]+I[x,y,n-1]'),
                       IMP('n<=0','I[x,y,n]<=' + post)
                   );
               }
};
