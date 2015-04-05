module.exports = {
    /**
     * Program: while(n>0){ {x=x+n}[p]{x=x+y}; n--; }
     * Domain:  x>=0,y>=0,n>=0
     * Param:   p=0.25
     * Rule: pre-condition <= I(x,y,n)
     *       n>0  impl 2*I(x,y,n) <= I(x+n,y,n-1)+I(x+y,y,n-1)
     *       n<=0 impl I(x,y,n) <= post-condition
     */
    vars:   'x,y,n',
    domain: 'x>=0 and y>=0 and n>=0',
    check: function(x,y,n,constraints) {
               if(n<0 || y<0 || x<0) return null;
               var lower = precond(x,y,n);
               var upper = undefined;
               constraints.push(lower + '<=' + I(x,y,n));
               if(n>0) constraints.push('4*' + I(x,y,n) + '<=' + I(x+n,y,n-1) + '+3*' + I(x+y,y,n-1));
               if(n<=0) {
                   var upper = postcond(x,y,n);
                   constraints.push(I(x,y,n) + '<=' + upper);
               }
               return lower>upper? null : [lower, upper];
           },
    rule:  function(pre, post) {
               return AND(
                   pre + '<=I[x,y,n]',
                   IMP('n>0', '4*I[x,y,n]<=I[x+n,y,n-1]+3*I[x+y,y,n-1]'),
                   IMP('n<=0', 'I[x,y,n]<=' + post)
               );
           }
};
