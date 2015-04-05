module.exports = {
    /**
     * Program: y>=0; x>=0; n=1; while(n!=0){ (x=x+y;n=0)[p](x=x-y;y=2*y); }
     * Domain:  n>=0
     * Param:   p=0.5
     * Rule: pre-condition <= I(x,y,n)
     *       n!=0 impl 2*I(x,y,n) <= I(x+y,y,0)+I(x-y,2*y,n)
     *       n==0 impl I(x,y,n) <= post-condition
     *
     * Example: var=x,y,n 'pre=y' 'post=x' test=martingale 'inv=x*[n==0]+y*[n<>0]'
     */
    vars:   'x,y,n',
    domain: 'y>=0 and n>=0',
    check: function(x,y,n,constraints) {
               if(n<0 || y<0) return null;
               var lower = precond(x,y,n);
               var upper = undefined;
               constraints.push(lower + '<=' + I(x,y,n));
               if(n!=0) constraints.push('2*' + I(x,y,n) + '<=' + I(x+y,y,0) + '+' + I(x-y,2*y,n));
               if(n==0) {
                   var upper = postcond(x,y,n);
                   constraints.push(I(x,y,n) + '<=' + upper);
               }
               return lower>upper? null : [lower, upper];
           },
    rule:  function(pre, post) {
               return AND(
                   pre + '<=I[x,y,n]',
                   IMP('n<>0', '2*I[x,y,n]<=I[x+y,y,0]+I[x-y,2*y,n]'),
                   IMP('n==0', 'I[x,y,n]<=' + post)
               );
           }
};
