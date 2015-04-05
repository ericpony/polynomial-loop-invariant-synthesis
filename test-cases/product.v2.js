module.exports = {
   /**
    * Program: while(n>0){ (x=x)[p](x++); (y=y)[p](y++); n--; }
    * Domain:  x>=0, y>=0, n>=0
    * Param:   p=0.5, skew=0.65
    * Rule: n>=2 impl pre-condition <= I(x,y,n)
    *       n>=1 impl 4*I(x,y,n) <= I(x+1,y+1,n-1)+I(x,y+1,n-1)+I(x+1,y,n-1)+I(x,y,n-1)
    *       I(x,y,0) <= post-condition
    *
    * Example: var=x,y,n 'pre=n*n' 'post=4*x*y' test=product2
    */
    vars:   'x,y,n',
    domain: 'x>=0 and y>=0 and n>=0',
    check: function(x,y,n,constraints) {
               if(x<0 || y<0 || n<0) return null;
               var lower = precond(x,y,n);
               var upper = undefined;
               if(n>=2) constraints.push(lower + '<=' + I(x,y,n));
               if(n>=1) constraints.push('4*' + I(x,y,n) + '<=' + I(x+1,y+1,n-1) + '+' + I(x+1,y,n-1)+ '+' + I(x,y+1,n-1)+ '+' + I(x,y,n-1));
               if(n==0) {
                   var upper = postcond(x,y,n);
                   constraints.push(I(x,y,n) + '<=' + upper);
               }
               return lower>upper? null : [lower, upper];
          },
    rule: function(pre, post) {
               return AND(
                   'I[x,y,0]<=' + post,
                   IMP('n>=2', pre + '<=I[0,0,n]'),
                   IMP('n>=1', '4*I[x,y,n] <= I[x+1,y+1,n-1]+I[x,y+1,n-1]+I[x+1,y,n-1]+I[x,y,n-1]')
               );
          }
};
