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
    domain: '(x=0 or x=1) and (y=0 or y=1) and n>=0',
    filter: function(x,y,n){ return ((x==0 || x==1) && (y==0 || y==1)) },
    check: function(x,y,n,constraints) {
               if(n<0 || x<0 || y<0) return null;
               var lower = precond(x,y,n);
               var upper = undefined;
               constraints.push(lower + '<=' + I(x,y,n));
               if(x==y) constraints.push('16*' + I(x,y,n) + '<=' +
                        '' + I(0,0,n+1) + '+' +
                        '3*' + I(0,1,n+1) + '+' +
                        '3*' + I(1,0,n+1) + '+' +
                        '9*' + I(1,1,n+1));
               if(x!=y) {
                   var upper = postcond(x,y,n);
                   constraints.push(I(x,y,n) + '<=' + upper);
               }
               return lower>upper? null : [lower, upper];
           },
    rule:  function(pre, post) {
               return AND(
                   pre + '<=I[x,y,n]',
                   IMP('x==y', '16*I[x,y,n] <= 9*I[1,1,n+1] + 3*I[1,0,n+1] + 3*I[0,1,n+1] + I[0,0,n+1]'),
                   IMP('x!=y', 'I[x,y,n]<=' + post)
               );
           }
};
