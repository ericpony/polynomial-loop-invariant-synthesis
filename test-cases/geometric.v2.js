module.exports = {
    /**
     * Program: while(x>0){ (x--)[p](n++); }
     * Domain:  n>=0, y>=0, x>=0
     * Param:   p=0.5
     * Rule: pre-condition <= I(x,y,n)
     *       x>0  impl 2*I(x,y,n) <= I(x-1,y,n)+I(x,y,n+1)
     *       x<=0 impl I(x,y,n) <= post-condition
     */
    vars:   'x,y,n',
//  domain: '(x=0 or x=1)and y>=0 and n>=0',
    domain: 'x>=0 and y>=0 and n>=0',
//  filter: function(x,y,n){ return x==0 || x==1; },
    check: function(x,y,n,constraints) {
//             if(n<0 || y<0 || (x!=1 && x!=0)) return null;
               if(n<0 || y<0 || x<0) return null;
               var lower = precond(x,y,n);
               var upper = undefined;
               constraints.push(lower + '<=' + I(x,y,n));
               if(x>0) constraints.push('2*' + I(x,y,n) + '<=' + I(x-1,y,n) + '+' + I(x,y,n+1));
               if(x<=0) {
                   var upper = postcond(x,y,n);
                   constraints.push(I(x,y,n) + '<=' + upper);
               }
               return lower>upper? null : [lower, upper];
           },
    rule:  function(pre, post) {
               return AND(
                   pre + '<=I[x,y,n]',
                   IMP('x>0', '2*I[x,y,n]<=I[x-1,y,n]+I[x,y,n+1]'),
                   IMP('x<=1', 'I[x,y,n]<=' + post)
               );
           }
};
