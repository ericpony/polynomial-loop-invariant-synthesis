module.exports = {
    /**
     * Program: n=0; while(0<x && x<y) { (x++)[p](x--); n++; }
     * Domain:  x>=0, y>=x, n>=0
     * Param:   p=0.5
     * Rule: pre-condition <= I(x,y,n)
     *       0<x and x<y impl 2*I(x,y,n)<=I(x-1,y,n+1)+I(x+1,y,n+1)
     *       x==0 or x==y impl I(x,y,n) <= post-condition
     */
    vars:   'x,y,n',
    domain: '0<=x<=y and n>=0',
    check: function(x,y,n,constraints) {
               if(x<0 || y<0 || x>y || n<0) return null;
               var lower = precond(x,y,n);
               var upper = undefined;
               constraints.push(lower + '<=' + I(x,y,n));
               if(0<x && x<y) constraints.push('2*' + I(x,y,n) + '<=' + I(x+1,y,n+1) + '+' + I(x-1,y,n+1)); // rule 2
               if(x==0 || x==y) {
                   upper = postcond(x,y,n);
                   constraints.push(I(x,y,n) + '<=' + upper);
               }
               return lower>upper? null : [lower, upper];
           },
    rule: function(pre, post) {
              return AND(
                  'I[x,y,n]>=' + pre,
                  IMP(AND('0<x', 'x<y'), '2*I[x,y,n]<=I[x-1,y,n+1]+I[x+1,y,n+1]'),
                  IMP(OR('x<=0', 'x>=y'),'I[x,y,n]<=' + post)
              );
          }
}
