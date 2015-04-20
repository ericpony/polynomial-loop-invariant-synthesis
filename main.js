var fs = require('fs');
var sh = require("execSync");
var colors = require('colors');

var Verbose = {
  QUIET:      -1,
  NORMAL:      0,
  INFORMATIVE: 1,
  DEBUG:       10
};
var Settings = {
  /**
   * theory: set the theory in which quantifier elimination is performed.
   * The value can be either 'pasf' (Presburg arithematics)
   * or 'ofsf' (approximation of real number arithematics).
   * exec: set the command to run RedLog
   */
  redlog: { theory: 'ofsf' },
  /**
   * lower: lowerbound of the sampling points
   * upper: upperbound of the sampling points
   * skewness: parameter to weight the sampling points
   * When skewness = 1, sampling are made uniformly from the sample space.
   * As skewness approaches zero, the result of the sampling tends to
   * determine more constraints. However, the benefit comes at the cost of
   * longer sampling time and lower possibility to spot a Lagrange basis
   * in a given timeout.
   */
  lagrange: { lower: 0, upper: 3, skewness: .65 },
  /**
   * Set the evaluators of numerical expressions.
   * Currently, three evaluators are supported:
   * 'mathomatic', 'javascript', and 'python'.
   */
  symbolic: { evaluator: 'javascript' },
  max_num_sample_verification: 100,
  verbose_level: 1,
  reduce_exec: 'redpsl',
  octave_exec: 'octave -qf --no-window-system'
};

function I(x, y, n) {
  if(n!==undefined)
    return 'I[' + x + ',' + y + ',' + n + ']';
  if(y!==undefined)
    return 'I[' + x + ',' + y + ']';
  return 'I[' + x + ']';
}
function pt_str(pt)  { return '[' + pt.split(' ').map(function(p){ return +p>=0 ? ' '+p : p }).join(' ') + ' ]' }
function round(x, n) { return +x.toFixed(n ? n:5); }
function isInt(x)    { return (typeof x==='number' && (x%1)===0); }
function gcd(a, b)   { return b ? gcd(b, a % b) : a; }
function lcm(a, b)   { return !a||!b ? 0 : a*b/gcd(a,b); }
function bool_val(val) {
  var sval = val.toString().toLowerCase();
  return (sval=='true'||sval=='yes'||sval=='1'||sval=='t') ? true : (sval=='false'||sval=='no'||sval=='0'||sval=='f') ? false : Boolean(val);
}

/**
 * This is the multiply-with-carry (MWC) random generator with
 * a pretty long period. Adapted from Wikipedia, see
 * http://en.wikipedia.org/wiki/Random_number_generation#Computational_methods
 */
Math.seed = function(s) { // Takes any integer
  var m_w = s;
  var m_z = 987654321;
  var mask = 0xffffffff;
  return function() {
    m_z = (36969 * (m_z & 65535) + (m_z >> 16)) & mask;
    m_w = (18000 * (m_w & 65535) + (m_w >> 16)) & mask;
    var result = ((m_z << 16) + m_w) & mask;
    result /= 4294967296;
    // return a number between 0 (inclusive) and 1.0 (exclusive),
    // just like Math.random() does.
    return result + 0.5;
  }
}

/* Use a fixed seed to obtain deterministic results */
Math.random = Math.seed(Math.round(Math.seed(42)()*10000));

Object.prototype.toString = function() {
  var str = '';
  for(var i=1;;i++) {
    var name = 'I_' + i + '_';
    if(this[name]===undefined) break;
    str += 'I_' + i + '=' + this[name].toString().cyan + "\t";
  }
  return str;
}
String.prototype.insertAt = function(str, index) {
  return this.substr(0, index) + str + this.substr(index);
};

/* Profiler */
var Profiler = (function() {
  var _timeout = 0;
  var _timers  = {};
  return {
    timers:   {},
    counters: {},
    tick:  function(mark) {
      if(_timers[mark]) this.stop(mark); else this.start(mark);
    },
    start: function(mark) {
      _timers[mark] = process.hrtime();
    },
    stop:  function(mark) {
      var elapsed_time = this.timeElapsed(mark);
      this.timers[mark] = (this.timers[mark] || 0) + elapsed_time;
      _timers[mark] = false;
    },
    count: function(mark) {
      this.counters[mark] = (this.counters[mark]||0) + 1
    },
    reset: function(timeout) {
      _timeout      = timeout;
      _timers       = {};
      this.timers   = {};
      this.counters = {};
    },
    exec:  function(command) {
      var timeout = this.timeLeft();
      if(timeout<=0) throw 'timeout';
      //log(('Time remains: ' + timeout.toFixed(2)).yellow);
      var command = 'timeout ' + timeout.toFixed(2) + 's ' + command;
      var res = sh.exec(command);
      if(res.code==124) // aborted by timer
        throw 'timeout';
      else
        return res.stdout;
    },
    timeElapsed:  function(mark) {
      if(!_timers[mark]) throw new Error('Should start the timer first: "' + mark + '"');
      var elapsed = process.hrtime(_timers[mark]);
      elapsed = elapsed[0] + elapsed[1]*1e-9;
      return elapsed;
    },
    timeLeft: function(mark) {
      return _timeout - this.timeElapsed('Total execution time');
    },
    expired:  function() {
      return this.timeLeft()<=0;
    }
  };
})();

/* Sample class */
var Sample = function(point, lowerbound, upperbound, constraints) {
  this.point = point;
  this.diff  = (upperbound!==undefined && lowerbound!==undefined) ? upperbound-lowerbound : undefined;
  this.lower = lowerbound;
  this.upper = upperbound;
  this.constraint = '(' + constraints.join(') and (') + ')';
}
Sample.prototype.toString = function () {
  return '(' + this.point + ')';
}

/* Node class */
var Node = function() {
  var nodes = [];
  for(var i=0; i<arguments.length; i++) nodes.push(arguments[i]);
  this.children = nodes;
}
Node.create = function(name) {
  var subclass = function() { Node.apply(this, arguments) };
  subclass.prototype = Object.create(Node.prototype); // keeps the proto clean
  subclass.prototype.constructor = subclass; // repair the inherited constructor
  subclass.prototype.name = name;
  GLOBAL[name.toUpperCase()] = function() {
    var obj = {};
    obj.__proto__ = subclass.prototype;
    subclass.apply(obj, arguments);
    return obj;
  };
  return subclass;
}

/* Make subclasses of Node behave like algebraic data types */
var Not = Node.create('Not'), And = Node.create('And'), Or = Node.create('Or'), Imp = Node.create('Imp');

/* Represent the node in the Z3 format */
Node.to_z3_formula = function(string_parser) {
  return function parse(node) {
    switch(node.constructor) {
      case Or:
        var sub_expr = node.children.map(parse).join(', ');
        /* At least one of the arguments must be a Z3 expression */
        if(!/[()a-zA-Z]/.test(sub_expr))
          return eval('(' + sub_expr.replace(/,/g, ')||(') + ')') ? 'True' : 'False';
        else
          return 'Or(' + sub_expr + ')';          
      case And:
        var sub_expr = node.children.map(parse).join(', ');
        /* At least one of the arguments must be a Z3 expression */
        if(!/[()a-zA-Z]/.test(sub_expr))
          return eval('(' + sub_expr.replace(/,/g, ')&&(') + ')') ? 'True' : 'False';
        else
          return 'And(' + sub_expr + ')';
      case Imp:    return 'Implies(' + parse(node.children[0]) + ', ' + parse(node.children[1]) + ')';
      case Not:    return 'Not(' + parse(node.children[0]) + ')';
      case String: return string_parser(node);
      default:     return node.toString();
    }
  }
}

/* Represent the node in the RedLog format */
Node.to_redlog_formula = function(string_parser) {
  return function parse(node) {
    switch(node.constructor) {
      case Or:     return '(' + node.children.map(parse).join(') or (') + ')';
      case And:    return '(' + node.children.map(parse).join(') and (') + ')';
      case Imp:    return '(' + parse(node.children[0]) + ') impl (' + parse(node.children[1]) + ')';
      case Not:    return 'not (' + parse(node.children[0]) + ')';
      case String: return string_parser(node.replace(/==/g,'=').replace(/!=/g,'<>'));
      default:     return node.toString();
    }
  }
}
Node.prototype.toString = function() { return this.name + '(' + this.children + ')' }

function log(msg, level) {
  if(!level) level = 0;
  if(!msg) msg = '';
  if(level<=Settings.verbose_level) console.log(msg);
}
function writeToFile(string, filename) {
  var fd = fs.openSync(filename, 'w');
  var buffer = new Buffer(string);
  fs.writeSync(fd, buffer, 0, buffer.length, 0);
  fs.closeSync(fd);
}

function verify_sample(vars) {
  vars.push([]);
  var bounds = testcase.check.apply(null, vars);
  var constraints = vars.pop();
  if(!bounds) return null;

  var lower = bounds[0];
  var upper = bounds[1];
  if(upper==lower) constraints = [I.apply(null, vars) + '==' + upper];
  return new Sample(vars.join(' '), lower, upper, constraints);
}

function verify_sample_v0(x,y,n) {
  var constraints = [];

  if(!isInt(x) || !isInt(y) || !isInt(n)) return null;

  Profiler.tick('verify_sample');
  var bounds = testcase.check(x,y,n,constraints);
  Profiler.tick('verify_sample');

  if(!bounds) return null;

  var lower = bounds[0];
  var upper = bounds[1];
  if(upper==lower) constraints = [I(x,y,n) + '==' + upper];
  return new Sample(x+' '+y+' '+n, lower, upper, constraints);
}

function build_sample_space(num_vars, num_samples) {
  Profiler.tick('Building sample space');
  var samples = [];
  var vars = [];
  (function uniform_sampling(i) {
    for(var val=LOWERBOUND; val<=UPPERBOUND; val++) {
      vars[i] = val;
      if(i>=num_vars-1) {
        var sample = verify_sample(vars);
        if(sample!==null && (sample.upper!==undefined || sample.lower!==undefined))
          samples.unshift(sample);
      }else
        uniform_sampling(i+1);
    }
  })(0);
  if(samples.length<num_samples)
    throw 'Unable to build large enough sample space: ' + samples.length + ' probed, ' + num_samples + ' needed.'
          + "\n\n" + 'Hint: try to adjust parameter "lower" and "upper". Current values: (' + LOWERBOUND + ', ' + UPPERBOUND + ')';

  samples = samples.sort(function(a,b) {
    return (a.diff===undefined||b.diff===undefined) ? -(Math.abs(a.diff||b.diff)||1) :(a.diff-b.diff);
  });
  Profiler.tick('Building sample space');
  return samples;
}

function compute_standard_basis(num_samples, monomials, sample_space) {
  var basis = [];
  for(var i=0; i<monomials.length; i++)
    for(var j=0; j<monomials.length; j++)
      basis.push(i==j? 1 : 0);
  var point_weights = sample_space.map(function(s,i) {
      return [i, s.point.split(' ').reduce(function(a,b){ return a + (b=='1' || b=='0' ? 0 : 1) }, 0)]
    }).sort(function(a,b){ return a[1] - b[1] });
  var samples = [];
  for(var i=0; i<num_samples; i++) samples.push(sample_space[point_weights[i][0]]);
  return [basis, samples];
}
/**
 *  Compute a Lagrange basis by random sampling.
 *  Note that sampling points are assumed to be integers.
 */
function compute_lagrange_basis(num_samples, monomials, sample_space) {

  var detVandermonde = 0;
  var N =  '[' + monomials.join('; ') + ']';

  function lagrange(samples) {
    var S = '[' + samples.join('; ') + ']';
    var command = Settings.octave_exec + ' ./lagrange.m "' + DEGREE + '" "' + num_vars + '" "' + num_samples + '" "' + S + '" "' + N + '"';
    var basis = Profiler.exec(command + ' 2>/dev/null');
    if(!/^singular/.test(basis)) {
      basis = basis.split(/ +/);
      detVandermonde = +basis.shift(); /* determinant of the Vandermonde matrix */
      basis.pop(); /* discard "\n" */
      if(isNaN(detVandermonde) || !detVandermonde || basis.length != num_samples*num_samples) {
        log("Basis\n".bold + basis);
        log("Command\n".bold + command);
        log("Result\n".bold + Profiler.exec(command));
        throw 'Invalid Lagrange basis!';
      }

      var detV = Math.abs(detVandermonde);
      var sign = detVandermonde>0 ? 1 : -1;
      basis = basis.map(function(b) {
        b = +b;
        if(b==0) return 0;
        b = b * sign;
        var a = Math.abs(gcd(b, detV));
        /* It must be hold that sign(b)==sign(b/a) */
        var n = b/a, m = detV/a;
        if(m==1) return n;
        var val = n + '/' + m;
        if(!USE_APPROX_ROUNDING) return val;

        val = round(eval(val), 3).toString();
        var dot = val.indexOf('.');
        if(dot<0) return val;
        var n_digits = val.length - dot - 1;
        var base = '1';
        while(n_digits-->0) base += '0';
        val = val.replace('.','') + '/' + base;
        return val[0]=='-' ? val.replace(/^\-0+/,'-') : val.replace(/^0+/,'');
      });
      var result = basis;
    }else
      var result = null;
    return result;
  }
  var point_weights = sample_space.map(function(s) {
    var weight = Math.pow(1-SKEWNESS, s.diff===undefined ? 1/(1-SKEWNESS) : s.diff);
    //var weight = Math.pow(1-SKEWNESS, s.diff===undefined ? 1/(1-SKEWNESS)/(1-SKEWNESS) : s.diff);
    log(pt_str(s.point) + ' ' + s.constraint + ' ' + round(weight,4).toString().cyan, Verbose.INFORMATIVE+1);
    return [s.point, weight];
  });
  var _points  = point_weights.map(function(s){ return s[0] });
  var _weights = point_weights.map(function(s){ return s[1] });
  var _weight = _weights.reduce(function(a,b){ return a+b });
  var samples  = new Array(num_samples);
  var indices  = new Array(num_samples);

  while(true) {
    Profiler.count('No. of basis searchs');
    var weight  = _weight;
    var weights = _weights.slice(0);
    var points  = _points.slice(0);
    var _indices = weights.map(function(a,i){ return i });
    var rands = [];
    for(var i=0; i<samples.length; i++) {
      var rand = Math.random();
      var mass = rand*weight, ptr = -1;
      rands.push(rand);
      while(mass>0 && ptr<weights.length-1) mass -= weights[++ptr];
      samples[i] = points[ptr];
      indices[i] = _indices[ptr];
      weight -= weights[ptr];
      points.splice(ptr, 1);
      weights.splice(ptr, 1);
      _indices.splice(ptr, 1);
    }
    var basis = lagrange(samples);
    if(basis) {
      log("Rand\n".bold + '['+rands.join(',')+']', Verbose.INFORMATIVE);
      samples = indices.map(function(i){ return sample_space[i] });
      return [basis, samples];
    }
    if(Profiler.expired()) break;
   }
   log(('[Error] Cannot find a valid sampling within timeout.').bold.red);
   throw 'timeout';
}

function refine_constraint(coeff_list, constraint, constraints) {
  Profiler.tick('Guessing coefficients');
  Profiler.count('No. of refinements');

  var z3_formula = constraint.replace(/ *and */g,',');
  z3_formula = "from z3 import *\n" + coeff_list.map(function(c){ return c + ' = Int(\'' + c + '\')'; }).join("\n")
         + "\ns = Solver()\n\ns.add(And(" + z3_formula + "))\n\n";
  constraints.forEach(function(c){ z3_formula += c + "\n" });
  z3_formula += "s.check()\nprint s.model()";

  var result = Profiler.exec('python -c "' + z3_formula + '" 2>&1');
  Profiler.tick('Guessing coefficients');

  /* sat */
  if(result[0]=='[') {
    result = '{' + result.substr(1, result.length-3).replace(/\n/g,'').replace(/ = /g,':') + '}';
    return result;
  }
  /* unsat or error */
  log("Z3 Error:\n".bold.red + result, Verbose.DEBUG);
  return '';
}

function build_template(num_samples, monomials, basis) {
  var monomials = monomials.map(function(degs) {
    return degs.reduce(function(term, deg, i) {
      switch(deg) {
        case 0:  return term;
        case 1:  return term + '*($' + (i+1) + ')';
        default: return term + '*($' + (i+1) + ')^' + deg;
      }
    }, '');
  });
  var terms = [];
  for(var i=0; i<num_samples; i++) {
    var term = [];
    for(var j=0; j<num_samples; j++) {
      var coeff = basis[num_samples*i + j];
      if(coeff) term.push('(' + coeff + ')' + monomials[j]);
    }
    terms[i] = term.join('+');
  }
  return terms.map(function(t,i){ return 'I_' + (i+1) + '_*(' + t + ')' }).join('+');
}

function bind_coeff(coeff, expr) {
  for(var name in coeff) {
    if(coeff[name]!=0) {
      expr = expr.replace(new RegExp(name,'g'), coeff[name]);
      continue;
    }
    while(true) {
      var pos = expr.indexOf(name);
      if(pos<0) break;
      var left_paren_pos = expr.indexOf('(', pos);
      var right_paren_pos = find_right_paren_pos(expr, left_paren_pos);
      expr = expr.substring(0, pos) + '0' + expr.substring(right_paren_pos+1);
    }
  }
  return expr;
}

function find_right_paren_pos(str, start) {
  if(str[start]!='(') return str;
  var c = 1, ptr = start+1;
  while(c>0 && ptr<str.length) {
    switch(str[ptr]) {
      case '(': c++; break;
      case ')': c--; break;
    }
    ptr++;
  }
  return ptr - 1;
}

/* substitute all sub-expression by thir values, e.g., (1+2) by 3 */
function simplify(expr) {
  var expr1 = expr;
  do {
    expr = expr1;
    expr1 = expr1.replace(/\(([\d\+\-]+)+\)/g, function(a,b) { return eval(b) });
  }while(expr!=expr1);
  expr = expr.replace(/\+0/g,'').replace(/0\+/g,'');
  return expr;
}

/* eliminate denominator of numbers in formula */
function normalize(coeff, expr, has_var, op) {
  if(!op) {
    var ops = ['<=','>=','<','>','=='];
    for(var i=0; i<ops.length; i++) {
      var expr1 = normalize(coeff, expr, has_var, ops[i]);
      if(expr1) return expr1;
    }
    return expr;
  }
  if(expr.indexOf(op)==-1) return '';

  log("EXPR (before): ".bold + expr, Verbose.DEBUG);

  /* Remove terms with zero-valued coefficients from expr (buggy) */ 
  //for(var name in coeff) {
  //  if(coeff[name]!=0) continue;
  //  while(true) {
  //    var pos = expr.indexOf(name);
  //    if(pos<0) break;
  //    var left_paren_pos = expr.indexOf('(', pos);
  //    var right_paren_pos = find_right_paren_pos(expr, left_paren_pos);
  //    expr = expr.substring(0, pos) + '0' + expr.substring(right_paren_pos+1);
  //  }
  //}
  //log("EXPR (zero coeff removed): ".bold + expr, Verbose.DEBUG);
  

  /* substitute all sub-expression by their values (for splitting) */
  expr = expr.replace(/\(([\d\+\-]+)\)/g, function(a,b) { return eval(b) });

  log("EXPR (sub-exp removed): ".bold + expr, Verbose.DEBUG);

  expr = expr.replace(/\(\(([\-\d\/]+)\)\)\*\*(\d+)/g, function(a, frac, deg) {
    var t = frac; for(var i=1; i<=+deg; i++) t+= '*(' + frac + ')'; return t;
  })

  log("EXPR (fraction power removed): ".bold + expr, Verbose.DEBUG);

  /* sides[0] is the LHS, sides[1] is the RHS */
  var sides = expr.split(op);

  /* compute the lcm of all denominators */
  var $lcm = 1;
  sides[0].split('+').forEach(function(t){ (t.match(/\/(\d+)/g)||[]).forEach(function(d){ $lcm = lcm($lcm, +d.substr(1)) })});
  sides[1].split('+').forEach(function(t){ (t.match(/\/(\d+)/g)||[]).forEach(function(d){ $lcm = lcm($lcm, +d.substr(1)) })});
  log("LCM: ".bold + $lcm.toString().cyan, Verbose.DEBUG);

  /* only handle the non-trivial case */
  if($lcm>1) {
    function reduce(expr) {
      var expr1 = '', start, last = 0, end = -1;
      var regex = new RegExp(/I_\d+_/g);
      while(true) {
        var rr = regex.exec(expr);
        if(!rr) break;
        start = rr.index + rr[0].length + 1;
        end = find_right_paren_pos(expr, start);
        expr1 += expr.substring(last, rr.index);

        var token = expr.substring(start+1, end); /* not including parentheses */

        if(has_var) {
          /* REMARK: We assume at most one fraction in each term */
          var num_reduced = 0;
          token = '(' + token.replace(/(\d+)\/(\d+)/g, function(a, num, den){ num_reduced++; return $lcm*+num/+den }) + ')';
          //if(fraction products detected)
          //  throw new Error('Sorry! I don\'t handle multiplications of fractions by now!');
          if(num_reduced==0)
            token = $lcm + '*' + token;
        }else {
          token = $lcm + '*(' + token + ')';
          switch(Settings.symbolic.evaluator) {
            case 'python':
              token = token.replace(/\/(\d+)/g, '\/$1.0');
              var command = 'echo -n $(python -c "print ' + token + '" | sed \'s/\\..*$//\')';
              token = Profiler.exec(command);
              break;
            case 'javascript':
              token = token.replace(/\(([\d\-]+)\)\*\*(\d+)/g, function(a,b,c){ return 'Math.pow('+b+','+c+')' })
              token = token.replace(/\(\(([^()]+)\)\)\*\*(\d+)/g, function(a,b,c){ return 'Math.pow('+b+','+c+')' })
              log("Token (JSified): ".bold + token, Verbose.DEBUG);
              token = round(eval(token),0); /* token should be an integer after reduction */
              break;
            case 'mathomatic':
              var command = 'echo -n $(mathomatic -ceq "' + token + '" | tail -n1 | sed \'s/^.* \\([^ ][^ ]*\\)$/\\1/\')';
              token = Profiler.exec(command);
              break;
            default: throw 'Invalid mode: ' + Settings.symbolic.evaluator;
          }
        }

        if(token!='0')
          expr1 += rr[0] + '*(' + token + ')';
        else
          expr1 += '0';
        regex.lastIndex = last = end + 1;
      }
      expr1 += expr.substring(end + 1);

      if(expr1 && end<0) {
        log('Scalar: '.bold + $lcm + '*(' + expr1 + ')', Verbose.DEBUG);
        expr1 = $lcm + '*(' + expr1 + ')';
        if(!has_var) expr1 = eval(expr1);
      }
      return expr1;
    }
    var lhs = reduce(sides[0]);
    var rhs = reduce(sides[1]);
    expr = lhs + op + rhs;
  }
  log("EXPR (after): ".bold + expr + "\n", Verbose.DEBUG);
  return expr;
}


var test_coeff = (function() { 
  var _regex, _coeff;

  function parser(point) {
    var values = point.split(' ');
    return function(rule0) {
      /* replace program variables by values in the rules */
      for(var i=0; i<var_names.length; i++)
        rule0 = rule0.replace(new RegExp(var_names[i], 'g'), values[i]);
      /* replace e.g. --2 by 2 */
      rule0 = rule0.replace(/--/g,'');
      log('Rule: ' + rule0, Verbose.INFORMATIVE+1);
      var rule1 = rule0.replace(_regex,
        function(a,b,c,d) {
          var g = arguments;
          var args = var_names.reduce(function(args, j, i){ args.push(g[i+1]); return args; }, []);
          var poly_expr = evaluate_poly3(args);
          return poly_expr; /* is an expression */
        });
      return normalize(_coeff, rule1, false);
    }
  }

  function test_point(index, point) {
    log(('Checking Point ' + index + ' : ').bold + '(' + point.cyan +') ...', Verbose.INFORMATIVE+1);
    Profiler.count('No. of random tests');

    var new_constraint = 's.add(' + Node.to_z3_formula(parser(point))(rule) + ')';
    var ruleZ3 = new_constraint;
    for(var name in _coeff) {
      ruleZ3 = ruleZ3.replace(new RegExp(name,'g'), _coeff[name]);
    }
    var z3_prog = "from z3 import *\ns = Solver()\n" + ruleZ3 + "\nprint s.check()";
    var result = Profiler.exec('python -c "' + z3_prog + '" 2>&1');
    var passed = /^sat/.test(result);

    /* Abort if Z3 outputs error messages */
    if(!passed && !/^unsat/.test(result)) throw new Error(result);

    log('Point (' + point.cyan + ') ' + (passed? 'passed'.green : 'failed'.red), Verbose.INFORMATIVE);

    return !passed ? new_constraint : null;
  }

  return function(coeff, coeff_list, constraints, invariant_regex, template, sample_space) {

    var z3_formula = "from z3 import *\n" 
      + coeff_list.map(function(c){ return c + ' = Int(\'' + c + '\')' }).join("\n") 
      + "\ns = Solver()\n\n";
    _regex = invariant_regex, _coeff = coeff;

    /* Check that the rules are not broken at all sampling points */
    if(testcase.filter) {
      var vars = [], counter = 0;
      var new_constraint = null;
      (function uniform_sampling(i) {
        if(new_constraint) return;
        for(var val=LOWERBOUND; val<=UPPERBOUND; val++) {
          vars[i] = val;
          if(i>=num_vars-1) {
            if(testcase.filter.apply(null, vars))
            {
              new_constraint = test_point(++counter, vars.join(' '));
              if(new_constraint) break;
            }
          }else
            uniform_sampling(i+1);
        }
      })(0);
      if(new_constraint) return [false, new_constraint];
    }else {
      for(var j = 0, N = sample_space.length; j<N; j++) {
        var new_constraint = test_point(j+1, sample_space[j].point);
        if(new_constraint) return [false, new_constraint];
      }
    }
    log('========Succeeded!========='.green, Verbose.INFORMATIVE);
    return [true, undefined];
  }
})(); /* end of test_coeff */

function evaluate_poly1(valuation, poly) {
  for(var i=0; i<valuation.length; i++) {
    poly = poly.replace(new RegExp('\\$' + (i+1), 'g'), '(' + valuation[i] + ')');
  }
  return round(eval(poly), 10);
}

function evaluate_poly2(valuation) {
  var linear = [];
  for(var j=0; j<template_terms.length; j++) {
    var term = template_terms[j];
    for(var i=0; i<var_names.length; i++) {
      term = term.replace(new RegExp('\\$' + (i+1), 'g'), '(' + valuation[i] + ')');
    }
    term = term.replace(/\^/g, '**');
    linear[j] = 'I_' + (j+1) + '_*(' + term + ')';
  }
  return '(' + linear.join('+').replace(/\+\-/g,'-') + ')';
}

function evaluate_poly3(valuation) {
  //return evaluate_poly2(valuation);
  var templ = template;
  for(var i=0; i<var_names.length; i++) {
    templ = templ.replace(new RegExp('\\$' + (i+1), 'g'), '(' + valuation[i] + ')');
  }
  return '(' + templ.replace(/\+\-/g,'-').replace(/\^/g, '**') + ')';
}

/** Convert the simplified formula produced by RedLog to Z3py format
 *  Example:
 *  input:  ((n >= 0 and y >= 0) and not(0 <= 0 and (n > 0 impl 0 <= 0) and (n <= 0 impl  - x <= 0)))
 *  output: And(And(n >= 0 , y >= 0) ,Not(And(0 <= 0 , Implies(n > 0 , 0 <= 0) , Implies(n <= 0 ,  - x <= 0))))
 */
function RL_to_Z3(expr) {
  return (function rec(expr) {
    var stubs = [];
    while(true) {
      var left = expr.indexOf('(');
      if(left<0) {
        var mappings = {and:'And', impl:'Implies', or:'Or'};
        for(var op in mappings) {
          var a = expr.split(op);
          if(a.length>1) {
            expr = mappings[op] + '(' + a + ')';
            break;
          }
        }
        break;
      }
      var right = find_right_paren_pos(expr,left);
      var sub_expr = expr.substring(left+1, right);
      sub_expr = rec(sub_expr);
      var stub = '$' + stubs.length;
      if((left>=3 && expr[left-1]=='t' && expr.substr(left-3,3)=='not')) {
        left -= 4; sub_expr = 'Not(' + sub_expr + ')';
      }
      expr = expr.substring(0,left) + stub + expr.substring(right+1);
      stubs.push(sub_expr);
    }
    stubs.forEach(function(s,i) {
      expr = expr.replace('$' + i, s);
    });
    return expr;
  })(expr).replace(/ = /g, '==');
}

function verify_poly(coeff, invariant_regex) {
  Profiler.tick('Quantifier elimination');
  log();
  log("Coefficients: ".bold + coeff);
  log("Pre-condition:  ".bold + PRE);
  log("Post-condition: ".bold + POST);
  log("Constraint:\t".bold + ruleRL);

  var templ = template;
  for(var name in coeff) {
    templ = templ.replace(new RegExp(name,'g'), coeff[name]);
  }
  var polyRL = bind_coeff(coeff, templ + '>=0');

  for(var i=0; i<var_names.length; i++)
    polyRL = 'ex(' + var_names[i] + ',' + polyRL.replace(new RegExp('\\$'+(i+1), 'g'), var_names[i]) + ')';

  var _ruleRL = Node.to_redlog_formula(function(expr) {
    return expr.replace(invariant_regex, '(' + template + ')');
  })(rule);

  for(var name in coeff) {
    _ruleRL = _ruleRL.replace(new RegExp(name,'g'), coeff[name]);
  }

  var redlog = 'all(x, all(y, all(n, (' + testcase.domain + ') impl (' + _ruleRL + '))))';
  redlog = 'load_package redlog; rlset ' + Settings.redlog.theory + '; poly := ' + polyRL
        + '; invariant := ' + redlog + '; feasible := rlsimpl rlqe invariant;';

  var command = "echo '" + redlog + "' | " + Settings.reduce_exec;
  result = Profiler.exec(command);

  log();
  //log("Redlog code\n".bold + redlog, Verbose.INFORMATIVE);
  log("Polynomial\n".bold + templ, Verbose.INFORMATIVE);
  log("Result\n".bold + result.replace(/\d+:/g, ''));

  if(/:= false/.test(result) || !/:= true/.test(result)) {
    var cex = 'load_package redlog; rlset ' + Settings.redlog.theory + '; find_cex := ex(x, ex(y, ex(n, (' + testcase.domain + ')';
    var point;
    var cex_desc;
    var constraints = [];

    while(constraints.length<3) {
      var cex1 = cex + (constraints.length ? ' and ' : '') + constraints.join(' and ') + ' and not (' + _ruleRL + ')))); cex := rlqea find_cex;';
      var cex_desc1 = Profiler.exec('echo "' + cex1 + '" | ' + Settings.reduce_exec);
      log("Resolving a Cex with Redlog:\n\n".bold + cex_desc1);
      if(!cex_desc) cex_desc = cex_desc1;

      if(Settings.redlog.theory=='pasf') {
        cex1 = cex_desc1.substr(cex_desc1.indexOf('true')).replace(/\n/g,'').match(/{[^}]+/)[0].substr(1);
        if(cex1) {
          if(/= *g/.test(cex1)) { /* found auxiliary variables */
            var aux_vars = cex1.match(/g\d+/g);
            var new_constraint = 'ex({' + aux_vars.toString() + '}, '
               + cex1.replace('!','1=1').replace(/,/g,' and ') + ')';
            log("Add a constraint to resolve Cex: ".bold + new_constraint.yellow, Verbose.INFORMATIVE);
            constraints.push(new_constraint);
            continue;
          }
          eval('var ' + var_names + ';'
             + cex1 + ';'
             + 'point = [' + var_names  + '];');
          point.forEach(function(p,i){ point[i] = p ? p : 0 });
        }
      }
      break;
    }
    if(!point || Settings.redlog.theory=='R' || Settings.redlog.theory=='ofsf') {
      log("\n" + '[Notice]'.bold + ' It seems we cannot obtain a Cex from Redlog, try Z3 instead. '.yellow + 'Cex: ' + point + "\n", Verbose.INFORMATIVE);
      var aa, bb;
      var lines = cex_desc.split('\n');
      for(var i=0; i<lines.length; i++) {
        if(aa===undefined && /^find_cex/.test(lines[i])) aa = i;
        if(aa!==undefined && /^cex/.test(lines[i])){ bb = i; break; }
      };
      /*                      2
       * Transforming e.g. 3*x  to 3*x**2
       */
      for(var i=aa; i<bb; i++) {
        if(!/^  *\d/.test(lines[i]) || /[^\d ]/.test(lines[i])) continue;
        for(var k=0,shift=0; k<lines[i].length; k++) {
          if(!/\d/.test(lines[i][k])) continue;
          lines[i+1] = lines[i+1].insertAt('**'+lines[i][k],k+shift);
          shift += 3;
        }
         lines[i] = '';
      }
      cex_desc = lines.slice(aa,bb).join('');
      cex_desc = cex_desc.substring(cex_desc.indexOf('('));
      cex_desc = cex_desc.substring(0, find_right_paren_pos(cex_desc, 0) + 1);
      log("Redlog formula for generating Cex\n".bold + cex_desc, Verbose.INFORMATIVE);
      cex_desc = RL_to_Z3(cex_desc);
      if(cex_desc) {
        log("Z3 formula for generating Cex:\n".bold + cex_desc.yellow);
        var z3_prog = "from z3 import *\n" + var_names.map(function(name){ return name + " = Int('" + name + "')\n" }).join('');
        z3_prog += "s = Solver()\ns.add(" + cex_desc + ")\ns.check()\nprint s.model()";
        var result = Profiler.exec('python -c "' + z3_prog + '" 2>&1');

        /* should be sat here */
        if(result[0]=='[') {
          eval('var ' + var_names.toString() + ';'
             + result.substring(1,result.length-2) + ';'
             + 'point = [' + var_names + ']');
          point.forEach(function(p,i){ point[i] = p ? p : 0 });
        }else {
          log("\n"+'[Warning] Z3 cannot resolve a counter-example: '.bold +"\n" + result);
          return [undefined, undefined]
        }
      }
    }
    if(!point) {
        log('[Error] Invalid counter example.'.bold);
        return [undefined, undefined]
    }
    log('Add Cex to the sample space:'.bold + '(' + point.toString().yellow + ")\n");
    Profiler.tick('Quantifier elimination');
    return [false, point.join(' ')];
  }
  Profiler.tick('Quantifier elimination');
  return [true, undefined];
} /* end of verify_poly */

/* eliminate denominator of numbers in formula */
function get_integral_z3_formula(coeff, expr, op) {
  if(!op) {
    var ops = ['<=','>=','<','>','='];
    for(var i=0; i<ops.length; i++) {
      var expr1 = get_integral_z3_formula(coeff, expr, ops[i]);
      if(expr1) return expr1;
    }
    return expr;
  }
  if(expr.indexOf(op)==-1) return '';
  log("EXPR (before):\n".bold + expr, Verbose.DEBUG);

  /* replace all sub-expressions with their values (for splitting) */
  expr = expr.replace(/\(([\d\+\-]+)\)/g, function(a,b) { return eval(b) });
  //expr = expr.replace(/(I?)(\([\d\+\-]+\))/g, function(a,b,c) {
  //  return b ? 'I('+eval(c)+')' : eval(c) // note case I(1+2)
  //});
  log("EXPR (sub-exp removed):\n".bold + expr, Verbose.DEBUG);

  expr = bind_coeff(coeff, expr);

  log("EXPR (coeff removed): ".bold + expr, Verbose.DEBUG);

  /* sides[0] is the LHS, sides[1] is the RHS */
  var sides = expr.split(op);

  /* compute the lcm of all denominators */
  /* REMARK: We assume at most one fraction in each term */
  var $lcm = (function($lcm) {
    (sides[0] + '+' + sides[1]).split('+').forEach(
      function(t){ (t.match(/\/(\d+)/g)||[]).forEach(
        function(d){ $lcm = lcm($lcm, +d.substr(1)) })
      });
    return $lcm;
  })(1);

  log("LCM: ".bold + $lcm.toString().cyan, Verbose.DEBUG);

  /* only handle the non-trivial case */
  if($lcm>1) {
    /* REMARK: We assume at most one fraction in each term */
    function reduce(expr) {
      return expr.replace(/(\d+)\/(\d+)/g, function(a, num, den){ return $lcm*+num/+den })
    }
    var lhs = reduce(sides[0]);
    var rhs = reduce(sides[1]);
    expr = lhs + op + rhs;
  }
  log("EXPR (after): ".bold + expr + "\n", Verbose.DEBUG);
  return expr;
} /* end of get_integral_z3_formula */

/////////////////////////////////// main function ///////////////////////////////////
function main(timeout) {

  if(!PRE) throw 'You have to specify a pre-expectation.';
  if(!POST) throw 'You have to specify a post-expectation.';
  if(!TEST_NAME) throw 'You have to specify a test case.';
  if(DEGREE===undefined || DEGREE<0) throw 'You have to specify the degree of invariant.';
  if(SKEWNESS<0 || SKEWNESS>=1) throw 'Skewness should be between 0 and 1.';

  Profiler.reset(timeout);
  Profiler.start('Total execution time');

  var _testcase = require('./test-cases/' + TEST_NAME);
  for(var name in _testcase) {
    var definition = _testcase[name];
    if(typeof definition == 'string') definition = '"' + definition + '"';
   /* add the definitions to the current scope */
    eval('testcase.' + name + '=' + definition + ';');
  }

  rule = testcase.rule(PRE, POST);
  ruleRL = Node.to_redlog_formula(function(x){ return x })(rule);
  log("Inference Rule\n".bold + ruleRL);

  var_names = testcase.vars.split(',');
  num_vars = var_names.length;
  log("Variables\n".bold + var_names);

  var invariant_regex = (function() {
    var regex = 'I\\[';
    for(var i=0; i<num_vars-1; i++) regex += '([^,]+),';
    regex += '([^\\]]+)\\]';  /* e.g. 'I\\[([^,]+),([^,]+),([^\]]+)\\]' */
    return new RegExp(regex, 'g');
  })();

  eval('precond  = function(' + var_names + '){return ' + PRE + '}');
  eval('postcond = function(' + var_names + '){return ' + POST + '}');

  num_samples = (function(fact) {
    return fact(fact, num_vars+1, num_vars+DEGREE)/fact(fact, 1, DEGREE);
  })(function(fact, from, to) {
    return (from==to ? from : (to*fact(fact, from, to-1)));
  });

  if(!isInt(num_samples) || num_samples<1) throw 'Invalid number of samples: ' + num_samples;

  var sample_space = build_sample_space(num_vars, num_samples);

  if(!sample_space.length) throw 'Sample space is empty.';

  /* For example, if DEGREE is 2, then the monomials will be 
     [[2,0,0],[0,2,0],[0,0,2],[1,1,0],[1,0,1],[0,1,1],[1,0,0],[0,1,0],[0,0,1],[0,0,0]] */
  var monomials = (function () {
    var result = [];
    (function rec(d,i,t) {
      if(d<=0 || i>=num_vars) {
        while(i<num_vars) t[i++] = 0;
        result.push(t.slice(0));
        return;
      }
      for(var j=0; j<=d; j++) {
        t[i] = j;
        rec(d-j,i+1,t);
      }
    })(DEGREE, 0, []);
    return result;
  })();

  log("All valid samples".bold, Verbose.INFORMATIVE+1);

  Profiler.tick('Computing basis');

  if(USE_LAGRANGE_BASIS)
    var result = compute_lagrange_basis(num_samples, monomials, sample_space);
  else
    var result = compute_standard_basis(num_samples, monomials, sample_space);

  result[1].forEach(function(s){ log(pt_str(s.point) + ' ' + s.constraint) });

  Profiler.tick('Computing basis');

  var basis   = result[0];
  var samples = result[1];
  var points  = samples.map(function(s){ return s.point });

  template = build_template(num_samples, monomials, basis);

  log("Sampling\n".bold +'Points: (' + samples.map(function(s){ return s.point }).join('), (') + ')', Verbose.INFORMATIVE);
  if(Settings.verbose_level>=Verbose.INFORMATIVE)
    samples.forEach(function(s){ log(pt_str(s.point) + ' ' + s.constraint) });

  log('Constraints'.bold, Verbose.INFORMATIVE);

  var constraint = bounded_constraint = '(I_1_==I_1_)';

  for(var i=0; i<samples.length; i++) {
    var s = samples[i];
    log(s.point.bold+' '+s.constraint, Verbose.INFORMATIVE);
    constraint += ' and ' + s.constraint;
    if(s.lower!==undefined && s.upper!==undefined)
      bounded_constraint += ' and ' + s.constraint;
  }

  var coeff_list = [];

  for(var i=0; i<samples.length; i++) {
    var p = samples[i].point.split(' ');
    var r = 'I\\[' + p.join(',') + '\\]';
    var c = 'I_' + (i+1) + '_';
    constraint = constraint.replace(new RegExp(r,'g'), USE_LAGRANGE_BASIS ? c : evaluate_poly3(p));
    coeff_list[i] = c;
  }

  log("Constraint before replacing free coeff:\n".bold + constraint, Verbose.INFORMATIVE);

  if(USE_LAGRANGE_BASIS)
    constraint = constraint.replace(/I\[[^\]]+\]/g, function(a,b) { var cc = 'I_' + (coeff_list.length+1) + '_'; coeff_list.push(cc); return cc });
  else
    constraint = constraint.replace(/I\[([^\]]+)\]/g, function(a,b) { return evaluate_poly3(b.split(',')) });
 
  //(function(free_coeffs) {
  //  if(!free_coeffs) return;
  //  free_coeffs.map(function(c) {
  //    var cc = 'I_' + (coeff_list.length+1) + '_';
  //    constraint = constraint.replace(new RegExp(c.replace(/([\[\]])/g,'\\$1'),'g'), cc);
  //    coeff_list.push(cc);
  //  });
  //})(constraint.match(/I\[[^\]]+\]/g));
  
  log("Constraint after replacing free coeff:\n".bold + constraint, Verbose.INFORMATIVE);
  log("Basis\n".bold + basis, Verbose.INFORMATIVE);
  log("Coeff names\n".bold + coeff_list.map(function(n){ return n.substr(0,n.length-1) }), Verbose.INFORMATIVE);
  log("Constraint for coefficients\n".bold + constraint);
  log("Constraint for invariant\n".bold + bounded_constraint);
  log("Template\n".bold +
    template.replace(/\+I/g," +\nI").split("\n").map(function(t) {
      return t.replace(/\(\$(\d+)\)/g, function(a,id){ return var_names[id-1] }).
           replace(/[a-z]+[\^\d]*/g, '$&'.green).
           replace(/I[_\d]+/, '$&'.bold)
    }).join("\n"), Verbose.INFORMATIVE+1);
  log();

  var invariant = (function() {
    var coeff = null;
    var constraintsZ3 = [];
    var times_to_try = Settings.max_num_sample_verification;
    while(times_to_try-->0) {
      /* guess a set of coefficients */
      if(!coeff) {
        var new_coeff = refine_constraint(coeff_list, constraint, constraintsZ3);
        if(!new_coeff) return false; /* unsat or error */
        eval('coeff = ' + new_coeff);
        //log('New coeff: '.bold + new_coeff.toString().bold);
        coeff_list.map(function(c){ if(!coeff[c]) coeff[c] = 0; });
        log("Guess: ".bold + coeff + "\n");
      }
      /* Check if the guessed polynomial satisfies the rules at all sampling points */
      Profiler.tick('Random tests');
      var invariant = USE_RANDOM_TESTS ? test_coeff(coeff, coeff_list, constraintsZ3, invariant_regex, template, sample_space) : [true];
      Profiler.tick('Random tests');

      /* yes */
      if(invariant[0]) {
        invariant = verify_poly(coeff, invariant_regex);
        if(invariant[0]) return coeff;  /* an invariant is found; return coeff */
        if(!invariant[1]) return invariant[0];      /* invariant doesn't exist */
        sample_space.unshift({point: invariant[1], toString: Sample.prototype.toString});
        //log("Sample space: ".bold + sample_space.map(function(s){ return s.toString() }).join(','));
        continue;
      }

      /* no, generate a new constraint */
      var new_constraint = invariant[1];
      new_constraint = new_constraint.replace(/\+0/g,'').replace(/0\+/g,'');

      //new_constraint = simplify(new_constraint);
      log("New constraint:\n".bold + new_constraint.yellow, Verbose.INFORMATIVE);
      constraintsZ3.push(new_constraint);
      coeff = null;
    }
    return undefined;  /* cannot find an invariant */
  })();

  if(invariant) {
    log("\n"+'Invariant has been proved successfully.'.yellow.bold);
    invariant = (function(coeff) {
      var _z3_prog_header = "from z3 import *\n" + var_names.map(function(name) {
        return name + " = Real('" + name + "')\n"
      }).join('') + "s = Solver()\n";

      var _z3_prog = bind_coeff(coeff, template.replace(/\^/g,'**').replace(/\$(\d+)/g,
        function(a,i){ return var_names[i-1] }
      )).replace(/(-?[0-9]+\/[\.0-9]+)/g, 'RealVal(\'$1\')');
      _z3_prog = _z3_prog_header + 'print simplify(' + _z3_prog + ')';
      var poly = Profiler.exec('python -c "' + _z3_prog + '"');
      return poly.replace(/(-?\d+\/\d+)/g, '($1)').replace(/\n/g, ' ').replace(/\*\*/g,'^');
    })(invariant);
    /* simplify invariant using RedLog */
    //invariant = Profiler.exec("echo 'load_package redlog; rlset " + Settings.redlog.theory
    // + "; poly := " + invariant + ";' | " + Settings.reduce_exec
    // + " | grep poly | grep -o '(.*>' | sed 's/[(>]//g' | sed 's/  /^2 /g'");
  }else {
    if(invariant===false) {
      log("\n" + "Invariant does not exists.".bold.red);
      invariant = 'None';
    }else {
      log("\n"+'Failed to prove invariant due to invalid counter-example.'.bold.red);
      invariant = 'Unknown';
    }
    log("\nRedLog rules:\t".bold + ruleRL);
  }
  Profiler.stop('Total execution time');

  log("\n"+"Profiling of ".bold + TEST_NAME.yellow.bold);
  for(var _mark in Profiler.timers) {
    log(_mark + ":\t" + (Profiler.timers[_mark].toFixed(2) + 's').cyan);
  }
  for(var _mark in Profiler.counters) {
    log(_mark + ":\t" + Profiler.counters[_mark].toString().cyan);
  }
  log('Pre-expectation:\t'  + PRE.substr(1, PRE.length-2));
  log('Post-expectation:\t' + POST.substr(1, POST.length-2));
  log("Invariant:\t\t" + invariant.cyan);

  return Profiler.timers['Total execution time'] * (invariant=='Unknown' ? -1 : 1);
}
////////////////////////////////////////////////////////////////////////////////////

var args = process.argv.slice(2);
var rule, ruleRL, ruleJS, precond, postcond, template; 
var var_names, num_vars, num_samples, testcase = {};

var UPPERBOUND = Settings.lagrange.upper;    /* default: 3   */
var LOWERBOUND = Settings.lagrange.lower;    /* default: 0   */
var SKEWNESS   = Settings.lagrange.skewness; /* default: .65 */
var TEST_NAME, PRE, POST, DEGREE = 2;
var USE_APPROX_ROUNDING = false;
var USE_LAGRANGE_BASIS  = true;
var USE_RANDOM_TESTS    = true;
var TIMEOUT = 180; /* in seconds */
var NUM_RUNS = 1;

for(var i=0; i<args.length; i++) {
    var arg = args[i].split('=');
    var val = arg[1];
    var param = arg[0];
    if(!val || !param) continue;
    switch(param) {
      case 'pre' :     PRE  = '(' + val + ')';     break; /* mandatory */
      case 'post':     POST = '(' + val + ')';     break; /* mandatory */
      case 'degree':   DEGREE = +val;              break; /* mandatory */
      case 'test':     TEST_NAME = val;            break; /* mandatory */
      case 'lower':    LOWERBOUND = +val;          break;
      case 'upper':    UPPERBOUND = +val;          break;
      case 'skew':     SKEWNESS = +val;            break;
      case 'timeout':  TIMEOUT = +val;             break;
      case 'repeat':   NUM_RUNS = +val;            break;

      case 'apprx':    USE_APPROX_ROUNDING = bool_val(val); break;
      case 'rand':     USE_RANDOM_TESTS    = bool_val(val); break;
      case 'lagrange': USE_LAGRANGE_BASIS  = bool_val(val); break;
      case 'theory':   Settings.redlog.theory = val;        break;
      case 'verbose':  Settings.verbose_level = +val;       break;
      default: continue;
    }
}

var total_execution_time = 0;

for(var i=0; i<NUM_RUNS; i++) {
  var timeout = TIMEOUT;
  try {
    while(true) {
      var time = main(TIMEOUT);
      timeout += (time>0 ? -1:1)*time;
      if(time>0 || timeout<=0) break;
    }
    total_execution_time += TIMEOUT - timeout;
  }catch(e) {
    if(typeof e != 'string') throw e;
    if(e == 'timeout') {
        total_execution_time += TIMEOUT;
        log("\n"+'Failed to prove invariant due to timeout.'.bold.red);
    }else {
        console.error('[error]'.bold.red + ' ' + e.bold);
        process.exit(-1);
    }
  }
}
if(NUM_RUNS>1) log("\n\nAverage execution time: " + (total_execution_time/NUM_RUNS).toFixed(2) + ' seconds over ' + NUM_RUNS + ' runs.');
