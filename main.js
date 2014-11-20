//#! /usr/local/bin/node

var fs = require('fs');
var sh = require("execSync");
var colors = require('colors');
//var fraction = require('./fraction.js');

var Verbose = {
    QUIET:      -1,
    NORMAL:      0,
    INFORMATIVE: 1,
    DEBUG:       10,
};
var Settings = {
    /**
     * The constraints with either 'pasf' (Presburg arithematics)
     * or 'ofsf' (an approximation of real number arithematics)
     */
    redlog: { theory: 'ofsf' },
    /**
     * Skewness determines how the sample points are chosen.
     * When skewness = 1, sampling are made uniformly from the sample space.
     * As skewness approaches zero, the result of sampling is more
     * likely to be a favorable one. However, this comes at the cost of
     * longer sampling time and the risk of failing the sampling process.
     */
    lagrange: { lower: 0, upper: 3, skewness: .65 },
    /**
     * Three evaluators available: 'mathomatic', 'javascript',  'python'
     */
    symbolic: { evaluator: 'javascript' },
    max_num_basis_probe: 500,
    max_num_sample_verification: 100,
    verbose_level: 0,
};
var precond, postcond, testcase;

function I(x, y, n) {
    if(n!==undefined)
        return 'I[' + x + ',' + y + ',' + n + ']';
    if(y!==undefined)
        return 'I[' + x + ',' + y + ']';
    return 'I[' + x + ']';
}
function pt_str(pt) { return '[' + pt.split(' ').map(function(p){ return +p>=0 ? ' '+p : p }).join(' ') + ' ]' }
function round(x, n) { return +x.toFixed(n ? n:5); }
function isInt(x) { return (typeof x==='number' && (x%1)===0); }
function gcd(a, b) { return b ? gcd(b, a % b) : a; }
function lcm(a, b) { return !a||!b ? 0 : a*b/gcd(a,b); }


/* This is the multiply-with-carry (MWC) random generator with
 * a pretty long period. Adapted from Wikipedia, see
 * http://en.wikipedia.org/wiki/Random_number_generation#Computational_methods
 */
Math.seed = function(s) { // Takes any integer
    var m_w = s;
    var m_z = 987654321;
    var mask = 0xffffffff;
    return function()
    // Returns number between 0 (inclusive) and 1.0 (exclusive),
    // just like Math.random().
    {
        m_z = (36969 * (m_z & 65535) + (m_z >> 16)) & mask;
        m_w = (18000 * (m_w & 65535) + (m_w >> 16)) & mask;
        var result = ((m_z << 16) + m_w) & mask;
        result /= 4294967296;
        return result + 0.5;
    }
}

Math.random = Math.seed(Math.round(Math.seed(42)()*10000));

Object.prototype.toString = function(){
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

/* Profiler and timer */
var Profiling = {};
var Timer = {
    marks: {},
    tick: function(marking) { // get interval from last tick in seconds
        var now = process.hrtime()[0];
        var last_tick = this.marks[marking] || now;
        this.marks[marking] = now>last_tick ? 0 : now;
        var elapsed = Profiling[marking];
        Profiling[marking] = (elapsed ? elapsed : 0) + now - last_tick;
    },
    reset: function(marking) {
        this.marks[marking] = undefined;
        Profiling[marking] = 0;
    }
};

/* Definition of class Sample */
var Sample = function(point, lowerbound, upperbound, constraints) {
    this.point = point;
    this.diff  = (upperbound!==undefined && lowerbound!==undefined) ? upperbound-lowerbound : undefined;
    this.lower = lowerbound;
    this.upper = upperbound;
    this.constraint = '(' + constraints.join(') and (') + ')';
}
Sample.prototype.toString = function (){
    return '(' + this.point + ')';
}

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

Node.to_z3_formula = function(string_parser) {
    return function parse(node) {
        switch(node.constructor) {
            case Not:
                return 'Not(' + parse(node.children[0]) + ')';
            case Or:
                var sub_expr = node.children.map(parse).join(', ');
                /* At least one of the arguments must be a Z3 expression */
                if(!/[()a-zA-Z]/.test(sub_expr))
                    return eval('('+sub_expr.replace(/,/g,')||(')+')') ? 'True' : 'False';
                else
                    return 'Or(' + sub_expr + ')';

                return 'Or(' + node.children.map(parse).join(', ') + ')';
            case And:
                var sub_expr = node.children.map(parse).join(', ');
                /* At least one of the arguments must be a Z3 expression */
                if(!/[()a-zA-Z]/.test(sub_expr))
                    return eval('('+sub_expr.replace(/,/g,')&&(')+')') ? 'True' : 'False';
                else
                    return 'And(' + sub_expr + ')';
            case Imp:
                return 'Implies(' + parse(node.children[0]) + ', ' + parse(node.children[1]) + ')';
            case String:
                return string_parser(node);
            default:
                return node.toString();
        }
    }
}
Node.to_redlog_formula = function(string_parser) {
    return function parse(node) {
        switch(node.constructor) {
            case Not:
                return 'not (' + parse(node.children[0]) + ')';
            case Or:
                return '(' + node.children.map(parse).join(') or (') + ')';
            case And:
                return '(' + node.children.map(parse).join(') and (') + ')';
            case Imp:
                return '(' + parse(node.children[0]) + ') impl (' + parse(node.children[1]) + ')';
            case String:
                return string_parser(node.replace(/==/g,'=').replace(/!=/g,'<>'));
            default:
                return node.toString();
        }
    }
}
Node.prototype.toString = function() { return this.name + '(' + this.children + ')' }

var Not = Node.create('Not'), And = Node.create('And'), Or = Node.create('Or'), Imp = Node.create('Imp');

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

function _verify_sample_(x,y,n) {
    var constraints = [];

    if(!isInt(x) || !isInt(y) || !isInt(n)) return null;

    Timer.tick('verify_sample');
    var bounds = testcase.check(x,y,n,constraints);
    Timer.tick('verify_sample');

    if(!bounds) return null;

    var lower = bounds[0];
    var upper = bounds[1];
    if(upper==lower) constraints = [I(x,y,n) + '==' + upper];
    return new Sample(x+' '+y+' '+n, lower, upper, constraints);
}

function build_sample_space(lower, upper, num_vars, num_samples) {
    Timer.tick('build_sample_space');
    var samples = [];
    var vars = [];
    (function uniform_sampling(i){
        for(var val=lower; val<=upper; val++) {
            vars[i] = val;
            if(i>=num_vars-1) {
                var sample = verify_sample(vars);
                if(sample!==null && (sample.upper!==undefined || sample.lower!==undefined))
                    samples.unshift(sample);
            }else
                uniform_sampling(i+1);
        }
    })(0);

    if(samples.length<num_samples) {
        console.log(('[Error] Unable to build large enough sample space: '
                    + samples.length + ' probed, ' + num_samples + ' needed.').bold);
        console.log('Hint: try to adjust parameter "lower" and "upper". Current values: (' + lower + ', ' + upper + ')');
        throw 'Program aborted';
    }
    samples = samples.sort(function(a,b){
        return (a.diff===undefined||b.diff===undefined) ? -(Math.abs(a.diff||b.diff)||1) :(a.diff-b.diff);
    });
    Timer.tick('build_sample_space');
    return samples;
}

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

/** Random sampling according to weights.
 *
 *  Note that sample points are assumed to be integers.
 */
function compute_lagrange(degree, num_samples, monomials, sample_space) {

    var detVandermonde = 0;
    var N =  '[' + monomials.join('; ') + ']';
    var num_vars = sample_space[0][0].split(' ').length;

    function lagrange(samples) {
        Timer.tick('compute_lagrange_basis');
        var S = '[' + samples.join('; ') + ']';
        var command = './lagrange.m "' + degree + '" "' + num_vars + '" "' + num_samples + '" "' + S + '" "' + N + '"';
        var basis = sh.exec(command + ' 2>/dev/null').stdout;
        if(!/^singular/.test(basis)) {
            basis = basis.split(/ +/);
            detVandermonde = +basis.shift(); // determinant of the Vandermonde matrix
            basis.pop(); // discard "\n"
            if(isNaN(detVandermonde) || !detVandermonde || basis.length != num_samples*num_samples) {
                log("Basis\n".bold + basis);
                log("Command\n".bold + command);
                log("Result\n".bold + sh.exec(command).stdout);
                throw 'Invalid Lagrange basis!';
            }
            //log('Command: ' + command); process.exit();

            var detV = Math.abs(detVandermonde);
            var sign = detVandermonde>0 ? 1 : -1;
            basis = basis.map(function(b) {
                b = +b;
                if(b==0) return 0;
                b = b * sign;
                var a = Math.abs(gcd(b, detV));
                // It must be sign(b)==sign(b/a)
                var n = b/a, m = detV/a;
                if(m==1) return n;
                return n + '/' + m;
            });
            //log("Basis\n".bold + basis, Verbose.INFORMATIVE);
            var result = basis;
        }else
            var result = null;
        Timer.tick('compute_lagrange_basis');
        return result;
    }
    Timer.tick('guess_lagrange_basis');
    var _weight  = 0;
    var _weights = sample_space.map(function(s){ return s[1] });
    var _points  = sample_space.map(function(s){ return s[0] });
    var samples  = new Array(num_samples);
    var indices  = new Array(num_samples);
    var times_to_try = Settings.max_num_basis_probe;

    _weights.forEach(function(w){ _weight += w; });

    while(times_to_try--) {
        var weight  = _weight;
        var weights = _weights.slice(0);
        var points  = _points.slice(0);
        var _indices = weights.map(function(a,i){return i});
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
        if(basis){
            log("Rand\n".bold + '['+rands.join(',')+']', Verbose.INFORMATIVE);
            Timer.tick('guess_lagrange_basis');
            return [basis, indices];
        }
   }
   log(('[Error] Cannot find a valid sampling within ' + Settings.max_num_basis_probe + ' trials.').bold.red);
   throw 'Cannot find a basis!';
}

function refine_constraint(coeff_list, constraint, constraints) {
    var z3_formula = constraint.replace(/ *and */g,',');
    z3_formula = "from z3 import *\n" + coeff_list.map(function(c){ return c + ' = Int(\'' + c + '\')'; }).join("\n")
                 + "\ns = Solver()\n\ns.add(And(" + z3_formula + "))\n\n";
    constraints.forEach(function(c){ z3_formula += c + "\n" });
    z3_formula += "s.check()\nprint s.model()";
//    log("Z3 formula:\n".bold + z3_formula, Verbose.DEBUG);

    var result = sh.exec('echo "' + z3_formula + '" | tee z3.refine.log | python -').stdout;
    // sat
    if(result[0]=='[') {
        result = '{' + result.substr(1, result.length-3).replace(/\n/g,'').replace(/ = /g,':') + '}';
        return result;
    }
    // unsat
    log("Z3 Error:\n".bold.red + result, Verbose.DEBUG);
    return '';
}


function build_template(num_samples, monomials, basis) {
    monomials = monomials.map(function(degs) {
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
    return terms;
}

function main() {
    Timer.tick('main');
    var args = process.argv.slice(2);
    var upper = Settings.lagrange.upper; // 3
    var lower = Settings.lagrange.lower; // 0
    var skewness = Settings.lagrange.skewness; // .65
    var search_strategy = Settings.search_strategy;
    var rule, ruleRL, ruleJS, var_names, num_vars, num_samples;
    var degree = 2;
    var pre  = 'x*(y-x)';
    var post = 'n';
    testcase = 'random-walk';

    for(var i=0; i<args.length; i++) {
        var arg = args[i].split('=');
        var val = arg[1];
        var param = arg[0];
        if(!val || !param) continue;
        switch(param) {
            case 'pre' :        pre  = '(' + val + ')'; break; // mandatory
            case 'post':        post = '(' + val + ')'; break; // mandatory
            case 'degree':      degree = +val;          break; // mandatory
            case 'var':     var_names = val.split(','); break; // mandatory
            case 'strategy':    search_strategy = val;  break;
            case 'test':        testcase = val;         break;
            case 'lower':       lower = +val;           break;
            case 'upper':       upper = +val;           break;
            case 'skew':        skewness = +val;        break;
            case 'verbose':     Settings.verbose_level = +val; break;
            case 'theory':      Settings.redlog.theory = val;  break;
            default: continue;
        }
    }
    if(skewness<0 || skewness>=1){
        console.log('[Error] Skewness should be between 0 and 1.'.bold);
        return;
    }
 
    var _testcase = require('./test-cases/' + testcase);
    testcase = {};
    for(var name in _testcase){
        var definition = _testcase[name];
        if(typeof definition == 'string') definition = '"' + definition + '"';
        eval('testcase.' + name + '=' + definition + ';');
    }
    rule = testcase.rule(pre, post);
    ruleRL = Node.to_redlog_formula(function(x){ return x })(rule);
    log("Inference Rule\n".bold + ruleRL);

    if(!var_names || !var_names.length) {
        log('[Error] Please give names of the program variables.'.bold.red);
        return;
    }
    num_vars = var_names.length;
    log("Variables\n".bold + var_names);

    var invariant_regex = 'I\\[';
    for(var i=0; i<num_vars-1; i++) invariant_regex += '([^,]+),';
    invariant_regex += '([^\\]]+)\\]';  // e.g. 'I\\[([^,]+),([^,]+),([^\]]+)\\]'
    invariant_regex = new RegExp(invariant_regex, 'g');

    eval('precond  = function(' + var_names + '){return ' + pre + '}');
    eval('postcond = function(' + var_names + '){return ' + post + '}');

    num_samples = (function(fact) {
        return fact(fact, num_vars+1, num_vars+degree)/fact(fact, 1, degree);
    })(function(fact, from, to) {
        return (from==to ? from : (to*fact(fact, from, to-1)));
    });

    if(!isInt(num_samples)||num_samples<1) { console.error('Invalid number of samples: ' + num_samples); return; }

    var sample_space = build_sample_space(lower, upper, num_vars, num_samples);

    if(!sample_space.length){ console.error('Sample space is empty.'); return; }

    var monomials = (function (){
        //if(degree==2)
        //    return [[2,0,0],[0,2,0],[0,0,2],[1,1,0],[1,0,1],[0,1,1],[1,0,0],[0,1,0],[0,0,1],[0,0,0]];
        var result = [];
        (function rec(d,i,t){
            if(d<=0 || i>=num_vars) {
                while(i<num_vars) t[i++] = 0;
                result.push(t.slice(0));
                return;
            }
            for(var j=0; j<=d; j++) {
                t[i] = j;
                rec(d-j,i+1,t);
            }
        })(degree, 0, []);
        return result;
    })();

    log("All valid samples".bold, Verbose.INFORMATIVE+1);

    var result = compute_lagrange(degree, num_samples, monomials, sample_space.map(function(s){
            var weight = Math.pow(1-skewness, s.diff===undefined ? 1/(1-skewness) : s.diff);
            log(pt_str(s.point) + ' ' + s.constraint + ' ' + round(weight,4).toString().cyan, Verbose.INFORMATIVE+1);
            return [s.point, weight];
        }));
    var basis   = result[0];
    var samples = result[1].map(function(i){ return sample_space[i] });
    var points  = samples.map(function(s){ return s.point });
    //basis = basis.split("\n").slice(2);

    var template_terms = build_template(num_samples, monomials, basis);
    var template = template_terms.map(function(t,i){ return 'I_' + (i+1) + '_*(' + t + ')' }).join('+');

//    log("Template terms\n".bold + template_terms.join("\n")); log("Template\n".bold + template); throw '';
    
    log("Sampling\n".bold +'Points: (' + samples.map(function(s){ return s.point }).join('), (') + ')', Verbose.INFORMATIVE);
    if(Settings.verbose_level>=Verbose.INFORMATIVE)
        samples.forEach(function(s){ console.log(pt_str(s.point) + ' ' + s.constraint) });

    log('Constraints'.bold, Verbose.INFORMATIVE);

    var constraint = bounded_constraint = '(1==1)';

    for(var i=0; i<samples.length; i++) {
        var s = samples[i];
        log(s.point, s.constraint, Verbose.INFORMATIVE);
        constraint += ' and ' + s.constraint;
        if(s.lower!==undefined && s.upper!==undefined)
            bounded_constraint += ' and ' + s.constraint;
    }

    var coeff_list = [];

    for(var i=0; i<samples.length; i++) {
        var r = 'I\\[' + samples[i].point.split(' ').join(',') + '\\]';
        var c = 'I_' + (i+1) + '_';
        constraint = constraint.replace(new RegExp(r,'g'), c);
        coeff_list[i] = c;
    }

    //log("Constraint before replacing free coeff:\n".bold + constraint, Verbose.INFORMATIVE);

    (function(free_coeffs){
        if(!free_coeffs) return;
        free_coeffs.map(function(c){
            var cc = 'I_' + (coeff_list.length+1) + '_';
            constraint = constraint.replace(new RegExp(c.replace(/([\[\]])/g,'\\$1'),'g'), cc);
            coeff_list.push(cc);
        });
    })(constraint.match(/I\[[^\]]+\]/g));

    //log("Constraint after replacing free coeff:\n".bold + constraint, Verbose.INFORMATIVE);

    log("Basis\n".bold + basis, Verbose.INFORMATIVE);
    log("Coeff names\n".bold + coeff_list.map(function(n){ return n.substr(0,n.length-1) }), Verbose.INFORMATIVE);
    log("Constraint for coefficients\n".bold + constraint);
    log("Constraint for invariant\n".bold + bounded_constraint);
    log("Template\n".bold +
        template.replace(/\+I/g," +\nI").split("\n").map(function(t){
            return t.replace(/\(\$(\d+)\)/g, function(a,id){ return var_names[id-1] }).
                   replace(/[a-z]+[\^\d]*/g, '$&'.green).
                   replace(/I[_\d]+/, '$&'.bold)
        }).join("\n"), Verbose.INFORMATIVE+1);
    log();

    function test_coeff(coeff, constraints) {
        Timer.tick('test_coeff');

        /* the formula to be checked for validity by Z3 */
        var z3_formula = "from z3 import *\n" + coeff_list.map(function(c){ return c + ' = Int(\'' + c + '\')' }).join("\n") + "\ns = Solver()\n\n";

        function parser(point) {
            var values = point.split(' ');
            return function(rule0) {
                /* replace program variables by values in the rules */
                for(var i=0; i<var_names.length; i++)
                    rule0 = rule0.replace(new RegExp(var_names[i], 'g'), values[i]);
                // replace e.g. --2 by 2
                rule0 = rule0.replace(/--/g,'');
                log('Rule: ' + rule0, Verbose.INFORMATIVE+1);
                var rule1 = rule0.replace(invariant_regex,
                    function(a,b,c,d){
                        var g = arguments;
                        var args = var_names.reduce(function(args, j, i){ args.push(g[i+1]); return args; }, []);
                        var poly_expr = evaluate_poly3(args, template);
                        return '(' + poly_expr + ')'; // is an expression
                    });
                return normalize(coeff, rule1, false);
            }
        }// end of parser

        function test_point(point) {
            log(('Checking Point' + (j+1) + ': ').bold + '(' + point.cyan +') ...', Verbose.INFORMATIVE+1);
            var new_constraint = 's.add(' + Node.to_z3_formula(parser(point))(rule) + ")\n";

            var ruleZ3 = new_constraint;
            for(var name in coeff)
                ruleZ3 = ruleZ3.replace(new RegExp(name,'g'), coeff[name]);

            //console.log("Rule:\n".bold + ruleZ3);
            var z3_prog = z3_formula + ruleZ3 + "\n";
            /* check if the formula (without free variables) is satisfiable */
            constraints.forEach(function(c){ z3_prog += c + "\n" });
            z3_prog += "print s.check()";
            var result = sh.exec('echo "' + z3_prog + '" | tee z3.qcheck.log | python -').stdout;
            var passed = /^sat/.test(result);
            // abort if Z3 outputs error messages
            if(!passed && !/^unsat/.test(result)) throw result.bold.red;

            log('Point (' + point.cyan + ') ' + (passed? 'passed'.green : 'failed'.red), Verbose.INFORMATIVE);
            log('Time for normalization: ' + Profiling['normalization'] + 's', Verbose.DEBUG);
            log('Critical: ' + Profiling['symbolic'] + 's' + "\n", Verbose.DEBUG);
            Timer.reset('normalization');
            Timer.reset('symbolic');
            return !passed ? new_constraint : null;
        }

        var times_to_try = Settings.max_num_sample_verification;

        /* check that the rules are not broken at all sample points */
        while(times_to_try-->0) {
            if(testcase.filter){
                var vars = [];
                var new_constraint = null;
                (function uniform_sampling(i){
                    if(new_constraint) return;
                    for(var val=lower; val<=upper; val++) {
                        vars[i] = val;
                        if(i>=num_vars-1) {
                            if(testcase.filter.apply(null, vars))
                            {
                                new_constraint = test_point(vars.join(' '));
                                if(new_constraint) break;
                            }
                        }else
                            uniform_sampling(i+1);
                    }
                })(0);
                if(new_constraint) return [false, new_constraint];
            }else {
                for(var j = 0, N = sample_space.length; j<N; j++) {
                    var new_constraint = test_point(sample_space[j].point);
                    if(new_constraint) return [false, new_constraint];
                }
            }
            Timer.tick('test_coeff');
            log('========Succeeded!========='.green, Verbose.INFORMATIVE);

            var replace_redlog_with_z3 = false;
            if(replace_redlog_with_z3) {
            var rule0 = 's.add(' + Node.to_z3_formula(function(expr){
                log('Exp before substitution: '.bold.red + expr);
//                expr = expr.replace(/I\(([^,]+),([^,]+),([^)]+)\)/g,
                expr = expr.replace(invariant_regex,
                    function(a,b,c,d) {
                        var g = arguments;
                        var args = var_names.reduce(function(args, j, i){ args.push(g[i+1]); return args; }, []);
                        var poly_expr = evaluate_poly3(args, template);
                        return '(' + poly_expr + ')'; // is an expression
                    })
                log('Exp after substitution: '.bold.red + expr);
                expr = normalize(coeff, expr, true);
//                expr = get_integral_z3_formula(coeff, expr);
                log('Exp after eliminating fractions: '.bold.red + expr);
                return expr;
            })(NOT(rule)) + ")\n";

            rule0 = bind_coeff(coeff, rule0);

            console.log(rule0);
            z3_prog = "from z3 import *\n" + var_names.map(function(name){ return name + " = Int('" + name + "')\n" }).join('');
            z3_prog += "s = Solver()\n\n" + rule0
                + "\nprint s.check()";
//                + "\ns.check()\nprint s.model()";
            var result = sh.exec('echo "' + z3_prog + '" | tee z3.cex.log | python -').stdout;

            console.log(result);
            // sat
            if(result[0]=='[') {
                result = '{' + result.substr(1, result.length-3).replace(/\n/g,'').replace(/ = /g,':') + '}';
            }
            throw "abort";
            }
            return [true, undefined];
        }
    }// end of test_coeff

    function evaluate_poly1(valuation, poly) {
        Timer.tick('evaluate_poly1');
        for(var i=0; i<valuation.length; i++) {
            poly = poly.replace(new RegExp('\\$'+(i+1), 'g'),'(' + valuation[i] + ')');
        }
        Timer.tick('evaluate_poly1');
        return round(eval(poly), 10);
    }

    function evaluate_poly2(valuation) {
        Timer.tick('evaluate_poly2');
        var linear = [];
        for(var j=0; j<template_terms.length; j++) {
            var term = template_terms[j];
            for(var i=0; i<var_names.length; i++) {
                term = term.replace(new RegExp('\\$'+(i+1),'g'), '('+valuation[i]+')');
            }
            term = term.replace(/\^/g, '**');
            linear[j] = 'I_' + (j+1) + '_*(' + term + ')';
        }
        Timer.tick('evaluate_poly2');
        return linear.join('+').replace(/\+\-/g,'-');
    }

    function evaluate_poly3(valuation, template) {
        //return evaluate_poly2(valuation);
        for(var i=0; i<var_names.length; i++) {
            template = template.replace(new RegExp('\\$'+(i+1),'g'), '('+valuation[i]+')');
        }
        template = template.replace(/\+\-/g,'-').replace(/\^/g, '**');
        return template;
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
    /* eliminate denominator of numbers in formula */
    function get_integral_z3_formula(coeff, expr, op){
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

        /* substitute all sub-expression by thir values (for splitting) */
        expr = expr.replace(/\(([\d\+\-]+)\)/g, function(a,b) { return eval(b) });
        //expr = expr.replace(/(I?)(\([\d\+\-]+\))/g, function(a,b,c){
        //    return b ? 'I('+eval(c)+')' : eval(c) // note case I(1+2)
        //});
        log("EXPR (sub-exp removed):\n".bold + expr, Verbose.DEBUG);

        expr = bind_coeff(coeff, expr);

        log("EXPR (coeff removed): ".bold + expr, Verbose.DEBUG);

        /* sides[0] is the LHS, sides[1] is the RHS */
        var sides = expr.split(op);

        /* compute the lcm of all denominators */
        // REMARK: We assume at most one fraction in each term
        var $lcm = (function($lcm) {
            (sides[0] + '+' + sides[1]).split('+').forEach(
                function(t){ (t.match(/\/(\d+)/g)||[]).forEach(
                    function(d){ $lcm = lcm($lcm, +d.substr(1)) })});
            return $lcm;
        })(1);

        console.log("LCM: ".bold + $lcm.toString().cyan, Verbose.DEBUG);

        // only handle the non-trivial case
        if($lcm>1) {
            // REMARK: We assume at most one fraction in each term
            function reduce(expr) {
                return expr.replace(/(\d+)\/(\d+)/g, function(a, num, den){ return $lcm*+num/+den })
            }
            var lhs = reduce(sides[0]);
            var rhs = reduce(sides[1]);
            expr = lhs + op + rhs;
        }
        log("EXPR (after): ".bold + expr + "\n", Verbose.DEBUG);
        return expr;
    }

    /** Convert the simplified formula produced by RedLog to Z3py format
     *  Example:
     *  input:  "((n >= 0 and y >= 0) and not(0 <= 0 and (n > 0 impl 0 <= 0) and (n <= 0 impl  - x <= 0)))"
     *  output: "And(And(n >= 0 , y >= 0) ,Not(And(0 <= 0 , Implies(n > 0 ,l 0 <= 0) , Implies(n <= 0 ,l  - x <= 0))))"
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
            stubs.forEach(function(s,i){
                expr = expr.replace('$' + i, s);
            });
            return expr;
        })(expr).replace(/ = /g, '==');
    }

    function verify_poly(coeff) {
        Timer.tick('verify_poly');
        log();
        log("Coefficients: ".bold + coeff);
        log("Pre-condition:  ".bold + pre);
        log("Post-condition: ".bold + post);
        log("Constraint:\t".bold + ruleRL);

        var template1 = template;
        for(var name in coeff){
            template1 = template1.replace(new RegExp(name,'g'), coeff[name]);
        }
        var polyRL = bind_coeff(coeff, template1 + '>=0');

        for(var i=0; i<var_names.length; i++)
            polyRL = 'ex(' + var_names[i] + ',' + polyRL.replace(new RegExp('\\$'+(i+1), 'g'), var_names[i]) + ')';

        var _ruleRL = Node.to_redlog_formula(function(expr){
            return expr.replace(invariant_regex, '(' + template + ')');
//            return reduce_redlog_formula(coeff, expr.replace(invariant_regex, '(' + template + ')'));
        })(rule);

        for(var name in coeff){
            //console.log('Name:' + name + ' Val:' + coeff[name] + "\nrule: " + _ruleRL);
            _ruleRL = _ruleRL.replace(new RegExp(name,'g'), coeff[name]);
        }

        var redlog = 'all(x, all(y, all(n, (' + testcase.domain + ') impl (' + _ruleRL + '))))';
        redlog = 'load_package redlog; rlset ' + Settings.redlog.theory + '; poly := ' + polyRL
                + '; invariant := ' + redlog + '; feasible := rlsimpl rlqe invariant;';

        //redlog = redlog.replace(/\+0/g,''); // remove "+0+0...+0" substring

        var command = "echo '" + redlog + "' | tee solver.log | ./reduce";

        result = sh.exec(command).stdout;
        log();
        log("Redlog code\n".bold + redlog, Verbose.INFORMATIVE);
        log("Polynomial\n".bold + template1, Verbose.INFORMATIVE);
        log("Result\n".bold + result);
        Timer.tick('verify_poly');

        if(/:= false/.test(result) || !/:= true/.test(result)) {
            var cex = 'load_package redlog; rlset ' + Settings.redlog.theory + '; find_cex := ex(x, ex(y, ex(n, (' + testcase.domain + ')';
            var point;
            var cex_desc;
            var constraints = [];

            while(constraints.length<3) {
                var cex1 = cex + (constraints.length ? ' and ' : '') + constraints.join(' and ') + ' and not (' + _ruleRL + ')))); cex := rlqea find_cex;';
                var cex_desc1 = sh.exec('echo "' + cex1 + '" | tee cex.log | ./reduce').stdout;
                log("Resolving a Cex with Redlog:\n\n".bold + cex_desc1);
                if(!cex_desc) cex_desc = cex_desc1;

                if(Settings.redlog.theory=='pasf') {
                    cex1 = cex_desc1.substr(cex_desc1.indexOf('true')).replace(/\n/g,'').match(/{[^}]+/)[0].substr(1);
                    if(cex1) {
                        if(/= *g/.test(cex1)) { //found auxiliary variables
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
                    if(!/^  *2/.test(lines[i])) continue;
                    for(var k=0,shift=0; k<lines[i].length; k++){
                        if(lines[i][k]!=2) continue;
                        lines[i+1] = lines[i+1].insertAt('**2',k+shift);
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
                    console.log("Z3 formula for generating Cex:\n".bold + cex_desc.yellow);
                    var z3_prog = "from z3 import *\n" + var_names.map(function(name){ return name + " = Int('" + name + "')\n" }).join('');
                    z3_prog += "s = Solver()\ns.add(" + cex_desc + ")\ns.check()\nprint s.model()";
                    var result = sh.exec('echo "' + z3_prog + '" | tee z3.cex.log | python -').stdout;
                    // should be sat
                    if(result[0]=='[') {
                        eval('var ' + var_names.toString() + ';'
                             + result.substring(1,result.length-2) + ';'
                             + 'point = [' + var_names + ']');
                        point.forEach(function(p,i){ point[i] = p ? p : 0 });
                    }else {
                        console.log("\n"+'[Warning] Z3 cannot resolve a counter-example '.bold +"(check z3.cex.log for details):\n" + result);
                        throw 'Program aborted.';
                    }
                }
            }
            if(!point) {
                  //var sampler = testcase.sampler;
                  console.log('[Error] Invalid counter example.'.bold);
                  throw 'Program aborted.';
                  //point = sampler();
            }
            console.log('Add Cex to the sample space:'.bold + '(' + point.toString().yellow + ")\n");
            return [false, point.join(' ')];
        }
        return [true, undefined];
    }

    function find_right_paren_pos(str, start) {
        if(str[start]!='(') return str;
        var c = 1, ptr = start+1;
        while(c>0 && ptr<str.length) {
            switch(str[ptr]){
                case '(': c++; break;
                case ')': c--; break;
            }
            ptr++;
        }
        return ptr - 1;
    }

    function simplify(expr) {
        /* substitute all sub-expression by thir values, e.g., (1+2) by 3 */
        var expr1 = '';
            expr1 = expr.replace(/\(([\d\+\-]+)+\)/g, function(a,b) { return eval(b) });
        while(expr!=expr1) {
            expr = expr1;
            expr1 = expr.replace(/\(([\d\+\-]+)+\)/g, function(a,b) { return eval(b) });
        };
        expr = expr.replace(/\+0/g,'').replace(/0\+/g,'');
        return expr;
    }

    /* eliminate denominator of numbers in formula */
    function normalize(coeff, expr, has_var, op){
        if(!op) {
            var ops = ['<=','>=','<','>','=='];
            for(var i=0; i<ops.length; i++) {
                var expr1 = normalize(coeff, expr, has_var, ops[i]);
                if(expr1) return expr1;
            }
            return expr;
        }
        if(expr.indexOf(op)==-1) return '';

        Timer.tick('normalization');

        log("EXPR (before): ".bold + expr, Verbose.DEBUG);

        /*
        for(var name in coeff) {
            if(coeff[name]!=0) continue;
            while(true) {
                var pos = expr.indexOf(name);
                if(pos<0) break;
                var left_paren_pos = expr.indexOf('(', pos);
                var right_paren_pos = find_right_paren_pos(expr, left_paren_pos);
                expr = expr.substring(0, pos) + '0' + expr.substring(right_paren_pos+1);
            }
        }
        log("EXPR (zero coeff removed): ".bold + expr, Verbose.DEBUG);
        */
        /* substitute all sub-expression by thir values (for splitting) */
        expr = expr.replace(/\(([\d\+\-]+)\)/g, function(a,b) { return eval(b) });
        //expr = expr.replace(/(I?)(\([\d\+\-]+\))/g, function(a,b,c){
        //    return b ? 'I('+eval(c)+')' : eval(c) // note case I(1+2)
        //});

        log("EXPR (sub-exp removed): ".bold + expr, Verbose.DEBUG);

        expr = expr.replace(/\(\(([\-\d\/]+)\)\)\*\*(\d+)/g, function(a, frac, deg){
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

        // only handle the non-trivial case
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

                    var token = expr.substring(start+1, end); // not including parentheses

                    if(has_var) {
                        // REMARK: We assume at most one fraction in each term
                        var num_reduced = 0;
                        token = '(' + token.replace(/(\d+)\/(\d+)/g, function(a, num, den){ num_reduced++; return $lcm*+num/+den }) + ')';
                        //if(fraction products detected)
                        //    throw '[Error] Sorry! I don\'t handle multiplications of fractions by now!';
                        if(num_reduced==0)
                            token = $lcm + '*' + token;
                    }else {
                        token = $lcm + '*(' + token + ')';
                        //log("Token (before): ".bold + token, Verbose.DEBUG);
                        Timer.tick('symbolic');
                        switch(Settings.symbolic.evaluator) {
                            case 'python':
                                token = token.replace(/\/(\d+)/g, '\/$1.0');
                                var command = 'echo -n $(python -c "print ' + token + '" | sed \'s/\\..*$//\')';
                                token = sh.exec(command).stdout;
                                break;
                            case 'javascript':
                                token = token.replace(/\(([\d\-]+)\)\*\*(\d+)/g, function(a,b,c){ return 'Math.pow('+b+','+c+')' })
                                token = token.replace(/\(\(([^()]+)\)\)\*\*(\d+)/g, function(a,b,c){ return 'Math.pow('+b+','+c+')' })
                                log("Token (JSified): ".bold + token, Verbose.DEBUG);
                                token = round(eval(token),0); // token should be an integer after reduction
                                break;
                            case 'mathomatic':
                                var command = 'echo -n $(mathomatic -ceq "' + token + '" | tail -n1 | sed \'s/^.* \\([^ ][^ ]*\\)$/\\1/\')';
                                //log("Command: ".bold + command, Verbose.DEBUG);
                                token = sh.exec(command).stdout;
                                break;
                            default: throw 'Invalid mode: ' + Settings.symbolic.evaluator;
                        }
                        //log("Token (after): ".bold + token, Verbose.DEBUG);
                        Timer.tick('symbolic');
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
        Timer.tick('normalization');
        log("EXPR (after): ".bold + expr + "\n", Verbose.DEBUG);
        return expr;
    }

   var guess_invariant = function() {
       Timer.tick('guess_invariant');
       var coeff = null;
       var constraintsZ3 = [];
       var times_to_try = Settings.max_num_sample_verification;
       while(times_to_try-->0) {
           /* guess a set of coefficients */
           if(!coeff) {
               var new_coeff = refine_constraint(coeff_list, constraint, constraintsZ3);
               if(!new_coeff) return false;

               eval('coeff = ' + new_coeff);
               log("Guess: ".bold + coeff + "\n");
           }
           /* check if the guessed polynomial satisfies the rules at all sample points */
           var result = test_coeff(coeff, constraintsZ3);

           // yes
           if(result[0]) {
               result = verify_poly(coeff);
               if(result[0]) return true;
               if(!result[1]) return false;
               sample_space.unshift({point: result[1], toString: Sample.prototype.toString});
               //log("Sample space: ".bold + sample_space.map(function(s){ return s.toString() }).join(','));
               continue;
           }

           // no, generate a new constraint
           var new_constraint = result[1];
           new_constraint = new_constraint.replace(/\+0/g,'').replace(/0\+/g,'');

           //new_constraint = simplify(new_constraint);
           log("New constraint:\n".bold + new_constraint.yellow, Verbose.INFORMATIVE);
           constraintsZ3.push(new_constraint);
           coeff = null;
       }
       Timer.tick('guess_invariant');
   };


    if(guess_invariant())
        log("\n"+'Invariant has been proved successfully.'.yellow.bold);
    else {
        log();
        log("Pre-condition:  ".bold + pre);
        log("Post-condition: ".bold + post);
        log("Rules:\t".bold + ruleRL);
        log("\n"+'Failed to prove invariant.'.bold.red);
    }
    Timer.tick('main');
    log("\n"+"Profiling:".bold);
    for(var mark in Profiling) {
        log(mark + ":\t" + (Profiling[mark] + 's').cyan);
    }
    return;
}

main();
