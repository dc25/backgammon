"use strict";
// This object will hold all exports.
var Haste = {};

/* Thunk
   Creates a thunk representing the given closure.
   If the non-updatable flag is undefined, the thunk is updatable.
*/
function T(f, nu) {
    this.f = f;
    if(nu === undefined) {
        this.x = __updatable;
    }
}

/* Hint to optimizer that an imported symbol is strict. */
function __strict(x) {return x}

// A tailcall.
function F(f) {
    this.f = f;
}

// A partially applied function. Invariant: members are never thunks.
function PAP(f, args) {
    this.f = f;
    this.args = args;
    this.arity = f.length - args.length;
}

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

/* Generic apply.
   Applies a function *or* a partial application object to a list of arguments.
   See https://ghc.haskell.org/trac/ghc/wiki/Commentary/Rts/HaskellExecution/FunctionCalls
   for more information.
*/
function A(f, args) {
    while(true) {
        f = E(f);
        if(f instanceof F) {
            f = E(B(f));
        }
        if(f instanceof PAP) {
            // f is a partial application
            if(args.length == f.arity) {
                // Saturated application
                return f.f.apply(null, f.args.concat(args));
            } else if(args.length < f.arity) {
                // Application is still unsaturated
                return new PAP(f.f, f.args.concat(args));
            } else {
                // Application is oversaturated; 
                var f2 = f.f.apply(null, f.args.concat(args.slice(0, f.arity)));
                args = args.slice(f.arity);
                f = B(f2);
            }
        } else if(f instanceof Function) {
            if(args.length == f.length) {
                return f.apply(null, args);
            } else if(args.length < f.length) {
                return new PAP(f, args);
            } else {
                var f2 = f.apply(null, args.slice(0, f.length));
                args = args.slice(f.length);
                f = B(f2);
            }
        } else {
            return f;
        }
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            if(t.x === __updatable) {
                var f = t.f;
                t.f = __blackhole;
                t.x = f();
            } else {
                return t.f();
            }
        }
        return t.x;
    } else {
        return t;
    }
}

/* Bounce
   Bounce on a trampoline for as long as we get a function back.
*/
function B(f) {
    while(f instanceof F) {
        var fun = f.f;
        f.f = __blackhole;
        f = fun();
    }
    return f;
}

// Export Haste, A, B and E. Haste because we need to preserve exports, A, B
// and E because they're handy for Haste.Foreign.
if(!window) {
    var window = {};
}
window['Haste'] = Haste;
window['A'] = A;
window['E'] = E;
window['B'] = B;


/* Throw an error.
   We need to be able to use throw as an exception so we wrap it in a function.
*/
function die(err) {
    throw E(err);
}

function quot(a, b) {
    return (a-a%b)/b;
}

function quotRemI(a, b) {
    return [0, (a-a%b)/b, a%b];
}

// 32 bit integer multiplication, with correct overflow behavior
// note that |0 or >>>0 needs to be applied to the result, for int and word
// respectively.
if(Math.imul) {
    var imul = Math.imul;
} else {
    var imul = function(a, b) {
        // ignore high a * high a as the result will always be truncated
        var lows = (a & 0xffff) * (b & 0xffff); // low a * low b
        var aB = (a & 0xffff) * (b & 0xffff0000); // low a * high b
        var bA = (a & 0xffff0000) * (b & 0xffff); // low b * high a
        return lows + aB + bA; // sum will not exceed 52 bits, so it's safe
    }
}

function addC(a, b) {
    var x = a+b;
    return [0, x & 0xffffffff, x > 0x7fffffff];
}

function subC(a, b) {
    var x = a-b;
    return [0, x & 0xffffffff, x < -2147483648];
}

function sinh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / 2;
}

function tanh (arg) {
    return (Math.exp(arg) - Math.exp(-arg)) / (Math.exp(arg) + Math.exp(-arg));
}

function cosh (arg) {
    return (Math.exp(arg) + Math.exp(-arg)) / 2;
}

function isFloatFinite(x) {
    return isFinite(x);
}

function isDoubleFinite(x) {
    return isFinite(x);
}

function err(str) {
    die(toJSStr(str));
}

/* unpackCString#
   NOTE: update constructor tags if the code generator starts munging them.
*/
function unCStr(str) {return unAppCStr(str, [0]);}

function unFoldrCStr(str, f, z) {
    var acc = z;
    for(var i = str.length-1; i >= 0; --i) {
        acc = B(A(f, [str.charCodeAt(i), acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return [1,str.charCodeAt(i),new T(function() {
            return unAppCStr(str,chrs,i+1);
        })];
    }
}

function charCodeAt(str, i) {return str.charCodeAt(i);}

function fromJSStr(str) {
    return unCStr(E(str));
}

function toJSStr(hsstr) {
    var s = '';
    for(var str = E(hsstr); str[0] == 1; str = E(str[2])) {
        s += String.fromCharCode(E(str[1]));
    }
    return s;
}

// newMutVar
function nMV(val) {
    return ({x: val});
}

// readMutVar
function rMV(mv) {
    return mv.x;
}

// writeMutVar
function wMV(mv, val) {
    mv.x = val;
}

// atomicModifyMutVar
function mMV(mv, f) {
    var x = B(A(f, [mv.x]));
    mv.x = x[1];
    return x[2];
}

function localeEncoding() {
    var le = newByteArr(5);
    le['v']['i8'][0] = 'U'.charCodeAt(0);
    le['v']['i8'][1] = 'T'.charCodeAt(0);
    le['v']['i8'][2] = 'F'.charCodeAt(0);
    le['v']['i8'][3] = '-'.charCodeAt(0);
    le['v']['i8'][4] = '8'.charCodeAt(0);
    return le;
}

var isDoubleNaN = isNaN;
var isFloatNaN = isNaN;

function isDoubleInfinite(d) {
    return (d === Infinity);
}
var isFloatInfinite = isDoubleInfinite;

function isDoubleNegativeZero(x) {
    return (x===0 && (1/x)===-Infinity);
}
var isFloatNegativeZero = isDoubleNegativeZero;

function strEq(a, b) {
    return a == b;
}

function strOrd(a, b) {
    if(a < b) {
        return 0;
    } else if(a == b) {
        return 1;
    }
    return 2;
}

function jsCatch(act, handler) {
    try {
        return B(A(act,[0]));
    } catch(e) {
        return B(A(handler,[e, 0]));
    }
}

/* Haste represents constructors internally using 1 for the first constructor,
   2 for the second, etc.
   However, dataToTag should use 0, 1, 2, etc. Also, booleans might be unboxed.
 */
function dataToTag(x) {
    if(x instanceof Array) {
        return x[0];
    } else {
        return x;
    }
}

function __word_encodeDouble(d, e) {
    return d * Math.pow(2,e);
}

var __word_encodeFloat = __word_encodeDouble;
var jsRound = Math.round, rintDouble = jsRound, rintFloat = jsRound;
var jsTrunc = Math.trunc ? Math.trunc : function(x) {
    return x < 0 ? Math.ceil(x) : Math.floor(x);
};
function jsRoundW(n) {
    return Math.abs(jsTrunc(n));
}
var realWorld = undefined;
if(typeof _ == 'undefined') {
    var _ = undefined;
}

function popCnt64(i) {
    return popCnt(I_getBits(i,0)) + popCnt(I_getBits(i,1));
}

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
}

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
    if(x === 0) {
        return [0,1,0,0,0];
    }
    rts_scratchFloat[0] = x;
    var sign = x < 0 ? -1 : 1;
    var exp = ((rts_scratchW32[0] >> 23) & 0xff) - 150;
    var man = rts_scratchW32[0] & 0x7fffff;
    if(exp === 0) {
        ++exp;
    } else {
        man |= (1 << 23);
    }
    return [0, sign*man, exp];
}

function decodeDouble(x) {
    if(x === 0) {
        // GHC 7.10+ *really* doesn't like 0 to be represented as anything
        // but zeroes all the way.
        return [0,1,0,0,0];
    }
    rts_scratchDouble[0] = x;
    var sign = x < 0 ? -1 : 1;
    var manHigh = rts_scratchW32[1] & 0xfffff;
    var manLow = rts_scratchW32[0];
    var exp = ((rts_scratchW32[1] >> 20) & 0x7ff) - 1075;
    if(exp === 0) {
        ++exp;
    } else {
        manHigh |= (1 << 20);
    }
    return [0, sign, manHigh, manLow, exp];
}

function jsAlert(val) {
    if(typeof alert != 'undefined') {
        alert(val);
    } else {
        print(val);
    }
}

function jsLog(val) {
    console.log(val);
}

function jsPrompt(str) {
    var val;
    if(typeof prompt != 'undefined') {
        val = prompt(str);
    } else {
        print(str);
        val = readline();
    }
    return val == undefined ? '' : val.toString();
}

function jsEval(str) {
    var x = eval(str);
    return x == undefined ? '' : x.toString();
}

function isNull(obj) {
    return obj === null;
}

function jsRead(str) {
    return Number(str);
}

function jsShowI(val) {return val.toString();}
function jsShow(val) {
    var ret = val.toString();
    return val == Math.round(val) ? ret + '.0' : ret;
}

window['jsGetMouseCoords'] = function jsGetMouseCoords(e) {
    var posx = 0;
    var posy = 0;
    if (!e) var e = window.event;
    if (e.pageX || e.pageY) 	{
	posx = e.pageX;
	posy = e.pageY;
    }
    else if (e.clientX || e.clientY) 	{
	posx = e.clientX + document.body.scrollLeft
	    + document.documentElement.scrollLeft;
	posy = e.clientY + document.body.scrollTop
	    + document.documentElement.scrollTop;
    }
    return [posx - (e.currentTarget.offsetLeft || 0),
	    posy - (e.currentTarget.offsetTop || 0)];
}

function jsGet(elem, prop) {
    return elem[prop].toString();
}

function jsSet(elem, prop, val) {
    elem[prop] = val;
}

function jsGetAttr(elem, prop) {
    if(elem.hasAttribute(prop)) {
        return elem.getAttribute(prop).toString();
    } else {
        return "";
    }
}

function jsSetAttr(elem, prop, val) {
    elem.setAttribute(prop, val);
}

function jsGetStyle(elem, prop) {
    return elem.style[prop].toString();
}

function jsSetStyle(elem, prop, val) {
    elem.style[prop] = val;
}

function jsKillChild(child, parent) {
    parent.removeChild(child);
}

function jsClearChildren(elem) {
    while(elem.hasChildNodes()){
        elem.removeChild(elem.lastChild);
    }
}

function jsFind(elem) {
    var e = document.getElementById(elem)
    if(e) {
        return [1,e];
    }
    return [0];
}

function jsElemsByClassName(cls) {
    var es = document.getElementsByClassName(cls);
    var els = [0];

    for (var i = es.length-1; i >= 0; --i) {
        els = [1, es[i], els];
    }
    return els;
}

function jsQuerySelectorAll(elem, query) {
    var els = [0], nl;

    if (!elem || typeof elem.querySelectorAll !== 'function') {
        return els;
    }

    nl = elem.querySelectorAll(query);

    for (var i = nl.length-1; i >= 0; --i) {
        els = [1, nl[i], els];
    }

    return els;
}

function jsCreateElem(tag) {
    return document.createElement(tag);
}

function jsCreateTextNode(str) {
    return document.createTextNode(str);
}

function jsGetChildBefore(elem) {
    elem = elem.previousSibling;
    while(elem) {
        if(typeof elem.tagName != 'undefined') {
            return [1,elem];
        }
        elem = elem.previousSibling;
    }
    return [0];
}

function jsGetLastChild(elem) {
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,elem.childNodes[i]];
        }
    }
    return [0];
}


function jsGetFirstChild(elem) {
    var len = elem.childNodes.length;
    for(var i = 0; i < len; i++) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,elem.childNodes[i]];
        }
    }
    return [0];
}


function jsGetChildren(elem) {
    var children = [0];
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            children = [1, elem.childNodes[i], children];
        }
    }
    return children;
}

function jsSetChildren(elem, children) {
    children = E(children);
    jsClearChildren(elem, 0);
    while(children[0] === 1) {
        elem.appendChild(E(children[1]));
        children = E(children[2]);
    }
}

function jsAppendChild(child, container) {
    container.appendChild(child);
}

function jsAddChildBefore(child, container, after) {
    container.insertBefore(child, after);
}

var jsRand = Math.random;

// Concatenate a Haskell list of JS strings
function jsCat(strs, sep) {
    var arr = [];
    strs = E(strs);
    while(strs[0]) {
        strs = E(strs);
        arr.push(E(strs[1]));
        strs = E(strs[2]);
    }
    return arr.join(sep);
}

// JSON stringify a string
function jsStringify(str) {
    return JSON.stringify(str);
}

// Parse a JSON message into a Haste.JSON.JSON value.
// As this pokes around inside Haskell values, it'll need to be updated if:
// * Haste.JSON.JSON changes;
// * E() starts to choke on non-thunks;
// * data constructor code generation changes; or
// * Just and Nothing change tags.
function jsParseJSON(str) {
    try {
        var js = JSON.parse(str);
        var hs = toHS(js);
    } catch(_) {
        return [0];
    }
    return [1,hs];
}

function toHS(obj) {
    switch(typeof obj) {
    case 'number':
        return [0, jsRead(obj)];
    case 'string':
        return [1, obj];
    case 'boolean':
        return [2, obj]; // Booleans are special wrt constructor tags!
    case 'object':
        if(obj instanceof Array) {
            return [3, arr2lst_json(obj, 0)];
        } else if (obj == null) {
            return [5];
        } else {
            // Object type but not array - it's a dictionary.
            // The RFC doesn't say anything about the ordering of keys, but
            // considering that lots of people rely on keys being "in order" as
            // defined by "the same way someone put them in at the other end,"
            // it's probably a good idea to put some cycles into meeting their
            // misguided expectations.
            var ks = [];
            for(var k in obj) {
                ks.unshift(k);
            }
            var xs = [0];
            for(var i = 0; i < ks.length; i++) {
                xs = [1, [0, ks[i], toHS(obj[ks[i]])], xs];
            }
            return [4, xs];
        }
    }
}

function arr2lst_json(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, toHS(arr[elem]), new T(function() {return arr2lst_json(arr,elem+1);}),true]
}

function ajaxReq(method, url, async, postdata, cb) {
    var xhr = new XMLHttpRequest();
    xhr.open(method, url, async);

    if(method == "POST") {
        xhr.setRequestHeader("Content-type",
                             "application/x-www-form-urlencoded");
    }
    xhr.onreadystatechange = function() {
        if(xhr.readyState == 4) {
            if(xhr.status == 200) {
                B(A(cb,[[1,xhr.responseText],0]));
            } else {
                B(A(cb,[[0],0])); // Nothing
            }
        }
    }
    xhr.send(postdata);
}

/* gettimeofday(2) */
function gettimeofday(tv, _tz) {
    var t = new Date().getTime();
    writeOffAddr("i32", 4, tv, 0, (t/1000)|0);
    writeOffAddr("i32", 4, tv, 1, ((t%1000)*1000)|0);
    return 0;
}

/* Utility functions for working with JSStrings. */

var _jss_singleton = String.fromCharCode;

function _jss_cons(c,s) {return String.fromCharCode(c)+s;}
function _jss_snoc(s,c) {return s+String.fromCharCode(c);}
function _jss_append(a,b) {return a+b;}
function _jss_len(s) {return s.length;}
function _jss_index(s,i) {return s.charCodeAt(i);}
function _jss_drop(s,i) {return s.substr(i);}
function _jss_substr(s,a,b) {return s.substr(a,b);}
function _jss_take(n,s) {return s.substr(0,n);}
// TODO: incorrect for some unusual characters.
function _jss_rev(s) {return s.split("").reverse().join("");}

function _jss_map(f,s) {
    f = E(f);
    var s2 = '';
    for(var i in s) {
        s2 += String.fromCharCode(E(f(s.charCodeAt(i))));
    }
    return s2;
}

function _jss_foldl(f,x,s) {
    f = E(f);
    for(var i in s) {
        x = A(f,[x,s.charCodeAt(i)]);
    }
    return x;
}

function _jss_re_match(s,re) {return s.search(re)>=0;}
function _jss_re_compile(re,fs) {return new RegExp(re,fs);}
function _jss_re_replace(s,re,rep) {return s.replace(re,rep);}

function _jss_re_find(re,s) {
    var a = s.match(re);
    return a ? mklst(a) : [0];
}

function mklst(arr) {
    var l = [0], len = arr.length-1;
    for(var i = 0; i <= len; ++i) {
        l = [1,arr[len-i],l];
    }
    return l;
}

// Create a little endian ArrayBuffer representation of something.
function toABHost(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    return a;
}

function toABSwap(v, n, x) {
    var a = new ArrayBuffer(n);
    new window[v](a)[0] = x;
    var bs = new Uint8Array(a);
    for(var i = 0, j = n-1; i < j; ++i, --j) {
        var tmp = bs[i];
        bs[i] = bs[j];
        bs[j] = tmp;
    }
    return a;
}

window['toABle'] = toABHost;
window['toABbe'] = toABSwap;

// Swap byte order if host is not little endian.
var buffer = new ArrayBuffer(2);
new DataView(buffer).setInt16(0, 256, true);
if(new Int16Array(buffer)[0] !== 256) {
    window['toABle'] = toABSwap;
    window['toABbe'] = toABHost;
}

// MVar implementation.
// Since Haste isn't concurrent, takeMVar and putMVar don't block on empty
// and full MVars respectively, but terminate the program since they would
// otherwise be blocking forever.

function newMVar() {
    return ({empty: true});
}

function tryTakeMVar(mv) {
    if(mv.empty) {
        return [0, 0, undefined];
    } else {
        var val = mv.x;
        mv.empty = true;
        mv.x = null;
        return [0, 1, val];
    }
}

function takeMVar(mv) {
    if(mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to take empty MVar!");
    }
    var val = mv.x;
    mv.empty = true;
    mv.x = null;
    return val;
}

function putMVar(mv, val) {
    if(!mv.empty) {
        // TODO: real BlockedOnDeadMVar exception, perhaps?
        err("Attempted to put full MVar!");
    }
    mv.empty = false;
    mv.x = val;
}

function tryPutMVar(mv, val) {
    if(!mv.empty) {
        return 0;
    } else {
        mv.empty = false;
        mv.x = val;
        return 1;
    }
}

function sameMVar(a, b) {
    return (a == b);
}

function isEmptyMVar(mv) {
    return mv.empty ? 1 : 0;
}

// Implementation of stable names.
// Unlike native GHC, the garbage collector isn't going to move data around
// in a way that we can detect, so each object could serve as its own stable
// name if it weren't for the fact we can't turn a JS reference into an
// integer.
// So instead, each object has a unique integer attached to it, which serves
// as its stable name.

var __next_stable_name = 1;
var __stable_table;

function makeStableName(x) {
    if(x instanceof Object) {
        if(!x.stableName) {
            x.stableName = __next_stable_name;
            __next_stable_name += 1;
        }
        return {type: 'obj', name: x.stableName};
    } else {
        return {type: 'prim', name: Number(x)};
    }
}

function eqStableName(x, y) {
    return (x.type == y.type && x.name == y.name) ? 1 : 0;
}

var Integer = function(bits, sign) {
  this.bits_ = [];
  this.sign_ = sign;

  var top = true;
  for (var i = bits.length - 1; i >= 0; i--) {
    var val = bits[i] | 0;
    if (!top || val != sign) {
      this.bits_[i] = val;
      top = false;
    }
  }
};

Integer.IntCache_ = {};

var I_fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Integer.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Integer([value | 0], value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Integer.IntCache_[value] = obj;
  }
  return obj;
};

var I_fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Integer.ZERO;
  } else if (value < 0) {
    return I_negate(I_fromNumber(-value));
  } else {
    var bits = [];
    var pow = 1;
    for (var i = 0; value >= pow; i++) {
      bits[i] = (value / pow) | 0;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return new Integer(bits, 0);
  }
};

var I_fromBits = function(bits) {
  var high = bits[bits.length - 1];
  return new Integer(bits, high & (1 << 31) ? -1 : 0);
};

var I_fromString = function(str, opt_radix) {
  if (str.length == 0) {
    throw Error('number format error: empty string');
  }

  var radix = opt_radix || 10;
  if (radix < 2 || 36 < radix) {
    throw Error('radix out of range: ' + radix);
  }

  if (str.charAt(0) == '-') {
    return I_negate(I_fromString(str.substring(1), radix));
  } else if (str.indexOf('-') >= 0) {
    throw Error('number format error: interior "-" character');
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 8));

  var result = Integer.ZERO;
  for (var i = 0; i < str.length; i += 8) {
    var size = Math.min(8, str.length - i);
    var value = parseInt(str.substring(i, i + size), radix);
    if (size < 8) {
      var power = I_fromNumber(Math.pow(radix, size));
      result = I_add(I_mul(result, power), I_fromNumber(value));
    } else {
      result = I_mul(result, radixToPower);
      result = I_add(result, I_fromNumber(value));
    }
  }
  return result;
};


Integer.TWO_PWR_32_DBL_ = (1 << 16) * (1 << 16);
Integer.ZERO = I_fromInt(0);
Integer.ONE = I_fromInt(1);
Integer.TWO_PWR_24_ = I_fromInt(1 << 24);

var I_toInt = function(self) {
  return self.bits_.length > 0 ? self.bits_[0] : self.sign_;
};

var I_toWord = function(self) {
  return I_toInt(self) >>> 0;
};

var I_toNumber = function(self) {
  if (isNegative(self)) {
    return -I_toNumber(I_negate(self));
  } else {
    var val = 0;
    var pow = 1;
    for (var i = 0; i < self.bits_.length; i++) {
      val += I_getBitsUnsigned(self, i) * pow;
      pow *= Integer.TWO_PWR_32_DBL_;
    }
    return val;
  }
};

var I_getBits = function(self, index) {
  if (index < 0) {
    return 0;
  } else if (index < self.bits_.length) {
    return self.bits_[index];
  } else {
    return self.sign_;
  }
};

var I_getBitsUnsigned = function(self, index) {
  var val = I_getBits(self, index);
  return val >= 0 ? val : Integer.TWO_PWR_32_DBL_ + val;
};

var getSign = function(self) {
  return self.sign_;
};

var isZero = function(self) {
  if (self.sign_ != 0) {
    return false;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    if (self.bits_[i] != 0) {
      return false;
    }
  }
  return true;
};

var isNegative = function(self) {
  return self.sign_ == -1;
};

var isOdd = function(self) {
  return (self.bits_.length == 0) && (self.sign_ == -1) ||
         (self.bits_.length > 0) && ((self.bits_[0] & 1) != 0);
};

var I_equals = function(self, other) {
  if (self.sign_ != other.sign_) {
    return false;
  }
  var len = Math.max(self.bits_.length, other.bits_.length);
  for (var i = 0; i < len; i++) {
    if (I_getBits(self, i) != I_getBits(other, i)) {
      return false;
    }
  }
  return true;
};

var I_notEquals = function(self, other) {
  return !I_equals(self, other);
};

var I_greaterThan = function(self, other) {
  return I_compare(self, other) > 0;
};

var I_greaterThanOrEqual = function(self, other) {
  return I_compare(self, other) >= 0;
};

var I_lessThan = function(self, other) {
  return I_compare(self, other) < 0;
};

var I_lessThanOrEqual = function(self, other) {
  return I_compare(self, other) <= 0;
};

var I_compare = function(self, other) {
  var diff = I_sub(self, other);
  if (isNegative(diff)) {
    return -1;
  } else if (isZero(diff)) {
    return 0;
  } else {
    return +1;
  }
};

var I_compareInt = function(self, other) {
  return I_compare(self, I_fromInt(other));
}

var shorten = function(self, numBits) {
  var arr_index = (numBits - 1) >> 5;
  var bit_index = (numBits - 1) % 32;
  var bits = [];
  for (var i = 0; i < arr_index; i++) {
    bits[i] = I_getBits(self, i);
  }
  var sigBits = bit_index == 31 ? 0xFFFFFFFF : (1 << (bit_index + 1)) - 1;
  var val = I_getBits(self, arr_index) & sigBits;
  if (val & (1 << bit_index)) {
    val |= 0xFFFFFFFF - sigBits;
    bits[arr_index] = val;
    return new Integer(bits, -1);
  } else {
    bits[arr_index] = val;
    return new Integer(bits, 0);
  }
};

var I_negate = function(self) {
  return I_add(not(self), Integer.ONE);
};

var I_add = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  var carry = 0;

  for (var i = 0; i <= len; i++) {
    var a1 = I_getBits(self, i) >>> 16;
    var a0 = I_getBits(self, i) & 0xFFFF;

    var b1 = I_getBits(other, i) >>> 16;
    var b0 = I_getBits(other, i) & 0xFFFF;

    var c0 = carry + a0 + b0;
    var c1 = (c0 >>> 16) + a1 + b1;
    carry = c1 >>> 16;
    c0 &= 0xFFFF;
    c1 &= 0xFFFF;
    arr[i] = (c1 << 16) | c0;
  }
  return I_fromBits(arr);
};

var I_sub = function(self, other) {
  return I_add(self, I_negate(other));
};

var I_mul = function(self, other) {
  if (isZero(self)) {
    return Integer.ZERO;
  } else if (isZero(other)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_mul(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_mul(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_mul(self, I_negate(other)));
  }

  if (I_lessThan(self, Integer.TWO_PWR_24_) &&
      I_lessThan(other, Integer.TWO_PWR_24_)) {
    return I_fromNumber(I_toNumber(self) * I_toNumber(other));
  }

  var len = self.bits_.length + other.bits_.length;
  var arr = [];
  for (var i = 0; i < 2 * len; i++) {
    arr[i] = 0;
  }
  for (var i = 0; i < self.bits_.length; i++) {
    for (var j = 0; j < other.bits_.length; j++) {
      var a1 = I_getBits(self, i) >>> 16;
      var a0 = I_getBits(self, i) & 0xFFFF;

      var b1 = I_getBits(other, j) >>> 16;
      var b0 = I_getBits(other, j) & 0xFFFF;

      arr[2 * i + 2 * j] += a0 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j);
      arr[2 * i + 2 * j + 1] += a1 * b0;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 1] += a0 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 1);
      arr[2 * i + 2 * j + 2] += a1 * b1;
      Integer.carry16_(arr, 2 * i + 2 * j + 2);
    }
  }

  for (var i = 0; i < len; i++) {
    arr[i] = (arr[2 * i + 1] << 16) | arr[2 * i];
  }
  for (var i = len; i < 2 * len; i++) {
    arr[i] = 0;
  }
  return new Integer(arr, 0);
};

Integer.carry16_ = function(bits, index) {
  while ((bits[index] & 0xFFFF) != bits[index]) {
    bits[index + 1] += bits[index] >>> 16;
    bits[index] &= 0xFFFF;
  }
};

var I_mod = function(self, other) {
  return I_rem(I_add(other, I_rem(self, other)), other);
}

var I_div = function(self, other) {
  if(I_greaterThan(self, Integer.ZERO) != I_greaterThan(other, Integer.ZERO)) {
    if(I_rem(self, other) != Integer.ZERO) {
      return I_sub(I_quot(self, other), Integer.ONE);
    }
  }
  return I_quot(self, other);
}

var I_quotRem = function(self, other) {
  return [0, I_quot(self, other), I_rem(self, other)];
}

var I_divMod = function(self, other) {
  return [0, I_div(self, other), I_mod(self, other)];
}

var I_quot = function(self, other) {
  if (isZero(other)) {
    throw Error('division by zero');
  } else if (isZero(self)) {
    return Integer.ZERO;
  }

  if (isNegative(self)) {
    if (isNegative(other)) {
      return I_quot(I_negate(self), I_negate(other));
    } else {
      return I_negate(I_quot(I_negate(self), other));
    }
  } else if (isNegative(other)) {
    return I_negate(I_quot(self, I_negate(other)));
  }

  var res = Integer.ZERO;
  var rem = self;
  while (I_greaterThanOrEqual(rem, other)) {
    var approx = Math.max(1, Math.floor(I_toNumber(rem) / I_toNumber(other)));
    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);
    var approxRes = I_fromNumber(approx);
    var approxRem = I_mul(approxRes, other);
    while (isNegative(approxRem) || I_greaterThan(approxRem, rem)) {
      approx -= delta;
      approxRes = I_fromNumber(approx);
      approxRem = I_mul(approxRes, other);
    }

    if (isZero(approxRes)) {
      approxRes = Integer.ONE;
    }

    res = I_add(res, approxRes);
    rem = I_sub(rem, approxRem);
  }
  return res;
};

var I_rem = function(self, other) {
  return I_sub(self, I_mul(I_quot(self, other), other));
};

var not = function(self) {
  var len = self.bits_.length;
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = ~self.bits_[i];
  }
  return new Integer(arr, ~self.sign_);
};

var I_and = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) & I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ & other.sign_);
};

var I_or = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) | I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ | other.sign_);
};

var I_xor = function(self, other) {
  var len = Math.max(self.bits_.length, other.bits_.length);
  var arr = [];
  for (var i = 0; i < len; i++) {
    arr[i] = I_getBits(self, i) ^ I_getBits(other, i);
  }
  return new Integer(arr, self.sign_ ^ other.sign_);
};

var I_shiftLeft = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length + arr_delta + (bit_delta > 0 ? 1 : 0);
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i - arr_delta) << bit_delta) |
               (I_getBits(self, i - arr_delta - 1) >>> (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i - arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_shiftRight = function(self, numBits) {
  var arr_delta = numBits >> 5;
  var bit_delta = numBits % 32;
  var len = self.bits_.length - arr_delta;
  var arr = [];
  for (var i = 0; i < len; i++) {
    if (bit_delta > 0) {
      arr[i] = (I_getBits(self, i + arr_delta) >>> bit_delta) |
               (I_getBits(self, i + arr_delta + 1) << (32 - bit_delta));
    } else {
      arr[i] = I_getBits(self, i + arr_delta);
    }
  }
  return new Integer(arr, self.sign_);
};

var I_signum = function(self) {
  var cmp = I_compare(self, Integer.ZERO);
  if(cmp > 0) {
    return Integer.ONE
  }
  if(cmp < 0) {
    return I_sub(Integer.ZERO, Integer.ONE);
  }
  return Integer.ZERO;
};

var I_abs = function(self) {
  if(I_compare(self, Integer.ZERO) < 0) {
    return I_sub(Integer.ZERO, self);
  }
  return self;
};

var I_decodeDouble = function(x) {
  var dec = decodeDouble(x);
  var mantissa = I_fromBits([dec[3], dec[2]]);
  if(dec[1] < 0) {
    mantissa = I_negate(mantissa);
  }
  return [0, dec[4], mantissa];
}

var I_toString = function(self) {
  var radix = 10;

  if (isZero(self)) {
    return '0';
  } else if (isNegative(self)) {
    return '-' + I_toString(I_negate(self));
  }

  var radixToPower = I_fromNumber(Math.pow(radix, 6));

  var rem = self;
  var result = '';
  while (true) {
    var remDiv = I_div(rem, radixToPower);
    var intval = I_toInt(I_sub(rem, I_mul(remDiv, radixToPower)));
    var digits = intval.toString();

    rem = remDiv;
    if (isZero(rem)) {
      return digits + result;
    } else {
      while (digits.length < 6) {
        digits = '0' + digits;
      }
      result = '' + digits + result;
    }
  }
};

var I_fromRat = function(a, b) {
    return I_toNumber(a) / I_toNumber(b);
}

function I_fromInt64(x) {
    return I_fromBits([x.getLowBits(), x.getHighBits()]);
}

function I_toInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

function I_fromWord64(x) {
    return x;
}

function I_toWord64(x) {
    return I_rem(I_add(__w64_max, x), __w64_max);
}

// Copyright 2009 The Closure Library Authors. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//      http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS-IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

var Long = function(low, high) {
  this.low_ = low | 0;
  this.high_ = high | 0;
};

Long.IntCache_ = {};

Long.fromInt = function(value) {
  if (-128 <= value && value < 128) {
    var cachedObj = Long.IntCache_[value];
    if (cachedObj) {
      return cachedObj;
    }
  }

  var obj = new Long(value | 0, value < 0 ? -1 : 0);
  if (-128 <= value && value < 128) {
    Long.IntCache_[value] = obj;
  }
  return obj;
};

Long.fromNumber = function(value) {
  if (isNaN(value) || !isFinite(value)) {
    return Long.ZERO;
  } else if (value <= -Long.TWO_PWR_63_DBL_) {
    return Long.MIN_VALUE;
  } else if (value + 1 >= Long.TWO_PWR_63_DBL_) {
    return Long.MAX_VALUE;
  } else if (value < 0) {
    return Long.fromNumber(-value).negate();
  } else {
    return new Long(
        (value % Long.TWO_PWR_32_DBL_) | 0,
        (value / Long.TWO_PWR_32_DBL_) | 0);
  }
};

Long.fromBits = function(lowBits, highBits) {
  return new Long(lowBits, highBits);
};

Long.TWO_PWR_16_DBL_ = 1 << 16;
Long.TWO_PWR_24_DBL_ = 1 << 24;
Long.TWO_PWR_32_DBL_ =
    Long.TWO_PWR_16_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_31_DBL_ =
    Long.TWO_PWR_32_DBL_ / 2;
Long.TWO_PWR_48_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_16_DBL_;
Long.TWO_PWR_64_DBL_ =
    Long.TWO_PWR_32_DBL_ * Long.TWO_PWR_32_DBL_;
Long.TWO_PWR_63_DBL_ =
    Long.TWO_PWR_64_DBL_ / 2;
Long.ZERO = Long.fromInt(0);
Long.ONE = Long.fromInt(1);
Long.NEG_ONE = Long.fromInt(-1);
Long.MAX_VALUE =
    Long.fromBits(0xFFFFFFFF | 0, 0x7FFFFFFF | 0);
Long.MIN_VALUE = Long.fromBits(0, 0x80000000 | 0);
Long.TWO_PWR_24_ = Long.fromInt(1 << 24);

Long.prototype.toInt = function() {
  return this.low_;
};

Long.prototype.toNumber = function() {
  return this.high_ * Long.TWO_PWR_32_DBL_ +
         this.getLowBitsUnsigned();
};

Long.prototype.getHighBits = function() {
  return this.high_;
};

Long.prototype.getLowBits = function() {
  return this.low_;
};

Long.prototype.getLowBitsUnsigned = function() {
  return (this.low_ >= 0) ?
      this.low_ : Long.TWO_PWR_32_DBL_ + this.low_;
};

Long.prototype.isZero = function() {
  return this.high_ == 0 && this.low_ == 0;
};

Long.prototype.isNegative = function() {
  return this.high_ < 0;
};

Long.prototype.isOdd = function() {
  return (this.low_ & 1) == 1;
};

Long.prototype.equals = function(other) {
  return (this.high_ == other.high_) && (this.low_ == other.low_);
};

Long.prototype.notEquals = function(other) {
  return (this.high_ != other.high_) || (this.low_ != other.low_);
};

Long.prototype.lessThan = function(other) {
  return this.compare(other) < 0;
};

Long.prototype.lessThanOrEqual = function(other) {
  return this.compare(other) <= 0;
};

Long.prototype.greaterThan = function(other) {
  return this.compare(other) > 0;
};

Long.prototype.greaterThanOrEqual = function(other) {
  return this.compare(other) >= 0;
};

Long.prototype.compare = function(other) {
  if (this.equals(other)) {
    return 0;
  }

  var thisNeg = this.isNegative();
  var otherNeg = other.isNegative();
  if (thisNeg && !otherNeg) {
    return -1;
  }
  if (!thisNeg && otherNeg) {
    return 1;
  }

  if (this.subtract(other).isNegative()) {
    return -1;
  } else {
    return 1;
  }
};

Long.prototype.negate = function() {
  if (this.equals(Long.MIN_VALUE)) {
    return Long.MIN_VALUE;
  } else {
    return this.not().add(Long.ONE);
  }
};

Long.prototype.add = function(other) {
  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 + b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 + b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 + b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 + b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.subtract = function(other) {
  return this.add(other.negate());
};

Long.prototype.multiply = function(other) {
  if (this.isZero()) {
    return Long.ZERO;
  } else if (other.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    return other.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  } else if (other.equals(Long.MIN_VALUE)) {
    return this.isOdd() ? Long.MIN_VALUE : Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().multiply(other.negate());
    } else {
      return this.negate().multiply(other).negate();
    }
  } else if (other.isNegative()) {
    return this.multiply(other.negate()).negate();
  }

  if (this.lessThan(Long.TWO_PWR_24_) &&
      other.lessThan(Long.TWO_PWR_24_)) {
    return Long.fromNumber(this.toNumber() * other.toNumber());
  }

  var a48 = this.high_ >>> 16;
  var a32 = this.high_ & 0xFFFF;
  var a16 = this.low_ >>> 16;
  var a00 = this.low_ & 0xFFFF;

  var b48 = other.high_ >>> 16;
  var b32 = other.high_ & 0xFFFF;
  var b16 = other.low_ >>> 16;
  var b00 = other.low_ & 0xFFFF;

  var c48 = 0, c32 = 0, c16 = 0, c00 = 0;
  c00 += a00 * b00;
  c16 += c00 >>> 16;
  c00 &= 0xFFFF;
  c16 += a16 * b00;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c16 += a00 * b16;
  c32 += c16 >>> 16;
  c16 &= 0xFFFF;
  c32 += a32 * b00;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a16 * b16;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c32 += a00 * b32;
  c48 += c32 >>> 16;
  c32 &= 0xFFFF;
  c48 += a48 * b00 + a32 * b16 + a16 * b32 + a00 * b48;
  c48 &= 0xFFFF;
  return Long.fromBits((c16 << 16) | c00, (c48 << 16) | c32);
};

Long.prototype.div = function(other) {
  if (other.isZero()) {
    throw Error('division by zero');
  } else if (this.isZero()) {
    return Long.ZERO;
  }

  if (this.equals(Long.MIN_VALUE)) {
    if (other.equals(Long.ONE) ||
        other.equals(Long.NEG_ONE)) {
      return Long.MIN_VALUE;
    } else if (other.equals(Long.MIN_VALUE)) {
      return Long.ONE;
    } else {
      var halfThis = this.shiftRight(1);
      var approx = halfThis.div(other).shiftLeft(1);
      if (approx.equals(Long.ZERO)) {
        return other.isNegative() ? Long.ONE : Long.NEG_ONE;
      } else {
        var rem = this.subtract(other.multiply(approx));
        var result = approx.add(rem.div(other));
        return result;
      }
    }
  } else if (other.equals(Long.MIN_VALUE)) {
    return Long.ZERO;
  }

  if (this.isNegative()) {
    if (other.isNegative()) {
      return this.negate().div(other.negate());
    } else {
      return this.negate().div(other).negate();
    }
  } else if (other.isNegative()) {
    return this.div(other.negate()).negate();
  }

  var res = Long.ZERO;
  var rem = this;
  while (rem.greaterThanOrEqual(other)) {
    var approx = Math.max(1, Math.floor(rem.toNumber() / other.toNumber()));

    var log2 = Math.ceil(Math.log(approx) / Math.LN2);
    var delta = (log2 <= 48) ? 1 : Math.pow(2, log2 - 48);

    var approxRes = Long.fromNumber(approx);
    var approxRem = approxRes.multiply(other);
    while (approxRem.isNegative() || approxRem.greaterThan(rem)) {
      approx -= delta;
      approxRes = Long.fromNumber(approx);
      approxRem = approxRes.multiply(other);
    }

    if (approxRes.isZero()) {
      approxRes = Long.ONE;
    }

    res = res.add(approxRes);
    rem = rem.subtract(approxRem);
  }
  return res;
};

Long.prototype.modulo = function(other) {
  return this.subtract(this.div(other).multiply(other));
};

Long.prototype.not = function() {
  return Long.fromBits(~this.low_, ~this.high_);
};

Long.prototype.and = function(other) {
  return Long.fromBits(this.low_ & other.low_,
                                 this.high_ & other.high_);
};

Long.prototype.or = function(other) {
  return Long.fromBits(this.low_ | other.low_,
                                 this.high_ | other.high_);
};

Long.prototype.xor = function(other) {
  return Long.fromBits(this.low_ ^ other.low_,
                                 this.high_ ^ other.high_);
};

Long.prototype.shiftLeft = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var low = this.low_;
    if (numBits < 32) {
      var high = this.high_;
      return Long.fromBits(
          low << numBits,
          (high << numBits) | (low >>> (32 - numBits)));
    } else {
      return Long.fromBits(0, low << (numBits - 32));
    }
  }
};

Long.prototype.shiftRight = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >> numBits);
    } else {
      return Long.fromBits(
          high >> (numBits - 32),
          high >= 0 ? 0 : -1);
    }
  }
};

Long.prototype.shiftRightUnsigned = function(numBits) {
  numBits &= 63;
  if (numBits == 0) {
    return this;
  } else {
    var high = this.high_;
    if (numBits < 32) {
      var low = this.low_;
      return Long.fromBits(
          (low >>> numBits) | (high << (32 - numBits)),
          high >>> numBits);
    } else if (numBits == 32) {
      return Long.fromBits(high, 0);
    } else {
      return Long.fromBits(high >>> (numBits - 32), 0);
    }
  }
};



// Int64
function hs_eqInt64(x, y) {return x.equals(y);}
function hs_neInt64(x, y) {return !x.equals(y);}
function hs_ltInt64(x, y) {return x.compare(y) < 0;}
function hs_leInt64(x, y) {return x.compare(y) <= 0;}
function hs_gtInt64(x, y) {return x.compare(y) > 0;}
function hs_geInt64(x, y) {return x.compare(y) >= 0;}
function hs_quotInt64(x, y) {return x.div(y);}
function hs_remInt64(x, y) {return x.modulo(y);}
function hs_plusInt64(x, y) {return x.add(y);}
function hs_minusInt64(x, y) {return x.subtract(y);}
function hs_timesInt64(x, y) {return x.multiply(y);}
function hs_negateInt64(x) {return x.negate();}
function hs_uncheckedIShiftL64(x, bits) {return x.shiftLeft(bits);}
function hs_uncheckedIShiftRA64(x, bits) {return x.shiftRight(bits);}
function hs_uncheckedIShiftRL64(x, bits) {return x.shiftRightUnsigned(bits);}
function hs_intToInt64(x) {return new Long(x, 0);}
function hs_int64ToInt(x) {return x.toInt();}



// Word64
function hs_wordToWord64(x) {
    return I_fromInt(x);
}
function hs_word64ToWord(x) {
    return I_toInt(x);
}
function hs_mkWord64(low, high) {
    return I_fromBits([low, high]);
}

var hs_and64 = I_and;
var hs_or64 = I_or;
var hs_xor64 = I_xor;
var __i64_all_ones = I_fromBits([0xffffffff, 0xffffffff]);
function hs_not64(x) {
    return I_xor(x, __i64_all_ones);
}
var hs_eqWord64 = I_equals;
var hs_neWord64 = I_notEquals;
var hs_ltWord64 = I_lessThan;
var hs_leWord64 = I_lessThanOrEqual;
var hs_gtWord64 = I_greaterThan;
var hs_geWord64 = I_greaterThanOrEqual;
var hs_quotWord64 = I_quot;
var hs_remWord64 = I_rem;
var __w64_max = I_fromBits([0,0,1]);
function hs_uncheckedShiftL64(x, bits) {
    return I_rem(I_shiftLeft(x, bits), __w64_max);
}
var hs_uncheckedShiftRL64 = I_shiftRight;
function hs_int64ToWord64(x) {
    var tmp = I_add(__w64_max, I_fromBits([x.getLowBits(), x.getHighBits()]));
    return I_rem(tmp, __w64_max);
}
function hs_word64ToInt64(x) {
    return Long.fromBits(I_getBits(x, 0), I_getBits(x, 1));
}

// Joseph Myers' MD5 implementation, ported to work on typed arrays.
// Used under the BSD license.
function md5cycle(x, k) {
    var a = x[0], b = x[1], c = x[2], d = x[3];

    a = ff(a, b, c, d, k[0], 7, -680876936);
    d = ff(d, a, b, c, k[1], 12, -389564586);
    c = ff(c, d, a, b, k[2], 17,  606105819);
    b = ff(b, c, d, a, k[3], 22, -1044525330);
    a = ff(a, b, c, d, k[4], 7, -176418897);
    d = ff(d, a, b, c, k[5], 12,  1200080426);
    c = ff(c, d, a, b, k[6], 17, -1473231341);
    b = ff(b, c, d, a, k[7], 22, -45705983);
    a = ff(a, b, c, d, k[8], 7,  1770035416);
    d = ff(d, a, b, c, k[9], 12, -1958414417);
    c = ff(c, d, a, b, k[10], 17, -42063);
    b = ff(b, c, d, a, k[11], 22, -1990404162);
    a = ff(a, b, c, d, k[12], 7,  1804603682);
    d = ff(d, a, b, c, k[13], 12, -40341101);
    c = ff(c, d, a, b, k[14], 17, -1502002290);
    b = ff(b, c, d, a, k[15], 22,  1236535329);

    a = gg(a, b, c, d, k[1], 5, -165796510);
    d = gg(d, a, b, c, k[6], 9, -1069501632);
    c = gg(c, d, a, b, k[11], 14,  643717713);
    b = gg(b, c, d, a, k[0], 20, -373897302);
    a = gg(a, b, c, d, k[5], 5, -701558691);
    d = gg(d, a, b, c, k[10], 9,  38016083);
    c = gg(c, d, a, b, k[15], 14, -660478335);
    b = gg(b, c, d, a, k[4], 20, -405537848);
    a = gg(a, b, c, d, k[9], 5,  568446438);
    d = gg(d, a, b, c, k[14], 9, -1019803690);
    c = gg(c, d, a, b, k[3], 14, -187363961);
    b = gg(b, c, d, a, k[8], 20,  1163531501);
    a = gg(a, b, c, d, k[13], 5, -1444681467);
    d = gg(d, a, b, c, k[2], 9, -51403784);
    c = gg(c, d, a, b, k[7], 14,  1735328473);
    b = gg(b, c, d, a, k[12], 20, -1926607734);

    a = hh(a, b, c, d, k[5], 4, -378558);
    d = hh(d, a, b, c, k[8], 11, -2022574463);
    c = hh(c, d, a, b, k[11], 16,  1839030562);
    b = hh(b, c, d, a, k[14], 23, -35309556);
    a = hh(a, b, c, d, k[1], 4, -1530992060);
    d = hh(d, a, b, c, k[4], 11,  1272893353);
    c = hh(c, d, a, b, k[7], 16, -155497632);
    b = hh(b, c, d, a, k[10], 23, -1094730640);
    a = hh(a, b, c, d, k[13], 4,  681279174);
    d = hh(d, a, b, c, k[0], 11, -358537222);
    c = hh(c, d, a, b, k[3], 16, -722521979);
    b = hh(b, c, d, a, k[6], 23,  76029189);
    a = hh(a, b, c, d, k[9], 4, -640364487);
    d = hh(d, a, b, c, k[12], 11, -421815835);
    c = hh(c, d, a, b, k[15], 16,  530742520);
    b = hh(b, c, d, a, k[2], 23, -995338651);

    a = ii(a, b, c, d, k[0], 6, -198630844);
    d = ii(d, a, b, c, k[7], 10,  1126891415);
    c = ii(c, d, a, b, k[14], 15, -1416354905);
    b = ii(b, c, d, a, k[5], 21, -57434055);
    a = ii(a, b, c, d, k[12], 6,  1700485571);
    d = ii(d, a, b, c, k[3], 10, -1894986606);
    c = ii(c, d, a, b, k[10], 15, -1051523);
    b = ii(b, c, d, a, k[1], 21, -2054922799);
    a = ii(a, b, c, d, k[8], 6,  1873313359);
    d = ii(d, a, b, c, k[15], 10, -30611744);
    c = ii(c, d, a, b, k[6], 15, -1560198380);
    b = ii(b, c, d, a, k[13], 21,  1309151649);
    a = ii(a, b, c, d, k[4], 6, -145523070);
    d = ii(d, a, b, c, k[11], 10, -1120210379);
    c = ii(c, d, a, b, k[2], 15,  718787259);
    b = ii(b, c, d, a, k[9], 21, -343485551);

    x[0] = add32(a, x[0]);
    x[1] = add32(b, x[1]);
    x[2] = add32(c, x[2]);
    x[3] = add32(d, x[3]);

}

function cmn(q, a, b, x, s, t) {
    a = add32(add32(a, q), add32(x, t));
    return add32((a << s) | (a >>> (32 - s)), b);
}

function ff(a, b, c, d, x, s, t) {
    return cmn((b & c) | ((~b) & d), a, b, x, s, t);
}

function gg(a, b, c, d, x, s, t) {
    return cmn((b & d) | (c & (~d)), a, b, x, s, t);
}

function hh(a, b, c, d, x, s, t) {
    return cmn(b ^ c ^ d, a, b, x, s, t);
}

function ii(a, b, c, d, x, s, t) {
    return cmn(c ^ (b | (~d)), a, b, x, s, t);
}

function md51(s, n) {
    var a = s['v']['w8'];
    var orig_n = n,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=n; i+=64) {
        md5cycle(state, md5blk(a.subarray(i-64, i)));
    }
    a = a.subarray(i-64);
    n = n < (i-64) ? 0 : n-(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<n; i++)
        tail[i>>2] |= a[i] << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = orig_n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s[i]
            + (s[i+1] << 8)
            + (s[i+2] << 16)
            + (s[i+3] << 24);
    }
    return md5blks;
}

var hex_chr = '0123456789abcdef'.split('');

function rhex(n)
{
    var s='', j=0;
    for(; j<4; j++)
        s += hex_chr[(n >> (j * 8 + 4)) & 0x0F]
        + hex_chr[(n >> (j * 8)) & 0x0F];
    return s;
}

function hex(x) {
    for (var i=0; i<x.length; i++)
        x[i] = rhex(x[i]);
    return x.join('');
}

function md5(s, n) {
    return hex(md51(s, n));
}

window['md5'] = md5;

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

function __hsbase_MD5Init(ctx) {}
// Note that this is a one time "update", since that's all that's used by
// GHC.Fingerprint.
function __hsbase_MD5Update(ctx, s, n) {
    ctx.md5 = md51(s, n);
}
function __hsbase_MD5Final(out, ctx) {
    var a = out['v']['i32'];
    a[0] = ctx.md5[0];
    a[1] = ctx.md5[1];
    a[2] = ctx.md5[2];
    a[3] = ctx.md5[3];
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = new Array(n);
    for(var i = 0; i < n; ++i) {
        arr[i] = x;
    }
    return arr;
}

// Create all views at once; perhaps it's wasteful, but it's better than having
// to check for the right view at each read or write.
function newByteArr(n) {
    // Pad the thing to multiples of 8.
    var padding = 8 - n % 8;
    if(padding < 8) {
        n += padding;
    }
    var arr = {};
    var buffer = new ArrayBuffer(n);
    var views = {};
    views['i8']  = new Int8Array(buffer);
    views['i16'] = new Int16Array(buffer);
    views['i32'] = new Int32Array(buffer);
    views['w8']  = new Uint8Array(buffer);
    views['w16'] = new Uint16Array(buffer);
    views['w32'] = new Uint32Array(buffer);
    views['f32'] = new Float32Array(buffer);
    views['f64'] = new Float64Array(buffer);
    arr['b'] = buffer;
    arr['v'] = views;
    // ByteArray and Addr are the same thing, so keep an offset if we get
    // casted.
    arr['off'] = 0;
    return arr;
}
window['newByteArr'] = newByteArr;

// An attempt at emulating pointers enough for ByteString and Text to be
// usable without patching the hell out of them.
// The general idea is that Addr# is a byte array with an associated offset.

function plusAddr(addr, off) {
    var newaddr = {};
    newaddr['off'] = addr['off'] + off;
    newaddr['b']   = addr['b'];
    newaddr['v']   = addr['v'];
    return newaddr;
}

function writeOffAddr(type, elemsize, addr, off, x) {
    addr['v'][type][addr.off/elemsize + off] = x;
}

function readOffAddr(type, elemsize, addr, off) {
    return addr['v'][type][addr.off/elemsize + off];
}

// Two addresses are equal if they point to the same buffer and have the same
// offset. For other comparisons, just use the offsets - nobody in their right
// mind would check if one pointer is less than another, completely unrelated,
// pointer and then act on that information anyway.
function addrEq(a, b) {
    if(a == b) {
        return true;
    }
    return a && b && a['b'] == b['b'] && a['off'] == b['off'];
}

function addrLT(a, b) {
    if(a) {
        return b && a['off'] < b['off'];
    } else {
        return (b != 0); 
    }
}

function addrGT(a, b) {
    if(b) {
        return a && a['off'] > b['off'];
    } else {
        return (a != 0);
    }
}

function withChar(f, charCode) {
    return f(String.fromCharCode(charCode)).charCodeAt(0);
}

function u_towlower(charCode) {
    return withChar(function(c) {return c.toLowerCase()}, charCode);
}

function u_towupper(charCode) {
    return withChar(function(c) {return c.toUpperCase()}, charCode);
}

var u_towtitle = u_towupper;

function u_iswupper(charCode) {
    var c = String.fromCharCode(charCode);
    return c == c.toUpperCase() && c != c.toLowerCase();
}

function u_iswlower(charCode) {
    var c = String.fromCharCode(charCode);
    return  c == c.toLowerCase() && c != c.toUpperCase();
}

function u_iswdigit(charCode) {
    return charCode >= 48 && charCode <= 57;
}

function u_iswcntrl(charCode) {
    return charCode <= 0x1f || charCode == 0x7f;
}

function u_iswspace(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(/\s/g,'') != c;
}

function u_iswalpha(charCode) {
    var c = String.fromCharCode(charCode);
    return c.replace(__hs_alphare, '') != c;
}

function u_iswalnum(charCode) {
    return u_iswdigit(charCode) || u_iswalpha(charCode);
}

function u_iswprint(charCode) {
    return !u_iswcntrl(charCode);
}

function u_gencat(c) {
    throw 'u_gencat is only supported with --full-unicode.';
}

// Regex that matches any alphabetic character in any language. Horrible thing.
var __hs_alphare = /[\u0041-\u005A\u0061-\u007A\u00AA\u00B5\u00BA\u00C0-\u00D6\u00D8-\u00F6\u00F8-\u02C1\u02C6-\u02D1\u02E0-\u02E4\u02EC\u02EE\u0370-\u0374\u0376\u0377\u037A-\u037D\u0386\u0388-\u038A\u038C\u038E-\u03A1\u03A3-\u03F5\u03F7-\u0481\u048A-\u0527\u0531-\u0556\u0559\u0561-\u0587\u05D0-\u05EA\u05F0-\u05F2\u0620-\u064A\u066E\u066F\u0671-\u06D3\u06D5\u06E5\u06E6\u06EE\u06EF\u06FA-\u06FC\u06FF\u0710\u0712-\u072F\u074D-\u07A5\u07B1\u07CA-\u07EA\u07F4\u07F5\u07FA\u0800-\u0815\u081A\u0824\u0828\u0840-\u0858\u08A0\u08A2-\u08AC\u0904-\u0939\u093D\u0950\u0958-\u0961\u0971-\u0977\u0979-\u097F\u0985-\u098C\u098F\u0990\u0993-\u09A8\u09AA-\u09B0\u09B2\u09B6-\u09B9\u09BD\u09CE\u09DC\u09DD\u09DF-\u09E1\u09F0\u09F1\u0A05-\u0A0A\u0A0F\u0A10\u0A13-\u0A28\u0A2A-\u0A30\u0A32\u0A33\u0A35\u0A36\u0A38\u0A39\u0A59-\u0A5C\u0A5E\u0A72-\u0A74\u0A85-\u0A8D\u0A8F-\u0A91\u0A93-\u0AA8\u0AAA-\u0AB0\u0AB2\u0AB3\u0AB5-\u0AB9\u0ABD\u0AD0\u0AE0\u0AE1\u0B05-\u0B0C\u0B0F\u0B10\u0B13-\u0B28\u0B2A-\u0B30\u0B32\u0B33\u0B35-\u0B39\u0B3D\u0B5C\u0B5D\u0B5F-\u0B61\u0B71\u0B83\u0B85-\u0B8A\u0B8E-\u0B90\u0B92-\u0B95\u0B99\u0B9A\u0B9C\u0B9E\u0B9F\u0BA3\u0BA4\u0BA8-\u0BAA\u0BAE-\u0BB9\u0BD0\u0C05-\u0C0C\u0C0E-\u0C10\u0C12-\u0C28\u0C2A-\u0C33\u0C35-\u0C39\u0C3D\u0C58\u0C59\u0C60\u0C61\u0C85-\u0C8C\u0C8E-\u0C90\u0C92-\u0CA8\u0CAA-\u0CB3\u0CB5-\u0CB9\u0CBD\u0CDE\u0CE0\u0CE1\u0CF1\u0CF2\u0D05-\u0D0C\u0D0E-\u0D10\u0D12-\u0D3A\u0D3D\u0D4E\u0D60\u0D61\u0D7A-\u0D7F\u0D85-\u0D96\u0D9A-\u0DB1\u0DB3-\u0DBB\u0DBD\u0DC0-\u0DC6\u0E01-\u0E30\u0E32\u0E33\u0E40-\u0E46\u0E81\u0E82\u0E84\u0E87\u0E88\u0E8A\u0E8D\u0E94-\u0E97\u0E99-\u0E9F\u0EA1-\u0EA3\u0EA5\u0EA7\u0EAA\u0EAB\u0EAD-\u0EB0\u0EB2\u0EB3\u0EBD\u0EC0-\u0EC4\u0EC6\u0EDC-\u0EDF\u0F00\u0F40-\u0F47\u0F49-\u0F6C\u0F88-\u0F8C\u1000-\u102A\u103F\u1050-\u1055\u105A-\u105D\u1061\u1065\u1066\u106E-\u1070\u1075-\u1081\u108E\u10A0-\u10C5\u10C7\u10CD\u10D0-\u10FA\u10FC-\u1248\u124A-\u124D\u1250-\u1256\u1258\u125A-\u125D\u1260-\u1288\u128A-\u128D\u1290-\u12B0\u12B2-\u12B5\u12B8-\u12BE\u12C0\u12C2-\u12C5\u12C8-\u12D6\u12D8-\u1310\u1312-\u1315\u1318-\u135A\u1380-\u138F\u13A0-\u13F4\u1401-\u166C\u166F-\u167F\u1681-\u169A\u16A0-\u16EA\u1700-\u170C\u170E-\u1711\u1720-\u1731\u1740-\u1751\u1760-\u176C\u176E-\u1770\u1780-\u17B3\u17D7\u17DC\u1820-\u1877\u1880-\u18A8\u18AA\u18B0-\u18F5\u1900-\u191C\u1950-\u196D\u1970-\u1974\u1980-\u19AB\u19C1-\u19C7\u1A00-\u1A16\u1A20-\u1A54\u1AA7\u1B05-\u1B33\u1B45-\u1B4B\u1B83-\u1BA0\u1BAE\u1BAF\u1BBA-\u1BE5\u1C00-\u1C23\u1C4D-\u1C4F\u1C5A-\u1C7D\u1CE9-\u1CEC\u1CEE-\u1CF1\u1CF5\u1CF6\u1D00-\u1DBF\u1E00-\u1F15\u1F18-\u1F1D\u1F20-\u1F45\u1F48-\u1F4D\u1F50-\u1F57\u1F59\u1F5B\u1F5D\u1F5F-\u1F7D\u1F80-\u1FB4\u1FB6-\u1FBC\u1FBE\u1FC2-\u1FC4\u1FC6-\u1FCC\u1FD0-\u1FD3\u1FD6-\u1FDB\u1FE0-\u1FEC\u1FF2-\u1FF4\u1FF6-\u1FFC\u2071\u207F\u2090-\u209C\u2102\u2107\u210A-\u2113\u2115\u2119-\u211D\u2124\u2126\u2128\u212A-\u212D\u212F-\u2139\u213C-\u213F\u2145-\u2149\u214E\u2183\u2184\u2C00-\u2C2E\u2C30-\u2C5E\u2C60-\u2CE4\u2CEB-\u2CEE\u2CF2\u2CF3\u2D00-\u2D25\u2D27\u2D2D\u2D30-\u2D67\u2D6F\u2D80-\u2D96\u2DA0-\u2DA6\u2DA8-\u2DAE\u2DB0-\u2DB6\u2DB8-\u2DBE\u2DC0-\u2DC6\u2DC8-\u2DCE\u2DD0-\u2DD6\u2DD8-\u2DDE\u2E2F\u3005\u3006\u3031-\u3035\u303B\u303C\u3041-\u3096\u309D-\u309F\u30A1-\u30FA\u30FC-\u30FF\u3105-\u312D\u3131-\u318E\u31A0-\u31BA\u31F0-\u31FF\u3400-\u4DB5\u4E00-\u9FCC\uA000-\uA48C\uA4D0-\uA4FD\uA500-\uA60C\uA610-\uA61F\uA62A\uA62B\uA640-\uA66E\uA67F-\uA697\uA6A0-\uA6E5\uA717-\uA71F\uA722-\uA788\uA78B-\uA78E\uA790-\uA793\uA7A0-\uA7AA\uA7F8-\uA801\uA803-\uA805\uA807-\uA80A\uA80C-\uA822\uA840-\uA873\uA882-\uA8B3\uA8F2-\uA8F7\uA8FB\uA90A-\uA925\uA930-\uA946\uA960-\uA97C\uA984-\uA9B2\uA9CF\uAA00-\uAA28\uAA40-\uAA42\uAA44-\uAA4B\uAA60-\uAA76\uAA7A\uAA80-\uAAAF\uAAB1\uAAB5\uAAB6\uAAB9-\uAABD\uAAC0\uAAC2\uAADB-\uAADD\uAAE0-\uAAEA\uAAF2-\uAAF4\uAB01-\uAB06\uAB09-\uAB0E\uAB11-\uAB16\uAB20-\uAB26\uAB28-\uAB2E\uABC0-\uABE2\uAC00-\uD7A3\uD7B0-\uD7C6\uD7CB-\uD7FB\uF900-\uFA6D\uFA70-\uFAD9\uFB00-\uFB06\uFB13-\uFB17\uFB1D\uFB1F-\uFB28\uFB2A-\uFB36\uFB38-\uFB3C\uFB3E\uFB40\uFB41\uFB43\uFB44\uFB46-\uFBB1\uFBD3-\uFD3D\uFD50-\uFD8F\uFD92-\uFDC7\uFDF0-\uFDFB\uFE70-\uFE74\uFE76-\uFEFC\uFF21-\uFF3A\uFF41-\uFF5A\uFF66-\uFFBE\uFFC2-\uFFC7\uFFCA-\uFFCF\uFFD2-\uFFD7\uFFDA-\uFFDC]/g;

// 2D Canvas drawing primitives.
function jsHasCtx2D(elem) {return !!elem.getContext;}
function jsGetCtx2D(elem) {return elem.getContext('2d');}
function jsBeginPath(ctx) {ctx.beginPath();}
function jsMoveTo(ctx, x, y) {ctx.moveTo(x, y);}
function jsLineTo(ctx, x, y) {ctx.lineTo(x, y);}
function jsStroke(ctx) {ctx.stroke();}
function jsFill(ctx) {ctx.fill();}
function jsRotate(ctx, radians) {ctx.rotate(radians);}
function jsTranslate(ctx, x, y) {ctx.translate(x, y);}
function jsScale(ctx, x, y) {ctx.scale(x, y);}
function jsPushState(ctx) {ctx.save();}
function jsPopState(ctx) {ctx.restore();}
function jsResetCanvas(el) {el.width = el.width;}
function jsDrawImage(ctx, img, x, y) {ctx.drawImage(img, x, y);}
function jsDrawImageClipped(ctx, img, x, y, cx, cy, cw, ch) {
    ctx.drawImage(img, cx, cy, cw, ch, x, y, cw, ch);
}
function jsDrawText(ctx, str, x, y) {ctx.fillText(str, x, y);}
function jsClip(ctx) {ctx.clip();}
function jsArc(ctx, x, y, radius, fromAngle, toAngle) {
    ctx.arc(x, y, radius, fromAngle, toAngle);
}
function jsCanvasToDataURL(el) {return el.toDataURL('image/png');}

// Simulate handles.
// When implementing new handles, remember that passed strings may be thunks,
// and so need to be evaluated before use.

function jsNewHandle(init, read, write, flush, close, seek, tell) {
    var h = {
        read: read || function() {},
        write: write || function() {},
        seek: seek || function() {},
        tell: tell || function() {},
        close: close || function() {},
        flush: flush || function() {}
    };
    init.call(h);
    return h;
}

function jsReadHandle(h, len) {return h.read(len);}
function jsWriteHandle(h, str) {return h.write(str);}
function jsFlushHandle(h) {return h.flush();}
function jsCloseHandle(h) {return h.close();}

function jsMkConWriter(op) {
    return function(str) {
        str = E(str);
        var lines = (this.buf + str).split('\n');
        for(var i = 0; i < lines.length-1; ++i) {
            op.call(console, lines[i]);
        }
        this.buf = lines[lines.length-1];
    }
}

function jsMkStdout() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.log),
        function() {console.log(this.buf); this.buf = '';}
    );
}

function jsMkStderr() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(_) {return '';},
        jsMkConWriter(console.warn),
        function() {console.warn(this.buf); this.buf = '';}
    );
}

function jsMkStdin() {
    return jsNewHandle(
        function() {this.buf = '';},
        function(len) {
            while(this.buf.length < len) {
                this.buf += prompt('[stdin]') + '\n';
            }
            var ret = this.buf.substr(0, len);
            this.buf = this.buf.substr(len);
            return ret;
        }
    );
}

// "Weak Pointers". Mostly useless implementation since
// JS does its own GC.

function mkWeak(key, val, fin) {
    fin = !fin? function() {}: fin;
    return {key: key, val: val, fin: fin};
}

function derefWeak(w) {
    return [0, 1, E(w).val];
}

function finalizeWeak(w) {
    return [0, B(A(E(w).fin, [0]))];
}

/* For foreign import ccall "wrapper" */
function createAdjustor(args, f, a, b) {
    return function(){
        var x = f.apply(null, arguments);
        while(x instanceof F) {x = x.f();}
        return x;
    };
}

var __apply = function(f,as) {
    var arr = [];
    for(; as[0] === 1; as = as[2]) {
        arr.push(as[1]);
    }
    arr.reverse();
    return f.apply(null, arr);
}
var __app0 = function(f) {return f();}
var __app1 = function(f,a) {return f(a);}
var __app2 = function(f,a,b) {return f(a,b);}
var __app3 = function(f,a,b,c) {return f(a,b,c);}
var __app4 = function(f,a,b,c,d) {return f(a,b,c,d);}
var __app5 = function(f,a,b,c,d,e) {return f(a,b,c,d,e);}
var __jsNull = function() {return null;}
var __eq = function(a,b) {return a===b;}
var __createJSFunc = function(arity, f){
    if(f instanceof Function && arity === f.length) {
        return (function() {
            var x = f.apply(null,arguments);
            if(x instanceof T) {
                if(x.f !== __blackhole) {
                    var ff = x.f;
                    x.f = __blackhole;
                    return x.x = ff();
                }
                return x.x;
            } else {
                while(x instanceof F) {
                    x = x.f();
                }
                return E(x);
            }
        });
    } else {
        return (function(){
            var as = Array.prototype.slice.call(arguments);
            as.push(0);
            return E(B(A(f,as)));
        });
    }
}


function __arr2lst(elem,arr) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, arr[elem],new T(function(){return __arr2lst(elem+1,arr);})]
}

function __lst2arr(xs) {
    var arr = [];
    xs = E(xs);
    for(;xs[0] === 1; xs = E(xs[2])) {
        arr.push(E(xs[1]));
    }
    return arr;
}

var __new = function() {return ({});}
var __set = function(o,k,v) {o[k]=v;}
var __get = function(o,k) {return o[k];}
var __has = function(o,k) {return o[k]!==undefined;}

var _0=function(_1,_){return [1,_1];},_2=function(_3){return E(_3);},_4=[0,_2,_0],_5=function(_6,_7,_){var _8=B(A(_6,[_])),_9=B(A(_7,[_]));return _8;},_a=function(_b,_c,_){var _d=B(A(_b,[_])),_e=_d,_f=B(A(_c,[_])),_g=_f;return new T(function(){return B(A(_e,[_g]));});},_h=function(_i,_j,_){var _k=B(A(_j,[_]));return _i;},_l=function(_m,_n,_){var _o=B(A(_n,[_])),_p=_o;return new T(function(){return B(A(_m,[_p]));});},_q=[0,_l,_h],_r=function(_s,_){return _s;},_t=function(_u,_v,_){var _w=B(A(_u,[_]));return new F(function(){return A(_v,[_]);});},_x=[0,_q,_r,_a,_t,_5],_y=function(_z,_A,_){var _B=B(A(_z,[_]));return new F(function(){return A(_A,[_B,_]);});},_C=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_D=new T(function(){return B(unCStr("base"));}),_E=new T(function(){return B(unCStr("IOException"));}),_F=[0],_G=new T(function(){var _H=hs_wordToWord64(4053623282),_I=hs_wordToWord64(3693590983);return [0,_H,_I,[0,_H,_I,_D,_C,_E],_F,_F];}),_J=function(_K){return E(_G);},_L=function(_M){return E(E(_M)[1]);},_N=function(_O,_P,_Q){var _R=B(A(_O,[_])),_S=B(A(_P,[_])),_T=hs_eqWord64(_R[1],_S[1]);if(!_T){return [0];}else{var _U=hs_eqWord64(_R[2],_S[2]);return (!_U)?[0]:[1,_Q];}},_V=function(_W){var _X=E(_W);return new F(function(){return _N(B(_L(_X[1])),_J,_X[2]);});},_Y=new T(function(){return B(unCStr(": "));}),_Z=new T(function(){return B(unCStr(")"));}),_10=new T(function(){return B(unCStr(" ("));}),_11=function(_12,_13){var _14=E(_12);if(!_14[0]){return E(_13);}else{var _15=_14[2],_16=new T(function(){return B(_11(_15,_13));});return [1,_14[1],_16];}},_17=new T(function(){return B(unCStr("interrupted"));}),_18=new T(function(){return B(unCStr("system error"));}),_19=new T(function(){return B(unCStr("unsatisified constraints"));}),_1a=new T(function(){return B(unCStr("user error"));}),_1b=new T(function(){return B(unCStr("permission denied"));}),_1c=new T(function(){return B(unCStr("illegal operation"));}),_1d=new T(function(){return B(unCStr("end of file"));}),_1e=new T(function(){return B(unCStr("resource exhausted"));}),_1f=new T(function(){return B(unCStr("resource busy"));}),_1g=new T(function(){return B(unCStr("does not exist"));}),_1h=new T(function(){return B(unCStr("already exists"));}),_1i=new T(function(){return B(unCStr("resource vanished"));}),_1j=new T(function(){return B(unCStr("timeout"));}),_1k=new T(function(){return B(unCStr("unsupported operation"));}),_1l=new T(function(){return B(unCStr("hardware fault"));}),_1m=new T(function(){return B(unCStr("inappropriate type"));}),_1n=new T(function(){return B(unCStr("invalid argument"));}),_1o=new T(function(){return B(unCStr("failed"));}),_1p=new T(function(){return B(unCStr("protocol error"));}),_1q=function(_1r,_1s){switch(E(_1r)){case 0:return new F(function(){return _11(_1h,_1s);});break;case 1:return new F(function(){return _11(_1g,_1s);});break;case 2:return new F(function(){return _11(_1f,_1s);});break;case 3:return new F(function(){return _11(_1e,_1s);});break;case 4:return new F(function(){return _11(_1d,_1s);});break;case 5:return new F(function(){return _11(_1c,_1s);});break;case 6:return new F(function(){return _11(_1b,_1s);});break;case 7:return new F(function(){return _11(_1a,_1s);});break;case 8:return new F(function(){return _11(_19,_1s);});break;case 9:return new F(function(){return _11(_18,_1s);});break;case 10:return new F(function(){return _11(_1p,_1s);});break;case 11:return new F(function(){return _11(_1o,_1s);});break;case 12:return new F(function(){return _11(_1n,_1s);});break;case 13:return new F(function(){return _11(_1m,_1s);});break;case 14:return new F(function(){return _11(_1l,_1s);});break;case 15:return new F(function(){return _11(_1k,_1s);});break;case 16:return new F(function(){return _11(_1j,_1s);});break;case 17:return new F(function(){return _11(_1i,_1s);});break;default:return new F(function(){return _11(_17,_1s);});}},_1t=new T(function(){return B(unCStr("}"));}),_1u=new T(function(){return B(unCStr("{handle: "));}),_1v=function(_1w,_1x,_1y,_1z,_1A,_1B){var _1C=new T(function(){var _1D=new T(function(){var _1E=new T(function(){var _1F=E(_1z);if(!_1F[0]){return E(_1B);}else{var _1G=new T(function(){var _1H=new T(function(){return B(_11(_Z,_1B));},1);return B(_11(_1F,_1H));},1);return B(_11(_10,_1G));}},1);return B(_1q(_1x,_1E));}),_1I=E(_1y);if(!_1I[0]){return E(_1D);}else{var _1J=new T(function(){return B(_11(_Y,_1D));},1);return B(_11(_1I,_1J));}}),_1K=E(_1A);if(!_1K[0]){var _1L=E(_1w);if(!_1L[0]){return E(_1C);}else{var _1M=E(_1L[1]);if(!_1M[0]){var _1N=_1M[1],_1O=new T(function(){var _1P=new T(function(){var _1Q=new T(function(){return B(_11(_Y,_1C));},1);return B(_11(_1t,_1Q));},1);return B(_11(_1N,_1P));},1);return new F(function(){return _11(_1u,_1O);});}else{var _1R=_1M[1],_1S=new T(function(){var _1T=new T(function(){var _1U=new T(function(){return B(_11(_Y,_1C));},1);return B(_11(_1t,_1U));},1);return B(_11(_1R,_1T));},1);return new F(function(){return _11(_1u,_1S);});}}}else{var _1V=new T(function(){return B(_11(_Y,_1C));},1);return new F(function(){return _11(_1K[1],_1V);});}},_1W=function(_1X){var _1Y=E(_1X);return new F(function(){return _1v(_1Y[1],_1Y[2],_1Y[3],_1Y[4],_1Y[6],_F);});},_1Z=function(_20,_21,_22){var _23=E(_21);return new F(function(){return _1v(_23[1],_23[2],_23[3],_23[4],_23[6],_22);});},_24=function(_25,_26){var _27=E(_25);return new F(function(){return _1v(_27[1],_27[2],_27[3],_27[4],_27[6],_26);});},_28=44,_29=93,_2a=91,_2b=function(_2c,_2d,_2e){var _2f=E(_2d);if(!_2f[0]){return new F(function(){return unAppCStr("[]",_2e);});}else{var _2g=_2f[1],_2h=_2f[2],_2i=new T(function(){var _2j=new T(function(){var _2k=[1,_29,_2e],_2l=function(_2m){var _2n=E(_2m);if(!_2n[0]){return E(_2k);}else{var _2o=_2n[1],_2p=_2n[2],_2q=new T(function(){var _2r=new T(function(){return B(_2l(_2p));});return B(A(_2c,[_2o,_2r]));});return [1,_28,_2q];}};return B(_2l(_2h));});return B(A(_2c,[_2g,_2j]));});return [1,_2a,_2i];}},_2s=function(_2t,_2u){return new F(function(){return _2b(_24,_2t,_2u);});},_2v=[0,_1Z,_1W,_2s],_2w=new T(function(){return [0,_J,_2v,_2x,_V,_1W];}),_2x=function(_2y){return [0,_2w,_2y];},_2z=[0],_2A=7,_2B=function(_2C){return [0,_2z,_2A,_F,_2C,_2z,_2z];},_2D=function(_2E,_){var _2F=new T(function(){var _2G=new T(function(){return B(_2B(_2E));});return B(_2x(_2G));});return new F(function(){return die(_2F);});},_2H=[0,_x,_y,_t,_r,_2D],_2I=[0,_2H,_2],_2J=function(_2K,_2L){if(_2K<=0){if(_2K>=0){return new F(function(){return quot(_2K,_2L);});}else{if(_2L<=0){return new F(function(){return quot(_2K,_2L);});}else{return quot(_2K+1|0,_2L)-1|0;}}}else{if(_2L>=0){if(_2K>=0){return new F(function(){return quot(_2K,_2L);});}else{if(_2L<=0){return new F(function(){return quot(_2K,_2L);});}else{return quot(_2K+1|0,_2L)-1|0;}}}else{return quot(_2K-1|0,_2L)-1|0;}}},_2M=new T(function(){return B(_2J(15,2));}),_2N=new T(function(){return 220+B(_2J(15,2))|0;}),_2O=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2P=new T(function(){return B(unCStr("base"));}),_2Q=new T(function(){return B(unCStr("PatternMatchFail"));}),_2R=new T(function(){var _2S=hs_wordToWord64(18445595),_2T=hs_wordToWord64(52003073);return [0,_2S,_2T,[0,_2S,_2T,_2P,_2O,_2Q],_F,_F];}),_2U=function(_2V){return E(_2R);},_2W=function(_2X){var _2Y=E(_2X);return new F(function(){return _N(B(_L(_2Y[1])),_2U,_2Y[2]);});},_2Z=function(_30){return E(E(_30)[1]);},_31=function(_32){return [0,_33,_32];},_34=function(_35,_36){return new F(function(){return _11(E(_35)[1],_36);});},_37=function(_38,_39){return new F(function(){return _2b(_34,_38,_39);});},_3a=function(_3b,_3c,_3d){return new F(function(){return _11(E(_3c)[1],_3d);});},_3e=[0,_3a,_2Z,_37],_33=new T(function(){return [0,_2U,_3e,_31,_2W,_2Z];}),_3f=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_3g=function(_3h){return E(E(_3h)[3]);},_3i=function(_3j,_3k){var _3l=new T(function(){return B(A(_3g,[_3k,_3j]));});return new F(function(){return die(_3l);});},_3m=function(_3n,_3o){return new F(function(){return _3i(_3n,_3o);});},_3p=function(_3q,_3r){var _3s=E(_3r);if(!_3s[0]){return [0,_F,_F];}else{var _3t=_3s[1],_3u=_3s[2];if(!B(A(_3q,[_3t]))){return [0,_F,_3s];}else{var _3v=new T(function(){var _3w=B(_3p(_3q,_3u));return [0,_3w[1],_3w[2]];}),_3x=new T(function(){return E(E(_3v)[2]);}),_3y=new T(function(){return E(E(_3v)[1]);});return [0,[1,_3t,_3y],_3x];}}},_3z=32,_3A=new T(function(){return B(unCStr("\n"));}),_3B=function(_3C){return (E(_3C)==124)?false:true;},_3D=function(_3E,_3F){var _3G=B(_3p(_3B,B(unCStr(_3E)))),_3H=_3G[1],_3I=function(_3J,_3K){var _3L=new T(function(){var _3M=new T(function(){var _3N=new T(function(){return B(_11(_3K,_3A));},1);return B(_11(_3F,_3N));});return B(unAppCStr(": ",_3M));},1);return new F(function(){return _11(_3J,_3L);});},_3O=E(_3G[2]);if(!_3O[0]){return new F(function(){return _3I(_3H,_F);});}else{if(E(_3O[1])==124){return new F(function(){return _3I(_3H,[1,_3z,_3O[2]]);});}else{return new F(function(){return _3I(_3H,_F);});}}},_3P=function(_3Q){var _3R=new T(function(){return B(_3D(_3Q,_3f));});return new F(function(){return _3m([0,_3R],_33);});},_3S=new T(function(){return B(_3P("main.hs:(92,1)-(119,116)|function checkerPosition"));}),_3T=function(_3U){var _3V=E(_3U);switch(_3V[0]){case 0:var _3W=_3V[1],_3X=_3V[2],_3Y=new T(function(){if(E(_3W)>=12){return 203+(imul(imul(imul(-1,E(_3X))|0,2)|0,6)|0)|0;}else{return 7+(imul(imul(E(_3X),2)|0,6)|0)|0;}}),_3Z=new T(function(){var _40=E(_3W);if(_40>=12){var _41=23-_40|0;if(_41>=6){return 25+(20+(imul(_41,15)|0)|0)|0;}else{return 25+(imul(_41,15)|0)|0;}}else{if(_40>=6){return 25+(20+(imul(_40,15)|0)|0)|0;}else{return 25+(imul(_40,15)|0)|0;}}});return [0,_3Z,_3Y];case 1:return E(_3S);case 2:var _42=_3V[1],_43=new T(function(){return 203-(imul(imul(E(_42),2)|0,6)|0)|0;});return [0,_2M,_43];default:var _44=_3V[1],_45=new T(function(){return 203-(imul(imul(E(_44),2)|0,6)|0)|0;});return [0,_2N,_45];}},_46=function(_47,_48){var _49=jsShowI(_47);return new F(function(){return _11(fromJSStr(_49),_48);});},_4a=41,_4b=40,_4c=function(_4d,_4e,_4f){if(_4e>=0){return new F(function(){return _46(_4e,_4f);});}else{if(_4d<=6){return new F(function(){return _46(_4e,_4f);});}else{var _4g=new T(function(){var _4h=jsShowI(_4e);return B(_11(fromJSStr(_4h),[1,_4a,_4f]));});return [1,_4b,_4g];}}},_4i=0,_4j=true,_4k=new T(function(){return B(unCStr("Black"));}),_4l=new T(function(){return B(unCStr("White"));}),_4m=new T(function(){return B(unCStr("}"));}),_4n=new T(function(){return B(unCStr(", "));}),_4o=new T(function(){return B(unCStr("onSideIndex = "));}),_4p=new T(function(){return B(unCStr("RightSidePlacement {"));}),_4q=new T(function(){return B(unCStr("LeftSidePlacement {"));}),_4r=new T(function(){return B(unCStr("onBarIndex = "));}),_4s=new T(function(){return B(unCStr("BarPlacement {"));}),_4t=new T(function(){return B(unCStr("onPointIndex = "));}),_4u=new T(function(){return B(unCStr("pointIndex = "));}),_4v=new T(function(){return B(unCStr("PointPlacement {"));}),_4w=function(_4x,_4y,_4z){var _4A=E(_4y);switch(_4A[0]){case 0:var _4B=_4A[1],_4C=_4A[2],_4D=function(_4E){var _4F=new T(function(){var _4G=new T(function(){var _4H=new T(function(){var _4I=new T(function(){var _4J=new T(function(){return B(_11(_4m,_4E));});return B(_4c(0,E(_4C),_4J));},1);return B(_11(_4t,_4I));},1);return B(_11(_4n,_4H));});return B(_4c(0,E(_4B),_4G));},1);return new F(function(){return _11(_4u,_4F);});};if(_4x<11){var _4K=new T(function(){return B(_4D(_4z));},1);return new F(function(){return _11(_4v,_4K);});}else{var _4L=new T(function(){var _4M=new T(function(){return B(_4D([1,_4a,_4z]));},1);return B(_11(_4v,_4M));});return [1,_4b,_4L];}break;case 1:var _4N=_4A[1],_4O=function(_4P){var _4Q=new T(function(){var _4R=new T(function(){var _4S=new T(function(){return B(_11(_4m,_4P));});return B(_4c(0,E(_4N),_4S));},1);return B(_11(_4r,_4R));},1);return new F(function(){return _11(_4s,_4Q);});};if(_4x<11){return new F(function(){return _4O(_4z);});}else{var _4T=new T(function(){return B(_4O([1,_4a,_4z]));});return [1,_4b,_4T];}break;case 2:var _4U=_4A[1],_4V=function(_4W){var _4X=new T(function(){var _4Y=new T(function(){var _4Z=new T(function(){return B(_11(_4m,_4W));});return B(_4c(0,E(_4U),_4Z));},1);return B(_11(_4o,_4Y));},1);return new F(function(){return _11(_4q,_4X);});};if(_4x<11){return new F(function(){return _4V(_4z);});}else{var _50=new T(function(){return B(_4V([1,_4a,_4z]));});return [1,_4b,_50];}break;default:var _51=_4A[1],_52=function(_53){var _54=new T(function(){var _55=new T(function(){var _56=new T(function(){return B(_11(_4m,_53));});return B(_4c(0,E(_51),_56));},1);return B(_11(_4o,_55));},1);return new F(function(){return _11(_4p,_54);});};if(_4x<11){return new F(function(){return _52(_4z);});}else{var _57=new T(function(){return B(_52([1,_4a,_4z]));});return [1,_4b,_57];}}},_58=95,_59=function(_5a){var _5b=E(_5a);return (E(_5b)==32)?E(_58):E(_5b);},_5c=new T(function(){return B(unCStr("draggable "));}),_5d=new T(function(){return B(unCStr("class"));}),_5e=function(_5f,_5g){var _5h=E(_5g);if(!_5h[0]){return [0];}else{var _5i=_5h[1],_5j=_5h[2],_5k=new T(function(){return B(_5e(_5f,_5j));}),_5l=new T(function(){return B(A(_5f,[_5i]));});return [1,_5l,_5k];}},_5m=function(_5n){return E(E(_5n)[1]);},_5o=function(_5p){return E(E(_5p)[2]);},_5q=function(_5r,_5s,_5t,_5u,_5v){var _5w=function(_){var _5x=jsSetAttr(B(A(_5m,[_5r,_5t])),toJSStr(E(_5u)),toJSStr(E(_5v)));return _4i;};return new F(function(){return A(_5o,[_5s,_5w]);});},_5y=function(_5z,_5A,_5B,_5C,_){var _5D=new T(function(){var _5E=new T(function(){var _5F=new T(function(){var _5G=new T(function(){return B(_5e(_59,B(_4w(0,_5C,_F))));});return B(unAppCStr(" ",_5G));});if(!E(_5A)){return B(_11(_4k,_5F));}else{return B(_11(_4l,_5F));}});if(!E(_5B)){return E(_5E);}else{return B(_11(_5c,_5E));}});return new F(function(){return A(_5q,[_4,_2I,_5z,_5d,_5D,_]);});},_5H=function(_){return _4i;},_5I=new T(function(){return (function (ns,tag) {return document.createElementNS(ns, tag);});}),_5J=function(_5K,_5L){if(_5K<=_5L){var _5M=function(_5N){var _5O=new T(function(){if(_5N!=_5L){return B(_5M(_5N+1|0));}else{return [0];}});return [1,_5N,_5O];};return new F(function(){return _5M(_5K);});}else{return [0];}},_5P=new T(function(){return B(_5J(0,2147483647));}),_5Q=new T(function(){return B(unCStr("cy"));}),_5R=new T(function(){return B(unCStr("cx"));}),_5S=new T(function(){return B(_4c(0,6,_F));}),_5T=new T(function(){return B(unCStr("r"));}),_5U=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:156:5-10"));}),_5V=[0,_2z,_2A,_F,_5U,_2z,_2z],_5W=new T(function(){return B(_2x(_5V));}),_5X=new T(function(){return B(unCStr("circle"));}),_5Y=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_5Z=new T(function(){return B(unCStr("board"));}),_60=function(_61,_62,_){if(0>=_62){return _4i;}else{var _63=function(_64,_65,_){var _66=jsFind(toJSStr(E(_5Z)));if(!_66[0]){return new F(function(){return die(_5W);});}else{var _67=E(_5I)(toJSStr(_5Y),toJSStr(_5X)),_68=B(A(_5q,[_4,_2I,_67,_5T,_5S,_])),_69=new T(function(){if(!E(_61)){return [3,_64];}else{return [2,_64];}}),_6a=new T(function(){var _6b=B(_3T(_69));return [0,_6b[1],_6b[2]];}),_6c=new T(function(){return B(_4c(0,E(E(_6a)[1]),_F));}),_6d=B(A(_5q,[_4,_2I,_67,_5R,_6c,_])),_6e=new T(function(){return B(_4c(0,E(E(_6a)[2]),_F));}),_6f=B(A(_5q,[_4,_2I,_67,_5Q,_6e,_])),_6g=B(_5y(_67,_61,_4j,_69,_)),_6h=jsAppendChild(_67,E(_66[1]));return new F(function(){return A(_65,[_]);});}},_6i=function(_6j,_6k,_){var _6l=E(_6j);if(!_6l[0]){return _4i;}else{var _6m=_6l[1],_6n=_6l[2],_6o=E(_6k);if(_6o==1){return new F(function(){return _63(_6m,_5H,_);});}else{var _6p=function(_){return new F(function(){return _6i(_6n,_6o-1|0,_);});};return new F(function(){return _63(_6m,_6p,_);});}}};return new F(function(){return _6i(_5P,_62,_);});}},_6q=0,_6r=1,_6s=function(_6t,_6u){while(1){var _6v=E(_6t);if(!_6v[0]){return E(_6u);}else{_6t=_6v[2];var _6w=[1,_6v[1],_6u];_6u=_6w;continue;}}},_6x=2,_6y=0,_6z=[1,_6y,_F],_6A=[1,_6y,_6z],_6B=[1,_6y,_6A],_6C=[1,_6y,_6B],_6D=[1,_6y,_6C],_6E=5,_6F=[1,_6E,_6D],_6G=[1,_6y,_6F],_6H=3,_6I=[1,_6H,_6G],_6J=[1,_6y,_6I],_6K=[1,_6y,_6J],_6L=[1,_6y,_6K],_6M=[1,_6y,_6L],_6N=[1,_6E,_6M],_6O=[1,_6y,_6N],_6P=[1,_6y,_6O],_6Q=[1,_6y,_6P],_6R=[1,_6y,_6Q],_6S=[1,_6y,_6R],_6T=[1,_6y,_6S],_6U=[1,_6y,_6T],_6V=[1,_6y,_6U],_6W=[1,_6y,_6V],_6X=[1,_6y,_6W],_6Y=function(_6Z){var _70=E(_6Z);if(!_70[0]){return [0];}else{var _71=_70[2],_72=new T(function(){return B(_6Y(_71));});return [1,[0,_6r,_70[1]],_72];}},_73=function(_74,_75){var _76=new T(function(){return B(_6Y(_75));});return [1,[0,_6r,_74],_76];},_77=new T(function(){return B(_73(_6x,_6X));}),_78=new T(function(){return B(_6s(_77,_F));}),_79=function(_7a){var _7b=E(_7a);return (E(_7b[1])==0)?E(_7b):[0,_6q,_7b[2]];},_7c=new T(function(){return B(_5e(_79,_78));}),_7d=function(_7e,_7f){var _7g=E(_7e);if(!E(_7g[1])){return new F(function(){return _3P("main.hs:(257,20)-(258,55)|function whiteOrBlack");});}else{return (E(_7g[2])==0)?E(_7f):E(_7g);}},_7h=function(_7i,_7j,_7k){var _7l=E(_7j);if(!_7l[0]){return [0];}else{var _7m=_7l[1],_7n=_7l[2],_7o=E(_7k);if(!_7o[0]){return [0];}else{var _7p=_7o[1],_7q=_7o[2],_7r=new T(function(){return B(_7h(_7i,_7n,_7q));}),_7s=new T(function(){return B(A(_7i,[_7m,_7p]));});return [1,_7s,_7r];}}},_7t=new T(function(){return B(_7h(_7d,_77,_7c));}),_7u=function(_7v,_7w){while(1){var _7x=E(_7v);if(!_7x[0]){return E(_7w);}else{_7v=_7x[2];var _7y=_7w+E(_7x[1])|0;_7w=_7y;continue;}}},_7z=function(_7A,_7B,_7C){return new F(function(){return _7u(_7B,_7C+_7A|0);});},_7D=new T(function(){return B(_7z(2,_6X,0));}),_7E=[0,_7t,_7D,_7D,_6y,_6y,_6r,_6r],_7F="deltaZ",_7G="deltaY",_7H="deltaX",_7I=new T(function(){return B(unCStr(")"));}),_7J=new T(function(){return B(_4c(0,2,_7I));}),_7K=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_7J));}),_7L=function(_7M){var _7N=new T(function(){return B(_4c(0,_7M,_7K));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_7N)));});},_7O=function(_7P,_){return new T(function(){var _7Q=Number(E(_7P)),_7R=jsTrunc(_7Q);if(_7R<0){return B(_7L(_7R));}else{if(_7R>2){return B(_7L(_7R));}else{return _7R;}}});},_7S=0,_7T=[0,_7S,_7S,_7S],_7U="button",_7V=new T(function(){return jsGetMouseCoords;}),_7W=function(_7X,_){var _7Y=E(_7X);if(!_7Y[0]){return _F;}else{var _7Z=_7Y[1],_80=B(_7W(_7Y[2],_)),_81=new T(function(){var _82=Number(E(_7Z));return jsTrunc(_82);});return [1,_81,_80];}},_83=function(_84,_){var _85=__arr2lst(0,_84);return new F(function(){return _7W(_85,_);});},_86=function(_87,_){return new F(function(){return _83(E(_87),_);});},_88=function(_89,_){return new T(function(){var _8a=Number(E(_89));return jsTrunc(_8a);});},_8b=[0,_88,_86],_8c=function(_8d,_){var _8e=E(_8d);if(!_8e[0]){return _F;}else{var _8f=B(_8c(_8e[2],_));return [1,_8e[1],_8f];}},_8g=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_8h=[0,_2z,_2A,_F,_8g,_2z,_2z],_8i=new T(function(){return B(_2x(_8h));}),_8j=function(_){return new F(function(){return die(_8i);});},_8k=function(_8l){return E(E(_8l)[1]);},_8m=function(_8n,_8o,_8p,_){var _8q=__arr2lst(0,_8p),_8r=B(_8c(_8q,_)),_8s=E(_8r);if(!_8s[0]){return new F(function(){return _8j(_);});}else{var _8t=E(_8s[2]);if(!_8t[0]){return new F(function(){return _8j(_);});}else{if(!E(_8t[2])[0]){var _8u=B(A(_8k,[_8n,_8s[1],_])),_8v=B(A(_8k,[_8o,_8t[1],_]));return [0,_8u,_8v];}else{return new F(function(){return _8j(_);});}}}},_8w=function(_){return new F(function(){return __jsNull();});},_8x=function(_8y){var _8z=B(A(_8y,[_]));return E(_8z);},_8A=new T(function(){return B(_8x(_8w));}),_8B=new T(function(){return E(_8A);}),_8C=function(_8D,_8E,_){if(E(_8D)==7){var _8F=E(_7V)(_8E),_8G=B(_8m(_8b,_8b,_8F,_)),_8H=_8G,_8I=_8E[E(_7H)],_8J=_8I,_8K=_8E[E(_7G)],_8L=_8K,_8M=_8E[E(_7F)],_8N=_8M;return new T(function(){return [0,E(_8H),E(_2z),[0,_8J,_8L,_8N]];});}else{var _8O=E(_7V)(_8E),_8P=B(_8m(_8b,_8b,_8O,_)),_8Q=_8P,_8R=_8E[E(_7U)],_8S=__eq(_8R,E(_8B));if(!E(_8S)){var _8T=B(_7O(_8R,_)),_8U=_8T;return new T(function(){return [0,E(_8Q),[1,_8U],E(_7T)];});}else{return new T(function(){return [0,E(_8Q),E(_2z),E(_7T)];});}}},_8V=function(_8W,_8X,_){return new F(function(){return _8C(_8W,E(_8X),_);});},_8Y="mouseout",_8Z="mouseover",_90="mousemove",_91="mouseup",_92="mousedown",_93="dblclick",_94="click",_95="wheel",_96=function(_97){switch(E(_97)){case 0:return E(_94);case 1:return E(_93);case 2:return E(_92);case 3:return E(_91);case 4:return E(_90);case 5:return E(_8Z);case 6:return E(_8Y);default:return E(_95);}},_98=[0,_96,_8V],_99=function(_){return _4i;},_9a=[0,_2I,_r],_9b=new T(function(){return B(unCStr("!!: negative index"));}),_9c=new T(function(){return B(unCStr("Prelude."));}),_9d=new T(function(){return B(_11(_9c,_9b));}),_9e=new T(function(){return B(err(_9d));}),_9f=new T(function(){return B(unCStr("!!: index too large"));}),_9g=new T(function(){return B(_11(_9c,_9f));}),_9h=new T(function(){return B(err(_9g));}),_9i=function(_9j,_9k){while(1){var _9l=E(_9j);if(!_9l[0]){return E(_9h);}else{var _9m=E(_9k);if(!_9m){return E(_9l[1]);}else{_9j=_9l[2];_9k=_9m-1|0;continue;}}}},_9n=function(_9o,_9p){if(_9p>=0){return new F(function(){return _9i(_9o,_9p);});}else{return E(_9e);}},_9q=0,_9r=new T(function(){return (function (msg) { alert(msg); });}),_9s="value",_9t=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:239:9-19"));}),_9u=[0,_2z,_2A,_F,_9t,_2z,_2z],_9v=new T(function(){return B(_2x(_9u));}),_9w=function(_){var _9x=jsFind("sharedKey");if(!_9x[0]){return new F(function(){return die(_9v);});}else{var _9y=jsGet(E(_9x[1]),E(_9s)),_9z=E(_9r)(toJSStr(fromJSStr(_9y)));return new F(function(){return _99(_);});}},_9A=function(_9B,_){return new F(function(){return _9w(_);});},_9C=new T(function(){return B(unCStr(": empty list"));}),_9D=function(_9E){var _9F=new T(function(){return B(_11(_9E,_9C));},1);return new F(function(){return err(B(_11(_9c,_9F)));});},_9G=new T(function(){return B(unCStr("head"));}),_9H=new T(function(){return B(_9D(_9G));}),_9I=new T(function(){return (function (elem, cx, cy, duration) {$(elem).velocity({ cx: cx, cy: cy }, { duration: duration });});}),_9J=function(_9K,_9L,_9M,_){var _9N=jsElemsByClassName(toJSStr(B(_5e(_59,B(_4w(0,_9K,_F))))));if(!_9N[0]){return E(_9H);}else{var _9O=E(_9N[1]),_9P=B(_3T(_9L)),_9Q=E(_9I)(_9O,E(_9P[1]),E(_9P[2]),300);return new F(function(){return _5y(_9O,_9M,_4j,_9L,_);});}},_9R=new T(function(){return (function (cb) {setDropCheckerCallback_ffi(cb);});}),_9S=function(_9T,_9U){var _9V=function(_9W,_9X){while(1){var _9Y=(function(_9Z,_a0){var _a1=E(_9Z);if(!_a1[0]){return [0];}else{var _a2=_a1[2];if(!B(A(_9T,[_a1[1]]))){_9W=_a2;var _a3=_a0+1|0;_9X=_a3;return null;}else{var _a4=new T(function(){return B(_9V(_a2,_a0+1|0));});return [1,_a0,_a4];}}})(_9W,_9X);if(_9Y!=null){return _9Y;}}},_a5=B(_9V(_9U,0));return (_a5[0]==0)?[0]:[1,_a5[1]];},_a6=new T(function(){return B(_2J(210,2));}),_a7=function(_a8){var _a9=E(_a8);return (E(_a9)==95)?32:E(_a9);},_aa=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_ab=new T(function(){return B(err(_aa));}),_ac=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_ad=new T(function(){return B(err(_ac));}),_ae=new T(function(){return B(_3P("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_af=function(_ag,_ah){while(1){var _ai=(function(_aj,_ak){var _al=E(_aj);switch(_al[0]){case 0:var _am=E(_ak);if(!_am[0]){return [0];}else{_ag=B(A(_al[1],[_am[1]]));_ah=_am[2];return null;}break;case 1:var _an=B(A(_al[1],[_ak])),_ao=_ak;_ag=_an;_ah=_ao;return null;case 2:return [0];case 3:var _ap=_al[2],_aq=new T(function(){return B(_af(_ap,_ak));});return [1,[0,_al[1],_ak],_aq];default:return E(_al[1]);}})(_ag,_ah);if(_ai!=null){return _ai;}}},_ar=function(_as,_at){var _au=function(_av){var _aw=E(_at);if(_aw[0]==3){var _ax=_aw[2],_ay=new T(function(){return B(_ar(_as,_ax));});return [3,_aw[1],_ay];}else{var _az=E(_as);if(_az[0]==2){return E(_aw);}else{var _aA=E(_aw);if(_aA[0]==2){return E(_az);}else{var _aB=function(_aC){var _aD=E(_aA);if(_aD[0]==4){var _aE=_aD[1];return [1,function(_aF){return [4,new T(function(){return B(_11(B(_af(_az,_aF)),_aE));})];}];}else{var _aG=E(_az);if(_aG[0]==1){var _aH=_aG[1],_aI=E(_aD);if(!_aI[0]){return [1,function(_aJ){return new F(function(){return _ar(B(A(_aH,[_aJ])),_aI);});}];}else{var _aK=_aI[1];return [1,function(_aL){var _aM=new T(function(){return B(A(_aK,[_aL]));});return new F(function(){return _ar(B(A(_aH,[_aL])),_aM);});}];}}else{var _aN=E(_aD);if(!_aN[0]){return E(_ae);}else{var _aO=_aN[1];return [1,function(_aP){var _aQ=new T(function(){return B(A(_aO,[_aP]));});return new F(function(){return _ar(_aG,_aQ);});}];}}}},_aR=E(_az);switch(_aR[0]){case 1:var _aS=_aR[1],_aT=E(_aA);if(_aT[0]==4){var _aU=_aT[1];return [1,function(_aV){return [4,new T(function(){return B(_11(B(_af(B(A(_aS,[_aV])),_aV)),_aU));})];}];}else{return new F(function(){return _aB(_);});}break;case 4:var _aW=_aR[1],_aX=E(_aA);switch(_aX[0]){case 0:return [1,function(_aY){return [4,new T(function(){var _aZ=new T(function(){return B(_af(_aX,_aY));},1);return B(_11(_aW,_aZ));})];}];case 1:var _b0=_aX[1];return [1,function(_b1){return [4,new T(function(){var _b2=new T(function(){return B(_af(B(A(_b0,[_b1])),_b1));},1);return B(_11(_aW,_b2));})];}];default:var _b3=_aX[1];return [4,new T(function(){return B(_11(_aW,_b3));})];}break;default:return new F(function(){return _aB(_);});}}}}},_b4=E(_as);switch(_b4[0]){case 0:var _b5=_b4[1],_b6=E(_at);if(!_b6[0]){var _b7=_b6[1];return [0,function(_b8){var _b9=new T(function(){return B(A(_b7,[_b8]));});return new F(function(){return _ar(B(A(_b5,[_b8])),_b9);});}];}else{return new F(function(){return _au(_);});}break;case 3:var _ba=_b4[2],_bb=new T(function(){return B(_ar(_ba,_at));});return [3,_b4[1],_bb];default:return new F(function(){return _au(_);});}},_bc=new T(function(){return B(unCStr("("));}),_bd=new T(function(){return B(unCStr(")"));}),_be=function(_bf,_bg){while(1){var _bh=E(_bf);if(!_bh[0]){return (E(_bg)[0]==0)?true:false;}else{var _bi=E(_bg);if(!_bi[0]){return false;}else{if(E(_bh[1])!=E(_bi[1])){return false;}else{_bf=_bh[2];_bg=_bi[2];continue;}}}}},_bj=function(_bk,_bl){return E(_bk)!=E(_bl);},_bm=function(_bn,_bo){return E(_bn)==E(_bo);},_bp=[0,_bm,_bj],_bq=function(_br,_bs){while(1){var _bt=E(_br);if(!_bt[0]){return (E(_bs)[0]==0)?true:false;}else{var _bu=E(_bs);if(!_bu[0]){return false;}else{if(E(_bt[1])!=E(_bu[1])){return false;}else{_br=_bt[2];_bs=_bu[2];continue;}}}}},_bv=function(_bw,_bx){return (!B(_bq(_bw,_bx)))?true:false;},_by=[0,_bq,_bv],_bz=function(_bA,_bB){var _bC=E(_bA);switch(_bC[0]){case 0:var _bD=_bC[1];return [0,function(_bE){return new F(function(){return _bz(B(A(_bD,[_bE])),_bB);});}];case 1:var _bF=_bC[1];return [1,function(_bG){return new F(function(){return _bz(B(A(_bF,[_bG])),_bB);});}];case 2:return [2];case 3:var _bH=_bC[2],_bI=new T(function(){return B(_bz(_bH,_bB));});return new F(function(){return _ar(B(A(_bB,[_bC[1]])),_bI);});break;default:var _bJ=function(_bK){var _bL=E(_bK);if(!_bL[0]){return [0];}else{var _bM=_bL[2],_bN=E(_bL[1]),_bO=new T(function(){return B(_bJ(_bM));},1);return new F(function(){return _11(B(_af(B(A(_bB,[_bN[1]])),_bN[2])),_bO);});}},_bP=B(_bJ(_bC[1]));return (_bP[0]==0)?[2]:[4,_bP];}},_bQ=[2],_bR=function(_bS){return [3,_bS,_bQ];},_bT=function(_bU,_bV){var _bW=E(_bU);if(!_bW){return new F(function(){return A(_bV,[_4i]);});}else{var _bX=new T(function(){return B(_bT(_bW-1|0,_bV));});return [0,function(_bY){return E(_bX);}];}},_bZ=function(_c0,_c1,_c2){var _c3=new T(function(){return B(A(_c0,[_bR]));}),_c4=function(_c5,_c6,_c7,_c8){while(1){var _c9=(function(_ca,_cb,_cc,_cd){var _ce=E(_ca);switch(_ce[0]){case 0:var _cf=E(_cb);if(!_cf[0]){return new F(function(){return A(_c1,[_cd]);});}else{_c5=B(A(_ce[1],[_cf[1]]));_c6=_cf[2];var _cg=_cc+1|0,_ch=_cd;_c7=_cg;_c8=_ch;return null;}break;case 1:var _ci=B(A(_ce[1],[_cb])),_cj=_cb,_cg=_cc,_ch=_cd;_c5=_ci;_c6=_cj;_c7=_cg;_c8=_ch;return null;case 2:return new F(function(){return A(_c1,[_cd]);});break;case 3:var _ck=new T(function(){return B(_bz(_ce,_cd));}),_cl=function(_cm){return E(_ck);};return new F(function(){return _bT(_cc,_cl);});break;default:return new F(function(){return _bz(_ce,_cd);});}})(_c5,_c6,_c7,_c8);if(_c9!=null){return _c9;}}};return function(_cn){return new F(function(){return _c4(_c3,_cn,0,_c2);});};},_co=function(_cp){return new F(function(){return A(_cp,[_F]);});},_cq=function(_cr,_cs){var _ct=function(_cu){var _cv=E(_cu);if(!_cv[0]){return E(_co);}else{var _cw=_cv[1],_cx=_cv[2];if(!B(A(_cr,[_cw]))){return E(_co);}else{var _cy=new T(function(){return B(_ct(_cx));}),_cz=function(_cA){var _cB=new T(function(){var _cC=function(_cD){return new F(function(){return A(_cA,[[1,_cw,_cD]]);});};return B(A(_cy,[_cC]));});return [0,function(_cE){return E(_cB);}];};return E(_cz);}}};return function(_cF){return new F(function(){return A(_ct,[_cF,_cs]);});};},_cG=[6],_cH=new T(function(){return B(unCStr("valDig: Bad base"));}),_cI=new T(function(){return B(err(_cH));}),_cJ=function(_cK,_cL){var _cM=function(_cN,_cO){var _cP=E(_cN);if(!_cP[0]){var _cQ=new T(function(){return B(A(_cO,[_F]));}),_cR=function(_cS){return new F(function(){return A(_cS,[_cQ]);});};return E(_cR);}else{var _cT=_cP[2],_cU=E(_cP[1]),_cV=function(_cW){var _cX=new T(function(){var _cY=function(_cZ){return new F(function(){return A(_cO,[[1,_cW,_cZ]]);});};return B(_cM(_cT,_cY));}),_d0=function(_d1){var _d2=new T(function(){return B(A(_cX,[_d1]));});return [0,function(_d3){return E(_d2);}];};return E(_d0);};switch(E(_cK)){case 8:if(48>_cU){var _d4=new T(function(){return B(A(_cO,[_F]));}),_d5=function(_d6){return new F(function(){return A(_d6,[_d4]);});};return E(_d5);}else{if(_cU>55){var _d7=new T(function(){return B(A(_cO,[_F]));}),_d8=function(_d9){return new F(function(){return A(_d9,[_d7]);});};return E(_d8);}else{return new F(function(){return _cV(_cU-48|0);});}}break;case 10:if(48>_cU){var _da=new T(function(){return B(A(_cO,[_F]));}),_db=function(_dc){return new F(function(){return A(_dc,[_da]);});};return E(_db);}else{if(_cU>57){var _dd=new T(function(){return B(A(_cO,[_F]));}),_de=function(_df){return new F(function(){return A(_df,[_dd]);});};return E(_de);}else{return new F(function(){return _cV(_cU-48|0);});}}break;case 16:if(48>_cU){if(97>_cU){if(65>_cU){var _dg=new T(function(){return B(A(_cO,[_F]));}),_dh=function(_di){return new F(function(){return A(_di,[_dg]);});};return E(_dh);}else{if(_cU>70){var _dj=new T(function(){return B(A(_cO,[_F]));}),_dk=function(_dl){return new F(function(){return A(_dl,[_dj]);});};return E(_dk);}else{return new F(function(){return _cV((_cU-65|0)+10|0);});}}}else{if(_cU>102){if(65>_cU){var _dm=new T(function(){return B(A(_cO,[_F]));}),_dn=function(_do){return new F(function(){return A(_do,[_dm]);});};return E(_dn);}else{if(_cU>70){var _dp=new T(function(){return B(A(_cO,[_F]));}),_dq=function(_dr){return new F(function(){return A(_dr,[_dp]);});};return E(_dq);}else{return new F(function(){return _cV((_cU-65|0)+10|0);});}}}else{return new F(function(){return _cV((_cU-97|0)+10|0);});}}}else{if(_cU>57){if(97>_cU){if(65>_cU){var _ds=new T(function(){return B(A(_cO,[_F]));}),_dt=function(_du){return new F(function(){return A(_du,[_ds]);});};return E(_dt);}else{if(_cU>70){var _dv=new T(function(){return B(A(_cO,[_F]));}),_dw=function(_dx){return new F(function(){return A(_dx,[_dv]);});};return E(_dw);}else{return new F(function(){return _cV((_cU-65|0)+10|0);});}}}else{if(_cU>102){if(65>_cU){var _dy=new T(function(){return B(A(_cO,[_F]));}),_dz=function(_dA){return new F(function(){return A(_dA,[_dy]);});};return E(_dz);}else{if(_cU>70){var _dB=new T(function(){return B(A(_cO,[_F]));}),_dC=function(_dD){return new F(function(){return A(_dD,[_dB]);});};return E(_dC);}else{return new F(function(){return _cV((_cU-65|0)+10|0);});}}}else{return new F(function(){return _cV((_cU-97|0)+10|0);});}}}else{return new F(function(){return _cV(_cU-48|0);});}}break;default:return E(_cI);}}},_dE=function(_dF){var _dG=E(_dF);if(!_dG[0]){return [2];}else{return new F(function(){return A(_cL,[_dG]);});}};return function(_dH){return new F(function(){return A(_cM,[_dH,_2,_dE]);});};},_dI=16,_dJ=8,_dK=function(_dL){var _dM=function(_dN){return new F(function(){return A(_dL,[[5,[0,_dJ,_dN]]]);});},_dO=function(_dP){return new F(function(){return A(_dL,[[5,[0,_dI,_dP]]]);});},_dQ=function(_dR){switch(E(_dR)){case 79:return [1,B(_cJ(_dJ,_dM))];case 88:return [1,B(_cJ(_dI,_dO))];case 111:return [1,B(_cJ(_dJ,_dM))];case 120:return [1,B(_cJ(_dI,_dO))];default:return [2];}},_dS=[0,_dQ];return function(_dT){return (E(_dT)==48)?E(_dS):[2];};},_dU=function(_dV){return [0,B(_dK(_dV))];},_dW=function(_dX){return new F(function(){return A(_dX,[_2z]);});},_dY=function(_dZ){return new F(function(){return A(_dZ,[_2z]);});},_e0=10,_e1=[0,1],_e2=[0,2147483647],_e3=function(_e4,_e5){while(1){var _e6=E(_e4);if(!_e6[0]){var _e7=_e6[1],_e8=E(_e5);if(!_e8[0]){var _e9=_e8[1],_ea=addC(_e7,_e9);if(!E(_ea[2])){return [0,_ea[1]];}else{_e4=[1,I_fromInt(_e7)];_e5=[1,I_fromInt(_e9)];continue;}}else{_e4=[1,I_fromInt(_e7)];_e5=_e8;continue;}}else{var _eb=E(_e5);if(!_eb[0]){_e4=_e6;_e5=[1,I_fromInt(_eb[1])];continue;}else{return [1,I_add(_e6[1],_eb[1])];}}}},_ec=new T(function(){return B(_e3(_e2,_e1));}),_ed=function(_ee){var _ef=E(_ee);if(!_ef[0]){var _eg=E(_ef[1]);return (_eg==(-2147483648))?E(_ec):[0, -_eg];}else{return [1,I_negate(_ef[1])];}},_eh=[0,10],_ei=function(_ej,_ek){while(1){var _el=E(_ej);if(!_el[0]){return E(_ek);}else{_ej=_el[2];var _em=_ek+1|0;_ek=_em;continue;}}},_en=function(_eo){return [0,_eo];},_ep=function(_eq){return new F(function(){return _en(E(_eq));});},_er=new T(function(){return B(unCStr("this should not happen"));}),_es=new T(function(){return B(err(_er));}),_et=function(_eu,_ev){while(1){var _ew=E(_eu);if(!_ew[0]){var _ex=_ew[1],_ey=E(_ev);if(!_ey[0]){var _ez=_ey[1];if(!(imul(_ex,_ez)|0)){return [0,imul(_ex,_ez)|0];}else{_eu=[1,I_fromInt(_ex)];_ev=[1,I_fromInt(_ez)];continue;}}else{_eu=[1,I_fromInt(_ex)];_ev=_ey;continue;}}else{var _eA=E(_ev);if(!_eA[0]){_eu=_ew;_ev=[1,I_fromInt(_eA[1])];continue;}else{return [1,I_mul(_ew[1],_eA[1])];}}}},_eB=function(_eC,_eD){var _eE=E(_eD);if(!_eE[0]){return [0];}else{var _eF=E(_eE[2]);if(!_eF[0]){return E(_es);}else{var _eG=_eF[2],_eH=new T(function(){return B(_eB(_eC,_eG));});return [1,B(_e3(B(_et(_eE[1],_eC)),_eF[1])),_eH];}}},_eI=[0,0],_eJ=function(_eK,_eL,_eM){while(1){var _eN=(function(_eO,_eP,_eQ){var _eR=E(_eQ);if(!_eR[0]){return E(_eI);}else{if(!E(_eR[2])[0]){return E(_eR[1]);}else{var _eS=E(_eP);if(_eS<=40){var _eT=_eI,_eU=_eR;while(1){var _eV=E(_eU);if(!_eV[0]){return E(_eT);}else{var _eW=B(_e3(B(_et(_eT,_eO)),_eV[1]));_eU=_eV[2];_eT=_eW;continue;}}}else{var _eX=B(_et(_eO,_eO));if(!(_eS%2)){_eK=_eX;_eL=quot(_eS+1|0,2);var _eY=B(_eB(_eO,_eR));_eM=_eY;return null;}else{_eK=_eX;_eL=quot(_eS+1|0,2);var _eY=B(_eB(_eO,[1,_eI,_eR]));_eM=_eY;return null;}}}}})(_eK,_eL,_eM);if(_eN!=null){return _eN;}}},_eZ=function(_f0,_f1){var _f2=new T(function(){return B(_ei(_f1,0));},1);return new F(function(){return _eJ(_f0,_f2,B(_5e(_ep,_f1)));});},_f3=function(_f4){var _f5=new T(function(){var _f6=new T(function(){var _f7=function(_f8){var _f9=new T(function(){return B(_eZ(_eh,_f8));});return new F(function(){return A(_f4,[[1,_f9]]);});};return [1,B(_cJ(_e0,_f7))];}),_fa=function(_fb){if(E(_fb)==43){var _fc=function(_fd){var _fe=new T(function(){return B(_eZ(_eh,_fd));});return new F(function(){return A(_f4,[[1,_fe]]);});};return [1,B(_cJ(_e0,_fc))];}else{return [2];}},_ff=function(_fg){if(E(_fg)==45){var _fh=function(_fi){var _fj=new T(function(){return B(_ed(B(_eZ(_eh,_fi))));});return new F(function(){return A(_f4,[[1,_fj]]);});};return [1,B(_cJ(_e0,_fh))];}else{return [2];}};return B(_ar(B(_ar([0,_ff],[0,_fa])),_f6));}),_fk=function(_fl){return (E(_fl)==69)?E(_f5):[2];},_fm=function(_fn){return (E(_fn)==101)?E(_f5):[2];};return new F(function(){return _ar([0,_fm],[0,_fk]);});},_fo=function(_fp){var _fq=function(_fr){return new F(function(){return A(_fp,[[1,_fr]]);});};return function(_fs){return (E(_fs)==46)?[1,B(_cJ(_e0,_fq))]:[2];};},_ft=function(_fu){return [0,B(_fo(_fu))];},_fv=function(_fw){var _fx=function(_fy){var _fz=function(_fA){var _fB=function(_fC){return new F(function(){return A(_fw,[[5,[1,_fy,_fA,_fC]]]);});};return [1,B(_bZ(_f3,_dW,_fB))];};return [1,B(_bZ(_ft,_dY,_fz))];};return new F(function(){return _cJ(_e0,_fx);});},_fD=function(_fE){return [1,B(_fv(_fE))];},_fF=function(_fG){return E(E(_fG)[1]);},_fH=function(_fI,_fJ,_fK){while(1){var _fL=E(_fK);if(!_fL[0]){return false;}else{if(!B(A(_fF,[_fI,_fJ,_fL[1]]))){_fK=_fL[2];continue;}else{return true;}}}},_fM=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_fN=function(_fO){return new F(function(){return _fH(_bp,_fO,_fM);});},_fP=false,_fQ=function(_fR){var _fS=new T(function(){return B(A(_fR,[_dJ]));}),_fT=new T(function(){return B(A(_fR,[_dI]));});return function(_fU){switch(E(_fU)){case 79:return E(_fS);case 88:return E(_fT);case 111:return E(_fS);case 120:return E(_fT);default:return [2];}};},_fV=function(_fW){return [0,B(_fQ(_fW))];},_fX=function(_fY){return new F(function(){return A(_fY,[_e0]);});},_fZ=function(_g0){var _g1=new T(function(){return B(_4c(9,_g0,_F));});return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",_g1)));});},_g2=function(_g3){var _g4=E(_g3);if(!_g4[0]){return E(_g4[1]);}else{return new F(function(){return I_toInt(_g4[1]);});}},_g5=function(_g6,_g7){var _g8=E(_g6);if(!_g8[0]){var _g9=_g8[1],_ga=E(_g7);return (_ga[0]==0)?_g9<=_ga[1]:I_compareInt(_ga[1],_g9)>=0;}else{var _gb=_g8[1],_gc=E(_g7);return (_gc[0]==0)?I_compareInt(_gb,_gc[1])<=0:I_compare(_gb,_gc[1])<=0;}},_gd=function(_ge){return [2];},_gf=function(_gg){var _gh=E(_gg);if(!_gh[0]){return E(_gd);}else{var _gi=_gh[1],_gj=E(_gh[2]);if(!_gj[0]){return E(_gi);}else{var _gk=new T(function(){return B(_gf(_gj));}),_gl=function(_gm){var _gn=new T(function(){return B(A(_gk,[_gm]));});return new F(function(){return _ar(B(A(_gi,[_gm])),_gn);});};return E(_gl);}}},_go=function(_gp,_gq){var _gr=function(_gs,_gt,_gu){var _gv=E(_gs);if(!_gv[0]){return new F(function(){return A(_gu,[_gp]);});}else{var _gw=_gv[2],_gx=E(_gt);if(!_gx[0]){return [2];}else{var _gy=_gx[2];if(E(_gv[1])!=E(_gx[1])){return [2];}else{var _gz=new T(function(){return B(_gr(_gw,_gy,_gu));});return [0,function(_gA){return E(_gz);}];}}}};return function(_gB){return new F(function(){return _gr(_gp,_gB,_gq);});};},_gC=new T(function(){return B(unCStr("SO"));}),_gD=14,_gE=function(_gF){var _gG=new T(function(){return B(A(_gF,[_gD]));}),_gH=function(_gI){return E(_gG);};return [1,B(_go(_gC,_gH))];},_gJ=new T(function(){return B(unCStr("SOH"));}),_gK=1,_gL=function(_gM){var _gN=new T(function(){return B(A(_gM,[_gK]));}),_gO=function(_gP){return E(_gN);};return [1,B(_go(_gJ,_gO))];},_gQ=function(_gR){return [1,B(_bZ(_gL,_gE,_gR))];},_gS=new T(function(){return B(unCStr("NUL"));}),_gT=0,_gU=function(_gV){var _gW=new T(function(){return B(A(_gV,[_gT]));}),_gX=function(_gY){return E(_gW);};return [1,B(_go(_gS,_gX))];},_gZ=new T(function(){return B(unCStr("STX"));}),_h0=2,_h1=function(_h2){var _h3=new T(function(){return B(A(_h2,[_h0]));}),_h4=function(_h5){return E(_h3);};return [1,B(_go(_gZ,_h4))];},_h6=new T(function(){return B(unCStr("ETX"));}),_h7=3,_h8=function(_h9){var _ha=new T(function(){return B(A(_h9,[_h7]));}),_hb=function(_hc){return E(_ha);};return [1,B(_go(_h6,_hb))];},_hd=new T(function(){return B(unCStr("EOT"));}),_he=4,_hf=function(_hg){var _hh=new T(function(){return B(A(_hg,[_he]));}),_hi=function(_hj){return E(_hh);};return [1,B(_go(_hd,_hi))];},_hk=new T(function(){return B(unCStr("ENQ"));}),_hl=5,_hm=function(_hn){var _ho=new T(function(){return B(A(_hn,[_hl]));}),_hp=function(_hq){return E(_ho);};return [1,B(_go(_hk,_hp))];},_hr=new T(function(){return B(unCStr("ACK"));}),_hs=6,_ht=function(_hu){var _hv=new T(function(){return B(A(_hu,[_hs]));}),_hw=function(_hx){return E(_hv);};return [1,B(_go(_hr,_hw))];},_hy=new T(function(){return B(unCStr("BEL"));}),_hz=7,_hA=function(_hB){var _hC=new T(function(){return B(A(_hB,[_hz]));}),_hD=function(_hE){return E(_hC);};return [1,B(_go(_hy,_hD))];},_hF=new T(function(){return B(unCStr("BS"));}),_hG=8,_hH=function(_hI){var _hJ=new T(function(){return B(A(_hI,[_hG]));}),_hK=function(_hL){return E(_hJ);};return [1,B(_go(_hF,_hK))];},_hM=new T(function(){return B(unCStr("HT"));}),_hN=9,_hO=function(_hP){var _hQ=new T(function(){return B(A(_hP,[_hN]));}),_hR=function(_hS){return E(_hQ);};return [1,B(_go(_hM,_hR))];},_hT=new T(function(){return B(unCStr("LF"));}),_hU=10,_hV=function(_hW){var _hX=new T(function(){return B(A(_hW,[_hU]));}),_hY=function(_hZ){return E(_hX);};return [1,B(_go(_hT,_hY))];},_i0=new T(function(){return B(unCStr("VT"));}),_i1=11,_i2=function(_i3){var _i4=new T(function(){return B(A(_i3,[_i1]));}),_i5=function(_i6){return E(_i4);};return [1,B(_go(_i0,_i5))];},_i7=new T(function(){return B(unCStr("FF"));}),_i8=12,_i9=function(_ia){var _ib=new T(function(){return B(A(_ia,[_i8]));}),_ic=function(_id){return E(_ib);};return [1,B(_go(_i7,_ic))];},_ie=new T(function(){return B(unCStr("CR"));}),_if=13,_ig=function(_ih){var _ii=new T(function(){return B(A(_ih,[_if]));}),_ij=function(_ik){return E(_ii);};return [1,B(_go(_ie,_ij))];},_il=new T(function(){return B(unCStr("SI"));}),_im=15,_in=function(_io){var _ip=new T(function(){return B(A(_io,[_im]));}),_iq=function(_ir){return E(_ip);};return [1,B(_go(_il,_iq))];},_is=new T(function(){return B(unCStr("DLE"));}),_it=16,_iu=function(_iv){var _iw=new T(function(){return B(A(_iv,[_it]));}),_ix=function(_iy){return E(_iw);};return [1,B(_go(_is,_ix))];},_iz=new T(function(){return B(unCStr("DC1"));}),_iA=17,_iB=function(_iC){var _iD=new T(function(){return B(A(_iC,[_iA]));}),_iE=function(_iF){return E(_iD);};return [1,B(_go(_iz,_iE))];},_iG=new T(function(){return B(unCStr("DC2"));}),_iH=18,_iI=function(_iJ){var _iK=new T(function(){return B(A(_iJ,[_iH]));}),_iL=function(_iM){return E(_iK);};return [1,B(_go(_iG,_iL))];},_iN=new T(function(){return B(unCStr("DC3"));}),_iO=19,_iP=function(_iQ){var _iR=new T(function(){return B(A(_iQ,[_iO]));}),_iS=function(_iT){return E(_iR);};return [1,B(_go(_iN,_iS))];},_iU=new T(function(){return B(unCStr("DC4"));}),_iV=20,_iW=function(_iX){var _iY=new T(function(){return B(A(_iX,[_iV]));}),_iZ=function(_j0){return E(_iY);};return [1,B(_go(_iU,_iZ))];},_j1=new T(function(){return B(unCStr("NAK"));}),_j2=21,_j3=function(_j4){var _j5=new T(function(){return B(A(_j4,[_j2]));}),_j6=function(_j7){return E(_j5);};return [1,B(_go(_j1,_j6))];},_j8=new T(function(){return B(unCStr("SYN"));}),_j9=22,_ja=function(_jb){var _jc=new T(function(){return B(A(_jb,[_j9]));}),_jd=function(_je){return E(_jc);};return [1,B(_go(_j8,_jd))];},_jf=new T(function(){return B(unCStr("ETB"));}),_jg=23,_jh=function(_ji){var _jj=new T(function(){return B(A(_ji,[_jg]));}),_jk=function(_jl){return E(_jj);};return [1,B(_go(_jf,_jk))];},_jm=new T(function(){return B(unCStr("CAN"));}),_jn=24,_jo=function(_jp){var _jq=new T(function(){return B(A(_jp,[_jn]));}),_jr=function(_js){return E(_jq);};return [1,B(_go(_jm,_jr))];},_jt=new T(function(){return B(unCStr("EM"));}),_ju=25,_jv=function(_jw){var _jx=new T(function(){return B(A(_jw,[_ju]));}),_jy=function(_jz){return E(_jx);};return [1,B(_go(_jt,_jy))];},_jA=new T(function(){return B(unCStr("SUB"));}),_jB=26,_jC=function(_jD){var _jE=new T(function(){return B(A(_jD,[_jB]));}),_jF=function(_jG){return E(_jE);};return [1,B(_go(_jA,_jF))];},_jH=new T(function(){return B(unCStr("ESC"));}),_jI=27,_jJ=function(_jK){var _jL=new T(function(){return B(A(_jK,[_jI]));}),_jM=function(_jN){return E(_jL);};return [1,B(_go(_jH,_jM))];},_jO=new T(function(){return B(unCStr("FS"));}),_jP=28,_jQ=function(_jR){var _jS=new T(function(){return B(A(_jR,[_jP]));}),_jT=function(_jU){return E(_jS);};return [1,B(_go(_jO,_jT))];},_jV=new T(function(){return B(unCStr("GS"));}),_jW=29,_jX=function(_jY){var _jZ=new T(function(){return B(A(_jY,[_jW]));}),_k0=function(_k1){return E(_jZ);};return [1,B(_go(_jV,_k0))];},_k2=new T(function(){return B(unCStr("RS"));}),_k3=30,_k4=function(_k5){var _k6=new T(function(){return B(A(_k5,[_k3]));}),_k7=function(_k8){return E(_k6);};return [1,B(_go(_k2,_k7))];},_k9=new T(function(){return B(unCStr("US"));}),_ka=31,_kb=function(_kc){var _kd=new T(function(){return B(A(_kc,[_ka]));}),_ke=function(_kf){return E(_kd);};return [1,B(_go(_k9,_ke))];},_kg=new T(function(){return B(unCStr("SP"));}),_kh=32,_ki=function(_kj){var _kk=new T(function(){return B(A(_kj,[_kh]));}),_kl=function(_km){return E(_kk);};return [1,B(_go(_kg,_kl))];},_kn=new T(function(){return B(unCStr("DEL"));}),_ko=127,_kp=function(_kq){var _kr=new T(function(){return B(A(_kq,[_ko]));}),_ks=function(_kt){return E(_kr);};return [1,B(_go(_kn,_ks))];},_ku=[1,_kp,_F],_kv=[1,_ki,_ku],_kw=[1,_kb,_kv],_kx=[1,_k4,_kw],_ky=[1,_jX,_kx],_kz=[1,_jQ,_ky],_kA=[1,_jJ,_kz],_kB=[1,_jC,_kA],_kC=[1,_jv,_kB],_kD=[1,_jo,_kC],_kE=[1,_jh,_kD],_kF=[1,_ja,_kE],_kG=[1,_j3,_kF],_kH=[1,_iW,_kG],_kI=[1,_iP,_kH],_kJ=[1,_iI,_kI],_kK=[1,_iB,_kJ],_kL=[1,_iu,_kK],_kM=[1,_in,_kL],_kN=[1,_ig,_kM],_kO=[1,_i9,_kN],_kP=[1,_i2,_kO],_kQ=[1,_hV,_kP],_kR=[1,_hO,_kQ],_kS=[1,_hH,_kR],_kT=[1,_hA,_kS],_kU=[1,_ht,_kT],_kV=[1,_hm,_kU],_kW=[1,_hf,_kV],_kX=[1,_h8,_kW],_kY=[1,_h1,_kX],_kZ=[1,_gU,_kY],_l0=[1,_gQ,_kZ],_l1=new T(function(){return B(_gf(_l0));}),_l2=34,_l3=[0,1114111],_l4=92,_l5=39,_l6=function(_l7){var _l8=new T(function(){return B(A(_l7,[_hz]));}),_l9=new T(function(){return B(A(_l7,[_hG]));}),_la=new T(function(){return B(A(_l7,[_hN]));}),_lb=new T(function(){return B(A(_l7,[_hU]));}),_lc=new T(function(){return B(A(_l7,[_i1]));}),_ld=new T(function(){return B(A(_l7,[_i8]));}),_le=new T(function(){return B(A(_l7,[_if]));}),_lf=new T(function(){return B(A(_l7,[_l4]));}),_lg=new T(function(){return B(A(_l7,[_l5]));}),_lh=new T(function(){return B(A(_l7,[_l2]));}),_li=new T(function(){var _lj=function(_lk){var _ll=new T(function(){return B(_en(E(_lk)));}),_lm=function(_ln){var _lo=B(_eZ(_ll,_ln));if(!B(_g5(_lo,_l3))){return [2];}else{var _lp=new T(function(){var _lq=B(_g2(_lo));if(_lq>>>0>1114111){return B(_fZ(_lq));}else{return _lq;}});return new F(function(){return A(_l7,[_lp]);});}};return [1,B(_cJ(_lk,_lm))];},_lr=new T(function(){var _ls=new T(function(){return B(A(_l7,[_ka]));}),_lt=new T(function(){return B(A(_l7,[_k3]));}),_lu=new T(function(){return B(A(_l7,[_jW]));}),_lv=new T(function(){return B(A(_l7,[_jP]));}),_lw=new T(function(){return B(A(_l7,[_jI]));}),_lx=new T(function(){return B(A(_l7,[_jB]));}),_ly=new T(function(){return B(A(_l7,[_ju]));}),_lz=new T(function(){return B(A(_l7,[_jn]));}),_lA=new T(function(){return B(A(_l7,[_jg]));}),_lB=new T(function(){return B(A(_l7,[_j9]));}),_lC=new T(function(){return B(A(_l7,[_j2]));}),_lD=new T(function(){return B(A(_l7,[_iV]));}),_lE=new T(function(){return B(A(_l7,[_iO]));}),_lF=new T(function(){return B(A(_l7,[_iH]));}),_lG=new T(function(){return B(A(_l7,[_iA]));}),_lH=new T(function(){return B(A(_l7,[_it]));}),_lI=new T(function(){return B(A(_l7,[_im]));}),_lJ=new T(function(){return B(A(_l7,[_gD]));}),_lK=new T(function(){return B(A(_l7,[_hs]));}),_lL=new T(function(){return B(A(_l7,[_hl]));}),_lM=new T(function(){return B(A(_l7,[_he]));}),_lN=new T(function(){return B(A(_l7,[_h7]));}),_lO=new T(function(){return B(A(_l7,[_h0]));}),_lP=new T(function(){return B(A(_l7,[_gK]));}),_lQ=new T(function(){return B(A(_l7,[_gT]));}),_lR=function(_lS){switch(E(_lS)){case 64:return E(_lQ);case 65:return E(_lP);case 66:return E(_lO);case 67:return E(_lN);case 68:return E(_lM);case 69:return E(_lL);case 70:return E(_lK);case 71:return E(_l8);case 72:return E(_l9);case 73:return E(_la);case 74:return E(_lb);case 75:return E(_lc);case 76:return E(_ld);case 77:return E(_le);case 78:return E(_lJ);case 79:return E(_lI);case 80:return E(_lH);case 81:return E(_lG);case 82:return E(_lF);case 83:return E(_lE);case 84:return E(_lD);case 85:return E(_lC);case 86:return E(_lB);case 87:return E(_lA);case 88:return E(_lz);case 89:return E(_ly);case 90:return E(_lx);case 91:return E(_lw);case 92:return E(_lv);case 93:return E(_lu);case 94:return E(_lt);case 95:return E(_ls);default:return [2];}},_lT=[0,_lR],_lU=new T(function(){return B(A(_l1,[_l7]));}),_lV=function(_lW){return (E(_lW)==94)?E(_lT):[2];};return B(_ar([0,_lV],_lU));});return B(_ar([1,B(_bZ(_fV,_fX,_lj))],_lr));}),_lX=function(_lY){switch(E(_lY)){case 34:return E(_lh);case 39:return E(_lg);case 92:return E(_lf);case 97:return E(_l8);case 98:return E(_l9);case 102:return E(_ld);case 110:return E(_lb);case 114:return E(_le);case 116:return E(_la);case 118:return E(_lc);default:return [2];}};return new F(function(){return _ar([0,_lX],_li);});},_lZ=function(_m0){return new F(function(){return A(_m0,[_4i]);});},_m1=function(_m2){var _m3=E(_m2);if(!_m3[0]){return E(_lZ);}else{var _m4=_m3[2],_m5=E(_m3[1]),_m6=_m5>>>0,_m7=new T(function(){return B(_m1(_m4));});if(_m6>887){var _m8=u_iswspace(_m5);if(!E(_m8)){return E(_lZ);}else{var _m9=function(_ma){var _mb=new T(function(){return B(A(_m7,[_ma]));});return [0,function(_mc){return E(_mb);}];};return E(_m9);}}else{var _md=E(_m6);if(_md==32){var _me=function(_mf){var _mg=new T(function(){return B(A(_m7,[_mf]));});return [0,function(_mh){return E(_mg);}];};return E(_me);}else{if(_md-9>>>0>4){if(E(_md)==160){var _mi=function(_mj){var _mk=new T(function(){return B(A(_m7,[_mj]));});return [0,function(_ml){return E(_mk);}];};return E(_mi);}else{return E(_lZ);}}else{var _mm=function(_mn){var _mo=new T(function(){return B(A(_m7,[_mn]));});return [0,function(_mp){return E(_mo);}];};return E(_mm);}}}}},_mq=function(_mr){var _ms=new T(function(){return B(_mq(_mr));}),_mt=function(_mu){return (E(_mu)==92)?E(_ms):[2];},_mv=[0,_mt],_mw=function(_mx){return E(_mv);},_my=function(_mz){return new F(function(){return A(_m1,[_mz,_mw]);});},_mA=[1,_my],_mB=new T(function(){var _mC=function(_mD){return new F(function(){return A(_mr,[[0,_mD,_4j]]);});};return B(_l6(_mC));}),_mE=function(_mF){var _mG=E(_mF);if(_mG==38){return E(_ms);}else{var _mH=_mG>>>0;if(_mH>887){var _mI=u_iswspace(_mG);return (E(_mI)==0)?[2]:E(_mA);}else{var _mJ=E(_mH);return (_mJ==32)?E(_mA):(_mJ-9>>>0>4)?(E(_mJ)==160)?E(_mA):[2]:E(_mA);}}},_mK=[0,_mE],_mL=function(_mM){var _mN=E(_mM);if(E(_mN)==92){return E(_mB);}else{return new F(function(){return A(_mr,[[0,_mN,_fP]]);});}},_mO=function(_mP){return (E(_mP)==92)?E(_mK):[2];};return new F(function(){return _ar([0,_mO],[0,_mL]);});},_mQ=function(_mR,_mS){var _mT=new T(function(){var _mU=new T(function(){return B(A(_mR,[_F]));});return B(A(_mS,[[1,_mU]]));}),_mV=function(_mW){var _mX=E(_mW),_mY=E(_mX[1]);if(E(_mY)==34){if(!E(_mX[2])){return E(_mT);}else{var _mZ=function(_n0){return new F(function(){return A(_mR,[[1,_mY,_n0]]);});};return new F(function(){return _mQ(_mZ,_mS);});}}else{var _n1=function(_n2){return new F(function(){return A(_mR,[[1,_mY,_n2]]);});};return new F(function(){return _mQ(_n1,_mS);});}};return new F(function(){return _mq(_mV);});},_n3=new T(function(){return B(unCStr("_\'"));}),_n4=function(_n5){var _n6=u_iswalnum(_n5);if(!E(_n6)){return new F(function(){return _fH(_bp,_n5,_n3);});}else{return true;}},_n7=function(_n8){return new F(function(){return _n4(E(_n8));});},_n9=new T(function(){return B(unCStr(",;()[]{}`"));}),_na=new T(function(){return B(unCStr("=>"));}),_nb=[1,_na,_F],_nc=new T(function(){return B(unCStr("~"));}),_nd=[1,_nc,_nb],_ne=new T(function(){return B(unCStr("@"));}),_nf=[1,_ne,_nd],_ng=new T(function(){return B(unCStr("->"));}),_nh=[1,_ng,_nf],_ni=new T(function(){return B(unCStr("<-"));}),_nj=[1,_ni,_nh],_nk=new T(function(){return B(unCStr("|"));}),_nl=[1,_nk,_nj],_nm=new T(function(){return B(unCStr("\\"));}),_nn=[1,_nm,_nl],_no=new T(function(){return B(unCStr("="));}),_np=[1,_no,_nn],_nq=new T(function(){return B(unCStr("::"));}),_nr=[1,_nq,_np],_ns=new T(function(){return B(unCStr(".."));}),_nt=[1,_ns,_nr],_nu=function(_nv){var _nw=new T(function(){return B(A(_nv,[_cG]));}),_nx=new T(function(){var _ny=new T(function(){var _nz=function(_nA){var _nB=new T(function(){return B(A(_nv,[[0,_nA]]));});return [0,function(_nC){return (E(_nC)==39)?E(_nB):[2];}];};return B(_l6(_nz));}),_nD=function(_nE){var _nF=E(_nE);switch(E(_nF)){case 39:return [2];case 92:return E(_ny);default:var _nG=new T(function(){return B(A(_nv,[[0,_nF]]));});return [0,function(_nH){return (E(_nH)==39)?E(_nG):[2];}];}},_nI=[0,_nD],_nJ=new T(function(){var _nK=new T(function(){return B(_mQ(_2,_nv));}),_nL=new T(function(){var _nM=new T(function(){var _nN=new T(function(){var _nO=new T(function(){return [1,B(_bZ(_dU,_fD,_nv))];}),_nP=function(_nQ){var _nR=E(_nQ),_nS=u_iswalpha(_nR);if(!E(_nS)){if(E(_nR)==95){var _nT=function(_nU){return new F(function(){return A(_nv,[[3,[1,_nR,_nU]]]);});};return [1,B(_cq(_n7,_nT))];}else{return [2];}}else{var _nV=function(_nW){return new F(function(){return A(_nv,[[3,[1,_nR,_nW]]]);});};return [1,B(_cq(_n7,_nV))];}};return B(_ar([0,_nP],_nO));}),_nX=function(_nY){if(!B(_fH(_bp,_nY,_fM))){return [2];}else{var _nZ=function(_o0){var _o1=[1,_nY,_o0];if(!B(_fH(_by,_o1,_nt))){return new F(function(){return A(_nv,[[4,_o1]]);});}else{return new F(function(){return A(_nv,[[2,_o1]]);});}};return [1,B(_cq(_fN,_nZ))];}};return B(_ar([0,_nX],_nN));}),_o2=function(_o3){if(!B(_fH(_bp,_o3,_n9))){return [2];}else{return new F(function(){return A(_nv,[[2,[1,_o3,_F]]]);});}};return B(_ar([0,_o2],_nM));}),_o4=function(_o5){return (E(_o5)==34)?E(_nK):[2];};return B(_ar([0,_o4],_nL));}),_o6=function(_o7){return (E(_o7)==39)?E(_nI):[2];};return B(_ar([0,_o6],_nJ));}),_o8=function(_o9){return (E(_o9)[0]==0)?E(_nw):[2];};return new F(function(){return _ar([1,_o8],_nx);});},_oa=0,_ob=function(_oc,_od){var _oe=new T(function(){var _of=new T(function(){var _og=function(_oh){var _oi=new T(function(){var _oj=new T(function(){return B(A(_od,[_oh]));}),_ok=function(_ol){var _om=E(_ol);return (_om[0]==2)?(!B(_be(_om[1],_bd)))?[2]:E(_oj):[2];};return B(_nu(_ok));}),_on=function(_oo){return E(_oi);};return [1,function(_op){return new F(function(){return A(_m1,[_op,_on]);});}];};return B(A(_oc,[_oa,_og]));}),_oq=function(_or){var _os=E(_or);return (_os[0]==2)?(!B(_be(_os[1],_bc)))?[2]:E(_of):[2];};return B(_nu(_oq));}),_ot=function(_ou){return E(_oe);};return function(_ov){return new F(function(){return A(_m1,[_ov,_ot]);});};},_ow=function(_ox,_oy){var _oz=function(_oA){var _oB=new T(function(){return B(A(_ox,[_oA]));}),_oC=function(_oD){var _oE=new T(function(){return [1,B(_ob(_oz,_oD))];});return new F(function(){return _ar(B(A(_oB,[_oD])),_oE);});};return E(_oC);},_oF=new T(function(){return B(A(_ox,[_oy]));}),_oG=function(_oH){var _oI=new T(function(){return [1,B(_ob(_oz,_oH))];});return new F(function(){return _ar(B(A(_oF,[_oH])),_oI);});};return E(_oG);},_oJ=function(_oK,_oL){var _oM=function(_oN,_oO){var _oP=function(_oQ){var _oR=new T(function(){return  -E(_oQ);});return new F(function(){return A(_oO,[_oR]);});},_oS=function(_oT){return new F(function(){return A(_oK,[_oT,_oN,_oP]);});},_oU=new T(function(){return B(_nu(_oS));}),_oV=function(_oW){return E(_oU);},_oX=function(_oY){return new F(function(){return A(_m1,[_oY,_oV]);});},_oZ=[1,_oX],_p0=function(_p1){var _p2=E(_p1);if(_p2[0]==4){var _p3=E(_p2[1]);if(!_p3[0]){return new F(function(){return A(_oK,[_p2,_oN,_oO]);});}else{if(E(_p3[1])==45){if(!E(_p3[2])[0]){return E(_oZ);}else{return new F(function(){return A(_oK,[_p2,_oN,_oO]);});}}else{return new F(function(){return A(_oK,[_p2,_oN,_oO]);});}}}else{return new F(function(){return A(_oK,[_p2,_oN,_oO]);});}},_p4=new T(function(){return B(_nu(_p0));}),_p5=function(_p6){return E(_p4);};return [1,function(_p7){return new F(function(){return A(_m1,[_p7,_p5]);});}];};return new F(function(){return _ow(_oM,_oL);});},_p8=function(_p9){var _pa=E(_p9);if(!_pa[0]){var _pb=_pa[1],_pc=_pa[2];return [1,new T(function(){var _pd=new T(function(){return B(_ei(_pc,0));},1),_pe=new T(function(){return B(_en(E(_pb)));});return B(_eJ(_pe,_pd,B(_5e(_ep,_pc))));})];}else{var _pf=_pa[1];if(!E(_pa[2])[0]){if(!E(_pa[3])[0]){return [1,new T(function(){return B(_eZ(_eh,_pf));})];}else{return [0];}}else{return [0];}}},_pg=function(_ph,_pi){return [2];},_pj=function(_pk){var _pl=E(_pk);if(_pl[0]==5){var _pm=B(_p8(_pl[1]));if(!_pm[0]){return E(_pg);}else{var _pn=_pm[1],_po=new T(function(){return B(_g2(_pn));}),_pp=function(_pq,_pr){return new F(function(){return A(_pr,[_po]);});};return E(_pp);}}else{return E(_pg);}},_ps=new T(function(){return B(unCStr("="));}),_pt=new T(function(){return B(unCStr("onPointIndex"));}),_pu=new T(function(){return B(unCStr(","));}),_pv=new T(function(){return B(unCStr("pointIndex"));}),_pw=new T(function(){return B(unCStr("{"));}),_px=new T(function(){return B(unCStr("PointPlacement"));}),_py=new T(function(){return B(unCStr("onBarIndex"));}),_pz=new T(function(){return B(unCStr("BarPlacement"));}),_pA=new T(function(){return B(unCStr("onSideIndex"));}),_pB=new T(function(){return B(unCStr("LeftSidePlacement"));}),_pC=new T(function(){return B(unCStr("RightSidePlacement"));}),_pD=function(_pE,_pF){var _pG=new T(function(){var _pH=new T(function(){var _pI=new T(function(){if(_pE>11){return [2];}else{var _pJ=new T(function(){var _pK=new T(function(){var _pL=new T(function(){var _pM=new T(function(){var _pN=new T(function(){var _pO=function(_pP){var _pQ=new T(function(){var _pR=new T(function(){return B(A(_pF,[[3,_pP]]));}),_pS=function(_pT){var _pU=E(_pT);return (_pU[0]==2)?(!B(_be(_pU[1],_4m)))?[2]:E(_pR):[2];};return B(_nu(_pS));}),_pV=function(_pW){return E(_pQ);};return [1,function(_pX){return new F(function(){return A(_m1,[_pX,_pV]);});}];};return B(A(_oJ,[_pj,_oa,_pO]));}),_pY=function(_pZ){var _q0=E(_pZ);return (_q0[0]==2)?(!B(_be(_q0[1],_ps)))?[2]:E(_pN):[2];};return B(_nu(_pY));}),_q1=function(_q2){return E(_pM);},_q3=function(_q4){return new F(function(){return A(_m1,[_q4,_q1]);});},_q5=[1,_q3],_q6=function(_q7){var _q8=E(_q7);return (_q8[0]==3)?(!B(_be(_q8[1],_pA)))?[2]:E(_q5):[2];};return B(_nu(_q6));}),_q9=function(_qa){return E(_pL);},_qb=function(_qc){return new F(function(){return A(_m1,[_qc,_q9]);});},_qd=[1,_qb],_qe=function(_qf){var _qg=E(_qf);return (_qg[0]==2)?(!B(_be(_qg[1],_pw)))?[2]:E(_qd):[2];};return B(_nu(_qe));}),_qh=function(_qi){return E(_pK);},_qj=function(_qk){return new F(function(){return A(_m1,[_qk,_qh]);});},_ql=[1,_qj],_qm=function(_qn){var _qo=E(_qn);return (_qo[0]==3)?(!B(_be(_qo[1],_pC)))?[2]:E(_ql):[2];};return B(_nu(_qm));}),_qp=function(_qq){return E(_pJ);};return [1,function(_qr){return new F(function(){return A(_m1,[_qr,_qp]);});}];}});if(_pE>11){return B(_ar(_bQ,_pI));}else{var _qs=new T(function(){var _qt=new T(function(){var _qu=new T(function(){var _qv=new T(function(){var _qw=new T(function(){var _qx=function(_qy){var _qz=new T(function(){var _qA=new T(function(){return B(A(_pF,[[2,_qy]]));}),_qB=function(_qC){var _qD=E(_qC);return (_qD[0]==2)?(!B(_be(_qD[1],_4m)))?[2]:E(_qA):[2];};return B(_nu(_qB));}),_qE=function(_qF){return E(_qz);};return [1,function(_qG){return new F(function(){return A(_m1,[_qG,_qE]);});}];};return B(A(_oJ,[_pj,_oa,_qx]));}),_qH=function(_qI){var _qJ=E(_qI);return (_qJ[0]==2)?(!B(_be(_qJ[1],_ps)))?[2]:E(_qw):[2];};return B(_nu(_qH));}),_qK=function(_qL){return E(_qv);},_qM=function(_qN){return new F(function(){return A(_m1,[_qN,_qK]);});},_qO=[1,_qM],_qP=function(_qQ){var _qR=E(_qQ);return (_qR[0]==3)?(!B(_be(_qR[1],_pA)))?[2]:E(_qO):[2];};return B(_nu(_qP));}),_qS=function(_qT){return E(_qu);},_qU=function(_qV){return new F(function(){return A(_m1,[_qV,_qS]);});},_qW=[1,_qU],_qX=function(_qY){var _qZ=E(_qY);return (_qZ[0]==2)?(!B(_be(_qZ[1],_pw)))?[2]:E(_qW):[2];};return B(_nu(_qX));}),_r0=function(_r1){return E(_qt);},_r2=function(_r3){return new F(function(){return A(_m1,[_r3,_r0]);});},_r4=[1,_r2],_r5=function(_r6){var _r7=E(_r6);return (_r7[0]==3)?(!B(_be(_r7[1],_pB)))?[2]:E(_r4):[2];};return B(_nu(_r5));}),_r8=function(_r9){return E(_qs);},_ra=function(_rb){return new F(function(){return A(_m1,[_rb,_r8]);});};return B(_ar([1,_ra],_pI));}});if(_pE>11){return B(_ar(_bQ,_pH));}else{var _rc=new T(function(){var _rd=new T(function(){var _re=new T(function(){var _rf=new T(function(){var _rg=new T(function(){var _rh=function(_ri){var _rj=new T(function(){var _rk=new T(function(){return B(A(_pF,[[1,_ri]]));}),_rl=function(_rm){var _rn=E(_rm);return (_rn[0]==2)?(!B(_be(_rn[1],_4m)))?[2]:E(_rk):[2];};return B(_nu(_rl));}),_ro=function(_rp){return E(_rj);};return [1,function(_rq){return new F(function(){return A(_m1,[_rq,_ro]);});}];};return B(A(_oJ,[_pj,_oa,_rh]));}),_rr=function(_rs){var _rt=E(_rs);return (_rt[0]==2)?(!B(_be(_rt[1],_ps)))?[2]:E(_rg):[2];};return B(_nu(_rr));}),_ru=function(_rv){return E(_rf);},_rw=function(_rx){return new F(function(){return A(_m1,[_rx,_ru]);});},_ry=[1,_rw],_rz=function(_rA){var _rB=E(_rA);return (_rB[0]==3)?(!B(_be(_rB[1],_py)))?[2]:E(_ry):[2];};return B(_nu(_rz));}),_rC=function(_rD){return E(_re);},_rE=function(_rF){return new F(function(){return A(_m1,[_rF,_rC]);});},_rG=[1,_rE],_rH=function(_rI){var _rJ=E(_rI);return (_rJ[0]==2)?(!B(_be(_rJ[1],_pw)))?[2]:E(_rG):[2];};return B(_nu(_rH));}),_rK=function(_rL){return E(_rd);},_rM=function(_rN){return new F(function(){return A(_m1,[_rN,_rK]);});},_rO=[1,_rM],_rP=function(_rQ){var _rR=E(_rQ);return (_rR[0]==3)?(!B(_be(_rR[1],_pz)))?[2]:E(_rO):[2];};return B(_nu(_rP));}),_rS=function(_rT){return E(_rc);},_rU=function(_rV){return new F(function(){return A(_m1,[_rV,_rS]);});};return B(_ar([1,_rU],_pH));}});if(_pE>11){return new F(function(){return _ar(_bQ,_pG);});}else{var _rW=new T(function(){var _rX=new T(function(){var _rY=new T(function(){var _rZ=new T(function(){var _s0=new T(function(){var _s1=function(_s2){var _s3=new T(function(){var _s4=new T(function(){var _s5=new T(function(){var _s6=new T(function(){var _s7=function(_s8){var _s9=new T(function(){var _sa=new T(function(){return B(A(_pF,[[0,_s2,_s8]]));}),_sb=function(_sc){var _sd=E(_sc);return (_sd[0]==2)?(!B(_be(_sd[1],_4m)))?[2]:E(_sa):[2];};return B(_nu(_sb));}),_se=function(_sf){return E(_s9);};return [1,function(_sg){return new F(function(){return A(_m1,[_sg,_se]);});}];};return B(A(_oJ,[_pj,_oa,_s7]));}),_sh=function(_si){var _sj=E(_si);return (_sj[0]==2)?(!B(_be(_sj[1],_ps)))?[2]:E(_s6):[2];};return B(_nu(_sh));}),_sk=function(_sl){return E(_s5);},_sm=function(_sn){return new F(function(){return A(_m1,[_sn,_sk]);});},_so=[1,_sm],_sp=function(_sq){var _sr=E(_sq);return (_sr[0]==3)?(!B(_be(_sr[1],_pt)))?[2]:E(_so):[2];};return B(_nu(_sp));}),_ss=function(_st){return E(_s4);},_su=function(_sv){return new F(function(){return A(_m1,[_sv,_ss]);});},_sw=[1,_su],_sx=function(_sy){var _sz=E(_sy);return (_sz[0]==2)?(!B(_be(_sz[1],_pu)))?[2]:E(_sw):[2];};return B(_nu(_sx));}),_sA=function(_sB){return E(_s3);};return [1,function(_sC){return new F(function(){return A(_m1,[_sC,_sA]);});}];};return B(A(_oJ,[_pj,_oa,_s1]));}),_sD=function(_sE){var _sF=E(_sE);return (_sF[0]==2)?(!B(_be(_sF[1],_ps)))?[2]:E(_s0):[2];};return B(_nu(_sD));}),_sG=function(_sH){return E(_rZ);},_sI=function(_sJ){return new F(function(){return A(_m1,[_sJ,_sG]);});},_sK=[1,_sI],_sL=function(_sM){var _sN=E(_sM);return (_sN[0]==3)?(!B(_be(_sN[1],_pv)))?[2]:E(_sK):[2];};return B(_nu(_sL));}),_sO=function(_sP){return E(_rY);},_sQ=function(_sR){return new F(function(){return A(_m1,[_sR,_sO]);});},_sS=[1,_sQ],_sT=function(_sU){var _sV=E(_sU);return (_sV[0]==2)?(!B(_be(_sV[1],_pw)))?[2]:E(_sS):[2];};return B(_nu(_sT));}),_sW=function(_sX){return E(_rX);},_sY=function(_sZ){return new F(function(){return A(_m1,[_sZ,_sW]);});},_t0=[1,_sY],_t1=function(_t2){var _t3=E(_t2);return (_t3[0]==3)?(!B(_be(_t3[1],_px)))?[2]:E(_t0):[2];};return B(_nu(_t1));}),_t4=function(_t5){return E(_rW);},_t6=function(_t7){return new F(function(){return A(_m1,[_t7,_t4]);});};return new F(function(){return _ar([1,_t6],_pG);});}},_t8=function(_t9,_ta){return new F(function(){return _pD(E(_t9),_ta);});},_tb=function(_tc){var _td=[3,_tc,_bQ],_te=function(_tf){return E(_td);};return [1,function(_tg){return new F(function(){return A(_m1,[_tg,_te]);});}];},_th=new T(function(){return B(A(_ow,[_t8,_oa,_tb]));}),_ti=new T(function(){return B(err(_aa));}),_tj=new T(function(){return B(err(_ac));}),_tk=function(_tl,_tm){return new F(function(){return A(_tm,[_6r]);});},_tn=[0,_4l,_tk],_to=[1,_tn,_F],_tp=function(_tq,_tr){return new F(function(){return A(_tr,[_6q]);});},_ts=[0,_4k,_tp],_tt=[1,_ts,_to],_tu=function(_tv,_tw,_tx){var _ty=E(_tv);if(!_ty[0]){return [2];}else{var _tz=_ty[2],_tA=E(_ty[1]),_tB=_tA[1],_tC=_tA[2],_tD=new T(function(){return B(A(_tC,[_tw,_tx]));}),_tE=function(_tF){var _tG=E(_tF);switch(_tG[0]){case 3:return (!B(_be(_tB,_tG[1])))?[2]:E(_tD);case 4:return (!B(_be(_tB,_tG[1])))?[2]:E(_tD);default:return [2];}},_tH=new T(function(){return B(_nu(_tE));}),_tI=function(_tJ){return E(_tH);},_tK=new T(function(){return B(_tu(_tz,_tw,_tx));}),_tL=function(_tM){return new F(function(){return A(_m1,[_tM,_tI]);});};return new F(function(){return _ar([1,_tL],_tK);});}},_tN=function(_tO,_tP){return new F(function(){return _tu(_tt,_tO,_tP);});},_tQ=new T(function(){return B(A(_ow,[_tN,_oa,_tb]));}),_tR=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:245:9-15"));}),_tS=[0,_2z,_2A,_F,_tR,_2z,_2z],_tT=new T(function(){return B(_2x(_tS));}),_tU=new T(function(){return B(unCStr("joinGame"));}),_tV=function(_tW){return E(E(_tW)[1]);},_tX=function(_tY){return E(E(_tY)[1]);},_tZ=function(_u0){return E(E(_u0)[2]);},_u1=function(_u2){return E(E(_u2)[2]);},_u3=function(_u4){return E(E(_u4)[1]);},_u5=function(_){return new F(function(){return nMV(_2z);});},_u6=new T(function(){return B(_8x(_u5));}),_u7=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_u8=function(_u9){return E(E(_u9)[2]);},_ua=function(_ub){return E(E(_ub)[4]);},_uc=function(_ud,_ue,_uf,_ug,_uh,_ui){var _uj=B(_tV(_ud)),_uk=B(_tX(_uj)),_ul=new T(function(){return B(_5o(_uj));}),_um=new T(function(){return B(_ua(_uk));}),_un=new T(function(){return B(A(_5m,[_ue,_ug]));}),_uo=new T(function(){return B(A(_u3,[_uf,_uh]));}),_up=function(_uq){return new F(function(){return A(_um,[[0,_uo,_un,_uq]]);});},_ur=function(_us){var _ut=new T(function(){var _uu=new T(function(){var _uv=E(_un),_uw=E(_uo),_ux=E(_us),_uy=function(_uz,_){var _uA=B(A(_ux,[_uz,_]));return _8B;},_uB=__createJSFunc(2,E(_uy)),_uC=_uB,_uD=function(_){return new F(function(){return E(_u7)(_uv,_uw,_uC);});};return E(_uD);});return B(A(_ul,[_uu]));});return new F(function(){return A(_tZ,[_uk,_ut,_up]);});},_uE=new T(function(){var _uF=new T(function(){return B(_5o(_uj));}),_uG=function(_uH){var _uI=new T(function(){var _uJ=function(_){var _=wMV(E(_u6),[1,_uH]);return new F(function(){return A(_u1,[_uf,_uh,_uH,_]);});};return B(A(_uF,[_uJ]));});return new F(function(){return A(_tZ,[_uk,_uI,_ui]);});};return B(A(_u8,[_ud,_uG]));});return new F(function(){return A(_tZ,[_uk,_uE,_ur]);});},_uK=function(_uL,_uM){var _uN=E(_uM);if(!_uN[0]){return [0];}else{var _uO=_uN[1],_uP=_uN[2],_uQ=E(_uL);if(_uQ==1){return [1,_uO,_F];}else{var _uR=new T(function(){return B(_uK(_uQ-1|0,_uP));});return [1,_uO,_uR];}}},_uS=function(_uT,_uU,_uV){if(_uV<=_uU){var _uW=new T(function(){var _uX=_uU-_uT|0,_uY=_uV-_uX|0,_uZ=function(_v0){if(_v0>=_uY){var _v1=new T(function(){return B(_uZ(_v0+_uX|0));});return [1,_v0,_v1];}else{return [1,_v0,_F];}};return B(_uZ(_uU));});return [1,_uT,_uW];}else{return (_uV<=_uT)?[1,_uT,_F]:[0];}},_v2=function(_v3,_v4,_v5){if(_v5>=_v4){var _v6=new T(function(){var _v7=_v4-_v3|0,_v8=_v5-_v7|0,_v9=function(_va){if(_va<=_v8){var _vb=new T(function(){return B(_v9(_va+_v7|0));});return [1,_va,_vb];}else{return [1,_va,_F];}};return B(_v9(_v4));});return [1,_v3,_v6];}else{return (_v5>=_v3)?[1,_v3,_F]:[0];}},_vc=function(_vd,_ve){if(_ve<_vd){return new F(function(){return _uS(_vd,_ve,-2147483648);});}else{return new F(function(){return _v2(_vd,_ve,2147483647);});}},_vf=new T(function(){return B(_vc(135,150));}),_vg=new T(function(){return B(_uK(6,_vf));}),_vh=function(_vi,_vj){var _vk=E(_vi);if(!_vk[0]){return E(_vg);}else{var _vl=_vk[1],_vm=_vk[2],_vn=E(_vj);if(_vn==1){return [1,_vl,_vg];}else{var _vo=new T(function(){return B(_vh(_vm,_vn-1|0));});return [1,_vl,_vo];}}},_vp=new T(function(){return B(_vc(25,40));}),_vq=new T(function(){return B(_vh(_vp,6));}),_vr=function(_vs){while(1){var _vt=(function(_vu){var _vv=E(_vu);if(!_vv[0]){return [0];}else{var _vw=_vv[2],_vx=E(_vv[1]);if(!E(_vx[2])[0]){var _vy=new T(function(){return B(_vr(_vw));});return [1,_vx[1],_vy];}else{_vs=_vw;return null;}}})(_vs);if(_vt!=null){return _vt;}}},_vz=function(_vA,_vB){var _vC=E(_vB);if(!_vC[0]){return [0,_F,_F];}else{var _vD=_vC[1],_vE=_vC[2];if(!B(A(_vA,[_vD]))){var _vF=new T(function(){var _vG=B(_vz(_vA,_vE));return [0,_vG[1],_vG[2]];}),_vH=new T(function(){return E(E(_vF)[2]);}),_vI=new T(function(){return E(E(_vF)[1]);});return [0,[1,_vD,_vI],_vH];}else{return [0,_F,_vC];}}},_vJ=function(_vK,_vL){while(1){var _vM=E(_vL);if(!_vM[0]){return [0];}else{if(!B(A(_vK,[_vM[1]]))){return E(_vM);}else{_vL=_vM[2];continue;}}}},_vN=function(_vO){var _vP=_vO>>>0;if(_vP>887){var _vQ=u_iswspace(_vO);return (E(_vQ)==0)?false:true;}else{var _vR=E(_vP);return (_vR==32)?true:(_vR-9>>>0>4)?(E(_vR)==160)?true:false:true;}},_vS=function(_vT){return new F(function(){return _vN(E(_vT));});},_vU=function(_vV){var _vW=B(_vJ(_vS,_vV));if(!_vW[0]){return [0];}else{var _vX=new T(function(){var _vY=B(_vz(_vS,_vW));return [0,_vY[1],_vY[2]];}),_vZ=new T(function(){return B(_vU(E(_vX)[2]));}),_w0=new T(function(){return E(E(_vX)[1]);});return [1,_w0,_vZ];}},_w1=function(_w2,_){var _w3=jsFind(toJSStr(E(_tU)));if(!_w3[0]){return new F(function(){return die(_tT);});}else{var _w4=B(A(_uc,[_9a,_4,_98,_w3[1],_9q,_9A,_])),_w5=function(_w6){var _w7=new T(function(){var _w8=String(E(_w6));return B(_vU(fromJSStr(_w8)));}),_w9=new T(function(){var _wa=new T(function(){return B(_5e(_a7,B(_9n(_w7,2))));});return B(_vr(B(_af(_th,_wa))));}),_wb=new T(function(){var _wc=new T(function(){return B(_9n(_w7,1));}),_wd=B(_vr(B(_af(_tQ,_wc))));if(!_wd[0]){return E(_ti);}else{if(!E(_wd[2])[0]){return E(_wd[1]);}else{return E(_tj);}}}),_we=function(_wf){var _wg=new T(function(){var _wh=new T(function(){var _wi=B(A(_wf,[_]));return E(_wi);}),_wj=function(_wk){var _wl=E(_wk)-E(_wh);return (_wl==0)?true:(_wl<=0)? -_wl<7:_wl<7;};return B(_9S(_wj,_vq));}),_wm=function(_wn,_){var _wo=E(_w2),_wp=_wo[1],_wq=_wo[2],_wr=_wo[3],_ws=_wo[4],_wt=_wo[5],_wu=_wo[6],_wv=_wo[7],_ww=E(_w9);if(!_ww[0]){return E(_ab);}else{if(!E(_ww[2])[0]){var _wx=E(_ww[1]);if(!_wx[0]){var _wy=_wx[1],_wz=_wx[2],_wA=E(_wg);if(!_wA[0]){var _wB=B(_9J(_wx,_wx,_wb,_));return _8B;}else{var _wC=_wA[1],_wD=B(A(_wn,[_])),_wE=function(_wF,_wG){var _wH=E(_wy),_wI=_wH;if(_wF<=_wI){return new F(function(){return _9J(_wx,_wx,_wb,_);});}else{var _wJ=B(_9n(_wp,_wF)),_wK=_wJ[2],_wL=function(_){var _wM=B(_9J(_wx,[0,_wG,_wK],_wb,_)),_wN=new T(function(){return E(B(_9n(_wp,_wI))[1]);}),_wO=function(_wP,_wQ){var _wR=E(_wP);if(!_wR[0]){return [0];}else{var _wS=_wR[1],_wT=_wR[2],_wU=E(_wQ);if(!_wU[0]){return [0];}else{var _wV=_wU[1],_wW=_wU[2],_wX=new T(function(){return B(_wO(_wT,_wW));}),_wY=new T(function(){var _wZ=E(_wS);if(_wZ!=_wI){if(_wZ!=_wF){return E(_wV);}else{var _x0=new T(function(){return E(E(_wV)[2])+1|0;});return [0,_wN,_x0];}}else{var _x1=new T(function(){return E(E(_wV)[2])-1|0;}),_x2=new T(function(){return E(E(_wV)[1]);});return [0,_x2,_x1];}});return [1,_wY,_wX];}}},_x3=B(_wO(_5P,_wp)),_x4=function(_x5,_){while(1){var _x6=(function(_x7,_){var _x8=E(_x7);if(!_x8[0]){return _4i;}else{var _x9=_x8[1],_xa=new T(function(){return E(_x9)-1|0;}),_xb=B(_9J([0,_wH,_x9],[0,_wH,_xa],_wu,_));_x5=_x8[2];return null;}})(_x5,_);if(_x6!=null){return _x6;}}},_xc=function(_xd,_xe){while(1){var _xf=E(_xe);if(!_xf[0]){return [0];}else{var _xg=_xf[2],_xh=E(_xd);if(_xh==1){return E(_xg);}else{_xd=_xh-1|0;_xe=_xg;continue;}}}},_xi=B(_x4(B(_xc(1,B(_5J(E(_wz),E(B(_9n(_x3,_wI))[2]))))),_));return new F(function(){return _w1([0,_x3,_wq,_wr,_ws,_wt,_wu,_wv],_);});},_xj=function(_){if(E(_wK)>=2){return new F(function(){return _9J(_wx,_wx,_wb,_);});}else{return new F(function(){return _wL(_);});}};if(!E(_wJ[1])){if(!E(_wb)){return new F(function(){return _wL(_);});}else{return new F(function(){return _xj(_);});}}else{if(!E(_wb)){return new F(function(){return _xj(_);});}else{return new F(function(){return _wL(_);});}}}};if(E(_wD)<=E(_a6)){var _xk=E(_wC),_xl=B(_wE(_xk,_xk));return _8B;}else{var _xm=23-E(_wC)|0,_xn=B(_wE(_xm,_xm));return _8B;}}}else{var _xo=B(_9J(_wx,_wx,_wb,_));return _8B;}}else{return E(_ad);}}};return E(_wm);};return E(_we);},_xp=__createJSFunc(4,E(_w5)),_xq=E(_9R)(_xp);return new F(function(){return _99(_);});}},_xr=new T(function(){return B(unCStr("You have not joined a game (yet)."));}),_xs=new T(function(){return B(unCStr("innerHTML"));}),_xt=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:265:9-15"));}),_xu=[0,_2z,_2A,_F,_xt,_2z,_2z],_xv=new T(function(){return B(_2x(_xu));}),_xw=function(_xx,_xy,_xz,_xA,_xB){var _xC=function(_){var _xD=jsSet(B(A(_5m,[_xx,_xz])),toJSStr(E(_xA)),toJSStr(E(_xB)));return _4i;};return new F(function(){return A(_5o,[_xy,_xC]);});},_xE=function(_){var _xF=jsFind("HintText");if(!_xF[0]){return new F(function(){return die(_xv);});}else{var _xG=B(A(_xw,[_4,_2I,_xF[1],_xs,_xr,_])),_xH=E(_7D),_xI=B(_60(_6r,_xH,_)),_xJ=B(_60(_6q,_xH,_));return new F(function(){return _w1(_7E,_);});}},_xK=function(_){return new F(function(){return _xE(_);});};
var hasteMain = function() {B(A(_xK, [0]));};window.onload = hasteMain;