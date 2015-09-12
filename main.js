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

var _0=function(_1,_){return [1,_1];},_2=function(_3){return E(_3);},_4=[0,_2,_0],_5=function(_6,_7,_){var _8=B(A(_6,[_])),_9=B(A(_7,[_]));return _8;},_a=function(_b,_c,_){var _d=B(A(_b,[_])),_e=_d,_f=B(A(_c,[_])),_g=_f;return new T(function(){return B(A(_e,[_g]));});},_h=function(_i,_j,_){var _k=B(A(_j,[_]));return _i;},_l=function(_m,_n,_){var _o=B(A(_n,[_])),_p=_o;return new T(function(){return B(A(_m,[_p]));});},_q=[0,_l,_h],_r=function(_s,_){return _s;},_t=function(_u,_v,_){var _w=B(A(_u,[_]));return new F(function(){return A(_v,[_]);});},_x=[0,_q,_r,_a,_t,_5],_y=function(_z,_A,_){var _B=B(A(_z,[_]));return new F(function(){return A(_A,[_B,_]);});},_C=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_D=new T(function(){return B(unCStr("base"));}),_E=new T(function(){return B(unCStr("IOException"));}),_F=[0],_G=new T(function(){var _H=hs_wordToWord64(4053623282),_I=hs_wordToWord64(3693590983);return [0,_H,_I,[0,_H,_I,_D,_C,_E],_F,_F];}),_J=function(_K){return E(_G);},_L=function(_M){return E(E(_M)[1]);},_N=function(_O,_P,_Q){var _R=B(A(_O,[_])),_S=B(A(_P,[_])),_T=hs_eqWord64(_R[1],_S[1]);if(!_T){return [0];}else{var _U=hs_eqWord64(_R[2],_S[2]);return (!_U)?[0]:[1,_Q];}},_V=function(_W){var _X=E(_W);return new F(function(){return _N(B(_L(_X[1])),_J,_X[2]);});},_Y=new T(function(){return B(unCStr(": "));}),_Z=new T(function(){return B(unCStr(")"));}),_10=new T(function(){return B(unCStr(" ("));}),_11=function(_12,_13){var _14=E(_12);if(!_14[0]){return E(_13);}else{var _15=_14[2],_16=new T(function(){return B(_11(_15,_13));});return [1,_14[1],_16];}},_17=new T(function(){return B(unCStr("interrupted"));}),_18=new T(function(){return B(unCStr("system error"));}),_19=new T(function(){return B(unCStr("unsatisified constraints"));}),_1a=new T(function(){return B(unCStr("user error"));}),_1b=new T(function(){return B(unCStr("permission denied"));}),_1c=new T(function(){return B(unCStr("illegal operation"));}),_1d=new T(function(){return B(unCStr("end of file"));}),_1e=new T(function(){return B(unCStr("resource exhausted"));}),_1f=new T(function(){return B(unCStr("resource busy"));}),_1g=new T(function(){return B(unCStr("does not exist"));}),_1h=new T(function(){return B(unCStr("already exists"));}),_1i=new T(function(){return B(unCStr("resource vanished"));}),_1j=new T(function(){return B(unCStr("timeout"));}),_1k=new T(function(){return B(unCStr("unsupported operation"));}),_1l=new T(function(){return B(unCStr("hardware fault"));}),_1m=new T(function(){return B(unCStr("inappropriate type"));}),_1n=new T(function(){return B(unCStr("invalid argument"));}),_1o=new T(function(){return B(unCStr("failed"));}),_1p=new T(function(){return B(unCStr("protocol error"));}),_1q=function(_1r,_1s){switch(E(_1r)){case 0:return new F(function(){return _11(_1h,_1s);});break;case 1:return new F(function(){return _11(_1g,_1s);});break;case 2:return new F(function(){return _11(_1f,_1s);});break;case 3:return new F(function(){return _11(_1e,_1s);});break;case 4:return new F(function(){return _11(_1d,_1s);});break;case 5:return new F(function(){return _11(_1c,_1s);});break;case 6:return new F(function(){return _11(_1b,_1s);});break;case 7:return new F(function(){return _11(_1a,_1s);});break;case 8:return new F(function(){return _11(_19,_1s);});break;case 9:return new F(function(){return _11(_18,_1s);});break;case 10:return new F(function(){return _11(_1p,_1s);});break;case 11:return new F(function(){return _11(_1o,_1s);});break;case 12:return new F(function(){return _11(_1n,_1s);});break;case 13:return new F(function(){return _11(_1m,_1s);});break;case 14:return new F(function(){return _11(_1l,_1s);});break;case 15:return new F(function(){return _11(_1k,_1s);});break;case 16:return new F(function(){return _11(_1j,_1s);});break;case 17:return new F(function(){return _11(_1i,_1s);});break;default:return new F(function(){return _11(_17,_1s);});}},_1t=new T(function(){return B(unCStr("}"));}),_1u=new T(function(){return B(unCStr("{handle: "));}),_1v=function(_1w,_1x,_1y,_1z,_1A,_1B){var _1C=new T(function(){var _1D=new T(function(){var _1E=new T(function(){var _1F=E(_1z);if(!_1F[0]){return E(_1B);}else{var _1G=new T(function(){var _1H=new T(function(){return B(_11(_Z,_1B));},1);return B(_11(_1F,_1H));},1);return B(_11(_10,_1G));}},1);return B(_1q(_1x,_1E));}),_1I=E(_1y);if(!_1I[0]){return E(_1D);}else{var _1J=new T(function(){return B(_11(_Y,_1D));},1);return B(_11(_1I,_1J));}}),_1K=E(_1A);if(!_1K[0]){var _1L=E(_1w);if(!_1L[0]){return E(_1C);}else{var _1M=E(_1L[1]);if(!_1M[0]){var _1N=_1M[1],_1O=new T(function(){var _1P=new T(function(){var _1Q=new T(function(){return B(_11(_Y,_1C));},1);return B(_11(_1t,_1Q));},1);return B(_11(_1N,_1P));},1);return new F(function(){return _11(_1u,_1O);});}else{var _1R=_1M[1],_1S=new T(function(){var _1T=new T(function(){var _1U=new T(function(){return B(_11(_Y,_1C));},1);return B(_11(_1t,_1U));},1);return B(_11(_1R,_1T));},1);return new F(function(){return _11(_1u,_1S);});}}}else{var _1V=new T(function(){return B(_11(_Y,_1C));},1);return new F(function(){return _11(_1K[1],_1V);});}},_1W=function(_1X){var _1Y=E(_1X);return new F(function(){return _1v(_1Y[1],_1Y[2],_1Y[3],_1Y[4],_1Y[6],_F);});},_1Z=function(_20,_21,_22){var _23=E(_21);return new F(function(){return _1v(_23[1],_23[2],_23[3],_23[4],_23[6],_22);});},_24=function(_25,_26){var _27=E(_25);return new F(function(){return _1v(_27[1],_27[2],_27[3],_27[4],_27[6],_26);});},_28=44,_29=93,_2a=91,_2b=function(_2c,_2d,_2e){var _2f=E(_2d);if(!_2f[0]){return new F(function(){return unAppCStr("[]",_2e);});}else{var _2g=_2f[1],_2h=_2f[2],_2i=new T(function(){var _2j=new T(function(){var _2k=[1,_29,_2e],_2l=function(_2m){var _2n=E(_2m);if(!_2n[0]){return E(_2k);}else{var _2o=_2n[1],_2p=_2n[2],_2q=new T(function(){var _2r=new T(function(){return B(_2l(_2p));});return B(A(_2c,[_2o,_2r]));});return [1,_28,_2q];}};return B(_2l(_2h));});return B(A(_2c,[_2g,_2j]));});return [1,_2a,_2i];}},_2s=function(_2t,_2u){return new F(function(){return _2b(_24,_2t,_2u);});},_2v=[0,_1Z,_1W,_2s],_2w=new T(function(){return [0,_J,_2v,_2x,_V,_1W];}),_2x=function(_2y){return [0,_2w,_2y];},_2z=[0],_2A=7,_2B=function(_2C){return [0,_2z,_2A,_F,_2C,_2z,_2z];},_2D=function(_2E,_){var _2F=new T(function(){var _2G=new T(function(){return B(_2B(_2E));});return B(_2x(_2G));});return new F(function(){return die(_2F);});},_2H=[0,_x,_y,_t,_r,_2D],_2I=[0,_2H,_2],_2J=function(_2K,_2L){while(1){var _2M=E(_2K);if(!_2M[0]){return E(_2L);}else{_2K=_2M[2];var _2N=[1,_2M[1],_2L];_2L=_2N;continue;}}},_2O=2,_2P=0,_2Q=[1,_2P,_F],_2R=[1,_2P,_2Q],_2S=[1,_2P,_2R],_2T=[1,_2P,_2S],_2U=[1,_2P,_2T],_2V=5,_2W=[1,_2V,_2U],_2X=[1,_2P,_2W],_2Y=3,_2Z=[1,_2Y,_2X],_30=[1,_2P,_2Z],_31=[1,_2P,_30],_32=[1,_2P,_31],_33=[1,_2P,_32],_34=[1,_2V,_33],_35=[1,_2P,_34],_36=[1,_2P,_35],_37=[1,_2P,_36],_38=[1,_2P,_37],_39=[1,_2P,_38],_3a=[1,_2P,_39],_3b=[1,_2P,_3a],_3c=[1,_2P,_3b],_3d=[1,_2P,_3c],_3e=[1,_2P,_3d],_3f=1,_3g=function(_3h){var _3i=E(_3h);if(!_3i[0]){return [0];}else{var _3j=_3i[2],_3k=new T(function(){return B(_3g(_3j));});return [1,[0,_3f,_3i[1]],_3k];}},_3l=function(_3m,_3n){var _3o=new T(function(){return B(_3g(_3n));});return [1,[0,_3f,_3m],_3o];},_3p=new T(function(){return B(_3l(_2O,_3e));}),_3q=new T(function(){return B(_2J(_3p,_F));}),_3r=0,_3s=function(_3t){var _3u=E(_3t);return (E(_3u[1])==0)?E(_3u):[0,_3r,_3u[2]];},_3v=function(_3w,_3x){var _3y=E(_3x);if(!_3y[0]){return [0];}else{var _3z=_3y[1],_3A=_3y[2],_3B=new T(function(){return B(_3v(_3w,_3A));}),_3C=new T(function(){return B(A(_3w,[_3z]));});return [1,_3C,_3B];}},_3D=new T(function(){return B(_3v(_3s,_3q));}),_3E=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3F=new T(function(){return B(unCStr("base"));}),_3G=new T(function(){return B(unCStr("PatternMatchFail"));}),_3H=new T(function(){var _3I=hs_wordToWord64(18445595),_3J=hs_wordToWord64(52003073);return [0,_3I,_3J,[0,_3I,_3J,_3F,_3E,_3G],_F,_F];}),_3K=function(_3L){return E(_3H);},_3M=function(_3N){var _3O=E(_3N);return new F(function(){return _N(B(_L(_3O[1])),_3K,_3O[2]);});},_3P=function(_3Q){return E(E(_3Q)[1]);},_3R=function(_3S){return [0,_3T,_3S];},_3U=function(_3V,_3W){return new F(function(){return _11(E(_3V)[1],_3W);});},_3X=function(_3Y,_3Z){return new F(function(){return _2b(_3U,_3Y,_3Z);});},_40=function(_41,_42,_43){return new F(function(){return _11(E(_42)[1],_43);});},_44=[0,_40,_3P,_3X],_3T=new T(function(){return [0,_3K,_44,_3R,_3M,_3P];}),_45=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_46=function(_47){return E(E(_47)[3]);},_48=function(_49,_4a){var _4b=new T(function(){return B(A(_46,[_4a,_49]));});return new F(function(){return die(_4b);});},_4c=function(_4d,_4e){return new F(function(){return _48(_4d,_4e);});},_4f=function(_4g,_4h){var _4i=E(_4h);if(!_4i[0]){return [0,_F,_F];}else{var _4j=_4i[1],_4k=_4i[2];if(!B(A(_4g,[_4j]))){return [0,_F,_4i];}else{var _4l=new T(function(){var _4m=B(_4f(_4g,_4k));return [0,_4m[1],_4m[2]];}),_4n=new T(function(){return E(E(_4l)[2]);}),_4o=new T(function(){return E(E(_4l)[1]);});return [0,[1,_4j,_4o],_4n];}}},_4p=32,_4q=new T(function(){return B(unCStr("\n"));}),_4r=function(_4s){return (E(_4s)==124)?false:true;},_4t=function(_4u,_4v){var _4w=B(_4f(_4r,B(unCStr(_4u)))),_4x=_4w[1],_4y=function(_4z,_4A){var _4B=new T(function(){var _4C=new T(function(){var _4D=new T(function(){return B(_11(_4A,_4q));},1);return B(_11(_4v,_4D));});return B(unAppCStr(": ",_4C));},1);return new F(function(){return _11(_4z,_4B);});},_4E=E(_4w[2]);if(!_4E[0]){return new F(function(){return _4y(_4x,_F);});}else{if(E(_4E[1])==124){return new F(function(){return _4y(_4x,[1,_4p,_4E[2]]);});}else{return new F(function(){return _4y(_4x,_F);});}}},_4F=function(_4G){var _4H=new T(function(){return B(_4t(_4G,_45));});return new F(function(){return _4c([0,_4H],_3T);});},_4I=function(_4J,_4K){var _4L=E(_4J);if(!E(_4L[1])){return new F(function(){return _4F("main.hs:(254,20)-(255,55)|function whiteOrBlack");});}else{return (E(_4L[2])==0)?E(_4K):E(_4L);}},_4M=function(_4N,_4O,_4P){var _4Q=E(_4O);if(!_4Q[0]){return [0];}else{var _4R=_4Q[1],_4S=_4Q[2],_4T=E(_4P);if(!_4T[0]){return [0];}else{var _4U=_4T[1],_4V=_4T[2],_4W=new T(function(){return B(_4M(_4N,_4S,_4V));}),_4X=new T(function(){return B(A(_4N,[_4R,_4U]));});return [1,_4X,_4W];}}},_4Y=new T(function(){return B(_4M(_4I,_3p,_3D));}),_4Z=function(_50,_51){while(1){var _52=E(_50);if(!_52[0]){return E(_51);}else{_50=_52[2];var _53=_51+E(_52[1])|0;_51=_53;continue;}}},_54=function(_55,_56,_57){return new F(function(){return _4Z(_56,_57+_55|0);});},_58=new T(function(){return B(_54(2,_3e,0));}),_59=[0,_4Y,_58,_58,_2P,_2P,_3f,_3f],_5a="deltaZ",_5b="deltaY",_5c="deltaX",_5d=function(_5e,_5f){var _5g=jsShowI(_5e);return new F(function(){return _11(fromJSStr(_5g),_5f);});},_5h=41,_5i=40,_5j=function(_5k,_5l,_5m){if(_5l>=0){return new F(function(){return _5d(_5l,_5m);});}else{if(_5k<=6){return new F(function(){return _5d(_5l,_5m);});}else{var _5n=new T(function(){var _5o=jsShowI(_5l);return B(_11(fromJSStr(_5o),[1,_5h,_5m]));});return [1,_5i,_5n];}}},_5p=new T(function(){return B(unCStr(")"));}),_5q=new T(function(){return B(_5j(0,2,_5p));}),_5r=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_5q));}),_5s=function(_5t){var _5u=new T(function(){return B(_5j(0,_5t,_5r));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_5u)));});},_5v=function(_5w,_){return new T(function(){var _5x=Number(E(_5w)),_5y=jsTrunc(_5x);if(_5y<0){return B(_5s(_5y));}else{if(_5y>2){return B(_5s(_5y));}else{return _5y;}}});},_5z=0,_5A=[0,_5z,_5z,_5z],_5B="button",_5C=new T(function(){return jsGetMouseCoords;}),_5D=function(_5E,_){var _5F=E(_5E);if(!_5F[0]){return _F;}else{var _5G=_5F[1],_5H=B(_5D(_5F[2],_)),_5I=new T(function(){var _5J=Number(E(_5G));return jsTrunc(_5J);});return [1,_5I,_5H];}},_5K=function(_5L,_){var _5M=__arr2lst(0,_5L);return new F(function(){return _5D(_5M,_);});},_5N=function(_5O,_){return new F(function(){return _5K(E(_5O),_);});},_5P=function(_5Q,_){return new T(function(){var _5R=Number(E(_5Q));return jsTrunc(_5R);});},_5S=[0,_5P,_5N],_5T=function(_5U,_){var _5V=E(_5U);if(!_5V[0]){return _F;}else{var _5W=B(_5T(_5V[2],_));return [1,_5V[1],_5W];}},_5X=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_5Y=[0,_2z,_2A,_F,_5X,_2z,_2z],_5Z=new T(function(){return B(_2x(_5Y));}),_60=function(_){return new F(function(){return die(_5Z);});},_61=function(_62){return E(E(_62)[1]);},_63=function(_64,_65,_66,_){var _67=__arr2lst(0,_66),_68=B(_5T(_67,_)),_69=E(_68);if(!_69[0]){return new F(function(){return _60(_);});}else{var _6a=E(_69[2]);if(!_6a[0]){return new F(function(){return _60(_);});}else{if(!E(_6a[2])[0]){var _6b=B(A(_61,[_64,_69[1],_])),_6c=B(A(_61,[_65,_6a[1],_]));return [0,_6b,_6c];}else{return new F(function(){return _60(_);});}}}},_6d=function(_){return new F(function(){return __jsNull();});},_6e=function(_6f){var _6g=B(A(_6f,[_]));return E(_6g);},_6h=new T(function(){return B(_6e(_6d));}),_6i=new T(function(){return E(_6h);}),_6j=function(_6k,_6l,_){if(E(_6k)==7){var _6m=E(_5C)(_6l),_6n=B(_63(_5S,_5S,_6m,_)),_6o=_6n,_6p=_6l[E(_5c)],_6q=_6p,_6r=_6l[E(_5b)],_6s=_6r,_6t=_6l[E(_5a)],_6u=_6t;return new T(function(){return [0,E(_6o),E(_2z),[0,_6q,_6s,_6u]];});}else{var _6v=E(_5C)(_6l),_6w=B(_63(_5S,_5S,_6v,_)),_6x=_6w,_6y=_6l[E(_5B)],_6z=__eq(_6y,E(_6i));if(!E(_6z)){var _6A=B(_5v(_6y,_)),_6B=_6A;return new T(function(){return [0,E(_6x),[1,_6B],E(_5A)];});}else{return new T(function(){return [0,E(_6x),E(_2z),E(_5A)];});}}},_6C=function(_6D,_6E,_){return new F(function(){return _6j(_6D,E(_6E),_);});},_6F="mouseout",_6G="mouseover",_6H="mousemove",_6I="mouseup",_6J="mousedown",_6K="dblclick",_6L="click",_6M="wheel",_6N=function(_6O){switch(E(_6O)){case 0:return E(_6L);case 1:return E(_6K);case 2:return E(_6J);case 3:return E(_6I);case 4:return E(_6H);case 5:return E(_6G);case 6:return E(_6F);default:return E(_6M);}},_6P=[0,_6N,_6C],_6Q=0,_6R=function(_){return _6Q;},_6S=[0,_2I,_r],_6T=new T(function(){return B(unCStr("!!: negative index"));}),_6U=new T(function(){return B(unCStr("Prelude."));}),_6V=new T(function(){return B(_11(_6U,_6T));}),_6W=new T(function(){return B(err(_6V));}),_6X=new T(function(){return B(unCStr("!!: index too large"));}),_6Y=new T(function(){return B(_11(_6U,_6X));}),_6Z=new T(function(){return B(err(_6Y));}),_70=function(_71,_72){while(1){var _73=E(_71);if(!_73[0]){return E(_6Z);}else{var _74=E(_72);if(!_74){return E(_73[1]);}else{_71=_73[2];_72=_74-1|0;continue;}}}},_75=function(_76,_77){if(_77>=0){return new F(function(){return _70(_76,_77);});}else{return E(_6W);}},_78=new T(function(){return B(unCStr("}"));}),_79=new T(function(){return B(unCStr(", "));}),_7a=new T(function(){return B(unCStr("onSideIndex = "));}),_7b=new T(function(){return B(unCStr("RightSidePlacement {"));}),_7c=new T(function(){return B(unCStr("LeftSidePlacement {"));}),_7d=new T(function(){return B(unCStr("onBarIndex = "));}),_7e=new T(function(){return B(unCStr("BarPlacement {"));}),_7f=new T(function(){return B(unCStr("onPointIndex = "));}),_7g=new T(function(){return B(unCStr("pointIndex = "));}),_7h=new T(function(){return B(unCStr("PointPlacement {"));}),_7i=function(_7j,_7k,_7l){var _7m=E(_7k);switch(_7m[0]){case 0:var _7n=_7m[1],_7o=_7m[2],_7p=function(_7q){var _7r=new T(function(){var _7s=new T(function(){var _7t=new T(function(){var _7u=new T(function(){var _7v=new T(function(){return B(_11(_78,_7q));});return B(_5j(0,E(_7o),_7v));},1);return B(_11(_7f,_7u));},1);return B(_11(_79,_7t));});return B(_5j(0,E(_7n),_7s));},1);return new F(function(){return _11(_7g,_7r);});};if(_7j<11){var _7w=new T(function(){return B(_7p(_7l));},1);return new F(function(){return _11(_7h,_7w);});}else{var _7x=new T(function(){var _7y=new T(function(){return B(_7p([1,_5h,_7l]));},1);return B(_11(_7h,_7y));});return [1,_5i,_7x];}break;case 1:var _7z=_7m[1],_7A=function(_7B){var _7C=new T(function(){var _7D=new T(function(){var _7E=new T(function(){return B(_11(_78,_7B));});return B(_5j(0,E(_7z),_7E));},1);return B(_11(_7d,_7D));},1);return new F(function(){return _11(_7e,_7C);});};if(_7j<11){return new F(function(){return _7A(_7l);});}else{var _7F=new T(function(){return B(_7A([1,_5h,_7l]));});return [1,_5i,_7F];}break;case 2:var _7G=_7m[1],_7H=function(_7I){var _7J=new T(function(){var _7K=new T(function(){var _7L=new T(function(){return B(_11(_78,_7I));});return B(_5j(0,E(_7G),_7L));},1);return B(_11(_7a,_7K));},1);return new F(function(){return _11(_7c,_7J);});};if(_7j<11){return new F(function(){return _7H(_7l);});}else{var _7M=new T(function(){return B(_7H([1,_5h,_7l]));});return [1,_5i,_7M];}break;default:var _7N=_7m[1],_7O=function(_7P){var _7Q=new T(function(){var _7R=new T(function(){var _7S=new T(function(){return B(_11(_78,_7P));});return B(_5j(0,E(_7N),_7S));},1);return B(_11(_7a,_7R));},1);return new F(function(){return _11(_7b,_7Q);});};if(_7j<11){return new F(function(){return _7O(_7l);});}else{var _7T=new T(function(){return B(_7O([1,_5h,_7l]));});return [1,_5i,_7T];}}},_7U=true,_7V=new T(function(){return B(unCStr("Black"));}),_7W=new T(function(){return B(unCStr("White"));}),_7X=95,_7Y=function(_7Z){var _80=E(_7Z);return (E(_80)==32)?E(_7X):E(_80);},_81=new T(function(){return B(unCStr("draggable "));}),_82=new T(function(){return B(unCStr("class"));}),_83=function(_84){return E(E(_84)[1]);},_85=function(_86){return E(E(_86)[2]);},_87=function(_88,_89,_8a,_8b,_8c){var _8d=function(_){var _8e=jsSetAttr(B(A(_83,[_88,_8a])),toJSStr(E(_8b)),toJSStr(E(_8c)));return _6Q;};return new F(function(){return A(_85,[_89,_8d]);});},_8f=function(_8g,_8h,_8i,_8j,_){var _8k=new T(function(){var _8l=new T(function(){var _8m=new T(function(){var _8n=new T(function(){return B(_3v(_7Y,B(_7i(0,_8j,_F))));});return B(unAppCStr(" ",_8n));});if(!E(_8h)){return B(_11(_7V,_8m));}else{return B(_11(_7W,_8m));}});if(!E(_8i)){return E(_8l);}else{return B(_11(_81,_8l));}});return new F(function(){return A(_87,[_4,_2I,_8g,_82,_8k,_]);});},_8o=new T(function(){return B(unCStr(": empty list"));}),_8p=function(_8q){var _8r=new T(function(){return B(_11(_8q,_8o));},1);return new F(function(){return err(B(_11(_6U,_8r)));});},_8s=new T(function(){return B(unCStr("head"));}),_8t=new T(function(){return B(_8p(_8s));}),_8u=new T(function(){return (function (elem, cx, cy, duration) {$(elem).velocity({ cx: cx, cy: cy }, { duration: duration });});}),_8v=function(_8w){return new F(function(){return _4F("main.hs:(200,1)-(204,42)|function moveChecker");});},_8x=new T(function(){return B(_8v(_));}),_8y=function(_8z,_8A,_8B,_){var _8C=E(_8A);if(!_8C[0]){var _8D=_8C[1],_8E=E(_8B);if(!_8E[0]){var _8F=_8E[2],_8G=jsElemsByClassName(toJSStr(B(_3v(_7Y,B(_7i(0,_8C,_F))))));if(!_8G[0]){return E(_8t);}else{var _8H=E(_8G[1]),_8I=_8H,_8J=E(_8E[1]),_8K=function(_8L){var _8M=_8L,_8N=function(_8O){var _8P=E(_8u)(_8I,_8M,_8O,300),_8Q=new T(function(){return E(B(_75(_8z,E(_8D)))[1]);},1);return new F(function(){return _8f(_8H,_8Q,_7U,_8E,_);});};if(_8J>=12){return new F(function(){return _8N(203+(imul(imul(imul(-1,E(_8F))|0,2)|0,6)|0)|0);});}else{return new F(function(){return _8N(7+(imul(imul(E(_8F),2)|0,6)|0)|0);});}};if(_8J>=12){var _8R=23-_8J|0;if(_8R>=6){return new F(function(){return _8K(25+(20+(imul(_8R,15)|0)|0)|0);});}else{return new F(function(){return _8K(25+(imul(_8R,15)|0)|0);});}}else{if(_8J>=6){return new F(function(){return _8K(25+(20+(imul(_8J,15)|0)|0)|0);});}else{return new F(function(){return _8K(25+(imul(_8J,15)|0)|0);});}}}}else{return E(_8x);}}else{return E(_8x);}},_8S=0,_8T=new T(function(){return (function (msg) { alert(msg); });}),_8U="value",_8V=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:236:9-19"));}),_8W=[0,_2z,_2A,_F,_8V,_2z,_2z],_8X=new T(function(){return B(_2x(_8W));}),_8Y=function(_){var _8Z=jsFind("sharedKey");if(!_8Z[0]){return new F(function(){return die(_8X);});}else{var _90=jsGet(E(_8Z[1]),E(_8U)),_91=E(_8T)(toJSStr(fromJSStr(_90)));return new F(function(){return _6R(_);});}},_92=function(_93,_){return new F(function(){return _8Y(_);});},_94=function(_95,_96){if(_95<=_96){var _97=function(_98){var _99=new T(function(){if(_98!=_96){return B(_97(_98+1|0));}else{return [0];}});return [1,_98,_99];};return new F(function(){return _97(_95);});}else{return [0];}},_9a=new T(function(){return (function (cb) {setDropCheckerCallback_ffi(cb);});}),_9b=function(_9c,_9d){var _9e=function(_9f,_9g){while(1){var _9h=(function(_9i,_9j){var _9k=E(_9i);if(!_9k[0]){return [0];}else{var _9l=_9k[2];if(!B(A(_9c,[_9k[1]]))){_9f=_9l;var _9m=_9j+1|0;_9g=_9m;return null;}else{var _9n=new T(function(){return B(_9e(_9l,_9j+1|0));});return [1,_9j,_9n];}}})(_9f,_9g);if(_9h!=null){return _9h;}}},_9o=B(_9e(_9d,0));return (_9o[0]==0)?[0]:[1,_9o[1]];},_9p=new T(function(){return B(_94(0,2147483647));}),_9q=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_9r=new T(function(){return B(err(_9q));}),_9s=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_9t=new T(function(){return B(err(_9s));}),_9u=new T(function(){return B(_4F("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_9v=function(_9w,_9x){while(1){var _9y=(function(_9z,_9A){var _9B=E(_9z);switch(_9B[0]){case 0:var _9C=E(_9A);if(!_9C[0]){return [0];}else{_9w=B(A(_9B[1],[_9C[1]]));_9x=_9C[2];return null;}break;case 1:var _9D=B(A(_9B[1],[_9A])),_9E=_9A;_9w=_9D;_9x=_9E;return null;case 2:return [0];case 3:var _9F=_9B[2],_9G=new T(function(){return B(_9v(_9F,_9A));});return [1,[0,_9B[1],_9A],_9G];default:return E(_9B[1]);}})(_9w,_9x);if(_9y!=null){return _9y;}}},_9H=function(_9I,_9J){var _9K=function(_9L){var _9M=E(_9J);if(_9M[0]==3){var _9N=_9M[2],_9O=new T(function(){return B(_9H(_9I,_9N));});return [3,_9M[1],_9O];}else{var _9P=E(_9I);if(_9P[0]==2){return E(_9M);}else{var _9Q=E(_9M);if(_9Q[0]==2){return E(_9P);}else{var _9R=function(_9S){var _9T=E(_9Q);if(_9T[0]==4){var _9U=_9T[1];return [1,function(_9V){return [4,new T(function(){return B(_11(B(_9v(_9P,_9V)),_9U));})];}];}else{var _9W=E(_9P);if(_9W[0]==1){var _9X=_9W[1],_9Y=E(_9T);if(!_9Y[0]){return [1,function(_9Z){return new F(function(){return _9H(B(A(_9X,[_9Z])),_9Y);});}];}else{var _a0=_9Y[1];return [1,function(_a1){var _a2=new T(function(){return B(A(_a0,[_a1]));});return new F(function(){return _9H(B(A(_9X,[_a1])),_a2);});}];}}else{var _a3=E(_9T);if(!_a3[0]){return E(_9u);}else{var _a4=_a3[1];return [1,function(_a5){var _a6=new T(function(){return B(A(_a4,[_a5]));});return new F(function(){return _9H(_9W,_a6);});}];}}}},_a7=E(_9P);switch(_a7[0]){case 1:var _a8=_a7[1],_a9=E(_9Q);if(_a9[0]==4){var _aa=_a9[1];return [1,function(_ab){return [4,new T(function(){return B(_11(B(_9v(B(A(_a8,[_ab])),_ab)),_aa));})];}];}else{return new F(function(){return _9R(_);});}break;case 4:var _ac=_a7[1],_ad=E(_9Q);switch(_ad[0]){case 0:return [1,function(_ae){return [4,new T(function(){var _af=new T(function(){return B(_9v(_ad,_ae));},1);return B(_11(_ac,_af));})];}];case 1:var _ag=_ad[1];return [1,function(_ah){return [4,new T(function(){var _ai=new T(function(){return B(_9v(B(A(_ag,[_ah])),_ah));},1);return B(_11(_ac,_ai));})];}];default:var _aj=_ad[1];return [4,new T(function(){return B(_11(_ac,_aj));})];}break;default:return new F(function(){return _9R(_);});}}}}},_ak=E(_9I);switch(_ak[0]){case 0:var _al=_ak[1],_am=E(_9J);if(!_am[0]){var _an=_am[1];return [0,function(_ao){var _ap=new T(function(){return B(A(_an,[_ao]));});return new F(function(){return _9H(B(A(_al,[_ao])),_ap);});}];}else{return new F(function(){return _9K(_);});}break;case 3:var _aq=_ak[2],_ar=new T(function(){return B(_9H(_aq,_9J));});return [3,_ak[1],_ar];default:return new F(function(){return _9K(_);});}},_as=new T(function(){return B(unCStr("("));}),_at=new T(function(){return B(unCStr(")"));}),_au=function(_av,_aw){while(1){var _ax=E(_av);if(!_ax[0]){return (E(_aw)[0]==0)?true:false;}else{var _ay=E(_aw);if(!_ay[0]){return false;}else{if(E(_ax[1])!=E(_ay[1])){return false;}else{_av=_ax[2];_aw=_ay[2];continue;}}}}},_az=function(_aA,_aB){return E(_aA)!=E(_aB);},_aC=function(_aD,_aE){return E(_aD)==E(_aE);},_aF=[0,_aC,_az],_aG=function(_aH,_aI){while(1){var _aJ=E(_aH);if(!_aJ[0]){return (E(_aI)[0]==0)?true:false;}else{var _aK=E(_aI);if(!_aK[0]){return false;}else{if(E(_aJ[1])!=E(_aK[1])){return false;}else{_aH=_aJ[2];_aI=_aK[2];continue;}}}}},_aL=function(_aM,_aN){return (!B(_aG(_aM,_aN)))?true:false;},_aO=[0,_aG,_aL],_aP=function(_aQ,_aR){var _aS=E(_aQ);switch(_aS[0]){case 0:var _aT=_aS[1];return [0,function(_aU){return new F(function(){return _aP(B(A(_aT,[_aU])),_aR);});}];case 1:var _aV=_aS[1];return [1,function(_aW){return new F(function(){return _aP(B(A(_aV,[_aW])),_aR);});}];case 2:return [2];case 3:var _aX=_aS[2],_aY=new T(function(){return B(_aP(_aX,_aR));});return new F(function(){return _9H(B(A(_aR,[_aS[1]])),_aY);});break;default:var _aZ=function(_b0){var _b1=E(_b0);if(!_b1[0]){return [0];}else{var _b2=_b1[2],_b3=E(_b1[1]),_b4=new T(function(){return B(_aZ(_b2));},1);return new F(function(){return _11(B(_9v(B(A(_aR,[_b3[1]])),_b3[2])),_b4);});}},_b5=B(_aZ(_aS[1]));return (_b5[0]==0)?[2]:[4,_b5];}},_b6=[2],_b7=function(_b8){return [3,_b8,_b6];},_b9=function(_ba,_bb){var _bc=E(_ba);if(!_bc){return new F(function(){return A(_bb,[_6Q]);});}else{var _bd=new T(function(){return B(_b9(_bc-1|0,_bb));});return [0,function(_be){return E(_bd);}];}},_bf=function(_bg,_bh,_bi){var _bj=new T(function(){return B(A(_bg,[_b7]));}),_bk=function(_bl,_bm,_bn,_bo){while(1){var _bp=(function(_bq,_br,_bs,_bt){var _bu=E(_bq);switch(_bu[0]){case 0:var _bv=E(_br);if(!_bv[0]){return new F(function(){return A(_bh,[_bt]);});}else{_bl=B(A(_bu[1],[_bv[1]]));_bm=_bv[2];var _bw=_bs+1|0,_bx=_bt;_bn=_bw;_bo=_bx;return null;}break;case 1:var _by=B(A(_bu[1],[_br])),_bz=_br,_bw=_bs,_bx=_bt;_bl=_by;_bm=_bz;_bn=_bw;_bo=_bx;return null;case 2:return new F(function(){return A(_bh,[_bt]);});break;case 3:var _bA=new T(function(){return B(_aP(_bu,_bt));}),_bB=function(_bC){return E(_bA);};return new F(function(){return _b9(_bs,_bB);});break;default:return new F(function(){return _aP(_bu,_bt);});}})(_bl,_bm,_bn,_bo);if(_bp!=null){return _bp;}}};return function(_bD){return new F(function(){return _bk(_bj,_bD,0,_bi);});};},_bE=function(_bF){return new F(function(){return A(_bF,[_F]);});},_bG=function(_bH,_bI){var _bJ=function(_bK){var _bL=E(_bK);if(!_bL[0]){return E(_bE);}else{var _bM=_bL[1],_bN=_bL[2];if(!B(A(_bH,[_bM]))){return E(_bE);}else{var _bO=new T(function(){return B(_bJ(_bN));}),_bP=function(_bQ){var _bR=new T(function(){var _bS=function(_bT){return new F(function(){return A(_bQ,[[1,_bM,_bT]]);});};return B(A(_bO,[_bS]));});return [0,function(_bU){return E(_bR);}];};return E(_bP);}}};return function(_bV){return new F(function(){return A(_bJ,[_bV,_bI]);});};},_bW=[6],_bX=new T(function(){return B(unCStr("valDig: Bad base"));}),_bY=new T(function(){return B(err(_bX));}),_bZ=function(_c0,_c1){var _c2=function(_c3,_c4){var _c5=E(_c3);if(!_c5[0]){var _c6=new T(function(){return B(A(_c4,[_F]));}),_c7=function(_c8){return new F(function(){return A(_c8,[_c6]);});};return E(_c7);}else{var _c9=_c5[2],_ca=E(_c5[1]),_cb=function(_cc){var _cd=new T(function(){var _ce=function(_cf){return new F(function(){return A(_c4,[[1,_cc,_cf]]);});};return B(_c2(_c9,_ce));}),_cg=function(_ch){var _ci=new T(function(){return B(A(_cd,[_ch]));});return [0,function(_cj){return E(_ci);}];};return E(_cg);};switch(E(_c0)){case 8:if(48>_ca){var _ck=new T(function(){return B(A(_c4,[_F]));}),_cl=function(_cm){return new F(function(){return A(_cm,[_ck]);});};return E(_cl);}else{if(_ca>55){var _cn=new T(function(){return B(A(_c4,[_F]));}),_co=function(_cp){return new F(function(){return A(_cp,[_cn]);});};return E(_co);}else{return new F(function(){return _cb(_ca-48|0);});}}break;case 10:if(48>_ca){var _cq=new T(function(){return B(A(_c4,[_F]));}),_cr=function(_cs){return new F(function(){return A(_cs,[_cq]);});};return E(_cr);}else{if(_ca>57){var _ct=new T(function(){return B(A(_c4,[_F]));}),_cu=function(_cv){return new F(function(){return A(_cv,[_ct]);});};return E(_cu);}else{return new F(function(){return _cb(_ca-48|0);});}}break;case 16:if(48>_ca){if(97>_ca){if(65>_ca){var _cw=new T(function(){return B(A(_c4,[_F]));}),_cx=function(_cy){return new F(function(){return A(_cy,[_cw]);});};return E(_cx);}else{if(_ca>70){var _cz=new T(function(){return B(A(_c4,[_F]));}),_cA=function(_cB){return new F(function(){return A(_cB,[_cz]);});};return E(_cA);}else{return new F(function(){return _cb((_ca-65|0)+10|0);});}}}else{if(_ca>102){if(65>_ca){var _cC=new T(function(){return B(A(_c4,[_F]));}),_cD=function(_cE){return new F(function(){return A(_cE,[_cC]);});};return E(_cD);}else{if(_ca>70){var _cF=new T(function(){return B(A(_c4,[_F]));}),_cG=function(_cH){return new F(function(){return A(_cH,[_cF]);});};return E(_cG);}else{return new F(function(){return _cb((_ca-65|0)+10|0);});}}}else{return new F(function(){return _cb((_ca-97|0)+10|0);});}}}else{if(_ca>57){if(97>_ca){if(65>_ca){var _cI=new T(function(){return B(A(_c4,[_F]));}),_cJ=function(_cK){return new F(function(){return A(_cK,[_cI]);});};return E(_cJ);}else{if(_ca>70){var _cL=new T(function(){return B(A(_c4,[_F]));}),_cM=function(_cN){return new F(function(){return A(_cN,[_cL]);});};return E(_cM);}else{return new F(function(){return _cb((_ca-65|0)+10|0);});}}}else{if(_ca>102){if(65>_ca){var _cO=new T(function(){return B(A(_c4,[_F]));}),_cP=function(_cQ){return new F(function(){return A(_cQ,[_cO]);});};return E(_cP);}else{if(_ca>70){var _cR=new T(function(){return B(A(_c4,[_F]));}),_cS=function(_cT){return new F(function(){return A(_cT,[_cR]);});};return E(_cS);}else{return new F(function(){return _cb((_ca-65|0)+10|0);});}}}else{return new F(function(){return _cb((_ca-97|0)+10|0);});}}}else{return new F(function(){return _cb(_ca-48|0);});}}break;default:return E(_bY);}}},_cU=function(_cV){var _cW=E(_cV);if(!_cW[0]){return [2];}else{return new F(function(){return A(_c1,[_cW]);});}};return function(_cX){return new F(function(){return A(_c2,[_cX,_2,_cU]);});};},_cY=16,_cZ=8,_d0=function(_d1){var _d2=function(_d3){return new F(function(){return A(_d1,[[5,[0,_cZ,_d3]]]);});},_d4=function(_d5){return new F(function(){return A(_d1,[[5,[0,_cY,_d5]]]);});},_d6=function(_d7){switch(E(_d7)){case 79:return [1,B(_bZ(_cZ,_d2))];case 88:return [1,B(_bZ(_cY,_d4))];case 111:return [1,B(_bZ(_cZ,_d2))];case 120:return [1,B(_bZ(_cY,_d4))];default:return [2];}},_d8=[0,_d6];return function(_d9){return (E(_d9)==48)?E(_d8):[2];};},_da=function(_db){return [0,B(_d0(_db))];},_dc=function(_dd){return new F(function(){return A(_dd,[_2z]);});},_de=function(_df){return new F(function(){return A(_df,[_2z]);});},_dg=10,_dh=[0,1],_di=[0,2147483647],_dj=function(_dk,_dl){while(1){var _dm=E(_dk);if(!_dm[0]){var _dn=_dm[1],_do=E(_dl);if(!_do[0]){var _dp=_do[1],_dq=addC(_dn,_dp);if(!E(_dq[2])){return [0,_dq[1]];}else{_dk=[1,I_fromInt(_dn)];_dl=[1,I_fromInt(_dp)];continue;}}else{_dk=[1,I_fromInt(_dn)];_dl=_do;continue;}}else{var _dr=E(_dl);if(!_dr[0]){_dk=_dm;_dl=[1,I_fromInt(_dr[1])];continue;}else{return [1,I_add(_dm[1],_dr[1])];}}}},_ds=new T(function(){return B(_dj(_di,_dh));}),_dt=function(_du){var _dv=E(_du);if(!_dv[0]){var _dw=E(_dv[1]);return (_dw==(-2147483648))?E(_ds):[0, -_dw];}else{return [1,I_negate(_dv[1])];}},_dx=[0,10],_dy=function(_dz,_dA){while(1){var _dB=E(_dz);if(!_dB[0]){return E(_dA);}else{_dz=_dB[2];var _dC=_dA+1|0;_dA=_dC;continue;}}},_dD=function(_dE){return [0,_dE];},_dF=function(_dG){return new F(function(){return _dD(E(_dG));});},_dH=new T(function(){return B(unCStr("this should not happen"));}),_dI=new T(function(){return B(err(_dH));}),_dJ=function(_dK,_dL){while(1){var _dM=E(_dK);if(!_dM[0]){var _dN=_dM[1],_dO=E(_dL);if(!_dO[0]){var _dP=_dO[1];if(!(imul(_dN,_dP)|0)){return [0,imul(_dN,_dP)|0];}else{_dK=[1,I_fromInt(_dN)];_dL=[1,I_fromInt(_dP)];continue;}}else{_dK=[1,I_fromInt(_dN)];_dL=_dO;continue;}}else{var _dQ=E(_dL);if(!_dQ[0]){_dK=_dM;_dL=[1,I_fromInt(_dQ[1])];continue;}else{return [1,I_mul(_dM[1],_dQ[1])];}}}},_dR=function(_dS,_dT){var _dU=E(_dT);if(!_dU[0]){return [0];}else{var _dV=E(_dU[2]);if(!_dV[0]){return E(_dI);}else{var _dW=_dV[2],_dX=new T(function(){return B(_dR(_dS,_dW));});return [1,B(_dj(B(_dJ(_dU[1],_dS)),_dV[1])),_dX];}}},_dY=[0,0],_dZ=function(_e0,_e1,_e2){while(1){var _e3=(function(_e4,_e5,_e6){var _e7=E(_e6);if(!_e7[0]){return E(_dY);}else{if(!E(_e7[2])[0]){return E(_e7[1]);}else{var _e8=E(_e5);if(_e8<=40){var _e9=_dY,_ea=_e7;while(1){var _eb=E(_ea);if(!_eb[0]){return E(_e9);}else{var _ec=B(_dj(B(_dJ(_e9,_e4)),_eb[1]));_ea=_eb[2];_e9=_ec;continue;}}}else{var _ed=B(_dJ(_e4,_e4));if(!(_e8%2)){_e0=_ed;_e1=quot(_e8+1|0,2);var _ee=B(_dR(_e4,_e7));_e2=_ee;return null;}else{_e0=_ed;_e1=quot(_e8+1|0,2);var _ee=B(_dR(_e4,[1,_dY,_e7]));_e2=_ee;return null;}}}}})(_e0,_e1,_e2);if(_e3!=null){return _e3;}}},_ef=function(_eg,_eh){var _ei=new T(function(){return B(_dy(_eh,0));},1);return new F(function(){return _dZ(_eg,_ei,B(_3v(_dF,_eh)));});},_ej=function(_ek){var _el=new T(function(){var _em=new T(function(){var _en=function(_eo){var _ep=new T(function(){return B(_ef(_dx,_eo));});return new F(function(){return A(_ek,[[1,_ep]]);});};return [1,B(_bZ(_dg,_en))];}),_eq=function(_er){if(E(_er)==43){var _es=function(_et){var _eu=new T(function(){return B(_ef(_dx,_et));});return new F(function(){return A(_ek,[[1,_eu]]);});};return [1,B(_bZ(_dg,_es))];}else{return [2];}},_ev=function(_ew){if(E(_ew)==45){var _ex=function(_ey){var _ez=new T(function(){return B(_dt(B(_ef(_dx,_ey))));});return new F(function(){return A(_ek,[[1,_ez]]);});};return [1,B(_bZ(_dg,_ex))];}else{return [2];}};return B(_9H(B(_9H([0,_ev],[0,_eq])),_em));}),_eA=function(_eB){return (E(_eB)==69)?E(_el):[2];},_eC=function(_eD){return (E(_eD)==101)?E(_el):[2];};return new F(function(){return _9H([0,_eC],[0,_eA]);});},_eE=function(_eF){var _eG=function(_eH){return new F(function(){return A(_eF,[[1,_eH]]);});};return function(_eI){return (E(_eI)==46)?[1,B(_bZ(_dg,_eG))]:[2];};},_eJ=function(_eK){return [0,B(_eE(_eK))];},_eL=function(_eM){var _eN=function(_eO){var _eP=function(_eQ){var _eR=function(_eS){return new F(function(){return A(_eM,[[5,[1,_eO,_eQ,_eS]]]);});};return [1,B(_bf(_ej,_dc,_eR))];};return [1,B(_bf(_eJ,_de,_eP))];};return new F(function(){return _bZ(_dg,_eN);});},_eT=function(_eU){return [1,B(_eL(_eU))];},_eV=function(_eW){return E(E(_eW)[1]);},_eX=function(_eY,_eZ,_f0){while(1){var _f1=E(_f0);if(!_f1[0]){return false;}else{if(!B(A(_eV,[_eY,_eZ,_f1[1]]))){_f0=_f1[2];continue;}else{return true;}}}},_f2=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_f3=function(_f4){return new F(function(){return _eX(_aF,_f4,_f2);});},_f5=false,_f6=function(_f7){var _f8=new T(function(){return B(A(_f7,[_cZ]));}),_f9=new T(function(){return B(A(_f7,[_cY]));});return function(_fa){switch(E(_fa)){case 79:return E(_f8);case 88:return E(_f9);case 111:return E(_f8);case 120:return E(_f9);default:return [2];}};},_fb=function(_fc){return [0,B(_f6(_fc))];},_fd=function(_fe){return new F(function(){return A(_fe,[_dg]);});},_ff=function(_fg){var _fh=new T(function(){return B(_5j(9,_fg,_F));});return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",_fh)));});},_fi=function(_fj){var _fk=E(_fj);if(!_fk[0]){return E(_fk[1]);}else{return new F(function(){return I_toInt(_fk[1]);});}},_fl=function(_fm,_fn){var _fo=E(_fm);if(!_fo[0]){var _fp=_fo[1],_fq=E(_fn);return (_fq[0]==0)?_fp<=_fq[1]:I_compareInt(_fq[1],_fp)>=0;}else{var _fr=_fo[1],_fs=E(_fn);return (_fs[0]==0)?I_compareInt(_fr,_fs[1])<=0:I_compare(_fr,_fs[1])<=0;}},_ft=function(_fu){return [2];},_fv=function(_fw){var _fx=E(_fw);if(!_fx[0]){return E(_ft);}else{var _fy=_fx[1],_fz=E(_fx[2]);if(!_fz[0]){return E(_fy);}else{var _fA=new T(function(){return B(_fv(_fz));}),_fB=function(_fC){var _fD=new T(function(){return B(A(_fA,[_fC]));});return new F(function(){return _9H(B(A(_fy,[_fC])),_fD);});};return E(_fB);}}},_fE=function(_fF,_fG){var _fH=function(_fI,_fJ,_fK){var _fL=E(_fI);if(!_fL[0]){return new F(function(){return A(_fK,[_fF]);});}else{var _fM=_fL[2],_fN=E(_fJ);if(!_fN[0]){return [2];}else{var _fO=_fN[2];if(E(_fL[1])!=E(_fN[1])){return [2];}else{var _fP=new T(function(){return B(_fH(_fM,_fO,_fK));});return [0,function(_fQ){return E(_fP);}];}}}};return function(_fR){return new F(function(){return _fH(_fF,_fR,_fG);});};},_fS=new T(function(){return B(unCStr("SO"));}),_fT=14,_fU=function(_fV){var _fW=new T(function(){return B(A(_fV,[_fT]));}),_fX=function(_fY){return E(_fW);};return [1,B(_fE(_fS,_fX))];},_fZ=new T(function(){return B(unCStr("SOH"));}),_g0=1,_g1=function(_g2){var _g3=new T(function(){return B(A(_g2,[_g0]));}),_g4=function(_g5){return E(_g3);};return [1,B(_fE(_fZ,_g4))];},_g6=function(_g7){return [1,B(_bf(_g1,_fU,_g7))];},_g8=new T(function(){return B(unCStr("NUL"));}),_g9=0,_ga=function(_gb){var _gc=new T(function(){return B(A(_gb,[_g9]));}),_gd=function(_ge){return E(_gc);};return [1,B(_fE(_g8,_gd))];},_gf=new T(function(){return B(unCStr("STX"));}),_gg=2,_gh=function(_gi){var _gj=new T(function(){return B(A(_gi,[_gg]));}),_gk=function(_gl){return E(_gj);};return [1,B(_fE(_gf,_gk))];},_gm=new T(function(){return B(unCStr("ETX"));}),_gn=3,_go=function(_gp){var _gq=new T(function(){return B(A(_gp,[_gn]));}),_gr=function(_gs){return E(_gq);};return [1,B(_fE(_gm,_gr))];},_gt=new T(function(){return B(unCStr("EOT"));}),_gu=4,_gv=function(_gw){var _gx=new T(function(){return B(A(_gw,[_gu]));}),_gy=function(_gz){return E(_gx);};return [1,B(_fE(_gt,_gy))];},_gA=new T(function(){return B(unCStr("ENQ"));}),_gB=5,_gC=function(_gD){var _gE=new T(function(){return B(A(_gD,[_gB]));}),_gF=function(_gG){return E(_gE);};return [1,B(_fE(_gA,_gF))];},_gH=new T(function(){return B(unCStr("ACK"));}),_gI=6,_gJ=function(_gK){var _gL=new T(function(){return B(A(_gK,[_gI]));}),_gM=function(_gN){return E(_gL);};return [1,B(_fE(_gH,_gM))];},_gO=new T(function(){return B(unCStr("BEL"));}),_gP=7,_gQ=function(_gR){var _gS=new T(function(){return B(A(_gR,[_gP]));}),_gT=function(_gU){return E(_gS);};return [1,B(_fE(_gO,_gT))];},_gV=new T(function(){return B(unCStr("BS"));}),_gW=8,_gX=function(_gY){var _gZ=new T(function(){return B(A(_gY,[_gW]));}),_h0=function(_h1){return E(_gZ);};return [1,B(_fE(_gV,_h0))];},_h2=new T(function(){return B(unCStr("HT"));}),_h3=9,_h4=function(_h5){var _h6=new T(function(){return B(A(_h5,[_h3]));}),_h7=function(_h8){return E(_h6);};return [1,B(_fE(_h2,_h7))];},_h9=new T(function(){return B(unCStr("LF"));}),_ha=10,_hb=function(_hc){var _hd=new T(function(){return B(A(_hc,[_ha]));}),_he=function(_hf){return E(_hd);};return [1,B(_fE(_h9,_he))];},_hg=new T(function(){return B(unCStr("VT"));}),_hh=11,_hi=function(_hj){var _hk=new T(function(){return B(A(_hj,[_hh]));}),_hl=function(_hm){return E(_hk);};return [1,B(_fE(_hg,_hl))];},_hn=new T(function(){return B(unCStr("FF"));}),_ho=12,_hp=function(_hq){var _hr=new T(function(){return B(A(_hq,[_ho]));}),_hs=function(_ht){return E(_hr);};return [1,B(_fE(_hn,_hs))];},_hu=new T(function(){return B(unCStr("CR"));}),_hv=13,_hw=function(_hx){var _hy=new T(function(){return B(A(_hx,[_hv]));}),_hz=function(_hA){return E(_hy);};return [1,B(_fE(_hu,_hz))];},_hB=new T(function(){return B(unCStr("SI"));}),_hC=15,_hD=function(_hE){var _hF=new T(function(){return B(A(_hE,[_hC]));}),_hG=function(_hH){return E(_hF);};return [1,B(_fE(_hB,_hG))];},_hI=new T(function(){return B(unCStr("DLE"));}),_hJ=16,_hK=function(_hL){var _hM=new T(function(){return B(A(_hL,[_hJ]));}),_hN=function(_hO){return E(_hM);};return [1,B(_fE(_hI,_hN))];},_hP=new T(function(){return B(unCStr("DC1"));}),_hQ=17,_hR=function(_hS){var _hT=new T(function(){return B(A(_hS,[_hQ]));}),_hU=function(_hV){return E(_hT);};return [1,B(_fE(_hP,_hU))];},_hW=new T(function(){return B(unCStr("DC2"));}),_hX=18,_hY=function(_hZ){var _i0=new T(function(){return B(A(_hZ,[_hX]));}),_i1=function(_i2){return E(_i0);};return [1,B(_fE(_hW,_i1))];},_i3=new T(function(){return B(unCStr("DC3"));}),_i4=19,_i5=function(_i6){var _i7=new T(function(){return B(A(_i6,[_i4]));}),_i8=function(_i9){return E(_i7);};return [1,B(_fE(_i3,_i8))];},_ia=new T(function(){return B(unCStr("DC4"));}),_ib=20,_ic=function(_id){var _ie=new T(function(){return B(A(_id,[_ib]));}),_if=function(_ig){return E(_ie);};return [1,B(_fE(_ia,_if))];},_ih=new T(function(){return B(unCStr("NAK"));}),_ii=21,_ij=function(_ik){var _il=new T(function(){return B(A(_ik,[_ii]));}),_im=function(_in){return E(_il);};return [1,B(_fE(_ih,_im))];},_io=new T(function(){return B(unCStr("SYN"));}),_ip=22,_iq=function(_ir){var _is=new T(function(){return B(A(_ir,[_ip]));}),_it=function(_iu){return E(_is);};return [1,B(_fE(_io,_it))];},_iv=new T(function(){return B(unCStr("ETB"));}),_iw=23,_ix=function(_iy){var _iz=new T(function(){return B(A(_iy,[_iw]));}),_iA=function(_iB){return E(_iz);};return [1,B(_fE(_iv,_iA))];},_iC=new T(function(){return B(unCStr("CAN"));}),_iD=24,_iE=function(_iF){var _iG=new T(function(){return B(A(_iF,[_iD]));}),_iH=function(_iI){return E(_iG);};return [1,B(_fE(_iC,_iH))];},_iJ=new T(function(){return B(unCStr("EM"));}),_iK=25,_iL=function(_iM){var _iN=new T(function(){return B(A(_iM,[_iK]));}),_iO=function(_iP){return E(_iN);};return [1,B(_fE(_iJ,_iO))];},_iQ=new T(function(){return B(unCStr("SUB"));}),_iR=26,_iS=function(_iT){var _iU=new T(function(){return B(A(_iT,[_iR]));}),_iV=function(_iW){return E(_iU);};return [1,B(_fE(_iQ,_iV))];},_iX=new T(function(){return B(unCStr("ESC"));}),_iY=27,_iZ=function(_j0){var _j1=new T(function(){return B(A(_j0,[_iY]));}),_j2=function(_j3){return E(_j1);};return [1,B(_fE(_iX,_j2))];},_j4=new T(function(){return B(unCStr("FS"));}),_j5=28,_j6=function(_j7){var _j8=new T(function(){return B(A(_j7,[_j5]));}),_j9=function(_ja){return E(_j8);};return [1,B(_fE(_j4,_j9))];},_jb=new T(function(){return B(unCStr("GS"));}),_jc=29,_jd=function(_je){var _jf=new T(function(){return B(A(_je,[_jc]));}),_jg=function(_jh){return E(_jf);};return [1,B(_fE(_jb,_jg))];},_ji=new T(function(){return B(unCStr("RS"));}),_jj=30,_jk=function(_jl){var _jm=new T(function(){return B(A(_jl,[_jj]));}),_jn=function(_jo){return E(_jm);};return [1,B(_fE(_ji,_jn))];},_jp=new T(function(){return B(unCStr("US"));}),_jq=31,_jr=function(_js){var _jt=new T(function(){return B(A(_js,[_jq]));}),_ju=function(_jv){return E(_jt);};return [1,B(_fE(_jp,_ju))];},_jw=new T(function(){return B(unCStr("SP"));}),_jx=32,_jy=function(_jz){var _jA=new T(function(){return B(A(_jz,[_jx]));}),_jB=function(_jC){return E(_jA);};return [1,B(_fE(_jw,_jB))];},_jD=new T(function(){return B(unCStr("DEL"));}),_jE=127,_jF=function(_jG){var _jH=new T(function(){return B(A(_jG,[_jE]));}),_jI=function(_jJ){return E(_jH);};return [1,B(_fE(_jD,_jI))];},_jK=[1,_jF,_F],_jL=[1,_jy,_jK],_jM=[1,_jr,_jL],_jN=[1,_jk,_jM],_jO=[1,_jd,_jN],_jP=[1,_j6,_jO],_jQ=[1,_iZ,_jP],_jR=[1,_iS,_jQ],_jS=[1,_iL,_jR],_jT=[1,_iE,_jS],_jU=[1,_ix,_jT],_jV=[1,_iq,_jU],_jW=[1,_ij,_jV],_jX=[1,_ic,_jW],_jY=[1,_i5,_jX],_jZ=[1,_hY,_jY],_k0=[1,_hR,_jZ],_k1=[1,_hK,_k0],_k2=[1,_hD,_k1],_k3=[1,_hw,_k2],_k4=[1,_hp,_k3],_k5=[1,_hi,_k4],_k6=[1,_hb,_k5],_k7=[1,_h4,_k6],_k8=[1,_gX,_k7],_k9=[1,_gQ,_k8],_ka=[1,_gJ,_k9],_kb=[1,_gC,_ka],_kc=[1,_gv,_kb],_kd=[1,_go,_kc],_ke=[1,_gh,_kd],_kf=[1,_ga,_ke],_kg=[1,_g6,_kf],_kh=new T(function(){return B(_fv(_kg));}),_ki=34,_kj=[0,1114111],_kk=92,_kl=39,_km=function(_kn){var _ko=new T(function(){return B(A(_kn,[_gP]));}),_kp=new T(function(){return B(A(_kn,[_gW]));}),_kq=new T(function(){return B(A(_kn,[_h3]));}),_kr=new T(function(){return B(A(_kn,[_ha]));}),_ks=new T(function(){return B(A(_kn,[_hh]));}),_kt=new T(function(){return B(A(_kn,[_ho]));}),_ku=new T(function(){return B(A(_kn,[_hv]));}),_kv=new T(function(){return B(A(_kn,[_kk]));}),_kw=new T(function(){return B(A(_kn,[_kl]));}),_kx=new T(function(){return B(A(_kn,[_ki]));}),_ky=new T(function(){var _kz=function(_kA){var _kB=new T(function(){return B(_dD(E(_kA)));}),_kC=function(_kD){var _kE=B(_ef(_kB,_kD));if(!B(_fl(_kE,_kj))){return [2];}else{var _kF=new T(function(){var _kG=B(_fi(_kE));if(_kG>>>0>1114111){return B(_ff(_kG));}else{return _kG;}});return new F(function(){return A(_kn,[_kF]);});}};return [1,B(_bZ(_kA,_kC))];},_kH=new T(function(){var _kI=new T(function(){return B(A(_kn,[_jq]));}),_kJ=new T(function(){return B(A(_kn,[_jj]));}),_kK=new T(function(){return B(A(_kn,[_jc]));}),_kL=new T(function(){return B(A(_kn,[_j5]));}),_kM=new T(function(){return B(A(_kn,[_iY]));}),_kN=new T(function(){return B(A(_kn,[_iR]));}),_kO=new T(function(){return B(A(_kn,[_iK]));}),_kP=new T(function(){return B(A(_kn,[_iD]));}),_kQ=new T(function(){return B(A(_kn,[_iw]));}),_kR=new T(function(){return B(A(_kn,[_ip]));}),_kS=new T(function(){return B(A(_kn,[_ii]));}),_kT=new T(function(){return B(A(_kn,[_ib]));}),_kU=new T(function(){return B(A(_kn,[_i4]));}),_kV=new T(function(){return B(A(_kn,[_hX]));}),_kW=new T(function(){return B(A(_kn,[_hQ]));}),_kX=new T(function(){return B(A(_kn,[_hJ]));}),_kY=new T(function(){return B(A(_kn,[_hC]));}),_kZ=new T(function(){return B(A(_kn,[_fT]));}),_l0=new T(function(){return B(A(_kn,[_gI]));}),_l1=new T(function(){return B(A(_kn,[_gB]));}),_l2=new T(function(){return B(A(_kn,[_gu]));}),_l3=new T(function(){return B(A(_kn,[_gn]));}),_l4=new T(function(){return B(A(_kn,[_gg]));}),_l5=new T(function(){return B(A(_kn,[_g0]));}),_l6=new T(function(){return B(A(_kn,[_g9]));}),_l7=function(_l8){switch(E(_l8)){case 64:return E(_l6);case 65:return E(_l5);case 66:return E(_l4);case 67:return E(_l3);case 68:return E(_l2);case 69:return E(_l1);case 70:return E(_l0);case 71:return E(_ko);case 72:return E(_kp);case 73:return E(_kq);case 74:return E(_kr);case 75:return E(_ks);case 76:return E(_kt);case 77:return E(_ku);case 78:return E(_kZ);case 79:return E(_kY);case 80:return E(_kX);case 81:return E(_kW);case 82:return E(_kV);case 83:return E(_kU);case 84:return E(_kT);case 85:return E(_kS);case 86:return E(_kR);case 87:return E(_kQ);case 88:return E(_kP);case 89:return E(_kO);case 90:return E(_kN);case 91:return E(_kM);case 92:return E(_kL);case 93:return E(_kK);case 94:return E(_kJ);case 95:return E(_kI);default:return [2];}},_l9=[0,_l7],_la=new T(function(){return B(A(_kh,[_kn]));}),_lb=function(_lc){return (E(_lc)==94)?E(_l9):[2];};return B(_9H([0,_lb],_la));});return B(_9H([1,B(_bf(_fb,_fd,_kz))],_kH));}),_ld=function(_le){switch(E(_le)){case 34:return E(_kx);case 39:return E(_kw);case 92:return E(_kv);case 97:return E(_ko);case 98:return E(_kp);case 102:return E(_kt);case 110:return E(_kr);case 114:return E(_ku);case 116:return E(_kq);case 118:return E(_ks);default:return [2];}};return new F(function(){return _9H([0,_ld],_ky);});},_lf=function(_lg){return new F(function(){return A(_lg,[_6Q]);});},_lh=function(_li){var _lj=E(_li);if(!_lj[0]){return E(_lf);}else{var _lk=_lj[2],_ll=E(_lj[1]),_lm=_ll>>>0,_ln=new T(function(){return B(_lh(_lk));});if(_lm>887){var _lo=u_iswspace(_ll);if(!E(_lo)){return E(_lf);}else{var _lp=function(_lq){var _lr=new T(function(){return B(A(_ln,[_lq]));});return [0,function(_ls){return E(_lr);}];};return E(_lp);}}else{var _lt=E(_lm);if(_lt==32){var _lu=function(_lv){var _lw=new T(function(){return B(A(_ln,[_lv]));});return [0,function(_lx){return E(_lw);}];};return E(_lu);}else{if(_lt-9>>>0>4){if(E(_lt)==160){var _ly=function(_lz){var _lA=new T(function(){return B(A(_ln,[_lz]));});return [0,function(_lB){return E(_lA);}];};return E(_ly);}else{return E(_lf);}}else{var _lC=function(_lD){var _lE=new T(function(){return B(A(_ln,[_lD]));});return [0,function(_lF){return E(_lE);}];};return E(_lC);}}}}},_lG=function(_lH){var _lI=new T(function(){return B(_lG(_lH));}),_lJ=function(_lK){return (E(_lK)==92)?E(_lI):[2];},_lL=[0,_lJ],_lM=function(_lN){return E(_lL);},_lO=function(_lP){return new F(function(){return A(_lh,[_lP,_lM]);});},_lQ=[1,_lO],_lR=new T(function(){var _lS=function(_lT){return new F(function(){return A(_lH,[[0,_lT,_7U]]);});};return B(_km(_lS));}),_lU=function(_lV){var _lW=E(_lV);if(_lW==38){return E(_lI);}else{var _lX=_lW>>>0;if(_lX>887){var _lY=u_iswspace(_lW);return (E(_lY)==0)?[2]:E(_lQ);}else{var _lZ=E(_lX);return (_lZ==32)?E(_lQ):(_lZ-9>>>0>4)?(E(_lZ)==160)?E(_lQ):[2]:E(_lQ);}}},_m0=[0,_lU],_m1=function(_m2){var _m3=E(_m2);if(E(_m3)==92){return E(_lR);}else{return new F(function(){return A(_lH,[[0,_m3,_f5]]);});}},_m4=function(_m5){return (E(_m5)==92)?E(_m0):[2];};return new F(function(){return _9H([0,_m4],[0,_m1]);});},_m6=function(_m7,_m8){var _m9=new T(function(){var _ma=new T(function(){return B(A(_m7,[_F]));});return B(A(_m8,[[1,_ma]]));}),_mb=function(_mc){var _md=E(_mc),_me=E(_md[1]);if(E(_me)==34){if(!E(_md[2])){return E(_m9);}else{var _mf=function(_mg){return new F(function(){return A(_m7,[[1,_me,_mg]]);});};return new F(function(){return _m6(_mf,_m8);});}}else{var _mh=function(_mi){return new F(function(){return A(_m7,[[1,_me,_mi]]);});};return new F(function(){return _m6(_mh,_m8);});}};return new F(function(){return _lG(_mb);});},_mj=new T(function(){return B(unCStr("_\'"));}),_mk=function(_ml){var _mm=u_iswalnum(_ml);if(!E(_mm)){return new F(function(){return _eX(_aF,_ml,_mj);});}else{return true;}},_mn=function(_mo){return new F(function(){return _mk(E(_mo));});},_mp=new T(function(){return B(unCStr(",;()[]{}`"));}),_mq=new T(function(){return B(unCStr("=>"));}),_mr=[1,_mq,_F],_ms=new T(function(){return B(unCStr("~"));}),_mt=[1,_ms,_mr],_mu=new T(function(){return B(unCStr("@"));}),_mv=[1,_mu,_mt],_mw=new T(function(){return B(unCStr("->"));}),_mx=[1,_mw,_mv],_my=new T(function(){return B(unCStr("<-"));}),_mz=[1,_my,_mx],_mA=new T(function(){return B(unCStr("|"));}),_mB=[1,_mA,_mz],_mC=new T(function(){return B(unCStr("\\"));}),_mD=[1,_mC,_mB],_mE=new T(function(){return B(unCStr("="));}),_mF=[1,_mE,_mD],_mG=new T(function(){return B(unCStr("::"));}),_mH=[1,_mG,_mF],_mI=new T(function(){return B(unCStr(".."));}),_mJ=[1,_mI,_mH],_mK=function(_mL){var _mM=new T(function(){return B(A(_mL,[_bW]));}),_mN=new T(function(){var _mO=new T(function(){var _mP=function(_mQ){var _mR=new T(function(){return B(A(_mL,[[0,_mQ]]));});return [0,function(_mS){return (E(_mS)==39)?E(_mR):[2];}];};return B(_km(_mP));}),_mT=function(_mU){var _mV=E(_mU);switch(E(_mV)){case 39:return [2];case 92:return E(_mO);default:var _mW=new T(function(){return B(A(_mL,[[0,_mV]]));});return [0,function(_mX){return (E(_mX)==39)?E(_mW):[2];}];}},_mY=[0,_mT],_mZ=new T(function(){var _n0=new T(function(){return B(_m6(_2,_mL));}),_n1=new T(function(){var _n2=new T(function(){var _n3=new T(function(){var _n4=new T(function(){return [1,B(_bf(_da,_eT,_mL))];}),_n5=function(_n6){var _n7=E(_n6),_n8=u_iswalpha(_n7);if(!E(_n8)){if(E(_n7)==95){var _n9=function(_na){return new F(function(){return A(_mL,[[3,[1,_n7,_na]]]);});};return [1,B(_bG(_mn,_n9))];}else{return [2];}}else{var _nb=function(_nc){return new F(function(){return A(_mL,[[3,[1,_n7,_nc]]]);});};return [1,B(_bG(_mn,_nb))];}};return B(_9H([0,_n5],_n4));}),_nd=function(_ne){if(!B(_eX(_aF,_ne,_f2))){return [2];}else{var _nf=function(_ng){var _nh=[1,_ne,_ng];if(!B(_eX(_aO,_nh,_mJ))){return new F(function(){return A(_mL,[[4,_nh]]);});}else{return new F(function(){return A(_mL,[[2,_nh]]);});}};return [1,B(_bG(_f3,_nf))];}};return B(_9H([0,_nd],_n3));}),_ni=function(_nj){if(!B(_eX(_aF,_nj,_mp))){return [2];}else{return new F(function(){return A(_mL,[[2,[1,_nj,_F]]]);});}};return B(_9H([0,_ni],_n2));}),_nk=function(_nl){return (E(_nl)==34)?E(_n0):[2];};return B(_9H([0,_nk],_n1));}),_nm=function(_nn){return (E(_nn)==39)?E(_mY):[2];};return B(_9H([0,_nm],_mZ));}),_no=function(_np){return (E(_np)[0]==0)?E(_mM):[2];};return new F(function(){return _9H([1,_no],_mN);});},_nq=0,_nr=function(_ns,_nt){var _nu=new T(function(){var _nv=new T(function(){var _nw=function(_nx){var _ny=new T(function(){var _nz=new T(function(){return B(A(_nt,[_nx]));}),_nA=function(_nB){var _nC=E(_nB);return (_nC[0]==2)?(!B(_au(_nC[1],_at)))?[2]:E(_nz):[2];};return B(_mK(_nA));}),_nD=function(_nE){return E(_ny);};return [1,function(_nF){return new F(function(){return A(_lh,[_nF,_nD]);});}];};return B(A(_ns,[_nq,_nw]));}),_nG=function(_nH){var _nI=E(_nH);return (_nI[0]==2)?(!B(_au(_nI[1],_as)))?[2]:E(_nv):[2];};return B(_mK(_nG));}),_nJ=function(_nK){return E(_nu);};return function(_nL){return new F(function(){return A(_lh,[_nL,_nJ]);});};},_nM=function(_nN,_nO){var _nP=function(_nQ){var _nR=new T(function(){return B(A(_nN,[_nQ]));}),_nS=function(_nT){var _nU=new T(function(){return [1,B(_nr(_nP,_nT))];});return new F(function(){return _9H(B(A(_nR,[_nT])),_nU);});};return E(_nS);},_nV=new T(function(){return B(A(_nN,[_nO]));}),_nW=function(_nX){var _nY=new T(function(){return [1,B(_nr(_nP,_nX))];});return new F(function(){return _9H(B(A(_nV,[_nX])),_nY);});};return E(_nW);},_nZ=function(_o0,_o1){var _o2=function(_o3,_o4){var _o5=function(_o6){var _o7=new T(function(){return  -E(_o6);});return new F(function(){return A(_o4,[_o7]);});},_o8=function(_o9){return new F(function(){return A(_o0,[_o9,_o3,_o5]);});},_oa=new T(function(){return B(_mK(_o8));}),_ob=function(_oc){return E(_oa);},_od=function(_oe){return new F(function(){return A(_lh,[_oe,_ob]);});},_of=[1,_od],_og=function(_oh){var _oi=E(_oh);if(_oi[0]==4){var _oj=E(_oi[1]);if(!_oj[0]){return new F(function(){return A(_o0,[_oi,_o3,_o4]);});}else{if(E(_oj[1])==45){if(!E(_oj[2])[0]){return E(_of);}else{return new F(function(){return A(_o0,[_oi,_o3,_o4]);});}}else{return new F(function(){return A(_o0,[_oi,_o3,_o4]);});}}}else{return new F(function(){return A(_o0,[_oi,_o3,_o4]);});}},_ok=new T(function(){return B(_mK(_og));}),_ol=function(_om){return E(_ok);};return [1,function(_on){return new F(function(){return A(_lh,[_on,_ol]);});}];};return new F(function(){return _nM(_o2,_o1);});},_oo=function(_op){var _oq=E(_op);if(!_oq[0]){var _or=_oq[1],_os=_oq[2];return [1,new T(function(){var _ot=new T(function(){return B(_dy(_os,0));},1),_ou=new T(function(){return B(_dD(E(_or)));});return B(_dZ(_ou,_ot,B(_3v(_dF,_os))));})];}else{var _ov=_oq[1];if(!E(_oq[2])[0]){if(!E(_oq[3])[0]){return [1,new T(function(){return B(_ef(_dx,_ov));})];}else{return [0];}}else{return [0];}}},_ow=function(_ox,_oy){return [2];},_oz=function(_oA){var _oB=E(_oA);if(_oB[0]==5){var _oC=B(_oo(_oB[1]));if(!_oC[0]){return E(_ow);}else{var _oD=_oC[1],_oE=new T(function(){return B(_fi(_oD));}),_oF=function(_oG,_oH){return new F(function(){return A(_oH,[_oE]);});};return E(_oF);}}else{return E(_ow);}},_oI=new T(function(){return B(unCStr("="));}),_oJ=new T(function(){return B(unCStr("onPointIndex"));}),_oK=new T(function(){return B(unCStr(","));}),_oL=new T(function(){return B(unCStr("pointIndex"));}),_oM=new T(function(){return B(unCStr("{"));}),_oN=new T(function(){return B(unCStr("PointPlacement"));}),_oO=new T(function(){return B(unCStr("onBarIndex"));}),_oP=new T(function(){return B(unCStr("BarPlacement"));}),_oQ=new T(function(){return B(unCStr("onSideIndex"));}),_oR=new T(function(){return B(unCStr("LeftSidePlacement"));}),_oS=new T(function(){return B(unCStr("RightSidePlacement"));}),_oT=function(_oU,_oV){var _oW=new T(function(){var _oX=new T(function(){var _oY=new T(function(){if(_oU>11){return [2];}else{var _oZ=new T(function(){var _p0=new T(function(){var _p1=new T(function(){var _p2=new T(function(){var _p3=new T(function(){var _p4=function(_p5){var _p6=new T(function(){var _p7=new T(function(){return B(A(_oV,[[3,_p5]]));}),_p8=function(_p9){var _pa=E(_p9);return (_pa[0]==2)?(!B(_au(_pa[1],_78)))?[2]:E(_p7):[2];};return B(_mK(_p8));}),_pb=function(_pc){return E(_p6);};return [1,function(_pd){return new F(function(){return A(_lh,[_pd,_pb]);});}];};return B(A(_nZ,[_oz,_nq,_p4]));}),_pe=function(_pf){var _pg=E(_pf);return (_pg[0]==2)?(!B(_au(_pg[1],_oI)))?[2]:E(_p3):[2];};return B(_mK(_pe));}),_ph=function(_pi){return E(_p2);},_pj=function(_pk){return new F(function(){return A(_lh,[_pk,_ph]);});},_pl=[1,_pj],_pm=function(_pn){var _po=E(_pn);return (_po[0]==3)?(!B(_au(_po[1],_oQ)))?[2]:E(_pl):[2];};return B(_mK(_pm));}),_pp=function(_pq){return E(_p1);},_pr=function(_ps){return new F(function(){return A(_lh,[_ps,_pp]);});},_pt=[1,_pr],_pu=function(_pv){var _pw=E(_pv);return (_pw[0]==2)?(!B(_au(_pw[1],_oM)))?[2]:E(_pt):[2];};return B(_mK(_pu));}),_px=function(_py){return E(_p0);},_pz=function(_pA){return new F(function(){return A(_lh,[_pA,_px]);});},_pB=[1,_pz],_pC=function(_pD){var _pE=E(_pD);return (_pE[0]==3)?(!B(_au(_pE[1],_oS)))?[2]:E(_pB):[2];};return B(_mK(_pC));}),_pF=function(_pG){return E(_oZ);};return [1,function(_pH){return new F(function(){return A(_lh,[_pH,_pF]);});}];}});if(_oU>11){return B(_9H(_b6,_oY));}else{var _pI=new T(function(){var _pJ=new T(function(){var _pK=new T(function(){var _pL=new T(function(){var _pM=new T(function(){var _pN=function(_pO){var _pP=new T(function(){var _pQ=new T(function(){return B(A(_oV,[[2,_pO]]));}),_pR=function(_pS){var _pT=E(_pS);return (_pT[0]==2)?(!B(_au(_pT[1],_78)))?[2]:E(_pQ):[2];};return B(_mK(_pR));}),_pU=function(_pV){return E(_pP);};return [1,function(_pW){return new F(function(){return A(_lh,[_pW,_pU]);});}];};return B(A(_nZ,[_oz,_nq,_pN]));}),_pX=function(_pY){var _pZ=E(_pY);return (_pZ[0]==2)?(!B(_au(_pZ[1],_oI)))?[2]:E(_pM):[2];};return B(_mK(_pX));}),_q0=function(_q1){return E(_pL);},_q2=function(_q3){return new F(function(){return A(_lh,[_q3,_q0]);});},_q4=[1,_q2],_q5=function(_q6){var _q7=E(_q6);return (_q7[0]==3)?(!B(_au(_q7[1],_oQ)))?[2]:E(_q4):[2];};return B(_mK(_q5));}),_q8=function(_q9){return E(_pK);},_qa=function(_qb){return new F(function(){return A(_lh,[_qb,_q8]);});},_qc=[1,_qa],_qd=function(_qe){var _qf=E(_qe);return (_qf[0]==2)?(!B(_au(_qf[1],_oM)))?[2]:E(_qc):[2];};return B(_mK(_qd));}),_qg=function(_qh){return E(_pJ);},_qi=function(_qj){return new F(function(){return A(_lh,[_qj,_qg]);});},_qk=[1,_qi],_ql=function(_qm){var _qn=E(_qm);return (_qn[0]==3)?(!B(_au(_qn[1],_oR)))?[2]:E(_qk):[2];};return B(_mK(_ql));}),_qo=function(_qp){return E(_pI);},_qq=function(_qr){return new F(function(){return A(_lh,[_qr,_qo]);});};return B(_9H([1,_qq],_oY));}});if(_oU>11){return B(_9H(_b6,_oX));}else{var _qs=new T(function(){var _qt=new T(function(){var _qu=new T(function(){var _qv=new T(function(){var _qw=new T(function(){var _qx=function(_qy){var _qz=new T(function(){var _qA=new T(function(){return B(A(_oV,[[1,_qy]]));}),_qB=function(_qC){var _qD=E(_qC);return (_qD[0]==2)?(!B(_au(_qD[1],_78)))?[2]:E(_qA):[2];};return B(_mK(_qB));}),_qE=function(_qF){return E(_qz);};return [1,function(_qG){return new F(function(){return A(_lh,[_qG,_qE]);});}];};return B(A(_nZ,[_oz,_nq,_qx]));}),_qH=function(_qI){var _qJ=E(_qI);return (_qJ[0]==2)?(!B(_au(_qJ[1],_oI)))?[2]:E(_qw):[2];};return B(_mK(_qH));}),_qK=function(_qL){return E(_qv);},_qM=function(_qN){return new F(function(){return A(_lh,[_qN,_qK]);});},_qO=[1,_qM],_qP=function(_qQ){var _qR=E(_qQ);return (_qR[0]==3)?(!B(_au(_qR[1],_oO)))?[2]:E(_qO):[2];};return B(_mK(_qP));}),_qS=function(_qT){return E(_qu);},_qU=function(_qV){return new F(function(){return A(_lh,[_qV,_qS]);});},_qW=[1,_qU],_qX=function(_qY){var _qZ=E(_qY);return (_qZ[0]==2)?(!B(_au(_qZ[1],_oM)))?[2]:E(_qW):[2];};return B(_mK(_qX));}),_r0=function(_r1){return E(_qt);},_r2=function(_r3){return new F(function(){return A(_lh,[_r3,_r0]);});},_r4=[1,_r2],_r5=function(_r6){var _r7=E(_r6);return (_r7[0]==3)?(!B(_au(_r7[1],_oP)))?[2]:E(_r4):[2];};return B(_mK(_r5));}),_r8=function(_r9){return E(_qs);},_ra=function(_rb){return new F(function(){return A(_lh,[_rb,_r8]);});};return B(_9H([1,_ra],_oX));}});if(_oU>11){return new F(function(){return _9H(_b6,_oW);});}else{var _rc=new T(function(){var _rd=new T(function(){var _re=new T(function(){var _rf=new T(function(){var _rg=new T(function(){var _rh=function(_ri){var _rj=new T(function(){var _rk=new T(function(){var _rl=new T(function(){var _rm=new T(function(){var _rn=function(_ro){var _rp=new T(function(){var _rq=new T(function(){return B(A(_oV,[[0,_ri,_ro]]));}),_rr=function(_rs){var _rt=E(_rs);return (_rt[0]==2)?(!B(_au(_rt[1],_78)))?[2]:E(_rq):[2];};return B(_mK(_rr));}),_ru=function(_rv){return E(_rp);};return [1,function(_rw){return new F(function(){return A(_lh,[_rw,_ru]);});}];};return B(A(_nZ,[_oz,_nq,_rn]));}),_rx=function(_ry){var _rz=E(_ry);return (_rz[0]==2)?(!B(_au(_rz[1],_oI)))?[2]:E(_rm):[2];};return B(_mK(_rx));}),_rA=function(_rB){return E(_rl);},_rC=function(_rD){return new F(function(){return A(_lh,[_rD,_rA]);});},_rE=[1,_rC],_rF=function(_rG){var _rH=E(_rG);return (_rH[0]==3)?(!B(_au(_rH[1],_oJ)))?[2]:E(_rE):[2];};return B(_mK(_rF));}),_rI=function(_rJ){return E(_rk);},_rK=function(_rL){return new F(function(){return A(_lh,[_rL,_rI]);});},_rM=[1,_rK],_rN=function(_rO){var _rP=E(_rO);return (_rP[0]==2)?(!B(_au(_rP[1],_oK)))?[2]:E(_rM):[2];};return B(_mK(_rN));}),_rQ=function(_rR){return E(_rj);};return [1,function(_rS){return new F(function(){return A(_lh,[_rS,_rQ]);});}];};return B(A(_nZ,[_oz,_nq,_rh]));}),_rT=function(_rU){var _rV=E(_rU);return (_rV[0]==2)?(!B(_au(_rV[1],_oI)))?[2]:E(_rg):[2];};return B(_mK(_rT));}),_rW=function(_rX){return E(_rf);},_rY=function(_rZ){return new F(function(){return A(_lh,[_rZ,_rW]);});},_s0=[1,_rY],_s1=function(_s2){var _s3=E(_s2);return (_s3[0]==3)?(!B(_au(_s3[1],_oL)))?[2]:E(_s0):[2];};return B(_mK(_s1));}),_s4=function(_s5){return E(_re);},_s6=function(_s7){return new F(function(){return A(_lh,[_s7,_s4]);});},_s8=[1,_s6],_s9=function(_sa){var _sb=E(_sa);return (_sb[0]==2)?(!B(_au(_sb[1],_oM)))?[2]:E(_s8):[2];};return B(_mK(_s9));}),_sc=function(_sd){return E(_rd);},_se=function(_sf){return new F(function(){return A(_lh,[_sf,_sc]);});},_sg=[1,_se],_sh=function(_si){var _sj=E(_si);return (_sj[0]==3)?(!B(_au(_sj[1],_oN)))?[2]:E(_sg):[2];};return B(_mK(_sh));}),_sk=function(_sl){return E(_rc);},_sm=function(_sn){return new F(function(){return A(_lh,[_sn,_sk]);});};return new F(function(){return _9H([1,_sm],_oW);});}},_so=function(_sp,_sq){return new F(function(){return _oT(E(_sp),_sq);});},_sr=function(_ss){var _st=[3,_ss,_b6],_su=function(_sv){return E(_st);};return [1,function(_sw){return new F(function(){return A(_lh,[_sw,_su]);});}];},_sx=new T(function(){return B(A(_nM,[_so,_nq,_sr]));}),_sy=function(_sz,_sA){if(_sz<=0){if(_sz>=0){return new F(function(){return quot(_sz,_sA);});}else{if(_sA<=0){return new F(function(){return quot(_sz,_sA);});}else{return quot(_sz+1|0,_sA)-1|0;}}}else{if(_sA>=0){if(_sz>=0){return new F(function(){return quot(_sz,_sA);});}else{if(_sA<=0){return new F(function(){return quot(_sz,_sA);});}else{return quot(_sz+1|0,_sA)-1|0;}}}else{return quot(_sz-1|0,_sA)-1|0;}}},_sB=new T(function(){return B(_sy(210,2));}),_sC=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:242:9-15"));}),_sD=[0,_2z,_2A,_F,_sC,_2z,_2z],_sE=new T(function(){return B(_2x(_sD));}),_sF=new T(function(){return B(unCStr("joinGame"));}),_sG=function(_sH){var _sI=E(_sH);return (E(_sI)==95)?32:E(_sI);},_sJ=function(_sK){return E(E(_sK)[1]);},_sL=function(_sM){return E(E(_sM)[1]);},_sN=function(_sO){return E(E(_sO)[2]);},_sP=function(_sQ){return E(E(_sQ)[2]);},_sR=function(_sS){return E(E(_sS)[1]);},_sT=function(_){return new F(function(){return nMV(_2z);});},_sU=new T(function(){return B(_6e(_sT));}),_sV=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_sW=function(_sX){return E(E(_sX)[2]);},_sY=function(_sZ){return E(E(_sZ)[4]);},_t0=function(_t1,_t2,_t3,_t4,_t5,_t6){var _t7=B(_sJ(_t1)),_t8=B(_sL(_t7)),_t9=new T(function(){return B(_85(_t7));}),_ta=new T(function(){return B(_sY(_t8));}),_tb=new T(function(){return B(A(_83,[_t2,_t4]));}),_tc=new T(function(){return B(A(_sR,[_t3,_t5]));}),_td=function(_te){return new F(function(){return A(_ta,[[0,_tc,_tb,_te]]);});},_tf=function(_tg){var _th=new T(function(){var _ti=new T(function(){var _tj=E(_tb),_tk=E(_tc),_tl=E(_tg),_tm=function(_tn,_){var _to=B(A(_tl,[_tn,_]));return _6i;},_tp=__createJSFunc(2,E(_tm)),_tq=_tp,_tr=function(_){return new F(function(){return E(_sV)(_tj,_tk,_tq);});};return E(_tr);});return B(A(_t9,[_ti]));});return new F(function(){return A(_sN,[_t8,_th,_td]);});},_ts=new T(function(){var _tt=new T(function(){return B(_85(_t7));}),_tu=function(_tv){var _tw=new T(function(){var _tx=function(_){var _=wMV(E(_sU),[1,_tv]);return new F(function(){return A(_sP,[_t3,_t5,_tv,_]);});};return B(A(_tt,[_tx]));});return new F(function(){return A(_sN,[_t8,_tw,_t6]);});};return B(A(_sW,[_t1,_tu]));});return new F(function(){return A(_sN,[_t8,_ts,_tf]);});},_ty=function(_tz,_tA){var _tB=E(_tA);if(!_tB[0]){return [0];}else{var _tC=_tB[1],_tD=_tB[2],_tE=E(_tz);if(_tE==1){return [1,_tC,_F];}else{var _tF=new T(function(){return B(_ty(_tE-1|0,_tD));});return [1,_tC,_tF];}}},_tG=function(_tH,_tI,_tJ){if(_tJ<=_tI){var _tK=new T(function(){var _tL=_tI-_tH|0,_tM=_tJ-_tL|0,_tN=function(_tO){if(_tO>=_tM){var _tP=new T(function(){return B(_tN(_tO+_tL|0));});return [1,_tO,_tP];}else{return [1,_tO,_F];}};return B(_tN(_tI));});return [1,_tH,_tK];}else{return (_tJ<=_tH)?[1,_tH,_F]:[0];}},_tQ=function(_tR,_tS,_tT){if(_tT>=_tS){var _tU=new T(function(){var _tV=_tS-_tR|0,_tW=_tT-_tV|0,_tX=function(_tY){if(_tY<=_tW){var _tZ=new T(function(){return B(_tX(_tY+_tV|0));});return [1,_tY,_tZ];}else{return [1,_tY,_F];}};return B(_tX(_tS));});return [1,_tR,_tU];}else{return (_tT>=_tR)?[1,_tR,_F]:[0];}},_u0=function(_u1,_u2){if(_u2<_u1){return new F(function(){return _tG(_u1,_u2,-2147483648);});}else{return new F(function(){return _tQ(_u1,_u2,2147483647);});}},_u3=new T(function(){return B(_u0(135,150));}),_u4=new T(function(){return B(_ty(6,_u3));}),_u5=function(_u6,_u7){var _u8=E(_u6);if(!_u8[0]){return E(_u4);}else{var _u9=_u8[1],_ua=_u8[2],_ub=E(_u7);if(_ub==1){return [1,_u9,_u4];}else{var _uc=new T(function(){return B(_u5(_ua,_ub-1|0));});return [1,_u9,_uc];}}},_ud=new T(function(){return B(_u0(25,40));}),_ue=new T(function(){return B(_u5(_ud,6));}),_uf=function(_ug){while(1){var _uh=(function(_ui){var _uj=E(_ui);if(!_uj[0]){return [0];}else{var _uk=_uj[2],_ul=E(_uj[1]);if(!E(_ul[2])[0]){var _um=new T(function(){return B(_uf(_uk));});return [1,_ul[1],_um];}else{_ug=_uk;return null;}}})(_ug);if(_uh!=null){return _uh;}}},_un=function(_uo,_up){var _uq=E(_up);if(!_uq[0]){return [0,_F,_F];}else{var _ur=_uq[1],_us=_uq[2];if(!B(A(_uo,[_ur]))){var _ut=new T(function(){var _uu=B(_un(_uo,_us));return [0,_uu[1],_uu[2]];}),_uv=new T(function(){return E(E(_ut)[2]);}),_uw=new T(function(){return E(E(_ut)[1]);});return [0,[1,_ur,_uw],_uv];}else{return [0,_F,_uq];}}},_ux=function(_uy,_uz){while(1){var _uA=E(_uz);if(!_uA[0]){return [0];}else{if(!B(A(_uy,[_uA[1]]))){return E(_uA);}else{_uz=_uA[2];continue;}}}},_uB=function(_uC){var _uD=_uC>>>0;if(_uD>887){var _uE=u_iswspace(_uC);return (E(_uE)==0)?false:true;}else{var _uF=E(_uD);return (_uF==32)?true:(_uF-9>>>0>4)?(E(_uF)==160)?true:false:true;}},_uG=function(_uH){return new F(function(){return _uB(E(_uH));});},_uI=function(_uJ){var _uK=B(_ux(_uG,_uJ));if(!_uK[0]){return [0];}else{var _uL=new T(function(){var _uM=B(_un(_uG,_uK));return [0,_uM[1],_uM[2]];}),_uN=new T(function(){return B(_uI(E(_uL)[2]));}),_uO=new T(function(){return E(E(_uL)[1]);});return [1,_uO,_uN];}},_uP=function(_uQ,_){var _uR=jsFind(toJSStr(E(_sF)));if(!_uR[0]){return new F(function(){return die(_sE);});}else{var _uS=B(A(_t0,[_6S,_4,_6P,_uR[1],_8S,_92,_])),_uT=function(_uU){var _uV=new T(function(){var _uW=new T(function(){var _uX=String(E(_uU));return B(_3v(_sG,B(_75(B(_uI(fromJSStr(_uX))),2))));});return B(_uf(B(_9v(_sx,_uW))));}),_uY=function(_uZ){var _v0=new T(function(){var _v1=new T(function(){var _v2=B(A(_uZ,[_]));return E(_v2);}),_v3=function(_v4){var _v5=E(_v4)-E(_v1);return (_v5==0)?true:(_v5<=0)? -_v5<7:_v5<7;};return B(_9b(_v3,_ue));}),_v6=function(_v7,_){var _v8=E(_uV);if(!_v8[0]){return E(_9r);}else{if(!E(_v8[2])[0]){var _v9=E(_v8[1]);if(!_v9[0]){var _va=_v9[1],_vb=_v9[2],_vc=E(_uQ),_vd=_vc[1],_ve=_vc[2],_vf=_vc[3],_vg=_vc[4],_vh=_vc[5],_vi=_vc[6],_vj=_vc[7],_vk=E(_v0);if(!_vk[0]){var _vl=B(_8y(_vd,_v9,_v9,_));return _6i;}else{var _vm=_vk[1],_vn=B(A(_v7,[_])),_vo=function(_vp,_vq){var _vr=E(_va),_vs=_vr;if(_vp<=_vs){return new F(function(){return _8y(_vd,_v9,_v9,_);});}else{var _vt=B(_75(_vd,_vp)),_vu=_vt[2],_vv=function(_){var _vw=B(_8y(_vd,_v9,[0,_vq,_vu],_)),_vx=new T(function(){return E(B(_75(_vd,_vs))[1]);}),_vy=function(_vz,_vA){var _vB=E(_vz);if(!_vB[0]){return [0];}else{var _vC=_vB[1],_vD=_vB[2],_vE=E(_vA);if(!_vE[0]){return [0];}else{var _vF=_vE[1],_vG=_vE[2],_vH=new T(function(){return B(_vy(_vD,_vG));}),_vI=new T(function(){var _vJ=E(_vC);if(_vJ!=_vs){if(_vJ!=_vp){return E(_vF);}else{var _vK=new T(function(){return E(E(_vF)[2])+1|0;});return [0,_vx,_vK];}}else{var _vL=new T(function(){return E(E(_vF)[2])-1|0;}),_vM=new T(function(){return E(E(_vF)[1]);});return [0,_vM,_vL];}});return [1,_vI,_vH];}}},_vN=B(_vy(_9p,_vd)),_vO=function(_vP,_){while(1){var _vQ=(function(_vR,_){var _vS=E(_vR);if(!_vS[0]){return _6Q;}else{var _vT=_vS[1],_vU=new T(function(){return E(_vT)-1|0;}),_vV=B(_8y(_vN,[0,_vr,_vT],[0,_vr,_vU],_));_vP=_vS[2];return null;}})(_vP,_);if(_vQ!=null){return _vQ;}}},_vW=function(_vX,_vY){while(1){var _vZ=E(_vY);if(!_vZ[0]){return [0];}else{var _w0=_vZ[2],_w1=E(_vX);if(_w1==1){return E(_w0);}else{_vX=_w1-1|0;_vY=_w0;continue;}}}},_w2=B(_vO(B(_vW(1,B(_94(E(_vb),E(B(_75(_vN,_vs))[2]))))),_));return new F(function(){return _uP([0,_vN,_ve,_vf,_vg,_vh,_vi,_vj],_);});},_w3=function(_){if(E(_vu)>=2){return new F(function(){return _8y(_vd,_v9,_v9,_);});}else{return new F(function(){return _vv(_);});}};if(!E(_vt[1])){if(!E(B(_75(_vd,_vs))[1])){return new F(function(){return _vv(_);});}else{return new F(function(){return _w3(_);});}}else{if(!E(B(_75(_vd,_vs))[1])){return new F(function(){return _w3(_);});}else{return new F(function(){return _vv(_);});}}}};if(E(_vn)<=E(_sB)){var _w4=E(_vm),_w5=B(_vo(_w4,_w4));return _6i;}else{var _w6=23-E(_vm)|0,_w7=B(_vo(_w6,_w6));return _6i;}}}else{var _w8=B(_8y(E(_uQ)[1],_v9,_v9,_));return _6i;}}else{return E(_9t);}}};return E(_v6);};return E(_uY);},_w9=__createJSFunc(4,E(_uT)),_wa=E(_9a)(_w9);return new F(function(){return _6R(_);});}},_wb=function(_){return _6Q;},_wc=new T(function(){return (function (ns,tag) {return document.createElementNS(ns, tag);});}),_wd=new T(function(){return B(unCStr("cy"));}),_we=new T(function(){return B(unCStr("cx"));}),_wf=new T(function(){return B(unCStr("r"));}),_wg=new T(function(){return B(_5j(0,6,_F));}),_wh=new T(function(){return B(unCStr("circle"));}),_wi=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_wj=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:152:5-10"));}),_wk=[0,_2z,_2A,_F,_wj,_2z,_2z],_wl=new T(function(){return B(_2x(_wk));}),_wm=new T(function(){return B(unCStr("board"));}),_wn=function(_wo,_wp,_){while(1){var _wq=(function(_wr,_ws,_){var _wt=E(_ws);if(!_wt[0]){return _6Q;}else{var _wu=_wt[2],_wv=E(_wt[1]),_ww=_wv[1],_wx=E(_wv[2]);if(0>=_wx){var _wy=E(_wr);if(_wy==2147483647){return _6Q;}else{_wo=_wy+1|0;_wp=_wu;return null;}}else{var _wz=_wr,_wA=new T(function(){if(!E(_ww)){return false;}else{return true;}}),_wB=function(_wC,_wD,_){var _wE=jsFind(toJSStr(E(_wm)));if(!_wE[0]){return new F(function(){return die(_wl);});}else{var _wF=E(_wc)(toJSStr(_wi),toJSStr(_wh)),_wG=B(A(_87,[_4,_2I,_wF,_wf,_wg,_])),_wH=new T(function(){if(_wr>=12){var _wI=23-_wr|0;if(_wI>=6){return B(_5j(0,25+(20+(imul(_wI,15)|0)|0)|0,_F));}else{return B(_5j(0,25+(imul(_wI,15)|0)|0,_F));}}else{if(_wr>=6){return B(_5j(0,25+(20+(imul(_wr,15)|0)|0)|0,_F));}else{return B(_5j(0,25+(imul(_wr,15)|0)|0,_F));}}}),_wJ=B(A(_87,[_4,_2I,_wF,_we,_wH,_])),_wK=new T(function(){if(_wr>=12){return B(_5j(0,203+(imul(imul(imul(-1,E(_wC))|0,2)|0,6)|0)|0,_F));}else{return B(_5j(0,7+(imul(imul(E(_wC),2)|0,6)|0)|0,_F));}}),_wL=B(A(_87,[_4,_2I,_wF,_wd,_wK,_])),_wM=B(_8f(_wF,_ww,_wA,[0,_wz,_wC],_)),_wN=jsAppendChild(_wF,E(_wE[1]));return new F(function(){return A(_wD,[_]);});}},_wO=function(_wP,_wQ,_){var _wR=E(_wP);if(!_wR[0]){return _6Q;}else{var _wS=_wR[1],_wT=_wR[2],_wU=E(_wQ);if(_wU==1){return new F(function(){return _wB(_wS,_wb,_);});}else{var _wV=function(_){return new F(function(){return _wO(_wT,_wU-1|0,_);});};return new F(function(){return _wB(_wS,_wV,_);});}}},_wW=B(_wO(_9p,_wx,_)),_wX=E(_wr);if(_wX==2147483647){return _6Q;}else{_wo=_wX+1|0;_wp=_wu;return null;}}}})(_wo,_wp,_);if(_wq!=null){return _wq;}}},_wY=new T(function(){return B(unCStr("You have not joined a game (yet)."));}),_wZ=new T(function(){return B(unCStr("innerHTML"));}),_x0=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:262:9-15"));}),_x1=[0,_2z,_2A,_F,_x0,_2z,_2z],_x2=new T(function(){return B(_2x(_x1));}),_x3=function(_x4,_x5,_x6,_x7,_x8){var _x9=function(_){var _xa=jsSet(B(A(_83,[_x4,_x6])),toJSStr(E(_x7)),toJSStr(E(_x8)));return _6Q;};return new F(function(){return A(_85,[_x5,_x9]);});},_xb=function(_){var _xc=jsFind("HintText");if(!_xc[0]){return new F(function(){return die(_x2);});}else{var _xd=B(A(_x3,[_4,_2I,_xc[1],_wZ,_wY,_])),_xe=B(_wn(0,_4Y,_));return new F(function(){return _uP(_59,_);});}},_xf=function(_){return new F(function(){return _xb(_);});};
var hasteMain = function() {B(A(_xf, [0]));};window.onload = hasteMain;