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

var _0=function(_1,_){return [1,_1];},_2=function(_3){return E(_3);},_4=[0,_2,_0],_5=function(_6,_7,_){var _8=B(A(_6,[_])),_9=B(A(_7,[_]));return _8;},_a=function(_b,_c,_){var _d=B(A(_b,[_])),_e=_d,_f=B(A(_c,[_])),_g=_f;return new T(function(){return B(A(_e,[_g]));});},_h=function(_i,_j,_){var _k=B(A(_j,[_]));return _i;},_l=function(_m,_n,_){var _o=B(A(_n,[_])),_p=_o;return new T(function(){return B(A(_m,[_p]));});},_q=[0,_l,_h],_r=function(_s,_){return _s;},_t=function(_u,_v,_){var _w=B(A(_u,[_]));return new F(function(){return A(_v,[_]);});},_x=[0,_q,_r,_a,_t,_5],_y=function(_z,_A,_){var _B=B(A(_z,[_]));return new F(function(){return A(_A,[_B,_]);});},_C=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_D=new T(function(){return B(unCStr("base"));}),_E=new T(function(){return B(unCStr("IOException"));}),_F=[0],_G=new T(function(){var _H=hs_wordToWord64(4053623282),_I=hs_wordToWord64(3693590983);return [0,_H,_I,[0,_H,_I,_D,_C,_E],_F,_F];}),_J=function(_K){return E(_G);},_L=function(_M){return E(E(_M)[1]);},_N=function(_O,_P,_Q){var _R=B(A(_O,[_])),_S=B(A(_P,[_])),_T=hs_eqWord64(_R[1],_S[1]);if(!_T){return [0];}else{var _U=hs_eqWord64(_R[2],_S[2]);return (!_U)?[0]:[1,_Q];}},_V=function(_W){var _X=E(_W);return new F(function(){return _N(B(_L(_X[1])),_J,_X[2]);});},_Y=new T(function(){return B(unCStr(": "));}),_Z=new T(function(){return B(unCStr(")"));}),_10=new T(function(){return B(unCStr(" ("));}),_11=function(_12,_13){var _14=E(_12);if(!_14[0]){return E(_13);}else{var _15=_14[2],_16=new T(function(){return B(_11(_15,_13));});return [1,_14[1],_16];}},_17=new T(function(){return B(unCStr("interrupted"));}),_18=new T(function(){return B(unCStr("system error"));}),_19=new T(function(){return B(unCStr("unsatisified constraints"));}),_1a=new T(function(){return B(unCStr("user error"));}),_1b=new T(function(){return B(unCStr("permission denied"));}),_1c=new T(function(){return B(unCStr("illegal operation"));}),_1d=new T(function(){return B(unCStr("end of file"));}),_1e=new T(function(){return B(unCStr("resource exhausted"));}),_1f=new T(function(){return B(unCStr("resource busy"));}),_1g=new T(function(){return B(unCStr("does not exist"));}),_1h=new T(function(){return B(unCStr("already exists"));}),_1i=new T(function(){return B(unCStr("resource vanished"));}),_1j=new T(function(){return B(unCStr("timeout"));}),_1k=new T(function(){return B(unCStr("unsupported operation"));}),_1l=new T(function(){return B(unCStr("hardware fault"));}),_1m=new T(function(){return B(unCStr("inappropriate type"));}),_1n=new T(function(){return B(unCStr("invalid argument"));}),_1o=new T(function(){return B(unCStr("failed"));}),_1p=new T(function(){return B(unCStr("protocol error"));}),_1q=function(_1r,_1s){switch(E(_1r)){case 0:return new F(function(){return _11(_1h,_1s);});break;case 1:return new F(function(){return _11(_1g,_1s);});break;case 2:return new F(function(){return _11(_1f,_1s);});break;case 3:return new F(function(){return _11(_1e,_1s);});break;case 4:return new F(function(){return _11(_1d,_1s);});break;case 5:return new F(function(){return _11(_1c,_1s);});break;case 6:return new F(function(){return _11(_1b,_1s);});break;case 7:return new F(function(){return _11(_1a,_1s);});break;case 8:return new F(function(){return _11(_19,_1s);});break;case 9:return new F(function(){return _11(_18,_1s);});break;case 10:return new F(function(){return _11(_1p,_1s);});break;case 11:return new F(function(){return _11(_1o,_1s);});break;case 12:return new F(function(){return _11(_1n,_1s);});break;case 13:return new F(function(){return _11(_1m,_1s);});break;case 14:return new F(function(){return _11(_1l,_1s);});break;case 15:return new F(function(){return _11(_1k,_1s);});break;case 16:return new F(function(){return _11(_1j,_1s);});break;case 17:return new F(function(){return _11(_1i,_1s);});break;default:return new F(function(){return _11(_17,_1s);});}},_1t=new T(function(){return B(unCStr("}"));}),_1u=new T(function(){return B(unCStr("{handle: "));}),_1v=function(_1w,_1x,_1y,_1z,_1A,_1B){var _1C=new T(function(){var _1D=new T(function(){var _1E=new T(function(){var _1F=E(_1z);if(!_1F[0]){return E(_1B);}else{var _1G=new T(function(){var _1H=new T(function(){return B(_11(_Z,_1B));},1);return B(_11(_1F,_1H));},1);return B(_11(_10,_1G));}},1);return B(_1q(_1x,_1E));}),_1I=E(_1y);if(!_1I[0]){return E(_1D);}else{var _1J=new T(function(){return B(_11(_Y,_1D));},1);return B(_11(_1I,_1J));}}),_1K=E(_1A);if(!_1K[0]){var _1L=E(_1w);if(!_1L[0]){return E(_1C);}else{var _1M=E(_1L[1]);if(!_1M[0]){var _1N=_1M[1],_1O=new T(function(){var _1P=new T(function(){var _1Q=new T(function(){return B(_11(_Y,_1C));},1);return B(_11(_1t,_1Q));},1);return B(_11(_1N,_1P));},1);return new F(function(){return _11(_1u,_1O);});}else{var _1R=_1M[1],_1S=new T(function(){var _1T=new T(function(){var _1U=new T(function(){return B(_11(_Y,_1C));},1);return B(_11(_1t,_1U));},1);return B(_11(_1R,_1T));},1);return new F(function(){return _11(_1u,_1S);});}}}else{var _1V=new T(function(){return B(_11(_Y,_1C));},1);return new F(function(){return _11(_1K[1],_1V);});}},_1W=function(_1X){var _1Y=E(_1X);return new F(function(){return _1v(_1Y[1],_1Y[2],_1Y[3],_1Y[4],_1Y[6],_F);});},_1Z=function(_20,_21,_22){var _23=E(_21);return new F(function(){return _1v(_23[1],_23[2],_23[3],_23[4],_23[6],_22);});},_24=function(_25,_26){var _27=E(_25);return new F(function(){return _1v(_27[1],_27[2],_27[3],_27[4],_27[6],_26);});},_28=44,_29=93,_2a=91,_2b=function(_2c,_2d,_2e){var _2f=E(_2d);if(!_2f[0]){return new F(function(){return unAppCStr("[]",_2e);});}else{var _2g=_2f[1],_2h=_2f[2],_2i=new T(function(){var _2j=new T(function(){var _2k=[1,_29,_2e],_2l=function(_2m){var _2n=E(_2m);if(!_2n[0]){return E(_2k);}else{var _2o=_2n[1],_2p=_2n[2],_2q=new T(function(){var _2r=new T(function(){return B(_2l(_2p));});return B(A(_2c,[_2o,_2r]));});return [1,_28,_2q];}};return B(_2l(_2h));});return B(A(_2c,[_2g,_2j]));});return [1,_2a,_2i];}},_2s=function(_2t,_2u){return new F(function(){return _2b(_24,_2t,_2u);});},_2v=[0,_1Z,_1W,_2s],_2w=new T(function(){return [0,_J,_2v,_2x,_V,_1W];}),_2x=function(_2y){return [0,_2w,_2y];},_2z=[0],_2A=7,_2B=function(_2C){return [0,_2z,_2A,_F,_2C,_2z,_2z];},_2D=function(_2E,_){var _2F=new T(function(){var _2G=new T(function(){return B(_2B(_2E));});return B(_2x(_2G));});return new F(function(){return die(_2F);});},_2H=[0,_x,_y,_t,_r,_2D],_2I=[0,_2H,_2],_2J=function(_2K,_2L){if(_2K<=0){if(_2K>=0){return new F(function(){return quot(_2K,_2L);});}else{if(_2L<=0){return new F(function(){return quot(_2K,_2L);});}else{return quot(_2K+1|0,_2L)-1|0;}}}else{if(_2L>=0){if(_2K>=0){return new F(function(){return quot(_2K,_2L);});}else{if(_2L<=0){return new F(function(){return quot(_2K,_2L);});}else{return quot(_2K+1|0,_2L)-1|0;}}}else{return quot(_2K-1|0,_2L)-1|0;}}},_2M=new T(function(){return B(_2J(15,2));}),_2N=new T(function(){return 220+B(_2J(15,2))|0;}),_2O=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2P=new T(function(){return B(unCStr("base"));}),_2Q=new T(function(){return B(unCStr("PatternMatchFail"));}),_2R=new T(function(){var _2S=hs_wordToWord64(18445595),_2T=hs_wordToWord64(52003073);return [0,_2S,_2T,[0,_2S,_2T,_2P,_2O,_2Q],_F,_F];}),_2U=function(_2V){return E(_2R);},_2W=function(_2X){var _2Y=E(_2X);return new F(function(){return _N(B(_L(_2Y[1])),_2U,_2Y[2]);});},_2Z=function(_30){return E(E(_30)[1]);},_31=function(_32){return [0,_33,_32];},_34=function(_35,_36){return new F(function(){return _11(E(_35)[1],_36);});},_37=function(_38,_39){return new F(function(){return _2b(_34,_38,_39);});},_3a=function(_3b,_3c,_3d){return new F(function(){return _11(E(_3c)[1],_3d);});},_3e=[0,_3a,_2Z,_37],_33=new T(function(){return [0,_2U,_3e,_31,_2W,_2Z];}),_3f=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_3g=function(_3h){return E(E(_3h)[3]);},_3i=function(_3j,_3k){var _3l=new T(function(){return B(A(_3g,[_3k,_3j]));});return new F(function(){return die(_3l);});},_3m=function(_3n,_3o){return new F(function(){return _3i(_3n,_3o);});},_3p=function(_3q,_3r){var _3s=E(_3r);if(!_3s[0]){return [0,_F,_F];}else{var _3t=_3s[1],_3u=_3s[2];if(!B(A(_3q,[_3t]))){return [0,_F,_3s];}else{var _3v=new T(function(){var _3w=B(_3p(_3q,_3u));return [0,_3w[1],_3w[2]];}),_3x=new T(function(){return E(E(_3v)[2]);}),_3y=new T(function(){return E(E(_3v)[1]);});return [0,[1,_3t,_3y],_3x];}}},_3z=32,_3A=new T(function(){return B(unCStr("\n"));}),_3B=function(_3C){return (E(_3C)==124)?false:true;},_3D=function(_3E,_3F){var _3G=B(_3p(_3B,B(unCStr(_3E)))),_3H=_3G[1],_3I=function(_3J,_3K){var _3L=new T(function(){var _3M=new T(function(){var _3N=new T(function(){return B(_11(_3K,_3A));},1);return B(_11(_3F,_3N));});return B(unAppCStr(": ",_3M));},1);return new F(function(){return _11(_3J,_3L);});},_3O=E(_3G[2]);if(!_3O[0]){return new F(function(){return _3I(_3H,_F);});}else{if(E(_3O[1])==124){return new F(function(){return _3I(_3H,[1,_3z,_3O[2]]);});}else{return new F(function(){return _3I(_3H,_F);});}}},_3P=function(_3Q){var _3R=new T(function(){return B(_3D(_3Q,_3f));});return new F(function(){return _3m([0,_3R],_33);});},_3S=new T(function(){return B(_3P("main.hs:(95,1)-(122,116)|function checkerPosition"));}),_3T=function(_3U){var _3V=E(_3U);switch(_3V[0]){case 0:var _3W=_3V[1],_3X=_3V[2],_3Y=new T(function(){if(E(_3W)>=12){return 203+(imul(imul(imul(-1,E(_3X))|0,2)|0,6)|0)|0;}else{return 7+(imul(imul(E(_3X),2)|0,6)|0)|0;}}),_3Z=new T(function(){var _40=E(_3W);if(_40>=12){var _41=23-_40|0;if(_41>=6){return 25+(20+(imul(_41,15)|0)|0)|0;}else{return 25+(imul(_41,15)|0)|0;}}else{if(_40>=6){return 25+(20+(imul(_40,15)|0)|0)|0;}else{return 25+(imul(_40,15)|0)|0;}}});return [0,_3Z,_3Y];case 1:return E(_3S);case 2:var _42=_3V[1],_43=new T(function(){return 203-(imul(imul(E(_42),2)|0,6)|0)|0;});return [0,_2M,_43];default:var _44=_3V[1],_45=new T(function(){return 203-(imul(imul(E(_44),2)|0,6)|0)|0;});return [0,_2N,_45];}},_46=function(_47,_48){var _49=jsShowI(_47);return new F(function(){return _11(fromJSStr(_49),_48);});},_4a=41,_4b=40,_4c=function(_4d,_4e,_4f){if(_4e>=0){return new F(function(){return _46(_4e,_4f);});}else{if(_4d<=6){return new F(function(){return _46(_4e,_4f);});}else{var _4g=new T(function(){var _4h=jsShowI(_4e);return B(_11(fromJSStr(_4h),[1,_4a,_4f]));});return [1,_4b,_4g];}}},_4i=0,_4j=new T(function(){return B(unCStr("Black"));}),_4k=new T(function(){return B(unCStr("White"));}),_4l=new T(function(){return B(unCStr("}"));}),_4m=new T(function(){return B(unCStr(", "));}),_4n=new T(function(){return B(unCStr("onSideIndex = "));}),_4o=new T(function(){return B(unCStr("RightSidePlacement {"));}),_4p=new T(function(){return B(unCStr("LeftSidePlacement {"));}),_4q=new T(function(){return B(unCStr("onBarIndex = "));}),_4r=new T(function(){return B(unCStr("BarPlacement {"));}),_4s=new T(function(){return B(unCStr("onPointIndex = "));}),_4t=new T(function(){return B(unCStr("pointIndex = "));}),_4u=new T(function(){return B(unCStr("PointPlacement {"));}),_4v=function(_4w,_4x,_4y){var _4z=E(_4x);switch(_4z[0]){case 0:var _4A=_4z[1],_4B=_4z[2],_4C=function(_4D){var _4E=new T(function(){var _4F=new T(function(){var _4G=new T(function(){var _4H=new T(function(){var _4I=new T(function(){return B(_11(_4l,_4D));});return B(_4c(0,E(_4B),_4I));},1);return B(_11(_4s,_4H));},1);return B(_11(_4m,_4G));});return B(_4c(0,E(_4A),_4F));},1);return new F(function(){return _11(_4t,_4E);});};if(_4w<11){var _4J=new T(function(){return B(_4C(_4y));},1);return new F(function(){return _11(_4u,_4J);});}else{var _4K=new T(function(){var _4L=new T(function(){return B(_4C([1,_4a,_4y]));},1);return B(_11(_4u,_4L));});return [1,_4b,_4K];}break;case 1:var _4M=_4z[1],_4N=function(_4O){var _4P=new T(function(){var _4Q=new T(function(){var _4R=new T(function(){return B(_11(_4l,_4O));});return B(_4c(0,E(_4M),_4R));},1);return B(_11(_4q,_4Q));},1);return new F(function(){return _11(_4r,_4P);});};if(_4w<11){return new F(function(){return _4N(_4y);});}else{var _4S=new T(function(){return B(_4N([1,_4a,_4y]));});return [1,_4b,_4S];}break;case 2:var _4T=_4z[1],_4U=function(_4V){var _4W=new T(function(){var _4X=new T(function(){var _4Y=new T(function(){return B(_11(_4l,_4V));});return B(_4c(0,E(_4T),_4Y));},1);return B(_11(_4n,_4X));},1);return new F(function(){return _11(_4p,_4W);});};if(_4w<11){return new F(function(){return _4U(_4y);});}else{var _4Z=new T(function(){return B(_4U([1,_4a,_4y]));});return [1,_4b,_4Z];}break;default:var _50=_4z[1],_51=function(_52){var _53=new T(function(){var _54=new T(function(){var _55=new T(function(){return B(_11(_4l,_52));});return B(_4c(0,E(_50),_55));},1);return B(_11(_4n,_54));},1);return new F(function(){return _11(_4o,_53);});};if(_4w<11){return new F(function(){return _51(_4y);});}else{var _56=new T(function(){return B(_51([1,_4a,_4y]));});return [1,_4b,_56];}}},_57=95,_58=function(_59){var _5a=E(_59);return (E(_5a)==32)?E(_57):E(_5a);},_5b=new T(function(){return B(unCStr("draggable "));}),_5c=new T(function(){return B(unCStr("class"));}),_5d=function(_5e,_5f){var _5g=E(_5f);if(!_5g[0]){return [0];}else{var _5h=_5g[1],_5i=_5g[2],_5j=new T(function(){return B(_5d(_5e,_5i));}),_5k=new T(function(){return B(A(_5e,[_5h]));});return [1,_5k,_5j];}},_5l=function(_5m){return E(E(_5m)[1]);},_5n=function(_5o){return E(E(_5o)[2]);},_5p=function(_5q,_5r,_5s,_5t,_5u){var _5v=function(_){var _5w=jsSetAttr(B(A(_5l,[_5q,_5s])),toJSStr(E(_5t)),toJSStr(E(_5u)));return _4i;};return new F(function(){return A(_5n,[_5r,_5v]);});},_5x=function(_5y,_5z,_5A,_5B,_){var _5C=new T(function(){var _5D=new T(function(){var _5E=new T(function(){var _5F=new T(function(){return B(_5d(_58,B(_4v(0,_5A,_F))));});return B(unAppCStr(" ",_5F));});if(!E(_5B)){return B(_11(_4j,_5E));}else{return B(_11(_4k,_5E));}});if(!E(_5z)){if(!E(_5B)){return B(_11(_5b,_5D));}else{return E(_5D);}}else{if(!E(_5B)){return E(_5D);}else{return B(_11(_5b,_5D));}}});return new F(function(){return A(_5p,[_4,_2I,_5y,_5c,_5C,_]);});},_5G=function(_){return _4i;},_5H=new T(function(){return (function (ns,tag) {return document.createElementNS(ns, tag);});}),_5I=function(_5J,_5K){if(_5J<=_5K){var _5L=function(_5M){var _5N=new T(function(){if(_5M!=_5K){return B(_5L(_5M+1|0));}else{return [0];}});return [1,_5M,_5N];};return new F(function(){return _5L(_5J);});}else{return [0];}},_5O=new T(function(){return B(_5I(0,2147483647));}),_5P=new T(function(){return B(unCStr("cy"));}),_5Q=new T(function(){return B(unCStr("cx"));}),_5R=new T(function(){return B(_4c(0,6,_F));}),_5S=new T(function(){return B(unCStr("r"));}),_5T=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:159:5-10"));}),_5U=[0,_2z,_2A,_F,_5T,_2z,_2z],_5V=new T(function(){return B(_2x(_5U));}),_5W=new T(function(){return B(unCStr("circle"));}),_5X=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_5Y=new T(function(){return B(unCStr("xboard"));}),_5Z=function(_60,_61,_62,_){if(0>=_62){return _4i;}else{var _63=function(_64,_65,_){var _66=jsFind(toJSStr(E(_5Y)));if(!_66[0]){return new F(function(){return die(_5V);});}else{var _67=E(_5H)(toJSStr(_5X),toJSStr(_5W)),_68=B(A(_5p,[_4,_2I,_67,_5S,_5R,_])),_69=new T(function(){if(!E(_60)){return [3,_64];}else{return [2,_64];}}),_6a=new T(function(){var _6b=B(_3T(_69));return [0,_6b[1],_6b[2]];}),_6c=new T(function(){return B(_4c(0,E(E(_6a)[1]),_F));}),_6d=B(A(_5p,[_4,_2I,_67,_5Q,_6c,_])),_6e=new T(function(){return B(_4c(0,E(E(_6a)[2]),_F));}),_6f=B(A(_5p,[_4,_2I,_67,_5P,_6e,_])),_6g=B(_5x(_67,_61,_69,_60,_)),_6h=jsAppendChild(E(_66[1]),_67);return new F(function(){return A(_65,[_]);});}},_6i=function(_6j,_6k,_){var _6l=E(_6j);if(!_6l[0]){return _4i;}else{var _6m=_6l[1],_6n=_6l[2],_6o=E(_6k);if(_6o==1){return new F(function(){return _63(_6m,_5G,_);});}else{var _6p=function(_){return new F(function(){return _6i(_6n,_6o-1|0,_);});};return new F(function(){return _63(_6m,_6p,_);});}}};return new F(function(){return _6i(_5O,_62,_);});}},_6q=0,_6r=1,_6s=function(_6t,_6u){while(1){var _6v=E(_6t);if(!_6v[0]){return E(_6u);}else{_6t=_6v[2];var _6w=[1,_6v[1],_6u];_6u=_6w;continue;}}},_6x=2,_6y=0,_6z=[1,_6y,_F],_6A=[1,_6y,_6z],_6B=[1,_6y,_6A],_6C=[1,_6y,_6B],_6D=[1,_6y,_6C],_6E=5,_6F=[1,_6E,_6D],_6G=[1,_6y,_6F],_6H=3,_6I=[1,_6H,_6G],_6J=[1,_6y,_6I],_6K=[1,_6y,_6J],_6L=[1,_6y,_6K],_6M=[1,_6y,_6L],_6N=[1,_6E,_6M],_6O=[1,_6y,_6N],_6P=[1,_6y,_6O],_6Q=[1,_6y,_6P],_6R=[1,_6y,_6Q],_6S=[1,_6y,_6R],_6T=[1,_6y,_6S],_6U=[1,_6y,_6T],_6V=[1,_6y,_6U],_6W=[1,_6y,_6V],_6X=[1,_6y,_6W],_6Y=function(_6Z){var _70=E(_6Z);if(!_70[0]){return [0];}else{var _71=_70[2],_72=new T(function(){return B(_6Y(_71));});return [1,[0,_6r,_70[1]],_72];}},_73=function(_74,_75){var _76=new T(function(){return B(_6Y(_75));});return [1,[0,_6r,_74],_76];},_77=new T(function(){return B(_73(_6x,_6X));}),_78=new T(function(){return B(_6s(_77,_F));}),_79=function(_7a){var _7b=E(_7a);return (E(_7b[1])==0)?E(_7b):[0,_6q,_7b[2]];},_7c=new T(function(){return B(_5d(_79,_78));}),_7d=function(_7e,_7f){var _7g=E(_7e);if(!E(_7g[1])){return new F(function(){return _3P("main.hs:(259,20)-(260,55)|function whiteOrBlack");});}else{return (E(_7g[2])==0)?E(_7f):E(_7g);}},_7h=function(_7i,_7j,_7k){var _7l=E(_7j);if(!_7l[0]){return [0];}else{var _7m=_7l[1],_7n=_7l[2],_7o=E(_7k);if(!_7o[0]){return [0];}else{var _7p=_7o[1],_7q=_7o[2],_7r=new T(function(){return B(_7h(_7i,_7n,_7q));}),_7s=new T(function(){return B(A(_7i,[_7m,_7p]));});return [1,_7s,_7r];}}},_7t=new T(function(){return B(_7h(_7d,_77,_7c));}),_7u=function(_7v,_7w){while(1){var _7x=E(_7v);if(!_7x[0]){return E(_7w);}else{_7v=_7x[2];var _7y=_7w+E(_7x[1])|0;_7w=_7y;continue;}}},_7z=function(_7A,_7B,_7C){return new F(function(){return _7u(_7B,_7C+_7A|0);});},_7D=new T(function(){return B(_7z(2,_6X,0));}),_7E=[0,_7t,_7D,_7D,_6y,_6y,_6r,_6r],_7F="deltaZ",_7G="deltaY",_7H="deltaX",_7I=new T(function(){return B(unCStr(")"));}),_7J=new T(function(){return B(_4c(0,2,_7I));}),_7K=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_7J));}),_7L=function(_7M){var _7N=new T(function(){return B(_4c(0,_7M,_7K));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_7N)));});},_7O=function(_7P,_){return new T(function(){var _7Q=Number(E(_7P)),_7R=jsTrunc(_7Q);if(_7R<0){return B(_7L(_7R));}else{if(_7R>2){return B(_7L(_7R));}else{return _7R;}}});},_7S=0,_7T=[0,_7S,_7S,_7S],_7U="button",_7V=new T(function(){return jsGetMouseCoords;}),_7W=function(_7X,_){var _7Y=E(_7X);if(!_7Y[0]){return _F;}else{var _7Z=_7Y[1],_80=B(_7W(_7Y[2],_)),_81=new T(function(){var _82=Number(E(_7Z));return jsTrunc(_82);});return [1,_81,_80];}},_83=function(_84,_){var _85=__arr2lst(0,_84);return new F(function(){return _7W(_85,_);});},_86=function(_87,_){return new F(function(){return _83(E(_87),_);});},_88=function(_89,_){return new T(function(){var _8a=Number(E(_89));return jsTrunc(_8a);});},_8b=[0,_88,_86],_8c=function(_8d,_){var _8e=E(_8d);if(!_8e[0]){return _F;}else{var _8f=B(_8c(_8e[2],_));return [1,_8e[1],_8f];}},_8g=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:264:5-9"));}),_8h=[0,_2z,_2A,_F,_8g,_2z,_2z],_8i=new T(function(){return B(_2x(_8h));}),_8j=function(_){return new F(function(){return die(_8i);});},_8k=function(_8l){return E(E(_8l)[1]);},_8m=function(_8n,_8o,_8p,_){var _8q=__arr2lst(0,_8p),_8r=B(_8c(_8q,_)),_8s=E(_8r);if(!_8s[0]){return new F(function(){return _8j(_);});}else{var _8t=E(_8s[2]);if(!_8t[0]){return new F(function(){return _8j(_);});}else{if(!E(_8t[2])[0]){var _8u=B(A(_8k,[_8n,_8s[1],_])),_8v=B(A(_8k,[_8o,_8t[1],_]));return [0,_8u,_8v];}else{return new F(function(){return _8j(_);});}}}},_8w=function(_){return new F(function(){return __jsNull();});},_8x=function(_8y){var _8z=B(A(_8y,[_]));return E(_8z);},_8A=new T(function(){return B(_8x(_8w));}),_8B=new T(function(){return E(_8A);}),_8C=function(_8D,_8E,_){if(E(_8D)==7){var _8F=E(_7V)(_8E),_8G=B(_8m(_8b,_8b,_8F,_)),_8H=_8G,_8I=_8E[E(_7H)],_8J=_8I,_8K=_8E[E(_7G)],_8L=_8K,_8M=_8E[E(_7F)],_8N=_8M;return new T(function(){return [0,E(_8H),E(_2z),[0,_8J,_8L,_8N]];});}else{var _8O=E(_7V)(_8E),_8P=B(_8m(_8b,_8b,_8O,_)),_8Q=_8P,_8R=_8E[E(_7U)],_8S=__eq(_8R,E(_8B));if(!E(_8S)){var _8T=B(_7O(_8R,_)),_8U=_8T;return new T(function(){return [0,E(_8Q),[1,_8U],E(_7T)];});}else{return new T(function(){return [0,E(_8Q),E(_2z),E(_7T)];});}}},_8V=function(_8W,_8X,_){return new F(function(){return _8C(_8W,E(_8X),_);});},_8Y="mouseout",_8Z="mouseover",_90="mousemove",_91="mouseup",_92="mousedown",_93="dblclick",_94="click",_95="wheel",_96=function(_97){switch(E(_97)){case 0:return E(_94);case 1:return E(_93);case 2:return E(_92);case 3:return E(_91);case 4:return E(_90);case 5:return E(_8Z);case 6:return E(_8Y);default:return E(_95);}},_98=[0,_96,_8V],_99=function(_){return _4i;},_9a=[0,_2I,_r],_9b=new T(function(){return B(unCStr("!!: negative index"));}),_9c=new T(function(){return B(unCStr("Prelude."));}),_9d=new T(function(){return B(_11(_9c,_9b));}),_9e=new T(function(){return B(err(_9d));}),_9f=new T(function(){return B(unCStr("!!: index too large"));}),_9g=new T(function(){return B(_11(_9c,_9f));}),_9h=new T(function(){return B(err(_9g));}),_9i=function(_9j,_9k){while(1){var _9l=E(_9j);if(!_9l[0]){return E(_9h);}else{var _9m=E(_9k);if(!_9m){return E(_9l[1]);}else{_9j=_9l[2];_9k=_9m-1|0;continue;}}}},_9n=function(_9o,_9p){if(_9p>=0){return new F(function(){return _9i(_9o,_9p);});}else{return E(_9e);}},_9q=0,_9r=new T(function(){return B(unCStr(": empty list"));}),_9s=function(_9t){var _9u=new T(function(){return B(_11(_9t,_9r));},1);return new F(function(){return err(B(_11(_9c,_9u)));});},_9v=new T(function(){return B(unCStr("head"));}),_9w=new T(function(){return B(_9s(_9v));}),_9x=new T(function(){return (function (elem, cx, cy, duration) {$(elem).velocity({ cx: cx, cy: cy }, { duration: duration });});}),_9y=function(_9z,_9A,_9B,_){var _9C=jsElemsByClassName(toJSStr(B(_5d(_58,B(_4v(0,_9z,_F))))));if(!_9C[0]){return E(_9w);}else{var _9D=E(_9C[1]),_9E=B(_3T(_9A)),_9F=E(_9x)(_9D,E(_9E[1]),E(_9E[2]),300);return new F(function(){return _5x(_9D,_9B,_9A,_9B,_);});}},_9G=new T(function(){return (function (msg) { alert(msg); });}),_9H="value",_9I=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:241:9-19"));}),_9J=[0,_2z,_2A,_F,_9I,_2z,_2z],_9K=new T(function(){return B(_2x(_9J));}),_9L=function(_){var _9M=jsFind("sharedKey");if(!_9M[0]){return new F(function(){return die(_9K);});}else{var _9N=jsGet(E(_9M[1]),E(_9H)),_9O=E(_9G)(toJSStr(fromJSStr(_9N)));return new F(function(){return _99(_);});}},_9P=function(_9Q,_){return new F(function(){return _9L(_);});},_9R=new T(function(){return (function (cb) {setDropCheckerCallback_ffi(cb);});}),_9S=function(_9T,_9U){var _9V=function(_9W,_9X){while(1){var _9Y=(function(_9Z,_a0){var _a1=E(_9Z);if(!_a1[0]){return [0];}else{var _a2=_a1[2];if(!B(A(_9T,[_a1[1]]))){_9W=_a2;var _a3=_a0+1|0;_9X=_a3;return null;}else{var _a4=new T(function(){return B(_9V(_a2,_a0+1|0));});return [1,_a0,_a4];}}})(_9W,_9X);if(_9Y!=null){return _9Y;}}},_a5=B(_9V(_9U,0));return (_a5[0]==0)?[0]:[1,_a5[1]];},_a6=new T(function(){return B(_2J(210,2));}),_a7=function(_a8){var _a9=E(_a8);return (E(_a9)==95)?32:E(_a9);},_aa=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_ab=new T(function(){return B(err(_aa));}),_ac=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_ad=new T(function(){return B(err(_ac));}),_ae=function(_af,_ag){return new F(function(){return A(_ag,[_6r]);});},_ah=[0,_4k,_ae],_ai=[1,_ah,_F],_aj=function(_ak,_al){return new F(function(){return A(_al,[_6q]);});},_am=[0,_4j,_aj],_an=[1,_am,_ai],_ao=new T(function(){return B(_3P("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_ap=function(_aq,_ar){while(1){var _as=(function(_at,_au){var _av=E(_at);switch(_av[0]){case 0:var _aw=E(_au);if(!_aw[0]){return [0];}else{_aq=B(A(_av[1],[_aw[1]]));_ar=_aw[2];return null;}break;case 1:var _ax=B(A(_av[1],[_au])),_ay=_au;_aq=_ax;_ar=_ay;return null;case 2:return [0];case 3:var _az=_av[2],_aA=new T(function(){return B(_ap(_az,_au));});return [1,[0,_av[1],_au],_aA];default:return E(_av[1]);}})(_aq,_ar);if(_as!=null){return _as;}}},_aB=function(_aC,_aD){var _aE=function(_aF){var _aG=E(_aD);if(_aG[0]==3){var _aH=_aG[2],_aI=new T(function(){return B(_aB(_aC,_aH));});return [3,_aG[1],_aI];}else{var _aJ=E(_aC);if(_aJ[0]==2){return E(_aG);}else{var _aK=E(_aG);if(_aK[0]==2){return E(_aJ);}else{var _aL=function(_aM){var _aN=E(_aK);if(_aN[0]==4){var _aO=_aN[1];return [1,function(_aP){return [4,new T(function(){return B(_11(B(_ap(_aJ,_aP)),_aO));})];}];}else{var _aQ=E(_aJ);if(_aQ[0]==1){var _aR=_aQ[1],_aS=E(_aN);if(!_aS[0]){return [1,function(_aT){return new F(function(){return _aB(B(A(_aR,[_aT])),_aS);});}];}else{var _aU=_aS[1];return [1,function(_aV){var _aW=new T(function(){return B(A(_aU,[_aV]));});return new F(function(){return _aB(B(A(_aR,[_aV])),_aW);});}];}}else{var _aX=E(_aN);if(!_aX[0]){return E(_ao);}else{var _aY=_aX[1];return [1,function(_aZ){var _b0=new T(function(){return B(A(_aY,[_aZ]));});return new F(function(){return _aB(_aQ,_b0);});}];}}}},_b1=E(_aJ);switch(_b1[0]){case 1:var _b2=_b1[1],_b3=E(_aK);if(_b3[0]==4){var _b4=_b3[1];return [1,function(_b5){return [4,new T(function(){return B(_11(B(_ap(B(A(_b2,[_b5])),_b5)),_b4));})];}];}else{return new F(function(){return _aL(_);});}break;case 4:var _b6=_b1[1],_b7=E(_aK);switch(_b7[0]){case 0:return [1,function(_b8){return [4,new T(function(){var _b9=new T(function(){return B(_ap(_b7,_b8));},1);return B(_11(_b6,_b9));})];}];case 1:var _ba=_b7[1];return [1,function(_bb){return [4,new T(function(){var _bc=new T(function(){return B(_ap(B(A(_ba,[_bb])),_bb));},1);return B(_11(_b6,_bc));})];}];default:var _bd=_b7[1];return [4,new T(function(){return B(_11(_b6,_bd));})];}break;default:return new F(function(){return _aL(_);});}}}}},_be=E(_aC);switch(_be[0]){case 0:var _bf=_be[1],_bg=E(_aD);if(!_bg[0]){var _bh=_bg[1];return [0,function(_bi){var _bj=new T(function(){return B(A(_bh,[_bi]));});return new F(function(){return _aB(B(A(_bf,[_bi])),_bj);});}];}else{return new F(function(){return _aE(_);});}break;case 3:var _bk=_be[2],_bl=new T(function(){return B(_aB(_bk,_aD));});return [3,_be[1],_bl];default:return new F(function(){return _aE(_);});}},_bm=function(_bn,_bo){while(1){var _bp=E(_bn);if(!_bp[0]){return (E(_bo)[0]==0)?true:false;}else{var _bq=E(_bo);if(!_bq[0]){return false;}else{if(E(_bp[1])!=E(_bq[1])){return false;}else{_bn=_bp[2];_bo=_bq[2];continue;}}}}},_br=function(_bs,_bt){return E(_bs)!=E(_bt);},_bu=function(_bv,_bw){return E(_bv)==E(_bw);},_bx=[0,_bu,_br],_by=function(_bz,_bA){while(1){var _bB=E(_bz);if(!_bB[0]){return (E(_bA)[0]==0)?true:false;}else{var _bC=E(_bA);if(!_bC[0]){return false;}else{if(E(_bB[1])!=E(_bC[1])){return false;}else{_bz=_bB[2];_bA=_bC[2];continue;}}}}},_bD=function(_bE,_bF){return (!B(_by(_bE,_bF)))?true:false;},_bG=[0,_by,_bD],_bH=function(_bI,_bJ){var _bK=E(_bI);switch(_bK[0]){case 0:var _bL=_bK[1];return [0,function(_bM){return new F(function(){return _bH(B(A(_bL,[_bM])),_bJ);});}];case 1:var _bN=_bK[1];return [1,function(_bO){return new F(function(){return _bH(B(A(_bN,[_bO])),_bJ);});}];case 2:return [2];case 3:var _bP=_bK[2],_bQ=new T(function(){return B(_bH(_bP,_bJ));});return new F(function(){return _aB(B(A(_bJ,[_bK[1]])),_bQ);});break;default:var _bR=function(_bS){var _bT=E(_bS);if(!_bT[0]){return [0];}else{var _bU=_bT[2],_bV=E(_bT[1]),_bW=new T(function(){return B(_bR(_bU));},1);return new F(function(){return _11(B(_ap(B(A(_bJ,[_bV[1]])),_bV[2])),_bW);});}},_bX=B(_bR(_bK[1]));return (_bX[0]==0)?[2]:[4,_bX];}},_bY=[2],_bZ=function(_c0){return [3,_c0,_bY];},_c1=function(_c2,_c3){var _c4=E(_c2);if(!_c4){return new F(function(){return A(_c3,[_4i]);});}else{var _c5=new T(function(){return B(_c1(_c4-1|0,_c3));});return [0,function(_c6){return E(_c5);}];}},_c7=function(_c8,_c9,_ca){var _cb=new T(function(){return B(A(_c8,[_bZ]));}),_cc=function(_cd,_ce,_cf,_cg){while(1){var _ch=(function(_ci,_cj,_ck,_cl){var _cm=E(_ci);switch(_cm[0]){case 0:var _cn=E(_cj);if(!_cn[0]){return new F(function(){return A(_c9,[_cl]);});}else{_cd=B(A(_cm[1],[_cn[1]]));_ce=_cn[2];var _co=_ck+1|0,_cp=_cl;_cf=_co;_cg=_cp;return null;}break;case 1:var _cq=B(A(_cm[1],[_cj])),_cr=_cj,_co=_ck,_cp=_cl;_cd=_cq;_ce=_cr;_cf=_co;_cg=_cp;return null;case 2:return new F(function(){return A(_c9,[_cl]);});break;case 3:var _cs=new T(function(){return B(_bH(_cm,_cl));}),_ct=function(_cu){return E(_cs);};return new F(function(){return _c1(_ck,_ct);});break;default:return new F(function(){return _bH(_cm,_cl);});}})(_cd,_ce,_cf,_cg);if(_ch!=null){return _ch;}}};return function(_cv){return new F(function(){return _cc(_cb,_cv,0,_ca);});};},_cw=function(_cx){return new F(function(){return A(_cx,[_F]);});},_cy=function(_cz,_cA){var _cB=function(_cC){var _cD=E(_cC);if(!_cD[0]){return E(_cw);}else{var _cE=_cD[1],_cF=_cD[2];if(!B(A(_cz,[_cE]))){return E(_cw);}else{var _cG=new T(function(){return B(_cB(_cF));}),_cH=function(_cI){var _cJ=new T(function(){var _cK=function(_cL){return new F(function(){return A(_cI,[[1,_cE,_cL]]);});};return B(A(_cG,[_cK]));});return [0,function(_cM){return E(_cJ);}];};return E(_cH);}}};return function(_cN){return new F(function(){return A(_cB,[_cN,_cA]);});};},_cO=[6],_cP=new T(function(){return B(unCStr("valDig: Bad base"));}),_cQ=new T(function(){return B(err(_cP));}),_cR=function(_cS,_cT){var _cU=function(_cV,_cW){var _cX=E(_cV);if(!_cX[0]){var _cY=new T(function(){return B(A(_cW,[_F]));}),_cZ=function(_d0){return new F(function(){return A(_d0,[_cY]);});};return E(_cZ);}else{var _d1=_cX[2],_d2=E(_cX[1]),_d3=function(_d4){var _d5=new T(function(){var _d6=function(_d7){return new F(function(){return A(_cW,[[1,_d4,_d7]]);});};return B(_cU(_d1,_d6));}),_d8=function(_d9){var _da=new T(function(){return B(A(_d5,[_d9]));});return [0,function(_db){return E(_da);}];};return E(_d8);};switch(E(_cS)){case 8:if(48>_d2){var _dc=new T(function(){return B(A(_cW,[_F]));}),_dd=function(_de){return new F(function(){return A(_de,[_dc]);});};return E(_dd);}else{if(_d2>55){var _df=new T(function(){return B(A(_cW,[_F]));}),_dg=function(_dh){return new F(function(){return A(_dh,[_df]);});};return E(_dg);}else{return new F(function(){return _d3(_d2-48|0);});}}break;case 10:if(48>_d2){var _di=new T(function(){return B(A(_cW,[_F]));}),_dj=function(_dk){return new F(function(){return A(_dk,[_di]);});};return E(_dj);}else{if(_d2>57){var _dl=new T(function(){return B(A(_cW,[_F]));}),_dm=function(_dn){return new F(function(){return A(_dn,[_dl]);});};return E(_dm);}else{return new F(function(){return _d3(_d2-48|0);});}}break;case 16:if(48>_d2){if(97>_d2){if(65>_d2){var _do=new T(function(){return B(A(_cW,[_F]));}),_dp=function(_dq){return new F(function(){return A(_dq,[_do]);});};return E(_dp);}else{if(_d2>70){var _dr=new T(function(){return B(A(_cW,[_F]));}),_ds=function(_dt){return new F(function(){return A(_dt,[_dr]);});};return E(_ds);}else{return new F(function(){return _d3((_d2-65|0)+10|0);});}}}else{if(_d2>102){if(65>_d2){var _du=new T(function(){return B(A(_cW,[_F]));}),_dv=function(_dw){return new F(function(){return A(_dw,[_du]);});};return E(_dv);}else{if(_d2>70){var _dx=new T(function(){return B(A(_cW,[_F]));}),_dy=function(_dz){return new F(function(){return A(_dz,[_dx]);});};return E(_dy);}else{return new F(function(){return _d3((_d2-65|0)+10|0);});}}}else{return new F(function(){return _d3((_d2-97|0)+10|0);});}}}else{if(_d2>57){if(97>_d2){if(65>_d2){var _dA=new T(function(){return B(A(_cW,[_F]));}),_dB=function(_dC){return new F(function(){return A(_dC,[_dA]);});};return E(_dB);}else{if(_d2>70){var _dD=new T(function(){return B(A(_cW,[_F]));}),_dE=function(_dF){return new F(function(){return A(_dF,[_dD]);});};return E(_dE);}else{return new F(function(){return _d3((_d2-65|0)+10|0);});}}}else{if(_d2>102){if(65>_d2){var _dG=new T(function(){return B(A(_cW,[_F]));}),_dH=function(_dI){return new F(function(){return A(_dI,[_dG]);});};return E(_dH);}else{if(_d2>70){var _dJ=new T(function(){return B(A(_cW,[_F]));}),_dK=function(_dL){return new F(function(){return A(_dL,[_dJ]);});};return E(_dK);}else{return new F(function(){return _d3((_d2-65|0)+10|0);});}}}else{return new F(function(){return _d3((_d2-97|0)+10|0);});}}}else{return new F(function(){return _d3(_d2-48|0);});}}break;default:return E(_cQ);}}},_dM=function(_dN){var _dO=E(_dN);if(!_dO[0]){return [2];}else{return new F(function(){return A(_cT,[_dO]);});}};return function(_dP){return new F(function(){return A(_cU,[_dP,_2,_dM]);});};},_dQ=16,_dR=8,_dS=function(_dT){var _dU=function(_dV){return new F(function(){return A(_dT,[[5,[0,_dR,_dV]]]);});},_dW=function(_dX){return new F(function(){return A(_dT,[[5,[0,_dQ,_dX]]]);});},_dY=function(_dZ){switch(E(_dZ)){case 79:return [1,B(_cR(_dR,_dU))];case 88:return [1,B(_cR(_dQ,_dW))];case 111:return [1,B(_cR(_dR,_dU))];case 120:return [1,B(_cR(_dQ,_dW))];default:return [2];}},_e0=[0,_dY];return function(_e1){return (E(_e1)==48)?E(_e0):[2];};},_e2=function(_e3){return [0,B(_dS(_e3))];},_e4=function(_e5){return new F(function(){return A(_e5,[_2z]);});},_e6=function(_e7){return new F(function(){return A(_e7,[_2z]);});},_e8=10,_e9=[0,1],_ea=[0,2147483647],_eb=function(_ec,_ed){while(1){var _ee=E(_ec);if(!_ee[0]){var _ef=_ee[1],_eg=E(_ed);if(!_eg[0]){var _eh=_eg[1],_ei=addC(_ef,_eh);if(!E(_ei[2])){return [0,_ei[1]];}else{_ec=[1,I_fromInt(_ef)];_ed=[1,I_fromInt(_eh)];continue;}}else{_ec=[1,I_fromInt(_ef)];_ed=_eg;continue;}}else{var _ej=E(_ed);if(!_ej[0]){_ec=_ee;_ed=[1,I_fromInt(_ej[1])];continue;}else{return [1,I_add(_ee[1],_ej[1])];}}}},_ek=new T(function(){return B(_eb(_ea,_e9));}),_el=function(_em){var _en=E(_em);if(!_en[0]){var _eo=E(_en[1]);return (_eo==(-2147483648))?E(_ek):[0, -_eo];}else{return [1,I_negate(_en[1])];}},_ep=[0,10],_eq=function(_er,_es){while(1){var _et=E(_er);if(!_et[0]){return E(_es);}else{_er=_et[2];var _eu=_es+1|0;_es=_eu;continue;}}},_ev=function(_ew){return [0,_ew];},_ex=function(_ey){return new F(function(){return _ev(E(_ey));});},_ez=new T(function(){return B(unCStr("this should not happen"));}),_eA=new T(function(){return B(err(_ez));}),_eB=function(_eC,_eD){while(1){var _eE=E(_eC);if(!_eE[0]){var _eF=_eE[1],_eG=E(_eD);if(!_eG[0]){var _eH=_eG[1];if(!(imul(_eF,_eH)|0)){return [0,imul(_eF,_eH)|0];}else{_eC=[1,I_fromInt(_eF)];_eD=[1,I_fromInt(_eH)];continue;}}else{_eC=[1,I_fromInt(_eF)];_eD=_eG;continue;}}else{var _eI=E(_eD);if(!_eI[0]){_eC=_eE;_eD=[1,I_fromInt(_eI[1])];continue;}else{return [1,I_mul(_eE[1],_eI[1])];}}}},_eJ=function(_eK,_eL){var _eM=E(_eL);if(!_eM[0]){return [0];}else{var _eN=E(_eM[2]);if(!_eN[0]){return E(_eA);}else{var _eO=_eN[2],_eP=new T(function(){return B(_eJ(_eK,_eO));});return [1,B(_eb(B(_eB(_eM[1],_eK)),_eN[1])),_eP];}}},_eQ=[0,0],_eR=function(_eS,_eT,_eU){while(1){var _eV=(function(_eW,_eX,_eY){var _eZ=E(_eY);if(!_eZ[0]){return E(_eQ);}else{if(!E(_eZ[2])[0]){return E(_eZ[1]);}else{var _f0=E(_eX);if(_f0<=40){var _f1=_eQ,_f2=_eZ;while(1){var _f3=E(_f2);if(!_f3[0]){return E(_f1);}else{var _f4=B(_eb(B(_eB(_f1,_eW)),_f3[1]));_f2=_f3[2];_f1=_f4;continue;}}}else{var _f5=B(_eB(_eW,_eW));if(!(_f0%2)){_eS=_f5;_eT=quot(_f0+1|0,2);var _f6=B(_eJ(_eW,_eZ));_eU=_f6;return null;}else{_eS=_f5;_eT=quot(_f0+1|0,2);var _f6=B(_eJ(_eW,[1,_eQ,_eZ]));_eU=_f6;return null;}}}}})(_eS,_eT,_eU);if(_eV!=null){return _eV;}}},_f7=function(_f8,_f9){var _fa=new T(function(){return B(_eq(_f9,0));},1);return new F(function(){return _eR(_f8,_fa,B(_5d(_ex,_f9)));});},_fb=function(_fc){var _fd=new T(function(){var _fe=new T(function(){var _ff=function(_fg){var _fh=new T(function(){return B(_f7(_ep,_fg));});return new F(function(){return A(_fc,[[1,_fh]]);});};return [1,B(_cR(_e8,_ff))];}),_fi=function(_fj){if(E(_fj)==43){var _fk=function(_fl){var _fm=new T(function(){return B(_f7(_ep,_fl));});return new F(function(){return A(_fc,[[1,_fm]]);});};return [1,B(_cR(_e8,_fk))];}else{return [2];}},_fn=function(_fo){if(E(_fo)==45){var _fp=function(_fq){var _fr=new T(function(){return B(_el(B(_f7(_ep,_fq))));});return new F(function(){return A(_fc,[[1,_fr]]);});};return [1,B(_cR(_e8,_fp))];}else{return [2];}};return B(_aB(B(_aB([0,_fn],[0,_fi])),_fe));}),_fs=function(_ft){return (E(_ft)==69)?E(_fd):[2];},_fu=function(_fv){return (E(_fv)==101)?E(_fd):[2];};return new F(function(){return _aB([0,_fu],[0,_fs]);});},_fw=function(_fx){var _fy=function(_fz){return new F(function(){return A(_fx,[[1,_fz]]);});};return function(_fA){return (E(_fA)==46)?[1,B(_cR(_e8,_fy))]:[2];};},_fB=function(_fC){return [0,B(_fw(_fC))];},_fD=function(_fE){var _fF=function(_fG){var _fH=function(_fI){var _fJ=function(_fK){return new F(function(){return A(_fE,[[5,[1,_fG,_fI,_fK]]]);});};return [1,B(_c7(_fb,_e4,_fJ))];};return [1,B(_c7(_fB,_e6,_fH))];};return new F(function(){return _cR(_e8,_fF);});},_fL=function(_fM){return [1,B(_fD(_fM))];},_fN=function(_fO){return E(E(_fO)[1]);},_fP=function(_fQ,_fR,_fS){while(1){var _fT=E(_fS);if(!_fT[0]){return false;}else{if(!B(A(_fN,[_fQ,_fR,_fT[1]]))){_fS=_fT[2];continue;}else{return true;}}}},_fU=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_fV=function(_fW){return new F(function(){return _fP(_bx,_fW,_fU);});},_fX=false,_fY=true,_fZ=function(_g0){var _g1=new T(function(){return B(A(_g0,[_dR]));}),_g2=new T(function(){return B(A(_g0,[_dQ]));});return function(_g3){switch(E(_g3)){case 79:return E(_g1);case 88:return E(_g2);case 111:return E(_g1);case 120:return E(_g2);default:return [2];}};},_g4=function(_g5){return [0,B(_fZ(_g5))];},_g6=function(_g7){return new F(function(){return A(_g7,[_e8]);});},_g8=function(_g9){var _ga=new T(function(){return B(_4c(9,_g9,_F));});return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",_ga)));});},_gb=function(_gc){var _gd=E(_gc);if(!_gd[0]){return E(_gd[1]);}else{return new F(function(){return I_toInt(_gd[1]);});}},_ge=function(_gf,_gg){var _gh=E(_gf);if(!_gh[0]){var _gi=_gh[1],_gj=E(_gg);return (_gj[0]==0)?_gi<=_gj[1]:I_compareInt(_gj[1],_gi)>=0;}else{var _gk=_gh[1],_gl=E(_gg);return (_gl[0]==0)?I_compareInt(_gk,_gl[1])<=0:I_compare(_gk,_gl[1])<=0;}},_gm=function(_gn){return [2];},_go=function(_gp){var _gq=E(_gp);if(!_gq[0]){return E(_gm);}else{var _gr=_gq[1],_gs=E(_gq[2]);if(!_gs[0]){return E(_gr);}else{var _gt=new T(function(){return B(_go(_gs));}),_gu=function(_gv){var _gw=new T(function(){return B(A(_gt,[_gv]));});return new F(function(){return _aB(B(A(_gr,[_gv])),_gw);});};return E(_gu);}}},_gx=function(_gy,_gz){var _gA=function(_gB,_gC,_gD){var _gE=E(_gB);if(!_gE[0]){return new F(function(){return A(_gD,[_gy]);});}else{var _gF=_gE[2],_gG=E(_gC);if(!_gG[0]){return [2];}else{var _gH=_gG[2];if(E(_gE[1])!=E(_gG[1])){return [2];}else{var _gI=new T(function(){return B(_gA(_gF,_gH,_gD));});return [0,function(_gJ){return E(_gI);}];}}}};return function(_gK){return new F(function(){return _gA(_gy,_gK,_gz);});};},_gL=new T(function(){return B(unCStr("SO"));}),_gM=14,_gN=function(_gO){var _gP=new T(function(){return B(A(_gO,[_gM]));}),_gQ=function(_gR){return E(_gP);};return [1,B(_gx(_gL,_gQ))];},_gS=new T(function(){return B(unCStr("SOH"));}),_gT=1,_gU=function(_gV){var _gW=new T(function(){return B(A(_gV,[_gT]));}),_gX=function(_gY){return E(_gW);};return [1,B(_gx(_gS,_gX))];},_gZ=function(_h0){return [1,B(_c7(_gU,_gN,_h0))];},_h1=new T(function(){return B(unCStr("NUL"));}),_h2=0,_h3=function(_h4){var _h5=new T(function(){return B(A(_h4,[_h2]));}),_h6=function(_h7){return E(_h5);};return [1,B(_gx(_h1,_h6))];},_h8=new T(function(){return B(unCStr("STX"));}),_h9=2,_ha=function(_hb){var _hc=new T(function(){return B(A(_hb,[_h9]));}),_hd=function(_he){return E(_hc);};return [1,B(_gx(_h8,_hd))];},_hf=new T(function(){return B(unCStr("ETX"));}),_hg=3,_hh=function(_hi){var _hj=new T(function(){return B(A(_hi,[_hg]));}),_hk=function(_hl){return E(_hj);};return [1,B(_gx(_hf,_hk))];},_hm=new T(function(){return B(unCStr("EOT"));}),_hn=4,_ho=function(_hp){var _hq=new T(function(){return B(A(_hp,[_hn]));}),_hr=function(_hs){return E(_hq);};return [1,B(_gx(_hm,_hr))];},_ht=new T(function(){return B(unCStr("ENQ"));}),_hu=5,_hv=function(_hw){var _hx=new T(function(){return B(A(_hw,[_hu]));}),_hy=function(_hz){return E(_hx);};return [1,B(_gx(_ht,_hy))];},_hA=new T(function(){return B(unCStr("ACK"));}),_hB=6,_hC=function(_hD){var _hE=new T(function(){return B(A(_hD,[_hB]));}),_hF=function(_hG){return E(_hE);};return [1,B(_gx(_hA,_hF))];},_hH=new T(function(){return B(unCStr("BEL"));}),_hI=7,_hJ=function(_hK){var _hL=new T(function(){return B(A(_hK,[_hI]));}),_hM=function(_hN){return E(_hL);};return [1,B(_gx(_hH,_hM))];},_hO=new T(function(){return B(unCStr("BS"));}),_hP=8,_hQ=function(_hR){var _hS=new T(function(){return B(A(_hR,[_hP]));}),_hT=function(_hU){return E(_hS);};return [1,B(_gx(_hO,_hT))];},_hV=new T(function(){return B(unCStr("HT"));}),_hW=9,_hX=function(_hY){var _hZ=new T(function(){return B(A(_hY,[_hW]));}),_i0=function(_i1){return E(_hZ);};return [1,B(_gx(_hV,_i0))];},_i2=new T(function(){return B(unCStr("LF"));}),_i3=10,_i4=function(_i5){var _i6=new T(function(){return B(A(_i5,[_i3]));}),_i7=function(_i8){return E(_i6);};return [1,B(_gx(_i2,_i7))];},_i9=new T(function(){return B(unCStr("VT"));}),_ia=11,_ib=function(_ic){var _id=new T(function(){return B(A(_ic,[_ia]));}),_ie=function(_if){return E(_id);};return [1,B(_gx(_i9,_ie))];},_ig=new T(function(){return B(unCStr("FF"));}),_ih=12,_ii=function(_ij){var _ik=new T(function(){return B(A(_ij,[_ih]));}),_il=function(_im){return E(_ik);};return [1,B(_gx(_ig,_il))];},_in=new T(function(){return B(unCStr("CR"));}),_io=13,_ip=function(_iq){var _ir=new T(function(){return B(A(_iq,[_io]));}),_is=function(_it){return E(_ir);};return [1,B(_gx(_in,_is))];},_iu=new T(function(){return B(unCStr("SI"));}),_iv=15,_iw=function(_ix){var _iy=new T(function(){return B(A(_ix,[_iv]));}),_iz=function(_iA){return E(_iy);};return [1,B(_gx(_iu,_iz))];},_iB=new T(function(){return B(unCStr("DLE"));}),_iC=16,_iD=function(_iE){var _iF=new T(function(){return B(A(_iE,[_iC]));}),_iG=function(_iH){return E(_iF);};return [1,B(_gx(_iB,_iG))];},_iI=new T(function(){return B(unCStr("DC1"));}),_iJ=17,_iK=function(_iL){var _iM=new T(function(){return B(A(_iL,[_iJ]));}),_iN=function(_iO){return E(_iM);};return [1,B(_gx(_iI,_iN))];},_iP=new T(function(){return B(unCStr("DC2"));}),_iQ=18,_iR=function(_iS){var _iT=new T(function(){return B(A(_iS,[_iQ]));}),_iU=function(_iV){return E(_iT);};return [1,B(_gx(_iP,_iU))];},_iW=new T(function(){return B(unCStr("DC3"));}),_iX=19,_iY=function(_iZ){var _j0=new T(function(){return B(A(_iZ,[_iX]));}),_j1=function(_j2){return E(_j0);};return [1,B(_gx(_iW,_j1))];},_j3=new T(function(){return B(unCStr("DC4"));}),_j4=20,_j5=function(_j6){var _j7=new T(function(){return B(A(_j6,[_j4]));}),_j8=function(_j9){return E(_j7);};return [1,B(_gx(_j3,_j8))];},_ja=new T(function(){return B(unCStr("NAK"));}),_jb=21,_jc=function(_jd){var _je=new T(function(){return B(A(_jd,[_jb]));}),_jf=function(_jg){return E(_je);};return [1,B(_gx(_ja,_jf))];},_jh=new T(function(){return B(unCStr("SYN"));}),_ji=22,_jj=function(_jk){var _jl=new T(function(){return B(A(_jk,[_ji]));}),_jm=function(_jn){return E(_jl);};return [1,B(_gx(_jh,_jm))];},_jo=new T(function(){return B(unCStr("ETB"));}),_jp=23,_jq=function(_jr){var _js=new T(function(){return B(A(_jr,[_jp]));}),_jt=function(_ju){return E(_js);};return [1,B(_gx(_jo,_jt))];},_jv=new T(function(){return B(unCStr("CAN"));}),_jw=24,_jx=function(_jy){var _jz=new T(function(){return B(A(_jy,[_jw]));}),_jA=function(_jB){return E(_jz);};return [1,B(_gx(_jv,_jA))];},_jC=new T(function(){return B(unCStr("EM"));}),_jD=25,_jE=function(_jF){var _jG=new T(function(){return B(A(_jF,[_jD]));}),_jH=function(_jI){return E(_jG);};return [1,B(_gx(_jC,_jH))];},_jJ=new T(function(){return B(unCStr("SUB"));}),_jK=26,_jL=function(_jM){var _jN=new T(function(){return B(A(_jM,[_jK]));}),_jO=function(_jP){return E(_jN);};return [1,B(_gx(_jJ,_jO))];},_jQ=new T(function(){return B(unCStr("ESC"));}),_jR=27,_jS=function(_jT){var _jU=new T(function(){return B(A(_jT,[_jR]));}),_jV=function(_jW){return E(_jU);};return [1,B(_gx(_jQ,_jV))];},_jX=new T(function(){return B(unCStr("FS"));}),_jY=28,_jZ=function(_k0){var _k1=new T(function(){return B(A(_k0,[_jY]));}),_k2=function(_k3){return E(_k1);};return [1,B(_gx(_jX,_k2))];},_k4=new T(function(){return B(unCStr("GS"));}),_k5=29,_k6=function(_k7){var _k8=new T(function(){return B(A(_k7,[_k5]));}),_k9=function(_ka){return E(_k8);};return [1,B(_gx(_k4,_k9))];},_kb=new T(function(){return B(unCStr("RS"));}),_kc=30,_kd=function(_ke){var _kf=new T(function(){return B(A(_ke,[_kc]));}),_kg=function(_kh){return E(_kf);};return [1,B(_gx(_kb,_kg))];},_ki=new T(function(){return B(unCStr("US"));}),_kj=31,_kk=function(_kl){var _km=new T(function(){return B(A(_kl,[_kj]));}),_kn=function(_ko){return E(_km);};return [1,B(_gx(_ki,_kn))];},_kp=new T(function(){return B(unCStr("SP"));}),_kq=32,_kr=function(_ks){var _kt=new T(function(){return B(A(_ks,[_kq]));}),_ku=function(_kv){return E(_kt);};return [1,B(_gx(_kp,_ku))];},_kw=new T(function(){return B(unCStr("DEL"));}),_kx=127,_ky=function(_kz){var _kA=new T(function(){return B(A(_kz,[_kx]));}),_kB=function(_kC){return E(_kA);};return [1,B(_gx(_kw,_kB))];},_kD=[1,_ky,_F],_kE=[1,_kr,_kD],_kF=[1,_kk,_kE],_kG=[1,_kd,_kF],_kH=[1,_k6,_kG],_kI=[1,_jZ,_kH],_kJ=[1,_jS,_kI],_kK=[1,_jL,_kJ],_kL=[1,_jE,_kK],_kM=[1,_jx,_kL],_kN=[1,_jq,_kM],_kO=[1,_jj,_kN],_kP=[1,_jc,_kO],_kQ=[1,_j5,_kP],_kR=[1,_iY,_kQ],_kS=[1,_iR,_kR],_kT=[1,_iK,_kS],_kU=[1,_iD,_kT],_kV=[1,_iw,_kU],_kW=[1,_ip,_kV],_kX=[1,_ii,_kW],_kY=[1,_ib,_kX],_kZ=[1,_i4,_kY],_l0=[1,_hX,_kZ],_l1=[1,_hQ,_l0],_l2=[1,_hJ,_l1],_l3=[1,_hC,_l2],_l4=[1,_hv,_l3],_l5=[1,_ho,_l4],_l6=[1,_hh,_l5],_l7=[1,_ha,_l6],_l8=[1,_h3,_l7],_l9=[1,_gZ,_l8],_la=new T(function(){return B(_go(_l9));}),_lb=34,_lc=[0,1114111],_ld=92,_le=39,_lf=function(_lg){var _lh=new T(function(){return B(A(_lg,[_hI]));}),_li=new T(function(){return B(A(_lg,[_hP]));}),_lj=new T(function(){return B(A(_lg,[_hW]));}),_lk=new T(function(){return B(A(_lg,[_i3]));}),_ll=new T(function(){return B(A(_lg,[_ia]));}),_lm=new T(function(){return B(A(_lg,[_ih]));}),_ln=new T(function(){return B(A(_lg,[_io]));}),_lo=new T(function(){return B(A(_lg,[_ld]));}),_lp=new T(function(){return B(A(_lg,[_le]));}),_lq=new T(function(){return B(A(_lg,[_lb]));}),_lr=new T(function(){var _ls=function(_lt){var _lu=new T(function(){return B(_ev(E(_lt)));}),_lv=function(_lw){var _lx=B(_f7(_lu,_lw));if(!B(_ge(_lx,_lc))){return [2];}else{var _ly=new T(function(){var _lz=B(_gb(_lx));if(_lz>>>0>1114111){return B(_g8(_lz));}else{return _lz;}});return new F(function(){return A(_lg,[_ly]);});}};return [1,B(_cR(_lt,_lv))];},_lA=new T(function(){var _lB=new T(function(){return B(A(_lg,[_kj]));}),_lC=new T(function(){return B(A(_lg,[_kc]));}),_lD=new T(function(){return B(A(_lg,[_k5]));}),_lE=new T(function(){return B(A(_lg,[_jY]));}),_lF=new T(function(){return B(A(_lg,[_jR]));}),_lG=new T(function(){return B(A(_lg,[_jK]));}),_lH=new T(function(){return B(A(_lg,[_jD]));}),_lI=new T(function(){return B(A(_lg,[_jw]));}),_lJ=new T(function(){return B(A(_lg,[_jp]));}),_lK=new T(function(){return B(A(_lg,[_ji]));}),_lL=new T(function(){return B(A(_lg,[_jb]));}),_lM=new T(function(){return B(A(_lg,[_j4]));}),_lN=new T(function(){return B(A(_lg,[_iX]));}),_lO=new T(function(){return B(A(_lg,[_iQ]));}),_lP=new T(function(){return B(A(_lg,[_iJ]));}),_lQ=new T(function(){return B(A(_lg,[_iC]));}),_lR=new T(function(){return B(A(_lg,[_iv]));}),_lS=new T(function(){return B(A(_lg,[_gM]));}),_lT=new T(function(){return B(A(_lg,[_hB]));}),_lU=new T(function(){return B(A(_lg,[_hu]));}),_lV=new T(function(){return B(A(_lg,[_hn]));}),_lW=new T(function(){return B(A(_lg,[_hg]));}),_lX=new T(function(){return B(A(_lg,[_h9]));}),_lY=new T(function(){return B(A(_lg,[_gT]));}),_lZ=new T(function(){return B(A(_lg,[_h2]));}),_m0=function(_m1){switch(E(_m1)){case 64:return E(_lZ);case 65:return E(_lY);case 66:return E(_lX);case 67:return E(_lW);case 68:return E(_lV);case 69:return E(_lU);case 70:return E(_lT);case 71:return E(_lh);case 72:return E(_li);case 73:return E(_lj);case 74:return E(_lk);case 75:return E(_ll);case 76:return E(_lm);case 77:return E(_ln);case 78:return E(_lS);case 79:return E(_lR);case 80:return E(_lQ);case 81:return E(_lP);case 82:return E(_lO);case 83:return E(_lN);case 84:return E(_lM);case 85:return E(_lL);case 86:return E(_lK);case 87:return E(_lJ);case 88:return E(_lI);case 89:return E(_lH);case 90:return E(_lG);case 91:return E(_lF);case 92:return E(_lE);case 93:return E(_lD);case 94:return E(_lC);case 95:return E(_lB);default:return [2];}},_m2=[0,_m0],_m3=new T(function(){return B(A(_la,[_lg]));}),_m4=function(_m5){return (E(_m5)==94)?E(_m2):[2];};return B(_aB([0,_m4],_m3));});return B(_aB([1,B(_c7(_g4,_g6,_ls))],_lA));}),_m6=function(_m7){switch(E(_m7)){case 34:return E(_lq);case 39:return E(_lp);case 92:return E(_lo);case 97:return E(_lh);case 98:return E(_li);case 102:return E(_lm);case 110:return E(_lk);case 114:return E(_ln);case 116:return E(_lj);case 118:return E(_ll);default:return [2];}};return new F(function(){return _aB([0,_m6],_lr);});},_m8=function(_m9){return new F(function(){return A(_m9,[_4i]);});},_ma=function(_mb){var _mc=E(_mb);if(!_mc[0]){return E(_m8);}else{var _md=_mc[2],_me=E(_mc[1]),_mf=_me>>>0,_mg=new T(function(){return B(_ma(_md));});if(_mf>887){var _mh=u_iswspace(_me);if(!E(_mh)){return E(_m8);}else{var _mi=function(_mj){var _mk=new T(function(){return B(A(_mg,[_mj]));});return [0,function(_ml){return E(_mk);}];};return E(_mi);}}else{var _mm=E(_mf);if(_mm==32){var _mn=function(_mo){var _mp=new T(function(){return B(A(_mg,[_mo]));});return [0,function(_mq){return E(_mp);}];};return E(_mn);}else{if(_mm-9>>>0>4){if(E(_mm)==160){var _mr=function(_ms){var _mt=new T(function(){return B(A(_mg,[_ms]));});return [0,function(_mu){return E(_mt);}];};return E(_mr);}else{return E(_m8);}}else{var _mv=function(_mw){var _mx=new T(function(){return B(A(_mg,[_mw]));});return [0,function(_my){return E(_mx);}];};return E(_mv);}}}}},_mz=function(_mA){var _mB=new T(function(){return B(_mz(_mA));}),_mC=function(_mD){return (E(_mD)==92)?E(_mB):[2];},_mE=[0,_mC],_mF=function(_mG){return E(_mE);},_mH=function(_mI){return new F(function(){return A(_ma,[_mI,_mF]);});},_mJ=[1,_mH],_mK=new T(function(){var _mL=function(_mM){return new F(function(){return A(_mA,[[0,_mM,_fY]]);});};return B(_lf(_mL));}),_mN=function(_mO){var _mP=E(_mO);if(_mP==38){return E(_mB);}else{var _mQ=_mP>>>0;if(_mQ>887){var _mR=u_iswspace(_mP);return (E(_mR)==0)?[2]:E(_mJ);}else{var _mS=E(_mQ);return (_mS==32)?E(_mJ):(_mS-9>>>0>4)?(E(_mS)==160)?E(_mJ):[2]:E(_mJ);}}},_mT=[0,_mN],_mU=function(_mV){var _mW=E(_mV);if(E(_mW)==92){return E(_mK);}else{return new F(function(){return A(_mA,[[0,_mW,_fX]]);});}},_mX=function(_mY){return (E(_mY)==92)?E(_mT):[2];};return new F(function(){return _aB([0,_mX],[0,_mU]);});},_mZ=function(_n0,_n1){var _n2=new T(function(){var _n3=new T(function(){return B(A(_n0,[_F]));});return B(A(_n1,[[1,_n3]]));}),_n4=function(_n5){var _n6=E(_n5),_n7=E(_n6[1]);if(E(_n7)==34){if(!E(_n6[2])){return E(_n2);}else{var _n8=function(_n9){return new F(function(){return A(_n0,[[1,_n7,_n9]]);});};return new F(function(){return _mZ(_n8,_n1);});}}else{var _na=function(_nb){return new F(function(){return A(_n0,[[1,_n7,_nb]]);});};return new F(function(){return _mZ(_na,_n1);});}};return new F(function(){return _mz(_n4);});},_nc=new T(function(){return B(unCStr("_\'"));}),_nd=function(_ne){var _nf=u_iswalnum(_ne);if(!E(_nf)){return new F(function(){return _fP(_bx,_ne,_nc);});}else{return true;}},_ng=function(_nh){return new F(function(){return _nd(E(_nh));});},_ni=new T(function(){return B(unCStr(",;()[]{}`"));}),_nj=new T(function(){return B(unCStr("=>"));}),_nk=[1,_nj,_F],_nl=new T(function(){return B(unCStr("~"));}),_nm=[1,_nl,_nk],_nn=new T(function(){return B(unCStr("@"));}),_no=[1,_nn,_nm],_np=new T(function(){return B(unCStr("->"));}),_nq=[1,_np,_no],_nr=new T(function(){return B(unCStr("<-"));}),_ns=[1,_nr,_nq],_nt=new T(function(){return B(unCStr("|"));}),_nu=[1,_nt,_ns],_nv=new T(function(){return B(unCStr("\\"));}),_nw=[1,_nv,_nu],_nx=new T(function(){return B(unCStr("="));}),_ny=[1,_nx,_nw],_nz=new T(function(){return B(unCStr("::"));}),_nA=[1,_nz,_ny],_nB=new T(function(){return B(unCStr(".."));}),_nC=[1,_nB,_nA],_nD=function(_nE){var _nF=new T(function(){return B(A(_nE,[_cO]));}),_nG=new T(function(){var _nH=new T(function(){var _nI=function(_nJ){var _nK=new T(function(){return B(A(_nE,[[0,_nJ]]));});return [0,function(_nL){return (E(_nL)==39)?E(_nK):[2];}];};return B(_lf(_nI));}),_nM=function(_nN){var _nO=E(_nN);switch(E(_nO)){case 39:return [2];case 92:return E(_nH);default:var _nP=new T(function(){return B(A(_nE,[[0,_nO]]));});return [0,function(_nQ){return (E(_nQ)==39)?E(_nP):[2];}];}},_nR=[0,_nM],_nS=new T(function(){var _nT=new T(function(){return B(_mZ(_2,_nE));}),_nU=new T(function(){var _nV=new T(function(){var _nW=new T(function(){var _nX=new T(function(){return [1,B(_c7(_e2,_fL,_nE))];}),_nY=function(_nZ){var _o0=E(_nZ),_o1=u_iswalpha(_o0);if(!E(_o1)){if(E(_o0)==95){var _o2=function(_o3){return new F(function(){return A(_nE,[[3,[1,_o0,_o3]]]);});};return [1,B(_cy(_ng,_o2))];}else{return [2];}}else{var _o4=function(_o5){return new F(function(){return A(_nE,[[3,[1,_o0,_o5]]]);});};return [1,B(_cy(_ng,_o4))];}};return B(_aB([0,_nY],_nX));}),_o6=function(_o7){if(!B(_fP(_bx,_o7,_fU))){return [2];}else{var _o8=function(_o9){var _oa=[1,_o7,_o9];if(!B(_fP(_bG,_oa,_nC))){return new F(function(){return A(_nE,[[4,_oa]]);});}else{return new F(function(){return A(_nE,[[2,_oa]]);});}};return [1,B(_cy(_fV,_o8))];}};return B(_aB([0,_o6],_nW));}),_ob=function(_oc){if(!B(_fP(_bx,_oc,_ni))){return [2];}else{return new F(function(){return A(_nE,[[2,[1,_oc,_F]]]);});}};return B(_aB([0,_ob],_nV));}),_od=function(_oe){return (E(_oe)==34)?E(_nT):[2];};return B(_aB([0,_od],_nU));}),_of=function(_og){return (E(_og)==39)?E(_nR):[2];};return B(_aB([0,_of],_nS));}),_oh=function(_oi){return (E(_oi)[0]==0)?E(_nF):[2];};return new F(function(){return _aB([1,_oh],_nG);});},_oj=function(_ok,_ol,_om){var _on=E(_ok);if(!_on[0]){return [2];}else{var _oo=_on[2],_op=E(_on[1]),_oq=_op[1],_or=_op[2],_os=new T(function(){return B(A(_or,[_ol,_om]));}),_ot=function(_ou){var _ov=E(_ou);switch(_ov[0]){case 3:return (!B(_bm(_oq,_ov[1])))?[2]:E(_os);case 4:return (!B(_bm(_oq,_ov[1])))?[2]:E(_os);default:return [2];}},_ow=new T(function(){return B(_nD(_ot));}),_ox=function(_oy){return E(_ow);},_oz=new T(function(){return B(_oj(_oo,_ol,_om));}),_oA=function(_oB){return new F(function(){return A(_ma,[_oB,_ox]);});};return new F(function(){return _aB([1,_oA],_oz);});}},_oC=function(_oD,_oE){return new F(function(){return _oj(_an,_oD,_oE);});},_oF=new T(function(){return B(unCStr("("));}),_oG=new T(function(){return B(unCStr(")"));}),_oH=0,_oI=function(_oJ,_oK){var _oL=new T(function(){var _oM=new T(function(){var _oN=function(_oO){var _oP=new T(function(){var _oQ=new T(function(){return B(A(_oK,[_oO]));}),_oR=function(_oS){var _oT=E(_oS);return (_oT[0]==2)?(!B(_bm(_oT[1],_oG)))?[2]:E(_oQ):[2];};return B(_nD(_oR));}),_oU=function(_oV){return E(_oP);};return [1,function(_oW){return new F(function(){return A(_ma,[_oW,_oU]);});}];};return B(A(_oJ,[_oH,_oN]));}),_oX=function(_oY){var _oZ=E(_oY);return (_oZ[0]==2)?(!B(_bm(_oZ[1],_oF)))?[2]:E(_oM):[2];};return B(_nD(_oX));}),_p0=function(_p1){return E(_oL);};return function(_p2){return new F(function(){return A(_ma,[_p2,_p0]);});};},_p3=function(_p4,_p5){var _p6=function(_p7){var _p8=new T(function(){return B(A(_p4,[_p7]));}),_p9=function(_pa){var _pb=new T(function(){return [1,B(_oI(_p6,_pa))];});return new F(function(){return _aB(B(A(_p8,[_pa])),_pb);});};return E(_p9);},_pc=new T(function(){return B(A(_p4,[_p5]));}),_pd=function(_pe){var _pf=new T(function(){return [1,B(_oI(_p6,_pe))];});return new F(function(){return _aB(B(A(_pc,[_pe])),_pf);});};return E(_pd);},_pg=function(_ph){var _pi=[3,_ph,_bY],_pj=function(_pk){return E(_pi);};return [1,function(_pl){return new F(function(){return A(_ma,[_pl,_pj]);});}];},_pm=new T(function(){return B(A(_p3,[_oC,_oH,_pg]));}),_pn=new T(function(){return B(err(_aa));}),_po=new T(function(){return B(err(_ac));}),_pp=function(_pq,_pr){var _ps=function(_pt,_pu){var _pv=function(_pw){var _px=new T(function(){return  -E(_pw);});return new F(function(){return A(_pu,[_px]);});},_py=function(_pz){return new F(function(){return A(_pq,[_pz,_pt,_pv]);});},_pA=new T(function(){return B(_nD(_py));}),_pB=function(_pC){return E(_pA);},_pD=function(_pE){return new F(function(){return A(_ma,[_pE,_pB]);});},_pF=[1,_pD],_pG=function(_pH){var _pI=E(_pH);if(_pI[0]==4){var _pJ=E(_pI[1]);if(!_pJ[0]){return new F(function(){return A(_pq,[_pI,_pt,_pu]);});}else{if(E(_pJ[1])==45){if(!E(_pJ[2])[0]){return E(_pF);}else{return new F(function(){return A(_pq,[_pI,_pt,_pu]);});}}else{return new F(function(){return A(_pq,[_pI,_pt,_pu]);});}}}else{return new F(function(){return A(_pq,[_pI,_pt,_pu]);});}},_pK=new T(function(){return B(_nD(_pG));}),_pL=function(_pM){return E(_pK);};return [1,function(_pN){return new F(function(){return A(_ma,[_pN,_pL]);});}];};return new F(function(){return _p3(_ps,_pr);});},_pO=function(_pP){var _pQ=E(_pP);if(!_pQ[0]){var _pR=_pQ[1],_pS=_pQ[2];return [1,new T(function(){var _pT=new T(function(){return B(_eq(_pS,0));},1),_pU=new T(function(){return B(_ev(E(_pR)));});return B(_eR(_pU,_pT,B(_5d(_ex,_pS))));})];}else{var _pV=_pQ[1];if(!E(_pQ[2])[0]){if(!E(_pQ[3])[0]){return [1,new T(function(){return B(_f7(_ep,_pV));})];}else{return [0];}}else{return [0];}}},_pW=function(_pX,_pY){return [2];},_pZ=function(_q0){var _q1=E(_q0);if(_q1[0]==5){var _q2=B(_pO(_q1[1]));if(!_q2[0]){return E(_pW);}else{var _q3=_q2[1],_q4=new T(function(){return B(_gb(_q3));}),_q5=function(_q6,_q7){return new F(function(){return A(_q7,[_q4]);});};return E(_q5);}}else{return E(_pW);}},_q8=new T(function(){return B(unCStr("="));}),_q9=new T(function(){return B(unCStr("onPointIndex"));}),_qa=new T(function(){return B(unCStr(","));}),_qb=new T(function(){return B(unCStr("pointIndex"));}),_qc=new T(function(){return B(unCStr("{"));}),_qd=new T(function(){return B(unCStr("PointPlacement"));}),_qe=new T(function(){return B(unCStr("onBarIndex"));}),_qf=new T(function(){return B(unCStr("BarPlacement"));}),_qg=new T(function(){return B(unCStr("onSideIndex"));}),_qh=new T(function(){return B(unCStr("LeftSidePlacement"));}),_qi=new T(function(){return B(unCStr("RightSidePlacement"));}),_qj=function(_qk,_ql){var _qm=new T(function(){var _qn=new T(function(){var _qo=new T(function(){if(_qk>11){return [2];}else{var _qp=new T(function(){var _qq=new T(function(){var _qr=new T(function(){var _qs=new T(function(){var _qt=new T(function(){var _qu=function(_qv){var _qw=new T(function(){var _qx=new T(function(){return B(A(_ql,[[3,_qv]]));}),_qy=function(_qz){var _qA=E(_qz);return (_qA[0]==2)?(!B(_bm(_qA[1],_4l)))?[2]:E(_qx):[2];};return B(_nD(_qy));}),_qB=function(_qC){return E(_qw);};return [1,function(_qD){return new F(function(){return A(_ma,[_qD,_qB]);});}];};return B(A(_pp,[_pZ,_oH,_qu]));}),_qE=function(_qF){var _qG=E(_qF);return (_qG[0]==2)?(!B(_bm(_qG[1],_q8)))?[2]:E(_qt):[2];};return B(_nD(_qE));}),_qH=function(_qI){return E(_qs);},_qJ=function(_qK){return new F(function(){return A(_ma,[_qK,_qH]);});},_qL=[1,_qJ],_qM=function(_qN){var _qO=E(_qN);return (_qO[0]==3)?(!B(_bm(_qO[1],_qg)))?[2]:E(_qL):[2];};return B(_nD(_qM));}),_qP=function(_qQ){return E(_qr);},_qR=function(_qS){return new F(function(){return A(_ma,[_qS,_qP]);});},_qT=[1,_qR],_qU=function(_qV){var _qW=E(_qV);return (_qW[0]==2)?(!B(_bm(_qW[1],_qc)))?[2]:E(_qT):[2];};return B(_nD(_qU));}),_qX=function(_qY){return E(_qq);},_qZ=function(_r0){return new F(function(){return A(_ma,[_r0,_qX]);});},_r1=[1,_qZ],_r2=function(_r3){var _r4=E(_r3);return (_r4[0]==3)?(!B(_bm(_r4[1],_qi)))?[2]:E(_r1):[2];};return B(_nD(_r2));}),_r5=function(_r6){return E(_qp);};return [1,function(_r7){return new F(function(){return A(_ma,[_r7,_r5]);});}];}});if(_qk>11){return B(_aB(_bY,_qo));}else{var _r8=new T(function(){var _r9=new T(function(){var _ra=new T(function(){var _rb=new T(function(){var _rc=new T(function(){var _rd=function(_re){var _rf=new T(function(){var _rg=new T(function(){return B(A(_ql,[[2,_re]]));}),_rh=function(_ri){var _rj=E(_ri);return (_rj[0]==2)?(!B(_bm(_rj[1],_4l)))?[2]:E(_rg):[2];};return B(_nD(_rh));}),_rk=function(_rl){return E(_rf);};return [1,function(_rm){return new F(function(){return A(_ma,[_rm,_rk]);});}];};return B(A(_pp,[_pZ,_oH,_rd]));}),_rn=function(_ro){var _rp=E(_ro);return (_rp[0]==2)?(!B(_bm(_rp[1],_q8)))?[2]:E(_rc):[2];};return B(_nD(_rn));}),_rq=function(_rr){return E(_rb);},_rs=function(_rt){return new F(function(){return A(_ma,[_rt,_rq]);});},_ru=[1,_rs],_rv=function(_rw){var _rx=E(_rw);return (_rx[0]==3)?(!B(_bm(_rx[1],_qg)))?[2]:E(_ru):[2];};return B(_nD(_rv));}),_ry=function(_rz){return E(_ra);},_rA=function(_rB){return new F(function(){return A(_ma,[_rB,_ry]);});},_rC=[1,_rA],_rD=function(_rE){var _rF=E(_rE);return (_rF[0]==2)?(!B(_bm(_rF[1],_qc)))?[2]:E(_rC):[2];};return B(_nD(_rD));}),_rG=function(_rH){return E(_r9);},_rI=function(_rJ){return new F(function(){return A(_ma,[_rJ,_rG]);});},_rK=[1,_rI],_rL=function(_rM){var _rN=E(_rM);return (_rN[0]==3)?(!B(_bm(_rN[1],_qh)))?[2]:E(_rK):[2];};return B(_nD(_rL));}),_rO=function(_rP){return E(_r8);},_rQ=function(_rR){return new F(function(){return A(_ma,[_rR,_rO]);});};return B(_aB([1,_rQ],_qo));}});if(_qk>11){return B(_aB(_bY,_qn));}else{var _rS=new T(function(){var _rT=new T(function(){var _rU=new T(function(){var _rV=new T(function(){var _rW=new T(function(){var _rX=function(_rY){var _rZ=new T(function(){var _s0=new T(function(){return B(A(_ql,[[1,_rY]]));}),_s1=function(_s2){var _s3=E(_s2);return (_s3[0]==2)?(!B(_bm(_s3[1],_4l)))?[2]:E(_s0):[2];};return B(_nD(_s1));}),_s4=function(_s5){return E(_rZ);};return [1,function(_s6){return new F(function(){return A(_ma,[_s6,_s4]);});}];};return B(A(_pp,[_pZ,_oH,_rX]));}),_s7=function(_s8){var _s9=E(_s8);return (_s9[0]==2)?(!B(_bm(_s9[1],_q8)))?[2]:E(_rW):[2];};return B(_nD(_s7));}),_sa=function(_sb){return E(_rV);},_sc=function(_sd){return new F(function(){return A(_ma,[_sd,_sa]);});},_se=[1,_sc],_sf=function(_sg){var _sh=E(_sg);return (_sh[0]==3)?(!B(_bm(_sh[1],_qe)))?[2]:E(_se):[2];};return B(_nD(_sf));}),_si=function(_sj){return E(_rU);},_sk=function(_sl){return new F(function(){return A(_ma,[_sl,_si]);});},_sm=[1,_sk],_sn=function(_so){var _sp=E(_so);return (_sp[0]==2)?(!B(_bm(_sp[1],_qc)))?[2]:E(_sm):[2];};return B(_nD(_sn));}),_sq=function(_sr){return E(_rT);},_ss=function(_st){return new F(function(){return A(_ma,[_st,_sq]);});},_su=[1,_ss],_sv=function(_sw){var _sx=E(_sw);return (_sx[0]==3)?(!B(_bm(_sx[1],_qf)))?[2]:E(_su):[2];};return B(_nD(_sv));}),_sy=function(_sz){return E(_rS);},_sA=function(_sB){return new F(function(){return A(_ma,[_sB,_sy]);});};return B(_aB([1,_sA],_qn));}});if(_qk>11){return new F(function(){return _aB(_bY,_qm);});}else{var _sC=new T(function(){var _sD=new T(function(){var _sE=new T(function(){var _sF=new T(function(){var _sG=new T(function(){var _sH=function(_sI){var _sJ=new T(function(){var _sK=new T(function(){var _sL=new T(function(){var _sM=new T(function(){var _sN=function(_sO){var _sP=new T(function(){var _sQ=new T(function(){return B(A(_ql,[[0,_sI,_sO]]));}),_sR=function(_sS){var _sT=E(_sS);return (_sT[0]==2)?(!B(_bm(_sT[1],_4l)))?[2]:E(_sQ):[2];};return B(_nD(_sR));}),_sU=function(_sV){return E(_sP);};return [1,function(_sW){return new F(function(){return A(_ma,[_sW,_sU]);});}];};return B(A(_pp,[_pZ,_oH,_sN]));}),_sX=function(_sY){var _sZ=E(_sY);return (_sZ[0]==2)?(!B(_bm(_sZ[1],_q8)))?[2]:E(_sM):[2];};return B(_nD(_sX));}),_t0=function(_t1){return E(_sL);},_t2=function(_t3){return new F(function(){return A(_ma,[_t3,_t0]);});},_t4=[1,_t2],_t5=function(_t6){var _t7=E(_t6);return (_t7[0]==3)?(!B(_bm(_t7[1],_q9)))?[2]:E(_t4):[2];};return B(_nD(_t5));}),_t8=function(_t9){return E(_sK);},_ta=function(_tb){return new F(function(){return A(_ma,[_tb,_t8]);});},_tc=[1,_ta],_td=function(_te){var _tf=E(_te);return (_tf[0]==2)?(!B(_bm(_tf[1],_qa)))?[2]:E(_tc):[2];};return B(_nD(_td));}),_tg=function(_th){return E(_sJ);};return [1,function(_ti){return new F(function(){return A(_ma,[_ti,_tg]);});}];};return B(A(_pp,[_pZ,_oH,_sH]));}),_tj=function(_tk){var _tl=E(_tk);return (_tl[0]==2)?(!B(_bm(_tl[1],_q8)))?[2]:E(_sG):[2];};return B(_nD(_tj));}),_tm=function(_tn){return E(_sF);},_to=function(_tp){return new F(function(){return A(_ma,[_tp,_tm]);});},_tq=[1,_to],_tr=function(_ts){var _tt=E(_ts);return (_tt[0]==3)?(!B(_bm(_tt[1],_qb)))?[2]:E(_tq):[2];};return B(_nD(_tr));}),_tu=function(_tv){return E(_sE);},_tw=function(_tx){return new F(function(){return A(_ma,[_tx,_tu]);});},_ty=[1,_tw],_tz=function(_tA){var _tB=E(_tA);return (_tB[0]==2)?(!B(_bm(_tB[1],_qc)))?[2]:E(_ty):[2];};return B(_nD(_tz));}),_tC=function(_tD){return E(_sD);},_tE=function(_tF){return new F(function(){return A(_ma,[_tF,_tC]);});},_tG=[1,_tE],_tH=function(_tI){var _tJ=E(_tI);return (_tJ[0]==3)?(!B(_bm(_tJ[1],_qd)))?[2]:E(_tG):[2];};return B(_nD(_tH));}),_tK=function(_tL){return E(_sC);},_tM=function(_tN){return new F(function(){return A(_ma,[_tN,_tK]);});};return new F(function(){return _aB([1,_tM],_qm);});}},_tO=function(_tP,_tQ){return new F(function(){return _qj(E(_tP),_tQ);});},_tR=new T(function(){return B(A(_p3,[_tO,_oH,_pg]));}),_tS=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:247:9-15"));}),_tT=[0,_2z,_2A,_F,_tS,_2z,_2z],_tU=new T(function(){return B(_2x(_tT));}),_tV=new T(function(){return B(unCStr("joinGame"));}),_tW=function(_tX){return E(E(_tX)[1]);},_tY=function(_tZ){return E(E(_tZ)[1]);},_u0=function(_u1){return E(E(_u1)[2]);},_u2=function(_u3){return E(E(_u3)[2]);},_u4=function(_u5){return E(E(_u5)[1]);},_u6=function(_){return new F(function(){return nMV(_2z);});},_u7=new T(function(){return B(_8x(_u6));}),_u8=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_u9=function(_ua){return E(E(_ua)[2]);},_ub=function(_uc){return E(E(_uc)[4]);},_ud=function(_ue,_uf,_ug,_uh,_ui,_uj){var _uk=B(_tW(_ue)),_ul=B(_tY(_uk)),_um=new T(function(){return B(_5n(_uk));}),_un=new T(function(){return B(_ub(_ul));}),_uo=new T(function(){return B(A(_5l,[_uf,_uh]));}),_up=new T(function(){return B(A(_u4,[_ug,_ui]));}),_uq=function(_ur){return new F(function(){return A(_un,[[0,_up,_uo,_ur]]);});},_us=function(_ut){var _uu=new T(function(){var _uv=new T(function(){var _uw=E(_uo),_ux=E(_up),_uy=E(_ut),_uz=function(_uA,_){var _uB=B(A(_uy,[_uA,_]));return _8B;},_uC=__createJSFunc(2,E(_uz)),_uD=_uC,_uE=function(_){return new F(function(){return E(_u8)(_uw,_ux,_uD);});};return E(_uE);});return B(A(_um,[_uv]));});return new F(function(){return A(_u0,[_ul,_uu,_uq]);});},_uF=new T(function(){var _uG=new T(function(){return B(_5n(_uk));}),_uH=function(_uI){var _uJ=new T(function(){var _uK=function(_){var _=wMV(E(_u7),[1,_uI]);return new F(function(){return A(_u2,[_ug,_ui,_uI,_]);});};return B(A(_uG,[_uK]));});return new F(function(){return A(_u0,[_ul,_uJ,_uj]);});};return B(A(_u9,[_ue,_uH]));});return new F(function(){return A(_u0,[_ul,_uF,_us]);});},_uL=function(_uM,_uN){var _uO=E(_uN);if(!_uO[0]){return [0];}else{var _uP=_uO[1],_uQ=_uO[2],_uR=E(_uM);if(_uR==1){return [1,_uP,_F];}else{var _uS=new T(function(){return B(_uL(_uR-1|0,_uQ));});return [1,_uP,_uS];}}},_uT=function(_uU,_uV,_uW){if(_uW<=_uV){var _uX=new T(function(){var _uY=_uV-_uU|0,_uZ=_uW-_uY|0,_v0=function(_v1){if(_v1>=_uZ){var _v2=new T(function(){return B(_v0(_v1+_uY|0));});return [1,_v1,_v2];}else{return [1,_v1,_F];}};return B(_v0(_uV));});return [1,_uU,_uX];}else{return (_uW<=_uU)?[1,_uU,_F]:[0];}},_v3=function(_v4,_v5,_v6){if(_v6>=_v5){var _v7=new T(function(){var _v8=_v5-_v4|0,_v9=_v6-_v8|0,_va=function(_vb){if(_vb<=_v9){var _vc=new T(function(){return B(_va(_vb+_v8|0));});return [1,_vb,_vc];}else{return [1,_vb,_F];}};return B(_va(_v5));});return [1,_v4,_v7];}else{return (_v6>=_v4)?[1,_v4,_F]:[0];}},_vd=function(_ve,_vf){if(_vf<_ve){return new F(function(){return _uT(_ve,_vf,-2147483648);});}else{return new F(function(){return _v3(_ve,_vf,2147483647);});}},_vg=new T(function(){return B(_vd(135,150));}),_vh=new T(function(){return B(_uL(6,_vg));}),_vi=function(_vj,_vk){var _vl=E(_vj);if(!_vl[0]){return E(_vh);}else{var _vm=_vl[1],_vn=_vl[2],_vo=E(_vk);if(_vo==1){return [1,_vm,_vh];}else{var _vp=new T(function(){return B(_vi(_vn,_vo-1|0));});return [1,_vm,_vp];}}},_vq=new T(function(){return B(_vd(25,40));}),_vr=new T(function(){return B(_vi(_vq,6));}),_vs=function(_vt){while(1){var _vu=(function(_vv){var _vw=E(_vv);if(!_vw[0]){return [0];}else{var _vx=_vw[2],_vy=E(_vw[1]);if(!E(_vy[2])[0]){var _vz=new T(function(){return B(_vs(_vx));});return [1,_vy[1],_vz];}else{_vt=_vx;return null;}}})(_vt);if(_vu!=null){return _vu;}}},_vA=function(_vB,_vC){var _vD=E(_vC);if(!_vD[0]){return [0,_F,_F];}else{var _vE=_vD[1],_vF=_vD[2];if(!B(A(_vB,[_vE]))){var _vG=new T(function(){var _vH=B(_vA(_vB,_vF));return [0,_vH[1],_vH[2]];}),_vI=new T(function(){return E(E(_vG)[2]);}),_vJ=new T(function(){return E(E(_vG)[1]);});return [0,[1,_vE,_vJ],_vI];}else{return [0,_F,_vD];}}},_vK=function(_vL,_vM){while(1){var _vN=E(_vM);if(!_vN[0]){return [0];}else{if(!B(A(_vL,[_vN[1]]))){return E(_vN);}else{_vM=_vN[2];continue;}}}},_vO=function(_vP){var _vQ=_vP>>>0;if(_vQ>887){var _vR=u_iswspace(_vP);return (E(_vR)==0)?false:true;}else{var _vS=E(_vQ);return (_vS==32)?true:(_vS-9>>>0>4)?(E(_vS)==160)?true:false:true;}},_vT=function(_vU){return new F(function(){return _vO(E(_vU));});},_vV=function(_vW){var _vX=B(_vK(_vT,_vW));if(!_vX[0]){return [0];}else{var _vY=new T(function(){var _vZ=B(_vA(_vT,_vX));return [0,_vZ[1],_vZ[2]];}),_w0=new T(function(){return B(_vV(E(_vY)[2]));}),_w1=new T(function(){return E(E(_vY)[1]);});return [1,_w1,_w0];}},_w2=function(_w3,_){var _w4=jsFind(toJSStr(E(_tV)));if(!_w4[0]){return new F(function(){return die(_tU);});}else{var _w5=B(A(_ud,[_9a,_4,_98,_w4[1],_9q,_9P,_])),_w6=function(_w7,_w8,_w9,_){var _wa=E(_w3),_wb=_wa[1],_wc=_wa[2],_wd=_wa[3],_we=_wa[4],_wf=_wa[5],_wg=_wa[6],_wh=_wa[7],_wi=new T(function(){return B(_vV(fromJSStr(E(_w7))));}),_wj=new T(function(){return B(_5d(_a7,B(_9n(_wi,2))));}),_wk=B(_vs(B(_ap(_tR,_wj))));if(!_wk[0]){return E(_pn);}else{if(!E(_wk[2])[0]){var _wl=E(_wk[1]);if(!_wl[0]){var _wm=_wl[1],_wn=_wl[2],_wo=function(_wp){var _wq=E(_wp)-E(_w8);return (_wq==0)?true:(_wq<=0)? -_wq<7:_wq<7;},_wr=B(_9S(_wo,_vr));if(!_wr[0]){return new F(function(){return _9y(_wl,_wl,_wg,_);});}else{var _ws=_wr[1],_wt=function(_wu,_wv){var _ww=E(_wm),_wx=_ww;if(_wu<=_wx){return new F(function(){return _9y(_wl,_wl,_wg,_);});}else{var _wy=B(_9n(_wb,_wu)),_wz=_wy[2],_wA=new T(function(){return B(_9n(_wi,1));}),_wB=B(_vs(B(_ap(_pm,_wA))));if(!_wB[0]){return E(_ab);}else{var _wC=_wB[1];if(!E(_wB[2])[0]){var _wD=function(_){var _wE=B(_9y(_wl,[0,_wv,_wz],_wg,_)),_wF=new T(function(){return E(B(_9n(_wb,_wx))[1]);}),_wG=function(_wH,_wI){var _wJ=E(_wH);if(!_wJ[0]){return [0];}else{var _wK=_wJ[1],_wL=_wJ[2],_wM=E(_wI);if(!_wM[0]){return [0];}else{var _wN=_wM[1],_wO=_wM[2],_wP=new T(function(){return B(_wG(_wL,_wO));}),_wQ=new T(function(){var _wR=E(_wK);if(_wR!=_wx){if(_wR!=_wu){return E(_wN);}else{var _wS=new T(function(){return E(E(_wN)[2])+1|0;});return [0,_wF,_wS];}}else{var _wT=new T(function(){return E(E(_wN)[2])-1|0;}),_wU=new T(function(){return E(E(_wN)[1]);});return [0,_wU,_wT];}});return [1,_wQ,_wP];}}},_wV=B(_wG(_5O,_wb)),_wW=function(_wX,_){while(1){var _wY=(function(_wZ,_){var _x0=E(_wZ);if(!_x0[0]){return _4i;}else{var _x1=_x0[1],_x2=new T(function(){return E(_x1)-1|0;}),_x3=B(_9y([0,_ww,_x1],[0,_ww,_x2],_wg,_));_wX=_x0[2];return null;}})(_wX,_);if(_wY!=null){return _wY;}}},_x4=function(_x5,_x6){while(1){var _x7=E(_x6);if(!_x7[0]){return [0];}else{var _x8=_x7[2],_x9=E(_x5);if(_x9==1){return E(_x8);}else{_x5=_x9-1|0;_x6=_x8;continue;}}}},_xa=B(_wW(B(_x4(1,B(_5I(E(_wn),E(B(_9n(_wV,_wx))[2]))))),_));return new F(function(){return _w2([0,_wV,_wc,_wd,_we,_wf,_wg,_wh],_);});},_xb=function(_){if(E(_wz)>=2){return new F(function(){return _9y(_wl,_wl,_wg,_);});}else{return new F(function(){return _wD(_);});}};if(!E(_wy[1])){if(!E(_wC)){return new F(function(){return _wD(_);});}else{return new F(function(){return _xb(_);});}}else{if(!E(_wC)){return new F(function(){return _xb(_);});}else{return new F(function(){return _wD(_);});}}}else{return E(_ad);}}}};if(E(_w9)<=E(_a6)){var _xc=E(_ws);return new F(function(){return _wt(_xc,_xc);});}else{var _xd=23-E(_ws)|0;return new F(function(){return _wt(_xd,_xd);});}}}else{return new F(function(){return _9y(_wl,_wl,_wg,_);});}}else{return E(_po);}}},_xe=E(_9R)(E(_w6));return new F(function(){return _99(_);});}},_xf=new T(function(){return B(unCStr("You have not joined a game (yet)."));}),_xg=new T(function(){return B(unCStr("innerHTML"));}),_xh=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:267:9-15"));}),_xi=[0,_2z,_2A,_F,_xh,_2z,_2z],_xj=new T(function(){return B(_2x(_xi));}),_xk=function(_xl,_xm,_xn,_xo,_xp){var _xq=function(_){var _xr=jsSet(B(A(_5l,[_xl,_xn])),toJSStr(E(_xo)),toJSStr(E(_xp)));return _4i;};return new F(function(){return A(_5n,[_xm,_xq]);});},_xs=function(_){var _xt=jsFind("HintText");if(!_xt[0]){return new F(function(){return die(_xj);});}else{var _xu=B(A(_xk,[_4,_2I,_xt[1],_xg,_xf,_])),_xv=E(_7D),_xw=B(_5Z(_6r,_6r,_xv,_)),_xx=B(_5Z(_6q,_6r,_xv,_));return new F(function(){return _w2(_7E,_);});}},_xy=function(_){return new F(function(){return _xs(_);});};
var hasteMain = function() {B(A(_xy, [0]));};window.onload = hasteMain;