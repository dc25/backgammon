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

var _0=function(_1,_){return [1,_1];},_2=function(_3){return E(_3);},_4=[0,_2,_0],_5=function(_6,_7,_){var _8=B(A(_6,[_])),_9=B(A(_7,[_]));return _8;},_a=function(_b,_c,_){var _d=B(A(_b,[_])),_e=_d,_f=B(A(_c,[_])),_g=_f;return new T(function(){return B(A(_e,[_g]));});},_h=function(_i,_j,_){var _k=B(A(_j,[_]));return _i;},_l=function(_m,_n,_){var _o=B(A(_n,[_])),_p=_o;return new T(function(){return B(A(_m,[_p]));});},_q=[0,_l,_h],_r=function(_s,_){return _s;},_t=function(_u,_v,_){var _w=B(A(_u,[_]));return new F(function(){return A(_v,[_]);});},_x=[0,_q,_r,_a,_t,_5],_y=function(_z,_A,_){var _B=B(A(_z,[_]));return new F(function(){return A(_A,[_B,_]);});},_C=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_D=new T(function(){return B(unCStr("base"));}),_E=new T(function(){return B(unCStr("IOException"));}),_F=[0],_G=new T(function(){var _H=hs_wordToWord64(4053623282),_I=hs_wordToWord64(3693590983);return [0,_H,_I,[0,_H,_I,_D,_C,_E],_F,_F];}),_J=function(_K){return E(_G);},_L=function(_M){return E(E(_M)[1]);},_N=function(_O,_P,_Q){var _R=B(A(_O,[_])),_S=B(A(_P,[_])),_T=hs_eqWord64(_R[1],_S[1]);if(!_T){return [0];}else{var _U=hs_eqWord64(_R[2],_S[2]);return (!_U)?[0]:[1,_Q];}},_V=function(_W){var _X=E(_W);return new F(function(){return _N(B(_L(_X[1])),_J,_X[2]);});},_Y=new T(function(){return B(unCStr(": "));}),_Z=new T(function(){return B(unCStr(")"));}),_10=new T(function(){return B(unCStr(" ("));}),_11=function(_12,_13){var _14=E(_12);if(!_14[0]){return E(_13);}else{var _15=_14[2],_16=new T(function(){return B(_11(_15,_13));});return [1,_14[1],_16];}},_17=new T(function(){return B(unCStr("interrupted"));}),_18=new T(function(){return B(unCStr("system error"));}),_19=new T(function(){return B(unCStr("unsatisified constraints"));}),_1a=new T(function(){return B(unCStr("user error"));}),_1b=new T(function(){return B(unCStr("permission denied"));}),_1c=new T(function(){return B(unCStr("illegal operation"));}),_1d=new T(function(){return B(unCStr("end of file"));}),_1e=new T(function(){return B(unCStr("resource exhausted"));}),_1f=new T(function(){return B(unCStr("resource busy"));}),_1g=new T(function(){return B(unCStr("does not exist"));}),_1h=new T(function(){return B(unCStr("already exists"));}),_1i=new T(function(){return B(unCStr("resource vanished"));}),_1j=new T(function(){return B(unCStr("timeout"));}),_1k=new T(function(){return B(unCStr("unsupported operation"));}),_1l=new T(function(){return B(unCStr("hardware fault"));}),_1m=new T(function(){return B(unCStr("inappropriate type"));}),_1n=new T(function(){return B(unCStr("invalid argument"));}),_1o=new T(function(){return B(unCStr("failed"));}),_1p=new T(function(){return B(unCStr("protocol error"));}),_1q=function(_1r,_1s){switch(E(_1r)){case 0:return new F(function(){return _11(_1h,_1s);});break;case 1:return new F(function(){return _11(_1g,_1s);});break;case 2:return new F(function(){return _11(_1f,_1s);});break;case 3:return new F(function(){return _11(_1e,_1s);});break;case 4:return new F(function(){return _11(_1d,_1s);});break;case 5:return new F(function(){return _11(_1c,_1s);});break;case 6:return new F(function(){return _11(_1b,_1s);});break;case 7:return new F(function(){return _11(_1a,_1s);});break;case 8:return new F(function(){return _11(_19,_1s);});break;case 9:return new F(function(){return _11(_18,_1s);});break;case 10:return new F(function(){return _11(_1p,_1s);});break;case 11:return new F(function(){return _11(_1o,_1s);});break;case 12:return new F(function(){return _11(_1n,_1s);});break;case 13:return new F(function(){return _11(_1m,_1s);});break;case 14:return new F(function(){return _11(_1l,_1s);});break;case 15:return new F(function(){return _11(_1k,_1s);});break;case 16:return new F(function(){return _11(_1j,_1s);});break;case 17:return new F(function(){return _11(_1i,_1s);});break;default:return new F(function(){return _11(_17,_1s);});}},_1t=new T(function(){return B(unCStr("}"));}),_1u=new T(function(){return B(unCStr("{handle: "));}),_1v=function(_1w,_1x,_1y,_1z,_1A,_1B){var _1C=new T(function(){var _1D=new T(function(){var _1E=new T(function(){var _1F=E(_1z);if(!_1F[0]){return E(_1B);}else{var _1G=new T(function(){var _1H=new T(function(){return B(_11(_Z,_1B));},1);return B(_11(_1F,_1H));},1);return B(_11(_10,_1G));}},1);return B(_1q(_1x,_1E));}),_1I=E(_1y);if(!_1I[0]){return E(_1D);}else{var _1J=new T(function(){return B(_11(_Y,_1D));},1);return B(_11(_1I,_1J));}}),_1K=E(_1A);if(!_1K[0]){var _1L=E(_1w);if(!_1L[0]){return E(_1C);}else{var _1M=E(_1L[1]);if(!_1M[0]){var _1N=_1M[1],_1O=new T(function(){var _1P=new T(function(){var _1Q=new T(function(){return B(_11(_Y,_1C));},1);return B(_11(_1t,_1Q));},1);return B(_11(_1N,_1P));},1);return new F(function(){return _11(_1u,_1O);});}else{var _1R=_1M[1],_1S=new T(function(){var _1T=new T(function(){var _1U=new T(function(){return B(_11(_Y,_1C));},1);return B(_11(_1t,_1U));},1);return B(_11(_1R,_1T));},1);return new F(function(){return _11(_1u,_1S);});}}}else{var _1V=new T(function(){return B(_11(_Y,_1C));},1);return new F(function(){return _11(_1K[1],_1V);});}},_1W=function(_1X){var _1Y=E(_1X);return new F(function(){return _1v(_1Y[1],_1Y[2],_1Y[3],_1Y[4],_1Y[6],_F);});},_1Z=function(_20,_21,_22){var _23=E(_21);return new F(function(){return _1v(_23[1],_23[2],_23[3],_23[4],_23[6],_22);});},_24=function(_25,_26){var _27=E(_25);return new F(function(){return _1v(_27[1],_27[2],_27[3],_27[4],_27[6],_26);});},_28=44,_29=93,_2a=91,_2b=function(_2c,_2d,_2e){var _2f=E(_2d);if(!_2f[0]){return new F(function(){return unAppCStr("[]",_2e);});}else{var _2g=_2f[1],_2h=_2f[2],_2i=new T(function(){var _2j=new T(function(){var _2k=[1,_29,_2e],_2l=function(_2m){var _2n=E(_2m);if(!_2n[0]){return E(_2k);}else{var _2o=_2n[1],_2p=_2n[2],_2q=new T(function(){var _2r=new T(function(){return B(_2l(_2p));});return B(A(_2c,[_2o,_2r]));});return [1,_28,_2q];}};return B(_2l(_2h));});return B(A(_2c,[_2g,_2j]));});return [1,_2a,_2i];}},_2s=function(_2t,_2u){return new F(function(){return _2b(_24,_2t,_2u);});},_2v=[0,_1Z,_1W,_2s],_2w=new T(function(){return [0,_J,_2v,_2x,_V,_1W];}),_2x=function(_2y){return [0,_2w,_2y];},_2z=[0],_2A=7,_2B=function(_2C){return [0,_2z,_2A,_F,_2C,_2z,_2z];},_2D=function(_2E,_){var _2F=new T(function(){var _2G=new T(function(){return B(_2B(_2E));});return B(_2x(_2G));});return new F(function(){return die(_2F);});},_2H=[0,_x,_y,_t,_r,_2D],_2I=[0,_2H,_2],_2J=function(_2K,_2L){while(1){var _2M=E(_2K);if(!_2M[0]){return E(_2L);}else{_2K=_2M[2];var _2N=[1,_2M[1],_2L];_2L=_2N;continue;}}},_2O=2,_2P=0,_2Q=[1,_2P,_F],_2R=[1,_2P,_2Q],_2S=[1,_2P,_2R],_2T=[1,_2P,_2S],_2U=[1,_2P,_2T],_2V=5,_2W=[1,_2V,_2U],_2X=[1,_2P,_2W],_2Y=3,_2Z=[1,_2Y,_2X],_30=[1,_2P,_2Z],_31=[1,_2P,_30],_32=[1,_2P,_31],_33=[1,_2P,_32],_34=[1,_2V,_33],_35=[1,_2P,_34],_36=[1,_2P,_35],_37=[1,_2P,_36],_38=[1,_2P,_37],_39=[1,_2P,_38],_3a=[1,_2P,_39],_3b=[1,_2P,_3a],_3c=[1,_2P,_3b],_3d=[1,_2P,_3c],_3e=[1,_2P,_3d],_3f=1,_3g=function(_3h){var _3i=E(_3h);if(!_3i[0]){return [0];}else{var _3j=_3i[2],_3k=new T(function(){return B(_3g(_3j));});return [1,[0,_3f,_3i[1]],_3k];}},_3l=function(_3m,_3n){var _3o=new T(function(){return B(_3g(_3n));});return [1,[0,_3f,_3m],_3o];},_3p=new T(function(){return B(_3l(_2O,_3e));}),_3q=new T(function(){return B(_2J(_3p,_F));}),_3r=0,_3s=function(_3t){var _3u=E(_3t);return (E(_3u[1])==0)?E(_3u):[0,_3r,_3u[2]];},_3v=function(_3w,_3x){var _3y=E(_3x);if(!_3y[0]){return [0];}else{var _3z=_3y[1],_3A=_3y[2],_3B=new T(function(){return B(_3v(_3w,_3A));}),_3C=new T(function(){return B(A(_3w,[_3z]));});return [1,_3C,_3B];}},_3D=new T(function(){return B(_3v(_3s,_3q));}),_3E=new T(function(){return B(unCStr("Control.Exception.Base"));}),_3F=new T(function(){return B(unCStr("base"));}),_3G=new T(function(){return B(unCStr("PatternMatchFail"));}),_3H=new T(function(){var _3I=hs_wordToWord64(18445595),_3J=hs_wordToWord64(52003073);return [0,_3I,_3J,[0,_3I,_3J,_3F,_3E,_3G],_F,_F];}),_3K=function(_3L){return E(_3H);},_3M=function(_3N){var _3O=E(_3N);return new F(function(){return _N(B(_L(_3O[1])),_3K,_3O[2]);});},_3P=function(_3Q){return E(E(_3Q)[1]);},_3R=function(_3S){return [0,_3T,_3S];},_3U=function(_3V,_3W){return new F(function(){return _11(E(_3V)[1],_3W);});},_3X=function(_3Y,_3Z){return new F(function(){return _2b(_3U,_3Y,_3Z);});},_40=function(_41,_42,_43){return new F(function(){return _11(E(_42)[1],_43);});},_44=[0,_40,_3P,_3X],_3T=new T(function(){return [0,_3K,_44,_3R,_3M,_3P];}),_45=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_46=function(_47){return E(E(_47)[3]);},_48=function(_49,_4a){var _4b=new T(function(){return B(A(_46,[_4a,_49]));});return new F(function(){return die(_4b);});},_4c=function(_4d,_4e){return new F(function(){return _48(_4d,_4e);});},_4f=function(_4g,_4h){var _4i=E(_4h);if(!_4i[0]){return [0,_F,_F];}else{var _4j=_4i[1],_4k=_4i[2];if(!B(A(_4g,[_4j]))){return [0,_F,_4i];}else{var _4l=new T(function(){var _4m=B(_4f(_4g,_4k));return [0,_4m[1],_4m[2]];}),_4n=new T(function(){return E(E(_4l)[2]);}),_4o=new T(function(){return E(E(_4l)[1]);});return [0,[1,_4j,_4o],_4n];}}},_4p=32,_4q=new T(function(){return B(unCStr("\n"));}),_4r=function(_4s){return (E(_4s)==124)?false:true;},_4t=function(_4u,_4v){var _4w=B(_4f(_4r,B(unCStr(_4u)))),_4x=_4w[1],_4y=function(_4z,_4A){var _4B=new T(function(){var _4C=new T(function(){var _4D=new T(function(){return B(_11(_4A,_4q));},1);return B(_11(_4v,_4D));});return B(unAppCStr(": ",_4C));},1);return new F(function(){return _11(_4z,_4B);});},_4E=E(_4w[2]);if(!_4E[0]){return new F(function(){return _4y(_4x,_F);});}else{if(E(_4E[1])==124){return new F(function(){return _4y(_4x,[1,_4p,_4E[2]]);});}else{return new F(function(){return _4y(_4x,_F);});}}},_4F=function(_4G){var _4H=new T(function(){return B(_4t(_4G,_45));});return new F(function(){return _4c([0,_4H],_3T);});},_4I=function(_4J,_4K){var _4L=E(_4J);if(!E(_4L[1])){return new F(function(){return _4F("main.hs:(253,20)-(254,55)|function whiteOrBlack");});}else{return (E(_4L[2])==0)?E(_4K):E(_4L);}},_4M=function(_4N,_4O,_4P){var _4Q=E(_4O);if(!_4Q[0]){return [0];}else{var _4R=_4Q[1],_4S=_4Q[2],_4T=E(_4P);if(!_4T[0]){return [0];}else{var _4U=_4T[1],_4V=_4T[2],_4W=new T(function(){return B(_4M(_4N,_4S,_4V));}),_4X=new T(function(){return B(A(_4N,[_4R,_4U]));});return [1,_4X,_4W];}}},_4Y=new T(function(){return B(_4M(_4I,_3p,_3D));}),_4Z=function(_50,_51){while(1){var _52=E(_50);if(!_52[0]){return E(_51);}else{_50=_52[2];var _53=_51+E(_52[1])|0;_51=_53;continue;}}},_54=function(_55,_56,_57){return new F(function(){return _4Z(_56,_57+_55|0);});},_58=new T(function(){return B(_54(2,_3e,0));}),_59=[0,_4Y,_58,_58,_2P,_2P,_3f,_3f],_5a="deltaZ",_5b="deltaY",_5c="deltaX",_5d=function(_5e,_5f){var _5g=jsShowI(_5e);return new F(function(){return _11(fromJSStr(_5g),_5f);});},_5h=41,_5i=40,_5j=function(_5k,_5l,_5m){if(_5l>=0){return new F(function(){return _5d(_5l,_5m);});}else{if(_5k<=6){return new F(function(){return _5d(_5l,_5m);});}else{var _5n=new T(function(){var _5o=jsShowI(_5l);return B(_11(fromJSStr(_5o),[1,_5h,_5m]));});return [1,_5i,_5n];}}},_5p=new T(function(){return B(unCStr(")"));}),_5q=new T(function(){return B(_5j(0,2,_5p));}),_5r=new T(function(){return B(unAppCStr(") is outside of enumeration\'s range (0,",_5q));}),_5s=function(_5t){var _5u=new T(function(){return B(_5j(0,_5t,_5r));});return new F(function(){return err(B(unAppCStr("toEnum{MouseButton}: tag (",_5u)));});},_5v=function(_5w,_){return new T(function(){var _5x=Number(E(_5w)),_5y=jsTrunc(_5x);if(_5y<0){return B(_5s(_5y));}else{if(_5y>2){return B(_5s(_5y));}else{return _5y;}}});},_5z=0,_5A=[0,_5z,_5z,_5z],_5B="button",_5C=new T(function(){return jsGetMouseCoords;}),_5D=function(_5E,_){var _5F=E(_5E);if(!_5F[0]){return _F;}else{var _5G=_5F[1],_5H=B(_5D(_5F[2],_)),_5I=new T(function(){var _5J=Number(E(_5G));return jsTrunc(_5J);});return [1,_5I,_5H];}},_5K=function(_5L,_){var _5M=__arr2lst(0,_5L);return new F(function(){return _5D(_5M,_);});},_5N=function(_5O,_){return new F(function(){return _5K(E(_5O),_);});},_5P=function(_5Q,_){return new T(function(){var _5R=Number(E(_5Q));return jsTrunc(_5R);});},_5S=[0,_5P,_5N],_5T=function(_5U,_){var _5V=E(_5U);if(!_5V[0]){return _F;}else{var _5W=B(_5T(_5V[2],_));return [1,_5V[1],_5W];}},_5X=new T(function(){return B(unCStr("Pattern match failure in do expression at src/Haste/Prim/Any.hs:272:5-9"));}),_5Y=[0,_2z,_2A,_F,_5X,_2z,_2z],_5Z=new T(function(){return B(_2x(_5Y));}),_60=function(_){return new F(function(){return die(_5Z);});},_61=function(_62){return E(E(_62)[1]);},_63=function(_64,_65,_66,_){var _67=__arr2lst(0,_66),_68=B(_5T(_67,_)),_69=E(_68);if(!_69[0]){return new F(function(){return _60(_);});}else{var _6a=E(_69[2]);if(!_6a[0]){return new F(function(){return _60(_);});}else{if(!E(_6a[2])[0]){var _6b=B(A(_61,[_64,_69[1],_])),_6c=B(A(_61,[_65,_6a[1],_]));return [0,_6b,_6c];}else{return new F(function(){return _60(_);});}}}},_6d=function(_){return new F(function(){return __jsNull();});},_6e=function(_6f){var _6g=B(A(_6f,[_]));return E(_6g);},_6h=new T(function(){return B(_6e(_6d));}),_6i=new T(function(){return E(_6h);}),_6j=function(_6k,_6l,_){if(E(_6k)==7){var _6m=E(_5C)(_6l),_6n=B(_63(_5S,_5S,_6m,_)),_6o=_6n,_6p=_6l[E(_5c)],_6q=_6p,_6r=_6l[E(_5b)],_6s=_6r,_6t=_6l[E(_5a)],_6u=_6t;return new T(function(){return [0,E(_6o),E(_2z),[0,_6q,_6s,_6u]];});}else{var _6v=E(_5C)(_6l),_6w=B(_63(_5S,_5S,_6v,_)),_6x=_6w,_6y=_6l[E(_5B)],_6z=__eq(_6y,E(_6i));if(!E(_6z)){var _6A=B(_5v(_6y,_)),_6B=_6A;return new T(function(){return [0,E(_6x),[1,_6B],E(_5A)];});}else{return new T(function(){return [0,E(_6x),E(_2z),E(_5A)];});}}},_6C=function(_6D,_6E,_){return new F(function(){return _6j(_6D,E(_6E),_);});},_6F="mouseout",_6G="mouseover",_6H="mousemove",_6I="mouseup",_6J="mousedown",_6K="dblclick",_6L="click",_6M="wheel",_6N=function(_6O){switch(E(_6O)){case 0:return E(_6L);case 1:return E(_6K);case 2:return E(_6J);case 3:return E(_6I);case 4:return E(_6H);case 5:return E(_6G);case 6:return E(_6F);default:return E(_6M);}},_6P=[0,_6N,_6C],_6Q=0,_6R=function(_){return _6Q;},_6S=[0,_2I,_r],_6T=new T(function(){return B(unCStr("!!: negative index"));}),_6U=new T(function(){return B(unCStr("Prelude."));}),_6V=new T(function(){return B(_11(_6U,_6T));}),_6W=new T(function(){return B(err(_6V));}),_6X=new T(function(){return B(unCStr("!!: index too large"));}),_6Y=new T(function(){return B(_11(_6U,_6X));}),_6Z=new T(function(){return B(err(_6Y));}),_70=function(_71,_72){while(1){var _73=E(_71);if(!_73[0]){return E(_6Z);}else{var _74=E(_72);if(!_74){return E(_73[1]);}else{_71=_73[2];_72=_74-1|0;continue;}}}},_75=function(_76,_77){if(_77>=0){return new F(function(){return _70(_76,_77);});}else{return E(_6W);}},_78=0,_79=new T(function(){return (function (msg) { alert(msg); });}),_7a="value",_7b=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:235:9-19"));}),_7c=[0,_2z,_2A,_F,_7b,_2z,_2z],_7d=new T(function(){return B(_2x(_7c));}),_7e=function(_){var _7f=jsFind("sharedKey");if(!_7f[0]){return new F(function(){return die(_7d);});}else{var _7g=jsGet(E(_7f[1]),E(_7a)),_7h=E(_79)(toJSStr(fromJSStr(_7g)));return new F(function(){return _6R(_);});}},_7i=function(_7j,_){return new F(function(){return _7e(_);});},_7k=new T(function(){return B(unCStr("}"));}),_7l=new T(function(){return B(unCStr(", "));}),_7m=new T(function(){return B(unCStr("onSideIndex = "));}),_7n=new T(function(){return B(unCStr("RightSidePlacement {"));}),_7o=new T(function(){return B(unCStr("LeftSidePlacement {"));}),_7p=new T(function(){return B(unCStr("onBarIndex = "));}),_7q=new T(function(){return B(unCStr("BarPlacement {"));}),_7r=new T(function(){return B(unCStr("onPointIndex = "));}),_7s=new T(function(){return B(unCStr("pointIndex = "));}),_7t=new T(function(){return B(unCStr("PointPlacement {"));}),_7u=function(_7v,_7w,_7x){var _7y=E(_7w);switch(_7y[0]){case 0:var _7z=_7y[1],_7A=_7y[2],_7B=function(_7C){var _7D=new T(function(){var _7E=new T(function(){var _7F=new T(function(){var _7G=new T(function(){var _7H=new T(function(){return B(_11(_7k,_7C));});return B(_5j(0,E(_7A),_7H));},1);return B(_11(_7r,_7G));},1);return B(_11(_7l,_7F));});return B(_5j(0,E(_7z),_7E));},1);return new F(function(){return _11(_7s,_7D);});};if(_7v<11){var _7I=new T(function(){return B(_7B(_7x));},1);return new F(function(){return _11(_7t,_7I);});}else{var _7J=new T(function(){var _7K=new T(function(){return B(_7B([1,_5h,_7x]));},1);return B(_11(_7t,_7K));});return [1,_5i,_7J];}break;case 1:var _7L=_7y[1],_7M=function(_7N){var _7O=new T(function(){var _7P=new T(function(){var _7Q=new T(function(){return B(_11(_7k,_7N));});return B(_5j(0,E(_7L),_7Q));},1);return B(_11(_7p,_7P));},1);return new F(function(){return _11(_7q,_7O);});};if(_7v<11){return new F(function(){return _7M(_7x);});}else{var _7R=new T(function(){return B(_7M([1,_5h,_7x]));});return [1,_5i,_7R];}break;case 2:var _7S=_7y[1],_7T=function(_7U){var _7V=new T(function(){var _7W=new T(function(){var _7X=new T(function(){return B(_11(_7k,_7U));});return B(_5j(0,E(_7S),_7X));},1);return B(_11(_7m,_7W));},1);return new F(function(){return _11(_7o,_7V);});};if(_7v<11){return new F(function(){return _7T(_7x);});}else{var _7Y=new T(function(){return B(_7T([1,_5h,_7x]));});return [1,_5i,_7Y];}break;default:var _7Z=_7y[1],_80=function(_81){var _82=new T(function(){var _83=new T(function(){var _84=new T(function(){return B(_11(_7k,_81));});return B(_5j(0,E(_7Z),_84));},1);return B(_11(_7m,_83));},1);return new F(function(){return _11(_7n,_82);});};if(_7v<11){return new F(function(){return _80(_7x);});}else{var _85=new T(function(){return B(_80([1,_5h,_7x]));});return [1,_5i,_85];}}},_86=true,_87=new T(function(){return B(unCStr("Black"));}),_88=new T(function(){return B(unCStr("White"));}),_89=95,_8a=function(_8b){var _8c=E(_8b);return (E(_8c)==32)?E(_89):E(_8c);},_8d=new T(function(){return B(unCStr("draggable "));}),_8e=new T(function(){return B(unCStr("class"));}),_8f=function(_8g){return E(E(_8g)[1]);},_8h=function(_8i){return E(E(_8i)[2]);},_8j=function(_8k,_8l,_8m,_8n,_8o){var _8p=function(_){var _8q=jsSetAttr(B(A(_8f,[_8k,_8m])),toJSStr(E(_8n)),toJSStr(E(_8o)));return _6Q;};return new F(function(){return A(_8h,[_8l,_8p]);});},_8r=function(_8s,_8t,_8u,_8v,_){var _8w=new T(function(){var _8x=new T(function(){var _8y=new T(function(){var _8z=new T(function(){return B(_3v(_8a,B(_7u(0,_8v,_F))));});return B(unAppCStr(" ",_8z));});if(!E(_8t)){return B(_11(_87,_8y));}else{return B(_11(_88,_8y));}});if(!E(_8u)){return E(_8x);}else{return B(_11(_8d,_8x));}});return new F(function(){return A(_8j,[_4,_2I,_8s,_8e,_8w,_]);});},_8A=new T(function(){return B(unCStr(": empty list"));}),_8B=function(_8C){var _8D=new T(function(){return B(_11(_8C,_8A));},1);return new F(function(){return err(B(_11(_6U,_8D)));});},_8E=new T(function(){return B(unCStr("head"));}),_8F=new T(function(){return B(_8B(_8E));}),_8G=new T(function(){return (function (elem, cx, cy, duration) {$(elem).velocity({ cx: cx, cy: cy }, { duration: duration });});}),_8H=function(_8I,_8J){if(_8I<=0){if(_8I>=0){return new F(function(){return quot(_8I,_8J);});}else{if(_8J<=0){return new F(function(){return quot(_8I,_8J);});}else{return quot(_8I+1|0,_8J)-1|0;}}}else{if(_8J>=0){if(_8I>=0){return new F(function(){return quot(_8I,_8J);});}else{if(_8J<=0){return new F(function(){return quot(_8I,_8J);});}else{return quot(_8I+1|0,_8J)-1|0;}}}else{return quot(_8I-1|0,_8J)-1|0;}}},_8K=new T(function(){return B(_8H(15,2));}),_8L=new T(function(){return 220+B(_8H(15,2))|0;}),_8M=new T(function(){return B(_4F("main.hs:(92,1)-(119,116)|function checkerPosition"));}),_8N=function(_8O,_8P,_8Q,_){var _8R=jsElemsByClassName(toJSStr(B(_3v(_8a,B(_7u(0,_8O,_F))))));if(!_8R[0]){return E(_8F);}else{var _8S=E(_8R[1]),_8T=_8S,_8U=function(_8V,_8W){var _8X=E(_8G)(_8T,E(_8V),E(_8W),300);return new F(function(){return _8r(_8S,_8Q,_86,_8P,_);});},_8Y=E(_8P);switch(_8Y[0]){case 0:var _8Z=_8Y[1],_90=_8Y[2],_91=new T(function(){if(E(_8Z)>=12){return 203+(imul(imul(imul(-1,E(_90))|0,2)|0,6)|0)|0;}else{return 7+(imul(imul(E(_90),2)|0,6)|0)|0;}}),_92=new T(function(){var _93=E(_8Z);if(_93>=12){var _94=23-_93|0;if(_94>=6){return 25+(20+(imul(_94,15)|0)|0)|0;}else{return 25+(imul(_94,15)|0)|0;}}else{if(_93>=6){return 25+(20+(imul(_93,15)|0)|0)|0;}else{return 25+(imul(_93,15)|0)|0;}}});return new F(function(){return _8U(_92,_91);});break;case 1:return E(_8M);case 2:var _95=_8Y[1],_96=new T(function(){return 203-(imul(imul(E(_95),2)|0,6)|0)|0;});return new F(function(){return _8U(_8K,_96);});break;default:var _97=_8Y[1],_98=new T(function(){return 203-(imul(imul(E(_97),2)|0,6)|0)|0;});return new F(function(){return _8U(_8L,_98);});}}},_99=function(_9a,_9b){if(_9a<=_9b){var _9c=function(_9d){var _9e=new T(function(){if(_9d!=_9b){return B(_9c(_9d+1|0));}else{return [0];}});return [1,_9d,_9e];};return new F(function(){return _9c(_9a);});}else{return [0];}},_9f=new T(function(){return (function (cb) {setDropCheckerCallback_ffi(cb);});}),_9g=function(_9h,_9i){var _9j=function(_9k,_9l){while(1){var _9m=(function(_9n,_9o){var _9p=E(_9n);if(!_9p[0]){return [0];}else{var _9q=_9p[2];if(!B(A(_9h,[_9p[1]]))){_9k=_9q;var _9r=_9o+1|0;_9l=_9r;return null;}else{var _9s=new T(function(){return B(_9j(_9q,_9o+1|0));});return [1,_9o,_9s];}}})(_9k,_9l);if(_9m!=null){return _9m;}}},_9t=B(_9j(_9i,0));return (_9t[0]==0)?[0]:[1,_9t[1]];},_9u=new T(function(){return B(_99(0,2147483647));}),_9v=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_9w=new T(function(){return B(err(_9v));}),_9x=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_9y=new T(function(){return B(err(_9x));}),_9z=new T(function(){return B(_8H(210,2));}),_9A=new T(function(){return B(_4F("Text/ParserCombinators/ReadP.hs:(128,3)-(151,52)|function <|>"));}),_9B=function(_9C,_9D){while(1){var _9E=(function(_9F,_9G){var _9H=E(_9F);switch(_9H[0]){case 0:var _9I=E(_9G);if(!_9I[0]){return [0];}else{_9C=B(A(_9H[1],[_9I[1]]));_9D=_9I[2];return null;}break;case 1:var _9J=B(A(_9H[1],[_9G])),_9K=_9G;_9C=_9J;_9D=_9K;return null;case 2:return [0];case 3:var _9L=_9H[2],_9M=new T(function(){return B(_9B(_9L,_9G));});return [1,[0,_9H[1],_9G],_9M];default:return E(_9H[1]);}})(_9C,_9D);if(_9E!=null){return _9E;}}},_9N=function(_9O,_9P){var _9Q=function(_9R){var _9S=E(_9P);if(_9S[0]==3){var _9T=_9S[2],_9U=new T(function(){return B(_9N(_9O,_9T));});return [3,_9S[1],_9U];}else{var _9V=E(_9O);if(_9V[0]==2){return E(_9S);}else{var _9W=E(_9S);if(_9W[0]==2){return E(_9V);}else{var _9X=function(_9Y){var _9Z=E(_9W);if(_9Z[0]==4){var _a0=_9Z[1];return [1,function(_a1){return [4,new T(function(){return B(_11(B(_9B(_9V,_a1)),_a0));})];}];}else{var _a2=E(_9V);if(_a2[0]==1){var _a3=_a2[1],_a4=E(_9Z);if(!_a4[0]){return [1,function(_a5){return new F(function(){return _9N(B(A(_a3,[_a5])),_a4);});}];}else{var _a6=_a4[1];return [1,function(_a7){var _a8=new T(function(){return B(A(_a6,[_a7]));});return new F(function(){return _9N(B(A(_a3,[_a7])),_a8);});}];}}else{var _a9=E(_9Z);if(!_a9[0]){return E(_9A);}else{var _aa=_a9[1];return [1,function(_ab){var _ac=new T(function(){return B(A(_aa,[_ab]));});return new F(function(){return _9N(_a2,_ac);});}];}}}},_ad=E(_9V);switch(_ad[0]){case 1:var _ae=_ad[1],_af=E(_9W);if(_af[0]==4){var _ag=_af[1];return [1,function(_ah){return [4,new T(function(){return B(_11(B(_9B(B(A(_ae,[_ah])),_ah)),_ag));})];}];}else{return new F(function(){return _9X(_);});}break;case 4:var _ai=_ad[1],_aj=E(_9W);switch(_aj[0]){case 0:return [1,function(_ak){return [4,new T(function(){var _al=new T(function(){return B(_9B(_aj,_ak));},1);return B(_11(_ai,_al));})];}];case 1:var _am=_aj[1];return [1,function(_an){return [4,new T(function(){var _ao=new T(function(){return B(_9B(B(A(_am,[_an])),_an));},1);return B(_11(_ai,_ao));})];}];default:var _ap=_aj[1];return [4,new T(function(){return B(_11(_ai,_ap));})];}break;default:return new F(function(){return _9X(_);});}}}}},_aq=E(_9O);switch(_aq[0]){case 0:var _ar=_aq[1],_as=E(_9P);if(!_as[0]){var _at=_as[1];return [0,function(_au){var _av=new T(function(){return B(A(_at,[_au]));});return new F(function(){return _9N(B(A(_ar,[_au])),_av);});}];}else{return new F(function(){return _9Q(_);});}break;case 3:var _aw=_aq[2],_ax=new T(function(){return B(_9N(_aw,_9P));});return [3,_aq[1],_ax];default:return new F(function(){return _9Q(_);});}},_ay=new T(function(){return B(unCStr("("));}),_az=new T(function(){return B(unCStr(")"));}),_aA=function(_aB,_aC){while(1){var _aD=E(_aB);if(!_aD[0]){return (E(_aC)[0]==0)?true:false;}else{var _aE=E(_aC);if(!_aE[0]){return false;}else{if(E(_aD[1])!=E(_aE[1])){return false;}else{_aB=_aD[2];_aC=_aE[2];continue;}}}}},_aF=function(_aG,_aH){return E(_aG)!=E(_aH);},_aI=function(_aJ,_aK){return E(_aJ)==E(_aK);},_aL=[0,_aI,_aF],_aM=function(_aN,_aO){while(1){var _aP=E(_aN);if(!_aP[0]){return (E(_aO)[0]==0)?true:false;}else{var _aQ=E(_aO);if(!_aQ[0]){return false;}else{if(E(_aP[1])!=E(_aQ[1])){return false;}else{_aN=_aP[2];_aO=_aQ[2];continue;}}}}},_aR=function(_aS,_aT){return (!B(_aM(_aS,_aT)))?true:false;},_aU=[0,_aM,_aR],_aV=function(_aW,_aX){var _aY=E(_aW);switch(_aY[0]){case 0:var _aZ=_aY[1];return [0,function(_b0){return new F(function(){return _aV(B(A(_aZ,[_b0])),_aX);});}];case 1:var _b1=_aY[1];return [1,function(_b2){return new F(function(){return _aV(B(A(_b1,[_b2])),_aX);});}];case 2:return [2];case 3:var _b3=_aY[2],_b4=new T(function(){return B(_aV(_b3,_aX));});return new F(function(){return _9N(B(A(_aX,[_aY[1]])),_b4);});break;default:var _b5=function(_b6){var _b7=E(_b6);if(!_b7[0]){return [0];}else{var _b8=_b7[2],_b9=E(_b7[1]),_ba=new T(function(){return B(_b5(_b8));},1);return new F(function(){return _11(B(_9B(B(A(_aX,[_b9[1]])),_b9[2])),_ba);});}},_bb=B(_b5(_aY[1]));return (_bb[0]==0)?[2]:[4,_bb];}},_bc=[2],_bd=function(_be){return [3,_be,_bc];},_bf=function(_bg,_bh){var _bi=E(_bg);if(!_bi){return new F(function(){return A(_bh,[_6Q]);});}else{var _bj=new T(function(){return B(_bf(_bi-1|0,_bh));});return [0,function(_bk){return E(_bj);}];}},_bl=function(_bm,_bn,_bo){var _bp=new T(function(){return B(A(_bm,[_bd]));}),_bq=function(_br,_bs,_bt,_bu){while(1){var _bv=(function(_bw,_bx,_by,_bz){var _bA=E(_bw);switch(_bA[0]){case 0:var _bB=E(_bx);if(!_bB[0]){return new F(function(){return A(_bn,[_bz]);});}else{_br=B(A(_bA[1],[_bB[1]]));_bs=_bB[2];var _bC=_by+1|0,_bD=_bz;_bt=_bC;_bu=_bD;return null;}break;case 1:var _bE=B(A(_bA[1],[_bx])),_bF=_bx,_bC=_by,_bD=_bz;_br=_bE;_bs=_bF;_bt=_bC;_bu=_bD;return null;case 2:return new F(function(){return A(_bn,[_bz]);});break;case 3:var _bG=new T(function(){return B(_aV(_bA,_bz));}),_bH=function(_bI){return E(_bG);};return new F(function(){return _bf(_by,_bH);});break;default:return new F(function(){return _aV(_bA,_bz);});}})(_br,_bs,_bt,_bu);if(_bv!=null){return _bv;}}};return function(_bJ){return new F(function(){return _bq(_bp,_bJ,0,_bo);});};},_bK=function(_bL){return new F(function(){return A(_bL,[_F]);});},_bM=function(_bN,_bO){var _bP=function(_bQ){var _bR=E(_bQ);if(!_bR[0]){return E(_bK);}else{var _bS=_bR[1],_bT=_bR[2];if(!B(A(_bN,[_bS]))){return E(_bK);}else{var _bU=new T(function(){return B(_bP(_bT));}),_bV=function(_bW){var _bX=new T(function(){var _bY=function(_bZ){return new F(function(){return A(_bW,[[1,_bS,_bZ]]);});};return B(A(_bU,[_bY]));});return [0,function(_c0){return E(_bX);}];};return E(_bV);}}};return function(_c1){return new F(function(){return A(_bP,[_c1,_bO]);});};},_c2=[6],_c3=new T(function(){return B(unCStr("valDig: Bad base"));}),_c4=new T(function(){return B(err(_c3));}),_c5=function(_c6,_c7){var _c8=function(_c9,_ca){var _cb=E(_c9);if(!_cb[0]){var _cc=new T(function(){return B(A(_ca,[_F]));}),_cd=function(_ce){return new F(function(){return A(_ce,[_cc]);});};return E(_cd);}else{var _cf=_cb[2],_cg=E(_cb[1]),_ch=function(_ci){var _cj=new T(function(){var _ck=function(_cl){return new F(function(){return A(_ca,[[1,_ci,_cl]]);});};return B(_c8(_cf,_ck));}),_cm=function(_cn){var _co=new T(function(){return B(A(_cj,[_cn]));});return [0,function(_cp){return E(_co);}];};return E(_cm);};switch(E(_c6)){case 8:if(48>_cg){var _cq=new T(function(){return B(A(_ca,[_F]));}),_cr=function(_cs){return new F(function(){return A(_cs,[_cq]);});};return E(_cr);}else{if(_cg>55){var _ct=new T(function(){return B(A(_ca,[_F]));}),_cu=function(_cv){return new F(function(){return A(_cv,[_ct]);});};return E(_cu);}else{return new F(function(){return _ch(_cg-48|0);});}}break;case 10:if(48>_cg){var _cw=new T(function(){return B(A(_ca,[_F]));}),_cx=function(_cy){return new F(function(){return A(_cy,[_cw]);});};return E(_cx);}else{if(_cg>57){var _cz=new T(function(){return B(A(_ca,[_F]));}),_cA=function(_cB){return new F(function(){return A(_cB,[_cz]);});};return E(_cA);}else{return new F(function(){return _ch(_cg-48|0);});}}break;case 16:if(48>_cg){if(97>_cg){if(65>_cg){var _cC=new T(function(){return B(A(_ca,[_F]));}),_cD=function(_cE){return new F(function(){return A(_cE,[_cC]);});};return E(_cD);}else{if(_cg>70){var _cF=new T(function(){return B(A(_ca,[_F]));}),_cG=function(_cH){return new F(function(){return A(_cH,[_cF]);});};return E(_cG);}else{return new F(function(){return _ch((_cg-65|0)+10|0);});}}}else{if(_cg>102){if(65>_cg){var _cI=new T(function(){return B(A(_ca,[_F]));}),_cJ=function(_cK){return new F(function(){return A(_cK,[_cI]);});};return E(_cJ);}else{if(_cg>70){var _cL=new T(function(){return B(A(_ca,[_F]));}),_cM=function(_cN){return new F(function(){return A(_cN,[_cL]);});};return E(_cM);}else{return new F(function(){return _ch((_cg-65|0)+10|0);});}}}else{return new F(function(){return _ch((_cg-97|0)+10|0);});}}}else{if(_cg>57){if(97>_cg){if(65>_cg){var _cO=new T(function(){return B(A(_ca,[_F]));}),_cP=function(_cQ){return new F(function(){return A(_cQ,[_cO]);});};return E(_cP);}else{if(_cg>70){var _cR=new T(function(){return B(A(_ca,[_F]));}),_cS=function(_cT){return new F(function(){return A(_cT,[_cR]);});};return E(_cS);}else{return new F(function(){return _ch((_cg-65|0)+10|0);});}}}else{if(_cg>102){if(65>_cg){var _cU=new T(function(){return B(A(_ca,[_F]));}),_cV=function(_cW){return new F(function(){return A(_cW,[_cU]);});};return E(_cV);}else{if(_cg>70){var _cX=new T(function(){return B(A(_ca,[_F]));}),_cY=function(_cZ){return new F(function(){return A(_cZ,[_cX]);});};return E(_cY);}else{return new F(function(){return _ch((_cg-65|0)+10|0);});}}}else{return new F(function(){return _ch((_cg-97|0)+10|0);});}}}else{return new F(function(){return _ch(_cg-48|0);});}}break;default:return E(_c4);}}},_d0=function(_d1){var _d2=E(_d1);if(!_d2[0]){return [2];}else{return new F(function(){return A(_c7,[_d2]);});}};return function(_d3){return new F(function(){return A(_c8,[_d3,_2,_d0]);});};},_d4=16,_d5=8,_d6=function(_d7){var _d8=function(_d9){return new F(function(){return A(_d7,[[5,[0,_d5,_d9]]]);});},_da=function(_db){return new F(function(){return A(_d7,[[5,[0,_d4,_db]]]);});},_dc=function(_dd){switch(E(_dd)){case 79:return [1,B(_c5(_d5,_d8))];case 88:return [1,B(_c5(_d4,_da))];case 111:return [1,B(_c5(_d5,_d8))];case 120:return [1,B(_c5(_d4,_da))];default:return [2];}},_de=[0,_dc];return function(_df){return (E(_df)==48)?E(_de):[2];};},_dg=function(_dh){return [0,B(_d6(_dh))];},_di=function(_dj){return new F(function(){return A(_dj,[_2z]);});},_dk=function(_dl){return new F(function(){return A(_dl,[_2z]);});},_dm=10,_dn=[0,1],_do=[0,2147483647],_dp=function(_dq,_dr){while(1){var _ds=E(_dq);if(!_ds[0]){var _dt=_ds[1],_du=E(_dr);if(!_du[0]){var _dv=_du[1],_dw=addC(_dt,_dv);if(!E(_dw[2])){return [0,_dw[1]];}else{_dq=[1,I_fromInt(_dt)];_dr=[1,I_fromInt(_dv)];continue;}}else{_dq=[1,I_fromInt(_dt)];_dr=_du;continue;}}else{var _dx=E(_dr);if(!_dx[0]){_dq=_ds;_dr=[1,I_fromInt(_dx[1])];continue;}else{return [1,I_add(_ds[1],_dx[1])];}}}},_dy=new T(function(){return B(_dp(_do,_dn));}),_dz=function(_dA){var _dB=E(_dA);if(!_dB[0]){var _dC=E(_dB[1]);return (_dC==(-2147483648))?E(_dy):[0, -_dC];}else{return [1,I_negate(_dB[1])];}},_dD=[0,10],_dE=function(_dF,_dG){while(1){var _dH=E(_dF);if(!_dH[0]){return E(_dG);}else{_dF=_dH[2];var _dI=_dG+1|0;_dG=_dI;continue;}}},_dJ=function(_dK){return [0,_dK];},_dL=function(_dM){return new F(function(){return _dJ(E(_dM));});},_dN=new T(function(){return B(unCStr("this should not happen"));}),_dO=new T(function(){return B(err(_dN));}),_dP=function(_dQ,_dR){while(1){var _dS=E(_dQ);if(!_dS[0]){var _dT=_dS[1],_dU=E(_dR);if(!_dU[0]){var _dV=_dU[1];if(!(imul(_dT,_dV)|0)){return [0,imul(_dT,_dV)|0];}else{_dQ=[1,I_fromInt(_dT)];_dR=[1,I_fromInt(_dV)];continue;}}else{_dQ=[1,I_fromInt(_dT)];_dR=_dU;continue;}}else{var _dW=E(_dR);if(!_dW[0]){_dQ=_dS;_dR=[1,I_fromInt(_dW[1])];continue;}else{return [1,I_mul(_dS[1],_dW[1])];}}}},_dX=function(_dY,_dZ){var _e0=E(_dZ);if(!_e0[0]){return [0];}else{var _e1=E(_e0[2]);if(!_e1[0]){return E(_dO);}else{var _e2=_e1[2],_e3=new T(function(){return B(_dX(_dY,_e2));});return [1,B(_dp(B(_dP(_e0[1],_dY)),_e1[1])),_e3];}}},_e4=[0,0],_e5=function(_e6,_e7,_e8){while(1){var _e9=(function(_ea,_eb,_ec){var _ed=E(_ec);if(!_ed[0]){return E(_e4);}else{if(!E(_ed[2])[0]){return E(_ed[1]);}else{var _ee=E(_eb);if(_ee<=40){var _ef=_e4,_eg=_ed;while(1){var _eh=E(_eg);if(!_eh[0]){return E(_ef);}else{var _ei=B(_dp(B(_dP(_ef,_ea)),_eh[1]));_eg=_eh[2];_ef=_ei;continue;}}}else{var _ej=B(_dP(_ea,_ea));if(!(_ee%2)){_e6=_ej;_e7=quot(_ee+1|0,2);var _ek=B(_dX(_ea,_ed));_e8=_ek;return null;}else{_e6=_ej;_e7=quot(_ee+1|0,2);var _ek=B(_dX(_ea,[1,_e4,_ed]));_e8=_ek;return null;}}}}})(_e6,_e7,_e8);if(_e9!=null){return _e9;}}},_el=function(_em,_en){var _eo=new T(function(){return B(_dE(_en,0));},1);return new F(function(){return _e5(_em,_eo,B(_3v(_dL,_en)));});},_ep=function(_eq){var _er=new T(function(){var _es=new T(function(){var _et=function(_eu){var _ev=new T(function(){return B(_el(_dD,_eu));});return new F(function(){return A(_eq,[[1,_ev]]);});};return [1,B(_c5(_dm,_et))];}),_ew=function(_ex){if(E(_ex)==43){var _ey=function(_ez){var _eA=new T(function(){return B(_el(_dD,_ez));});return new F(function(){return A(_eq,[[1,_eA]]);});};return [1,B(_c5(_dm,_ey))];}else{return [2];}},_eB=function(_eC){if(E(_eC)==45){var _eD=function(_eE){var _eF=new T(function(){return B(_dz(B(_el(_dD,_eE))));});return new F(function(){return A(_eq,[[1,_eF]]);});};return [1,B(_c5(_dm,_eD))];}else{return [2];}};return B(_9N(B(_9N([0,_eB],[0,_ew])),_es));}),_eG=function(_eH){return (E(_eH)==69)?E(_er):[2];},_eI=function(_eJ){return (E(_eJ)==101)?E(_er):[2];};return new F(function(){return _9N([0,_eI],[0,_eG]);});},_eK=function(_eL){var _eM=function(_eN){return new F(function(){return A(_eL,[[1,_eN]]);});};return function(_eO){return (E(_eO)==46)?[1,B(_c5(_dm,_eM))]:[2];};},_eP=function(_eQ){return [0,B(_eK(_eQ))];},_eR=function(_eS){var _eT=function(_eU){var _eV=function(_eW){var _eX=function(_eY){return new F(function(){return A(_eS,[[5,[1,_eU,_eW,_eY]]]);});};return [1,B(_bl(_ep,_di,_eX))];};return [1,B(_bl(_eP,_dk,_eV))];};return new F(function(){return _c5(_dm,_eT);});},_eZ=function(_f0){return [1,B(_eR(_f0))];},_f1=function(_f2){return E(E(_f2)[1]);},_f3=function(_f4,_f5,_f6){while(1){var _f7=E(_f6);if(!_f7[0]){return false;}else{if(!B(A(_f1,[_f4,_f5,_f7[1]]))){_f6=_f7[2];continue;}else{return true;}}}},_f8=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_f9=function(_fa){return new F(function(){return _f3(_aL,_fa,_f8);});},_fb=false,_fc=function(_fd){var _fe=new T(function(){return B(A(_fd,[_d5]));}),_ff=new T(function(){return B(A(_fd,[_d4]));});return function(_fg){switch(E(_fg)){case 79:return E(_fe);case 88:return E(_ff);case 111:return E(_fe);case 120:return E(_ff);default:return [2];}};},_fh=function(_fi){return [0,B(_fc(_fi))];},_fj=function(_fk){return new F(function(){return A(_fk,[_dm]);});},_fl=function(_fm){var _fn=new T(function(){return B(_5j(9,_fm,_F));});return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",_fn)));});},_fo=function(_fp){var _fq=E(_fp);if(!_fq[0]){return E(_fq[1]);}else{return new F(function(){return I_toInt(_fq[1]);});}},_fr=function(_fs,_ft){var _fu=E(_fs);if(!_fu[0]){var _fv=_fu[1],_fw=E(_ft);return (_fw[0]==0)?_fv<=_fw[1]:I_compareInt(_fw[1],_fv)>=0;}else{var _fx=_fu[1],_fy=E(_ft);return (_fy[0]==0)?I_compareInt(_fx,_fy[1])<=0:I_compare(_fx,_fy[1])<=0;}},_fz=function(_fA){return [2];},_fB=function(_fC){var _fD=E(_fC);if(!_fD[0]){return E(_fz);}else{var _fE=_fD[1],_fF=E(_fD[2]);if(!_fF[0]){return E(_fE);}else{var _fG=new T(function(){return B(_fB(_fF));}),_fH=function(_fI){var _fJ=new T(function(){return B(A(_fG,[_fI]));});return new F(function(){return _9N(B(A(_fE,[_fI])),_fJ);});};return E(_fH);}}},_fK=function(_fL,_fM){var _fN=function(_fO,_fP,_fQ){var _fR=E(_fO);if(!_fR[0]){return new F(function(){return A(_fQ,[_fL]);});}else{var _fS=_fR[2],_fT=E(_fP);if(!_fT[0]){return [2];}else{var _fU=_fT[2];if(E(_fR[1])!=E(_fT[1])){return [2];}else{var _fV=new T(function(){return B(_fN(_fS,_fU,_fQ));});return [0,function(_fW){return E(_fV);}];}}}};return function(_fX){return new F(function(){return _fN(_fL,_fX,_fM);});};},_fY=new T(function(){return B(unCStr("SO"));}),_fZ=14,_g0=function(_g1){var _g2=new T(function(){return B(A(_g1,[_fZ]));}),_g3=function(_g4){return E(_g2);};return [1,B(_fK(_fY,_g3))];},_g5=new T(function(){return B(unCStr("SOH"));}),_g6=1,_g7=function(_g8){var _g9=new T(function(){return B(A(_g8,[_g6]));}),_ga=function(_gb){return E(_g9);};return [1,B(_fK(_g5,_ga))];},_gc=function(_gd){return [1,B(_bl(_g7,_g0,_gd))];},_ge=new T(function(){return B(unCStr("NUL"));}),_gf=0,_gg=function(_gh){var _gi=new T(function(){return B(A(_gh,[_gf]));}),_gj=function(_gk){return E(_gi);};return [1,B(_fK(_ge,_gj))];},_gl=new T(function(){return B(unCStr("STX"));}),_gm=2,_gn=function(_go){var _gp=new T(function(){return B(A(_go,[_gm]));}),_gq=function(_gr){return E(_gp);};return [1,B(_fK(_gl,_gq))];},_gs=new T(function(){return B(unCStr("ETX"));}),_gt=3,_gu=function(_gv){var _gw=new T(function(){return B(A(_gv,[_gt]));}),_gx=function(_gy){return E(_gw);};return [1,B(_fK(_gs,_gx))];},_gz=new T(function(){return B(unCStr("EOT"));}),_gA=4,_gB=function(_gC){var _gD=new T(function(){return B(A(_gC,[_gA]));}),_gE=function(_gF){return E(_gD);};return [1,B(_fK(_gz,_gE))];},_gG=new T(function(){return B(unCStr("ENQ"));}),_gH=5,_gI=function(_gJ){var _gK=new T(function(){return B(A(_gJ,[_gH]));}),_gL=function(_gM){return E(_gK);};return [1,B(_fK(_gG,_gL))];},_gN=new T(function(){return B(unCStr("ACK"));}),_gO=6,_gP=function(_gQ){var _gR=new T(function(){return B(A(_gQ,[_gO]));}),_gS=function(_gT){return E(_gR);};return [1,B(_fK(_gN,_gS))];},_gU=new T(function(){return B(unCStr("BEL"));}),_gV=7,_gW=function(_gX){var _gY=new T(function(){return B(A(_gX,[_gV]));}),_gZ=function(_h0){return E(_gY);};return [1,B(_fK(_gU,_gZ))];},_h1=new T(function(){return B(unCStr("BS"));}),_h2=8,_h3=function(_h4){var _h5=new T(function(){return B(A(_h4,[_h2]));}),_h6=function(_h7){return E(_h5);};return [1,B(_fK(_h1,_h6))];},_h8=new T(function(){return B(unCStr("HT"));}),_h9=9,_ha=function(_hb){var _hc=new T(function(){return B(A(_hb,[_h9]));}),_hd=function(_he){return E(_hc);};return [1,B(_fK(_h8,_hd))];},_hf=new T(function(){return B(unCStr("LF"));}),_hg=10,_hh=function(_hi){var _hj=new T(function(){return B(A(_hi,[_hg]));}),_hk=function(_hl){return E(_hj);};return [1,B(_fK(_hf,_hk))];},_hm=new T(function(){return B(unCStr("VT"));}),_hn=11,_ho=function(_hp){var _hq=new T(function(){return B(A(_hp,[_hn]));}),_hr=function(_hs){return E(_hq);};return [1,B(_fK(_hm,_hr))];},_ht=new T(function(){return B(unCStr("FF"));}),_hu=12,_hv=function(_hw){var _hx=new T(function(){return B(A(_hw,[_hu]));}),_hy=function(_hz){return E(_hx);};return [1,B(_fK(_ht,_hy))];},_hA=new T(function(){return B(unCStr("CR"));}),_hB=13,_hC=function(_hD){var _hE=new T(function(){return B(A(_hD,[_hB]));}),_hF=function(_hG){return E(_hE);};return [1,B(_fK(_hA,_hF))];},_hH=new T(function(){return B(unCStr("SI"));}),_hI=15,_hJ=function(_hK){var _hL=new T(function(){return B(A(_hK,[_hI]));}),_hM=function(_hN){return E(_hL);};return [1,B(_fK(_hH,_hM))];},_hO=new T(function(){return B(unCStr("DLE"));}),_hP=16,_hQ=function(_hR){var _hS=new T(function(){return B(A(_hR,[_hP]));}),_hT=function(_hU){return E(_hS);};return [1,B(_fK(_hO,_hT))];},_hV=new T(function(){return B(unCStr("DC1"));}),_hW=17,_hX=function(_hY){var _hZ=new T(function(){return B(A(_hY,[_hW]));}),_i0=function(_i1){return E(_hZ);};return [1,B(_fK(_hV,_i0))];},_i2=new T(function(){return B(unCStr("DC2"));}),_i3=18,_i4=function(_i5){var _i6=new T(function(){return B(A(_i5,[_i3]));}),_i7=function(_i8){return E(_i6);};return [1,B(_fK(_i2,_i7))];},_i9=new T(function(){return B(unCStr("DC3"));}),_ia=19,_ib=function(_ic){var _id=new T(function(){return B(A(_ic,[_ia]));}),_ie=function(_if){return E(_id);};return [1,B(_fK(_i9,_ie))];},_ig=new T(function(){return B(unCStr("DC4"));}),_ih=20,_ii=function(_ij){var _ik=new T(function(){return B(A(_ij,[_ih]));}),_il=function(_im){return E(_ik);};return [1,B(_fK(_ig,_il))];},_in=new T(function(){return B(unCStr("NAK"));}),_io=21,_ip=function(_iq){var _ir=new T(function(){return B(A(_iq,[_io]));}),_is=function(_it){return E(_ir);};return [1,B(_fK(_in,_is))];},_iu=new T(function(){return B(unCStr("SYN"));}),_iv=22,_iw=function(_ix){var _iy=new T(function(){return B(A(_ix,[_iv]));}),_iz=function(_iA){return E(_iy);};return [1,B(_fK(_iu,_iz))];},_iB=new T(function(){return B(unCStr("ETB"));}),_iC=23,_iD=function(_iE){var _iF=new T(function(){return B(A(_iE,[_iC]));}),_iG=function(_iH){return E(_iF);};return [1,B(_fK(_iB,_iG))];},_iI=new T(function(){return B(unCStr("CAN"));}),_iJ=24,_iK=function(_iL){var _iM=new T(function(){return B(A(_iL,[_iJ]));}),_iN=function(_iO){return E(_iM);};return [1,B(_fK(_iI,_iN))];},_iP=new T(function(){return B(unCStr("EM"));}),_iQ=25,_iR=function(_iS){var _iT=new T(function(){return B(A(_iS,[_iQ]));}),_iU=function(_iV){return E(_iT);};return [1,B(_fK(_iP,_iU))];},_iW=new T(function(){return B(unCStr("SUB"));}),_iX=26,_iY=function(_iZ){var _j0=new T(function(){return B(A(_iZ,[_iX]));}),_j1=function(_j2){return E(_j0);};return [1,B(_fK(_iW,_j1))];},_j3=new T(function(){return B(unCStr("ESC"));}),_j4=27,_j5=function(_j6){var _j7=new T(function(){return B(A(_j6,[_j4]));}),_j8=function(_j9){return E(_j7);};return [1,B(_fK(_j3,_j8))];},_ja=new T(function(){return B(unCStr("FS"));}),_jb=28,_jc=function(_jd){var _je=new T(function(){return B(A(_jd,[_jb]));}),_jf=function(_jg){return E(_je);};return [1,B(_fK(_ja,_jf))];},_jh=new T(function(){return B(unCStr("GS"));}),_ji=29,_jj=function(_jk){var _jl=new T(function(){return B(A(_jk,[_ji]));}),_jm=function(_jn){return E(_jl);};return [1,B(_fK(_jh,_jm))];},_jo=new T(function(){return B(unCStr("RS"));}),_jp=30,_jq=function(_jr){var _js=new T(function(){return B(A(_jr,[_jp]));}),_jt=function(_ju){return E(_js);};return [1,B(_fK(_jo,_jt))];},_jv=new T(function(){return B(unCStr("US"));}),_jw=31,_jx=function(_jy){var _jz=new T(function(){return B(A(_jy,[_jw]));}),_jA=function(_jB){return E(_jz);};return [1,B(_fK(_jv,_jA))];},_jC=new T(function(){return B(unCStr("SP"));}),_jD=32,_jE=function(_jF){var _jG=new T(function(){return B(A(_jF,[_jD]));}),_jH=function(_jI){return E(_jG);};return [1,B(_fK(_jC,_jH))];},_jJ=new T(function(){return B(unCStr("DEL"));}),_jK=127,_jL=function(_jM){var _jN=new T(function(){return B(A(_jM,[_jK]));}),_jO=function(_jP){return E(_jN);};return [1,B(_fK(_jJ,_jO))];},_jQ=[1,_jL,_F],_jR=[1,_jE,_jQ],_jS=[1,_jx,_jR],_jT=[1,_jq,_jS],_jU=[1,_jj,_jT],_jV=[1,_jc,_jU],_jW=[1,_j5,_jV],_jX=[1,_iY,_jW],_jY=[1,_iR,_jX],_jZ=[1,_iK,_jY],_k0=[1,_iD,_jZ],_k1=[1,_iw,_k0],_k2=[1,_ip,_k1],_k3=[1,_ii,_k2],_k4=[1,_ib,_k3],_k5=[1,_i4,_k4],_k6=[1,_hX,_k5],_k7=[1,_hQ,_k6],_k8=[1,_hJ,_k7],_k9=[1,_hC,_k8],_ka=[1,_hv,_k9],_kb=[1,_ho,_ka],_kc=[1,_hh,_kb],_kd=[1,_ha,_kc],_ke=[1,_h3,_kd],_kf=[1,_gW,_ke],_kg=[1,_gP,_kf],_kh=[1,_gI,_kg],_ki=[1,_gB,_kh],_kj=[1,_gu,_ki],_kk=[1,_gn,_kj],_kl=[1,_gg,_kk],_km=[1,_gc,_kl],_kn=new T(function(){return B(_fB(_km));}),_ko=34,_kp=[0,1114111],_kq=92,_kr=39,_ks=function(_kt){var _ku=new T(function(){return B(A(_kt,[_gV]));}),_kv=new T(function(){return B(A(_kt,[_h2]));}),_kw=new T(function(){return B(A(_kt,[_h9]));}),_kx=new T(function(){return B(A(_kt,[_hg]));}),_ky=new T(function(){return B(A(_kt,[_hn]));}),_kz=new T(function(){return B(A(_kt,[_hu]));}),_kA=new T(function(){return B(A(_kt,[_hB]));}),_kB=new T(function(){return B(A(_kt,[_kq]));}),_kC=new T(function(){return B(A(_kt,[_kr]));}),_kD=new T(function(){return B(A(_kt,[_ko]));}),_kE=new T(function(){var _kF=function(_kG){var _kH=new T(function(){return B(_dJ(E(_kG)));}),_kI=function(_kJ){var _kK=B(_el(_kH,_kJ));if(!B(_fr(_kK,_kp))){return [2];}else{var _kL=new T(function(){var _kM=B(_fo(_kK));if(_kM>>>0>1114111){return B(_fl(_kM));}else{return _kM;}});return new F(function(){return A(_kt,[_kL]);});}};return [1,B(_c5(_kG,_kI))];},_kN=new T(function(){var _kO=new T(function(){return B(A(_kt,[_jw]));}),_kP=new T(function(){return B(A(_kt,[_jp]));}),_kQ=new T(function(){return B(A(_kt,[_ji]));}),_kR=new T(function(){return B(A(_kt,[_jb]));}),_kS=new T(function(){return B(A(_kt,[_j4]));}),_kT=new T(function(){return B(A(_kt,[_iX]));}),_kU=new T(function(){return B(A(_kt,[_iQ]));}),_kV=new T(function(){return B(A(_kt,[_iJ]));}),_kW=new T(function(){return B(A(_kt,[_iC]));}),_kX=new T(function(){return B(A(_kt,[_iv]));}),_kY=new T(function(){return B(A(_kt,[_io]));}),_kZ=new T(function(){return B(A(_kt,[_ih]));}),_l0=new T(function(){return B(A(_kt,[_ia]));}),_l1=new T(function(){return B(A(_kt,[_i3]));}),_l2=new T(function(){return B(A(_kt,[_hW]));}),_l3=new T(function(){return B(A(_kt,[_hP]));}),_l4=new T(function(){return B(A(_kt,[_hI]));}),_l5=new T(function(){return B(A(_kt,[_fZ]));}),_l6=new T(function(){return B(A(_kt,[_gO]));}),_l7=new T(function(){return B(A(_kt,[_gH]));}),_l8=new T(function(){return B(A(_kt,[_gA]));}),_l9=new T(function(){return B(A(_kt,[_gt]));}),_la=new T(function(){return B(A(_kt,[_gm]));}),_lb=new T(function(){return B(A(_kt,[_g6]));}),_lc=new T(function(){return B(A(_kt,[_gf]));}),_ld=function(_le){switch(E(_le)){case 64:return E(_lc);case 65:return E(_lb);case 66:return E(_la);case 67:return E(_l9);case 68:return E(_l8);case 69:return E(_l7);case 70:return E(_l6);case 71:return E(_ku);case 72:return E(_kv);case 73:return E(_kw);case 74:return E(_kx);case 75:return E(_ky);case 76:return E(_kz);case 77:return E(_kA);case 78:return E(_l5);case 79:return E(_l4);case 80:return E(_l3);case 81:return E(_l2);case 82:return E(_l1);case 83:return E(_l0);case 84:return E(_kZ);case 85:return E(_kY);case 86:return E(_kX);case 87:return E(_kW);case 88:return E(_kV);case 89:return E(_kU);case 90:return E(_kT);case 91:return E(_kS);case 92:return E(_kR);case 93:return E(_kQ);case 94:return E(_kP);case 95:return E(_kO);default:return [2];}},_lf=[0,_ld],_lg=new T(function(){return B(A(_kn,[_kt]));}),_lh=function(_li){return (E(_li)==94)?E(_lf):[2];};return B(_9N([0,_lh],_lg));});return B(_9N([1,B(_bl(_fh,_fj,_kF))],_kN));}),_lj=function(_lk){switch(E(_lk)){case 34:return E(_kD);case 39:return E(_kC);case 92:return E(_kB);case 97:return E(_ku);case 98:return E(_kv);case 102:return E(_kz);case 110:return E(_kx);case 114:return E(_kA);case 116:return E(_kw);case 118:return E(_ky);default:return [2];}};return new F(function(){return _9N([0,_lj],_kE);});},_ll=function(_lm){return new F(function(){return A(_lm,[_6Q]);});},_ln=function(_lo){var _lp=E(_lo);if(!_lp[0]){return E(_ll);}else{var _lq=_lp[2],_lr=E(_lp[1]),_ls=_lr>>>0,_lt=new T(function(){return B(_ln(_lq));});if(_ls>887){var _lu=u_iswspace(_lr);if(!E(_lu)){return E(_ll);}else{var _lv=function(_lw){var _lx=new T(function(){return B(A(_lt,[_lw]));});return [0,function(_ly){return E(_lx);}];};return E(_lv);}}else{var _lz=E(_ls);if(_lz==32){var _lA=function(_lB){var _lC=new T(function(){return B(A(_lt,[_lB]));});return [0,function(_lD){return E(_lC);}];};return E(_lA);}else{if(_lz-9>>>0>4){if(E(_lz)==160){var _lE=function(_lF){var _lG=new T(function(){return B(A(_lt,[_lF]));});return [0,function(_lH){return E(_lG);}];};return E(_lE);}else{return E(_ll);}}else{var _lI=function(_lJ){var _lK=new T(function(){return B(A(_lt,[_lJ]));});return [0,function(_lL){return E(_lK);}];};return E(_lI);}}}}},_lM=function(_lN){var _lO=new T(function(){return B(_lM(_lN));}),_lP=function(_lQ){return (E(_lQ)==92)?E(_lO):[2];},_lR=[0,_lP],_lS=function(_lT){return E(_lR);},_lU=function(_lV){return new F(function(){return A(_ln,[_lV,_lS]);});},_lW=[1,_lU],_lX=new T(function(){var _lY=function(_lZ){return new F(function(){return A(_lN,[[0,_lZ,_86]]);});};return B(_ks(_lY));}),_m0=function(_m1){var _m2=E(_m1);if(_m2==38){return E(_lO);}else{var _m3=_m2>>>0;if(_m3>887){var _m4=u_iswspace(_m2);return (E(_m4)==0)?[2]:E(_lW);}else{var _m5=E(_m3);return (_m5==32)?E(_lW):(_m5-9>>>0>4)?(E(_m5)==160)?E(_lW):[2]:E(_lW);}}},_m6=[0,_m0],_m7=function(_m8){var _m9=E(_m8);if(E(_m9)==92){return E(_lX);}else{return new F(function(){return A(_lN,[[0,_m9,_fb]]);});}},_ma=function(_mb){return (E(_mb)==92)?E(_m6):[2];};return new F(function(){return _9N([0,_ma],[0,_m7]);});},_mc=function(_md,_me){var _mf=new T(function(){var _mg=new T(function(){return B(A(_md,[_F]));});return B(A(_me,[[1,_mg]]));}),_mh=function(_mi){var _mj=E(_mi),_mk=E(_mj[1]);if(E(_mk)==34){if(!E(_mj[2])){return E(_mf);}else{var _ml=function(_mm){return new F(function(){return A(_md,[[1,_mk,_mm]]);});};return new F(function(){return _mc(_ml,_me);});}}else{var _mn=function(_mo){return new F(function(){return A(_md,[[1,_mk,_mo]]);});};return new F(function(){return _mc(_mn,_me);});}};return new F(function(){return _lM(_mh);});},_mp=new T(function(){return B(unCStr("_\'"));}),_mq=function(_mr){var _ms=u_iswalnum(_mr);if(!E(_ms)){return new F(function(){return _f3(_aL,_mr,_mp);});}else{return true;}},_mt=function(_mu){return new F(function(){return _mq(E(_mu));});},_mv=new T(function(){return B(unCStr(",;()[]{}`"));}),_mw=new T(function(){return B(unCStr("=>"));}),_mx=[1,_mw,_F],_my=new T(function(){return B(unCStr("~"));}),_mz=[1,_my,_mx],_mA=new T(function(){return B(unCStr("@"));}),_mB=[1,_mA,_mz],_mC=new T(function(){return B(unCStr("->"));}),_mD=[1,_mC,_mB],_mE=new T(function(){return B(unCStr("<-"));}),_mF=[1,_mE,_mD],_mG=new T(function(){return B(unCStr("|"));}),_mH=[1,_mG,_mF],_mI=new T(function(){return B(unCStr("\\"));}),_mJ=[1,_mI,_mH],_mK=new T(function(){return B(unCStr("="));}),_mL=[1,_mK,_mJ],_mM=new T(function(){return B(unCStr("::"));}),_mN=[1,_mM,_mL],_mO=new T(function(){return B(unCStr(".."));}),_mP=[1,_mO,_mN],_mQ=function(_mR){var _mS=new T(function(){return B(A(_mR,[_c2]));}),_mT=new T(function(){var _mU=new T(function(){var _mV=function(_mW){var _mX=new T(function(){return B(A(_mR,[[0,_mW]]));});return [0,function(_mY){return (E(_mY)==39)?E(_mX):[2];}];};return B(_ks(_mV));}),_mZ=function(_n0){var _n1=E(_n0);switch(E(_n1)){case 39:return [2];case 92:return E(_mU);default:var _n2=new T(function(){return B(A(_mR,[[0,_n1]]));});return [0,function(_n3){return (E(_n3)==39)?E(_n2):[2];}];}},_n4=[0,_mZ],_n5=new T(function(){var _n6=new T(function(){return B(_mc(_2,_mR));}),_n7=new T(function(){var _n8=new T(function(){var _n9=new T(function(){var _na=new T(function(){return [1,B(_bl(_dg,_eZ,_mR))];}),_nb=function(_nc){var _nd=E(_nc),_ne=u_iswalpha(_nd);if(!E(_ne)){if(E(_nd)==95){var _nf=function(_ng){return new F(function(){return A(_mR,[[3,[1,_nd,_ng]]]);});};return [1,B(_bM(_mt,_nf))];}else{return [2];}}else{var _nh=function(_ni){return new F(function(){return A(_mR,[[3,[1,_nd,_ni]]]);});};return [1,B(_bM(_mt,_nh))];}};return B(_9N([0,_nb],_na));}),_nj=function(_nk){if(!B(_f3(_aL,_nk,_f8))){return [2];}else{var _nl=function(_nm){var _nn=[1,_nk,_nm];if(!B(_f3(_aU,_nn,_mP))){return new F(function(){return A(_mR,[[4,_nn]]);});}else{return new F(function(){return A(_mR,[[2,_nn]]);});}};return [1,B(_bM(_f9,_nl))];}};return B(_9N([0,_nj],_n9));}),_no=function(_np){if(!B(_f3(_aL,_np,_mv))){return [2];}else{return new F(function(){return A(_mR,[[2,[1,_np,_F]]]);});}};return B(_9N([0,_no],_n8));}),_nq=function(_nr){return (E(_nr)==34)?E(_n6):[2];};return B(_9N([0,_nq],_n7));}),_ns=function(_nt){return (E(_nt)==39)?E(_n4):[2];};return B(_9N([0,_ns],_n5));}),_nu=function(_nv){return (E(_nv)[0]==0)?E(_mS):[2];};return new F(function(){return _9N([1,_nu],_mT);});},_nw=0,_nx=function(_ny,_nz){var _nA=new T(function(){var _nB=new T(function(){var _nC=function(_nD){var _nE=new T(function(){var _nF=new T(function(){return B(A(_nz,[_nD]));}),_nG=function(_nH){var _nI=E(_nH);return (_nI[0]==2)?(!B(_aA(_nI[1],_az)))?[2]:E(_nF):[2];};return B(_mQ(_nG));}),_nJ=function(_nK){return E(_nE);};return [1,function(_nL){return new F(function(){return A(_ln,[_nL,_nJ]);});}];};return B(A(_ny,[_nw,_nC]));}),_nM=function(_nN){var _nO=E(_nN);return (_nO[0]==2)?(!B(_aA(_nO[1],_ay)))?[2]:E(_nB):[2];};return B(_mQ(_nM));}),_nP=function(_nQ){return E(_nA);};return function(_nR){return new F(function(){return A(_ln,[_nR,_nP]);});};},_nS=function(_nT,_nU){var _nV=function(_nW){var _nX=new T(function(){return B(A(_nT,[_nW]));}),_nY=function(_nZ){var _o0=new T(function(){return [1,B(_nx(_nV,_nZ))];});return new F(function(){return _9N(B(A(_nX,[_nZ])),_o0);});};return E(_nY);},_o1=new T(function(){return B(A(_nT,[_nU]));}),_o2=function(_o3){var _o4=new T(function(){return [1,B(_nx(_nV,_o3))];});return new F(function(){return _9N(B(A(_o1,[_o3])),_o4);});};return E(_o2);},_o5=function(_o6,_o7){var _o8=function(_o9,_oa){var _ob=function(_oc){var _od=new T(function(){return  -E(_oc);});return new F(function(){return A(_oa,[_od]);});},_oe=function(_of){return new F(function(){return A(_o6,[_of,_o9,_ob]);});},_og=new T(function(){return B(_mQ(_oe));}),_oh=function(_oi){return E(_og);},_oj=function(_ok){return new F(function(){return A(_ln,[_ok,_oh]);});},_ol=[1,_oj],_om=function(_on){var _oo=E(_on);if(_oo[0]==4){var _op=E(_oo[1]);if(!_op[0]){return new F(function(){return A(_o6,[_oo,_o9,_oa]);});}else{if(E(_op[1])==45){if(!E(_op[2])[0]){return E(_ol);}else{return new F(function(){return A(_o6,[_oo,_o9,_oa]);});}}else{return new F(function(){return A(_o6,[_oo,_o9,_oa]);});}}}else{return new F(function(){return A(_o6,[_oo,_o9,_oa]);});}},_oq=new T(function(){return B(_mQ(_om));}),_or=function(_os){return E(_oq);};return [1,function(_ot){return new F(function(){return A(_ln,[_ot,_or]);});}];};return new F(function(){return _nS(_o8,_o7);});},_ou=function(_ov){var _ow=E(_ov);if(!_ow[0]){var _ox=_ow[1],_oy=_ow[2];return [1,new T(function(){var _oz=new T(function(){return B(_dE(_oy,0));},1),_oA=new T(function(){return B(_dJ(E(_ox)));});return B(_e5(_oA,_oz,B(_3v(_dL,_oy))));})];}else{var _oB=_ow[1];if(!E(_ow[2])[0]){if(!E(_ow[3])[0]){return [1,new T(function(){return B(_el(_dD,_oB));})];}else{return [0];}}else{return [0];}}},_oC=function(_oD,_oE){return [2];},_oF=function(_oG){var _oH=E(_oG);if(_oH[0]==5){var _oI=B(_ou(_oH[1]));if(!_oI[0]){return E(_oC);}else{var _oJ=_oI[1],_oK=new T(function(){return B(_fo(_oJ));}),_oL=function(_oM,_oN){return new F(function(){return A(_oN,[_oK]);});};return E(_oL);}}else{return E(_oC);}},_oO=new T(function(){return B(unCStr("="));}),_oP=new T(function(){return B(unCStr("onPointIndex"));}),_oQ=new T(function(){return B(unCStr(","));}),_oR=new T(function(){return B(unCStr("pointIndex"));}),_oS=new T(function(){return B(unCStr("{"));}),_oT=new T(function(){return B(unCStr("PointPlacement"));}),_oU=new T(function(){return B(unCStr("onBarIndex"));}),_oV=new T(function(){return B(unCStr("BarPlacement"));}),_oW=new T(function(){return B(unCStr("onSideIndex"));}),_oX=new T(function(){return B(unCStr("LeftSidePlacement"));}),_oY=new T(function(){return B(unCStr("RightSidePlacement"));}),_oZ=function(_p0,_p1){var _p2=new T(function(){var _p3=new T(function(){var _p4=new T(function(){if(_p0>11){return [2];}else{var _p5=new T(function(){var _p6=new T(function(){var _p7=new T(function(){var _p8=new T(function(){var _p9=new T(function(){var _pa=function(_pb){var _pc=new T(function(){var _pd=new T(function(){return B(A(_p1,[[3,_pb]]));}),_pe=function(_pf){var _pg=E(_pf);return (_pg[0]==2)?(!B(_aA(_pg[1],_7k)))?[2]:E(_pd):[2];};return B(_mQ(_pe));}),_ph=function(_pi){return E(_pc);};return [1,function(_pj){return new F(function(){return A(_ln,[_pj,_ph]);});}];};return B(A(_o5,[_oF,_nw,_pa]));}),_pk=function(_pl){var _pm=E(_pl);return (_pm[0]==2)?(!B(_aA(_pm[1],_oO)))?[2]:E(_p9):[2];};return B(_mQ(_pk));}),_pn=function(_po){return E(_p8);},_pp=function(_pq){return new F(function(){return A(_ln,[_pq,_pn]);});},_pr=[1,_pp],_ps=function(_pt){var _pu=E(_pt);return (_pu[0]==3)?(!B(_aA(_pu[1],_oW)))?[2]:E(_pr):[2];};return B(_mQ(_ps));}),_pv=function(_pw){return E(_p7);},_px=function(_py){return new F(function(){return A(_ln,[_py,_pv]);});},_pz=[1,_px],_pA=function(_pB){var _pC=E(_pB);return (_pC[0]==2)?(!B(_aA(_pC[1],_oS)))?[2]:E(_pz):[2];};return B(_mQ(_pA));}),_pD=function(_pE){return E(_p6);},_pF=function(_pG){return new F(function(){return A(_ln,[_pG,_pD]);});},_pH=[1,_pF],_pI=function(_pJ){var _pK=E(_pJ);return (_pK[0]==3)?(!B(_aA(_pK[1],_oY)))?[2]:E(_pH):[2];};return B(_mQ(_pI));}),_pL=function(_pM){return E(_p5);};return [1,function(_pN){return new F(function(){return A(_ln,[_pN,_pL]);});}];}});if(_p0>11){return B(_9N(_bc,_p4));}else{var _pO=new T(function(){var _pP=new T(function(){var _pQ=new T(function(){var _pR=new T(function(){var _pS=new T(function(){var _pT=function(_pU){var _pV=new T(function(){var _pW=new T(function(){return B(A(_p1,[[2,_pU]]));}),_pX=function(_pY){var _pZ=E(_pY);return (_pZ[0]==2)?(!B(_aA(_pZ[1],_7k)))?[2]:E(_pW):[2];};return B(_mQ(_pX));}),_q0=function(_q1){return E(_pV);};return [1,function(_q2){return new F(function(){return A(_ln,[_q2,_q0]);});}];};return B(A(_o5,[_oF,_nw,_pT]));}),_q3=function(_q4){var _q5=E(_q4);return (_q5[0]==2)?(!B(_aA(_q5[1],_oO)))?[2]:E(_pS):[2];};return B(_mQ(_q3));}),_q6=function(_q7){return E(_pR);},_q8=function(_q9){return new F(function(){return A(_ln,[_q9,_q6]);});},_qa=[1,_q8],_qb=function(_qc){var _qd=E(_qc);return (_qd[0]==3)?(!B(_aA(_qd[1],_oW)))?[2]:E(_qa):[2];};return B(_mQ(_qb));}),_qe=function(_qf){return E(_pQ);},_qg=function(_qh){return new F(function(){return A(_ln,[_qh,_qe]);});},_qi=[1,_qg],_qj=function(_qk){var _ql=E(_qk);return (_ql[0]==2)?(!B(_aA(_ql[1],_oS)))?[2]:E(_qi):[2];};return B(_mQ(_qj));}),_qm=function(_qn){return E(_pP);},_qo=function(_qp){return new F(function(){return A(_ln,[_qp,_qm]);});},_qq=[1,_qo],_qr=function(_qs){var _qt=E(_qs);return (_qt[0]==3)?(!B(_aA(_qt[1],_oX)))?[2]:E(_qq):[2];};return B(_mQ(_qr));}),_qu=function(_qv){return E(_pO);},_qw=function(_qx){return new F(function(){return A(_ln,[_qx,_qu]);});};return B(_9N([1,_qw],_p4));}});if(_p0>11){return B(_9N(_bc,_p3));}else{var _qy=new T(function(){var _qz=new T(function(){var _qA=new T(function(){var _qB=new T(function(){var _qC=new T(function(){var _qD=function(_qE){var _qF=new T(function(){var _qG=new T(function(){return B(A(_p1,[[1,_qE]]));}),_qH=function(_qI){var _qJ=E(_qI);return (_qJ[0]==2)?(!B(_aA(_qJ[1],_7k)))?[2]:E(_qG):[2];};return B(_mQ(_qH));}),_qK=function(_qL){return E(_qF);};return [1,function(_qM){return new F(function(){return A(_ln,[_qM,_qK]);});}];};return B(A(_o5,[_oF,_nw,_qD]));}),_qN=function(_qO){var _qP=E(_qO);return (_qP[0]==2)?(!B(_aA(_qP[1],_oO)))?[2]:E(_qC):[2];};return B(_mQ(_qN));}),_qQ=function(_qR){return E(_qB);},_qS=function(_qT){return new F(function(){return A(_ln,[_qT,_qQ]);});},_qU=[1,_qS],_qV=function(_qW){var _qX=E(_qW);return (_qX[0]==3)?(!B(_aA(_qX[1],_oU)))?[2]:E(_qU):[2];};return B(_mQ(_qV));}),_qY=function(_qZ){return E(_qA);},_r0=function(_r1){return new F(function(){return A(_ln,[_r1,_qY]);});},_r2=[1,_r0],_r3=function(_r4){var _r5=E(_r4);return (_r5[0]==2)?(!B(_aA(_r5[1],_oS)))?[2]:E(_r2):[2];};return B(_mQ(_r3));}),_r6=function(_r7){return E(_qz);},_r8=function(_r9){return new F(function(){return A(_ln,[_r9,_r6]);});},_ra=[1,_r8],_rb=function(_rc){var _rd=E(_rc);return (_rd[0]==3)?(!B(_aA(_rd[1],_oV)))?[2]:E(_ra):[2];};return B(_mQ(_rb));}),_re=function(_rf){return E(_qy);},_rg=function(_rh){return new F(function(){return A(_ln,[_rh,_re]);});};return B(_9N([1,_rg],_p3));}});if(_p0>11){return new F(function(){return _9N(_bc,_p2);});}else{var _ri=new T(function(){var _rj=new T(function(){var _rk=new T(function(){var _rl=new T(function(){var _rm=new T(function(){var _rn=function(_ro){var _rp=new T(function(){var _rq=new T(function(){var _rr=new T(function(){var _rs=new T(function(){var _rt=function(_ru){var _rv=new T(function(){var _rw=new T(function(){return B(A(_p1,[[0,_ro,_ru]]));}),_rx=function(_ry){var _rz=E(_ry);return (_rz[0]==2)?(!B(_aA(_rz[1],_7k)))?[2]:E(_rw):[2];};return B(_mQ(_rx));}),_rA=function(_rB){return E(_rv);};return [1,function(_rC){return new F(function(){return A(_ln,[_rC,_rA]);});}];};return B(A(_o5,[_oF,_nw,_rt]));}),_rD=function(_rE){var _rF=E(_rE);return (_rF[0]==2)?(!B(_aA(_rF[1],_oO)))?[2]:E(_rs):[2];};return B(_mQ(_rD));}),_rG=function(_rH){return E(_rr);},_rI=function(_rJ){return new F(function(){return A(_ln,[_rJ,_rG]);});},_rK=[1,_rI],_rL=function(_rM){var _rN=E(_rM);return (_rN[0]==3)?(!B(_aA(_rN[1],_oP)))?[2]:E(_rK):[2];};return B(_mQ(_rL));}),_rO=function(_rP){return E(_rq);},_rQ=function(_rR){return new F(function(){return A(_ln,[_rR,_rO]);});},_rS=[1,_rQ],_rT=function(_rU){var _rV=E(_rU);return (_rV[0]==2)?(!B(_aA(_rV[1],_oQ)))?[2]:E(_rS):[2];};return B(_mQ(_rT));}),_rW=function(_rX){return E(_rp);};return [1,function(_rY){return new F(function(){return A(_ln,[_rY,_rW]);});}];};return B(A(_o5,[_oF,_nw,_rn]));}),_rZ=function(_s0){var _s1=E(_s0);return (_s1[0]==2)?(!B(_aA(_s1[1],_oO)))?[2]:E(_rm):[2];};return B(_mQ(_rZ));}),_s2=function(_s3){return E(_rl);},_s4=function(_s5){return new F(function(){return A(_ln,[_s5,_s2]);});},_s6=[1,_s4],_s7=function(_s8){var _s9=E(_s8);return (_s9[0]==3)?(!B(_aA(_s9[1],_oR)))?[2]:E(_s6):[2];};return B(_mQ(_s7));}),_sa=function(_sb){return E(_rk);},_sc=function(_sd){return new F(function(){return A(_ln,[_sd,_sa]);});},_se=[1,_sc],_sf=function(_sg){var _sh=E(_sg);return (_sh[0]==2)?(!B(_aA(_sh[1],_oS)))?[2]:E(_se):[2];};return B(_mQ(_sf));}),_si=function(_sj){return E(_rj);},_sk=function(_sl){return new F(function(){return A(_ln,[_sl,_si]);});},_sm=[1,_sk],_sn=function(_so){var _sp=E(_so);return (_sp[0]==3)?(!B(_aA(_sp[1],_oT)))?[2]:E(_sm):[2];};return B(_mQ(_sn));}),_sq=function(_sr){return E(_ri);},_ss=function(_st){return new F(function(){return A(_ln,[_st,_sq]);});};return new F(function(){return _9N([1,_ss],_p2);});}},_su=function(_sv,_sw){return new F(function(){return _oZ(E(_sv),_sw);});},_sx=function(_sy){var _sz=[3,_sy,_bc],_sA=function(_sB){return E(_sz);};return [1,function(_sC){return new F(function(){return A(_ln,[_sC,_sA]);});}];},_sD=new T(function(){return B(A(_nS,[_su,_nw,_sx]));}),_sE=new T(function(){return B(err(_9v));}),_sF=new T(function(){return B(err(_9x));}),_sG=function(_sH,_sI){return new F(function(){return A(_sI,[_3f]);});},_sJ=[0,_88,_sG],_sK=[1,_sJ,_F],_sL=function(_sM,_sN){return new F(function(){return A(_sN,[_3r]);});},_sO=[0,_87,_sL],_sP=[1,_sO,_sK],_sQ=function(_sR,_sS,_sT){var _sU=E(_sR);if(!_sU[0]){return [2];}else{var _sV=_sU[2],_sW=E(_sU[1]),_sX=_sW[1],_sY=_sW[2],_sZ=new T(function(){return B(A(_sY,[_sS,_sT]));}),_t0=function(_t1){var _t2=E(_t1);switch(_t2[0]){case 3:return (!B(_aA(_sX,_t2[1])))?[2]:E(_sZ);case 4:return (!B(_aA(_sX,_t2[1])))?[2]:E(_sZ);default:return [2];}},_t3=new T(function(){return B(_mQ(_t0));}),_t4=function(_t5){return E(_t3);},_t6=new T(function(){return B(_sQ(_sV,_sS,_sT));}),_t7=function(_t8){return new F(function(){return A(_ln,[_t8,_t4]);});};return new F(function(){return _9N([1,_t7],_t6);});}},_t9=function(_ta,_tb){return new F(function(){return _sQ(_sP,_ta,_tb);});},_tc=new T(function(){return B(A(_nS,[_t9,_nw,_sx]));}),_td=function(_te){var _tf=E(_te);return (E(_tf)==95)?32:E(_tf);},_tg=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:241:9-15"));}),_th=[0,_2z,_2A,_F,_tg,_2z,_2z],_ti=new T(function(){return B(_2x(_th));}),_tj=new T(function(){return B(unCStr("joinGame"));}),_tk=function(_tl){return E(E(_tl)[1]);},_tm=function(_tn){return E(E(_tn)[1]);},_to=function(_tp){return E(E(_tp)[2]);},_tq=function(_tr){return E(E(_tr)[2]);},_ts=function(_tt){return E(E(_tt)[1]);},_tu=function(_){return new F(function(){return nMV(_2z);});},_tv=new T(function(){return B(_6e(_tu));}),_tw=(function(e,name,f){e.addEventListener(name,f,false);return [f];}),_tx=function(_ty){return E(E(_ty)[2]);},_tz=function(_tA){return E(E(_tA)[4]);},_tB=function(_tC,_tD,_tE,_tF,_tG,_tH){var _tI=B(_tk(_tC)),_tJ=B(_tm(_tI)),_tK=new T(function(){return B(_8h(_tI));}),_tL=new T(function(){return B(_tz(_tJ));}),_tM=new T(function(){return B(A(_8f,[_tD,_tF]));}),_tN=new T(function(){return B(A(_ts,[_tE,_tG]));}),_tO=function(_tP){return new F(function(){return A(_tL,[[0,_tN,_tM,_tP]]);});},_tQ=function(_tR){var _tS=new T(function(){var _tT=new T(function(){var _tU=E(_tM),_tV=E(_tN),_tW=E(_tR),_tX=function(_tY,_){var _tZ=B(A(_tW,[_tY,_]));return _6i;},_u0=__createJSFunc(2,E(_tX)),_u1=_u0,_u2=function(_){return new F(function(){return E(_tw)(_tU,_tV,_u1);});};return E(_u2);});return B(A(_tK,[_tT]));});return new F(function(){return A(_to,[_tJ,_tS,_tO]);});},_u3=new T(function(){var _u4=new T(function(){return B(_8h(_tI));}),_u5=function(_u6){var _u7=new T(function(){var _u8=function(_){var _=wMV(E(_tv),[1,_u6]);return new F(function(){return A(_tq,[_tE,_tG,_u6,_]);});};return B(A(_u4,[_u8]));});return new F(function(){return A(_to,[_tJ,_u7,_tH]);});};return B(A(_tx,[_tC,_u5]));});return new F(function(){return A(_to,[_tJ,_u3,_tQ]);});},_u9=function(_ua,_ub){var _uc=E(_ub);if(!_uc[0]){return [0];}else{var _ud=_uc[1],_ue=_uc[2],_uf=E(_ua);if(_uf==1){return [1,_ud,_F];}else{var _ug=new T(function(){return B(_u9(_uf-1|0,_ue));});return [1,_ud,_ug];}}},_uh=function(_ui,_uj,_uk){if(_uk<=_uj){var _ul=new T(function(){var _um=_uj-_ui|0,_un=_uk-_um|0,_uo=function(_up){if(_up>=_un){var _uq=new T(function(){return B(_uo(_up+_um|0));});return [1,_up,_uq];}else{return [1,_up,_F];}};return B(_uo(_uj));});return [1,_ui,_ul];}else{return (_uk<=_ui)?[1,_ui,_F]:[0];}},_ur=function(_us,_ut,_uu){if(_uu>=_ut){var _uv=new T(function(){var _uw=_ut-_us|0,_ux=_uu-_uw|0,_uy=function(_uz){if(_uz<=_ux){var _uA=new T(function(){return B(_uy(_uz+_uw|0));});return [1,_uz,_uA];}else{return [1,_uz,_F];}};return B(_uy(_ut));});return [1,_us,_uv];}else{return (_uu>=_us)?[1,_us,_F]:[0];}},_uB=function(_uC,_uD){if(_uD<_uC){return new F(function(){return _uh(_uC,_uD,-2147483648);});}else{return new F(function(){return _ur(_uC,_uD,2147483647);});}},_uE=new T(function(){return B(_uB(135,150));}),_uF=new T(function(){return B(_u9(6,_uE));}),_uG=function(_uH,_uI){var _uJ=E(_uH);if(!_uJ[0]){return E(_uF);}else{var _uK=_uJ[1],_uL=_uJ[2],_uM=E(_uI);if(_uM==1){return [1,_uK,_uF];}else{var _uN=new T(function(){return B(_uG(_uL,_uM-1|0));});return [1,_uK,_uN];}}},_uO=new T(function(){return B(_uB(25,40));}),_uP=new T(function(){return B(_uG(_uO,6));}),_uQ=function(_uR){while(1){var _uS=(function(_uT){var _uU=E(_uT);if(!_uU[0]){return [0];}else{var _uV=_uU[2],_uW=E(_uU[1]);if(!E(_uW[2])[0]){var _uX=new T(function(){return B(_uQ(_uV));});return [1,_uW[1],_uX];}else{_uR=_uV;return null;}}})(_uR);if(_uS!=null){return _uS;}}},_uY=function(_uZ,_v0){var _v1=E(_v0);if(!_v1[0]){return [0,_F,_F];}else{var _v2=_v1[1],_v3=_v1[2];if(!B(A(_uZ,[_v2]))){var _v4=new T(function(){var _v5=B(_uY(_uZ,_v3));return [0,_v5[1],_v5[2]];}),_v6=new T(function(){return E(E(_v4)[2]);}),_v7=new T(function(){return E(E(_v4)[1]);});return [0,[1,_v2,_v7],_v6];}else{return [0,_F,_v1];}}},_v8=function(_v9,_va){while(1){var _vb=E(_va);if(!_vb[0]){return [0];}else{if(!B(A(_v9,[_vb[1]]))){return E(_vb);}else{_va=_vb[2];continue;}}}},_vc=function(_vd){var _ve=_vd>>>0;if(_ve>887){var _vf=u_iswspace(_vd);return (E(_vf)==0)?false:true;}else{var _vg=E(_ve);return (_vg==32)?true:(_vg-9>>>0>4)?(E(_vg)==160)?true:false:true;}},_vh=function(_vi){return new F(function(){return _vc(E(_vi));});},_vj=function(_vk){var _vl=B(_v8(_vh,_vk));if(!_vl[0]){return [0];}else{var _vm=new T(function(){var _vn=B(_uY(_vh,_vl));return [0,_vn[1],_vn[2]];}),_vo=new T(function(){return B(_vj(E(_vm)[2]));}),_vp=new T(function(){return E(E(_vm)[1]);});return [1,_vp,_vo];}},_vq=function(_vr,_){var _vs=jsFind(toJSStr(E(_tj)));if(!_vs[0]){return new F(function(){return die(_ti);});}else{var _vt=B(A(_tB,[_6S,_4,_6P,_vs[1],_78,_7i,_])),_vu=function(_vv){var _vw=new T(function(){var _vx=String(E(_vv));return B(_vj(fromJSStr(_vx)));}),_vy=new T(function(){var _vz=new T(function(){return B(_3v(_td,B(_75(_vw,2))));});return B(_uQ(B(_9B(_sD,_vz))));}),_vA=new T(function(){var _vB=new T(function(){return B(_75(_vw,1));}),_vC=B(_uQ(B(_9B(_tc,_vB))));if(!_vC[0]){return E(_sE);}else{if(!E(_vC[2])[0]){return E(_vC[1]);}else{return E(_sF);}}}),_vD=function(_vE){var _vF=new T(function(){var _vG=new T(function(){var _vH=B(A(_vE,[_]));return E(_vH);}),_vI=function(_vJ){var _vK=E(_vJ)-E(_vG);return (_vK==0)?true:(_vK<=0)? -_vK<7:_vK<7;};return B(_9g(_vI,_uP));}),_vL=function(_vM,_){var _vN=E(_vr),_vO=_vN[1],_vP=_vN[2],_vQ=_vN[3],_vR=_vN[4],_vS=_vN[5],_vT=_vN[6],_vU=_vN[7],_vV=E(_vy);if(!_vV[0]){return E(_9w);}else{if(!E(_vV[2])[0]){var _vW=E(_vV[1]);if(!_vW[0]){var _vX=_vW[1],_vY=_vW[2],_vZ=E(_vF);if(!_vZ[0]){var _w0=B(_8N(_vW,_vW,_vA,_));return _6i;}else{var _w1=_vZ[1],_w2=B(A(_vM,[_])),_w3=function(_w4,_w5){var _w6=E(_vX),_w7=_w6;if(_w4<=_w7){return new F(function(){return _8N(_vW,_vW,_vA,_);});}else{var _w8=B(_75(_vO,_w4)),_w9=_w8[2],_wa=function(_){var _wb=B(_8N(_vW,[0,_w5,_w9],_vA,_)),_wc=new T(function(){return E(B(_75(_vO,_w7))[1]);}),_wd=function(_we,_wf){var _wg=E(_we);if(!_wg[0]){return [0];}else{var _wh=_wg[1],_wi=_wg[2],_wj=E(_wf);if(!_wj[0]){return [0];}else{var _wk=_wj[1],_wl=_wj[2],_wm=new T(function(){return B(_wd(_wi,_wl));}),_wn=new T(function(){var _wo=E(_wh);if(_wo!=_w7){if(_wo!=_w4){return E(_wk);}else{var _wp=new T(function(){return E(E(_wk)[2])+1|0;});return [0,_wc,_wp];}}else{var _wq=new T(function(){return E(E(_wk)[2])-1|0;}),_wr=new T(function(){return E(E(_wk)[1]);});return [0,_wr,_wq];}});return [1,_wn,_wm];}}},_ws=B(_wd(_9u,_vO)),_wt=function(_wu,_){while(1){var _wv=(function(_ww,_){var _wx=E(_ww);if(!_wx[0]){return _6Q;}else{var _wy=_wx[1],_wz=new T(function(){return E(_wy)-1|0;}),_wA=B(_8N([0,_w6,_wy],[0,_w6,_wz],_vT,_));_wu=_wx[2];return null;}})(_wu,_);if(_wv!=null){return _wv;}}},_wB=function(_wC,_wD){while(1){var _wE=E(_wD);if(!_wE[0]){return [0];}else{var _wF=_wE[2],_wG=E(_wC);if(_wG==1){return E(_wF);}else{_wC=_wG-1|0;_wD=_wF;continue;}}}},_wH=B(_wt(B(_wB(1,B(_99(E(_vY),E(B(_75(_ws,_w7))[2]))))),_));return new F(function(){return _vq([0,_ws,_vP,_vQ,_vR,_vS,_vT,_vU],_);});},_wI=function(_){if(E(_w9)>=2){return new F(function(){return _8N(_vW,_vW,_vA,_);});}else{return new F(function(){return _wa(_);});}};if(!E(_w8[1])){if(!E(_vA)){return new F(function(){return _wa(_);});}else{return new F(function(){return _wI(_);});}}else{if(!E(_vA)){return new F(function(){return _wI(_);});}else{return new F(function(){return _wa(_);});}}}};if(E(_w2)<=E(_9z)){var _wJ=E(_w1),_wK=B(_w3(_wJ,_wJ));return _6i;}else{var _wL=23-E(_w1)|0,_wM=B(_w3(_wL,_wL));return _6i;}}}else{var _wN=B(_8N(_vW,_vW,_vA,_));return _6i;}}else{return E(_9y);}}};return E(_vL);};return E(_vD);},_wO=__createJSFunc(4,E(_vu)),_wP=E(_9f)(_wO);return new F(function(){return _6R(_);});}},_wQ=function(_){return _6Q;},_wR=new T(function(){return (function (ns,tag) {return document.createElementNS(ns, tag);});}),_wS=new T(function(){return B(unCStr("cy"));}),_wT=new T(function(){return B(unCStr("cx"));}),_wU=new T(function(){return B(unCStr("r"));}),_wV=new T(function(){return B(_5j(0,6,_F));}),_wW=new T(function(){return B(unCStr("circle"));}),_wX=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_wY=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:152:5-10"));}),_wZ=[0,_2z,_2A,_F,_wY,_2z,_2z],_x0=new T(function(){return B(_2x(_wZ));}),_x1=new T(function(){return B(unCStr("board"));}),_x2=function(_x3,_x4,_){while(1){var _x5=(function(_x6,_x7,_){var _x8=E(_x7);if(!_x8[0]){return _6Q;}else{var _x9=_x8[2],_xa=E(_x8[1]),_xb=_xa[1],_xc=E(_xa[2]);if(0>=_xc){var _xd=E(_x6);if(_xd==2147483647){return _6Q;}else{_x3=_xd+1|0;_x4=_x9;return null;}}else{var _xe=_x6,_xf=new T(function(){if(!E(_xb)){return false;}else{return true;}}),_xg=function(_xh,_xi,_){var _xj=jsFind(toJSStr(E(_x1)));if(!_xj[0]){return new F(function(){return die(_x0);});}else{var _xk=E(_wR)(toJSStr(_wX),toJSStr(_wW)),_xl=B(A(_8j,[_4,_2I,_xk,_wU,_wV,_])),_xm=new T(function(){if(_x6>=12){var _xn=23-_x6|0;if(_xn>=6){return B(_5j(0,25+(20+(imul(_xn,15)|0)|0)|0,_F));}else{return B(_5j(0,25+(imul(_xn,15)|0)|0,_F));}}else{if(_x6>=6){return B(_5j(0,25+(20+(imul(_x6,15)|0)|0)|0,_F));}else{return B(_5j(0,25+(imul(_x6,15)|0)|0,_F));}}}),_xo=B(A(_8j,[_4,_2I,_xk,_wT,_xm,_])),_xp=new T(function(){if(_x6>=12){return B(_5j(0,203+(imul(imul(imul(-1,E(_xh))|0,2)|0,6)|0)|0,_F));}else{return B(_5j(0,7+(imul(imul(E(_xh),2)|0,6)|0)|0,_F));}}),_xq=B(A(_8j,[_4,_2I,_xk,_wS,_xp,_])),_xr=B(_8r(_xk,_xb,_xf,[0,_xe,_xh],_)),_xs=jsAppendChild(_xk,E(_xj[1]));return new F(function(){return A(_xi,[_]);});}},_xt=function(_xu,_xv,_){var _xw=E(_xu);if(!_xw[0]){return _6Q;}else{var _xx=_xw[1],_xy=_xw[2],_xz=E(_xv);if(_xz==1){return new F(function(){return _xg(_xx,_wQ,_);});}else{var _xA=function(_){return new F(function(){return _xt(_xy,_xz-1|0,_);});};return new F(function(){return _xg(_xx,_xA,_);});}}},_xB=B(_xt(_9u,_xc,_)),_xC=E(_x6);if(_xC==2147483647){return _6Q;}else{_x3=_xC+1|0;_x4=_x9;return null;}}}})(_x3,_x4,_);if(_x5!=null){return _x5;}}},_xD=new T(function(){return B(unCStr("You have not joined a game (yet)."));}),_xE=new T(function(){return B(unCStr("innerHTML"));}),_xF=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:261:9-15"));}),_xG=[0,_2z,_2A,_F,_xF,_2z,_2z],_xH=new T(function(){return B(_2x(_xG));}),_xI=function(_xJ,_xK,_xL,_xM,_xN){var _xO=function(_){var _xP=jsSet(B(A(_8f,[_xJ,_xL])),toJSStr(E(_xM)),toJSStr(E(_xN)));return _6Q;};return new F(function(){return A(_8h,[_xK,_xO]);});},_xQ=function(_){var _xR=jsFind("HintText");if(!_xR[0]){return new F(function(){return die(_xH);});}else{var _xS=B(A(_xI,[_4,_2I,_xR[1],_xE,_xD,_])),_xT=B(_x2(0,_4Y,_));return new F(function(){return _vq(_59,_);});}},_xU=function(_){return new F(function(){return _xQ(_);});};
var hasteMain = function() {B(A(_xU, [0]));};window.onload = hasteMain;