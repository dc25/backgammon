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

function F(f) {
    this.f = f;
}

// Special object used for blackholing.
var __blackhole = {};

// Used to indicate that an object is updatable.
var __updatable = {};

/* Apply
   Applies the function f to the arguments args. If the application is under-
   saturated, a closure is returned, awaiting further arguments. If it is over-
   saturated, the function is fully applied, and the result (assumed to be a
   function) is then applied to the remaining arguments.
*/
function A(f, args) {
    if(f instanceof T) {
        f = E(f);
    }
    // Closure does some funny stuff with functions that occasionally
    // results in non-functions getting applied, so we have to deal with
    // it.
    if(!(f instanceof Function)) {
        f = B(f);
        if(!(f instanceof Function)) {
            return f;
        }
    }

    if(f.arity === undefined) {
        f.arity = f.length;
    }
    if(args.length === f.arity) {
        switch(f.arity) {
            case 0:  return f();
            case 1:  return f(args[0]);
            default: return f.apply(null, args);
        }
    } else if(args.length > f.arity) {
        switch(f.arity) {
            case 0:  return f();
            case 1:  return A(f(args.shift()), args);
            default: return A(f.apply(null, args.splice(0, f.arity)), args);
        }
    } else {
        var g = function() {
            return A(f, args.concat(Array.prototype.slice.call(arguments)));
        };
        g.arity = f.arity - args.length;
        return g;
    }
}

/* Eval
   Evaluate the given thunk t into head normal form.
   If the "thunk" we get isn't actually a thunk, just return it.
*/
function E(t) {
    if(t instanceof T) {
        if(t.f !== __blackhole) {
            var f = t.f;
            t.f = __blackhole;
            if(t.x === __updatable) {
                t.x = f();
            } else {
                return f();
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
    throw err;
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

// Scratch space for byte arrays.
var rts_scratchBuf = new ArrayBuffer(8);
var rts_scratchW32 = new Uint32Array(rts_scratchBuf);
var rts_scratchFloat = new Float32Array(rts_scratchBuf);
var rts_scratchDouble = new Float64Array(rts_scratchBuf);

function decodeFloat(x) {
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
        acc = B(A(f, [[0, str.charCodeAt(i)], acc]));
    }
    return acc;
}

function unAppCStr(str, chrs) {
    var i = arguments[2] ? arguments[2] : 0;
    if(i >= str.length) {
        return E(chrs);
    } else {
        return [1,[0,str.charCodeAt(i)],new T(function() {
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
        s += String.fromCharCode(E(str[1])[1]);
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
        return [0];
    } else if(a == b) {
        return [1];
    }
    return [2];
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
var jsRound = Math.round;
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

function popCnt(i) {
    i = i - ((i >> 1) & 0x55555555);
    i = (i & 0x33333333) + ((i >> 2) & 0x33333333);
    return (((i + (i >> 4)) & 0x0F0F0F0F) * 0x01010101) >> 24;
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

function jsGetMouseCoords(e) {
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

function jsSetCB(elem, evt, cb) {
    // Count return press in single line text box as a change event.
    if(evt == 'change' && elem.type.toLowerCase() == 'text') {
        setCB(elem, 'keyup', function(k) {
            if(k == '\n'.charCodeAt(0)) {
                B(A(cb,[[0,k.keyCode],0]));
            }
        });
    }

    var fun;
    switch(evt) {
    case 'click':
    case 'dblclick':
    case 'mouseup':
    case 'mousedown':
        fun = function(x) {
            var mpos = jsGetMouseCoords(x);
            var mx = [0,mpos[0]];
            var my = [0,mpos[1]];
            B(A(cb,[[0,x.button],[0,mx,my],0]));
        };
        break;
    case 'mousemove':
    case 'mouseover':
        fun = function(x) {
            var mpos = jsGetMouseCoords(x);
            var mx = [0,mpos[0]];
            var my = [0,mpos[1]];
            B(A(cb,[[0,mx,my],0]));
        };
        break;
    case 'keypress':
    case 'keyup':
    case 'keydown':
        fun = function(x) {B(A(cb,[[0,x.keyCode],0]));};
        break;
    case 'wheel':
        fun = function(x) {
            var mpos = jsGetMouseCoords(x);
            var mx = [0,mpos[0]];
            var my = [0,mpos[1]];
            var mdx = [0,x.deltaX];
            var mdy = [0,x.deltaY];
            var mdz = [0,x.deltaZ];
            B(A(cb,[[0,mx,my],[0,mdx,mdy,mdz],0]));
        };
        break;
    default:
        fun = function() {B(A(cb,[0]));};
        break;
    }
    return setCB(elem, evt, fun);
}

function setCB(elem, evt, cb) {
    if(elem.addEventListener) {
        elem.addEventListener(evt, cb, false);
        return true;
    } else if(elem.attachEvent) {
        elem.attachEvent('on'+evt, cb);
        return true;
    }
    return false;
}

function jsSetTimeout(msecs, cb) {
    window.setTimeout(function() {B(A(cb,[0]));}, msecs);
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
        return [1,[0,e]];
    }
    return [0];
}

function jsElemsByClassName(cls) {
    var es = document.getElementsByClassName(cls);
    var els = [0];

    for (var i = es.length-1; i >= 0; --i) {
        els = [1, [0, es[i]], els];
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
        els = [1, [0, nl[i]], els];
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
            return [1,[0,elem]];
        }
        elem = elem.previousSibling;
    }
    return [0];
}

function jsGetLastChild(elem) {
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,[0,elem.childNodes[i]]];
        }
    }
    return [0];
}


function jsGetFirstChild(elem) {
    var len = elem.childNodes.length;
    for(var i = 0; i < len; i++) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            return [1,[0,elem.childNodes[i]]];
        }
    }
    return [0];
}


function jsGetChildren(elem) {
    var children = [0];
    var len = elem.childNodes.length;
    for(var i = len-1; i >= 0; --i) {
        if(typeof elem.childNodes[i].tagName != 'undefined') {
            children = [1, [0,elem.childNodes[i]], children];
        }
    }
    return children;
}

function jsSetChildren(elem, children) {
    children = E(children);
    jsClearChildren(elem, 0);
    while(children[0] === 1) {
        elem.appendChild(E(E(children[1])[1]));
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
        arr.push(E(strs[1])[1]);
        strs = E(strs[2]);
    }
    return arr.join(sep);
}

var jsJSONParse = JSON.parse;

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
                xs = [1, [0, [0,ks[i]], toHS(obj[ks[i]])], xs];
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

function arr2lst(arr, elem) {
    if(elem >= arr.length) {
        return [0];
    }
    return [1, arr[elem], new T(function() {return arr2lst(arr,elem+1);})]
}
window['arr2lst'] = arr2lst;

function lst2arr(xs) {
    var arr = [];
    for(; xs[0]; xs = E(xs[2])) {
        arr.push(E(xs[1]));
    }
    return arr;
}
window['lst2arr'] = lst2arr;

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
                B(A(cb,[[1,[0,xhr.responseText]],0]));
            } else {
                B(A(cb,[[0],0])); // Nothing
            }
        }
    }
    xhr.send(postdata);
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

function makeStableName(x) {
    if(!x.stableName) {
        x.stableName = __next_stable_name;
        __next_stable_name += 1;
    }
    return x.stableName;
}

function eqStableName(x, y) {
    return (x == y) ? 1 : 0;
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

// Joseph Myers' MD5 implementation; used under the BSD license.

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

function md51(s) {
    var n = s.length,
        state = [1732584193, -271733879, -1732584194, 271733878], i;
    for (i=64; i<=s.length; i+=64) {
        md5cycle(state, md5blk(s.substring(i-64, i)));
    }
    s = s.substring(i-64);
    var tail = [0,0,0,0, 0,0,0,0, 0,0,0,0, 0,0,0,0];
    for (i=0; i<s.length; i++)
        tail[i>>2] |= s.charCodeAt(i) << ((i%4) << 3);
    tail[i>>2] |= 0x80 << ((i%4) << 3);
    if (i > 55) {
        md5cycle(state, tail);
        for (i=0; i<16; i++) tail[i] = 0;
    }
    tail[14] = n*8;
    md5cycle(state, tail);
    return state;
}
window['md51'] = md51;

function md5blk(s) {
    var md5blks = [], i;
    for (i=0; i<64; i+=4) {
        md5blks[i>>2] = s.charCodeAt(i)
            + (s.charCodeAt(i+1) << 8)
            + (s.charCodeAt(i+2) << 16)
            + (s.charCodeAt(i+3) << 24);
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

function md5(s) {
    return hex(md51(s));
}

function add32(a, b) {
    return (a + b) & 0xFFFFFFFF;
}

// Functions for dealing with arrays.

function newArr(n, x) {
    var arr = [];
    for(; n >= 0; --n) {
        arr.push(x);
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

var _0=new T(function(){return B(unCStr("You have not joined a game (yet)."));}),_1=new T(function(){return B(unCStr("innerHTML"));}),_2=new T(function(){return B(unCStr("HintText"));}),_3=new T(function(){return B(unCStr("Black"));}),_4=new T(function(){return B(unCStr("White"));}),_5=[0,125],_6=new T(function(){return B(unCStr(", "));}),_7=function(_8,_9){var _a=E(_8);return _a[0]==0?E(_9):[1,_a[1],new T(function(){return B(_7(_a[2],_9));})];},_b=function(_c,_d){var _e=jsShowI(_c),_f=_e;return new F(function(){return _7(fromJSStr(_f),_d);});},_g=[0,41],_h=[0,40],_i=function(_j,_k,_l){return _k>=0?B(_b(_k,_l)):_j<=6?B(_b(_k,_l)):[1,_h,new T(function(){var _m=jsShowI(_k),_n=_m;return B(_7(fromJSStr(_n),[1,_g,_l]));})];},_o=new T(function(){return B(unCStr("onPointIndex = "));}),_p=new T(function(){return B(unCStr("BarPlacement {"));}),_q=new T(function(){return B(unCStr("onBarIndex = "));}),_r=new T(function(){return B(unCStr("LeftSidePlacement {"));}),_s=new T(function(){return B(unCStr("onSideIndex = "));}),_t=new T(function(){return B(unCStr("RightSidePlacement {"));}),_u=new T(function(){return B(unCStr("PointPlacement {"));}),_v=new T(function(){return B(unCStr("pointIndex = "));}),_w=function(_x,_y,_z){var _A=E(_y);switch(_A[0]){case 0:var _B=function(_C){return new F(function(){return _7(_v,new T(function(){return B(_i(0,E(_A[1])[1],new T(function(){return B(_7(_6,new T(function(){return B(_7(_o,new T(function(){return B(_i(0,E(_A[2])[1],[1,_5,_C]));})));})));})));}));});};return _x<11?B(_7(_u,new T(function(){return B(_B(_z));}))):[1,_h,new T(function(){return B(_7(_u,new T(function(){return B(_B([1,_g,_z]));})));})];case 1:var _D=function(_E){return new F(function(){return _7(_p,new T(function(){return B(_7(_q,new T(function(){return B(_i(0,E(_A[1])[1],[1,_5,_E]));})));}));});};return _x<11?B(_D(_z)):[1,_h,new T(function(){return B(_D([1,_g,_z]));})];case 2:var _F=function(_G){return new F(function(){return _7(_r,new T(function(){return B(_7(_s,new T(function(){return B(_i(0,E(_A[1])[1],[1,_5,_G]));})));}));});};return _x<11?B(_F(_z)):[1,_h,new T(function(){return B(_F([1,_g,_z]));})];default:var _H=function(_I){return new F(function(){return _7(_t,new T(function(){return B(_7(_s,new T(function(){return B(_i(0,E(_A[1])[1],[1,_5,_I]));})));}));});};return _x<11?B(_H(_z)):[1,_h,new T(function(){return B(_H([1,_g,_z]));})];}},_J=0,_K=function(_L,_M,_N,_O){return new F(function(){return A(_L,[new T(function(){return function(_){var _P=jsSetAttr(E(_M)[1],toJSStr(E(_N)),toJSStr(E(_O)));return _J;};})]);});},_Q=[0],_R=function(_S){return E(_S);},_T=[0,95],_U=function(_V){var _W=E(_V);return E(_W[1])==32?E(_T):E(_W);},_X=new T(function(){return B(unCStr("class"));}),_Y=new T(function(){return B(unCStr("draggable "));}),_Z=[0,32],_10=function(_11,_12){var _13=E(_12);return _13[0]==0?[0]:[1,new T(function(){return B(A(_11,[_13[1]]));}),new T(function(){return B(_10(_11,_13[2]));})];},_14=function(_15,_16,_17,_18){return new F(function(){return _K(_R,_15,_X,new T(function(){var _19=new T(function(){var _1a=new T(function(){return B(_10(_U,B(_w(0,_17,_Q))));});return E(_18)==0?B(_7(_3,[1,_Z,_1a])):B(_7(_4,[1,_Z,_1a]));});return E(_16)==0?E(_18)==0?B(_7(_Y,_19)):E(_19):E(_18)==0?E(_19):B(_7(_Y,_19));}));});},_1b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_1c=new T(function(){return B(unCStr("base"));}),_1d=new T(function(){return B(unCStr("PatternMatchFail"));}),_1e=new T(function(){var _1f=hs_wordToWord64(18445595),_1g=_1f,_1h=hs_wordToWord64(52003073),_1i=_1h;return [0,_1g,_1i,[0,_1g,_1i,_1c,_1b,_1d],_Q];}),_1j=function(_1k){return E(_1e);},_1l=function(_1m){return E(E(_1m)[1]);},_1n=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1o=new T(function(){return B(err(_1n));}),_1p=function(_1q,_1r,_1s){var _1t=new T(function(){var _1u=B(A(_1q,[_1s])),_1v=B(A(_1r,[new T(function(){var _1w=E(_1t);return _1w[0]==0?E(_1o):E(_1w[1]);})])),_1x=hs_eqWord64(_1u[1],_1v[1]),_1y=_1x;if(!E(_1y)){var _1z=[0];}else{var _1A=hs_eqWord64(_1u[2],_1v[2]),_1B=_1A,_1z=E(_1B)==0?[0]:[1,_1s];}var _1C=_1z,_1D=_1C;return _1D;});return E(_1t);},_1E=function(_1F){var _1G=E(_1F);return new F(function(){return _1p(B(_1l(_1G[1])),_1j,_1G[2]);});},_1H=function(_1I){return E(E(_1I)[1]);},_1J=function(_1K,_1L){return new F(function(){return _7(E(_1K)[1],_1L);});},_1M=[0,44],_1N=[0,93],_1O=[0,91],_1P=function(_1Q,_1R,_1S){var _1T=E(_1R);return _1T[0]==0?B(unAppCStr("[]",_1S)):[1,_1O,new T(function(){return B(A(_1Q,[_1T[1],new T(function(){var _1U=function(_1V){var _1W=E(_1V);return _1W[0]==0?E([1,_1N,_1S]):[1,_1M,new T(function(){return B(A(_1Q,[_1W[1],new T(function(){return B(_1U(_1W[2]));})]));})];};return B(_1U(_1T[2]));})]));})];},_1X=function(_1Y,_1Z){return new F(function(){return _1P(_1J,_1Y,_1Z);});},_20=function(_21,_22,_23){return new F(function(){return _7(E(_22)[1],_23);});},_24=[0,_20,_1H,_1X],_25=new T(function(){return [0,_1j,_24,_26,_1E];}),_26=function(_27){return [0,_25,_27];},_28=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_29=function(_2a,_2b){return new F(function(){return die(new T(function(){return B(A(_2b,[_2a]));}));});},_2c=function(_2d,_2e){var _2f=E(_2e);if(!_2f[0]){return [0,_Q,_Q];}else{var _2g=_2f[1];if(!B(A(_2d,[_2g]))){return [0,_Q,_2f];}else{var _2h=new T(function(){var _2i=B(_2c(_2d,_2f[2]));return [0,_2i[1],_2i[2]];});return [0,[1,_2g,new T(function(){return E(E(_2h)[1]);})],new T(function(){return E(E(_2h)[2]);})];}}},_2j=[0,32],_2k=[0,10],_2l=[1,_2k,_Q],_2m=function(_2n){return E(E(_2n)[1])==124?false:true;},_2o=function(_2p,_2q){var _2r=B(_2c(_2m,B(unCStr(_2p)))),_2s=_2r[1],_2t=function(_2u,_2v){return new F(function(){return _7(_2u,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_7(_2q,new T(function(){return B(_7(_2v,_2l));})));})));}));});},_2w=E(_2r[2]);if(!_2w[0]){return new F(function(){return _2t(_2s,_Q);});}else{return E(E(_2w[1])[1])==124?B(_2t(_2s,[1,_2j,_2w[2]])):B(_2t(_2s,_Q));}},_2x=function(_2y){return new F(function(){return _29([0,new T(function(){return B(_2o(_2y,_28));})],_26);});},_2z=new T(function(){return B(_2x("main.hs:(87,1)-(114,116)|function checkerPosition"));}),_2A=function(_2B,_2C){if(_2B<=0){if(_2B>=0){return new F(function(){return quot(_2B,_2C);});}else{if(_2C<=0){return new F(function(){return quot(_2B,_2C);});}else{return quot(_2B+1|0,_2C)-1|0;}}}else{if(_2C>=0){if(_2B>=0){return new F(function(){return quot(_2B,_2C);});}else{if(_2C<=0){return new F(function(){return quot(_2B,_2C);});}else{return quot(_2B+1|0,_2C)-1|0;}}}else{return quot(_2B-1|0,_2C)-1|0;}}},_2D=new T(function(){return [0,B(_2A(15,2))];}),_2E=new T(function(){return [0,220+B(_2A(15,2))|0];}),_2F=function(_2G){var _2H=E(_2G);switch(_2H[0]){case 0:var _2I=_2H[1],_2J=_2H[2];return [0,new T(function(){var _2K=E(_2I)[1];if(_2K>=12){var _2L=23-_2K|0;if(_2L>=6){var _2M=[0,25+(20+(imul(_2L,15)|0)|0)|0];}else{var _2M=[0,25+(imul(_2L,15)|0)|0];}var _2N=_2M,_2O=_2N;}else{if(_2K>=6){var _2P=[0,25+(20+(imul(_2K,15)|0)|0)|0];}else{var _2P=[0,25+(imul(_2K,15)|0)|0];}var _2O=_2P;}var _2Q=_2O;return _2Q;}),new T(function(){if(E(_2I)[1]>=12){var _2R=[0,203+(imul(imul(imul(-1,E(_2J)[1])|0,2)|0,6)|0)|0];}else{var _2R=[0,7+(imul(imul(E(_2J)[1],2)|0,6)|0)|0];}var _2S=_2R;return _2S;})];case 1:return E(_2z);case 2:return [0,_2D,new T(function(){return [0,203-(imul(imul(E(_2H[1])[1],2)|0,6)|0)|0];})];default:return [0,_2E,new T(function(){return [0,203-(imul(imul(E(_2H[1])[1],2)|0,6)|0)|0];})];}},_2T=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:151:5-10"));}),_2U=function(_){return _J;},_2V=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_2W=new T(function(){return B(unCStr("base"));}),_2X=new T(function(){return B(unCStr("IOException"));}),_2Y=new T(function(){var _2Z=hs_wordToWord64(4053623282),_30=_2Z,_31=hs_wordToWord64(3693590983),_32=_31;return [0,_30,_32,[0,_30,_32,_2W,_2V,_2X],_Q];}),_33=function(_34){return E(_2Y);},_35=function(_36){var _37=E(_36);return new F(function(){return _1p(B(_1l(_37[1])),_33,_37[2]);});},_38=new T(function(){return B(unCStr(": "));}),_39=[0,41],_3a=new T(function(){return B(unCStr(" ("));}),_3b=new T(function(){return B(unCStr("already exists"));}),_3c=new T(function(){return B(unCStr("does not exist"));}),_3d=new T(function(){return B(unCStr("protocol error"));}),_3e=new T(function(){return B(unCStr("failed"));}),_3f=new T(function(){return B(unCStr("invalid argument"));}),_3g=new T(function(){return B(unCStr("inappropriate type"));}),_3h=new T(function(){return B(unCStr("hardware fault"));}),_3i=new T(function(){return B(unCStr("unsupported operation"));}),_3j=new T(function(){return B(unCStr("timeout"));}),_3k=new T(function(){return B(unCStr("resource vanished"));}),_3l=new T(function(){return B(unCStr("interrupted"));}),_3m=new T(function(){return B(unCStr("resource busy"));}),_3n=new T(function(){return B(unCStr("resource exhausted"));}),_3o=new T(function(){return B(unCStr("end of file"));}),_3p=new T(function(){return B(unCStr("illegal operation"));}),_3q=new T(function(){return B(unCStr("permission denied"));}),_3r=new T(function(){return B(unCStr("user error"));}),_3s=new T(function(){return B(unCStr("unsatisified constraints"));}),_3t=new T(function(){return B(unCStr("system error"));}),_3u=function(_3v,_3w){switch(E(_3v)){case 0:return new F(function(){return _7(_3b,_3w);});break;case 1:return new F(function(){return _7(_3c,_3w);});break;case 2:return new F(function(){return _7(_3m,_3w);});break;case 3:return new F(function(){return _7(_3n,_3w);});break;case 4:return new F(function(){return _7(_3o,_3w);});break;case 5:return new F(function(){return _7(_3p,_3w);});break;case 6:return new F(function(){return _7(_3q,_3w);});break;case 7:return new F(function(){return _7(_3r,_3w);});break;case 8:return new F(function(){return _7(_3s,_3w);});break;case 9:return new F(function(){return _7(_3t,_3w);});break;case 10:return new F(function(){return _7(_3d,_3w);});break;case 11:return new F(function(){return _7(_3e,_3w);});break;case 12:return new F(function(){return _7(_3f,_3w);});break;case 13:return new F(function(){return _7(_3g,_3w);});break;case 14:return new F(function(){return _7(_3h,_3w);});break;case 15:return new F(function(){return _7(_3i,_3w);});break;case 16:return new F(function(){return _7(_3j,_3w);});break;case 17:return new F(function(){return _7(_3k,_3w);});break;default:return new F(function(){return _7(_3l,_3w);});}},_3x=[0,125],_3y=new T(function(){return B(unCStr("{handle: "));}),_3z=function(_3A,_3B,_3C,_3D,_3E,_3F){var _3G=new T(function(){var _3H=new T(function(){return B(_3u(_3B,new T(function(){var _3I=E(_3D);return _3I[0]==0?E(_3F):B(_7(_3a,new T(function(){return B(_7(_3I,[1,_39,_3F]));})));})));}),_3J=E(_3C);return _3J[0]==0?E(_3H):B(_7(_3J,new T(function(){return B(_7(_38,_3H));})));}),_3K=E(_3E);if(!_3K[0]){var _3L=E(_3A);if(!_3L[0]){return E(_3G);}else{var _3M=E(_3L[1]);return _3M[0]==0?B(_7(_3y,new T(function(){return B(_7(_3M[1],[1,_3x,new T(function(){return B(_7(_38,_3G));})]));}))):B(_7(_3y,new T(function(){return B(_7(_3M[1],[1,_3x,new T(function(){return B(_7(_38,_3G));})]));})));}}else{return new F(function(){return _7(_3K[1],new T(function(){return B(_7(_38,_3G));}));});}},_3N=function(_3O){var _3P=E(_3O);return new F(function(){return _3z(_3P[1],_3P[2],_3P[3],_3P[4],_3P[6],_Q);});},_3Q=function(_3R,_3S){var _3T=E(_3R);return new F(function(){return _3z(_3T[1],_3T[2],_3T[3],_3T[4],_3T[6],_3S);});},_3U=function(_3V,_3W){return new F(function(){return _1P(_3Q,_3V,_3W);});},_3X=function(_3Y,_3Z,_40){var _41=E(_3Z);return new F(function(){return _3z(_41[1],_41[2],_41[3],_41[4],_41[6],_40);});},_42=[0,_3X,_3N,_3U],_43=new T(function(){return [0,_33,_42,_44,_35];}),_44=function(_45){return [0,_43,_45];},_46=[0],_47=7,_48=function(_49){return [0,_46,_47,_Q,_49,_46,_46];},_4a=function(_4b,_){return new F(function(){return die(new T(function(){return B(_44(new T(function(){return B(_48(_4b));})));}));});},_4c=function(_4d,_){return new F(function(){return _4a(_4d,_);});},_4e=[0,114],_4f=[1,_4e,_Q],_4g=new T(function(){return B(_i(0,6,_Q));}),_4h=new T(function(){return B(unCStr("cx"));}),_4i=new T(function(){return B(unCStr("cy"));}),_4j=function(_4k,_4l){if(_4k<=_4l){var _4m=function(_4n){return [1,[0,_4n],new T(function(){if(_4n!=_4l){var _4o=B(_4m(_4n+1|0));}else{var _4o=[0];}return _4o;})];};return new F(function(){return _4m(_4k);});}else{return [0];}},_4p=new T(function(){return B(_4j(0,2147483647));}),_4q=new T(function(){return B(unCStr("circle"));}),_4r=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_4s=new T(function(){return B(unCStr("board"));}),_4t=function(_4u,_4v,_4w,_){if(_4w>0){var _4x=function(_4y,_4z,_){var _4A=jsFind(toJSStr(E(_4s))),_4B=_4A,_4C=E(_4B);if(!_4C[0]){var _4D=B(_4c(_2T,_)),_4E=_4D;return new F(function(){return A(_4z,[_]);});}else{var _4F=jsCreateElemNS(toJSStr(E(_4r)),toJSStr(E(_4q))),_4G=_4F,_4H=[0,_4G],_4I=B(A(_K,[_R,_4H,_4f,_4g,_])),_4J=_4I,_4K=new T(function(){return E(_4u)==0?[3,_4y]:[2,_4y];}),_4L=new T(function(){var _4M=B(_2F(_4K));return [0,_4M[1],_4M[2]];}),_4N=B(A(_K,[_R,_4H,_4h,new T(function(){return B(_i(0,E(E(_4L)[1])[1],_Q));}),_])),_4O=_4N,_4P=B(A(_K,[_R,_4H,_4i,new T(function(){return B(_i(0,E(E(_4L)[2])[1],_Q));}),_])),_4Q=_4P,_4R=B(A(_14,[_4H,_4v,_4K,_4u,_])),_4S=_4R,_4T=jsAppendChild(_4G,E(_4C[1])[1]);return new F(function(){return A(_4z,[_]);});}},_4U=function(_4V,_4W,_){var _4X=E(_4V);if(!_4X[0]){return _J;}else{var _4Y=_4X[1];if(_4W>1){return new F(function(){return _4x(_4Y,function(_){return new F(function(){return _4U(_4X[2],_4W-1|0,_);});},_);});}else{return new F(function(){return _4x(_4Y,_2U,_);});}}};return new F(function(){return _4U(_4p,_4w,_);});}else{return _J;}},_4Z=0,_50=1,_51=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_52=new T(function(){return B(err(_51));}),_53=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_54=new T(function(){return B(err(_53));}),_55=function(_56,_57){while(1){var _58=E(_56);if(!_58[0]){return E(_54);}else{var _59=E(_57);if(!_59){return E(_58[1]);}else{_56=_58[2];_57=_59-1|0;continue;}}}},_5a=new T(function(){return B(unCStr(": empty list"));}),_5b=new T(function(){return B(unCStr("Prelude."));}),_5c=function(_5d){return new F(function(){return err(B(_7(_5b,new T(function(){return B(_7(_5d,_5a));}))));});},_5e=new T(function(){return B(unCStr("head"));}),_5f=new T(function(){return B(_5c(_5e));}),_5g=function(_5h,_5i,_5j,_){var _5k=jsElemsByClassName(toJSStr(B(_10(_U,B(_w(0,_5h,_Q)))))),_5l=_5k,_5m=E(_5l);if(!_5m[0]){return E(_5f);}else{var _5n=E(_5m[1]),_5o=B(_2F(_5i)),_5p=animateCircle_ffi(_5n[1],E(_5o[1])[1],E(_5o[2])[1],300);return new F(function(){return A(_14,[_5n,_5j,_5i,_5j,_]);});}},_5q=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:239:9-15"));}),_5r=function(_5s,_5t){while(1){var _5u=E(_5s);if(!_5u){return E(_5t);}else{var _5v=E(_5t);if(!_5v[0]){return [0];}else{_5s=_5u-1|0;_5t=_5v[2];continue;}}}},_5w=new T(function(){return [0,"click"];}),_5x=function(_5y,_5z){var _5A=function(_5B,_5C){while(1){var _5D=(function(_5E,_5F){var _5G=E(_5F);if(!_5G[0]){return [0];}else{var _5H=_5G[2];if(!B(A(_5y,[_5G[1]]))){var _5I=_5E+1|0;_5C=_5H;_5B=_5I;return null;}else{return [1,[0,_5E],new T(function(){return B(_5A(_5E+1|0,_5H));})];}}})(_5B,_5C);if(_5D!=null){return _5D;}}};return new F(function(){return _5A(0,_5z);});},_5J=function(_5K,_5L,_5M,_5N){var _5O=E(_5M);if(!_5O[0]){return E(_5L);}else{var _5P=E(_5N);if(!_5P[0]){return E(_5L);}else{return new F(function(){return A(_5K,[_5O[1],_5P[1],new T(function(){return B(_5J(_5K,_5L,_5O[2],_5P[2]));})]);});}}},_5Q=function(_5R){return new F(function(){return fromJSStr(E(_5R)[1]);});},_5S=function(_5T){var _5U=E(_5T);return E(_5U[1])==95?E(_Z):E(_5U);},_5V=new T(function(){return [0,B(_2A(210,2))];}),_5W=new T(function(){return B(unCStr("joinGame"));}),_5X=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:233:9-19"));}),_5Y=new T(function(){return [0,"value"];}),_5Z=new T(function(){return B(unCStr("sharedKey"));}),_60=function(_){var _61=jsFind(toJSStr(E(_5Z))),_62=_61,_63=E(_62);if(!_63[0]){return new F(function(){return _4c(_5X,_);});}else{var _64=jsGet(E(_63[1])[1],E(_5Y)[1]),_65=_64,_66=showAlert_ffi(_65);return _J;}},_67=function(_68,_69,_){return new F(function(){return _60(_);});},_6a=[0,_67],_6b=new T(function(){return B(_2x("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_6c=function(_6d,_6e){while(1){var _6f=(function(_6g,_6h){var _6i=E(_6g);switch(_6i[0]){case 0:var _6j=E(_6h);if(!_6j[0]){return [0];}else{_6d=B(A(_6i[1],[_6j[1]]));_6e=_6j[2];return null;}break;case 1:var _6k=B(A(_6i[1],[_6h])),_6l=_6h;_6d=_6k;_6e=_6l;return null;case 2:return [0];case 3:return [1,[0,_6i[1],_6h],new T(function(){return B(_6c(_6i[2],_6h));})];default:return E(_6i[1]);}})(_6d,_6e);if(_6f!=null){return _6f;}}},_6m=function(_6n,_6o){var _6p=new T(function(){var _6q=E(_6o);if(_6q[0]==3){var _6r=[3,_6q[1],new T(function(){return B(_6m(_6n,_6q[2]));})];}else{var _6s=E(_6n);if(_6s[0]==2){var _6t=E(_6q);}else{var _6u=E(_6q);if(_6u[0]==2){var _6v=E(_6s);}else{var _6w=new T(function(){var _6x=E(_6u);if(_6x[0]==4){var _6y=[1,function(_6z){return [4,new T(function(){return B(_7(B(_6c(_6s,_6z)),_6x[1]));})];}];}else{var _6A=E(_6s);if(_6A[0]==1){var _6B=_6A[1],_6C=E(_6x);if(!_6C[0]){var _6D=[1,function(_6E){return new F(function(){return _6m(B(A(_6B,[_6E])),_6C);});}];}else{var _6D=[1,function(_6F){return new F(function(){return _6m(B(A(_6B,[_6F])),new T(function(){return B(A(_6C[1],[_6F]));}));});}];}var _6G=_6D;}else{var _6H=E(_6x);if(!_6H[0]){var _6I=E(_6b);}else{var _6I=[1,function(_6J){return new F(function(){return _6m(_6A,new T(function(){return B(A(_6H[1],[_6J]));}));});}];}var _6G=_6I;}var _6y=_6G;}return _6y;}),_6K=E(_6s);switch(_6K[0]){case 1:var _6L=E(_6u);if(_6L[0]==4){var _6M=[1,function(_6N){return [4,new T(function(){return B(_7(B(_6c(B(A(_6K[1],[_6N])),_6N)),_6L[1]));})];}];}else{var _6M=E(_6w);}var _6O=_6M;break;case 4:var _6P=_6K[1],_6Q=E(_6u);switch(_6Q[0]){case 0:var _6R=[1,function(_6S){return [4,new T(function(){return B(_7(_6P,new T(function(){return B(_6c(_6Q,_6S));})));})];}];break;case 1:var _6R=[1,function(_6T){return [4,new T(function(){return B(_7(_6P,new T(function(){return B(_6c(B(A(_6Q[1],[_6T])),_6T));})));})];}];break;default:var _6R=[4,new T(function(){return B(_7(_6P,_6Q[1]));})];}var _6O=_6R;break;default:var _6O=E(_6w);}var _6v=_6O;}var _6t=_6v;}var _6r=_6t;}return _6r;}),_6U=E(_6n);switch(_6U[0]){case 0:var _6V=E(_6o);return _6V[0]==0?[0,function(_6W){return new F(function(){return _6m(B(A(_6U[1],[_6W])),new T(function(){return B(A(_6V[1],[_6W]));}));});}]:E(_6p);case 3:return [3,_6U[1],new T(function(){return B(_6m(_6U[2],_6o));})];default:return E(_6p);}},_6X=function(_6Y,_6Z){return E(_6Y)[1]!=E(_6Z)[1];},_70=function(_71,_72){return E(_71)[1]==E(_72)[1];},_73=[0,_70,_6X],_74=function(_75){return E(E(_75)[1]);},_76=function(_77,_78,_79){while(1){var _7a=E(_78);if(!_7a[0]){return E(_79)[0]==0?true:false;}else{var _7b=E(_79);if(!_7b[0]){return false;}else{if(!B(A(_74,[_77,_7a[1],_7b[1]]))){return false;}else{_78=_7a[2];_79=_7b[2];continue;}}}}},_7c=function(_7d,_7e,_7f){return !B(_76(_7d,_7e,_7f))?true:false;},_7g=function(_7h){return [0,function(_7i,_7j){return new F(function(){return _76(_7h,_7i,_7j);});},function(_7i,_7j){return new F(function(){return _7c(_7h,_7i,_7j);});}];},_7k=new T(function(){return B(_7g(_73));}),_7l=function(_7m,_7n){var _7o=E(_7m);switch(_7o[0]){case 0:return [0,function(_7p){return new F(function(){return _7l(B(A(_7o[1],[_7p])),_7n);});}];case 1:return [1,function(_7q){return new F(function(){return _7l(B(A(_7o[1],[_7q])),_7n);});}];case 2:return [2];case 3:return new F(function(){return _6m(B(A(_7n,[_7o[1]])),new T(function(){return B(_7l(_7o[2],_7n));}));});break;default:var _7r=function(_7s){var _7t=E(_7s);if(!_7t[0]){return [0];}else{var _7u=E(_7t[1]);return new F(function(){return _7(B(_6c(B(A(_7n,[_7u[1]])),_7u[2])),new T(function(){return B(_7r(_7t[2]));}));});}},_7v=B(_7r(_7o[1]));return _7v[0]==0?[2]:[4,_7v];}},_7w=[2],_7x=function(_7y){return [3,_7y,_7w];},_7z=function(_7A,_7B){var _7C=E(_7A);if(!_7C){return new F(function(){return A(_7B,[_J]);});}else{return [0,function(_7D){return E(new T(function(){return B(_7z(_7C-1|0,_7B));}));}];}},_7E=function(_7F,_7G,_7H){return [1,function(_7I){return new F(function(){return A(function(_7J,_7K,_7L){while(1){var _7M=(function(_7N,_7O,_7P){var _7Q=E(_7N);switch(_7Q[0]){case 0:var _7R=E(_7O);if(!_7R[0]){return E(_7G);}else{_7J=B(A(_7Q[1],[_7R[1]]));_7K=_7R[2];var _7S=_7P+1|0;_7L=_7S;return null;}break;case 1:var _7T=B(A(_7Q[1],[_7O])),_7U=_7O,_7S=_7P;_7J=_7T;_7K=_7U;_7L=_7S;return null;case 2:return E(_7G);case 3:return function(_7V){return new F(function(){return _7z(_7P,function(_7W){return E(new T(function(){return B(_7l(_7Q,_7V));}));});});};default:return function(_7X){return new F(function(){return _7l(_7Q,_7X);});};}})(_7J,_7K,_7L);if(_7M!=null){return _7M;}}},[new T(function(){return B(A(_7F,[_7x]));}),_7I,0,_7H]);});}];},_7Y=[6],_7Z=new T(function(){return B(unCStr("valDig: Bad base"));}),_80=new T(function(){return B(err(_7Z));}),_81=function(_82,_83){var _84=function(_85,_86){var _87=E(_85);if(!_87[0]){return function(_88){return new F(function(){return A(_88,[new T(function(){return B(A(_86,[_Q]));})]);});};}else{var _89=E(_87[1])[1],_8a=function(_8b){return function(_8c){return [0,function(_8d){return E(new T(function(){return B(A(new T(function(){return B(_84(_87[2],function(_8e){return new F(function(){return A(_86,[[1,_8b,_8e]]);});}));}),[_8c]));}));}];};};switch(E(E(_82)[1])){case 8:if(48>_89){return function(_8f){return new F(function(){return A(_8f,[new T(function(){return B(A(_86,[_Q]));})]);});};}else{if(_89>55){return function(_8g){return new F(function(){return A(_8g,[new T(function(){return B(A(_86,[_Q]));})]);});};}else{return new F(function(){return _8a([0,_89-48|0]);});}}break;case 10:if(48>_89){return function(_8h){return new F(function(){return A(_8h,[new T(function(){return B(A(_86,[_Q]));})]);});};}else{if(_89>57){return function(_8i){return new F(function(){return A(_8i,[new T(function(){return B(A(_86,[_Q]));})]);});};}else{return new F(function(){return _8a([0,_89-48|0]);});}}break;case 16:var _8j=new T(function(){if(97>_89){if(65>_89){var _8k=[0];}else{if(_89>70){var _8l=[0];}else{var _8l=[1,[0,(_89-65|0)+10|0]];}var _8k=_8l;}var _8m=_8k;}else{if(_89>102){if(65>_89){var _8n=[0];}else{if(_89>70){var _8o=[0];}else{var _8o=[1,[0,(_89-65|0)+10|0]];}var _8n=_8o;}var _8p=_8n;}else{var _8p=[1,[0,(_89-97|0)+10|0]];}var _8m=_8p;}return _8m;});if(48>_89){var _8q=E(_8j);if(!_8q[0]){return function(_8r){return new F(function(){return A(_8r,[new T(function(){return B(A(_86,[_Q]));})]);});};}else{return new F(function(){return _8a(_8q[1]);});}}else{if(_89>57){var _8s=E(_8j);if(!_8s[0]){return function(_8t){return new F(function(){return A(_8t,[new T(function(){return B(A(_86,[_Q]));})]);});};}else{return new F(function(){return _8a(_8s[1]);});}}else{return new F(function(){return _8a([0,_89-48|0]);});}}break;default:return E(_80);}}};return [1,function(_8u){return new F(function(){return A(_84,[_8u,_R,function(_8v){var _8w=E(_8v);return _8w[0]==0?[2]:B(A(_83,[_8w]));}]);});}];},_8x=[0,10],_8y=[0,1],_8z=[0,2147483647],_8A=function(_8B,_8C){while(1){var _8D=E(_8B);if(!_8D[0]){var _8E=_8D[1],_8F=E(_8C);if(!_8F[0]){var _8G=_8F[1],_8H=addC(_8E,_8G);if(!E(_8H[2])){return [0,_8H[1]];}else{_8B=[1,I_fromInt(_8E)];_8C=[1,I_fromInt(_8G)];continue;}}else{_8B=[1,I_fromInt(_8E)];_8C=_8F;continue;}}else{var _8I=E(_8C);if(!_8I[0]){_8B=_8D;_8C=[1,I_fromInt(_8I[1])];continue;}else{return [1,I_add(_8D[1],_8I[1])];}}}},_8J=new T(function(){return B(_8A(_8z,_8y));}),_8K=function(_8L){var _8M=E(_8L);if(!_8M[0]){var _8N=E(_8M[1]);return _8N==(-2147483648)?E(_8J):[0, -_8N];}else{return [1,I_negate(_8M[1])];}},_8O=[0,10],_8P=[0,0],_8Q=function(_8R){return [0,_8R];},_8S=function(_8T,_8U){while(1){var _8V=E(_8T);if(!_8V[0]){var _8W=_8V[1],_8X=E(_8U);if(!_8X[0]){var _8Y=_8X[1];if(!(imul(_8W,_8Y)|0)){return [0,imul(_8W,_8Y)|0];}else{_8T=[1,I_fromInt(_8W)];_8U=[1,I_fromInt(_8Y)];continue;}}else{_8T=[1,I_fromInt(_8W)];_8U=_8X;continue;}}else{var _8Z=E(_8U);if(!_8Z[0]){_8T=_8V;_8U=[1,I_fromInt(_8Z[1])];continue;}else{return [1,I_mul(_8V[1],_8Z[1])];}}}},_90=function(_91,_92,_93){while(1){var _94=E(_93);if(!_94[0]){return E(_92);}else{var _95=B(_8A(B(_8S(_92,_91)),B(_8Q(E(_94[1])[1]))));_93=_94[2];_92=_95;continue;}}},_96=function(_97){var _98=new T(function(){return B(_6m(B(_6m([0,function(_99){if(E(E(_99)[1])==45){return new F(function(){return _81(_8x,function(_9a){return new F(function(){return A(_97,[[1,new T(function(){return B(_8K(B(_90(_8O,_8P,_9a))));})]]);});});});}else{return [2];}}],[0,function(_9b){if(E(E(_9b)[1])==43){return new F(function(){return _81(_8x,function(_9c){return new F(function(){return A(_97,[[1,new T(function(){return B(_90(_8O,_8P,_9c));})]]);});});});}else{return [2];}}])),new T(function(){return B(_81(_8x,function(_9d){return new F(function(){return A(_97,[[1,new T(function(){return B(_90(_8O,_8P,_9d));})]]);});}));})));});return new F(function(){return _6m([0,function(_9e){return E(E(_9e)[1])==101?E(_98):[2];}],[0,function(_9f){return E(E(_9f)[1])==69?E(_98):[2];}]);});},_9g=function(_9h){return new F(function(){return A(_9h,[_46]);});},_9i=function(_9j){return new F(function(){return A(_9j,[_46]);});},_9k=function(_9l){return [0,function(_9m){return E(E(_9m)[1])==46?E(new T(function(){return B(_81(_8x,function(_9n){return new F(function(){return A(_9l,[[1,_9n]]);});}));})):[2];}];},_9o=function(_9p){return new F(function(){return _81(_8x,function(_9q){return new F(function(){return _7E(_9k,_9g,function(_9r){return new F(function(){return _7E(_96,_9i,function(_9s){return new F(function(){return A(_9p,[[5,[1,_9q,_9r,_9s]]]);});});});});});});});},_9t=function(_9u,_9v,_9w){while(1){var _9x=E(_9w);if(!_9x[0]){return false;}else{if(!B(A(_74,[_9u,_9v,_9x[1]]))){_9w=_9x[2];continue;}else{return true;}}}},_9y=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_9z=function(_9A){return new F(function(){return _9t(_73,_9A,_9y);});},_9B=[0,8],_9C=[0,16],_9D=function(_9E){return [0,function(_9F){return E(E(_9F)[1])==48?E([0,function(_9G){switch(E(E(_9G)[1])){case 79:return E(new T(function(){return B(_81(_9B,function(_9H){return new F(function(){return A(_9E,[[5,[0,_9B,_9H]]]);});}));}));case 88:return E(new T(function(){return B(_81(_9C,function(_9I){return new F(function(){return A(_9E,[[5,[0,_9C,_9I]]]);});}));}));case 111:return E(new T(function(){return B(_81(_9B,function(_9J){return new F(function(){return A(_9E,[[5,[0,_9B,_9J]]]);});}));}));case 120:return E(new T(function(){return B(_81(_9C,function(_9K){return new F(function(){return A(_9E,[[5,[0,_9C,_9K]]]);});}));}));default:return [2];}}]):[2];}];},_9L=false,_9M=true,_9N=function(_9O){return [0,function(_9P){switch(E(E(_9P)[1])){case 79:return E(new T(function(){return B(A(_9O,[_9B]));}));case 88:return E(new T(function(){return B(A(_9O,[_9C]));}));case 111:return E(new T(function(){return B(A(_9O,[_9B]));}));case 120:return E(new T(function(){return B(A(_9O,[_9C]));}));default:return [2];}}];},_9Q=function(_9R){return new F(function(){return A(_9R,[_8x]);});},_9S=function(_9T){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_i(9,_9T,_Q));}))));});},_9U=function(_9V){var _9W=E(_9V);return _9W[0]==0?E(_9W[1]):I_toInt(_9W[1]);},_9X=function(_9Y,_9Z){var _a0=E(_9Y);if(!_a0[0]){var _a1=_a0[1],_a2=E(_9Z);return _a2[0]==0?_a1<=_a2[1]:I_compareInt(_a2[1],_a1)>=0;}else{var _a3=_a0[1],_a4=E(_9Z);return _a4[0]==0?I_compareInt(_a3,_a4[1])<=0:I_compare(_a3,_a4[1])<=0;}},_a5=function(_a6){return [2];},_a7=function(_a8){var _a9=E(_a8);if(!_a9[0]){return E(_a5);}else{var _aa=_a9[1],_ab=E(_a9[2]);return _ab[0]==0?E(_aa):function(_ac){return new F(function(){return _6m(B(A(_aa,[_ac])),new T(function(){return B(A(new T(function(){return B(_a7(_ab));}),[_ac]));}));});};}},_ad=new T(function(){return B(unCStr("NUL"));}),_ae=function(_af){return [2];},_ag=function(_ah){return new F(function(){return _ae(_ah);});},_ai=function(_aj,_ak){var _al=function(_am,_an){var _ao=E(_am);if(!_ao[0]){return function(_ap){return new F(function(){return A(_ap,[_aj]);});};}else{var _aq=E(_an);return _aq[0]==0?E(_ae):E(_ao[1])[1]!=E(_aq[1])[1]?E(_ag):function(_ar){return [0,function(_as){return E(new T(function(){return B(A(new T(function(){return B(_al(_ao[2],_aq[2]));}),[_ar]));}));}];};}};return [1,function(_at){return new F(function(){return A(_al,[_aj,_at,_ak]);});}];},_au=[0,0],_av=function(_aw){return new F(function(){return _ai(_ad,function(_ax){return E(new T(function(){return B(A(_aw,[_au]));}));});});},_ay=new T(function(){return B(unCStr("STX"));}),_az=[0,2],_aA=function(_aB){return new F(function(){return _ai(_ay,function(_aC){return E(new T(function(){return B(A(_aB,[_az]));}));});});},_aD=new T(function(){return B(unCStr("ETX"));}),_aE=[0,3],_aF=function(_aG){return new F(function(){return _ai(_aD,function(_aH){return E(new T(function(){return B(A(_aG,[_aE]));}));});});},_aI=new T(function(){return B(unCStr("EOT"));}),_aJ=[0,4],_aK=function(_aL){return new F(function(){return _ai(_aI,function(_aM){return E(new T(function(){return B(A(_aL,[_aJ]));}));});});},_aN=new T(function(){return B(unCStr("ENQ"));}),_aO=[0,5],_aP=function(_aQ){return new F(function(){return _ai(_aN,function(_aR){return E(new T(function(){return B(A(_aQ,[_aO]));}));});});},_aS=new T(function(){return B(unCStr("ACK"));}),_aT=[0,6],_aU=function(_aV){return new F(function(){return _ai(_aS,function(_aW){return E(new T(function(){return B(A(_aV,[_aT]));}));});});},_aX=new T(function(){return B(unCStr("BEL"));}),_aY=[0,7],_aZ=function(_b0){return new F(function(){return _ai(_aX,function(_b1){return E(new T(function(){return B(A(_b0,[_aY]));}));});});},_b2=new T(function(){return B(unCStr("BS"));}),_b3=[0,8],_b4=function(_b5){return new F(function(){return _ai(_b2,function(_b6){return E(new T(function(){return B(A(_b5,[_b3]));}));});});},_b7=new T(function(){return B(unCStr("HT"));}),_b8=[0,9],_b9=function(_ba){return new F(function(){return _ai(_b7,function(_bb){return E(new T(function(){return B(A(_ba,[_b8]));}));});});},_bc=new T(function(){return B(unCStr("LF"));}),_bd=[0,10],_be=function(_bf){return new F(function(){return _ai(_bc,function(_bg){return E(new T(function(){return B(A(_bf,[_bd]));}));});});},_bh=new T(function(){return B(unCStr("VT"));}),_bi=[0,11],_bj=function(_bk){return new F(function(){return _ai(_bh,function(_bl){return E(new T(function(){return B(A(_bk,[_bi]));}));});});},_bm=new T(function(){return B(unCStr("FF"));}),_bn=[0,12],_bo=function(_bp){return new F(function(){return _ai(_bm,function(_bq){return E(new T(function(){return B(A(_bp,[_bn]));}));});});},_br=new T(function(){return B(unCStr("CR"));}),_bs=[0,13],_bt=function(_bu){return new F(function(){return _ai(_br,function(_bv){return E(new T(function(){return B(A(_bu,[_bs]));}));});});},_bw=new T(function(){return B(unCStr("SI"));}),_bx=[0,15],_by=function(_bz){return new F(function(){return _ai(_bw,function(_bA){return E(new T(function(){return B(A(_bz,[_bx]));}));});});},_bB=new T(function(){return B(unCStr("DLE"));}),_bC=[0,16],_bD=function(_bE){return new F(function(){return _ai(_bB,function(_bF){return E(new T(function(){return B(A(_bE,[_bC]));}));});});},_bG=new T(function(){return B(unCStr("DC1"));}),_bH=[0,17],_bI=function(_bJ){return new F(function(){return _ai(_bG,function(_bK){return E(new T(function(){return B(A(_bJ,[_bH]));}));});});},_bL=new T(function(){return B(unCStr("DC2"));}),_bM=[0,18],_bN=function(_bO){return new F(function(){return _ai(_bL,function(_bP){return E(new T(function(){return B(A(_bO,[_bM]));}));});});},_bQ=new T(function(){return B(unCStr("DC3"));}),_bR=[0,19],_bS=function(_bT){return new F(function(){return _ai(_bQ,function(_bU){return E(new T(function(){return B(A(_bT,[_bR]));}));});});},_bV=new T(function(){return B(unCStr("DC4"));}),_bW=[0,20],_bX=function(_bY){return new F(function(){return _ai(_bV,function(_bZ){return E(new T(function(){return B(A(_bY,[_bW]));}));});});},_c0=new T(function(){return B(unCStr("NAK"));}),_c1=[0,21],_c2=function(_c3){return new F(function(){return _ai(_c0,function(_c4){return E(new T(function(){return B(A(_c3,[_c1]));}));});});},_c5=new T(function(){return B(unCStr("SYN"));}),_c6=[0,22],_c7=function(_c8){return new F(function(){return _ai(_c5,function(_c9){return E(new T(function(){return B(A(_c8,[_c6]));}));});});},_ca=new T(function(){return B(unCStr("ETB"));}),_cb=[0,23],_cc=function(_cd){return new F(function(){return _ai(_ca,function(_ce){return E(new T(function(){return B(A(_cd,[_cb]));}));});});},_cf=new T(function(){return B(unCStr("CAN"));}),_cg=[0,24],_ch=function(_ci){return new F(function(){return _ai(_cf,function(_cj){return E(new T(function(){return B(A(_ci,[_cg]));}));});});},_ck=new T(function(){return B(unCStr("EM"));}),_cl=[0,25],_cm=function(_cn){return new F(function(){return _ai(_ck,function(_co){return E(new T(function(){return B(A(_cn,[_cl]));}));});});},_cp=new T(function(){return B(unCStr("SUB"));}),_cq=[0,26],_cr=function(_cs){return new F(function(){return _ai(_cp,function(_ct){return E(new T(function(){return B(A(_cs,[_cq]));}));});});},_cu=new T(function(){return B(unCStr("ESC"));}),_cv=[0,27],_cw=function(_cx){return new F(function(){return _ai(_cu,function(_cy){return E(new T(function(){return B(A(_cx,[_cv]));}));});});},_cz=new T(function(){return B(unCStr("FS"));}),_cA=[0,28],_cB=function(_cC){return new F(function(){return _ai(_cz,function(_cD){return E(new T(function(){return B(A(_cC,[_cA]));}));});});},_cE=new T(function(){return B(unCStr("GS"));}),_cF=[0,29],_cG=function(_cH){return new F(function(){return _ai(_cE,function(_cI){return E(new T(function(){return B(A(_cH,[_cF]));}));});});},_cJ=new T(function(){return B(unCStr("RS"));}),_cK=[0,30],_cL=function(_cM){return new F(function(){return _ai(_cJ,function(_cN){return E(new T(function(){return B(A(_cM,[_cK]));}));});});},_cO=new T(function(){return B(unCStr("US"));}),_cP=[0,31],_cQ=function(_cR){return new F(function(){return _ai(_cO,function(_cS){return E(new T(function(){return B(A(_cR,[_cP]));}));});});},_cT=new T(function(){return B(unCStr("SP"));}),_cU=[0,32],_cV=function(_cW){return new F(function(){return _ai(_cT,function(_cX){return E(new T(function(){return B(A(_cW,[_cU]));}));});});},_cY=new T(function(){return B(unCStr("DEL"));}),_cZ=[0,127],_d0=function(_d1){return new F(function(){return _ai(_cY,function(_d2){return E(new T(function(){return B(A(_d1,[_cZ]));}));});});},_d3=[1,_d0,_Q],_d4=[1,_cV,_d3],_d5=[1,_cQ,_d4],_d6=[1,_cL,_d5],_d7=[1,_cG,_d6],_d8=[1,_cB,_d7],_d9=[1,_cw,_d8],_da=[1,_cr,_d9],_db=[1,_cm,_da],_dc=[1,_ch,_db],_dd=[1,_cc,_dc],_de=[1,_c7,_dd],_df=[1,_c2,_de],_dg=[1,_bX,_df],_dh=[1,_bS,_dg],_di=[1,_bN,_dh],_dj=[1,_bI,_di],_dk=[1,_bD,_dj],_dl=[1,_by,_dk],_dm=[1,_bt,_dl],_dn=[1,_bo,_dm],_do=[1,_bj,_dn],_dp=[1,_be,_do],_dq=[1,_b9,_dp],_dr=[1,_b4,_dq],_ds=[1,_aZ,_dr],_dt=[1,_aU,_ds],_du=[1,_aP,_dt],_dv=[1,_aK,_du],_dw=[1,_aF,_dv],_dx=[1,_aA,_dw],_dy=[1,_av,_dx],_dz=new T(function(){return B(unCStr("SOH"));}),_dA=[0,1],_dB=function(_dC){return new F(function(){return _ai(_dz,function(_dD){return E(new T(function(){return B(A(_dC,[_dA]));}));});});},_dE=new T(function(){return B(unCStr("SO"));}),_dF=[0,14],_dG=function(_dH){return new F(function(){return _ai(_dE,function(_dI){return E(new T(function(){return B(A(_dH,[_dF]));}));});});},_dJ=function(_dK){return new F(function(){return _7E(_dB,_dG,_dK);});},_dL=[1,_dJ,_dy],_dM=new T(function(){return B(_a7(_dL));}),_dN=[0,1114111],_dO=[0,34],_dP=[0,_dO,_9M],_dQ=[0,39],_dR=[0,_dQ,_9M],_dS=[0,92],_dT=[0,_dS,_9M],_dU=[0,_aY,_9M],_dV=[0,_b3,_9M],_dW=[0,_bn,_9M],_dX=[0,_bd,_9M],_dY=[0,_bs,_9M],_dZ=[0,_b8,_9M],_e0=[0,_bi,_9M],_e1=[0,_au,_9M],_e2=[0,_dA,_9M],_e3=[0,_az,_9M],_e4=[0,_aE,_9M],_e5=[0,_aJ,_9M],_e6=[0,_aO,_9M],_e7=[0,_aT,_9M],_e8=[0,_aY,_9M],_e9=[0,_b3,_9M],_ea=[0,_b8,_9M],_eb=[0,_bd,_9M],_ec=[0,_bi,_9M],_ed=[0,_bn,_9M],_ee=[0,_bs,_9M],_ef=[0,_dF,_9M],_eg=[0,_bx,_9M],_eh=[0,_bC,_9M],_ei=[0,_bH,_9M],_ej=[0,_bM,_9M],_ek=[0,_bR,_9M],_el=[0,_bW,_9M],_em=[0,_c1,_9M],_en=[0,_c6,_9M],_eo=[0,_cb,_9M],_ep=[0,_cg,_9M],_eq=[0,_cl,_9M],_er=[0,_cq,_9M],_es=[0,_cv,_9M],_et=[0,_cA,_9M],_eu=[0,_cF,_9M],_ev=[0,_cK,_9M],_ew=[0,_cP,_9M],_ex=function(_ey){return new F(function(){return _6m([0,function(_ez){switch(E(E(_ez)[1])){case 34:return E(new T(function(){return B(A(_ey,[_dP]));}));case 39:return E(new T(function(){return B(A(_ey,[_dR]));}));case 92:return E(new T(function(){return B(A(_ey,[_dT]));}));case 97:return E(new T(function(){return B(A(_ey,[_dU]));}));case 98:return E(new T(function(){return B(A(_ey,[_dV]));}));case 102:return E(new T(function(){return B(A(_ey,[_dW]));}));case 110:return E(new T(function(){return B(A(_ey,[_dX]));}));case 114:return E(new T(function(){return B(A(_ey,[_dY]));}));case 116:return E(new T(function(){return B(A(_ey,[_dZ]));}));case 118:return E(new T(function(){return B(A(_ey,[_e0]));}));default:return [2];}}],new T(function(){return B(_6m(B(_7E(_9N,_9Q,function(_eA){return new F(function(){return _81(_eA,function(_eB){var _eC=B(_90(new T(function(){return B(_8Q(E(_eA)[1]));}),_8P,_eB));return !B(_9X(_eC,_dN))?[2]:B(A(_ey,[[0,new T(function(){var _eD=B(_9U(_eC));if(_eD>>>0>1114111){var _eE=B(_9S(_eD));}else{var _eE=[0,_eD];}var _eF=_eE,_eG=_eF;return _eG;}),_9M]]));});});})),new T(function(){return B(_6m([0,function(_eH){return E(E(_eH)[1])==94?E([0,function(_eI){switch(E(E(_eI)[1])){case 64:return E(new T(function(){return B(A(_ey,[_e1]));}));case 65:return E(new T(function(){return B(A(_ey,[_e2]));}));case 66:return E(new T(function(){return B(A(_ey,[_e3]));}));case 67:return E(new T(function(){return B(A(_ey,[_e4]));}));case 68:return E(new T(function(){return B(A(_ey,[_e5]));}));case 69:return E(new T(function(){return B(A(_ey,[_e6]));}));case 70:return E(new T(function(){return B(A(_ey,[_e7]));}));case 71:return E(new T(function(){return B(A(_ey,[_e8]));}));case 72:return E(new T(function(){return B(A(_ey,[_e9]));}));case 73:return E(new T(function(){return B(A(_ey,[_ea]));}));case 74:return E(new T(function(){return B(A(_ey,[_eb]));}));case 75:return E(new T(function(){return B(A(_ey,[_ec]));}));case 76:return E(new T(function(){return B(A(_ey,[_ed]));}));case 77:return E(new T(function(){return B(A(_ey,[_ee]));}));case 78:return E(new T(function(){return B(A(_ey,[_ef]));}));case 79:return E(new T(function(){return B(A(_ey,[_eg]));}));case 80:return E(new T(function(){return B(A(_ey,[_eh]));}));case 81:return E(new T(function(){return B(A(_ey,[_ei]));}));case 82:return E(new T(function(){return B(A(_ey,[_ej]));}));case 83:return E(new T(function(){return B(A(_ey,[_ek]));}));case 84:return E(new T(function(){return B(A(_ey,[_el]));}));case 85:return E(new T(function(){return B(A(_ey,[_em]));}));case 86:return E(new T(function(){return B(A(_ey,[_en]));}));case 87:return E(new T(function(){return B(A(_ey,[_eo]));}));case 88:return E(new T(function(){return B(A(_ey,[_ep]));}));case 89:return E(new T(function(){return B(A(_ey,[_eq]));}));case 90:return E(new T(function(){return B(A(_ey,[_er]));}));case 91:return E(new T(function(){return B(A(_ey,[_es]));}));case 92:return E(new T(function(){return B(A(_ey,[_et]));}));case 93:return E(new T(function(){return B(A(_ey,[_eu]));}));case 94:return E(new T(function(){return B(A(_ey,[_ev]));}));case 95:return E(new T(function(){return B(A(_ey,[_ew]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_dM,[function(_eJ){return new F(function(){return A(_ey,[[0,_eJ,_9M]]);});}]));})));})));}));});},_eK=function(_eL){return new F(function(){return A(_eL,[_J]);});},_eM=function(_eN){var _eO=E(_eN);if(!_eO[0]){return E(_eK);}else{var _eP=_eO[2],_eQ=E(E(_eO[1])[1]);switch(_eQ){case 9:return function(_eR){return [0,function(_eS){return E(new T(function(){return B(A(new T(function(){return B(_eM(_eP));}),[_eR]));}));}];};case 10:return function(_eT){return [0,function(_eU){return E(new T(function(){return B(A(new T(function(){return B(_eM(_eP));}),[_eT]));}));}];};case 11:return function(_eV){return [0,function(_eW){return E(new T(function(){return B(A(new T(function(){return B(_eM(_eP));}),[_eV]));}));}];};case 12:return function(_eX){return [0,function(_eY){return E(new T(function(){return B(A(new T(function(){return B(_eM(_eP));}),[_eX]));}));}];};case 13:return function(_eZ){return [0,function(_f0){return E(new T(function(){return B(A(new T(function(){return B(_eM(_eP));}),[_eZ]));}));}];};case 32:return function(_f1){return [0,function(_f2){return E(new T(function(){return B(A(new T(function(){return B(_eM(_eP));}),[_f1]));}));}];};case 160:return function(_f3){return [0,function(_f4){return E(new T(function(){return B(A(new T(function(){return B(_eM(_eP));}),[_f3]));}));}];};default:var _f5=u_iswspace(_eQ),_f6=_f5;return E(_f6)==0?E(_eK):function(_f7){return [0,function(_f8){return E(new T(function(){return B(A(new T(function(){return B(_eM(_eP));}),[_f7]));}));}];};}}},_f9=function(_fa){var _fb=new T(function(){return B(_f9(_fa));}),_fc=[1,function(_fd){return new F(function(){return A(_eM,[_fd,function(_fe){return E([0,function(_ff){return E(E(_ff)[1])==92?E(_fb):[2];}]);}]);});}];return new F(function(){return _6m([0,function(_fg){return E(E(_fg)[1])==92?E([0,function(_fh){var _fi=E(E(_fh)[1]);switch(_fi){case 9:return E(_fc);case 10:return E(_fc);case 11:return E(_fc);case 12:return E(_fc);case 13:return E(_fc);case 32:return E(_fc);case 38:return E(_fb);case 160:return E(_fc);default:var _fj=u_iswspace(_fi),_fk=_fj;return E(_fk)==0?[2]:E(_fc);}}]):[2];}],[0,function(_fl){var _fm=E(_fl);return E(_fm[1])==92?E(new T(function(){return B(_ex(_fa));})):B(A(_fa,[[0,_fm,_9L]]));}]);});},_fn=function(_fo,_fp){return new F(function(){return _f9(function(_fq){var _fr=E(_fq),_fs=E(_fr[1]);if(E(_fs[1])==34){if(!E(_fr[2])){return E(new T(function(){return B(A(_fp,[[1,new T(function(){return B(A(_fo,[_Q]));})]]));}));}else{return new F(function(){return _fn(function(_ft){return new F(function(){return A(_fo,[[1,_fs,_ft]]);});},_fp);});}}else{return new F(function(){return _fn(function(_fu){return new F(function(){return A(_fo,[[1,_fs,_fu]]);});},_fp);});}});});},_fv=new T(function(){return B(unCStr("_\'"));}),_fw=function(_fx){var _fy=u_iswalnum(_fx),_fz=_fy;return E(_fz)==0?B(_9t(_73,[0,_fx],_fv)):true;},_fA=function(_fB){return new F(function(){return _fw(E(_fB)[1]);});},_fC=new T(function(){return B(unCStr(",;()[]{}`"));}),_fD=function(_fE){return new F(function(){return A(_fE,[_Q]);});},_fF=function(_fG,_fH){var _fI=function(_fJ){var _fK=E(_fJ);if(!_fK[0]){return E(_fD);}else{var _fL=_fK[1];return !B(A(_fG,[_fL]))?E(_fD):function(_fM){return [0,function(_fN){return E(new T(function(){return B(A(new T(function(){return B(_fI(_fK[2]));}),[function(_fO){return new F(function(){return A(_fM,[[1,_fL,_fO]]);});}]));}));}];};}};return [1,function(_fP){return new F(function(){return A(_fI,[_fP,_fH]);});}];},_fQ=new T(function(){return B(unCStr(".."));}),_fR=new T(function(){return B(unCStr("::"));}),_fS=new T(function(){return B(unCStr("->"));}),_fT=[0,64],_fU=[1,_fT,_Q],_fV=[0,126],_fW=[1,_fV,_Q],_fX=new T(function(){return B(unCStr("=>"));}),_fY=[1,_fX,_Q],_fZ=[1,_fW,_fY],_g0=[1,_fU,_fZ],_g1=[1,_fS,_g0],_g2=new T(function(){return B(unCStr("<-"));}),_g3=[1,_g2,_g1],_g4=[0,124],_g5=[1,_g4,_Q],_g6=[1,_g5,_g3],_g7=[1,_dS,_Q],_g8=[1,_g7,_g6],_g9=[0,61],_ga=[1,_g9,_Q],_gb=[1,_ga,_g8],_gc=[1,_fR,_gb],_gd=[1,_fQ,_gc],_ge=function(_gf){return new F(function(){return _6m([1,function(_gg){return E(_gg)[0]==0?E(new T(function(){return B(A(_gf,[_7Y]));})):[2];}],new T(function(){return B(_6m([0,function(_gh){return E(E(_gh)[1])==39?E([0,function(_gi){var _gj=E(_gi);switch(E(_gj[1])){case 39:return [2];case 92:return E(new T(function(){return B(_ex(function(_gk){var _gl=E(_gk);return new F(function(){return (function(_gm,_gn){var _go=new T(function(){return B(A(_gf,[[0,_gm]]));});return !E(_gn)?E(E(_gm)[1])==39?[2]:[0,function(_gp){return E(E(_gp)[1])==39?E(_go):[2];}]:[0,function(_gq){return E(E(_gq)[1])==39?E(_go):[2];}];})(_gl[1],_gl[2]);});}));}));default:return [0,function(_gr){return E(E(_gr)[1])==39?E(new T(function(){return B(A(_gf,[[0,_gj]]));})):[2];}];}}]):[2];}],new T(function(){return B(_6m([0,function(_gs){return E(E(_gs)[1])==34?E(new T(function(){return B(_fn(_R,_gf));})):[2];}],new T(function(){return B(_6m([0,function(_gt){return !B(_9t(_73,_gt,_fC))?[2]:B(A(_gf,[[2,[1,_gt,_Q]]]));}],new T(function(){return B(_6m([0,function(_gu){if(!B(_9t(_73,_gu,_9y))){return [2];}else{return new F(function(){return _fF(_9z,function(_gv){var _gw=[1,_gu,_gv];return !B(_9t(_7k,_gw,_gd))?B(A(_gf,[[4,_gw]])):B(A(_gf,[[2,_gw]]));});});}}],new T(function(){return B(_6m([0,function(_gx){var _gy=E(_gx),_gz=_gy[1],_gA=u_iswalpha(_gz),_gB=_gA;if(!E(_gB)){if(E(_gz)==95){return new F(function(){return _fF(_fA,function(_gC){return new F(function(){return A(_gf,[[3,[1,_gy,_gC]]]);});});});}else{return [2];}}else{return new F(function(){return _fF(_fA,function(_gD){return new F(function(){return A(_gf,[[3,[1,_gy,_gD]]]);});});});}}],new T(function(){return B(_7E(_9D,_9o,_gf));})));})));})));})));})));}));});},_gE=function(_gF){return [1,function(_gG){return new F(function(){return A(_eM,[_gG,function(_gH){return E(new T(function(){return B(_ge(_gF));}));}]);});}];},_gI=[0,0],_gJ=function(_gK,_gL){return new F(function(){return _gE(function(_gM){var _gN=E(_gM);if(_gN[0]==2){var _gO=E(_gN[1]);return _gO[0]==0?[2]:E(E(_gO[1])[1])==40?E(_gO[2])[0]==0?E(new T(function(){return B(A(_gK,[_gI,function(_gP){return new F(function(){return _gE(function(_gQ){var _gR=E(_gQ);if(_gR[0]==2){var _gS=E(_gR[1]);return _gS[0]==0?[2]:E(E(_gS[1])[1])==41?E(_gS[2])[0]==0?E(new T(function(){return B(A(_gL,[_gP]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_gT=function(_gU,_gV,_gW){var _gX=function(_gY,_gZ){return new F(function(){return _6m(B(_gE(function(_h0){var _h1=E(_h0);if(_h1[0]==4){var _h2=E(_h1[1]);if(!_h2[0]){return new F(function(){return A(_gU,[_h1,_gY,_gZ]);});}else{return E(E(_h2[1])[1])==45?E(_h2[2])[0]==0?E([1,function(_h3){return new F(function(){return A(_eM,[_h3,function(_h4){return E(new T(function(){return B(_ge(function(_h5){return new F(function(){return A(_gU,[_h5,_gY,function(_h6){return new F(function(){return A(_gZ,[new T(function(){return [0, -E(_h6)[1]];})]);});}]);});}));}));}]);});}]):B(A(_gU,[_h1,_gY,_gZ])):B(A(_gU,[_h1,_gY,_gZ]));}}else{return new F(function(){return A(_gU,[_h1,_gY,_gZ]);});}})),new T(function(){return B(_gJ(_gX,_gZ));}));});};return new F(function(){return _gX(_gV,_gW);});},_h7=function(_h8,_h9){return [2];},_ha=function(_hb,_hc){return new F(function(){return _h7(_hb,_hc);});},_hd=function(_he){var _hf=E(_he);return _hf[0]==0?[1,new T(function(){return B(_90(new T(function(){return B(_8Q(E(_hf[1])[1]));}),_8P,_hf[2]));})]:E(_hf[2])[0]==0?E(_hf[3])[0]==0?[1,new T(function(){return B(_90(_8O,_8P,_hf[1]));})]:[0]:[0];},_hg=function(_hh){var _hi=E(_hh);if(_hi[0]==5){var _hj=B(_hd(_hi[1]));return _hj[0]==0?E(_h7):function(_hk,_hl){return new F(function(){return A(_hl,[new T(function(){return [0,B(_9U(_hj[1]))];})]);});};}else{return E(_ha);}},_hm=function(_hn,_ho){while(1){var _hp=E(_hn);if(!_hp[0]){return E(_ho)[0]==0?true:false;}else{var _hq=E(_ho);if(!_hq[0]){return false;}else{if(E(_hp[1])[1]!=E(_hq[1])[1]){return false;}else{_hn=_hp[2];_ho=_hq[2];continue;}}}}},_hr=new T(function(){return B(unCStr("onSideIndex"));}),_hs=new T(function(){return B(unCStr("LeftSidePlacement"));}),_ht=new T(function(){return B(unCStr("RightSidePlacement"));}),_hu=function(_hv,_hw){var _hx=new T(function(){if(_hv>11){var _hy=[2];}else{var _hy=[1,function(_hz){return new F(function(){return A(_eM,[_hz,function(_hA){return E(new T(function(){return B(_ge(function(_hB){var _hC=E(_hB);return _hC[0]==3?!B(_hm(_hC[1],_ht))?[2]:E([1,function(_hD){return new F(function(){return A(_eM,[_hD,function(_hE){return E(new T(function(){return B(_ge(function(_hF){var _hG=E(_hF);if(_hG[0]==2){var _hH=E(_hG[1]);return _hH[0]==0?[2]:E(E(_hH[1])[1])==123?E(_hH[2])[0]==0?E([1,function(_hI){return new F(function(){return A(_eM,[_hI,function(_hJ){return E(new T(function(){return B(_ge(function(_hK){var _hL=E(_hK);return _hL[0]==3?!B(_hm(_hL[1],_hr))?[2]:E([1,function(_hM){return new F(function(){return A(_eM,[_hM,function(_hN){return E(new T(function(){return B(_ge(function(_hO){var _hP=E(_hO);if(_hP[0]==2){var _hQ=E(_hP[1]);return _hQ[0]==0?[2]:E(E(_hQ[1])[1])==61?E(_hQ[2])[0]==0?E(new T(function(){return B(_gT(_hg,_gI,function(_hR){return new F(function(){return _gE(function(_hS){var _hT=E(_hS);if(_hT[0]==2){var _hU=E(_hT[1]);return _hU[0]==0?[2]:E(E(_hU[1])[1])==125?E(_hU[2])[0]==0?E(new T(function(){return B(A(_hw,[[3,_hR]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}];}return _hy;});if(_hv>11){return new F(function(){return _6m(_7w,_hx);});}else{return new F(function(){return _6m(B(_gE(function(_hV){var _hW=E(_hV);return _hW[0]==3?!B(_hm(_hW[1],_hs))?[2]:E([1,function(_hX){return new F(function(){return A(_eM,[_hX,function(_hY){return E(new T(function(){return B(_ge(function(_hZ){var _i0=E(_hZ);if(_i0[0]==2){var _i1=E(_i0[1]);return _i1[0]==0?[2]:E(E(_i1[1])[1])==123?E(_i1[2])[0]==0?E([1,function(_i2){return new F(function(){return A(_eM,[_i2,function(_i3){return E(new T(function(){return B(_ge(function(_i4){var _i5=E(_i4);return _i5[0]==3?!B(_hm(_i5[1],_hr))?[2]:E([1,function(_i6){return new F(function(){return A(_eM,[_i6,function(_i7){return E(new T(function(){return B(_ge(function(_i8){var _i9=E(_i8);if(_i9[0]==2){var _ia=E(_i9[1]);return _ia[0]==0?[2]:E(E(_ia[1])[1])==61?E(_ia[2])[0]==0?E(new T(function(){return B(_gT(_hg,_gI,function(_ib){return new F(function(){return _gE(function(_ic){var _id=E(_ic);if(_id[0]==2){var _ie=E(_id[1]);return _ie[0]==0?[2]:E(E(_ie[1])[1])==125?E(_ie[2])[0]==0?E(new T(function(){return B(A(_hw,[[2,_ib]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),_hx);});}},_if=new T(function(){return B(unCStr("onBarIndex"));}),_ig=new T(function(){return B(unCStr("BarPlacement"));}),_ih=function(_ii,_ij){if(_ii>11){return new F(function(){return _6m(_7w,new T(function(){return B(_hu(_ii,_ij));}));});}else{return new F(function(){return _6m(B(_gE(function(_ik){var _il=E(_ik);return _il[0]==3?!B(_hm(_il[1],_ig))?[2]:E([1,function(_im){return new F(function(){return A(_eM,[_im,function(_in){return E(new T(function(){return B(_ge(function(_io){var _ip=E(_io);if(_ip[0]==2){var _iq=E(_ip[1]);return _iq[0]==0?[2]:E(E(_iq[1])[1])==123?E(_iq[2])[0]==0?E([1,function(_ir){return new F(function(){return A(_eM,[_ir,function(_is){return E(new T(function(){return B(_ge(function(_it){var _iu=E(_it);return _iu[0]==3?!B(_hm(_iu[1],_if))?[2]:E([1,function(_iv){return new F(function(){return A(_eM,[_iv,function(_iw){return E(new T(function(){return B(_ge(function(_ix){var _iy=E(_ix);if(_iy[0]==2){var _iz=E(_iy[1]);return _iz[0]==0?[2]:E(E(_iz[1])[1])==61?E(_iz[2])[0]==0?E(new T(function(){return B(_gT(_hg,_gI,function(_iA){return new F(function(){return _gE(function(_iB){var _iC=E(_iB);if(_iC[0]==2){var _iD=E(_iC[1]);return _iD[0]==0?[2]:E(E(_iD[1])[1])==125?E(_iD[2])[0]==0?E(new T(function(){return B(A(_ij,[[1,_iA]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_hu(_ii,_ij));}));});}},_iE=new T(function(){return B(unCStr("onPointIndex"));}),_iF=new T(function(){return B(unCStr("pointIndex"));}),_iG=new T(function(){return B(unCStr("PointPlacement"));}),_iH=function(_iI,_iJ){if(_iI>11){return new F(function(){return _6m(_7w,new T(function(){return B(_ih(_iI,_iJ));}));});}else{return new F(function(){return _6m(B(_gE(function(_iK){var _iL=E(_iK);return _iL[0]==3?!B(_hm(_iL[1],_iG))?[2]:E([1,function(_iM){return new F(function(){return A(_eM,[_iM,function(_iN){return E(new T(function(){return B(_ge(function(_iO){var _iP=E(_iO);if(_iP[0]==2){var _iQ=E(_iP[1]);return _iQ[0]==0?[2]:E(E(_iQ[1])[1])==123?E(_iQ[2])[0]==0?E([1,function(_iR){return new F(function(){return A(_eM,[_iR,function(_iS){return E(new T(function(){return B(_ge(function(_iT){var _iU=E(_iT);return _iU[0]==3?!B(_hm(_iU[1],_iF))?[2]:E([1,function(_iV){return new F(function(){return A(_eM,[_iV,function(_iW){return E(new T(function(){return B(_ge(function(_iX){var _iY=E(_iX);if(_iY[0]==2){var _iZ=E(_iY[1]);return _iZ[0]==0?[2]:E(E(_iZ[1])[1])==61?E(_iZ[2])[0]==0?E(new T(function(){return B(_gT(_hg,_gI,function(_j0){return new F(function(){return _gE(function(_j1){var _j2=E(_j1);if(_j2[0]==2){var _j3=E(_j2[1]);return _j3[0]==0?[2]:E(E(_j3[1])[1])==44?E(_j3[2])[0]==0?E([1,function(_j4){return new F(function(){return A(_eM,[_j4,function(_j5){return E(new T(function(){return B(_ge(function(_j6){var _j7=E(_j6);return _j7[0]==3?!B(_hm(_j7[1],_iE))?[2]:E([1,function(_j8){return new F(function(){return A(_eM,[_j8,function(_j9){return E(new T(function(){return B(_ge(function(_ja){var _jb=E(_ja);if(_jb[0]==2){var _jc=E(_jb[1]);return _jc[0]==0?[2]:E(E(_jc[1])[1])==61?E(_jc[2])[0]==0?E(new T(function(){return B(_gT(_hg,_gI,function(_jd){return new F(function(){return _gE(function(_je){var _jf=E(_je);if(_jf[0]==2){var _jg=E(_jf[1]);return _jg[0]==0?[2]:E(E(_jg[1])[1])==125?E(_jg[2])[0]==0?E(new T(function(){return B(A(_iJ,[[0,_j0,_jd]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_ih(_iI,_iJ));}));});}},_jh=function(_ji,_jj){return new F(function(){return _iH(E(_ji)[1],_jj);});},_jk=function(_jl,_jm){var _jn=function(_jo){return function(_jp){return new F(function(){return _6m(B(A(new T(function(){return B(A(_jl,[_jo]));}),[_jp])),new T(function(){return B(_gJ(_jn,_jp));}));});};};return new F(function(){return _jn(_jm);});},_jq=function(_jr){return [1,function(_js){return new F(function(){return A(_eM,[_js,function(_jt){return E([3,_jr,_7w]);}]);});}];},_ju=new T(function(){return B(A(_jk,[_jh,_gI,_jq]));}),_jv=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_jw=new T(function(){return B(err(_jv));}),_jx=function(_jy,_jz){return new F(function(){return A(_jz,[_50]);});},_jA=[0,_4,_jx],_jB=[1,_jA,_Q],_jC=function(_jD,_jE){return new F(function(){return A(_jE,[_4Z]);});},_jF=[0,_3,_jC],_jG=[1,_jF,_jB],_jH=function(_jI,_jJ,_jK){var _jL=E(_jI);if(!_jL[0]){return [2];}else{var _jM=E(_jL[1]),_jN=_jM[1],_jO=new T(function(){return B(A(_jM[2],[_jJ,_jK]));});return new F(function(){return _6m(B(_gE(function(_jP){var _jQ=E(_jP);switch(_jQ[0]){case 3:return !B(_hm(_jN,_jQ[1]))?[2]:E(_jO);case 4:return !B(_hm(_jN,_jQ[1]))?[2]:E(_jO);default:return [2];}})),new T(function(){return B(_jH(_jL[2],_jJ,_jK));}));});}},_jR=function(_jS,_jT){return new F(function(){return _jH(_jG,_jS,_jT);});},_jU=new T(function(){return B(A(_jk,[_jR,_gI,_jq]));}),_jV=new T(function(){return B(err(_jv));}),_jW=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_jX=new T(function(){return B(err(_jW));}),_jY=new T(function(){return B(err(_jW));}),_jZ=function(_k0,_k1,_k2){return _k2<=_k1?[1,[0,_k0],new T(function(){var _k3=_k1-_k0|0,_k4=function(_k5){return _k5>=(_k2-_k3|0)?[1,[0,_k5],new T(function(){return B(_k4(_k5+_k3|0));})]:[1,[0,_k5],_Q];};return B(_k4(_k1));})]:_k2<=_k0?[1,[0,_k0],_Q]:[0];},_k6=function(_k7,_k8,_k9){return _k9>=_k8?[1,[0,_k7],new T(function(){var _ka=_k8-_k7|0,_kb=function(_kc){return _kc<=(_k9-_ka|0)?[1,[0,_kc],new T(function(){return B(_kb(_kc+_ka|0));})]:[1,[0,_kc],_Q];};return B(_kb(_k8));})]:_k9>=_k7?[1,[0,_k7],_Q]:[0];},_kd=function(_ke,_kf){return _kf<_ke?B(_jZ(_ke,_kf,-2147483648)):B(_k6(_ke,_kf,2147483647));},_kg=new T(function(){return B(_kd(135,150));}),_kh=function(_ki,_kj){var _kk=E(_ki);if(!_kk){return [0];}else{var _kl=E(_kj);return _kl[0]==0?[0]:[1,_kl[1],new T(function(){return B(_kh(_kk-1|0,_kl[2]));})];}},_km=new T(function(){return B(_kh(6,_kg));}),_kn=function(_ko,_kp){var _kq=E(_ko);if(!_kq[0]){return E(_km);}else{var _kr=_kq[1];return _kp>1?[1,_kr,new T(function(){return B(_kn(_kq[2],_kp-1|0));})]:[1,_kr,_km];}},_ks=new T(function(){return B(_kd(25,40));}),_kt=new T(function(){return B(_kn(_ks,6));}),_ku=function(_kv){while(1){var _kw=(function(_kx){var _ky=E(_kx);if(!_ky[0]){return [0];}else{var _kz=_ky[2],_kA=E(_ky[1]);if(!E(_kA[2])[0]){return [1,_kA[1],new T(function(){return B(_ku(_kz));})];}else{_kv=_kz;return null;}}})(_kv);if(_kw!=null){return _kw;}}},_kB=function(_kC,_kD){var _kE=E(_kD);if(!_kE[0]){return [0,_Q,_Q];}else{var _kF=_kE[1];if(!B(A(_kC,[_kF]))){var _kG=new T(function(){var _kH=B(_kB(_kC,_kE[2]));return [0,_kH[1],_kH[2]];});return [0,[1,_kF,new T(function(){return E(E(_kG)[1]);})],new T(function(){return E(E(_kG)[2]);})];}else{return [0,_Q,_kE];}}},_kI=function(_kJ,_kK){while(1){var _kL=E(_kK);if(!_kL[0]){return [0];}else{if(!B(A(_kJ,[_kL[1]]))){return E(_kL);}else{_kK=_kL[2];continue;}}}},_kM=function(_kN){var _kO=E(_kN);switch(_kO){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _kP=u_iswspace(_kO),_kQ=_kP;return E(_kQ)==0?false:true;}},_kR=function(_kS){return new F(function(){return _kM(E(_kS)[1]);});},_kT=function(_kU){var _kV=B(_kI(_kR,_kU));if(!_kV[0]){return [0];}else{var _kW=new T(function(){var _kX=B(_kB(_kR,_kV));return [0,_kX[1],_kX[2]];});return [1,new T(function(){return E(E(_kW)[1]);}),new T(function(){return B(_kT(E(_kW)[2]));})];}},_kY=function(_kZ,_){var _l0=jsFind(toJSStr(E(_5W))),_l1=_l0,_l2=E(_l1);if(!_l2[0]){return new F(function(){return _4c(_5q,_);});}else{var _l3=jsSetCB(E(_l2[1])[1],E(_5w)[1],E(_6a)[1]),_l4=_l3,_l5=setDropCheckerCallback_ffi(function(_l6,_l7,_l8){var _l9=E(_kZ),_la=_l9[1],_lb=_l9[6],_lc=new T(function(){return B(_kT(B(_5Q(_l6))));}),_ld=B(_ku(B(_6c(_ju,new T(function(){return B(_10(_5S,B(_55(_lc,2))));})))));if(!_ld[0]){return E(_jY);}else{if(!E(_ld[2])[0]){var _le=E(_ld[1]);if(!_le[0]){var _lf=B(_5x(function(_lg){var _lh=E(_lg)[1]-E(_l7)[1];return _lh<0? -_lh<7:_lh<7;},_kt));if(!_lf[0]){return function(_7X){return new F(function(){return _5g(_le,_le,_lb,_7X);});};}else{var _li=_lf[1],_lj=function(_lk,_ll,_){var _lm=E(_le[1]),_ln=_lm[1];if(_lk<=_ln){return new F(function(){return _5g(_le,_le,_lb,_);});}else{var _lo=B(_ku(B(_6c(_jU,new T(function(){return B(_55(_lc,1));})))));if(!_lo[0]){return E(_jX);}else{var _lp=_lo[1];if(!E(_lo[2])[0]){if(_lk>=0){var _lq=B(_55(_la,_lk)),_lr=function(_){var _ls=B(_5g(_le,[0,_ll,new T(function(){if(_lk>=0){var _lt=E(B(_55(_la,_lk))[2]);}else{var _lt=E(_52);}return _lt;})],_lb,_)),_lu=_ls;if(_ln>=0){var _lv=new T(function(){return B(_5J(function(_lw,_lx,_ly){return [1,new T(function(){var _lz=E(_lw)[1];return _lz!=_ln?_lz!=_lk?E(_lx):[0,new T(function(){if(_ln>=0){var _lA=E(B(_55(_la,_ln))[1]);}else{var _lA=E(_52);}return _lA;}),new T(function(){return [0,E(E(_lx)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_lx)[1]);}),new T(function(){return [0,E(E(_lx)[2])[1]-1|0];})];}),_ly];},_Q,_4p,_la));}),_lB=B((function(_lC,_){while(1){var _lD=(function(_lE,_){var _lF=E(_lE);if(!_lF[0]){return _J;}else{var _lG=_lF[1],_lH=B(_5g([0,_lm,_lG],[0,_lm,new T(function(){return [0,E(_lG)[1]-1|0];})],_lb,_)),_lI=_lH;_lC=_lF[2];return null;}})(_lC,_);if(_lD!=null){return _lD;}}})(B(_5r(1,B(_4j(E(_le[2])[1],E(B(_55(_lv,_ln))[2])[1])))),_)),_lJ=_lB;return new F(function(){return _kY([0,_lv,_l9[2],_l9[3],_l9[4],_l9[5],_lb,_l9[7]],_);});}else{return E(_52);}},_lK=function(_){return E(_lq[2])[1]>=2?B(_5g(_le,_le,_lb,_)):B(_lr(_));};return E(_lq[1])==0?E(_lp)==0?B(_lr(_)):B(_lK(_)):E(_lp)==0?B(_lK(_)):B(_lr(_));}else{return E(_52);}}else{return E(_jV);}}}};if(E(_l8)[1]<=E(_5V)[1]){var _lL=E(_li);return function(_7X){return new F(function(){return _lj(_lL[1],_lL,_7X);});};}else{var _lM=23-E(_li)[1]|0;return function(_7X){return new F(function(){return _lj(_lM,[0,_lM],_7X);});};}}}else{return function(_7X){return new F(function(){return _5g(_le,_le,_lb,_7X);});};}}else{return E(_jw);}}});return _J;}},_lN=function(_lO,_lP){while(1){var _lQ=E(_lO);if(!_lQ[0]){return E(_lP);}else{_lO=_lQ[2];var _lR=[1,_lQ[1],_lP];_lP=_lR;continue;}}},_lS=[0,2],_lT=[0,0],_lU=[1,_lT,_Q],_lV=[1,_lT,_lU],_lW=[1,_lT,_lV],_lX=[1,_lT,_lW],_lY=[1,_lT,_lX],_lZ=[0,5],_m0=[1,_lZ,_lY],_m1=[1,_lT,_m0],_m2=[0,3],_m3=[1,_m2,_m1],_m4=[1,_lT,_m3],_m5=[1,_lT,_m4],_m6=[1,_lT,_m5],_m7=[1,_lT,_m6],_m8=[1,_lZ,_m7],_m9=[1,_lT,_m8],_ma=[1,_lT,_m9],_mb=[1,_lT,_ma],_mc=[1,_lT,_mb],_md=[1,_lT,_mc],_me=[1,_lT,_md],_mf=[1,_lT,_me],_mg=[1,_lT,_mf],_mh=[1,_lT,_mg],_mi=[1,_lT,_mh],_mj=[1,_lS,_mi],_mk=function(_ml){var _mm=E(_ml);return _mm[0]==0?[0]:[1,[0,_50,_mm[1]],new T(function(){return B(_mk(_mm[2]));})];},_mn=new T(function(){return B(_mk(_mj));}),_mo=new T(function(){return B(_lN(_mn,_Q));}),_mp=new T(function(){return B(_2x("main.hs:(251,20)-(252,55)|function whiteOrBlack"));}),_mq=function(_mr,_ms){var _mt=E(_mr);if(!_mt[0]){return [0];}else{var _mu=E(_ms);return _mu[0]==0?[0]:[1,new T(function(){var _mv=E(_mu[1]);if(!E(_mv[1])){var _mw=E(_mp);}else{if(!E(E(_mv[2])[1])){var _mx=E(_mt[1]),_my=E(_mx[1])==0?E(_mx):[0,_4Z,_mx[2]];}else{var _my=E(_mv);}var _mz=_my,_mw=_mz;}var _mA=_mw;return _mA;}),new T(function(){return B(_mq(_mt[2],_mu[2]));})];}},_mB=new T(function(){return B(_mq(_mo,_mn));}),_mC=function(_mD,_mE){while(1){var _mF=E(_mD);if(!_mF[0]){return E(_mE);}else{_mD=_mF[2];var _mG=_mE+E(_mF[1])[1]|0;_mE=_mG;continue;}}},_mH=new T(function(){return [0,B(_mC(_mj,0))];}),_mI=[0,_mB,_mH,_mH,_lT,_lT,_50,_50],_mJ=function(_){var _mK=E(_mH)[1],_mL=B(_4t(_50,_50,_mK,_)),_mM=_mL,_mN=B(_4t(_4Z,_50,_mK,_)),_mO=_mN;return new F(function(){return _kY(_mI,_);});},_mP=function(_){var _mQ=jsFind(toJSStr(E(_2))),_mR=_mQ,_mS=E(_mR);if(!_mS[0]){return new F(function(){return _mJ(_);});}else{var _mT=jsSet(E(_mS[1])[1],toJSStr(E(_1)),toJSStr(E(_0)));return new F(function(){return _mJ(_);});}},_mU=function(_){return new F(function(){return _mP(_);});};
var hasteMain = function() {B(A(_mU, [0]));};window.onload = hasteMain;