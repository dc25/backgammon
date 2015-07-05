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

var _0=new T(function(){return B(unCStr("Black"));}),_1=new T(function(){return B(unCStr("White"));}),_2=[0,125],_3=new T(function(){return B(unCStr(", "));}),_4=function(_5,_6){var _7=E(_5);return _7[0]==0?E(_6):[1,_7[1],new T(function(){return B(_4(_7[2],_6));})];},_8=function(_9,_a){var _b=jsShowI(_9),_c=_b;return new F(function(){return _4(fromJSStr(_c),_a);});},_d=[0,41],_e=[0,40],_f=function(_g,_h,_i){return _h>=0?B(_8(_h,_i)):_g<=6?B(_8(_h,_i)):[1,_e,new T(function(){var _j=jsShowI(_h),_k=_j;return B(_4(fromJSStr(_k),[1,_d,_i]));})];},_l=new T(function(){return B(unCStr("onPointIndex = "));}),_m=new T(function(){return B(unCStr("BarPlacement {"));}),_n=new T(function(){return B(unCStr("onBarIndex = "));}),_o=new T(function(){return B(unCStr("LeftSidePlacement {"));}),_p=new T(function(){return B(unCStr("onSideIndex = "));}),_q=new T(function(){return B(unCStr("RightSidePlacement {"));}),_r=new T(function(){return B(unCStr("PointPlacement {"));}),_s=new T(function(){return B(unCStr("pointIndex = "));}),_t=function(_u,_v,_w){var _x=E(_v);switch(_x[0]){case 0:var _y=function(_z){return new F(function(){return _4(_s,new T(function(){return B(_f(0,E(_x[1])[1],new T(function(){return B(_4(_3,new T(function(){return B(_4(_l,new T(function(){return B(_f(0,E(_x[2])[1],[1,_2,_z]));})));})));})));}));});};return _u<11?B(_4(_r,new T(function(){return B(_y(_w));}))):[1,_e,new T(function(){return B(_4(_r,new T(function(){return B(_y([1,_d,_w]));})));})];case 1:var _A=function(_B){return new F(function(){return _4(_m,new T(function(){return B(_4(_n,new T(function(){return B(_f(0,E(_x[1])[1],[1,_2,_B]));})));}));});};return _u<11?B(_A(_w)):[1,_e,new T(function(){return B(_A([1,_d,_w]));})];case 2:var _C=function(_D){return new F(function(){return _4(_o,new T(function(){return B(_4(_p,new T(function(){return B(_f(0,E(_x[1])[1],[1,_2,_D]));})));}));});};return _u<11?B(_C(_w)):[1,_e,new T(function(){return B(_C([1,_d,_w]));})];default:var _E=function(_F){return new F(function(){return _4(_q,new T(function(){return B(_4(_p,new T(function(){return B(_f(0,E(_x[1])[1],[1,_2,_F]));})));}));});};return _u<11?B(_E(_w)):[1,_e,new T(function(){return B(_E([1,_d,_w]));})];}},_G=0,_H=function(_I,_J,_K,_L){return new F(function(){return A(_I,[new T(function(){return function(_){var _M=jsSetAttr(E(_J)[1],toJSStr(E(_K)),toJSStr(E(_L)));return _G;};})]);});},_N=[0],_O=function(_P){return E(_P);},_Q=[0,95],_R=function(_S){var _T=E(_S);return E(_T[1])==32?E(_Q):E(_T);},_U=new T(function(){return B(unCStr("class"));}),_V=new T(function(){return B(unCStr("draggable "));}),_W=[0,32],_X=function(_Y,_Z){var _10=E(_Z);return _10[0]==0?[0]:[1,new T(function(){return B(A(_Y,[_10[1]]));}),new T(function(){return B(_X(_Y,_10[2]));})];},_11=function(_12,_13,_14,_15){return new F(function(){return _H(_O,_12,_U,new T(function(){var _16=new T(function(){var _17=new T(function(){return B(_X(_R,B(_t(0,_14,_N))));});return E(_15)==0?B(_4(_0,[1,_W,_17])):B(_4(_1,[1,_W,_17]));});return E(_13)==0?E(_15)==0?B(_4(_V,_16)):E(_16):E(_15)==0?E(_16):B(_4(_V,_16));}));});},_18=new T(function(){return B(unCStr("Control.Exception.Base"));}),_19=new T(function(){return B(unCStr("base"));}),_1a=new T(function(){return B(unCStr("PatternMatchFail"));}),_1b=new T(function(){var _1c=hs_wordToWord64(18445595),_1d=_1c,_1e=hs_wordToWord64(52003073),_1f=_1e;return [0,_1d,_1f,[0,_1d,_1f,_19,_18,_1a],_N];}),_1g=function(_1h){return E(_1b);},_1i=function(_1j){return E(E(_1j)[1]);},_1k=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1l=new T(function(){return B(err(_1k));}),_1m=function(_1n,_1o,_1p){var _1q=new T(function(){var _1r=B(A(_1n,[_1p])),_1s=B(A(_1o,[new T(function(){var _1t=E(_1q);return _1t[0]==0?E(_1l):E(_1t[1]);})])),_1u=hs_eqWord64(_1r[1],_1s[1]),_1v=_1u;if(!E(_1v)){var _1w=[0];}else{var _1x=hs_eqWord64(_1r[2],_1s[2]),_1y=_1x,_1w=E(_1y)==0?[0]:[1,_1p];}var _1z=_1w,_1A=_1z;return _1A;});return E(_1q);},_1B=function(_1C){var _1D=E(_1C);return new F(function(){return _1m(B(_1i(_1D[1])),_1g,_1D[2]);});},_1E=function(_1F){return E(E(_1F)[1]);},_1G=function(_1H,_1I){return new F(function(){return _4(E(_1H)[1],_1I);});},_1J=[0,44],_1K=[0,93],_1L=[0,91],_1M=function(_1N,_1O,_1P){var _1Q=E(_1O);return _1Q[0]==0?B(unAppCStr("[]",_1P)):[1,_1L,new T(function(){return B(A(_1N,[_1Q[1],new T(function(){var _1R=function(_1S){var _1T=E(_1S);return _1T[0]==0?E([1,_1K,_1P]):[1,_1J,new T(function(){return B(A(_1N,[_1T[1],new T(function(){return B(_1R(_1T[2]));})]));})];};return B(_1R(_1Q[2]));})]));})];},_1U=function(_1V,_1W){return new F(function(){return _1M(_1G,_1V,_1W);});},_1X=function(_1Y,_1Z,_20){return new F(function(){return _4(E(_1Z)[1],_20);});},_21=[0,_1X,_1E,_1U],_22=new T(function(){return [0,_1g,_21,_23,_1B];}),_23=function(_24){return [0,_22,_24];},_25=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_26=function(_27,_28){return new F(function(){return die(new T(function(){return B(A(_28,[_27]));}));});},_29=function(_2a,_2b){var _2c=E(_2b);if(!_2c[0]){return [0,_N,_N];}else{var _2d=_2c[1];if(!B(A(_2a,[_2d]))){return [0,_N,_2c];}else{var _2e=new T(function(){var _2f=B(_29(_2a,_2c[2]));return [0,_2f[1],_2f[2]];});return [0,[1,_2d,new T(function(){return E(E(_2e)[1]);})],new T(function(){return E(E(_2e)[2]);})];}}},_2g=[0,32],_2h=[0,10],_2i=[1,_2h,_N],_2j=function(_2k){return E(E(_2k)[1])==124?false:true;},_2l=function(_2m,_2n){var _2o=B(_29(_2j,B(unCStr(_2m)))),_2p=_2o[1],_2q=function(_2r,_2s){return new F(function(){return _4(_2r,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_4(_2n,new T(function(){return B(_4(_2s,_2i));})));})));}));});},_2t=E(_2o[2]);if(!_2t[0]){return new F(function(){return _2q(_2p,_N);});}else{return E(E(_2t[1])[1])==124?B(_2q(_2p,[1,_2g,_2t[2]])):B(_2q(_2p,_N));}},_2u=function(_2v){return new F(function(){return _26([0,new T(function(){return B(_2l(_2v,_25));})],_23);});},_2w=new T(function(){return B(_2u("main.hs:(84,1)-(111,116)|function checkerPosition"));}),_2x=function(_2y,_2z){if(_2y<=0){if(_2y>=0){return new F(function(){return quot(_2y,_2z);});}else{if(_2z<=0){return new F(function(){return quot(_2y,_2z);});}else{return quot(_2y+1|0,_2z)-1|0;}}}else{if(_2z>=0){if(_2y>=0){return new F(function(){return quot(_2y,_2z);});}else{if(_2z<=0){return new F(function(){return quot(_2y,_2z);});}else{return quot(_2y+1|0,_2z)-1|0;}}}else{return quot(_2y-1|0,_2z)-1|0;}}},_2A=new T(function(){return [0,B(_2x(15,2))];}),_2B=new T(function(){return [0,220+B(_2x(15,2))|0];}),_2C=function(_2D){var _2E=E(_2D);switch(_2E[0]){case 0:var _2F=_2E[1],_2G=_2E[2];return [0,new T(function(){var _2H=E(_2F)[1];if(_2H>=12){var _2I=23-_2H|0;if(_2I>=6){var _2J=[0,25+(20+(imul(_2I,15)|0)|0)|0];}else{var _2J=[0,25+(imul(_2I,15)|0)|0];}var _2K=_2J,_2L=_2K;}else{if(_2H>=6){var _2M=[0,25+(20+(imul(_2H,15)|0)|0)|0];}else{var _2M=[0,25+(imul(_2H,15)|0)|0];}var _2L=_2M;}var _2N=_2L;return _2N;}),new T(function(){if(E(_2F)[1]>=12){var _2O=[0,203+(imul(imul(imul(-1,E(_2G)[1])|0,2)|0,6)|0)|0];}else{var _2O=[0,7+(imul(imul(E(_2G)[1],2)|0,6)|0)|0];}var _2P=_2O;return _2P;})];case 1:return E(_2w);case 2:return [0,_2A,new T(function(){return [0,203-(imul(imul(E(_2E[1])[1],2)|0,6)|0)|0];})];default:return [0,_2B,new T(function(){return [0,203-(imul(imul(E(_2E[1])[1],2)|0,6)|0)|0];})];}},_2Q=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:148:5-10"));}),_2R=function(_){return _G;},_2S=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_2T=new T(function(){return B(unCStr("base"));}),_2U=new T(function(){return B(unCStr("IOException"));}),_2V=new T(function(){var _2W=hs_wordToWord64(4053623282),_2X=_2W,_2Y=hs_wordToWord64(3693590983),_2Z=_2Y;return [0,_2X,_2Z,[0,_2X,_2Z,_2T,_2S,_2U],_N];}),_30=function(_31){return E(_2V);},_32=function(_33){var _34=E(_33);return new F(function(){return _1m(B(_1i(_34[1])),_30,_34[2]);});},_35=new T(function(){return B(unCStr(": "));}),_36=[0,41],_37=new T(function(){return B(unCStr(" ("));}),_38=new T(function(){return B(unCStr("already exists"));}),_39=new T(function(){return B(unCStr("does not exist"));}),_3a=new T(function(){return B(unCStr("protocol error"));}),_3b=new T(function(){return B(unCStr("failed"));}),_3c=new T(function(){return B(unCStr("invalid argument"));}),_3d=new T(function(){return B(unCStr("inappropriate type"));}),_3e=new T(function(){return B(unCStr("hardware fault"));}),_3f=new T(function(){return B(unCStr("unsupported operation"));}),_3g=new T(function(){return B(unCStr("timeout"));}),_3h=new T(function(){return B(unCStr("resource vanished"));}),_3i=new T(function(){return B(unCStr("interrupted"));}),_3j=new T(function(){return B(unCStr("resource busy"));}),_3k=new T(function(){return B(unCStr("resource exhausted"));}),_3l=new T(function(){return B(unCStr("end of file"));}),_3m=new T(function(){return B(unCStr("illegal operation"));}),_3n=new T(function(){return B(unCStr("permission denied"));}),_3o=new T(function(){return B(unCStr("user error"));}),_3p=new T(function(){return B(unCStr("unsatisified constraints"));}),_3q=new T(function(){return B(unCStr("system error"));}),_3r=function(_3s,_3t){switch(E(_3s)){case 0:return new F(function(){return _4(_38,_3t);});break;case 1:return new F(function(){return _4(_39,_3t);});break;case 2:return new F(function(){return _4(_3j,_3t);});break;case 3:return new F(function(){return _4(_3k,_3t);});break;case 4:return new F(function(){return _4(_3l,_3t);});break;case 5:return new F(function(){return _4(_3m,_3t);});break;case 6:return new F(function(){return _4(_3n,_3t);});break;case 7:return new F(function(){return _4(_3o,_3t);});break;case 8:return new F(function(){return _4(_3p,_3t);});break;case 9:return new F(function(){return _4(_3q,_3t);});break;case 10:return new F(function(){return _4(_3a,_3t);});break;case 11:return new F(function(){return _4(_3b,_3t);});break;case 12:return new F(function(){return _4(_3c,_3t);});break;case 13:return new F(function(){return _4(_3d,_3t);});break;case 14:return new F(function(){return _4(_3e,_3t);});break;case 15:return new F(function(){return _4(_3f,_3t);});break;case 16:return new F(function(){return _4(_3g,_3t);});break;case 17:return new F(function(){return _4(_3h,_3t);});break;default:return new F(function(){return _4(_3i,_3t);});}},_3u=[0,125],_3v=new T(function(){return B(unCStr("{handle: "));}),_3w=function(_3x,_3y,_3z,_3A,_3B,_3C){var _3D=new T(function(){var _3E=new T(function(){return B(_3r(_3y,new T(function(){var _3F=E(_3A);return _3F[0]==0?E(_3C):B(_4(_37,new T(function(){return B(_4(_3F,[1,_36,_3C]));})));})));}),_3G=E(_3z);return _3G[0]==0?E(_3E):B(_4(_3G,new T(function(){return B(_4(_35,_3E));})));}),_3H=E(_3B);if(!_3H[0]){var _3I=E(_3x);if(!_3I[0]){return E(_3D);}else{var _3J=E(_3I[1]);return _3J[0]==0?B(_4(_3v,new T(function(){return B(_4(_3J[1],[1,_3u,new T(function(){return B(_4(_35,_3D));})]));}))):B(_4(_3v,new T(function(){return B(_4(_3J[1],[1,_3u,new T(function(){return B(_4(_35,_3D));})]));})));}}else{return new F(function(){return _4(_3H[1],new T(function(){return B(_4(_35,_3D));}));});}},_3K=function(_3L){var _3M=E(_3L);return new F(function(){return _3w(_3M[1],_3M[2],_3M[3],_3M[4],_3M[6],_N);});},_3N=function(_3O,_3P){var _3Q=E(_3O);return new F(function(){return _3w(_3Q[1],_3Q[2],_3Q[3],_3Q[4],_3Q[6],_3P);});},_3R=function(_3S,_3T){return new F(function(){return _1M(_3N,_3S,_3T);});},_3U=function(_3V,_3W,_3X){var _3Y=E(_3W);return new F(function(){return _3w(_3Y[1],_3Y[2],_3Y[3],_3Y[4],_3Y[6],_3X);});},_3Z=[0,_3U,_3K,_3R],_40=new T(function(){return [0,_30,_3Z,_41,_32];}),_41=function(_42){return [0,_40,_42];},_43=[0],_44=7,_45=function(_46){return [0,_43,_44,_N,_46,_43,_43];},_47=function(_48,_){return new F(function(){return die(new T(function(){return B(_41(new T(function(){return B(_45(_48));})));}));});},_49=function(_4a,_){return new F(function(){return _47(_4a,_);});},_4b=[0,114],_4c=[1,_4b,_N],_4d=new T(function(){return B(_f(0,6,_N));}),_4e=new T(function(){return B(unCStr("cx"));}),_4f=new T(function(){return B(unCStr("cy"));}),_4g=function(_4h,_4i){if(_4h<=_4i){var _4j=function(_4k){return [1,[0,_4k],new T(function(){if(_4k!=_4i){var _4l=B(_4j(_4k+1|0));}else{var _4l=[0];}return _4l;})];};return new F(function(){return _4j(_4h);});}else{return [0];}},_4m=new T(function(){return B(_4g(0,2147483647));}),_4n=new T(function(){return B(unCStr("circle"));}),_4o=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_4p=new T(function(){return B(unCStr("board"));}),_4q=function(_4r,_4s,_4t,_){if(_4t>0){var _4u=function(_4v,_4w,_){var _4x=jsFind(toJSStr(E(_4p))),_4y=_4x,_4z=E(_4y);if(!_4z[0]){var _4A=B(_49(_2Q,_)),_4B=_4A;return new F(function(){return A(_4w,[_]);});}else{var _4C=jsCreateElemNS(toJSStr(E(_4o)),toJSStr(E(_4n))),_4D=_4C,_4E=[0,_4D],_4F=B(A(_H,[_O,_4E,_4c,_4d,_])),_4G=_4F,_4H=new T(function(){return E(_4r)==0?[3,_4v]:[2,_4v];}),_4I=new T(function(){var _4J=B(_2C(_4H));return [0,_4J[1],_4J[2]];}),_4K=B(A(_H,[_O,_4E,_4e,new T(function(){return B(_f(0,E(E(_4I)[1])[1],_N));}),_])),_4L=_4K,_4M=B(A(_H,[_O,_4E,_4f,new T(function(){return B(_f(0,E(E(_4I)[2])[1],_N));}),_])),_4N=_4M,_4O=B(A(_11,[_4E,_4s,_4H,_4r,_])),_4P=_4O,_4Q=jsAppendChild(_4D,E(_4z[1])[1]);return new F(function(){return A(_4w,[_]);});}},_4R=function(_4S,_4T,_){var _4U=E(_4S);if(!_4U[0]){return _G;}else{var _4V=_4U[1];if(_4T>1){return new F(function(){return _4u(_4V,function(_){return new F(function(){return _4R(_4U[2],_4T-1|0,_);});},_);});}else{return new F(function(){return _4u(_4V,_2R,_);});}}};return new F(function(){return _4R(_4m,_4t,_);});}else{return _G;}},_4W=0,_4X=1,_4Y=[0,0],_4Z=function(_50,_51){while(1){var _52=E(_50);if(!_52[0]){return E(_51);}else{_50=_52[2];var _53=[1,_52[1],_51];_51=_53;continue;}}},_54=[0,2],_55=[1,_4Y,_N],_56=[1,_4Y,_55],_57=[1,_4Y,_56],_58=[1,_4Y,_57],_59=[1,_4Y,_58],_5a=[0,5],_5b=[1,_5a,_59],_5c=[1,_4Y,_5b],_5d=[0,3],_5e=[1,_5d,_5c],_5f=[1,_4Y,_5e],_5g=[1,_4Y,_5f],_5h=[1,_4Y,_5g],_5i=[1,_4Y,_5h],_5j=[1,_5a,_5i],_5k=[1,_4Y,_5j],_5l=[1,_4Y,_5k],_5m=[1,_4Y,_5l],_5n=[1,_4Y,_5m],_5o=[1,_4Y,_5n],_5p=[1,_4Y,_5o],_5q=[1,_4Y,_5p],_5r=[1,_4Y,_5q],_5s=[1,_4Y,_5r],_5t=[1,_4Y,_5s],_5u=[1,_54,_5t],_5v=function(_5w){var _5x=E(_5w);return _5x[0]==0?[0]:[1,[0,_4X,_5x[1]],new T(function(){return B(_5v(_5x[2]));})];},_5y=new T(function(){return B(_5v(_5u));}),_5z=new T(function(){return B(_4Z(_5y,_N));}),_5A=new T(function(){return B(_2u("main.hs:(239,20)-(240,55)|function whiteOrBlack"));}),_5B=function(_5C,_5D){var _5E=E(_5C);if(!_5E[0]){return [0];}else{var _5F=E(_5D);return _5F[0]==0?[0]:[1,new T(function(){var _5G=E(_5F[1]);if(!E(_5G[1])){var _5H=E(_5A);}else{if(!E(E(_5G[2])[1])){var _5I=E(_5E[1]),_5J=E(_5I[1])==0?E(_5I):[0,_4W,_5I[2]];}else{var _5J=E(_5G);}var _5K=_5J,_5H=_5K;}var _5L=_5H;return _5L;}),new T(function(){return B(_5B(_5E[2],_5F[2]));})];}},_5M=new T(function(){return B(_5B(_5z,_5y));}),_5N=function(_5O,_5P){while(1){var _5Q=E(_5O);if(!_5Q[0]){return E(_5P);}else{_5O=_5Q[2];var _5R=_5P+E(_5Q[1])[1]|0;_5P=_5R;continue;}}},_5S=new T(function(){return [0,B(_5N(_5u,0))];}),_5T=[0,_5M,_5S,_5S,_4Y,_4Y,_4X,_4X],_5U=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_5V=new T(function(){return B(err(_5U));}),_5W=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_5X=new T(function(){return B(err(_5W));}),_5Y=function(_5Z,_60){while(1){var _61=E(_5Z);if(!_61[0]){return E(_5X);}else{var _62=E(_60);if(!_62){return E(_61[1]);}else{_5Z=_61[2];_60=_62-1|0;continue;}}}},_63=new T(function(){return B(unCStr(": empty list"));}),_64=new T(function(){return B(unCStr("Prelude."));}),_65=function(_66){return new F(function(){return err(B(_4(_64,new T(function(){return B(_4(_66,_63));}))));});},_67=new T(function(){return B(unCStr("head"));}),_68=new T(function(){return B(_65(_67));}),_69=function(_6a,_6b,_6c,_){var _6d=jsElemsByClassName(toJSStr(B(_X(_R,B(_t(0,_6a,_N)))))),_6e=_6d,_6f=E(_6e);if(!_6f[0]){return E(_68);}else{var _6g=E(_6f[1]),_6h=B(_2C(_6b)),_6i=animateCircle_ffi(_6g[1],E(_6h[1])[1],E(_6h[2])[1],300);return new F(function(){return A(_11,[_6g,_6c,_6b,_6c,_]);});}},_6j=function(_6k,_6l){while(1){var _6m=E(_6k);if(!_6m){return E(_6l);}else{var _6n=E(_6l);if(!_6n[0]){return [0];}else{_6k=_6m-1|0;_6l=_6n[2];continue;}}}},_6o=function(_6p,_6q){var _6r=function(_6s,_6t){while(1){var _6u=(function(_6v,_6w){var _6x=E(_6w);if(!_6x[0]){return [0];}else{var _6y=_6x[2];if(!B(A(_6p,[_6x[1]]))){var _6z=_6v+1|0;_6t=_6y;_6s=_6z;return null;}else{return [1,[0,_6v],new T(function(){return B(_6r(_6v+1|0,_6y));})];}}})(_6s,_6t);if(_6u!=null){return _6u;}}};return new F(function(){return _6r(0,_6q);});},_6A=function(_6B,_6C,_6D,_6E){var _6F=E(_6D);if(!_6F[0]){return E(_6C);}else{var _6G=E(_6E);if(!_6G[0]){return E(_6C);}else{return new F(function(){return A(_6B,[_6F[1],_6G[1],new T(function(){return B(_6A(_6B,_6C,_6F[2],_6G[2]));})]);});}}},_6H=function(_6I){return new F(function(){return fromJSStr(E(_6I)[1]);});},_6J=function(_6K){var _6L=E(_6K);return E(_6L[1])==95?E(_W):E(_6L);},_6M=new T(function(){return [0,B(_2x(210,2))];}),_6N=new T(function(){return B(_2u("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_6O=function(_6P,_6Q){while(1){var _6R=(function(_6S,_6T){var _6U=E(_6S);switch(_6U[0]){case 0:var _6V=E(_6T);if(!_6V[0]){return [0];}else{_6P=B(A(_6U[1],[_6V[1]]));_6Q=_6V[2];return null;}break;case 1:var _6W=B(A(_6U[1],[_6T])),_6X=_6T;_6P=_6W;_6Q=_6X;return null;case 2:return [0];case 3:return [1,[0,_6U[1],_6T],new T(function(){return B(_6O(_6U[2],_6T));})];default:return E(_6U[1]);}})(_6P,_6Q);if(_6R!=null){return _6R;}}},_6Y=function(_6Z,_70){var _71=new T(function(){var _72=E(_70);if(_72[0]==3){var _73=[3,_72[1],new T(function(){return B(_6Y(_6Z,_72[2]));})];}else{var _74=E(_6Z);if(_74[0]==2){var _75=E(_72);}else{var _76=E(_72);if(_76[0]==2){var _77=E(_74);}else{var _78=new T(function(){var _79=E(_76);if(_79[0]==4){var _7a=[1,function(_7b){return [4,new T(function(){return B(_4(B(_6O(_74,_7b)),_79[1]));})];}];}else{var _7c=E(_74);if(_7c[0]==1){var _7d=_7c[1],_7e=E(_79);if(!_7e[0]){var _7f=[1,function(_7g){return new F(function(){return _6Y(B(A(_7d,[_7g])),_7e);});}];}else{var _7f=[1,function(_7h){return new F(function(){return _6Y(B(A(_7d,[_7h])),new T(function(){return B(A(_7e[1],[_7h]));}));});}];}var _7i=_7f;}else{var _7j=E(_79);if(!_7j[0]){var _7k=E(_6N);}else{var _7k=[1,function(_7l){return new F(function(){return _6Y(_7c,new T(function(){return B(A(_7j[1],[_7l]));}));});}];}var _7i=_7k;}var _7a=_7i;}return _7a;}),_7m=E(_74);switch(_7m[0]){case 1:var _7n=E(_76);if(_7n[0]==4){var _7o=[1,function(_7p){return [4,new T(function(){return B(_4(B(_6O(B(A(_7m[1],[_7p])),_7p)),_7n[1]));})];}];}else{var _7o=E(_78);}var _7q=_7o;break;case 4:var _7r=_7m[1],_7s=E(_76);switch(_7s[0]){case 0:var _7t=[1,function(_7u){return [4,new T(function(){return B(_4(_7r,new T(function(){return B(_6O(_7s,_7u));})));})];}];break;case 1:var _7t=[1,function(_7v){return [4,new T(function(){return B(_4(_7r,new T(function(){return B(_6O(B(A(_7s[1],[_7v])),_7v));})));})];}];break;default:var _7t=[4,new T(function(){return B(_4(_7r,_7s[1]));})];}var _7q=_7t;break;default:var _7q=E(_78);}var _77=_7q;}var _75=_77;}var _73=_75;}return _73;}),_7w=E(_6Z);switch(_7w[0]){case 0:var _7x=E(_70);return _7x[0]==0?[0,function(_7y){return new F(function(){return _6Y(B(A(_7w[1],[_7y])),new T(function(){return B(A(_7x[1],[_7y]));}));});}]:E(_71);case 3:return [3,_7w[1],new T(function(){return B(_6Y(_7w[2],_70));})];default:return E(_71);}},_7z=function(_7A,_7B){return E(_7A)[1]!=E(_7B)[1];},_7C=function(_7D,_7E){return E(_7D)[1]==E(_7E)[1];},_7F=[0,_7C,_7z],_7G=function(_7H){return E(E(_7H)[1]);},_7I=function(_7J,_7K,_7L){while(1){var _7M=E(_7K);if(!_7M[0]){return E(_7L)[0]==0?true:false;}else{var _7N=E(_7L);if(!_7N[0]){return false;}else{if(!B(A(_7G,[_7J,_7M[1],_7N[1]]))){return false;}else{_7K=_7M[2];_7L=_7N[2];continue;}}}}},_7O=function(_7P,_7Q,_7R){return !B(_7I(_7P,_7Q,_7R))?true:false;},_7S=function(_7T){return [0,function(_7U,_7V){return new F(function(){return _7I(_7T,_7U,_7V);});},function(_7U,_7V){return new F(function(){return _7O(_7T,_7U,_7V);});}];},_7W=new T(function(){return B(_7S(_7F));}),_7X=function(_7Y,_7Z){var _80=E(_7Y);switch(_80[0]){case 0:return [0,function(_81){return new F(function(){return _7X(B(A(_80[1],[_81])),_7Z);});}];case 1:return [1,function(_82){return new F(function(){return _7X(B(A(_80[1],[_82])),_7Z);});}];case 2:return [2];case 3:return new F(function(){return _6Y(B(A(_7Z,[_80[1]])),new T(function(){return B(_7X(_80[2],_7Z));}));});break;default:var _83=function(_84){var _85=E(_84);if(!_85[0]){return [0];}else{var _86=E(_85[1]);return new F(function(){return _4(B(_6O(B(A(_7Z,[_86[1]])),_86[2])),new T(function(){return B(_83(_85[2]));}));});}},_87=B(_83(_80[1]));return _87[0]==0?[2]:[4,_87];}},_88=[2],_89=function(_8a){return [3,_8a,_88];},_8b=function(_8c,_8d){var _8e=E(_8c);if(!_8e){return new F(function(){return A(_8d,[_G]);});}else{return [0,function(_8f){return E(new T(function(){return B(_8b(_8e-1|0,_8d));}));}];}},_8g=function(_8h,_8i,_8j){return [1,function(_8k){return new F(function(){return A(function(_8l,_8m,_8n){while(1){var _8o=(function(_8p,_8q,_8r){var _8s=E(_8p);switch(_8s[0]){case 0:var _8t=E(_8q);if(!_8t[0]){return E(_8i);}else{_8l=B(A(_8s[1],[_8t[1]]));_8m=_8t[2];var _8u=_8r+1|0;_8n=_8u;return null;}break;case 1:var _8v=B(A(_8s[1],[_8q])),_8w=_8q,_8u=_8r;_8l=_8v;_8m=_8w;_8n=_8u;return null;case 2:return E(_8i);case 3:return function(_8x){return new F(function(){return _8b(_8r,function(_8y){return E(new T(function(){return B(_7X(_8s,_8x));}));});});};default:return function(_8z){return new F(function(){return _7X(_8s,_8z);});};}})(_8l,_8m,_8n);if(_8o!=null){return _8o;}}},[new T(function(){return B(A(_8h,[_89]));}),_8k,0,_8j]);});}];},_8A=[6],_8B=new T(function(){return B(unCStr("valDig: Bad base"));}),_8C=new T(function(){return B(err(_8B));}),_8D=function(_8E,_8F){var _8G=function(_8H,_8I){var _8J=E(_8H);if(!_8J[0]){return function(_8K){return new F(function(){return A(_8K,[new T(function(){return B(A(_8I,[_N]));})]);});};}else{var _8L=E(_8J[1])[1],_8M=function(_8N){return function(_8O){return [0,function(_8P){return E(new T(function(){return B(A(new T(function(){return B(_8G(_8J[2],function(_8Q){return new F(function(){return A(_8I,[[1,_8N,_8Q]]);});}));}),[_8O]));}));}];};};switch(E(E(_8E)[1])){case 8:if(48>_8L){return function(_8R){return new F(function(){return A(_8R,[new T(function(){return B(A(_8I,[_N]));})]);});};}else{if(_8L>55){return function(_8S){return new F(function(){return A(_8S,[new T(function(){return B(A(_8I,[_N]));})]);});};}else{return new F(function(){return _8M([0,_8L-48|0]);});}}break;case 10:if(48>_8L){return function(_8T){return new F(function(){return A(_8T,[new T(function(){return B(A(_8I,[_N]));})]);});};}else{if(_8L>57){return function(_8U){return new F(function(){return A(_8U,[new T(function(){return B(A(_8I,[_N]));})]);});};}else{return new F(function(){return _8M([0,_8L-48|0]);});}}break;case 16:var _8V=new T(function(){if(97>_8L){if(65>_8L){var _8W=[0];}else{if(_8L>70){var _8X=[0];}else{var _8X=[1,[0,(_8L-65|0)+10|0]];}var _8W=_8X;}var _8Y=_8W;}else{if(_8L>102){if(65>_8L){var _8Z=[0];}else{if(_8L>70){var _90=[0];}else{var _90=[1,[0,(_8L-65|0)+10|0]];}var _8Z=_90;}var _91=_8Z;}else{var _91=[1,[0,(_8L-97|0)+10|0]];}var _8Y=_91;}return _8Y;});if(48>_8L){var _92=E(_8V);if(!_92[0]){return function(_93){return new F(function(){return A(_93,[new T(function(){return B(A(_8I,[_N]));})]);});};}else{return new F(function(){return _8M(_92[1]);});}}else{if(_8L>57){var _94=E(_8V);if(!_94[0]){return function(_95){return new F(function(){return A(_95,[new T(function(){return B(A(_8I,[_N]));})]);});};}else{return new F(function(){return _8M(_94[1]);});}}else{return new F(function(){return _8M([0,_8L-48|0]);});}}break;default:return E(_8C);}}};return [1,function(_96){return new F(function(){return A(_8G,[_96,_O,function(_97){var _98=E(_97);return _98[0]==0?[2]:B(A(_8F,[_98]));}]);});}];},_99=[0,10],_9a=[0,1],_9b=[0,2147483647],_9c=function(_9d,_9e){while(1){var _9f=E(_9d);if(!_9f[0]){var _9g=_9f[1],_9h=E(_9e);if(!_9h[0]){var _9i=_9h[1],_9j=addC(_9g,_9i);if(!E(_9j[2])){return [0,_9j[1]];}else{_9d=[1,I_fromInt(_9g)];_9e=[1,I_fromInt(_9i)];continue;}}else{_9d=[1,I_fromInt(_9g)];_9e=_9h;continue;}}else{var _9k=E(_9e);if(!_9k[0]){_9d=_9f;_9e=[1,I_fromInt(_9k[1])];continue;}else{return [1,I_add(_9f[1],_9k[1])];}}}},_9l=new T(function(){return B(_9c(_9b,_9a));}),_9m=function(_9n){var _9o=E(_9n);if(!_9o[0]){var _9p=E(_9o[1]);return _9p==(-2147483648)?E(_9l):[0, -_9p];}else{return [1,I_negate(_9o[1])];}},_9q=[0,10],_9r=[0,0],_9s=function(_9t){return [0,_9t];},_9u=function(_9v,_9w){while(1){var _9x=E(_9v);if(!_9x[0]){var _9y=_9x[1],_9z=E(_9w);if(!_9z[0]){var _9A=_9z[1];if(!(imul(_9y,_9A)|0)){return [0,imul(_9y,_9A)|0];}else{_9v=[1,I_fromInt(_9y)];_9w=[1,I_fromInt(_9A)];continue;}}else{_9v=[1,I_fromInt(_9y)];_9w=_9z;continue;}}else{var _9B=E(_9w);if(!_9B[0]){_9v=_9x;_9w=[1,I_fromInt(_9B[1])];continue;}else{return [1,I_mul(_9x[1],_9B[1])];}}}},_9C=function(_9D,_9E,_9F){while(1){var _9G=E(_9F);if(!_9G[0]){return E(_9E);}else{var _9H=B(_9c(B(_9u(_9E,_9D)),B(_9s(E(_9G[1])[1]))));_9F=_9G[2];_9E=_9H;continue;}}},_9I=function(_9J){var _9K=new T(function(){return B(_6Y(B(_6Y([0,function(_9L){if(E(E(_9L)[1])==45){return new F(function(){return _8D(_99,function(_9M){return new F(function(){return A(_9J,[[1,new T(function(){return B(_9m(B(_9C(_9q,_9r,_9M))));})]]);});});});}else{return [2];}}],[0,function(_9N){if(E(E(_9N)[1])==43){return new F(function(){return _8D(_99,function(_9O){return new F(function(){return A(_9J,[[1,new T(function(){return B(_9C(_9q,_9r,_9O));})]]);});});});}else{return [2];}}])),new T(function(){return B(_8D(_99,function(_9P){return new F(function(){return A(_9J,[[1,new T(function(){return B(_9C(_9q,_9r,_9P));})]]);});}));})));});return new F(function(){return _6Y([0,function(_9Q){return E(E(_9Q)[1])==101?E(_9K):[2];}],[0,function(_9R){return E(E(_9R)[1])==69?E(_9K):[2];}]);});},_9S=function(_9T){return new F(function(){return A(_9T,[_43]);});},_9U=function(_9V){return new F(function(){return A(_9V,[_43]);});},_9W=function(_9X){return [0,function(_9Y){return E(E(_9Y)[1])==46?E(new T(function(){return B(_8D(_99,function(_9Z){return new F(function(){return A(_9X,[[1,_9Z]]);});}));})):[2];}];},_a0=function(_a1){return new F(function(){return _8D(_99,function(_a2){return new F(function(){return _8g(_9W,_9S,function(_a3){return new F(function(){return _8g(_9I,_9U,function(_a4){return new F(function(){return A(_a1,[[5,[1,_a2,_a3,_a4]]]);});});});});});});});},_a5=function(_a6,_a7,_a8){while(1){var _a9=E(_a8);if(!_a9[0]){return false;}else{if(!B(A(_7G,[_a6,_a7,_a9[1]]))){_a8=_a9[2];continue;}else{return true;}}}},_aa=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_ab=function(_ac){return new F(function(){return _a5(_7F,_ac,_aa);});},_ad=[0,8],_ae=[0,16],_af=function(_ag){return [0,function(_ah){return E(E(_ah)[1])==48?E([0,function(_ai){switch(E(E(_ai)[1])){case 79:return E(new T(function(){return B(_8D(_ad,function(_aj){return new F(function(){return A(_ag,[[5,[0,_ad,_aj]]]);});}));}));case 88:return E(new T(function(){return B(_8D(_ae,function(_ak){return new F(function(){return A(_ag,[[5,[0,_ae,_ak]]]);});}));}));case 111:return E(new T(function(){return B(_8D(_ad,function(_al){return new F(function(){return A(_ag,[[5,[0,_ad,_al]]]);});}));}));case 120:return E(new T(function(){return B(_8D(_ae,function(_am){return new F(function(){return A(_ag,[[5,[0,_ae,_am]]]);});}));}));default:return [2];}}]):[2];}];},_an=false,_ao=true,_ap=function(_aq){return [0,function(_ar){switch(E(E(_ar)[1])){case 79:return E(new T(function(){return B(A(_aq,[_ad]));}));case 88:return E(new T(function(){return B(A(_aq,[_ae]));}));case 111:return E(new T(function(){return B(A(_aq,[_ad]));}));case 120:return E(new T(function(){return B(A(_aq,[_ae]));}));default:return [2];}}];},_as=function(_at){return new F(function(){return A(_at,[_99]);});},_au=function(_av){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_f(9,_av,_N));}))));});},_aw=function(_ax){var _ay=E(_ax);return _ay[0]==0?E(_ay[1]):I_toInt(_ay[1]);},_az=function(_aA,_aB){var _aC=E(_aA);if(!_aC[0]){var _aD=_aC[1],_aE=E(_aB);return _aE[0]==0?_aD<=_aE[1]:I_compareInt(_aE[1],_aD)>=0;}else{var _aF=_aC[1],_aG=E(_aB);return _aG[0]==0?I_compareInt(_aF,_aG[1])<=0:I_compare(_aF,_aG[1])<=0;}},_aH=function(_aI){return [2];},_aJ=function(_aK){var _aL=E(_aK);if(!_aL[0]){return E(_aH);}else{var _aM=_aL[1],_aN=E(_aL[2]);return _aN[0]==0?E(_aM):function(_aO){return new F(function(){return _6Y(B(A(_aM,[_aO])),new T(function(){return B(A(new T(function(){return B(_aJ(_aN));}),[_aO]));}));});};}},_aP=new T(function(){return B(unCStr("NUL"));}),_aQ=function(_aR){return [2];},_aS=function(_aT){return new F(function(){return _aQ(_aT);});},_aU=function(_aV,_aW){var _aX=function(_aY,_aZ){var _b0=E(_aY);if(!_b0[0]){return function(_b1){return new F(function(){return A(_b1,[_aV]);});};}else{var _b2=E(_aZ);return _b2[0]==0?E(_aQ):E(_b0[1])[1]!=E(_b2[1])[1]?E(_aS):function(_b3){return [0,function(_b4){return E(new T(function(){return B(A(new T(function(){return B(_aX(_b0[2],_b2[2]));}),[_b3]));}));}];};}};return [1,function(_b5){return new F(function(){return A(_aX,[_aV,_b5,_aW]);});}];},_b6=[0,0],_b7=function(_b8){return new F(function(){return _aU(_aP,function(_b9){return E(new T(function(){return B(A(_b8,[_b6]));}));});});},_ba=new T(function(){return B(unCStr("STX"));}),_bb=[0,2],_bc=function(_bd){return new F(function(){return _aU(_ba,function(_be){return E(new T(function(){return B(A(_bd,[_bb]));}));});});},_bf=new T(function(){return B(unCStr("ETX"));}),_bg=[0,3],_bh=function(_bi){return new F(function(){return _aU(_bf,function(_bj){return E(new T(function(){return B(A(_bi,[_bg]));}));});});},_bk=new T(function(){return B(unCStr("EOT"));}),_bl=[0,4],_bm=function(_bn){return new F(function(){return _aU(_bk,function(_bo){return E(new T(function(){return B(A(_bn,[_bl]));}));});});},_bp=new T(function(){return B(unCStr("ENQ"));}),_bq=[0,5],_br=function(_bs){return new F(function(){return _aU(_bp,function(_bt){return E(new T(function(){return B(A(_bs,[_bq]));}));});});},_bu=new T(function(){return B(unCStr("ACK"));}),_bv=[0,6],_bw=function(_bx){return new F(function(){return _aU(_bu,function(_by){return E(new T(function(){return B(A(_bx,[_bv]));}));});});},_bz=new T(function(){return B(unCStr("BEL"));}),_bA=[0,7],_bB=function(_bC){return new F(function(){return _aU(_bz,function(_bD){return E(new T(function(){return B(A(_bC,[_bA]));}));});});},_bE=new T(function(){return B(unCStr("BS"));}),_bF=[0,8],_bG=function(_bH){return new F(function(){return _aU(_bE,function(_bI){return E(new T(function(){return B(A(_bH,[_bF]));}));});});},_bJ=new T(function(){return B(unCStr("HT"));}),_bK=[0,9],_bL=function(_bM){return new F(function(){return _aU(_bJ,function(_bN){return E(new T(function(){return B(A(_bM,[_bK]));}));});});},_bO=new T(function(){return B(unCStr("LF"));}),_bP=[0,10],_bQ=function(_bR){return new F(function(){return _aU(_bO,function(_bS){return E(new T(function(){return B(A(_bR,[_bP]));}));});});},_bT=new T(function(){return B(unCStr("VT"));}),_bU=[0,11],_bV=function(_bW){return new F(function(){return _aU(_bT,function(_bX){return E(new T(function(){return B(A(_bW,[_bU]));}));});});},_bY=new T(function(){return B(unCStr("FF"));}),_bZ=[0,12],_c0=function(_c1){return new F(function(){return _aU(_bY,function(_c2){return E(new T(function(){return B(A(_c1,[_bZ]));}));});});},_c3=new T(function(){return B(unCStr("CR"));}),_c4=[0,13],_c5=function(_c6){return new F(function(){return _aU(_c3,function(_c7){return E(new T(function(){return B(A(_c6,[_c4]));}));});});},_c8=new T(function(){return B(unCStr("SI"));}),_c9=[0,15],_ca=function(_cb){return new F(function(){return _aU(_c8,function(_cc){return E(new T(function(){return B(A(_cb,[_c9]));}));});});},_cd=new T(function(){return B(unCStr("DLE"));}),_ce=[0,16],_cf=function(_cg){return new F(function(){return _aU(_cd,function(_ch){return E(new T(function(){return B(A(_cg,[_ce]));}));});});},_ci=new T(function(){return B(unCStr("DC1"));}),_cj=[0,17],_ck=function(_cl){return new F(function(){return _aU(_ci,function(_cm){return E(new T(function(){return B(A(_cl,[_cj]));}));});});},_cn=new T(function(){return B(unCStr("DC2"));}),_co=[0,18],_cp=function(_cq){return new F(function(){return _aU(_cn,function(_cr){return E(new T(function(){return B(A(_cq,[_co]));}));});});},_cs=new T(function(){return B(unCStr("DC3"));}),_ct=[0,19],_cu=function(_cv){return new F(function(){return _aU(_cs,function(_cw){return E(new T(function(){return B(A(_cv,[_ct]));}));});});},_cx=new T(function(){return B(unCStr("DC4"));}),_cy=[0,20],_cz=function(_cA){return new F(function(){return _aU(_cx,function(_cB){return E(new T(function(){return B(A(_cA,[_cy]));}));});});},_cC=new T(function(){return B(unCStr("NAK"));}),_cD=[0,21],_cE=function(_cF){return new F(function(){return _aU(_cC,function(_cG){return E(new T(function(){return B(A(_cF,[_cD]));}));});});},_cH=new T(function(){return B(unCStr("SYN"));}),_cI=[0,22],_cJ=function(_cK){return new F(function(){return _aU(_cH,function(_cL){return E(new T(function(){return B(A(_cK,[_cI]));}));});});},_cM=new T(function(){return B(unCStr("ETB"));}),_cN=[0,23],_cO=function(_cP){return new F(function(){return _aU(_cM,function(_cQ){return E(new T(function(){return B(A(_cP,[_cN]));}));});});},_cR=new T(function(){return B(unCStr("CAN"));}),_cS=[0,24],_cT=function(_cU){return new F(function(){return _aU(_cR,function(_cV){return E(new T(function(){return B(A(_cU,[_cS]));}));});});},_cW=new T(function(){return B(unCStr("EM"));}),_cX=[0,25],_cY=function(_cZ){return new F(function(){return _aU(_cW,function(_d0){return E(new T(function(){return B(A(_cZ,[_cX]));}));});});},_d1=new T(function(){return B(unCStr("SUB"));}),_d2=[0,26],_d3=function(_d4){return new F(function(){return _aU(_d1,function(_d5){return E(new T(function(){return B(A(_d4,[_d2]));}));});});},_d6=new T(function(){return B(unCStr("ESC"));}),_d7=[0,27],_d8=function(_d9){return new F(function(){return _aU(_d6,function(_da){return E(new T(function(){return B(A(_d9,[_d7]));}));});});},_db=new T(function(){return B(unCStr("FS"));}),_dc=[0,28],_dd=function(_de){return new F(function(){return _aU(_db,function(_df){return E(new T(function(){return B(A(_de,[_dc]));}));});});},_dg=new T(function(){return B(unCStr("GS"));}),_dh=[0,29],_di=function(_dj){return new F(function(){return _aU(_dg,function(_dk){return E(new T(function(){return B(A(_dj,[_dh]));}));});});},_dl=new T(function(){return B(unCStr("RS"));}),_dm=[0,30],_dn=function(_do){return new F(function(){return _aU(_dl,function(_dp){return E(new T(function(){return B(A(_do,[_dm]));}));});});},_dq=new T(function(){return B(unCStr("US"));}),_dr=[0,31],_ds=function(_dt){return new F(function(){return _aU(_dq,function(_du){return E(new T(function(){return B(A(_dt,[_dr]));}));});});},_dv=new T(function(){return B(unCStr("SP"));}),_dw=[0,32],_dx=function(_dy){return new F(function(){return _aU(_dv,function(_dz){return E(new T(function(){return B(A(_dy,[_dw]));}));});});},_dA=new T(function(){return B(unCStr("DEL"));}),_dB=[0,127],_dC=function(_dD){return new F(function(){return _aU(_dA,function(_dE){return E(new T(function(){return B(A(_dD,[_dB]));}));});});},_dF=[1,_dC,_N],_dG=[1,_dx,_dF],_dH=[1,_ds,_dG],_dI=[1,_dn,_dH],_dJ=[1,_di,_dI],_dK=[1,_dd,_dJ],_dL=[1,_d8,_dK],_dM=[1,_d3,_dL],_dN=[1,_cY,_dM],_dO=[1,_cT,_dN],_dP=[1,_cO,_dO],_dQ=[1,_cJ,_dP],_dR=[1,_cE,_dQ],_dS=[1,_cz,_dR],_dT=[1,_cu,_dS],_dU=[1,_cp,_dT],_dV=[1,_ck,_dU],_dW=[1,_cf,_dV],_dX=[1,_ca,_dW],_dY=[1,_c5,_dX],_dZ=[1,_c0,_dY],_e0=[1,_bV,_dZ],_e1=[1,_bQ,_e0],_e2=[1,_bL,_e1],_e3=[1,_bG,_e2],_e4=[1,_bB,_e3],_e5=[1,_bw,_e4],_e6=[1,_br,_e5],_e7=[1,_bm,_e6],_e8=[1,_bh,_e7],_e9=[1,_bc,_e8],_ea=[1,_b7,_e9],_eb=new T(function(){return B(unCStr("SOH"));}),_ec=[0,1],_ed=function(_ee){return new F(function(){return _aU(_eb,function(_ef){return E(new T(function(){return B(A(_ee,[_ec]));}));});});},_eg=new T(function(){return B(unCStr("SO"));}),_eh=[0,14],_ei=function(_ej){return new F(function(){return _aU(_eg,function(_ek){return E(new T(function(){return B(A(_ej,[_eh]));}));});});},_el=function(_em){return new F(function(){return _8g(_ed,_ei,_em);});},_en=[1,_el,_ea],_eo=new T(function(){return B(_aJ(_en));}),_ep=[0,1114111],_eq=[0,34],_er=[0,_eq,_ao],_es=[0,39],_et=[0,_es,_ao],_eu=[0,92],_ev=[0,_eu,_ao],_ew=[0,_bA,_ao],_ex=[0,_bF,_ao],_ey=[0,_bZ,_ao],_ez=[0,_bP,_ao],_eA=[0,_c4,_ao],_eB=[0,_bK,_ao],_eC=[0,_bU,_ao],_eD=[0,_b6,_ao],_eE=[0,_ec,_ao],_eF=[0,_bb,_ao],_eG=[0,_bg,_ao],_eH=[0,_bl,_ao],_eI=[0,_bq,_ao],_eJ=[0,_bv,_ao],_eK=[0,_bA,_ao],_eL=[0,_bF,_ao],_eM=[0,_bK,_ao],_eN=[0,_bP,_ao],_eO=[0,_bU,_ao],_eP=[0,_bZ,_ao],_eQ=[0,_c4,_ao],_eR=[0,_eh,_ao],_eS=[0,_c9,_ao],_eT=[0,_ce,_ao],_eU=[0,_cj,_ao],_eV=[0,_co,_ao],_eW=[0,_ct,_ao],_eX=[0,_cy,_ao],_eY=[0,_cD,_ao],_eZ=[0,_cI,_ao],_f0=[0,_cN,_ao],_f1=[0,_cS,_ao],_f2=[0,_cX,_ao],_f3=[0,_d2,_ao],_f4=[0,_d7,_ao],_f5=[0,_dc,_ao],_f6=[0,_dh,_ao],_f7=[0,_dm,_ao],_f8=[0,_dr,_ao],_f9=function(_fa){return new F(function(){return _6Y([0,function(_fb){switch(E(E(_fb)[1])){case 34:return E(new T(function(){return B(A(_fa,[_er]));}));case 39:return E(new T(function(){return B(A(_fa,[_et]));}));case 92:return E(new T(function(){return B(A(_fa,[_ev]));}));case 97:return E(new T(function(){return B(A(_fa,[_ew]));}));case 98:return E(new T(function(){return B(A(_fa,[_ex]));}));case 102:return E(new T(function(){return B(A(_fa,[_ey]));}));case 110:return E(new T(function(){return B(A(_fa,[_ez]));}));case 114:return E(new T(function(){return B(A(_fa,[_eA]));}));case 116:return E(new T(function(){return B(A(_fa,[_eB]));}));case 118:return E(new T(function(){return B(A(_fa,[_eC]));}));default:return [2];}}],new T(function(){return B(_6Y(B(_8g(_ap,_as,function(_fc){return new F(function(){return _8D(_fc,function(_fd){var _fe=B(_9C(new T(function(){return B(_9s(E(_fc)[1]));}),_9r,_fd));return !B(_az(_fe,_ep))?[2]:B(A(_fa,[[0,new T(function(){var _ff=B(_aw(_fe));if(_ff>>>0>1114111){var _fg=B(_au(_ff));}else{var _fg=[0,_ff];}var _fh=_fg,_fi=_fh;return _fi;}),_ao]]));});});})),new T(function(){return B(_6Y([0,function(_fj){return E(E(_fj)[1])==94?E([0,function(_fk){switch(E(E(_fk)[1])){case 64:return E(new T(function(){return B(A(_fa,[_eD]));}));case 65:return E(new T(function(){return B(A(_fa,[_eE]));}));case 66:return E(new T(function(){return B(A(_fa,[_eF]));}));case 67:return E(new T(function(){return B(A(_fa,[_eG]));}));case 68:return E(new T(function(){return B(A(_fa,[_eH]));}));case 69:return E(new T(function(){return B(A(_fa,[_eI]));}));case 70:return E(new T(function(){return B(A(_fa,[_eJ]));}));case 71:return E(new T(function(){return B(A(_fa,[_eK]));}));case 72:return E(new T(function(){return B(A(_fa,[_eL]));}));case 73:return E(new T(function(){return B(A(_fa,[_eM]));}));case 74:return E(new T(function(){return B(A(_fa,[_eN]));}));case 75:return E(new T(function(){return B(A(_fa,[_eO]));}));case 76:return E(new T(function(){return B(A(_fa,[_eP]));}));case 77:return E(new T(function(){return B(A(_fa,[_eQ]));}));case 78:return E(new T(function(){return B(A(_fa,[_eR]));}));case 79:return E(new T(function(){return B(A(_fa,[_eS]));}));case 80:return E(new T(function(){return B(A(_fa,[_eT]));}));case 81:return E(new T(function(){return B(A(_fa,[_eU]));}));case 82:return E(new T(function(){return B(A(_fa,[_eV]));}));case 83:return E(new T(function(){return B(A(_fa,[_eW]));}));case 84:return E(new T(function(){return B(A(_fa,[_eX]));}));case 85:return E(new T(function(){return B(A(_fa,[_eY]));}));case 86:return E(new T(function(){return B(A(_fa,[_eZ]));}));case 87:return E(new T(function(){return B(A(_fa,[_f0]));}));case 88:return E(new T(function(){return B(A(_fa,[_f1]));}));case 89:return E(new T(function(){return B(A(_fa,[_f2]));}));case 90:return E(new T(function(){return B(A(_fa,[_f3]));}));case 91:return E(new T(function(){return B(A(_fa,[_f4]));}));case 92:return E(new T(function(){return B(A(_fa,[_f5]));}));case 93:return E(new T(function(){return B(A(_fa,[_f6]));}));case 94:return E(new T(function(){return B(A(_fa,[_f7]));}));case 95:return E(new T(function(){return B(A(_fa,[_f8]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_eo,[function(_fl){return new F(function(){return A(_fa,[[0,_fl,_ao]]);});}]));})));})));}));});},_fm=function(_fn){return new F(function(){return A(_fn,[_G]);});},_fo=function(_fp){var _fq=E(_fp);if(!_fq[0]){return E(_fm);}else{var _fr=_fq[2],_fs=E(E(_fq[1])[1]);switch(_fs){case 9:return function(_ft){return [0,function(_fu){return E(new T(function(){return B(A(new T(function(){return B(_fo(_fr));}),[_ft]));}));}];};case 10:return function(_fv){return [0,function(_fw){return E(new T(function(){return B(A(new T(function(){return B(_fo(_fr));}),[_fv]));}));}];};case 11:return function(_fx){return [0,function(_fy){return E(new T(function(){return B(A(new T(function(){return B(_fo(_fr));}),[_fx]));}));}];};case 12:return function(_fz){return [0,function(_fA){return E(new T(function(){return B(A(new T(function(){return B(_fo(_fr));}),[_fz]));}));}];};case 13:return function(_fB){return [0,function(_fC){return E(new T(function(){return B(A(new T(function(){return B(_fo(_fr));}),[_fB]));}));}];};case 32:return function(_fD){return [0,function(_fE){return E(new T(function(){return B(A(new T(function(){return B(_fo(_fr));}),[_fD]));}));}];};case 160:return function(_fF){return [0,function(_fG){return E(new T(function(){return B(A(new T(function(){return B(_fo(_fr));}),[_fF]));}));}];};default:var _fH=u_iswspace(_fs),_fI=_fH;return E(_fI)==0?E(_fm):function(_fJ){return [0,function(_fK){return E(new T(function(){return B(A(new T(function(){return B(_fo(_fr));}),[_fJ]));}));}];};}}},_fL=function(_fM){var _fN=new T(function(){return B(_fL(_fM));}),_fO=[1,function(_fP){return new F(function(){return A(_fo,[_fP,function(_fQ){return E([0,function(_fR){return E(E(_fR)[1])==92?E(_fN):[2];}]);}]);});}];return new F(function(){return _6Y([0,function(_fS){return E(E(_fS)[1])==92?E([0,function(_fT){var _fU=E(E(_fT)[1]);switch(_fU){case 9:return E(_fO);case 10:return E(_fO);case 11:return E(_fO);case 12:return E(_fO);case 13:return E(_fO);case 32:return E(_fO);case 38:return E(_fN);case 160:return E(_fO);default:var _fV=u_iswspace(_fU),_fW=_fV;return E(_fW)==0?[2]:E(_fO);}}]):[2];}],[0,function(_fX){var _fY=E(_fX);return E(_fY[1])==92?E(new T(function(){return B(_f9(_fM));})):B(A(_fM,[[0,_fY,_an]]));}]);});},_fZ=function(_g0,_g1){return new F(function(){return _fL(function(_g2){var _g3=E(_g2),_g4=E(_g3[1]);if(E(_g4[1])==34){if(!E(_g3[2])){return E(new T(function(){return B(A(_g1,[[1,new T(function(){return B(A(_g0,[_N]));})]]));}));}else{return new F(function(){return _fZ(function(_g5){return new F(function(){return A(_g0,[[1,_g4,_g5]]);});},_g1);});}}else{return new F(function(){return _fZ(function(_g6){return new F(function(){return A(_g0,[[1,_g4,_g6]]);});},_g1);});}});});},_g7=new T(function(){return B(unCStr("_\'"));}),_g8=function(_g9){var _ga=u_iswalnum(_g9),_gb=_ga;return E(_gb)==0?B(_a5(_7F,[0,_g9],_g7)):true;},_gc=function(_gd){return new F(function(){return _g8(E(_gd)[1]);});},_ge=new T(function(){return B(unCStr(",;()[]{}`"));}),_gf=function(_gg){return new F(function(){return A(_gg,[_N]);});},_gh=function(_gi,_gj){var _gk=function(_gl){var _gm=E(_gl);if(!_gm[0]){return E(_gf);}else{var _gn=_gm[1];return !B(A(_gi,[_gn]))?E(_gf):function(_go){return [0,function(_gp){return E(new T(function(){return B(A(new T(function(){return B(_gk(_gm[2]));}),[function(_gq){return new F(function(){return A(_go,[[1,_gn,_gq]]);});}]));}));}];};}};return [1,function(_gr){return new F(function(){return A(_gk,[_gr,_gj]);});}];},_gs=new T(function(){return B(unCStr(".."));}),_gt=new T(function(){return B(unCStr("::"));}),_gu=new T(function(){return B(unCStr("->"));}),_gv=[0,64],_gw=[1,_gv,_N],_gx=[0,126],_gy=[1,_gx,_N],_gz=new T(function(){return B(unCStr("=>"));}),_gA=[1,_gz,_N],_gB=[1,_gy,_gA],_gC=[1,_gw,_gB],_gD=[1,_gu,_gC],_gE=new T(function(){return B(unCStr("<-"));}),_gF=[1,_gE,_gD],_gG=[0,124],_gH=[1,_gG,_N],_gI=[1,_gH,_gF],_gJ=[1,_eu,_N],_gK=[1,_gJ,_gI],_gL=[0,61],_gM=[1,_gL,_N],_gN=[1,_gM,_gK],_gO=[1,_gt,_gN],_gP=[1,_gs,_gO],_gQ=function(_gR){return new F(function(){return _6Y([1,function(_gS){return E(_gS)[0]==0?E(new T(function(){return B(A(_gR,[_8A]));})):[2];}],new T(function(){return B(_6Y([0,function(_gT){return E(E(_gT)[1])==39?E([0,function(_gU){var _gV=E(_gU);switch(E(_gV[1])){case 39:return [2];case 92:return E(new T(function(){return B(_f9(function(_gW){var _gX=E(_gW);return new F(function(){return (function(_gY,_gZ){var _h0=new T(function(){return B(A(_gR,[[0,_gY]]));});return !E(_gZ)?E(E(_gY)[1])==39?[2]:[0,function(_h1){return E(E(_h1)[1])==39?E(_h0):[2];}]:[0,function(_h2){return E(E(_h2)[1])==39?E(_h0):[2];}];})(_gX[1],_gX[2]);});}));}));default:return [0,function(_h3){return E(E(_h3)[1])==39?E(new T(function(){return B(A(_gR,[[0,_gV]]));})):[2];}];}}]):[2];}],new T(function(){return B(_6Y([0,function(_h4){return E(E(_h4)[1])==34?E(new T(function(){return B(_fZ(_O,_gR));})):[2];}],new T(function(){return B(_6Y([0,function(_h5){return !B(_a5(_7F,_h5,_ge))?[2]:B(A(_gR,[[2,[1,_h5,_N]]]));}],new T(function(){return B(_6Y([0,function(_h6){if(!B(_a5(_7F,_h6,_aa))){return [2];}else{return new F(function(){return _gh(_ab,function(_h7){var _h8=[1,_h6,_h7];return !B(_a5(_7W,_h8,_gP))?B(A(_gR,[[4,_h8]])):B(A(_gR,[[2,_h8]]));});});}}],new T(function(){return B(_6Y([0,function(_h9){var _ha=E(_h9),_hb=_ha[1],_hc=u_iswalpha(_hb),_hd=_hc;if(!E(_hd)){if(E(_hb)==95){return new F(function(){return _gh(_gc,function(_he){return new F(function(){return A(_gR,[[3,[1,_ha,_he]]]);});});});}else{return [2];}}else{return new F(function(){return _gh(_gc,function(_hf){return new F(function(){return A(_gR,[[3,[1,_ha,_hf]]]);});});});}}],new T(function(){return B(_8g(_af,_a0,_gR));})));})));})));})));})));}));});},_hg=function(_hh){return [1,function(_hi){return new F(function(){return A(_fo,[_hi,function(_hj){return E(new T(function(){return B(_gQ(_hh));}));}]);});}];},_hk=[0,0],_hl=function(_hm,_hn){return new F(function(){return _hg(function(_ho){var _hp=E(_ho);if(_hp[0]==2){var _hq=E(_hp[1]);return _hq[0]==0?[2]:E(E(_hq[1])[1])==40?E(_hq[2])[0]==0?E(new T(function(){return B(A(_hm,[_hk,function(_hr){return new F(function(){return _hg(function(_hs){var _ht=E(_hs);if(_ht[0]==2){var _hu=E(_ht[1]);return _hu[0]==0?[2]:E(E(_hu[1])[1])==41?E(_hu[2])[0]==0?E(new T(function(){return B(A(_hn,[_hr]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_hv=function(_hw,_hx,_hy){var _hz=function(_hA,_hB){return new F(function(){return _6Y(B(_hg(function(_hC){var _hD=E(_hC);if(_hD[0]==4){var _hE=E(_hD[1]);if(!_hE[0]){return new F(function(){return A(_hw,[_hD,_hA,_hB]);});}else{return E(E(_hE[1])[1])==45?E(_hE[2])[0]==0?E([1,function(_hF){return new F(function(){return A(_fo,[_hF,function(_hG){return E(new T(function(){return B(_gQ(function(_hH){return new F(function(){return A(_hw,[_hH,_hA,function(_hI){return new F(function(){return A(_hB,[new T(function(){return [0, -E(_hI)[1]];})]);});}]);});}));}));}]);});}]):B(A(_hw,[_hD,_hA,_hB])):B(A(_hw,[_hD,_hA,_hB]));}}else{return new F(function(){return A(_hw,[_hD,_hA,_hB]);});}})),new T(function(){return B(_hl(_hz,_hB));}));});};return new F(function(){return _hz(_hx,_hy);});},_hJ=function(_hK,_hL){return [2];},_hM=function(_hN,_hO){return new F(function(){return _hJ(_hN,_hO);});},_hP=function(_hQ){var _hR=E(_hQ);return _hR[0]==0?[1,new T(function(){return B(_9C(new T(function(){return B(_9s(E(_hR[1])[1]));}),_9r,_hR[2]));})]:E(_hR[2])[0]==0?E(_hR[3])[0]==0?[1,new T(function(){return B(_9C(_9q,_9r,_hR[1]));})]:[0]:[0];},_hS=function(_hT){var _hU=E(_hT);if(_hU[0]==5){var _hV=B(_hP(_hU[1]));return _hV[0]==0?E(_hJ):function(_hW,_hX){return new F(function(){return A(_hX,[new T(function(){return [0,B(_aw(_hV[1]))];})]);});};}else{return E(_hM);}},_hY=function(_hZ,_i0){while(1){var _i1=E(_hZ);if(!_i1[0]){return E(_i0)[0]==0?true:false;}else{var _i2=E(_i0);if(!_i2[0]){return false;}else{if(E(_i1[1])[1]!=E(_i2[1])[1]){return false;}else{_hZ=_i1[2];_i0=_i2[2];continue;}}}}},_i3=new T(function(){return B(unCStr("onSideIndex"));}),_i4=new T(function(){return B(unCStr("LeftSidePlacement"));}),_i5=new T(function(){return B(unCStr("RightSidePlacement"));}),_i6=function(_i7,_i8){var _i9=new T(function(){if(_i7>11){var _ia=[2];}else{var _ia=[1,function(_ib){return new F(function(){return A(_fo,[_ib,function(_ic){return E(new T(function(){return B(_gQ(function(_id){var _ie=E(_id);return _ie[0]==3?!B(_hY(_ie[1],_i5))?[2]:E([1,function(_if){return new F(function(){return A(_fo,[_if,function(_ig){return E(new T(function(){return B(_gQ(function(_ih){var _ii=E(_ih);if(_ii[0]==2){var _ij=E(_ii[1]);return _ij[0]==0?[2]:E(E(_ij[1])[1])==123?E(_ij[2])[0]==0?E([1,function(_ik){return new F(function(){return A(_fo,[_ik,function(_il){return E(new T(function(){return B(_gQ(function(_im){var _in=E(_im);return _in[0]==3?!B(_hY(_in[1],_i3))?[2]:E([1,function(_io){return new F(function(){return A(_fo,[_io,function(_ip){return E(new T(function(){return B(_gQ(function(_iq){var _ir=E(_iq);if(_ir[0]==2){var _is=E(_ir[1]);return _is[0]==0?[2]:E(E(_is[1])[1])==61?E(_is[2])[0]==0?E(new T(function(){return B(_hv(_hS,_hk,function(_it){return new F(function(){return _hg(function(_iu){var _iv=E(_iu);if(_iv[0]==2){var _iw=E(_iv[1]);return _iw[0]==0?[2]:E(E(_iw[1])[1])==125?E(_iw[2])[0]==0?E(new T(function(){return B(A(_i8,[[3,_it]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}];}return _ia;});if(_i7>11){return new F(function(){return _6Y(_88,_i9);});}else{return new F(function(){return _6Y(B(_hg(function(_ix){var _iy=E(_ix);return _iy[0]==3?!B(_hY(_iy[1],_i4))?[2]:E([1,function(_iz){return new F(function(){return A(_fo,[_iz,function(_iA){return E(new T(function(){return B(_gQ(function(_iB){var _iC=E(_iB);if(_iC[0]==2){var _iD=E(_iC[1]);return _iD[0]==0?[2]:E(E(_iD[1])[1])==123?E(_iD[2])[0]==0?E([1,function(_iE){return new F(function(){return A(_fo,[_iE,function(_iF){return E(new T(function(){return B(_gQ(function(_iG){var _iH=E(_iG);return _iH[0]==3?!B(_hY(_iH[1],_i3))?[2]:E([1,function(_iI){return new F(function(){return A(_fo,[_iI,function(_iJ){return E(new T(function(){return B(_gQ(function(_iK){var _iL=E(_iK);if(_iL[0]==2){var _iM=E(_iL[1]);return _iM[0]==0?[2]:E(E(_iM[1])[1])==61?E(_iM[2])[0]==0?E(new T(function(){return B(_hv(_hS,_hk,function(_iN){return new F(function(){return _hg(function(_iO){var _iP=E(_iO);if(_iP[0]==2){var _iQ=E(_iP[1]);return _iQ[0]==0?[2]:E(E(_iQ[1])[1])==125?E(_iQ[2])[0]==0?E(new T(function(){return B(A(_i8,[[2,_iN]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),_i9);});}},_iR=new T(function(){return B(unCStr("onBarIndex"));}),_iS=new T(function(){return B(unCStr("BarPlacement"));}),_iT=function(_iU,_iV){if(_iU>11){return new F(function(){return _6Y(_88,new T(function(){return B(_i6(_iU,_iV));}));});}else{return new F(function(){return _6Y(B(_hg(function(_iW){var _iX=E(_iW);return _iX[0]==3?!B(_hY(_iX[1],_iS))?[2]:E([1,function(_iY){return new F(function(){return A(_fo,[_iY,function(_iZ){return E(new T(function(){return B(_gQ(function(_j0){var _j1=E(_j0);if(_j1[0]==2){var _j2=E(_j1[1]);return _j2[0]==0?[2]:E(E(_j2[1])[1])==123?E(_j2[2])[0]==0?E([1,function(_j3){return new F(function(){return A(_fo,[_j3,function(_j4){return E(new T(function(){return B(_gQ(function(_j5){var _j6=E(_j5);return _j6[0]==3?!B(_hY(_j6[1],_iR))?[2]:E([1,function(_j7){return new F(function(){return A(_fo,[_j7,function(_j8){return E(new T(function(){return B(_gQ(function(_j9){var _ja=E(_j9);if(_ja[0]==2){var _jb=E(_ja[1]);return _jb[0]==0?[2]:E(E(_jb[1])[1])==61?E(_jb[2])[0]==0?E(new T(function(){return B(_hv(_hS,_hk,function(_jc){return new F(function(){return _hg(function(_jd){var _je=E(_jd);if(_je[0]==2){var _jf=E(_je[1]);return _jf[0]==0?[2]:E(E(_jf[1])[1])==125?E(_jf[2])[0]==0?E(new T(function(){return B(A(_iV,[[1,_jc]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_i6(_iU,_iV));}));});}},_jg=new T(function(){return B(unCStr("onPointIndex"));}),_jh=new T(function(){return B(unCStr("pointIndex"));}),_ji=new T(function(){return B(unCStr("PointPlacement"));}),_jj=function(_jk,_jl){if(_jk>11){return new F(function(){return _6Y(_88,new T(function(){return B(_iT(_jk,_jl));}));});}else{return new F(function(){return _6Y(B(_hg(function(_jm){var _jn=E(_jm);return _jn[0]==3?!B(_hY(_jn[1],_ji))?[2]:E([1,function(_jo){return new F(function(){return A(_fo,[_jo,function(_jp){return E(new T(function(){return B(_gQ(function(_jq){var _jr=E(_jq);if(_jr[0]==2){var _js=E(_jr[1]);return _js[0]==0?[2]:E(E(_js[1])[1])==123?E(_js[2])[0]==0?E([1,function(_jt){return new F(function(){return A(_fo,[_jt,function(_ju){return E(new T(function(){return B(_gQ(function(_jv){var _jw=E(_jv);return _jw[0]==3?!B(_hY(_jw[1],_jh))?[2]:E([1,function(_jx){return new F(function(){return A(_fo,[_jx,function(_jy){return E(new T(function(){return B(_gQ(function(_jz){var _jA=E(_jz);if(_jA[0]==2){var _jB=E(_jA[1]);return _jB[0]==0?[2]:E(E(_jB[1])[1])==61?E(_jB[2])[0]==0?E(new T(function(){return B(_hv(_hS,_hk,function(_jC){return new F(function(){return _hg(function(_jD){var _jE=E(_jD);if(_jE[0]==2){var _jF=E(_jE[1]);return _jF[0]==0?[2]:E(E(_jF[1])[1])==44?E(_jF[2])[0]==0?E([1,function(_jG){return new F(function(){return A(_fo,[_jG,function(_jH){return E(new T(function(){return B(_gQ(function(_jI){var _jJ=E(_jI);return _jJ[0]==3?!B(_hY(_jJ[1],_jg))?[2]:E([1,function(_jK){return new F(function(){return A(_fo,[_jK,function(_jL){return E(new T(function(){return B(_gQ(function(_jM){var _jN=E(_jM);if(_jN[0]==2){var _jO=E(_jN[1]);return _jO[0]==0?[2]:E(E(_jO[1])[1])==61?E(_jO[2])[0]==0?E(new T(function(){return B(_hv(_hS,_hk,function(_jP){return new F(function(){return _hg(function(_jQ){var _jR=E(_jQ);if(_jR[0]==2){var _jS=E(_jR[1]);return _jS[0]==0?[2]:E(E(_jS[1])[1])==125?E(_jS[2])[0]==0?E(new T(function(){return B(A(_jl,[[0,_jC,_jP]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_iT(_jk,_jl));}));});}},_jT=function(_jU,_jV){return new F(function(){return _jj(E(_jU)[1],_jV);});},_jW=function(_jX,_jY){var _jZ=function(_k0){return function(_k1){return new F(function(){return _6Y(B(A(new T(function(){return B(A(_jX,[_k0]));}),[_k1])),new T(function(){return B(_hl(_jZ,_k1));}));});};};return new F(function(){return _jZ(_jY);});},_k2=function(_k3){return [1,function(_k4){return new F(function(){return A(_fo,[_k4,function(_k5){return E([3,_k3,_88]);}]);});}];},_k6=new T(function(){return B(A(_jW,[_jT,_hk,_k2]));}),_k7=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_k8=new T(function(){return B(err(_k7));}),_k9=function(_ka,_kb){return new F(function(){return A(_kb,[_4X]);});},_kc=[0,_1,_k9],_kd=[1,_kc,_N],_ke=function(_kf,_kg){return new F(function(){return A(_kg,[_4W]);});},_kh=[0,_0,_ke],_ki=[1,_kh,_kd],_kj=function(_kk,_kl,_km){var _kn=E(_kk);if(!_kn[0]){return [2];}else{var _ko=E(_kn[1]),_kp=_ko[1],_kq=new T(function(){return B(A(_ko[2],[_kl,_km]));});return new F(function(){return _6Y(B(_hg(function(_kr){var _ks=E(_kr);switch(_ks[0]){case 3:return !B(_hY(_kp,_ks[1]))?[2]:E(_kq);case 4:return !B(_hY(_kp,_ks[1]))?[2]:E(_kq);default:return [2];}})),new T(function(){return B(_kj(_kn[2],_kl,_km));}));});}},_kt=function(_ku,_kv){return new F(function(){return _kj(_ki,_ku,_kv);});},_kw=new T(function(){return B(A(_jW,[_kt,_hk,_k2]));}),_kx=new T(function(){return B(err(_k7));}),_ky=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_kz=new T(function(){return B(err(_ky));}),_kA=new T(function(){return B(err(_ky));}),_kB=function(_kC,_kD,_kE){return _kE<=_kD?[1,[0,_kC],new T(function(){var _kF=_kD-_kC|0,_kG=function(_kH){return _kH>=(_kE-_kF|0)?[1,[0,_kH],new T(function(){return B(_kG(_kH+_kF|0));})]:[1,[0,_kH],_N];};return B(_kG(_kD));})]:_kE<=_kC?[1,[0,_kC],_N]:[0];},_kI=function(_kJ,_kK,_kL){return _kL>=_kK?[1,[0,_kJ],new T(function(){var _kM=_kK-_kJ|0,_kN=function(_kO){return _kO<=(_kL-_kM|0)?[1,[0,_kO],new T(function(){return B(_kN(_kO+_kM|0));})]:[1,[0,_kO],_N];};return B(_kN(_kK));})]:_kL>=_kJ?[1,[0,_kJ],_N]:[0];},_kP=function(_kQ,_kR){return _kR<_kQ?B(_kB(_kQ,_kR,-2147483648)):B(_kI(_kQ,_kR,2147483647));},_kS=new T(function(){return B(_kP(135,150));}),_kT=function(_kU,_kV){var _kW=E(_kU);if(!_kW){return [0];}else{var _kX=E(_kV);return _kX[0]==0?[0]:[1,_kX[1],new T(function(){return B(_kT(_kW-1|0,_kX[2]));})];}},_kY=new T(function(){return B(_kT(6,_kS));}),_kZ=function(_l0,_l1){var _l2=E(_l0);if(!_l2[0]){return E(_kY);}else{var _l3=_l2[1];return _l1>1?[1,_l3,new T(function(){return B(_kZ(_l2[2],_l1-1|0));})]:[1,_l3,_kY];}},_l4=new T(function(){return B(_kP(25,40));}),_l5=new T(function(){return B(_kZ(_l4,6));}),_l6=function(_l7){while(1){var _l8=(function(_l9){var _la=E(_l9);if(!_la[0]){return [0];}else{var _lb=_la[2],_lc=E(_la[1]);if(!E(_lc[2])[0]){return [1,_lc[1],new T(function(){return B(_l6(_lb));})];}else{_l7=_lb;return null;}}})(_l7);if(_l8!=null){return _l8;}}},_ld=function(_le,_lf){var _lg=E(_lf);if(!_lg[0]){return [0,_N,_N];}else{var _lh=_lg[1];if(!B(A(_le,[_lh]))){var _li=new T(function(){var _lj=B(_ld(_le,_lg[2]));return [0,_lj[1],_lj[2]];});return [0,[1,_lh,new T(function(){return E(E(_li)[1]);})],new T(function(){return E(E(_li)[2]);})];}else{return [0,_N,_lg];}}},_lk=function(_ll,_lm){while(1){var _ln=E(_lm);if(!_ln[0]){return [0];}else{if(!B(A(_ll,[_ln[1]]))){return E(_ln);}else{_lm=_ln[2];continue;}}}},_lo=function(_lp){var _lq=E(_lp);switch(_lq){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _lr=u_iswspace(_lq),_ls=_lr;return E(_ls)==0?false:true;}},_lt=function(_lu){return new F(function(){return _lo(E(_lu)[1]);});},_lv=function(_lw){var _lx=B(_lk(_lt,_lw));if(!_lx[0]){return [0];}else{var _ly=new T(function(){var _lz=B(_ld(_lt,_lx));return [0,_lz[1],_lz[2]];});return [1,new T(function(){return E(E(_ly)[1]);}),new T(function(){return B(_lv(E(_ly)[2]));})];}},_lA=function(_lB,_){var _lC=setDropCheckerCallback_ffi(function(_lD,_lE,_lF){var _lG=E(_lB),_lH=_lG[1],_lI=_lG[6],_lJ=new T(function(){return B(_lv(B(_6H(_lD))));}),_lK=B(_l6(B(_6O(_k6,new T(function(){return B(_X(_6J,B(_5Y(_lJ,2))));})))));if(!_lK[0]){return E(_kA);}else{if(!E(_lK[2])[0]){var _lL=E(_lK[1]);if(!_lL[0]){var _lM=B(_6o(function(_lN){var _lO=E(_lN)[1]-E(_lE)[1];return _lO<0? -_lO<7:_lO<7;},_l5));if(!_lM[0]){return function(_8z){return new F(function(){return _69(_lL,_lL,_lI,_8z);});};}else{var _lP=_lM[1],_lQ=function(_lR,_lS,_){var _lT=E(_lL[1]),_lU=_lT[1];if(_lR<=_lU){return new F(function(){return _69(_lL,_lL,_lI,_);});}else{var _lV=B(_l6(B(_6O(_kw,new T(function(){return B(_5Y(_lJ,1));})))));if(!_lV[0]){return E(_kz);}else{var _lW=_lV[1];if(!E(_lV[2])[0]){if(_lR>=0){var _lX=B(_5Y(_lH,_lR)),_lY=function(_){var _lZ=B(_69(_lL,[0,_lS,new T(function(){if(_lR>=0){var _m0=E(B(_5Y(_lH,_lR))[2]);}else{var _m0=E(_5V);}return _m0;})],_lI,_)),_m1=_lZ;if(_lU>=0){var _m2=new T(function(){return B(_6A(function(_m3,_m4,_m5){return [1,new T(function(){var _m6=E(_m3)[1];return _m6!=_lU?_m6!=_lR?E(_m4):[0,new T(function(){if(_lU>=0){var _m7=E(B(_5Y(_lH,_lU))[1]);}else{var _m7=E(_5V);}return _m7;}),new T(function(){return [0,E(E(_m4)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_m4)[1]);}),new T(function(){return [0,E(E(_m4)[2])[1]-1|0];})];}),_m5];},_N,_4m,_lH));}),_m8=B((function(_m9,_){while(1){var _ma=(function(_mb,_){var _mc=E(_mb);if(!_mc[0]){return _G;}else{var _md=_mc[1],_me=B(_69([0,_lT,_md],[0,_lT,new T(function(){return [0,E(_md)[1]-1|0];})],_lI,_)),_mf=_me;_m9=_mc[2];return null;}})(_m9,_);if(_ma!=null){return _ma;}}})(B(_6j(1,B(_4g(E(_lL[2])[1],E(B(_5Y(_m2,_lU))[2])[1])))),_)),_mg=_m8;return new F(function(){return _lA([0,_m2,_lG[2],_lG[3],_lG[4],_lG[5],_lI,_lG[7]],_);});}else{return E(_5V);}},_mh=function(_){return E(_lX[2])[1]>=2?B(_69(_lL,_lL,_lI,_)):B(_lY(_));};return E(_lX[1])==0?E(_lW)==0?B(_lY(_)):B(_mh(_)):E(_lW)==0?B(_mh(_)):B(_lY(_));}else{return E(_5V);}}else{return E(_kx);}}}};if(E(_lF)[1]<=E(_6M)[1]){var _mi=E(_lP);return function(_8z){return new F(function(){return _lQ(_mi[1],_mi,_8z);});};}else{var _mj=23-E(_lP)[1]|0;return function(_8z){return new F(function(){return _lQ(_mj,[0,_mj],_8z);});};}}}else{return function(_8z){return new F(function(){return _69(_lL,_lL,_lI,_8z);});};}}else{return E(_k8);}}});return _G;},_mk=function(_){var _ml=E(_5S)[1],_mm=B(_4q(_4X,_4X,_ml,_)),_mn=_mm,_mo=B(_4q(_4W,_4X,_ml,_)),_mp=_mo;return new F(function(){return _lA(_5T,_);});},_mq=function(_){return new F(function(){return _mk(_);});};
var hasteMain = function() {B(A(_mq, [0]));};window.onload = hasteMain;