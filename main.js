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

var _0=new T(function(){return B(unCStr("You have not joined a game (yet)."));}),_1=new T(function(){return B(unCStr("innerHTML"));}),_2=new T(function(){return B(unCStr("HintText"));}),_3=new T(function(){return B(unCStr("Black"));}),_4=new T(function(){return B(unCStr("White"));}),_5=[0,125],_6=new T(function(){return B(unCStr(", "));}),_7=function(_8,_9){var _a=E(_8);return _a[0]==0?E(_9):[1,_a[1],new T(function(){return B(_7(_a[2],_9));})];},_b=function(_c,_d){var _e=jsShowI(_c),_f=_e;return new F(function(){return _7(fromJSStr(_f),_d);});},_g=[0,41],_h=[0,40],_i=function(_j,_k,_l){return _k>=0?B(_b(_k,_l)):_j<=6?B(_b(_k,_l)):[1,_h,new T(function(){var _m=jsShowI(_k),_n=_m;return B(_7(fromJSStr(_n),[1,_g,_l]));})];},_o=new T(function(){return B(unCStr("onPointIndex = "));}),_p=new T(function(){return B(unCStr("BarPlacement {"));}),_q=new T(function(){return B(unCStr("onBarIndex = "));}),_r=new T(function(){return B(unCStr("LeftSidePlacement {"));}),_s=new T(function(){return B(unCStr("onSideIndex = "));}),_t=new T(function(){return B(unCStr("RightSidePlacement {"));}),_u=new T(function(){return B(unCStr("PointPlacement {"));}),_v=new T(function(){return B(unCStr("pointIndex = "));}),_w=function(_x,_y,_z){var _A=E(_y);switch(_A[0]){case 0:var _B=function(_C){return new F(function(){return _7(_v,new T(function(){return B(_i(0,E(_A[1])[1],new T(function(){return B(_7(_6,new T(function(){return B(_7(_o,new T(function(){return B(_i(0,E(_A[2])[1],[1,_5,_C]));})));})));})));}));});};return _x<11?B(_7(_u,new T(function(){return B(_B(_z));}))):[1,_h,new T(function(){return B(_7(_u,new T(function(){return B(_B([1,_g,_z]));})));})];case 1:var _D=function(_E){return new F(function(){return _7(_p,new T(function(){return B(_7(_q,new T(function(){return B(_i(0,E(_A[1])[1],[1,_5,_E]));})));}));});};return _x<11?B(_D(_z)):[1,_h,new T(function(){return B(_D([1,_g,_z]));})];case 2:var _F=function(_G){return new F(function(){return _7(_r,new T(function(){return B(_7(_s,new T(function(){return B(_i(0,E(_A[1])[1],[1,_5,_G]));})));}));});};return _x<11?B(_F(_z)):[1,_h,new T(function(){return B(_F([1,_g,_z]));})];default:var _H=function(_I){return new F(function(){return _7(_t,new T(function(){return B(_7(_s,new T(function(){return B(_i(0,E(_A[1])[1],[1,_5,_I]));})));}));});};return _x<11?B(_H(_z)):[1,_h,new T(function(){return B(_H([1,_g,_z]));})];}},_J=0,_K=function(_L,_M,_N,_O){return new F(function(){return A(_L,[new T(function(){return function(_){var _P=jsSetAttr(E(_M)[1],toJSStr(E(_N)),toJSStr(E(_O)));return _J;};})]);});},_Q=[0],_R=function(_S){return E(_S);},_T=[0,95],_U=function(_V){var _W=E(_V);return E(_W[1])==32?E(_T):E(_W);},_X=new T(function(){return B(unCStr("class"));}),_Y=new T(function(){return B(unCStr("draggable "));}),_Z=[0,32],_10=function(_11,_12){var _13=E(_12);return _13[0]==0?[0]:[1,new T(function(){return B(A(_11,[_13[1]]));}),new T(function(){return B(_10(_11,_13[2]));})];},_14=function(_15,_16,_17,_18){return new F(function(){return _K(_R,_15,_X,new T(function(){var _19=new T(function(){var _1a=new T(function(){return B(_10(_U,B(_w(0,_17,_Q))));});return E(_18)==0?B(_7(_3,[1,_Z,_1a])):B(_7(_4,[1,_Z,_1a]));});return E(_16)==0?E(_18)==0?B(_7(_Y,_19)):E(_19):E(_18)==0?E(_19):B(_7(_Y,_19));}));});},_1b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_1c=new T(function(){return B(unCStr("base"));}),_1d=new T(function(){return B(unCStr("PatternMatchFail"));}),_1e=new T(function(){var _1f=hs_wordToWord64(18445595),_1g=_1f,_1h=hs_wordToWord64(52003073),_1i=_1h;return [0,_1g,_1i,[0,_1g,_1i,_1c,_1b,_1d],_Q];}),_1j=function(_1k){return E(_1e);},_1l=function(_1m){return E(E(_1m)[1]);},_1n=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1o=new T(function(){return B(err(_1n));}),_1p=function(_1q,_1r,_1s){var _1t=new T(function(){var _1u=B(A(_1q,[_1s])),_1v=B(A(_1r,[new T(function(){var _1w=E(_1t);return _1w[0]==0?E(_1o):E(_1w[1]);})])),_1x=hs_eqWord64(_1u[1],_1v[1]),_1y=_1x;if(!E(_1y)){var _1z=[0];}else{var _1A=hs_eqWord64(_1u[2],_1v[2]),_1B=_1A,_1z=E(_1B)==0?[0]:[1,_1s];}var _1C=_1z,_1D=_1C;return _1D;});return E(_1t);},_1E=function(_1F){var _1G=E(_1F);return new F(function(){return _1p(B(_1l(_1G[1])),_1j,_1G[2]);});},_1H=function(_1I){return E(E(_1I)[1]);},_1J=function(_1K,_1L){return new F(function(){return _7(E(_1K)[1],_1L);});},_1M=[0,44],_1N=[0,93],_1O=[0,91],_1P=function(_1Q,_1R,_1S){var _1T=E(_1R);return _1T[0]==0?B(unAppCStr("[]",_1S)):[1,_1O,new T(function(){return B(A(_1Q,[_1T[1],new T(function(){var _1U=function(_1V){var _1W=E(_1V);return _1W[0]==0?E([1,_1N,_1S]):[1,_1M,new T(function(){return B(A(_1Q,[_1W[1],new T(function(){return B(_1U(_1W[2]));})]));})];};return B(_1U(_1T[2]));})]));})];},_1X=function(_1Y,_1Z){return new F(function(){return _1P(_1J,_1Y,_1Z);});},_20=function(_21,_22,_23){return new F(function(){return _7(E(_22)[1],_23);});},_24=[0,_20,_1H,_1X],_25=new T(function(){return [0,_1j,_24,_26,_1E];}),_26=function(_27){return [0,_25,_27];},_28=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_29=function(_2a,_2b){return new F(function(){return die(new T(function(){return B(A(_2b,[_2a]));}));});},_2c=function(_2d,_2e){var _2f=E(_2e);if(!_2f[0]){return [0,_Q,_Q];}else{var _2g=_2f[1];if(!B(A(_2d,[_2g]))){return [0,_Q,_2f];}else{var _2h=new T(function(){var _2i=B(_2c(_2d,_2f[2]));return [0,_2i[1],_2i[2]];});return [0,[1,_2g,new T(function(){return E(E(_2h)[1]);})],new T(function(){return E(E(_2h)[2]);})];}}},_2j=[0,32],_2k=[0,10],_2l=[1,_2k,_Q],_2m=function(_2n){return E(E(_2n)[1])==124?false:true;},_2o=function(_2p,_2q){var _2r=B(_2c(_2m,B(unCStr(_2p)))),_2s=_2r[1],_2t=function(_2u,_2v){return new F(function(){return _7(_2u,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_7(_2q,new T(function(){return B(_7(_2v,_2l));})));})));}));});},_2w=E(_2r[2]);if(!_2w[0]){return new F(function(){return _2t(_2s,_Q);});}else{return E(E(_2w[1])[1])==124?B(_2t(_2s,[1,_2j,_2w[2]])):B(_2t(_2s,_Q));}},_2x=function(_2y){return new F(function(){return _29([0,new T(function(){return B(_2o(_2y,_28));})],_26);});},_2z=new T(function(){return B(_2x("main.hs:(84,1)-(111,116)|function checkerPosition"));}),_2A=function(_2B,_2C){if(_2B<=0){if(_2B>=0){return new F(function(){return quot(_2B,_2C);});}else{if(_2C<=0){return new F(function(){return quot(_2B,_2C);});}else{return quot(_2B+1|0,_2C)-1|0;}}}else{if(_2C>=0){if(_2B>=0){return new F(function(){return quot(_2B,_2C);});}else{if(_2C<=0){return new F(function(){return quot(_2B,_2C);});}else{return quot(_2B+1|0,_2C)-1|0;}}}else{return quot(_2B-1|0,_2C)-1|0;}}},_2D=new T(function(){return [0,B(_2A(15,2))];}),_2E=new T(function(){return [0,220+B(_2A(15,2))|0];}),_2F=function(_2G){var _2H=E(_2G);switch(_2H[0]){case 0:var _2I=_2H[1],_2J=_2H[2];return [0,new T(function(){var _2K=E(_2I)[1];if(_2K>=12){var _2L=23-_2K|0;if(_2L>=6){var _2M=[0,25+(20+(imul(_2L,15)|0)|0)|0];}else{var _2M=[0,25+(imul(_2L,15)|0)|0];}var _2N=_2M,_2O=_2N;}else{if(_2K>=6){var _2P=[0,25+(20+(imul(_2K,15)|0)|0)|0];}else{var _2P=[0,25+(imul(_2K,15)|0)|0];}var _2O=_2P;}var _2Q=_2O;return _2Q;}),new T(function(){if(E(_2I)[1]>=12){var _2R=[0,203+(imul(imul(imul(-1,E(_2J)[1])|0,2)|0,6)|0)|0];}else{var _2R=[0,7+(imul(imul(E(_2J)[1],2)|0,6)|0)|0];}var _2S=_2R;return _2S;})];case 1:return E(_2z);case 2:return [0,_2D,new T(function(){return [0,203-(imul(imul(E(_2H[1])[1],2)|0,6)|0)|0];})];default:return [0,_2E,new T(function(){return [0,203-(imul(imul(E(_2H[1])[1],2)|0,6)|0)|0];})];}},_2T=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:148:5-10"));}),_2U=function(_){return _J;},_2V=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_2W=new T(function(){return B(unCStr("base"));}),_2X=new T(function(){return B(unCStr("IOException"));}),_2Y=new T(function(){var _2Z=hs_wordToWord64(4053623282),_30=_2Z,_31=hs_wordToWord64(3693590983),_32=_31;return [0,_30,_32,[0,_30,_32,_2W,_2V,_2X],_Q];}),_33=function(_34){return E(_2Y);},_35=function(_36){var _37=E(_36);return new F(function(){return _1p(B(_1l(_37[1])),_33,_37[2]);});},_38=new T(function(){return B(unCStr(": "));}),_39=[0,41],_3a=new T(function(){return B(unCStr(" ("));}),_3b=new T(function(){return B(unCStr("already exists"));}),_3c=new T(function(){return B(unCStr("does not exist"));}),_3d=new T(function(){return B(unCStr("protocol error"));}),_3e=new T(function(){return B(unCStr("failed"));}),_3f=new T(function(){return B(unCStr("invalid argument"));}),_3g=new T(function(){return B(unCStr("inappropriate type"));}),_3h=new T(function(){return B(unCStr("hardware fault"));}),_3i=new T(function(){return B(unCStr("unsupported operation"));}),_3j=new T(function(){return B(unCStr("timeout"));}),_3k=new T(function(){return B(unCStr("resource vanished"));}),_3l=new T(function(){return B(unCStr("interrupted"));}),_3m=new T(function(){return B(unCStr("resource busy"));}),_3n=new T(function(){return B(unCStr("resource exhausted"));}),_3o=new T(function(){return B(unCStr("end of file"));}),_3p=new T(function(){return B(unCStr("illegal operation"));}),_3q=new T(function(){return B(unCStr("permission denied"));}),_3r=new T(function(){return B(unCStr("user error"));}),_3s=new T(function(){return B(unCStr("unsatisified constraints"));}),_3t=new T(function(){return B(unCStr("system error"));}),_3u=function(_3v,_3w){switch(E(_3v)){case 0:return new F(function(){return _7(_3b,_3w);});break;case 1:return new F(function(){return _7(_3c,_3w);});break;case 2:return new F(function(){return _7(_3m,_3w);});break;case 3:return new F(function(){return _7(_3n,_3w);});break;case 4:return new F(function(){return _7(_3o,_3w);});break;case 5:return new F(function(){return _7(_3p,_3w);});break;case 6:return new F(function(){return _7(_3q,_3w);});break;case 7:return new F(function(){return _7(_3r,_3w);});break;case 8:return new F(function(){return _7(_3s,_3w);});break;case 9:return new F(function(){return _7(_3t,_3w);});break;case 10:return new F(function(){return _7(_3d,_3w);});break;case 11:return new F(function(){return _7(_3e,_3w);});break;case 12:return new F(function(){return _7(_3f,_3w);});break;case 13:return new F(function(){return _7(_3g,_3w);});break;case 14:return new F(function(){return _7(_3h,_3w);});break;case 15:return new F(function(){return _7(_3i,_3w);});break;case 16:return new F(function(){return _7(_3j,_3w);});break;case 17:return new F(function(){return _7(_3k,_3w);});break;default:return new F(function(){return _7(_3l,_3w);});}},_3x=[0,125],_3y=new T(function(){return B(unCStr("{handle: "));}),_3z=function(_3A,_3B,_3C,_3D,_3E,_3F){var _3G=new T(function(){var _3H=new T(function(){return B(_3u(_3B,new T(function(){var _3I=E(_3D);return _3I[0]==0?E(_3F):B(_7(_3a,new T(function(){return B(_7(_3I,[1,_39,_3F]));})));})));}),_3J=E(_3C);return _3J[0]==0?E(_3H):B(_7(_3J,new T(function(){return B(_7(_38,_3H));})));}),_3K=E(_3E);if(!_3K[0]){var _3L=E(_3A);if(!_3L[0]){return E(_3G);}else{var _3M=E(_3L[1]);return _3M[0]==0?B(_7(_3y,new T(function(){return B(_7(_3M[1],[1,_3x,new T(function(){return B(_7(_38,_3G));})]));}))):B(_7(_3y,new T(function(){return B(_7(_3M[1],[1,_3x,new T(function(){return B(_7(_38,_3G));})]));})));}}else{return new F(function(){return _7(_3K[1],new T(function(){return B(_7(_38,_3G));}));});}},_3N=function(_3O){var _3P=E(_3O);return new F(function(){return _3z(_3P[1],_3P[2],_3P[3],_3P[4],_3P[6],_Q);});},_3Q=function(_3R,_3S){var _3T=E(_3R);return new F(function(){return _3z(_3T[1],_3T[2],_3T[3],_3T[4],_3T[6],_3S);});},_3U=function(_3V,_3W){return new F(function(){return _1P(_3Q,_3V,_3W);});},_3X=function(_3Y,_3Z,_40){var _41=E(_3Z);return new F(function(){return _3z(_41[1],_41[2],_41[3],_41[4],_41[6],_40);});},_42=[0,_3X,_3N,_3U],_43=new T(function(){return [0,_33,_42,_44,_35];}),_44=function(_45){return [0,_43,_45];},_46=[0],_47=7,_48=function(_49){return [0,_46,_47,_Q,_49,_46,_46];},_4a=function(_4b,_){return new F(function(){return die(new T(function(){return B(_44(new T(function(){return B(_48(_4b));})));}));});},_4c=function(_4d,_){return new F(function(){return _4a(_4d,_);});},_4e=[0,114],_4f=[1,_4e,_Q],_4g=new T(function(){return B(_i(0,6,_Q));}),_4h=new T(function(){return B(unCStr("cx"));}),_4i=new T(function(){return B(unCStr("cy"));}),_4j=function(_4k,_4l){if(_4k<=_4l){var _4m=function(_4n){return [1,[0,_4n],new T(function(){if(_4n!=_4l){var _4o=B(_4m(_4n+1|0));}else{var _4o=[0];}return _4o;})];};return new F(function(){return _4m(_4k);});}else{return [0];}},_4p=new T(function(){return B(_4j(0,2147483647));}),_4q=new T(function(){return B(unCStr("circle"));}),_4r=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_4s=new T(function(){return B(unCStr("board"));}),_4t=function(_4u,_4v,_4w,_){if(_4w>0){var _4x=function(_4y,_4z,_){var _4A=jsFind(toJSStr(E(_4s))),_4B=_4A,_4C=E(_4B);if(!_4C[0]){var _4D=B(_4c(_2T,_)),_4E=_4D;return new F(function(){return A(_4z,[_]);});}else{var _4F=jsCreateElemNS(toJSStr(E(_4r)),toJSStr(E(_4q))),_4G=_4F,_4H=[0,_4G],_4I=B(A(_K,[_R,_4H,_4f,_4g,_])),_4J=_4I,_4K=new T(function(){return E(_4u)==0?[3,_4y]:[2,_4y];}),_4L=new T(function(){var _4M=B(_2F(_4K));return [0,_4M[1],_4M[2]];}),_4N=B(A(_K,[_R,_4H,_4h,new T(function(){return B(_i(0,E(E(_4L)[1])[1],_Q));}),_])),_4O=_4N,_4P=B(A(_K,[_R,_4H,_4i,new T(function(){return B(_i(0,E(E(_4L)[2])[1],_Q));}),_])),_4Q=_4P,_4R=B(A(_14,[_4H,_4v,_4K,_4u,_])),_4S=_4R,_4T=jsAppendChild(_4G,E(_4C[1])[1]);return new F(function(){return A(_4z,[_]);});}},_4U=function(_4V,_4W,_){var _4X=E(_4V);if(!_4X[0]){return _J;}else{var _4Y=_4X[1];if(_4W>1){return new F(function(){return _4x(_4Y,function(_){return new F(function(){return _4U(_4X[2],_4W-1|0,_);});},_);});}else{return new F(function(){return _4x(_4Y,_2U,_);});}}};return new F(function(){return _4U(_4p,_4w,_);});}else{return _J;}},_4Z=0,_50=1,_51=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_52=new T(function(){return B(err(_51));}),_53=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_54=new T(function(){return B(err(_53));}),_55=function(_56,_57){while(1){var _58=E(_56);if(!_58[0]){return E(_54);}else{var _59=E(_57);if(!_59){return E(_58[1]);}else{_56=_58[2];_57=_59-1|0;continue;}}}},_5a=new T(function(){return B(unCStr(": empty list"));}),_5b=new T(function(){return B(unCStr("Prelude."));}),_5c=function(_5d){return new F(function(){return err(B(_7(_5b,new T(function(){return B(_7(_5d,_5a));}))));});},_5e=new T(function(){return B(unCStr("head"));}),_5f=new T(function(){return B(_5c(_5e));}),_5g=function(_5h,_5i,_5j,_){var _5k=jsElemsByClassName(toJSStr(B(_10(_U,B(_w(0,_5h,_Q)))))),_5l=_5k,_5m=E(_5l);if(!_5m[0]){return E(_5f);}else{var _5n=E(_5m[1]),_5o=B(_2F(_5i)),_5p=animateCircle_ffi(_5n[1],E(_5o[1])[1],E(_5o[2])[1],300);return new F(function(){return A(_14,[_5n,_5j,_5i,_5j,_]);});}},_5q=function(_5r,_5s){while(1){var _5t=E(_5r);if(!_5t){return E(_5s);}else{var _5u=E(_5s);if(!_5u[0]){return [0];}else{_5r=_5t-1|0;_5s=_5u[2];continue;}}}},_5v=function(_5w,_5x){var _5y=function(_5z,_5A){while(1){var _5B=(function(_5C,_5D){var _5E=E(_5D);if(!_5E[0]){return [0];}else{var _5F=_5E[2];if(!B(A(_5w,[_5E[1]]))){var _5G=_5C+1|0;_5A=_5F;_5z=_5G;return null;}else{return [1,[0,_5C],new T(function(){return B(_5y(_5C+1|0,_5F));})];}}})(_5z,_5A);if(_5B!=null){return _5B;}}};return new F(function(){return _5y(0,_5x);});},_5H=function(_5I,_5J,_5K,_5L){var _5M=E(_5K);if(!_5M[0]){return E(_5J);}else{var _5N=E(_5L);if(!_5N[0]){return E(_5J);}else{return new F(function(){return A(_5I,[_5M[1],_5N[1],new T(function(){return B(_5H(_5I,_5J,_5M[2],_5N[2]));})]);});}}},_5O=function(_5P){return new F(function(){return fromJSStr(E(_5P)[1]);});},_5Q=function(_5R){var _5S=E(_5R);return E(_5S[1])==95?E(_Z):E(_5S);},_5T=new T(function(){return [0,B(_2A(210,2))];}),_5U=new T(function(){return B(_2x("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_5V=function(_5W,_5X){while(1){var _5Y=(function(_5Z,_60){var _61=E(_5Z);switch(_61[0]){case 0:var _62=E(_60);if(!_62[0]){return [0];}else{_5W=B(A(_61[1],[_62[1]]));_5X=_62[2];return null;}break;case 1:var _63=B(A(_61[1],[_60])),_64=_60;_5W=_63;_5X=_64;return null;case 2:return [0];case 3:return [1,[0,_61[1],_60],new T(function(){return B(_5V(_61[2],_60));})];default:return E(_61[1]);}})(_5W,_5X);if(_5Y!=null){return _5Y;}}},_65=function(_66,_67){var _68=new T(function(){var _69=E(_67);if(_69[0]==3){var _6a=[3,_69[1],new T(function(){return B(_65(_66,_69[2]));})];}else{var _6b=E(_66);if(_6b[0]==2){var _6c=E(_69);}else{var _6d=E(_69);if(_6d[0]==2){var _6e=E(_6b);}else{var _6f=new T(function(){var _6g=E(_6d);if(_6g[0]==4){var _6h=[1,function(_6i){return [4,new T(function(){return B(_7(B(_5V(_6b,_6i)),_6g[1]));})];}];}else{var _6j=E(_6b);if(_6j[0]==1){var _6k=_6j[1],_6l=E(_6g);if(!_6l[0]){var _6m=[1,function(_6n){return new F(function(){return _65(B(A(_6k,[_6n])),_6l);});}];}else{var _6m=[1,function(_6o){return new F(function(){return _65(B(A(_6k,[_6o])),new T(function(){return B(A(_6l[1],[_6o]));}));});}];}var _6p=_6m;}else{var _6q=E(_6g);if(!_6q[0]){var _6r=E(_5U);}else{var _6r=[1,function(_6s){return new F(function(){return _65(_6j,new T(function(){return B(A(_6q[1],[_6s]));}));});}];}var _6p=_6r;}var _6h=_6p;}return _6h;}),_6t=E(_6b);switch(_6t[0]){case 1:var _6u=E(_6d);if(_6u[0]==4){var _6v=[1,function(_6w){return [4,new T(function(){return B(_7(B(_5V(B(A(_6t[1],[_6w])),_6w)),_6u[1]));})];}];}else{var _6v=E(_6f);}var _6x=_6v;break;case 4:var _6y=_6t[1],_6z=E(_6d);switch(_6z[0]){case 0:var _6A=[1,function(_6B){return [4,new T(function(){return B(_7(_6y,new T(function(){return B(_5V(_6z,_6B));})));})];}];break;case 1:var _6A=[1,function(_6C){return [4,new T(function(){return B(_7(_6y,new T(function(){return B(_5V(B(A(_6z[1],[_6C])),_6C));})));})];}];break;default:var _6A=[4,new T(function(){return B(_7(_6y,_6z[1]));})];}var _6x=_6A;break;default:var _6x=E(_6f);}var _6e=_6x;}var _6c=_6e;}var _6a=_6c;}return _6a;}),_6D=E(_66);switch(_6D[0]){case 0:var _6E=E(_67);return _6E[0]==0?[0,function(_6F){return new F(function(){return _65(B(A(_6D[1],[_6F])),new T(function(){return B(A(_6E[1],[_6F]));}));});}]:E(_68);case 3:return [3,_6D[1],new T(function(){return B(_65(_6D[2],_67));})];default:return E(_68);}},_6G=function(_6H,_6I){return E(_6H)[1]!=E(_6I)[1];},_6J=function(_6K,_6L){return E(_6K)[1]==E(_6L)[1];},_6M=[0,_6J,_6G],_6N=function(_6O){return E(E(_6O)[1]);},_6P=function(_6Q,_6R,_6S){while(1){var _6T=E(_6R);if(!_6T[0]){return E(_6S)[0]==0?true:false;}else{var _6U=E(_6S);if(!_6U[0]){return false;}else{if(!B(A(_6N,[_6Q,_6T[1],_6U[1]]))){return false;}else{_6R=_6T[2];_6S=_6U[2];continue;}}}}},_6V=function(_6W,_6X,_6Y){return !B(_6P(_6W,_6X,_6Y))?true:false;},_6Z=function(_70){return [0,function(_71,_72){return new F(function(){return _6P(_70,_71,_72);});},function(_71,_72){return new F(function(){return _6V(_70,_71,_72);});}];},_73=new T(function(){return B(_6Z(_6M));}),_74=function(_75,_76){var _77=E(_75);switch(_77[0]){case 0:return [0,function(_78){return new F(function(){return _74(B(A(_77[1],[_78])),_76);});}];case 1:return [1,function(_79){return new F(function(){return _74(B(A(_77[1],[_79])),_76);});}];case 2:return [2];case 3:return new F(function(){return _65(B(A(_76,[_77[1]])),new T(function(){return B(_74(_77[2],_76));}));});break;default:var _7a=function(_7b){var _7c=E(_7b);if(!_7c[0]){return [0];}else{var _7d=E(_7c[1]);return new F(function(){return _7(B(_5V(B(A(_76,[_7d[1]])),_7d[2])),new T(function(){return B(_7a(_7c[2]));}));});}},_7e=B(_7a(_77[1]));return _7e[0]==0?[2]:[4,_7e];}},_7f=[2],_7g=function(_7h){return [3,_7h,_7f];},_7i=function(_7j,_7k){var _7l=E(_7j);if(!_7l){return new F(function(){return A(_7k,[_J]);});}else{return [0,function(_7m){return E(new T(function(){return B(_7i(_7l-1|0,_7k));}));}];}},_7n=function(_7o,_7p,_7q){return [1,function(_7r){return new F(function(){return A(function(_7s,_7t,_7u){while(1){var _7v=(function(_7w,_7x,_7y){var _7z=E(_7w);switch(_7z[0]){case 0:var _7A=E(_7x);if(!_7A[0]){return E(_7p);}else{_7s=B(A(_7z[1],[_7A[1]]));_7t=_7A[2];var _7B=_7y+1|0;_7u=_7B;return null;}break;case 1:var _7C=B(A(_7z[1],[_7x])),_7D=_7x,_7B=_7y;_7s=_7C;_7t=_7D;_7u=_7B;return null;case 2:return E(_7p);case 3:return function(_7E){return new F(function(){return _7i(_7y,function(_7F){return E(new T(function(){return B(_74(_7z,_7E));}));});});};default:return function(_7G){return new F(function(){return _74(_7z,_7G);});};}})(_7s,_7t,_7u);if(_7v!=null){return _7v;}}},[new T(function(){return B(A(_7o,[_7g]));}),_7r,0,_7q]);});}];},_7H=[6],_7I=new T(function(){return B(unCStr("valDig: Bad base"));}),_7J=new T(function(){return B(err(_7I));}),_7K=function(_7L,_7M){var _7N=function(_7O,_7P){var _7Q=E(_7O);if(!_7Q[0]){return function(_7R){return new F(function(){return A(_7R,[new T(function(){return B(A(_7P,[_Q]));})]);});};}else{var _7S=E(_7Q[1])[1],_7T=function(_7U){return function(_7V){return [0,function(_7W){return E(new T(function(){return B(A(new T(function(){return B(_7N(_7Q[2],function(_7X){return new F(function(){return A(_7P,[[1,_7U,_7X]]);});}));}),[_7V]));}));}];};};switch(E(E(_7L)[1])){case 8:if(48>_7S){return function(_7Y){return new F(function(){return A(_7Y,[new T(function(){return B(A(_7P,[_Q]));})]);});};}else{if(_7S>55){return function(_7Z){return new F(function(){return A(_7Z,[new T(function(){return B(A(_7P,[_Q]));})]);});};}else{return new F(function(){return _7T([0,_7S-48|0]);});}}break;case 10:if(48>_7S){return function(_80){return new F(function(){return A(_80,[new T(function(){return B(A(_7P,[_Q]));})]);});};}else{if(_7S>57){return function(_81){return new F(function(){return A(_81,[new T(function(){return B(A(_7P,[_Q]));})]);});};}else{return new F(function(){return _7T([0,_7S-48|0]);});}}break;case 16:var _82=new T(function(){if(97>_7S){if(65>_7S){var _83=[0];}else{if(_7S>70){var _84=[0];}else{var _84=[1,[0,(_7S-65|0)+10|0]];}var _83=_84;}var _85=_83;}else{if(_7S>102){if(65>_7S){var _86=[0];}else{if(_7S>70){var _87=[0];}else{var _87=[1,[0,(_7S-65|0)+10|0]];}var _86=_87;}var _88=_86;}else{var _88=[1,[0,(_7S-97|0)+10|0]];}var _85=_88;}return _85;});if(48>_7S){var _89=E(_82);if(!_89[0]){return function(_8a){return new F(function(){return A(_8a,[new T(function(){return B(A(_7P,[_Q]));})]);});};}else{return new F(function(){return _7T(_89[1]);});}}else{if(_7S>57){var _8b=E(_82);if(!_8b[0]){return function(_8c){return new F(function(){return A(_8c,[new T(function(){return B(A(_7P,[_Q]));})]);});};}else{return new F(function(){return _7T(_8b[1]);});}}else{return new F(function(){return _7T([0,_7S-48|0]);});}}break;default:return E(_7J);}}};return [1,function(_8d){return new F(function(){return A(_7N,[_8d,_R,function(_8e){var _8f=E(_8e);return _8f[0]==0?[2]:B(A(_7M,[_8f]));}]);});}];},_8g=[0,10],_8h=[0,1],_8i=[0,2147483647],_8j=function(_8k,_8l){while(1){var _8m=E(_8k);if(!_8m[0]){var _8n=_8m[1],_8o=E(_8l);if(!_8o[0]){var _8p=_8o[1],_8q=addC(_8n,_8p);if(!E(_8q[2])){return [0,_8q[1]];}else{_8k=[1,I_fromInt(_8n)];_8l=[1,I_fromInt(_8p)];continue;}}else{_8k=[1,I_fromInt(_8n)];_8l=_8o;continue;}}else{var _8r=E(_8l);if(!_8r[0]){_8k=_8m;_8l=[1,I_fromInt(_8r[1])];continue;}else{return [1,I_add(_8m[1],_8r[1])];}}}},_8s=new T(function(){return B(_8j(_8i,_8h));}),_8t=function(_8u){var _8v=E(_8u);if(!_8v[0]){var _8w=E(_8v[1]);return _8w==(-2147483648)?E(_8s):[0, -_8w];}else{return [1,I_negate(_8v[1])];}},_8x=[0,10],_8y=[0,0],_8z=function(_8A){return [0,_8A];},_8B=function(_8C,_8D){while(1){var _8E=E(_8C);if(!_8E[0]){var _8F=_8E[1],_8G=E(_8D);if(!_8G[0]){var _8H=_8G[1];if(!(imul(_8F,_8H)|0)){return [0,imul(_8F,_8H)|0];}else{_8C=[1,I_fromInt(_8F)];_8D=[1,I_fromInt(_8H)];continue;}}else{_8C=[1,I_fromInt(_8F)];_8D=_8G;continue;}}else{var _8I=E(_8D);if(!_8I[0]){_8C=_8E;_8D=[1,I_fromInt(_8I[1])];continue;}else{return [1,I_mul(_8E[1],_8I[1])];}}}},_8J=function(_8K,_8L,_8M){while(1){var _8N=E(_8M);if(!_8N[0]){return E(_8L);}else{var _8O=B(_8j(B(_8B(_8L,_8K)),B(_8z(E(_8N[1])[1]))));_8M=_8N[2];_8L=_8O;continue;}}},_8P=function(_8Q){var _8R=new T(function(){return B(_65(B(_65([0,function(_8S){if(E(E(_8S)[1])==45){return new F(function(){return _7K(_8g,function(_8T){return new F(function(){return A(_8Q,[[1,new T(function(){return B(_8t(B(_8J(_8x,_8y,_8T))));})]]);});});});}else{return [2];}}],[0,function(_8U){if(E(E(_8U)[1])==43){return new F(function(){return _7K(_8g,function(_8V){return new F(function(){return A(_8Q,[[1,new T(function(){return B(_8J(_8x,_8y,_8V));})]]);});});});}else{return [2];}}])),new T(function(){return B(_7K(_8g,function(_8W){return new F(function(){return A(_8Q,[[1,new T(function(){return B(_8J(_8x,_8y,_8W));})]]);});}));})));});return new F(function(){return _65([0,function(_8X){return E(E(_8X)[1])==101?E(_8R):[2];}],[0,function(_8Y){return E(E(_8Y)[1])==69?E(_8R):[2];}]);});},_8Z=function(_90){return new F(function(){return A(_90,[_46]);});},_91=function(_92){return new F(function(){return A(_92,[_46]);});},_93=function(_94){return [0,function(_95){return E(E(_95)[1])==46?E(new T(function(){return B(_7K(_8g,function(_96){return new F(function(){return A(_94,[[1,_96]]);});}));})):[2];}];},_97=function(_98){return new F(function(){return _7K(_8g,function(_99){return new F(function(){return _7n(_93,_8Z,function(_9a){return new F(function(){return _7n(_8P,_91,function(_9b){return new F(function(){return A(_98,[[5,[1,_99,_9a,_9b]]]);});});});});});});});},_9c=function(_9d,_9e,_9f){while(1){var _9g=E(_9f);if(!_9g[0]){return false;}else{if(!B(A(_6N,[_9d,_9e,_9g[1]]))){_9f=_9g[2];continue;}else{return true;}}}},_9h=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_9i=function(_9j){return new F(function(){return _9c(_6M,_9j,_9h);});},_9k=[0,8],_9l=[0,16],_9m=function(_9n){return [0,function(_9o){return E(E(_9o)[1])==48?E([0,function(_9p){switch(E(E(_9p)[1])){case 79:return E(new T(function(){return B(_7K(_9k,function(_9q){return new F(function(){return A(_9n,[[5,[0,_9k,_9q]]]);});}));}));case 88:return E(new T(function(){return B(_7K(_9l,function(_9r){return new F(function(){return A(_9n,[[5,[0,_9l,_9r]]]);});}));}));case 111:return E(new T(function(){return B(_7K(_9k,function(_9s){return new F(function(){return A(_9n,[[5,[0,_9k,_9s]]]);});}));}));case 120:return E(new T(function(){return B(_7K(_9l,function(_9t){return new F(function(){return A(_9n,[[5,[0,_9l,_9t]]]);});}));}));default:return [2];}}]):[2];}];},_9u=false,_9v=true,_9w=function(_9x){return [0,function(_9y){switch(E(E(_9y)[1])){case 79:return E(new T(function(){return B(A(_9x,[_9k]));}));case 88:return E(new T(function(){return B(A(_9x,[_9l]));}));case 111:return E(new T(function(){return B(A(_9x,[_9k]));}));case 120:return E(new T(function(){return B(A(_9x,[_9l]));}));default:return [2];}}];},_9z=function(_9A){return new F(function(){return A(_9A,[_8g]);});},_9B=function(_9C){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_i(9,_9C,_Q));}))));});},_9D=function(_9E){var _9F=E(_9E);return _9F[0]==0?E(_9F[1]):I_toInt(_9F[1]);},_9G=function(_9H,_9I){var _9J=E(_9H);if(!_9J[0]){var _9K=_9J[1],_9L=E(_9I);return _9L[0]==0?_9K<=_9L[1]:I_compareInt(_9L[1],_9K)>=0;}else{var _9M=_9J[1],_9N=E(_9I);return _9N[0]==0?I_compareInt(_9M,_9N[1])<=0:I_compare(_9M,_9N[1])<=0;}},_9O=function(_9P){return [2];},_9Q=function(_9R){var _9S=E(_9R);if(!_9S[0]){return E(_9O);}else{var _9T=_9S[1],_9U=E(_9S[2]);return _9U[0]==0?E(_9T):function(_9V){return new F(function(){return _65(B(A(_9T,[_9V])),new T(function(){return B(A(new T(function(){return B(_9Q(_9U));}),[_9V]));}));});};}},_9W=new T(function(){return B(unCStr("NUL"));}),_9X=function(_9Y){return [2];},_9Z=function(_a0){return new F(function(){return _9X(_a0);});},_a1=function(_a2,_a3){var _a4=function(_a5,_a6){var _a7=E(_a5);if(!_a7[0]){return function(_a8){return new F(function(){return A(_a8,[_a2]);});};}else{var _a9=E(_a6);return _a9[0]==0?E(_9X):E(_a7[1])[1]!=E(_a9[1])[1]?E(_9Z):function(_aa){return [0,function(_ab){return E(new T(function(){return B(A(new T(function(){return B(_a4(_a7[2],_a9[2]));}),[_aa]));}));}];};}};return [1,function(_ac){return new F(function(){return A(_a4,[_a2,_ac,_a3]);});}];},_ad=[0,0],_ae=function(_af){return new F(function(){return _a1(_9W,function(_ag){return E(new T(function(){return B(A(_af,[_ad]));}));});});},_ah=new T(function(){return B(unCStr("STX"));}),_ai=[0,2],_aj=function(_ak){return new F(function(){return _a1(_ah,function(_al){return E(new T(function(){return B(A(_ak,[_ai]));}));});});},_am=new T(function(){return B(unCStr("ETX"));}),_an=[0,3],_ao=function(_ap){return new F(function(){return _a1(_am,function(_aq){return E(new T(function(){return B(A(_ap,[_an]));}));});});},_ar=new T(function(){return B(unCStr("EOT"));}),_as=[0,4],_at=function(_au){return new F(function(){return _a1(_ar,function(_av){return E(new T(function(){return B(A(_au,[_as]));}));});});},_aw=new T(function(){return B(unCStr("ENQ"));}),_ax=[0,5],_ay=function(_az){return new F(function(){return _a1(_aw,function(_aA){return E(new T(function(){return B(A(_az,[_ax]));}));});});},_aB=new T(function(){return B(unCStr("ACK"));}),_aC=[0,6],_aD=function(_aE){return new F(function(){return _a1(_aB,function(_aF){return E(new T(function(){return B(A(_aE,[_aC]));}));});});},_aG=new T(function(){return B(unCStr("BEL"));}),_aH=[0,7],_aI=function(_aJ){return new F(function(){return _a1(_aG,function(_aK){return E(new T(function(){return B(A(_aJ,[_aH]));}));});});},_aL=new T(function(){return B(unCStr("BS"));}),_aM=[0,8],_aN=function(_aO){return new F(function(){return _a1(_aL,function(_aP){return E(new T(function(){return B(A(_aO,[_aM]));}));});});},_aQ=new T(function(){return B(unCStr("HT"));}),_aR=[0,9],_aS=function(_aT){return new F(function(){return _a1(_aQ,function(_aU){return E(new T(function(){return B(A(_aT,[_aR]));}));});});},_aV=new T(function(){return B(unCStr("LF"));}),_aW=[0,10],_aX=function(_aY){return new F(function(){return _a1(_aV,function(_aZ){return E(new T(function(){return B(A(_aY,[_aW]));}));});});},_b0=new T(function(){return B(unCStr("VT"));}),_b1=[0,11],_b2=function(_b3){return new F(function(){return _a1(_b0,function(_b4){return E(new T(function(){return B(A(_b3,[_b1]));}));});});},_b5=new T(function(){return B(unCStr("FF"));}),_b6=[0,12],_b7=function(_b8){return new F(function(){return _a1(_b5,function(_b9){return E(new T(function(){return B(A(_b8,[_b6]));}));});});},_ba=new T(function(){return B(unCStr("CR"));}),_bb=[0,13],_bc=function(_bd){return new F(function(){return _a1(_ba,function(_be){return E(new T(function(){return B(A(_bd,[_bb]));}));});});},_bf=new T(function(){return B(unCStr("SI"));}),_bg=[0,15],_bh=function(_bi){return new F(function(){return _a1(_bf,function(_bj){return E(new T(function(){return B(A(_bi,[_bg]));}));});});},_bk=new T(function(){return B(unCStr("DLE"));}),_bl=[0,16],_bm=function(_bn){return new F(function(){return _a1(_bk,function(_bo){return E(new T(function(){return B(A(_bn,[_bl]));}));});});},_bp=new T(function(){return B(unCStr("DC1"));}),_bq=[0,17],_br=function(_bs){return new F(function(){return _a1(_bp,function(_bt){return E(new T(function(){return B(A(_bs,[_bq]));}));});});},_bu=new T(function(){return B(unCStr("DC2"));}),_bv=[0,18],_bw=function(_bx){return new F(function(){return _a1(_bu,function(_by){return E(new T(function(){return B(A(_bx,[_bv]));}));});});},_bz=new T(function(){return B(unCStr("DC3"));}),_bA=[0,19],_bB=function(_bC){return new F(function(){return _a1(_bz,function(_bD){return E(new T(function(){return B(A(_bC,[_bA]));}));});});},_bE=new T(function(){return B(unCStr("DC4"));}),_bF=[0,20],_bG=function(_bH){return new F(function(){return _a1(_bE,function(_bI){return E(new T(function(){return B(A(_bH,[_bF]));}));});});},_bJ=new T(function(){return B(unCStr("NAK"));}),_bK=[0,21],_bL=function(_bM){return new F(function(){return _a1(_bJ,function(_bN){return E(new T(function(){return B(A(_bM,[_bK]));}));});});},_bO=new T(function(){return B(unCStr("SYN"));}),_bP=[0,22],_bQ=function(_bR){return new F(function(){return _a1(_bO,function(_bS){return E(new T(function(){return B(A(_bR,[_bP]));}));});});},_bT=new T(function(){return B(unCStr("ETB"));}),_bU=[0,23],_bV=function(_bW){return new F(function(){return _a1(_bT,function(_bX){return E(new T(function(){return B(A(_bW,[_bU]));}));});});},_bY=new T(function(){return B(unCStr("CAN"));}),_bZ=[0,24],_c0=function(_c1){return new F(function(){return _a1(_bY,function(_c2){return E(new T(function(){return B(A(_c1,[_bZ]));}));});});},_c3=new T(function(){return B(unCStr("EM"));}),_c4=[0,25],_c5=function(_c6){return new F(function(){return _a1(_c3,function(_c7){return E(new T(function(){return B(A(_c6,[_c4]));}));});});},_c8=new T(function(){return B(unCStr("SUB"));}),_c9=[0,26],_ca=function(_cb){return new F(function(){return _a1(_c8,function(_cc){return E(new T(function(){return B(A(_cb,[_c9]));}));});});},_cd=new T(function(){return B(unCStr("ESC"));}),_ce=[0,27],_cf=function(_cg){return new F(function(){return _a1(_cd,function(_ch){return E(new T(function(){return B(A(_cg,[_ce]));}));});});},_ci=new T(function(){return B(unCStr("FS"));}),_cj=[0,28],_ck=function(_cl){return new F(function(){return _a1(_ci,function(_cm){return E(new T(function(){return B(A(_cl,[_cj]));}));});});},_cn=new T(function(){return B(unCStr("GS"));}),_co=[0,29],_cp=function(_cq){return new F(function(){return _a1(_cn,function(_cr){return E(new T(function(){return B(A(_cq,[_co]));}));});});},_cs=new T(function(){return B(unCStr("RS"));}),_ct=[0,30],_cu=function(_cv){return new F(function(){return _a1(_cs,function(_cw){return E(new T(function(){return B(A(_cv,[_ct]));}));});});},_cx=new T(function(){return B(unCStr("US"));}),_cy=[0,31],_cz=function(_cA){return new F(function(){return _a1(_cx,function(_cB){return E(new T(function(){return B(A(_cA,[_cy]));}));});});},_cC=new T(function(){return B(unCStr("SP"));}),_cD=[0,32],_cE=function(_cF){return new F(function(){return _a1(_cC,function(_cG){return E(new T(function(){return B(A(_cF,[_cD]));}));});});},_cH=new T(function(){return B(unCStr("DEL"));}),_cI=[0,127],_cJ=function(_cK){return new F(function(){return _a1(_cH,function(_cL){return E(new T(function(){return B(A(_cK,[_cI]));}));});});},_cM=[1,_cJ,_Q],_cN=[1,_cE,_cM],_cO=[1,_cz,_cN],_cP=[1,_cu,_cO],_cQ=[1,_cp,_cP],_cR=[1,_ck,_cQ],_cS=[1,_cf,_cR],_cT=[1,_ca,_cS],_cU=[1,_c5,_cT],_cV=[1,_c0,_cU],_cW=[1,_bV,_cV],_cX=[1,_bQ,_cW],_cY=[1,_bL,_cX],_cZ=[1,_bG,_cY],_d0=[1,_bB,_cZ],_d1=[1,_bw,_d0],_d2=[1,_br,_d1],_d3=[1,_bm,_d2],_d4=[1,_bh,_d3],_d5=[1,_bc,_d4],_d6=[1,_b7,_d5],_d7=[1,_b2,_d6],_d8=[1,_aX,_d7],_d9=[1,_aS,_d8],_da=[1,_aN,_d9],_db=[1,_aI,_da],_dc=[1,_aD,_db],_dd=[1,_ay,_dc],_de=[1,_at,_dd],_df=[1,_ao,_de],_dg=[1,_aj,_df],_dh=[1,_ae,_dg],_di=new T(function(){return B(unCStr("SOH"));}),_dj=[0,1],_dk=function(_dl){return new F(function(){return _a1(_di,function(_dm){return E(new T(function(){return B(A(_dl,[_dj]));}));});});},_dn=new T(function(){return B(unCStr("SO"));}),_do=[0,14],_dp=function(_dq){return new F(function(){return _a1(_dn,function(_dr){return E(new T(function(){return B(A(_dq,[_do]));}));});});},_ds=function(_dt){return new F(function(){return _7n(_dk,_dp,_dt);});},_du=[1,_ds,_dh],_dv=new T(function(){return B(_9Q(_du));}),_dw=[0,1114111],_dx=[0,34],_dy=[0,_dx,_9v],_dz=[0,39],_dA=[0,_dz,_9v],_dB=[0,92],_dC=[0,_dB,_9v],_dD=[0,_aH,_9v],_dE=[0,_aM,_9v],_dF=[0,_b6,_9v],_dG=[0,_aW,_9v],_dH=[0,_bb,_9v],_dI=[0,_aR,_9v],_dJ=[0,_b1,_9v],_dK=[0,_ad,_9v],_dL=[0,_dj,_9v],_dM=[0,_ai,_9v],_dN=[0,_an,_9v],_dO=[0,_as,_9v],_dP=[0,_ax,_9v],_dQ=[0,_aC,_9v],_dR=[0,_aH,_9v],_dS=[0,_aM,_9v],_dT=[0,_aR,_9v],_dU=[0,_aW,_9v],_dV=[0,_b1,_9v],_dW=[0,_b6,_9v],_dX=[0,_bb,_9v],_dY=[0,_do,_9v],_dZ=[0,_bg,_9v],_e0=[0,_bl,_9v],_e1=[0,_bq,_9v],_e2=[0,_bv,_9v],_e3=[0,_bA,_9v],_e4=[0,_bF,_9v],_e5=[0,_bK,_9v],_e6=[0,_bP,_9v],_e7=[0,_bU,_9v],_e8=[0,_bZ,_9v],_e9=[0,_c4,_9v],_ea=[0,_c9,_9v],_eb=[0,_ce,_9v],_ec=[0,_cj,_9v],_ed=[0,_co,_9v],_ee=[0,_ct,_9v],_ef=[0,_cy,_9v],_eg=function(_eh){return new F(function(){return _65([0,function(_ei){switch(E(E(_ei)[1])){case 34:return E(new T(function(){return B(A(_eh,[_dy]));}));case 39:return E(new T(function(){return B(A(_eh,[_dA]));}));case 92:return E(new T(function(){return B(A(_eh,[_dC]));}));case 97:return E(new T(function(){return B(A(_eh,[_dD]));}));case 98:return E(new T(function(){return B(A(_eh,[_dE]));}));case 102:return E(new T(function(){return B(A(_eh,[_dF]));}));case 110:return E(new T(function(){return B(A(_eh,[_dG]));}));case 114:return E(new T(function(){return B(A(_eh,[_dH]));}));case 116:return E(new T(function(){return B(A(_eh,[_dI]));}));case 118:return E(new T(function(){return B(A(_eh,[_dJ]));}));default:return [2];}}],new T(function(){return B(_65(B(_7n(_9w,_9z,function(_ej){return new F(function(){return _7K(_ej,function(_ek){var _el=B(_8J(new T(function(){return B(_8z(E(_ej)[1]));}),_8y,_ek));return !B(_9G(_el,_dw))?[2]:B(A(_eh,[[0,new T(function(){var _em=B(_9D(_el));if(_em>>>0>1114111){var _en=B(_9B(_em));}else{var _en=[0,_em];}var _eo=_en,_ep=_eo;return _ep;}),_9v]]));});});})),new T(function(){return B(_65([0,function(_eq){return E(E(_eq)[1])==94?E([0,function(_er){switch(E(E(_er)[1])){case 64:return E(new T(function(){return B(A(_eh,[_dK]));}));case 65:return E(new T(function(){return B(A(_eh,[_dL]));}));case 66:return E(new T(function(){return B(A(_eh,[_dM]));}));case 67:return E(new T(function(){return B(A(_eh,[_dN]));}));case 68:return E(new T(function(){return B(A(_eh,[_dO]));}));case 69:return E(new T(function(){return B(A(_eh,[_dP]));}));case 70:return E(new T(function(){return B(A(_eh,[_dQ]));}));case 71:return E(new T(function(){return B(A(_eh,[_dR]));}));case 72:return E(new T(function(){return B(A(_eh,[_dS]));}));case 73:return E(new T(function(){return B(A(_eh,[_dT]));}));case 74:return E(new T(function(){return B(A(_eh,[_dU]));}));case 75:return E(new T(function(){return B(A(_eh,[_dV]));}));case 76:return E(new T(function(){return B(A(_eh,[_dW]));}));case 77:return E(new T(function(){return B(A(_eh,[_dX]));}));case 78:return E(new T(function(){return B(A(_eh,[_dY]));}));case 79:return E(new T(function(){return B(A(_eh,[_dZ]));}));case 80:return E(new T(function(){return B(A(_eh,[_e0]));}));case 81:return E(new T(function(){return B(A(_eh,[_e1]));}));case 82:return E(new T(function(){return B(A(_eh,[_e2]));}));case 83:return E(new T(function(){return B(A(_eh,[_e3]));}));case 84:return E(new T(function(){return B(A(_eh,[_e4]));}));case 85:return E(new T(function(){return B(A(_eh,[_e5]));}));case 86:return E(new T(function(){return B(A(_eh,[_e6]));}));case 87:return E(new T(function(){return B(A(_eh,[_e7]));}));case 88:return E(new T(function(){return B(A(_eh,[_e8]));}));case 89:return E(new T(function(){return B(A(_eh,[_e9]));}));case 90:return E(new T(function(){return B(A(_eh,[_ea]));}));case 91:return E(new T(function(){return B(A(_eh,[_eb]));}));case 92:return E(new T(function(){return B(A(_eh,[_ec]));}));case 93:return E(new T(function(){return B(A(_eh,[_ed]));}));case 94:return E(new T(function(){return B(A(_eh,[_ee]));}));case 95:return E(new T(function(){return B(A(_eh,[_ef]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_dv,[function(_es){return new F(function(){return A(_eh,[[0,_es,_9v]]);});}]));})));})));}));});},_et=function(_eu){return new F(function(){return A(_eu,[_J]);});},_ev=function(_ew){var _ex=E(_ew);if(!_ex[0]){return E(_et);}else{var _ey=_ex[2],_ez=E(E(_ex[1])[1]);switch(_ez){case 9:return function(_eA){return [0,function(_eB){return E(new T(function(){return B(A(new T(function(){return B(_ev(_ey));}),[_eA]));}));}];};case 10:return function(_eC){return [0,function(_eD){return E(new T(function(){return B(A(new T(function(){return B(_ev(_ey));}),[_eC]));}));}];};case 11:return function(_eE){return [0,function(_eF){return E(new T(function(){return B(A(new T(function(){return B(_ev(_ey));}),[_eE]));}));}];};case 12:return function(_eG){return [0,function(_eH){return E(new T(function(){return B(A(new T(function(){return B(_ev(_ey));}),[_eG]));}));}];};case 13:return function(_eI){return [0,function(_eJ){return E(new T(function(){return B(A(new T(function(){return B(_ev(_ey));}),[_eI]));}));}];};case 32:return function(_eK){return [0,function(_eL){return E(new T(function(){return B(A(new T(function(){return B(_ev(_ey));}),[_eK]));}));}];};case 160:return function(_eM){return [0,function(_eN){return E(new T(function(){return B(A(new T(function(){return B(_ev(_ey));}),[_eM]));}));}];};default:var _eO=u_iswspace(_ez),_eP=_eO;return E(_eP)==0?E(_et):function(_eQ){return [0,function(_eR){return E(new T(function(){return B(A(new T(function(){return B(_ev(_ey));}),[_eQ]));}));}];};}}},_eS=function(_eT){var _eU=new T(function(){return B(_eS(_eT));}),_eV=[1,function(_eW){return new F(function(){return A(_ev,[_eW,function(_eX){return E([0,function(_eY){return E(E(_eY)[1])==92?E(_eU):[2];}]);}]);});}];return new F(function(){return _65([0,function(_eZ){return E(E(_eZ)[1])==92?E([0,function(_f0){var _f1=E(E(_f0)[1]);switch(_f1){case 9:return E(_eV);case 10:return E(_eV);case 11:return E(_eV);case 12:return E(_eV);case 13:return E(_eV);case 32:return E(_eV);case 38:return E(_eU);case 160:return E(_eV);default:var _f2=u_iswspace(_f1),_f3=_f2;return E(_f3)==0?[2]:E(_eV);}}]):[2];}],[0,function(_f4){var _f5=E(_f4);return E(_f5[1])==92?E(new T(function(){return B(_eg(_eT));})):B(A(_eT,[[0,_f5,_9u]]));}]);});},_f6=function(_f7,_f8){return new F(function(){return _eS(function(_f9){var _fa=E(_f9),_fb=E(_fa[1]);if(E(_fb[1])==34){if(!E(_fa[2])){return E(new T(function(){return B(A(_f8,[[1,new T(function(){return B(A(_f7,[_Q]));})]]));}));}else{return new F(function(){return _f6(function(_fc){return new F(function(){return A(_f7,[[1,_fb,_fc]]);});},_f8);});}}else{return new F(function(){return _f6(function(_fd){return new F(function(){return A(_f7,[[1,_fb,_fd]]);});},_f8);});}});});},_fe=new T(function(){return B(unCStr("_\'"));}),_ff=function(_fg){var _fh=u_iswalnum(_fg),_fi=_fh;return E(_fi)==0?B(_9c(_6M,[0,_fg],_fe)):true;},_fj=function(_fk){return new F(function(){return _ff(E(_fk)[1]);});},_fl=new T(function(){return B(unCStr(",;()[]{}`"));}),_fm=function(_fn){return new F(function(){return A(_fn,[_Q]);});},_fo=function(_fp,_fq){var _fr=function(_fs){var _ft=E(_fs);if(!_ft[0]){return E(_fm);}else{var _fu=_ft[1];return !B(A(_fp,[_fu]))?E(_fm):function(_fv){return [0,function(_fw){return E(new T(function(){return B(A(new T(function(){return B(_fr(_ft[2]));}),[function(_fx){return new F(function(){return A(_fv,[[1,_fu,_fx]]);});}]));}));}];};}};return [1,function(_fy){return new F(function(){return A(_fr,[_fy,_fq]);});}];},_fz=new T(function(){return B(unCStr(".."));}),_fA=new T(function(){return B(unCStr("::"));}),_fB=new T(function(){return B(unCStr("->"));}),_fC=[0,64],_fD=[1,_fC,_Q],_fE=[0,126],_fF=[1,_fE,_Q],_fG=new T(function(){return B(unCStr("=>"));}),_fH=[1,_fG,_Q],_fI=[1,_fF,_fH],_fJ=[1,_fD,_fI],_fK=[1,_fB,_fJ],_fL=new T(function(){return B(unCStr("<-"));}),_fM=[1,_fL,_fK],_fN=[0,124],_fO=[1,_fN,_Q],_fP=[1,_fO,_fM],_fQ=[1,_dB,_Q],_fR=[1,_fQ,_fP],_fS=[0,61],_fT=[1,_fS,_Q],_fU=[1,_fT,_fR],_fV=[1,_fA,_fU],_fW=[1,_fz,_fV],_fX=function(_fY){return new F(function(){return _65([1,function(_fZ){return E(_fZ)[0]==0?E(new T(function(){return B(A(_fY,[_7H]));})):[2];}],new T(function(){return B(_65([0,function(_g0){return E(E(_g0)[1])==39?E([0,function(_g1){var _g2=E(_g1);switch(E(_g2[1])){case 39:return [2];case 92:return E(new T(function(){return B(_eg(function(_g3){var _g4=E(_g3);return new F(function(){return (function(_g5,_g6){var _g7=new T(function(){return B(A(_fY,[[0,_g5]]));});return !E(_g6)?E(E(_g5)[1])==39?[2]:[0,function(_g8){return E(E(_g8)[1])==39?E(_g7):[2];}]:[0,function(_g9){return E(E(_g9)[1])==39?E(_g7):[2];}];})(_g4[1],_g4[2]);});}));}));default:return [0,function(_ga){return E(E(_ga)[1])==39?E(new T(function(){return B(A(_fY,[[0,_g2]]));})):[2];}];}}]):[2];}],new T(function(){return B(_65([0,function(_gb){return E(E(_gb)[1])==34?E(new T(function(){return B(_f6(_R,_fY));})):[2];}],new T(function(){return B(_65([0,function(_gc){return !B(_9c(_6M,_gc,_fl))?[2]:B(A(_fY,[[2,[1,_gc,_Q]]]));}],new T(function(){return B(_65([0,function(_gd){if(!B(_9c(_6M,_gd,_9h))){return [2];}else{return new F(function(){return _fo(_9i,function(_ge){var _gf=[1,_gd,_ge];return !B(_9c(_73,_gf,_fW))?B(A(_fY,[[4,_gf]])):B(A(_fY,[[2,_gf]]));});});}}],new T(function(){return B(_65([0,function(_gg){var _gh=E(_gg),_gi=_gh[1],_gj=u_iswalpha(_gi),_gk=_gj;if(!E(_gk)){if(E(_gi)==95){return new F(function(){return _fo(_fj,function(_gl){return new F(function(){return A(_fY,[[3,[1,_gh,_gl]]]);});});});}else{return [2];}}else{return new F(function(){return _fo(_fj,function(_gm){return new F(function(){return A(_fY,[[3,[1,_gh,_gm]]]);});});});}}],new T(function(){return B(_7n(_9m,_97,_fY));})));})));})));})));})));}));});},_gn=function(_go){return [1,function(_gp){return new F(function(){return A(_ev,[_gp,function(_gq){return E(new T(function(){return B(_fX(_go));}));}]);});}];},_gr=[0,0],_gs=function(_gt,_gu){return new F(function(){return _gn(function(_gv){var _gw=E(_gv);if(_gw[0]==2){var _gx=E(_gw[1]);return _gx[0]==0?[2]:E(E(_gx[1])[1])==40?E(_gx[2])[0]==0?E(new T(function(){return B(A(_gt,[_gr,function(_gy){return new F(function(){return _gn(function(_gz){var _gA=E(_gz);if(_gA[0]==2){var _gB=E(_gA[1]);return _gB[0]==0?[2]:E(E(_gB[1])[1])==41?E(_gB[2])[0]==0?E(new T(function(){return B(A(_gu,[_gy]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_gC=function(_gD,_gE,_gF){var _gG=function(_gH,_gI){return new F(function(){return _65(B(_gn(function(_gJ){var _gK=E(_gJ);if(_gK[0]==4){var _gL=E(_gK[1]);if(!_gL[0]){return new F(function(){return A(_gD,[_gK,_gH,_gI]);});}else{return E(E(_gL[1])[1])==45?E(_gL[2])[0]==0?E([1,function(_gM){return new F(function(){return A(_ev,[_gM,function(_gN){return E(new T(function(){return B(_fX(function(_gO){return new F(function(){return A(_gD,[_gO,_gH,function(_gP){return new F(function(){return A(_gI,[new T(function(){return [0, -E(_gP)[1]];})]);});}]);});}));}));}]);});}]):B(A(_gD,[_gK,_gH,_gI])):B(A(_gD,[_gK,_gH,_gI]));}}else{return new F(function(){return A(_gD,[_gK,_gH,_gI]);});}})),new T(function(){return B(_gs(_gG,_gI));}));});};return new F(function(){return _gG(_gE,_gF);});},_gQ=function(_gR,_gS){return [2];},_gT=function(_gU,_gV){return new F(function(){return _gQ(_gU,_gV);});},_gW=function(_gX){var _gY=E(_gX);return _gY[0]==0?[1,new T(function(){return B(_8J(new T(function(){return B(_8z(E(_gY[1])[1]));}),_8y,_gY[2]));})]:E(_gY[2])[0]==0?E(_gY[3])[0]==0?[1,new T(function(){return B(_8J(_8x,_8y,_gY[1]));})]:[0]:[0];},_gZ=function(_h0){var _h1=E(_h0);if(_h1[0]==5){var _h2=B(_gW(_h1[1]));return _h2[0]==0?E(_gQ):function(_h3,_h4){return new F(function(){return A(_h4,[new T(function(){return [0,B(_9D(_h2[1]))];})]);});};}else{return E(_gT);}},_h5=function(_h6,_h7){while(1){var _h8=E(_h6);if(!_h8[0]){return E(_h7)[0]==0?true:false;}else{var _h9=E(_h7);if(!_h9[0]){return false;}else{if(E(_h8[1])[1]!=E(_h9[1])[1]){return false;}else{_h6=_h8[2];_h7=_h9[2];continue;}}}}},_ha=new T(function(){return B(unCStr("onSideIndex"));}),_hb=new T(function(){return B(unCStr("LeftSidePlacement"));}),_hc=new T(function(){return B(unCStr("RightSidePlacement"));}),_hd=function(_he,_hf){var _hg=new T(function(){if(_he>11){var _hh=[2];}else{var _hh=[1,function(_hi){return new F(function(){return A(_ev,[_hi,function(_hj){return E(new T(function(){return B(_fX(function(_hk){var _hl=E(_hk);return _hl[0]==3?!B(_h5(_hl[1],_hc))?[2]:E([1,function(_hm){return new F(function(){return A(_ev,[_hm,function(_hn){return E(new T(function(){return B(_fX(function(_ho){var _hp=E(_ho);if(_hp[0]==2){var _hq=E(_hp[1]);return _hq[0]==0?[2]:E(E(_hq[1])[1])==123?E(_hq[2])[0]==0?E([1,function(_hr){return new F(function(){return A(_ev,[_hr,function(_hs){return E(new T(function(){return B(_fX(function(_ht){var _hu=E(_ht);return _hu[0]==3?!B(_h5(_hu[1],_ha))?[2]:E([1,function(_hv){return new F(function(){return A(_ev,[_hv,function(_hw){return E(new T(function(){return B(_fX(function(_hx){var _hy=E(_hx);if(_hy[0]==2){var _hz=E(_hy[1]);return _hz[0]==0?[2]:E(E(_hz[1])[1])==61?E(_hz[2])[0]==0?E(new T(function(){return B(_gC(_gZ,_gr,function(_hA){return new F(function(){return _gn(function(_hB){var _hC=E(_hB);if(_hC[0]==2){var _hD=E(_hC[1]);return _hD[0]==0?[2]:E(E(_hD[1])[1])==125?E(_hD[2])[0]==0?E(new T(function(){return B(A(_hf,[[3,_hA]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}];}return _hh;});if(_he>11){return new F(function(){return _65(_7f,_hg);});}else{return new F(function(){return _65(B(_gn(function(_hE){var _hF=E(_hE);return _hF[0]==3?!B(_h5(_hF[1],_hb))?[2]:E([1,function(_hG){return new F(function(){return A(_ev,[_hG,function(_hH){return E(new T(function(){return B(_fX(function(_hI){var _hJ=E(_hI);if(_hJ[0]==2){var _hK=E(_hJ[1]);return _hK[0]==0?[2]:E(E(_hK[1])[1])==123?E(_hK[2])[0]==0?E([1,function(_hL){return new F(function(){return A(_ev,[_hL,function(_hM){return E(new T(function(){return B(_fX(function(_hN){var _hO=E(_hN);return _hO[0]==3?!B(_h5(_hO[1],_ha))?[2]:E([1,function(_hP){return new F(function(){return A(_ev,[_hP,function(_hQ){return E(new T(function(){return B(_fX(function(_hR){var _hS=E(_hR);if(_hS[0]==2){var _hT=E(_hS[1]);return _hT[0]==0?[2]:E(E(_hT[1])[1])==61?E(_hT[2])[0]==0?E(new T(function(){return B(_gC(_gZ,_gr,function(_hU){return new F(function(){return _gn(function(_hV){var _hW=E(_hV);if(_hW[0]==2){var _hX=E(_hW[1]);return _hX[0]==0?[2]:E(E(_hX[1])[1])==125?E(_hX[2])[0]==0?E(new T(function(){return B(A(_hf,[[2,_hU]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),_hg);});}},_hY=new T(function(){return B(unCStr("onBarIndex"));}),_hZ=new T(function(){return B(unCStr("BarPlacement"));}),_i0=function(_i1,_i2){if(_i1>11){return new F(function(){return _65(_7f,new T(function(){return B(_hd(_i1,_i2));}));});}else{return new F(function(){return _65(B(_gn(function(_i3){var _i4=E(_i3);return _i4[0]==3?!B(_h5(_i4[1],_hZ))?[2]:E([1,function(_i5){return new F(function(){return A(_ev,[_i5,function(_i6){return E(new T(function(){return B(_fX(function(_i7){var _i8=E(_i7);if(_i8[0]==2){var _i9=E(_i8[1]);return _i9[0]==0?[2]:E(E(_i9[1])[1])==123?E(_i9[2])[0]==0?E([1,function(_ia){return new F(function(){return A(_ev,[_ia,function(_ib){return E(new T(function(){return B(_fX(function(_ic){var _id=E(_ic);return _id[0]==3?!B(_h5(_id[1],_hY))?[2]:E([1,function(_ie){return new F(function(){return A(_ev,[_ie,function(_if){return E(new T(function(){return B(_fX(function(_ig){var _ih=E(_ig);if(_ih[0]==2){var _ii=E(_ih[1]);return _ii[0]==0?[2]:E(E(_ii[1])[1])==61?E(_ii[2])[0]==0?E(new T(function(){return B(_gC(_gZ,_gr,function(_ij){return new F(function(){return _gn(function(_ik){var _il=E(_ik);if(_il[0]==2){var _im=E(_il[1]);return _im[0]==0?[2]:E(E(_im[1])[1])==125?E(_im[2])[0]==0?E(new T(function(){return B(A(_i2,[[1,_ij]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_hd(_i1,_i2));}));});}},_in=new T(function(){return B(unCStr("onPointIndex"));}),_io=new T(function(){return B(unCStr("pointIndex"));}),_ip=new T(function(){return B(unCStr("PointPlacement"));}),_iq=function(_ir,_is){if(_ir>11){return new F(function(){return _65(_7f,new T(function(){return B(_i0(_ir,_is));}));});}else{return new F(function(){return _65(B(_gn(function(_it){var _iu=E(_it);return _iu[0]==3?!B(_h5(_iu[1],_ip))?[2]:E([1,function(_iv){return new F(function(){return A(_ev,[_iv,function(_iw){return E(new T(function(){return B(_fX(function(_ix){var _iy=E(_ix);if(_iy[0]==2){var _iz=E(_iy[1]);return _iz[0]==0?[2]:E(E(_iz[1])[1])==123?E(_iz[2])[0]==0?E([1,function(_iA){return new F(function(){return A(_ev,[_iA,function(_iB){return E(new T(function(){return B(_fX(function(_iC){var _iD=E(_iC);return _iD[0]==3?!B(_h5(_iD[1],_io))?[2]:E([1,function(_iE){return new F(function(){return A(_ev,[_iE,function(_iF){return E(new T(function(){return B(_fX(function(_iG){var _iH=E(_iG);if(_iH[0]==2){var _iI=E(_iH[1]);return _iI[0]==0?[2]:E(E(_iI[1])[1])==61?E(_iI[2])[0]==0?E(new T(function(){return B(_gC(_gZ,_gr,function(_iJ){return new F(function(){return _gn(function(_iK){var _iL=E(_iK);if(_iL[0]==2){var _iM=E(_iL[1]);return _iM[0]==0?[2]:E(E(_iM[1])[1])==44?E(_iM[2])[0]==0?E([1,function(_iN){return new F(function(){return A(_ev,[_iN,function(_iO){return E(new T(function(){return B(_fX(function(_iP){var _iQ=E(_iP);return _iQ[0]==3?!B(_h5(_iQ[1],_in))?[2]:E([1,function(_iR){return new F(function(){return A(_ev,[_iR,function(_iS){return E(new T(function(){return B(_fX(function(_iT){var _iU=E(_iT);if(_iU[0]==2){var _iV=E(_iU[1]);return _iV[0]==0?[2]:E(E(_iV[1])[1])==61?E(_iV[2])[0]==0?E(new T(function(){return B(_gC(_gZ,_gr,function(_iW){return new F(function(){return _gn(function(_iX){var _iY=E(_iX);if(_iY[0]==2){var _iZ=E(_iY[1]);return _iZ[0]==0?[2]:E(E(_iZ[1])[1])==125?E(_iZ[2])[0]==0?E(new T(function(){return B(A(_is,[[0,_iJ,_iW]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_i0(_ir,_is));}));});}},_j0=function(_j1,_j2){return new F(function(){return _iq(E(_j1)[1],_j2);});},_j3=function(_j4,_j5){var _j6=function(_j7){return function(_j8){return new F(function(){return _65(B(A(new T(function(){return B(A(_j4,[_j7]));}),[_j8])),new T(function(){return B(_gs(_j6,_j8));}));});};};return new F(function(){return _j6(_j5);});},_j9=function(_ja){return [1,function(_jb){return new F(function(){return A(_ev,[_jb,function(_jc){return E([3,_ja,_7f]);}]);});}];},_jd=new T(function(){return B(A(_j3,[_j0,_gr,_j9]));}),_je=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_jf=new T(function(){return B(err(_je));}),_jg=function(_jh,_ji){return new F(function(){return A(_ji,[_50]);});},_jj=[0,_4,_jg],_jk=[1,_jj,_Q],_jl=function(_jm,_jn){return new F(function(){return A(_jn,[_4Z]);});},_jo=[0,_3,_jl],_jp=[1,_jo,_jk],_jq=function(_jr,_js,_jt){var _ju=E(_jr);if(!_ju[0]){return [2];}else{var _jv=E(_ju[1]),_jw=_jv[1],_jx=new T(function(){return B(A(_jv[2],[_js,_jt]));});return new F(function(){return _65(B(_gn(function(_jy){var _jz=E(_jy);switch(_jz[0]){case 3:return !B(_h5(_jw,_jz[1]))?[2]:E(_jx);case 4:return !B(_h5(_jw,_jz[1]))?[2]:E(_jx);default:return [2];}})),new T(function(){return B(_jq(_ju[2],_js,_jt));}));});}},_jA=function(_jB,_jC){return new F(function(){return _jq(_jp,_jB,_jC);});},_jD=new T(function(){return B(A(_j3,[_jA,_gr,_j9]));}),_jE=new T(function(){return B(err(_je));}),_jF=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_jG=new T(function(){return B(err(_jF));}),_jH=new T(function(){return B(err(_jF));}),_jI=function(_jJ,_jK,_jL){return _jL<=_jK?[1,[0,_jJ],new T(function(){var _jM=_jK-_jJ|0,_jN=function(_jO){return _jO>=(_jL-_jM|0)?[1,[0,_jO],new T(function(){return B(_jN(_jO+_jM|0));})]:[1,[0,_jO],_Q];};return B(_jN(_jK));})]:_jL<=_jJ?[1,[0,_jJ],_Q]:[0];},_jP=function(_jQ,_jR,_jS){return _jS>=_jR?[1,[0,_jQ],new T(function(){var _jT=_jR-_jQ|0,_jU=function(_jV){return _jV<=(_jS-_jT|0)?[1,[0,_jV],new T(function(){return B(_jU(_jV+_jT|0));})]:[1,[0,_jV],_Q];};return B(_jU(_jR));})]:_jS>=_jQ?[1,[0,_jQ],_Q]:[0];},_jW=function(_jX,_jY){return _jY<_jX?B(_jI(_jX,_jY,-2147483648)):B(_jP(_jX,_jY,2147483647));},_jZ=new T(function(){return B(_jW(135,150));}),_k0=function(_k1,_k2){var _k3=E(_k1);if(!_k3){return [0];}else{var _k4=E(_k2);return _k4[0]==0?[0]:[1,_k4[1],new T(function(){return B(_k0(_k3-1|0,_k4[2]));})];}},_k5=new T(function(){return B(_k0(6,_jZ));}),_k6=function(_k7,_k8){var _k9=E(_k7);if(!_k9[0]){return E(_k5);}else{var _ka=_k9[1];return _k8>1?[1,_ka,new T(function(){return B(_k6(_k9[2],_k8-1|0));})]:[1,_ka,_k5];}},_kb=new T(function(){return B(_jW(25,40));}),_kc=new T(function(){return B(_k6(_kb,6));}),_kd=function(_ke){while(1){var _kf=(function(_kg){var _kh=E(_kg);if(!_kh[0]){return [0];}else{var _ki=_kh[2],_kj=E(_kh[1]);if(!E(_kj[2])[0]){return [1,_kj[1],new T(function(){return B(_kd(_ki));})];}else{_ke=_ki;return null;}}})(_ke);if(_kf!=null){return _kf;}}},_kk=function(_kl,_km){var _kn=E(_km);if(!_kn[0]){return [0,_Q,_Q];}else{var _ko=_kn[1];if(!B(A(_kl,[_ko]))){var _kp=new T(function(){var _kq=B(_kk(_kl,_kn[2]));return [0,_kq[1],_kq[2]];});return [0,[1,_ko,new T(function(){return E(E(_kp)[1]);})],new T(function(){return E(E(_kp)[2]);})];}else{return [0,_Q,_kn];}}},_kr=function(_ks,_kt){while(1){var _ku=E(_kt);if(!_ku[0]){return [0];}else{if(!B(A(_ks,[_ku[1]]))){return E(_ku);}else{_kt=_ku[2];continue;}}}},_kv=function(_kw){var _kx=E(_kw);switch(_kx){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _ky=u_iswspace(_kx),_kz=_ky;return E(_kz)==0?false:true;}},_kA=function(_kB){return new F(function(){return _kv(E(_kB)[1]);});},_kC=function(_kD){var _kE=B(_kr(_kA,_kD));if(!_kE[0]){return [0];}else{var _kF=new T(function(){var _kG=B(_kk(_kA,_kE));return [0,_kG[1],_kG[2]];});return [1,new T(function(){return E(E(_kF)[1]);}),new T(function(){return B(_kC(E(_kF)[2]));})];}},_kH=function(_kI,_){var _kJ=setDropCheckerCallback_ffi(function(_kK,_kL,_kM){var _kN=E(_kI),_kO=_kN[1],_kP=_kN[6],_kQ=new T(function(){return B(_kC(B(_5O(_kK))));}),_kR=B(_kd(B(_5V(_jd,new T(function(){return B(_10(_5Q,B(_55(_kQ,2))));})))));if(!_kR[0]){return E(_jH);}else{if(!E(_kR[2])[0]){var _kS=E(_kR[1]);if(!_kS[0]){var _kT=B(_5v(function(_kU){var _kV=E(_kU)[1]-E(_kL)[1];return _kV<0? -_kV<7:_kV<7;},_kc));if(!_kT[0]){return function(_7G){return new F(function(){return _5g(_kS,_kS,_kP,_7G);});};}else{var _kW=_kT[1],_kX=function(_kY,_kZ,_){var _l0=E(_kS[1]),_l1=_l0[1];if(_kY<=_l1){return new F(function(){return _5g(_kS,_kS,_kP,_);});}else{var _l2=B(_kd(B(_5V(_jD,new T(function(){return B(_55(_kQ,1));})))));if(!_l2[0]){return E(_jG);}else{var _l3=_l2[1];if(!E(_l2[2])[0]){if(_kY>=0){var _l4=B(_55(_kO,_kY)),_l5=function(_){var _l6=B(_5g(_kS,[0,_kZ,new T(function(){if(_kY>=0){var _l7=E(B(_55(_kO,_kY))[2]);}else{var _l7=E(_52);}return _l7;})],_kP,_)),_l8=_l6;if(_l1>=0){var _l9=new T(function(){return B(_5H(function(_la,_lb,_lc){return [1,new T(function(){var _ld=E(_la)[1];return _ld!=_l1?_ld!=_kY?E(_lb):[0,new T(function(){if(_l1>=0){var _le=E(B(_55(_kO,_l1))[1]);}else{var _le=E(_52);}return _le;}),new T(function(){return [0,E(E(_lb)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_lb)[1]);}),new T(function(){return [0,E(E(_lb)[2])[1]-1|0];})];}),_lc];},_Q,_4p,_kO));}),_lf=B((function(_lg,_){while(1){var _lh=(function(_li,_){var _lj=E(_li);if(!_lj[0]){return _J;}else{var _lk=_lj[1],_ll=B(_5g([0,_l0,_lk],[0,_l0,new T(function(){return [0,E(_lk)[1]-1|0];})],_kP,_)),_lm=_ll;_lg=_lj[2];return null;}})(_lg,_);if(_lh!=null){return _lh;}}})(B(_5q(1,B(_4j(E(_kS[2])[1],E(B(_55(_l9,_l1))[2])[1])))),_)),_ln=_lf;return new F(function(){return _kH([0,_l9,_kN[2],_kN[3],_kN[4],_kN[5],_kP,_kN[7]],_);});}else{return E(_52);}},_lo=function(_){return E(_l4[2])[1]>=2?B(_5g(_kS,_kS,_kP,_)):B(_l5(_));};return E(_l4[1])==0?E(_l3)==0?B(_l5(_)):B(_lo(_)):E(_l3)==0?B(_lo(_)):B(_l5(_));}else{return E(_52);}}else{return E(_jE);}}}};if(E(_kM)[1]<=E(_5T)[1]){var _lp=E(_kW);return function(_7G){return new F(function(){return _kX(_lp[1],_lp,_7G);});};}else{var _lq=23-E(_kW)[1]|0;return function(_7G){return new F(function(){return _kX(_lq,[0,_lq],_7G);});};}}}else{return function(_7G){return new F(function(){return _5g(_kS,_kS,_kP,_7G);});};}}else{return E(_jf);}}});return _J;},_lr=function(_ls,_lt){while(1){var _lu=E(_ls);if(!_lu[0]){return E(_lt);}else{_ls=_lu[2];var _lv=[1,_lu[1],_lt];_lt=_lv;continue;}}},_lw=[0,2],_lx=[0,0],_ly=[1,_lx,_Q],_lz=[1,_lx,_ly],_lA=[1,_lx,_lz],_lB=[1,_lx,_lA],_lC=[1,_lx,_lB],_lD=[0,5],_lE=[1,_lD,_lC],_lF=[1,_lx,_lE],_lG=[0,3],_lH=[1,_lG,_lF],_lI=[1,_lx,_lH],_lJ=[1,_lx,_lI],_lK=[1,_lx,_lJ],_lL=[1,_lx,_lK],_lM=[1,_lD,_lL],_lN=[1,_lx,_lM],_lO=[1,_lx,_lN],_lP=[1,_lx,_lO],_lQ=[1,_lx,_lP],_lR=[1,_lx,_lQ],_lS=[1,_lx,_lR],_lT=[1,_lx,_lS],_lU=[1,_lx,_lT],_lV=[1,_lx,_lU],_lW=[1,_lx,_lV],_lX=[1,_lw,_lW],_lY=function(_lZ){var _m0=E(_lZ);return _m0[0]==0?[0]:[1,[0,_50,_m0[1]],new T(function(){return B(_lY(_m0[2]));})];},_m1=new T(function(){return B(_lY(_lX));}),_m2=new T(function(){return B(_lr(_m1,_Q));}),_m3=new T(function(){return B(_2x("main.hs:(239,20)-(240,55)|function whiteOrBlack"));}),_m4=function(_m5,_m6){var _m7=E(_m5);if(!_m7[0]){return [0];}else{var _m8=E(_m6);return _m8[0]==0?[0]:[1,new T(function(){var _m9=E(_m8[1]);if(!E(_m9[1])){var _ma=E(_m3);}else{if(!E(E(_m9[2])[1])){var _mb=E(_m7[1]),_mc=E(_mb[1])==0?E(_mb):[0,_4Z,_mb[2]];}else{var _mc=E(_m9);}var _md=_mc,_ma=_md;}var _me=_ma;return _me;}),new T(function(){return B(_m4(_m7[2],_m8[2]));})];}},_mf=new T(function(){return B(_m4(_m2,_m1));}),_mg=function(_mh,_mi){while(1){var _mj=E(_mh);if(!_mj[0]){return E(_mi);}else{_mh=_mj[2];var _mk=_mi+E(_mj[1])[1]|0;_mi=_mk;continue;}}},_ml=new T(function(){return [0,B(_mg(_lX,0))];}),_mm=[0,_mf,_ml,_ml,_lx,_lx,_50,_50],_mn=function(_){var _mo=E(_ml)[1],_mp=B(_4t(_50,_50,_mo,_)),_mq=_mp,_mr=B(_4t(_4Z,_50,_mo,_)),_ms=_mr;return new F(function(){return _kH(_mm,_);});},_mt=function(_){var _mu=jsFind(toJSStr(E(_2))),_mv=_mu,_mw=E(_mv);if(!_mw[0]){return new F(function(){return _mn(_);});}else{var _mx=jsSet(E(_mw[1])[1],toJSStr(E(_1)),toJSStr(E(_0)));return new F(function(){return _mn(_);});}},_my=function(_){return new F(function(){return _mt(_);});};
var hasteMain = function() {B(A(_my, [0]));};window.onload = hasteMain;