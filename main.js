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

var _0=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_1=new T(function(){return B(unCStr("base"));}),_2=new T(function(){return B(unCStr("IOException"));}),_3=[0],_4=new T(function(){var _5=hs_wordToWord64(4053623282),_6=_5,_7=hs_wordToWord64(3693590983),_8=_7;return [0,_6,_8,[0,_6,_8,_1,_0,_2],_3];}),_9=function(_a){return E(_4);},_b=function(_c){return E(E(_c)[1]);},_d=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_e=new T(function(){return B(err(_d));}),_f=function(_g,_h,_i){var _j=new T(function(){var _k=B(A(_g,[_i])),_l=B(A(_h,[new T(function(){var _m=E(_j);return _m[0]==0?E(_e):E(_m[1]);})])),_n=hs_eqWord64(_k[1],_l[1]),_o=_n;if(!E(_o)){var _p=[0];}else{var _q=hs_eqWord64(_k[2],_l[2]),_r=_q,_p=E(_r)==0?[0]:[1,_i];}var _s=_p,_t=_s;return _t;});return E(_j);},_u=function(_v){var _w=E(_v);return new F(function(){return _f(B(_b(_w[1])),_9,_w[2]);});},_x=new T(function(){return B(unCStr(": "));}),_y=[0,41],_z=new T(function(){return B(unCStr(" ("));}),_A=function(_B,_C){var _D=E(_B);return _D[0]==0?E(_C):[1,_D[1],new T(function(){return B(_A(_D[2],_C));})];},_E=new T(function(){return B(unCStr("already exists"));}),_F=new T(function(){return B(unCStr("does not exist"));}),_G=new T(function(){return B(unCStr("protocol error"));}),_H=new T(function(){return B(unCStr("failed"));}),_I=new T(function(){return B(unCStr("invalid argument"));}),_J=new T(function(){return B(unCStr("inappropriate type"));}),_K=new T(function(){return B(unCStr("hardware fault"));}),_L=new T(function(){return B(unCStr("unsupported operation"));}),_M=new T(function(){return B(unCStr("timeout"));}),_N=new T(function(){return B(unCStr("resource vanished"));}),_O=new T(function(){return B(unCStr("interrupted"));}),_P=new T(function(){return B(unCStr("resource busy"));}),_Q=new T(function(){return B(unCStr("resource exhausted"));}),_R=new T(function(){return B(unCStr("end of file"));}),_S=new T(function(){return B(unCStr("illegal operation"));}),_T=new T(function(){return B(unCStr("permission denied"));}),_U=new T(function(){return B(unCStr("user error"));}),_V=new T(function(){return B(unCStr("unsatisified constraints"));}),_W=new T(function(){return B(unCStr("system error"));}),_X=function(_Y,_Z){switch(E(_Y)){case 0:return new F(function(){return _A(_E,_Z);});break;case 1:return new F(function(){return _A(_F,_Z);});break;case 2:return new F(function(){return _A(_P,_Z);});break;case 3:return new F(function(){return _A(_Q,_Z);});break;case 4:return new F(function(){return _A(_R,_Z);});break;case 5:return new F(function(){return _A(_S,_Z);});break;case 6:return new F(function(){return _A(_T,_Z);});break;case 7:return new F(function(){return _A(_U,_Z);});break;case 8:return new F(function(){return _A(_V,_Z);});break;case 9:return new F(function(){return _A(_W,_Z);});break;case 10:return new F(function(){return _A(_G,_Z);});break;case 11:return new F(function(){return _A(_H,_Z);});break;case 12:return new F(function(){return _A(_I,_Z);});break;case 13:return new F(function(){return _A(_J,_Z);});break;case 14:return new F(function(){return _A(_K,_Z);});break;case 15:return new F(function(){return _A(_L,_Z);});break;case 16:return new F(function(){return _A(_M,_Z);});break;case 17:return new F(function(){return _A(_N,_Z);});break;default:return new F(function(){return _A(_O,_Z);});}},_10=[0,125],_11=new T(function(){return B(unCStr("{handle: "));}),_12=function(_13,_14,_15,_16,_17,_18){var _19=new T(function(){var _1a=new T(function(){return B(_X(_14,new T(function(){var _1b=E(_16);return _1b[0]==0?E(_18):B(_A(_z,new T(function(){return B(_A(_1b,[1,_y,_18]));})));})));}),_1c=E(_15);return _1c[0]==0?E(_1a):B(_A(_1c,new T(function(){return B(_A(_x,_1a));})));}),_1d=E(_17);if(!_1d[0]){var _1e=E(_13);if(!_1e[0]){return E(_19);}else{var _1f=E(_1e[1]);return _1f[0]==0?B(_A(_11,new T(function(){return B(_A(_1f[1],[1,_10,new T(function(){return B(_A(_x,_19));})]));}))):B(_A(_11,new T(function(){return B(_A(_1f[1],[1,_10,new T(function(){return B(_A(_x,_19));})]));})));}}else{return new F(function(){return _A(_1d[1],new T(function(){return B(_A(_x,_19));}));});}},_1g=function(_1h){var _1i=E(_1h);return new F(function(){return _12(_1i[1],_1i[2],_1i[3],_1i[4],_1i[6],_3);});},_1j=function(_1k,_1l){var _1m=E(_1k);return new F(function(){return _12(_1m[1],_1m[2],_1m[3],_1m[4],_1m[6],_1l);});},_1n=[0,44],_1o=[0,93],_1p=[0,91],_1q=function(_1r,_1s,_1t){var _1u=E(_1s);return _1u[0]==0?B(unAppCStr("[]",_1t)):[1,_1p,new T(function(){return B(A(_1r,[_1u[1],new T(function(){var _1v=function(_1w){var _1x=E(_1w);return _1x[0]==0?E([1,_1o,_1t]):[1,_1n,new T(function(){return B(A(_1r,[_1x[1],new T(function(){return B(_1v(_1x[2]));})]));})];};return B(_1v(_1u[2]));})]));})];},_1y=function(_1z,_1A){return new F(function(){return _1q(_1j,_1z,_1A);});},_1B=function(_1C,_1D,_1E){var _1F=E(_1D);return new F(function(){return _12(_1F[1],_1F[2],_1F[3],_1F[4],_1F[6],_1E);});},_1G=[0,_1B,_1g,_1y],_1H=new T(function(){return [0,_9,_1G,_1I,_u];}),_1I=function(_1J){return [0,_1H,_1J];},_1K=[0],_1L=7,_1M=function(_1N){return [0,_1K,_1L,_3,_1N,_1K,_1K];},_1O=function(_1P,_){return new F(function(){return die(new T(function(){return B(_1I(new T(function(){return B(_1M(_1P));})));}));});},_1Q=function(_1R,_){return new F(function(){return _1O(_1R,_);});},_1S=new T(function(){return B(unCStr("You have not joined a game (yet)."));}),_1T=new T(function(){return B(unCStr("innerHTML"));}),_1U=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:259:9-15"));}),_1V=new T(function(){return B(unCStr("HintText"));}),_1W=new T(function(){return B(unCStr("Black"));}),_1X=new T(function(){return B(unCStr("White"));}),_1Y=[0,125],_1Z=new T(function(){return B(unCStr(", "));}),_20=function(_21,_22){var _23=jsShowI(_21),_24=_23;return new F(function(){return _A(fromJSStr(_24),_22);});},_25=[0,41],_26=[0,40],_27=function(_28,_29,_2a){return _29>=0?B(_20(_29,_2a)):_28<=6?B(_20(_29,_2a)):[1,_26,new T(function(){var _2b=jsShowI(_29),_2c=_2b;return B(_A(fromJSStr(_2c),[1,_25,_2a]));})];},_2d=new T(function(){return B(unCStr("onPointIndex = "));}),_2e=new T(function(){return B(unCStr("BarPlacement {"));}),_2f=new T(function(){return B(unCStr("onBarIndex = "));}),_2g=new T(function(){return B(unCStr("LeftSidePlacement {"));}),_2h=new T(function(){return B(unCStr("onSideIndex = "));}),_2i=new T(function(){return B(unCStr("RightSidePlacement {"));}),_2j=new T(function(){return B(unCStr("PointPlacement {"));}),_2k=new T(function(){return B(unCStr("pointIndex = "));}),_2l=function(_2m,_2n,_2o){var _2p=E(_2n);switch(_2p[0]){case 0:var _2q=function(_2r){return new F(function(){return _A(_2k,new T(function(){return B(_27(0,E(_2p[1])[1],new T(function(){return B(_A(_1Z,new T(function(){return B(_A(_2d,new T(function(){return B(_27(0,E(_2p[2])[1],[1,_1Y,_2r]));})));})));})));}));});};return _2m<11?B(_A(_2j,new T(function(){return B(_2q(_2o));}))):[1,_26,new T(function(){return B(_A(_2j,new T(function(){return B(_2q([1,_25,_2o]));})));})];case 1:var _2s=function(_2t){return new F(function(){return _A(_2e,new T(function(){return B(_A(_2f,new T(function(){return B(_27(0,E(_2p[1])[1],[1,_1Y,_2t]));})));}));});};return _2m<11?B(_2s(_2o)):[1,_26,new T(function(){return B(_2s([1,_25,_2o]));})];case 2:var _2u=function(_2v){return new F(function(){return _A(_2g,new T(function(){return B(_A(_2h,new T(function(){return B(_27(0,E(_2p[1])[1],[1,_1Y,_2v]));})));}));});};return _2m<11?B(_2u(_2o)):[1,_26,new T(function(){return B(_2u([1,_25,_2o]));})];default:var _2w=function(_2x){return new F(function(){return _A(_2i,new T(function(){return B(_A(_2h,new T(function(){return B(_27(0,E(_2p[1])[1],[1,_1Y,_2x]));})));}));});};return _2m<11?B(_2w(_2o)):[1,_26,new T(function(){return B(_2w([1,_25,_2o]));})];}},_2y=0,_2z=function(_2A,_2B,_2C,_2D){return new F(function(){return A(_2A,[new T(function(){return function(_){var _2E=jsSetAttr(E(_2B)[1],toJSStr(E(_2C)),toJSStr(E(_2D)));return _2y;};})]);});},_2F=function(_2G){return E(_2G);},_2H=[0,95],_2I=function(_2J){var _2K=E(_2J);return E(_2K[1])==32?E(_2H):E(_2K);},_2L=new T(function(){return B(unCStr("class"));}),_2M=new T(function(){return B(unCStr("draggable "));}),_2N=[0,32],_2O=function(_2P,_2Q){var _2R=E(_2Q);return _2R[0]==0?[0]:[1,new T(function(){return B(A(_2P,[_2R[1]]));}),new T(function(){return B(_2O(_2P,_2R[2]));})];},_2S=function(_2T,_2U,_2V,_2W){return new F(function(){return _2z(_2F,_2T,_2L,new T(function(){var _2X=new T(function(){var _2Y=new T(function(){return B(_2O(_2I,B(_2l(0,_2V,_3))));});return E(_2W)==0?B(_A(_1W,[1,_2N,_2Y])):B(_A(_1X,[1,_2N,_2Y]));});return E(_2U)==0?E(_2W)==0?B(_A(_2M,_2X)):E(_2X):E(_2W)==0?E(_2X):B(_A(_2M,_2X));}));});},_2Z=new T(function(){return B(unCStr("Control.Exception.Base"));}),_30=new T(function(){return B(unCStr("base"));}),_31=new T(function(){return B(unCStr("PatternMatchFail"));}),_32=new T(function(){var _33=hs_wordToWord64(18445595),_34=_33,_35=hs_wordToWord64(52003073),_36=_35;return [0,_34,_36,[0,_34,_36,_30,_2Z,_31],_3];}),_37=function(_38){return E(_32);},_39=function(_3a){var _3b=E(_3a);return new F(function(){return _f(B(_b(_3b[1])),_37,_3b[2]);});},_3c=function(_3d){return E(E(_3d)[1]);},_3e=function(_3f,_3g){return new F(function(){return _A(E(_3f)[1],_3g);});},_3h=function(_3i,_3j){return new F(function(){return _1q(_3e,_3i,_3j);});},_3k=function(_3l,_3m,_3n){return new F(function(){return _A(E(_3m)[1],_3n);});},_3o=[0,_3k,_3c,_3h],_3p=new T(function(){return [0,_37,_3o,_3q,_39];}),_3q=function(_3r){return [0,_3p,_3r];},_3s=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_3t=function(_3u,_3v){return new F(function(){return die(new T(function(){return B(A(_3v,[_3u]));}));});},_3w=function(_3x,_3y){var _3z=E(_3y);if(!_3z[0]){return [0,_3,_3];}else{var _3A=_3z[1];if(!B(A(_3x,[_3A]))){return [0,_3,_3z];}else{var _3B=new T(function(){var _3C=B(_3w(_3x,_3z[2]));return [0,_3C[1],_3C[2]];});return [0,[1,_3A,new T(function(){return E(E(_3B)[1]);})],new T(function(){return E(E(_3B)[2]);})];}}},_3D=[0,32],_3E=[0,10],_3F=[1,_3E,_3],_3G=function(_3H){return E(E(_3H)[1])==124?false:true;},_3I=function(_3J,_3K){var _3L=B(_3w(_3G,B(unCStr(_3J)))),_3M=_3L[1],_3N=function(_3O,_3P){return new F(function(){return _A(_3O,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_A(_3K,new T(function(){return B(_A(_3P,_3F));})));})));}));});},_3Q=E(_3L[2]);if(!_3Q[0]){return new F(function(){return _3N(_3M,_3);});}else{return E(E(_3Q[1])[1])==124?B(_3N(_3M,[1,_3D,_3Q[2]])):B(_3N(_3M,_3));}},_3R=function(_3S){return new F(function(){return _3t([0,new T(function(){return B(_3I(_3S,_3s));})],_3q);});},_3T=new T(function(){return B(_3R("main.hs:(87,1)-(114,116)|function checkerPosition"));}),_3U=function(_3V,_3W){if(_3V<=0){if(_3V>=0){return new F(function(){return quot(_3V,_3W);});}else{if(_3W<=0){return new F(function(){return quot(_3V,_3W);});}else{return quot(_3V+1|0,_3W)-1|0;}}}else{if(_3W>=0){if(_3V>=0){return new F(function(){return quot(_3V,_3W);});}else{if(_3W<=0){return new F(function(){return quot(_3V,_3W);});}else{return quot(_3V+1|0,_3W)-1|0;}}}else{return quot(_3V-1|0,_3W)-1|0;}}},_3X=new T(function(){return [0,B(_3U(15,2))];}),_3Y=new T(function(){return [0,220+B(_3U(15,2))|0];}),_3Z=function(_40){var _41=E(_40);switch(_41[0]){case 0:var _42=_41[1],_43=_41[2];return [0,new T(function(){var _44=E(_42)[1];if(_44>=12){var _45=23-_44|0;if(_45>=6){var _46=[0,25+(20+(imul(_45,15)|0)|0)|0];}else{var _46=[0,25+(imul(_45,15)|0)|0];}var _47=_46,_48=_47;}else{if(_44>=6){var _49=[0,25+(20+(imul(_44,15)|0)|0)|0];}else{var _49=[0,25+(imul(_44,15)|0)|0];}var _48=_49;}var _4a=_48;return _4a;}),new T(function(){if(E(_42)[1]>=12){var _4b=[0,203+(imul(imul(imul(-1,E(_43)[1])|0,2)|0,6)|0)|0];}else{var _4b=[0,7+(imul(imul(E(_43)[1],2)|0,6)|0)|0];}var _4c=_4b;return _4c;})];case 1:return E(_3T);case 2:return [0,_3X,new T(function(){return [0,203-(imul(imul(E(_41[1])[1],2)|0,6)|0)|0];})];default:return [0,_3Y,new T(function(){return [0,203-(imul(imul(E(_41[1])[1],2)|0,6)|0)|0];})];}},_4d=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:151:5-10"));}),_4e=function(_){return _2y;},_4f=[0,114],_4g=[1,_4f,_3],_4h=new T(function(){return B(_27(0,6,_3));}),_4i=new T(function(){return B(unCStr("cx"));}),_4j=new T(function(){return B(unCStr("cy"));}),_4k=function(_4l,_4m){if(_4l<=_4m){var _4n=function(_4o){return [1,[0,_4o],new T(function(){if(_4o!=_4m){var _4p=B(_4n(_4o+1|0));}else{var _4p=[0];}return _4p;})];};return new F(function(){return _4n(_4l);});}else{return [0];}},_4q=new T(function(){return B(_4k(0,2147483647));}),_4r=new T(function(){return B(unCStr("circle"));}),_4s=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_4t=new T(function(){return B(unCStr("board"));}),_4u=function(_4v,_4w,_4x,_){if(_4x>0){var _4y=function(_4z,_4A,_){var _4B=jsFind(toJSStr(E(_4t))),_4C=_4B,_4D=E(_4C);if(!_4D[0]){var _4E=B(_1Q(_4d,_)),_4F=_4E;return new F(function(){return A(_4A,[_]);});}else{var _4G=jsCreateElemNS(toJSStr(E(_4s)),toJSStr(E(_4r))),_4H=_4G,_4I=[0,_4H],_4J=B(A(_2z,[_2F,_4I,_4g,_4h,_])),_4K=_4J,_4L=new T(function(){return E(_4v)==0?[3,_4z]:[2,_4z];}),_4M=new T(function(){var _4N=B(_3Z(_4L));return [0,_4N[1],_4N[2]];}),_4O=B(A(_2z,[_2F,_4I,_4i,new T(function(){return B(_27(0,E(E(_4M)[1])[1],_3));}),_])),_4P=_4O,_4Q=B(A(_2z,[_2F,_4I,_4j,new T(function(){return B(_27(0,E(E(_4M)[2])[1],_3));}),_])),_4R=_4Q,_4S=B(A(_2S,[_4I,_4w,_4L,_4v,_])),_4T=_4S,_4U=jsAppendChild(_4H,E(_4D[1])[1]);return new F(function(){return A(_4A,[_]);});}},_4V=function(_4W,_4X,_){var _4Y=E(_4W);if(!_4Y[0]){return _2y;}else{var _4Z=_4Y[1];if(_4X>1){return new F(function(){return _4y(_4Z,function(_){return new F(function(){return _4V(_4Y[2],_4X-1|0,_);});},_);});}else{return new F(function(){return _4y(_4Z,_4e,_);});}}};return new F(function(){return _4V(_4q,_4x,_);});}else{return _2y;}},_50=0,_51=1,_52=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_53=new T(function(){return B(err(_52));}),_54=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_55=new T(function(){return B(err(_54));}),_56=function(_57,_58){while(1){var _59=E(_57);if(!_59[0]){return E(_55);}else{var _5a=E(_58);if(!_5a){return E(_59[1]);}else{_57=_59[2];_58=_5a-1|0;continue;}}}},_5b=new T(function(){return B(unCStr(": empty list"));}),_5c=new T(function(){return B(unCStr("Prelude."));}),_5d=function(_5e){return new F(function(){return err(B(_A(_5c,new T(function(){return B(_A(_5e,_5b));}))));});},_5f=new T(function(){return B(unCStr("head"));}),_5g=new T(function(){return B(_5d(_5f));}),_5h=function(_5i,_5j,_5k,_){var _5l=jsElemsByClassName(toJSStr(B(_2O(_2I,B(_2l(0,_5i,_3)))))),_5m=_5l,_5n=E(_5m);if(!_5n[0]){return E(_5g);}else{var _5o=E(_5n[1]),_5p=B(_3Z(_5j)),_5q=animateCircle_ffi(_5o[1],E(_5p[1])[1],E(_5p[2])[1],300);return new F(function(){return A(_2S,[_5o,_5k,_5j,_5k,_]);});}},_5r=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:239:9-15"));}),_5s=function(_5t,_5u){while(1){var _5v=E(_5t);if(!_5v){return E(_5u);}else{var _5w=E(_5u);if(!_5w[0]){return [0];}else{_5t=_5v-1|0;_5u=_5w[2];continue;}}}},_5x=new T(function(){return [0,"click"];}),_5y=function(_5z,_5A){var _5B=function(_5C,_5D){while(1){var _5E=(function(_5F,_5G){var _5H=E(_5G);if(!_5H[0]){return [0];}else{var _5I=_5H[2];if(!B(A(_5z,[_5H[1]]))){var _5J=_5F+1|0;_5D=_5I;_5C=_5J;return null;}else{return [1,[0,_5F],new T(function(){return B(_5B(_5F+1|0,_5I));})];}}})(_5C,_5D);if(_5E!=null){return _5E;}}};return new F(function(){return _5B(0,_5A);});},_5K=function(_5L,_5M,_5N,_5O){var _5P=E(_5N);if(!_5P[0]){return E(_5M);}else{var _5Q=E(_5O);if(!_5Q[0]){return E(_5M);}else{return new F(function(){return A(_5L,[_5P[1],_5Q[1],new T(function(){return B(_5K(_5L,_5M,_5P[2],_5Q[2]));})]);});}}},_5R=function(_5S){return new F(function(){return fromJSStr(E(_5S)[1]);});},_5T=function(_5U){var _5V=E(_5U);return E(_5V[1])==95?E(_2N):E(_5V);},_5W=new T(function(){return [0,B(_3U(210,2))];}),_5X=new T(function(){return B(unCStr("joinGame"));}),_5Y=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:233:9-19"));}),_5Z=new T(function(){return [0,"value"];}),_60=new T(function(){return B(unCStr("sharedKey"));}),_61=function(_){var _62=jsFind(toJSStr(E(_60))),_63=_62,_64=E(_63);if(!_64[0]){return new F(function(){return _1Q(_5Y,_);});}else{var _65=jsGet(E(_64[1])[1],E(_5Z)[1]),_66=_65,_67=showAlert_ffi(_66);return _2y;}},_68=function(_69,_6a,_){return new F(function(){return _61(_);});},_6b=[0,_68],_6c=new T(function(){return B(_3R("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_6d=function(_6e,_6f){while(1){var _6g=(function(_6h,_6i){var _6j=E(_6h);switch(_6j[0]){case 0:var _6k=E(_6i);if(!_6k[0]){return [0];}else{_6e=B(A(_6j[1],[_6k[1]]));_6f=_6k[2];return null;}break;case 1:var _6l=B(A(_6j[1],[_6i])),_6m=_6i;_6e=_6l;_6f=_6m;return null;case 2:return [0];case 3:return [1,[0,_6j[1],_6i],new T(function(){return B(_6d(_6j[2],_6i));})];default:return E(_6j[1]);}})(_6e,_6f);if(_6g!=null){return _6g;}}},_6n=function(_6o,_6p){var _6q=new T(function(){var _6r=E(_6p);if(_6r[0]==3){var _6s=[3,_6r[1],new T(function(){return B(_6n(_6o,_6r[2]));})];}else{var _6t=E(_6o);if(_6t[0]==2){var _6u=E(_6r);}else{var _6v=E(_6r);if(_6v[0]==2){var _6w=E(_6t);}else{var _6x=new T(function(){var _6y=E(_6v);if(_6y[0]==4){var _6z=[1,function(_6A){return [4,new T(function(){return B(_A(B(_6d(_6t,_6A)),_6y[1]));})];}];}else{var _6B=E(_6t);if(_6B[0]==1){var _6C=_6B[1],_6D=E(_6y);if(!_6D[0]){var _6E=[1,function(_6F){return new F(function(){return _6n(B(A(_6C,[_6F])),_6D);});}];}else{var _6E=[1,function(_6G){return new F(function(){return _6n(B(A(_6C,[_6G])),new T(function(){return B(A(_6D[1],[_6G]));}));});}];}var _6H=_6E;}else{var _6I=E(_6y);if(!_6I[0]){var _6J=E(_6c);}else{var _6J=[1,function(_6K){return new F(function(){return _6n(_6B,new T(function(){return B(A(_6I[1],[_6K]));}));});}];}var _6H=_6J;}var _6z=_6H;}return _6z;}),_6L=E(_6t);switch(_6L[0]){case 1:var _6M=E(_6v);if(_6M[0]==4){var _6N=[1,function(_6O){return [4,new T(function(){return B(_A(B(_6d(B(A(_6L[1],[_6O])),_6O)),_6M[1]));})];}];}else{var _6N=E(_6x);}var _6P=_6N;break;case 4:var _6Q=_6L[1],_6R=E(_6v);switch(_6R[0]){case 0:var _6S=[1,function(_6T){return [4,new T(function(){return B(_A(_6Q,new T(function(){return B(_6d(_6R,_6T));})));})];}];break;case 1:var _6S=[1,function(_6U){return [4,new T(function(){return B(_A(_6Q,new T(function(){return B(_6d(B(A(_6R[1],[_6U])),_6U));})));})];}];break;default:var _6S=[4,new T(function(){return B(_A(_6Q,_6R[1]));})];}var _6P=_6S;break;default:var _6P=E(_6x);}var _6w=_6P;}var _6u=_6w;}var _6s=_6u;}return _6s;}),_6V=E(_6o);switch(_6V[0]){case 0:var _6W=E(_6p);return _6W[0]==0?[0,function(_6X){return new F(function(){return _6n(B(A(_6V[1],[_6X])),new T(function(){return B(A(_6W[1],[_6X]));}));});}]:E(_6q);case 3:return [3,_6V[1],new T(function(){return B(_6n(_6V[2],_6p));})];default:return E(_6q);}},_6Y=function(_6Z,_70){return E(_6Z)[1]!=E(_70)[1];},_71=function(_72,_73){return E(_72)[1]==E(_73)[1];},_74=[0,_71,_6Y],_75=function(_76){return E(E(_76)[1]);},_77=function(_78,_79,_7a){while(1){var _7b=E(_79);if(!_7b[0]){return E(_7a)[0]==0?true:false;}else{var _7c=E(_7a);if(!_7c[0]){return false;}else{if(!B(A(_75,[_78,_7b[1],_7c[1]]))){return false;}else{_79=_7b[2];_7a=_7c[2];continue;}}}}},_7d=function(_7e,_7f,_7g){return !B(_77(_7e,_7f,_7g))?true:false;},_7h=function(_7i){return [0,function(_7j,_7k){return new F(function(){return _77(_7i,_7j,_7k);});},function(_7j,_7k){return new F(function(){return _7d(_7i,_7j,_7k);});}];},_7l=new T(function(){return B(_7h(_74));}),_7m=function(_7n,_7o){var _7p=E(_7n);switch(_7p[0]){case 0:return [0,function(_7q){return new F(function(){return _7m(B(A(_7p[1],[_7q])),_7o);});}];case 1:return [1,function(_7r){return new F(function(){return _7m(B(A(_7p[1],[_7r])),_7o);});}];case 2:return [2];case 3:return new F(function(){return _6n(B(A(_7o,[_7p[1]])),new T(function(){return B(_7m(_7p[2],_7o));}));});break;default:var _7s=function(_7t){var _7u=E(_7t);if(!_7u[0]){return [0];}else{var _7v=E(_7u[1]);return new F(function(){return _A(B(_6d(B(A(_7o,[_7v[1]])),_7v[2])),new T(function(){return B(_7s(_7u[2]));}));});}},_7w=B(_7s(_7p[1]));return _7w[0]==0?[2]:[4,_7w];}},_7x=[2],_7y=function(_7z){return [3,_7z,_7x];},_7A=function(_7B,_7C){var _7D=E(_7B);if(!_7D){return new F(function(){return A(_7C,[_2y]);});}else{return [0,function(_7E){return E(new T(function(){return B(_7A(_7D-1|0,_7C));}));}];}},_7F=function(_7G,_7H,_7I){return [1,function(_7J){return new F(function(){return A(function(_7K,_7L,_7M){while(1){var _7N=(function(_7O,_7P,_7Q){var _7R=E(_7O);switch(_7R[0]){case 0:var _7S=E(_7P);if(!_7S[0]){return E(_7H);}else{_7K=B(A(_7R[1],[_7S[1]]));_7L=_7S[2];var _7T=_7Q+1|0;_7M=_7T;return null;}break;case 1:var _7U=B(A(_7R[1],[_7P])),_7V=_7P,_7T=_7Q;_7K=_7U;_7L=_7V;_7M=_7T;return null;case 2:return E(_7H);case 3:return function(_7W){return new F(function(){return _7A(_7Q,function(_7X){return E(new T(function(){return B(_7m(_7R,_7W));}));});});};default:return function(_7Y){return new F(function(){return _7m(_7R,_7Y);});};}})(_7K,_7L,_7M);if(_7N!=null){return _7N;}}},[new T(function(){return B(A(_7G,[_7y]));}),_7J,0,_7I]);});}];},_7Z=[6],_80=new T(function(){return B(unCStr("valDig: Bad base"));}),_81=new T(function(){return B(err(_80));}),_82=function(_83,_84){var _85=function(_86,_87){var _88=E(_86);if(!_88[0]){return function(_89){return new F(function(){return A(_89,[new T(function(){return B(A(_87,[_3]));})]);});};}else{var _8a=E(_88[1])[1],_8b=function(_8c){return function(_8d){return [0,function(_8e){return E(new T(function(){return B(A(new T(function(){return B(_85(_88[2],function(_8f){return new F(function(){return A(_87,[[1,_8c,_8f]]);});}));}),[_8d]));}));}];};};switch(E(E(_83)[1])){case 8:if(48>_8a){return function(_8g){return new F(function(){return A(_8g,[new T(function(){return B(A(_87,[_3]));})]);});};}else{if(_8a>55){return function(_8h){return new F(function(){return A(_8h,[new T(function(){return B(A(_87,[_3]));})]);});};}else{return new F(function(){return _8b([0,_8a-48|0]);});}}break;case 10:if(48>_8a){return function(_8i){return new F(function(){return A(_8i,[new T(function(){return B(A(_87,[_3]));})]);});};}else{if(_8a>57){return function(_8j){return new F(function(){return A(_8j,[new T(function(){return B(A(_87,[_3]));})]);});};}else{return new F(function(){return _8b([0,_8a-48|0]);});}}break;case 16:var _8k=new T(function(){if(97>_8a){if(65>_8a){var _8l=[0];}else{if(_8a>70){var _8m=[0];}else{var _8m=[1,[0,(_8a-65|0)+10|0]];}var _8l=_8m;}var _8n=_8l;}else{if(_8a>102){if(65>_8a){var _8o=[0];}else{if(_8a>70){var _8p=[0];}else{var _8p=[1,[0,(_8a-65|0)+10|0]];}var _8o=_8p;}var _8q=_8o;}else{var _8q=[1,[0,(_8a-97|0)+10|0]];}var _8n=_8q;}return _8n;});if(48>_8a){var _8r=E(_8k);if(!_8r[0]){return function(_8s){return new F(function(){return A(_8s,[new T(function(){return B(A(_87,[_3]));})]);});};}else{return new F(function(){return _8b(_8r[1]);});}}else{if(_8a>57){var _8t=E(_8k);if(!_8t[0]){return function(_8u){return new F(function(){return A(_8u,[new T(function(){return B(A(_87,[_3]));})]);});};}else{return new F(function(){return _8b(_8t[1]);});}}else{return new F(function(){return _8b([0,_8a-48|0]);});}}break;default:return E(_81);}}};return [1,function(_8v){return new F(function(){return A(_85,[_8v,_2F,function(_8w){var _8x=E(_8w);return _8x[0]==0?[2]:B(A(_84,[_8x]));}]);});}];},_8y=[0,10],_8z=[0,1],_8A=[0,2147483647],_8B=function(_8C,_8D){while(1){var _8E=E(_8C);if(!_8E[0]){var _8F=_8E[1],_8G=E(_8D);if(!_8G[0]){var _8H=_8G[1],_8I=addC(_8F,_8H);if(!E(_8I[2])){return [0,_8I[1]];}else{_8C=[1,I_fromInt(_8F)];_8D=[1,I_fromInt(_8H)];continue;}}else{_8C=[1,I_fromInt(_8F)];_8D=_8G;continue;}}else{var _8J=E(_8D);if(!_8J[0]){_8C=_8E;_8D=[1,I_fromInt(_8J[1])];continue;}else{return [1,I_add(_8E[1],_8J[1])];}}}},_8K=new T(function(){return B(_8B(_8A,_8z));}),_8L=function(_8M){var _8N=E(_8M);if(!_8N[0]){var _8O=E(_8N[1]);return _8O==(-2147483648)?E(_8K):[0, -_8O];}else{return [1,I_negate(_8N[1])];}},_8P=[0,10],_8Q=[0,0],_8R=function(_8S){return [0,_8S];},_8T=function(_8U,_8V){while(1){var _8W=E(_8U);if(!_8W[0]){var _8X=_8W[1],_8Y=E(_8V);if(!_8Y[0]){var _8Z=_8Y[1];if(!(imul(_8X,_8Z)|0)){return [0,imul(_8X,_8Z)|0];}else{_8U=[1,I_fromInt(_8X)];_8V=[1,I_fromInt(_8Z)];continue;}}else{_8U=[1,I_fromInt(_8X)];_8V=_8Y;continue;}}else{var _90=E(_8V);if(!_90[0]){_8U=_8W;_8V=[1,I_fromInt(_90[1])];continue;}else{return [1,I_mul(_8W[1],_90[1])];}}}},_91=function(_92,_93,_94){while(1){var _95=E(_94);if(!_95[0]){return E(_93);}else{var _96=B(_8B(B(_8T(_93,_92)),B(_8R(E(_95[1])[1]))));_94=_95[2];_93=_96;continue;}}},_97=function(_98){var _99=new T(function(){return B(_6n(B(_6n([0,function(_9a){if(E(E(_9a)[1])==45){return new F(function(){return _82(_8y,function(_9b){return new F(function(){return A(_98,[[1,new T(function(){return B(_8L(B(_91(_8P,_8Q,_9b))));})]]);});});});}else{return [2];}}],[0,function(_9c){if(E(E(_9c)[1])==43){return new F(function(){return _82(_8y,function(_9d){return new F(function(){return A(_98,[[1,new T(function(){return B(_91(_8P,_8Q,_9d));})]]);});});});}else{return [2];}}])),new T(function(){return B(_82(_8y,function(_9e){return new F(function(){return A(_98,[[1,new T(function(){return B(_91(_8P,_8Q,_9e));})]]);});}));})));});return new F(function(){return _6n([0,function(_9f){return E(E(_9f)[1])==101?E(_99):[2];}],[0,function(_9g){return E(E(_9g)[1])==69?E(_99):[2];}]);});},_9h=function(_9i){return new F(function(){return A(_9i,[_1K]);});},_9j=function(_9k){return new F(function(){return A(_9k,[_1K]);});},_9l=function(_9m){return [0,function(_9n){return E(E(_9n)[1])==46?E(new T(function(){return B(_82(_8y,function(_9o){return new F(function(){return A(_9m,[[1,_9o]]);});}));})):[2];}];},_9p=function(_9q){return new F(function(){return _82(_8y,function(_9r){return new F(function(){return _7F(_9l,_9h,function(_9s){return new F(function(){return _7F(_97,_9j,function(_9t){return new F(function(){return A(_9q,[[5,[1,_9r,_9s,_9t]]]);});});});});});});});},_9u=function(_9v,_9w,_9x){while(1){var _9y=E(_9x);if(!_9y[0]){return false;}else{if(!B(A(_75,[_9v,_9w,_9y[1]]))){_9x=_9y[2];continue;}else{return true;}}}},_9z=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_9A=function(_9B){return new F(function(){return _9u(_74,_9B,_9z);});},_9C=[0,8],_9D=[0,16],_9E=function(_9F){return [0,function(_9G){return E(E(_9G)[1])==48?E([0,function(_9H){switch(E(E(_9H)[1])){case 79:return E(new T(function(){return B(_82(_9C,function(_9I){return new F(function(){return A(_9F,[[5,[0,_9C,_9I]]]);});}));}));case 88:return E(new T(function(){return B(_82(_9D,function(_9J){return new F(function(){return A(_9F,[[5,[0,_9D,_9J]]]);});}));}));case 111:return E(new T(function(){return B(_82(_9C,function(_9K){return new F(function(){return A(_9F,[[5,[0,_9C,_9K]]]);});}));}));case 120:return E(new T(function(){return B(_82(_9D,function(_9L){return new F(function(){return A(_9F,[[5,[0,_9D,_9L]]]);});}));}));default:return [2];}}]):[2];}];},_9M=false,_9N=true,_9O=function(_9P){return [0,function(_9Q){switch(E(E(_9Q)[1])){case 79:return E(new T(function(){return B(A(_9P,[_9C]));}));case 88:return E(new T(function(){return B(A(_9P,[_9D]));}));case 111:return E(new T(function(){return B(A(_9P,[_9C]));}));case 120:return E(new T(function(){return B(A(_9P,[_9D]));}));default:return [2];}}];},_9R=function(_9S){return new F(function(){return A(_9S,[_8y]);});},_9T=function(_9U){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_27(9,_9U,_3));}))));});},_9V=function(_9W){var _9X=E(_9W);return _9X[0]==0?E(_9X[1]):I_toInt(_9X[1]);},_9Y=function(_9Z,_a0){var _a1=E(_9Z);if(!_a1[0]){var _a2=_a1[1],_a3=E(_a0);return _a3[0]==0?_a2<=_a3[1]:I_compareInt(_a3[1],_a2)>=0;}else{var _a4=_a1[1],_a5=E(_a0);return _a5[0]==0?I_compareInt(_a4,_a5[1])<=0:I_compare(_a4,_a5[1])<=0;}},_a6=function(_a7){return [2];},_a8=function(_a9){var _aa=E(_a9);if(!_aa[0]){return E(_a6);}else{var _ab=_aa[1],_ac=E(_aa[2]);return _ac[0]==0?E(_ab):function(_ad){return new F(function(){return _6n(B(A(_ab,[_ad])),new T(function(){return B(A(new T(function(){return B(_a8(_ac));}),[_ad]));}));});};}},_ae=new T(function(){return B(unCStr("NUL"));}),_af=function(_ag){return [2];},_ah=function(_ai){return new F(function(){return _af(_ai);});},_aj=function(_ak,_al){var _am=function(_an,_ao){var _ap=E(_an);if(!_ap[0]){return function(_aq){return new F(function(){return A(_aq,[_ak]);});};}else{var _ar=E(_ao);return _ar[0]==0?E(_af):E(_ap[1])[1]!=E(_ar[1])[1]?E(_ah):function(_as){return [0,function(_at){return E(new T(function(){return B(A(new T(function(){return B(_am(_ap[2],_ar[2]));}),[_as]));}));}];};}};return [1,function(_au){return new F(function(){return A(_am,[_ak,_au,_al]);});}];},_av=[0,0],_aw=function(_ax){return new F(function(){return _aj(_ae,function(_ay){return E(new T(function(){return B(A(_ax,[_av]));}));});});},_az=new T(function(){return B(unCStr("STX"));}),_aA=[0,2],_aB=function(_aC){return new F(function(){return _aj(_az,function(_aD){return E(new T(function(){return B(A(_aC,[_aA]));}));});});},_aE=new T(function(){return B(unCStr("ETX"));}),_aF=[0,3],_aG=function(_aH){return new F(function(){return _aj(_aE,function(_aI){return E(new T(function(){return B(A(_aH,[_aF]));}));});});},_aJ=new T(function(){return B(unCStr("EOT"));}),_aK=[0,4],_aL=function(_aM){return new F(function(){return _aj(_aJ,function(_aN){return E(new T(function(){return B(A(_aM,[_aK]));}));});});},_aO=new T(function(){return B(unCStr("ENQ"));}),_aP=[0,5],_aQ=function(_aR){return new F(function(){return _aj(_aO,function(_aS){return E(new T(function(){return B(A(_aR,[_aP]));}));});});},_aT=new T(function(){return B(unCStr("ACK"));}),_aU=[0,6],_aV=function(_aW){return new F(function(){return _aj(_aT,function(_aX){return E(new T(function(){return B(A(_aW,[_aU]));}));});});},_aY=new T(function(){return B(unCStr("BEL"));}),_aZ=[0,7],_b0=function(_b1){return new F(function(){return _aj(_aY,function(_b2){return E(new T(function(){return B(A(_b1,[_aZ]));}));});});},_b3=new T(function(){return B(unCStr("BS"));}),_b4=[0,8],_b5=function(_b6){return new F(function(){return _aj(_b3,function(_b7){return E(new T(function(){return B(A(_b6,[_b4]));}));});});},_b8=new T(function(){return B(unCStr("HT"));}),_b9=[0,9],_ba=function(_bb){return new F(function(){return _aj(_b8,function(_bc){return E(new T(function(){return B(A(_bb,[_b9]));}));});});},_bd=new T(function(){return B(unCStr("LF"));}),_be=[0,10],_bf=function(_bg){return new F(function(){return _aj(_bd,function(_bh){return E(new T(function(){return B(A(_bg,[_be]));}));});});},_bi=new T(function(){return B(unCStr("VT"));}),_bj=[0,11],_bk=function(_bl){return new F(function(){return _aj(_bi,function(_bm){return E(new T(function(){return B(A(_bl,[_bj]));}));});});},_bn=new T(function(){return B(unCStr("FF"));}),_bo=[0,12],_bp=function(_bq){return new F(function(){return _aj(_bn,function(_br){return E(new T(function(){return B(A(_bq,[_bo]));}));});});},_bs=new T(function(){return B(unCStr("CR"));}),_bt=[0,13],_bu=function(_bv){return new F(function(){return _aj(_bs,function(_bw){return E(new T(function(){return B(A(_bv,[_bt]));}));});});},_bx=new T(function(){return B(unCStr("SI"));}),_by=[0,15],_bz=function(_bA){return new F(function(){return _aj(_bx,function(_bB){return E(new T(function(){return B(A(_bA,[_by]));}));});});},_bC=new T(function(){return B(unCStr("DLE"));}),_bD=[0,16],_bE=function(_bF){return new F(function(){return _aj(_bC,function(_bG){return E(new T(function(){return B(A(_bF,[_bD]));}));});});},_bH=new T(function(){return B(unCStr("DC1"));}),_bI=[0,17],_bJ=function(_bK){return new F(function(){return _aj(_bH,function(_bL){return E(new T(function(){return B(A(_bK,[_bI]));}));});});},_bM=new T(function(){return B(unCStr("DC2"));}),_bN=[0,18],_bO=function(_bP){return new F(function(){return _aj(_bM,function(_bQ){return E(new T(function(){return B(A(_bP,[_bN]));}));});});},_bR=new T(function(){return B(unCStr("DC3"));}),_bS=[0,19],_bT=function(_bU){return new F(function(){return _aj(_bR,function(_bV){return E(new T(function(){return B(A(_bU,[_bS]));}));});});},_bW=new T(function(){return B(unCStr("DC4"));}),_bX=[0,20],_bY=function(_bZ){return new F(function(){return _aj(_bW,function(_c0){return E(new T(function(){return B(A(_bZ,[_bX]));}));});});},_c1=new T(function(){return B(unCStr("NAK"));}),_c2=[0,21],_c3=function(_c4){return new F(function(){return _aj(_c1,function(_c5){return E(new T(function(){return B(A(_c4,[_c2]));}));});});},_c6=new T(function(){return B(unCStr("SYN"));}),_c7=[0,22],_c8=function(_c9){return new F(function(){return _aj(_c6,function(_ca){return E(new T(function(){return B(A(_c9,[_c7]));}));});});},_cb=new T(function(){return B(unCStr("ETB"));}),_cc=[0,23],_cd=function(_ce){return new F(function(){return _aj(_cb,function(_cf){return E(new T(function(){return B(A(_ce,[_cc]));}));});});},_cg=new T(function(){return B(unCStr("CAN"));}),_ch=[0,24],_ci=function(_cj){return new F(function(){return _aj(_cg,function(_ck){return E(new T(function(){return B(A(_cj,[_ch]));}));});});},_cl=new T(function(){return B(unCStr("EM"));}),_cm=[0,25],_cn=function(_co){return new F(function(){return _aj(_cl,function(_cp){return E(new T(function(){return B(A(_co,[_cm]));}));});});},_cq=new T(function(){return B(unCStr("SUB"));}),_cr=[0,26],_cs=function(_ct){return new F(function(){return _aj(_cq,function(_cu){return E(new T(function(){return B(A(_ct,[_cr]));}));});});},_cv=new T(function(){return B(unCStr("ESC"));}),_cw=[0,27],_cx=function(_cy){return new F(function(){return _aj(_cv,function(_cz){return E(new T(function(){return B(A(_cy,[_cw]));}));});});},_cA=new T(function(){return B(unCStr("FS"));}),_cB=[0,28],_cC=function(_cD){return new F(function(){return _aj(_cA,function(_cE){return E(new T(function(){return B(A(_cD,[_cB]));}));});});},_cF=new T(function(){return B(unCStr("GS"));}),_cG=[0,29],_cH=function(_cI){return new F(function(){return _aj(_cF,function(_cJ){return E(new T(function(){return B(A(_cI,[_cG]));}));});});},_cK=new T(function(){return B(unCStr("RS"));}),_cL=[0,30],_cM=function(_cN){return new F(function(){return _aj(_cK,function(_cO){return E(new T(function(){return B(A(_cN,[_cL]));}));});});},_cP=new T(function(){return B(unCStr("US"));}),_cQ=[0,31],_cR=function(_cS){return new F(function(){return _aj(_cP,function(_cT){return E(new T(function(){return B(A(_cS,[_cQ]));}));});});},_cU=new T(function(){return B(unCStr("SP"));}),_cV=[0,32],_cW=function(_cX){return new F(function(){return _aj(_cU,function(_cY){return E(new T(function(){return B(A(_cX,[_cV]));}));});});},_cZ=new T(function(){return B(unCStr("DEL"));}),_d0=[0,127],_d1=function(_d2){return new F(function(){return _aj(_cZ,function(_d3){return E(new T(function(){return B(A(_d2,[_d0]));}));});});},_d4=[1,_d1,_3],_d5=[1,_cW,_d4],_d6=[1,_cR,_d5],_d7=[1,_cM,_d6],_d8=[1,_cH,_d7],_d9=[1,_cC,_d8],_da=[1,_cx,_d9],_db=[1,_cs,_da],_dc=[1,_cn,_db],_dd=[1,_ci,_dc],_de=[1,_cd,_dd],_df=[1,_c8,_de],_dg=[1,_c3,_df],_dh=[1,_bY,_dg],_di=[1,_bT,_dh],_dj=[1,_bO,_di],_dk=[1,_bJ,_dj],_dl=[1,_bE,_dk],_dm=[1,_bz,_dl],_dn=[1,_bu,_dm],_do=[1,_bp,_dn],_dp=[1,_bk,_do],_dq=[1,_bf,_dp],_dr=[1,_ba,_dq],_ds=[1,_b5,_dr],_dt=[1,_b0,_ds],_du=[1,_aV,_dt],_dv=[1,_aQ,_du],_dw=[1,_aL,_dv],_dx=[1,_aG,_dw],_dy=[1,_aB,_dx],_dz=[1,_aw,_dy],_dA=new T(function(){return B(unCStr("SOH"));}),_dB=[0,1],_dC=function(_dD){return new F(function(){return _aj(_dA,function(_dE){return E(new T(function(){return B(A(_dD,[_dB]));}));});});},_dF=new T(function(){return B(unCStr("SO"));}),_dG=[0,14],_dH=function(_dI){return new F(function(){return _aj(_dF,function(_dJ){return E(new T(function(){return B(A(_dI,[_dG]));}));});});},_dK=function(_dL){return new F(function(){return _7F(_dC,_dH,_dL);});},_dM=[1,_dK,_dz],_dN=new T(function(){return B(_a8(_dM));}),_dO=[0,1114111],_dP=[0,34],_dQ=[0,_dP,_9N],_dR=[0,39],_dS=[0,_dR,_9N],_dT=[0,92],_dU=[0,_dT,_9N],_dV=[0,_aZ,_9N],_dW=[0,_b4,_9N],_dX=[0,_bo,_9N],_dY=[0,_be,_9N],_dZ=[0,_bt,_9N],_e0=[0,_b9,_9N],_e1=[0,_bj,_9N],_e2=[0,_av,_9N],_e3=[0,_dB,_9N],_e4=[0,_aA,_9N],_e5=[0,_aF,_9N],_e6=[0,_aK,_9N],_e7=[0,_aP,_9N],_e8=[0,_aU,_9N],_e9=[0,_aZ,_9N],_ea=[0,_b4,_9N],_eb=[0,_b9,_9N],_ec=[0,_be,_9N],_ed=[0,_bj,_9N],_ee=[0,_bo,_9N],_ef=[0,_bt,_9N],_eg=[0,_dG,_9N],_eh=[0,_by,_9N],_ei=[0,_bD,_9N],_ej=[0,_bI,_9N],_ek=[0,_bN,_9N],_el=[0,_bS,_9N],_em=[0,_bX,_9N],_en=[0,_c2,_9N],_eo=[0,_c7,_9N],_ep=[0,_cc,_9N],_eq=[0,_ch,_9N],_er=[0,_cm,_9N],_es=[0,_cr,_9N],_et=[0,_cw,_9N],_eu=[0,_cB,_9N],_ev=[0,_cG,_9N],_ew=[0,_cL,_9N],_ex=[0,_cQ,_9N],_ey=function(_ez){return new F(function(){return _6n([0,function(_eA){switch(E(E(_eA)[1])){case 34:return E(new T(function(){return B(A(_ez,[_dQ]));}));case 39:return E(new T(function(){return B(A(_ez,[_dS]));}));case 92:return E(new T(function(){return B(A(_ez,[_dU]));}));case 97:return E(new T(function(){return B(A(_ez,[_dV]));}));case 98:return E(new T(function(){return B(A(_ez,[_dW]));}));case 102:return E(new T(function(){return B(A(_ez,[_dX]));}));case 110:return E(new T(function(){return B(A(_ez,[_dY]));}));case 114:return E(new T(function(){return B(A(_ez,[_dZ]));}));case 116:return E(new T(function(){return B(A(_ez,[_e0]));}));case 118:return E(new T(function(){return B(A(_ez,[_e1]));}));default:return [2];}}],new T(function(){return B(_6n(B(_7F(_9O,_9R,function(_eB){return new F(function(){return _82(_eB,function(_eC){var _eD=B(_91(new T(function(){return B(_8R(E(_eB)[1]));}),_8Q,_eC));return !B(_9Y(_eD,_dO))?[2]:B(A(_ez,[[0,new T(function(){var _eE=B(_9V(_eD));if(_eE>>>0>1114111){var _eF=B(_9T(_eE));}else{var _eF=[0,_eE];}var _eG=_eF,_eH=_eG;return _eH;}),_9N]]));});});})),new T(function(){return B(_6n([0,function(_eI){return E(E(_eI)[1])==94?E([0,function(_eJ){switch(E(E(_eJ)[1])){case 64:return E(new T(function(){return B(A(_ez,[_e2]));}));case 65:return E(new T(function(){return B(A(_ez,[_e3]));}));case 66:return E(new T(function(){return B(A(_ez,[_e4]));}));case 67:return E(new T(function(){return B(A(_ez,[_e5]));}));case 68:return E(new T(function(){return B(A(_ez,[_e6]));}));case 69:return E(new T(function(){return B(A(_ez,[_e7]));}));case 70:return E(new T(function(){return B(A(_ez,[_e8]));}));case 71:return E(new T(function(){return B(A(_ez,[_e9]));}));case 72:return E(new T(function(){return B(A(_ez,[_ea]));}));case 73:return E(new T(function(){return B(A(_ez,[_eb]));}));case 74:return E(new T(function(){return B(A(_ez,[_ec]));}));case 75:return E(new T(function(){return B(A(_ez,[_ed]));}));case 76:return E(new T(function(){return B(A(_ez,[_ee]));}));case 77:return E(new T(function(){return B(A(_ez,[_ef]));}));case 78:return E(new T(function(){return B(A(_ez,[_eg]));}));case 79:return E(new T(function(){return B(A(_ez,[_eh]));}));case 80:return E(new T(function(){return B(A(_ez,[_ei]));}));case 81:return E(new T(function(){return B(A(_ez,[_ej]));}));case 82:return E(new T(function(){return B(A(_ez,[_ek]));}));case 83:return E(new T(function(){return B(A(_ez,[_el]));}));case 84:return E(new T(function(){return B(A(_ez,[_em]));}));case 85:return E(new T(function(){return B(A(_ez,[_en]));}));case 86:return E(new T(function(){return B(A(_ez,[_eo]));}));case 87:return E(new T(function(){return B(A(_ez,[_ep]));}));case 88:return E(new T(function(){return B(A(_ez,[_eq]));}));case 89:return E(new T(function(){return B(A(_ez,[_er]));}));case 90:return E(new T(function(){return B(A(_ez,[_es]));}));case 91:return E(new T(function(){return B(A(_ez,[_et]));}));case 92:return E(new T(function(){return B(A(_ez,[_eu]));}));case 93:return E(new T(function(){return B(A(_ez,[_ev]));}));case 94:return E(new T(function(){return B(A(_ez,[_ew]));}));case 95:return E(new T(function(){return B(A(_ez,[_ex]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_dN,[function(_eK){return new F(function(){return A(_ez,[[0,_eK,_9N]]);});}]));})));})));}));});},_eL=function(_eM){return new F(function(){return A(_eM,[_2y]);});},_eN=function(_eO){var _eP=E(_eO);if(!_eP[0]){return E(_eL);}else{var _eQ=_eP[2],_eR=E(E(_eP[1])[1]);switch(_eR){case 9:return function(_eS){return [0,function(_eT){return E(new T(function(){return B(A(new T(function(){return B(_eN(_eQ));}),[_eS]));}));}];};case 10:return function(_eU){return [0,function(_eV){return E(new T(function(){return B(A(new T(function(){return B(_eN(_eQ));}),[_eU]));}));}];};case 11:return function(_eW){return [0,function(_eX){return E(new T(function(){return B(A(new T(function(){return B(_eN(_eQ));}),[_eW]));}));}];};case 12:return function(_eY){return [0,function(_eZ){return E(new T(function(){return B(A(new T(function(){return B(_eN(_eQ));}),[_eY]));}));}];};case 13:return function(_f0){return [0,function(_f1){return E(new T(function(){return B(A(new T(function(){return B(_eN(_eQ));}),[_f0]));}));}];};case 32:return function(_f2){return [0,function(_f3){return E(new T(function(){return B(A(new T(function(){return B(_eN(_eQ));}),[_f2]));}));}];};case 160:return function(_f4){return [0,function(_f5){return E(new T(function(){return B(A(new T(function(){return B(_eN(_eQ));}),[_f4]));}));}];};default:var _f6=u_iswspace(_eR),_f7=_f6;return E(_f7)==0?E(_eL):function(_f8){return [0,function(_f9){return E(new T(function(){return B(A(new T(function(){return B(_eN(_eQ));}),[_f8]));}));}];};}}},_fa=function(_fb){var _fc=new T(function(){return B(_fa(_fb));}),_fd=[1,function(_fe){return new F(function(){return A(_eN,[_fe,function(_ff){return E([0,function(_fg){return E(E(_fg)[1])==92?E(_fc):[2];}]);}]);});}];return new F(function(){return _6n([0,function(_fh){return E(E(_fh)[1])==92?E([0,function(_fi){var _fj=E(E(_fi)[1]);switch(_fj){case 9:return E(_fd);case 10:return E(_fd);case 11:return E(_fd);case 12:return E(_fd);case 13:return E(_fd);case 32:return E(_fd);case 38:return E(_fc);case 160:return E(_fd);default:var _fk=u_iswspace(_fj),_fl=_fk;return E(_fl)==0?[2]:E(_fd);}}]):[2];}],[0,function(_fm){var _fn=E(_fm);return E(_fn[1])==92?E(new T(function(){return B(_ey(_fb));})):B(A(_fb,[[0,_fn,_9M]]));}]);});},_fo=function(_fp,_fq){return new F(function(){return _fa(function(_fr){var _fs=E(_fr),_ft=E(_fs[1]);if(E(_ft[1])==34){if(!E(_fs[2])){return E(new T(function(){return B(A(_fq,[[1,new T(function(){return B(A(_fp,[_3]));})]]));}));}else{return new F(function(){return _fo(function(_fu){return new F(function(){return A(_fp,[[1,_ft,_fu]]);});},_fq);});}}else{return new F(function(){return _fo(function(_fv){return new F(function(){return A(_fp,[[1,_ft,_fv]]);});},_fq);});}});});},_fw=new T(function(){return B(unCStr("_\'"));}),_fx=function(_fy){var _fz=u_iswalnum(_fy),_fA=_fz;return E(_fA)==0?B(_9u(_74,[0,_fy],_fw)):true;},_fB=function(_fC){return new F(function(){return _fx(E(_fC)[1]);});},_fD=new T(function(){return B(unCStr(",;()[]{}`"));}),_fE=function(_fF){return new F(function(){return A(_fF,[_3]);});},_fG=function(_fH,_fI){var _fJ=function(_fK){var _fL=E(_fK);if(!_fL[0]){return E(_fE);}else{var _fM=_fL[1];return !B(A(_fH,[_fM]))?E(_fE):function(_fN){return [0,function(_fO){return E(new T(function(){return B(A(new T(function(){return B(_fJ(_fL[2]));}),[function(_fP){return new F(function(){return A(_fN,[[1,_fM,_fP]]);});}]));}));}];};}};return [1,function(_fQ){return new F(function(){return A(_fJ,[_fQ,_fI]);});}];},_fR=new T(function(){return B(unCStr(".."));}),_fS=new T(function(){return B(unCStr("::"));}),_fT=new T(function(){return B(unCStr("->"));}),_fU=[0,64],_fV=[1,_fU,_3],_fW=[0,126],_fX=[1,_fW,_3],_fY=new T(function(){return B(unCStr("=>"));}),_fZ=[1,_fY,_3],_g0=[1,_fX,_fZ],_g1=[1,_fV,_g0],_g2=[1,_fT,_g1],_g3=new T(function(){return B(unCStr("<-"));}),_g4=[1,_g3,_g2],_g5=[0,124],_g6=[1,_g5,_3],_g7=[1,_g6,_g4],_g8=[1,_dT,_3],_g9=[1,_g8,_g7],_ga=[0,61],_gb=[1,_ga,_3],_gc=[1,_gb,_g9],_gd=[1,_fS,_gc],_ge=[1,_fR,_gd],_gf=function(_gg){return new F(function(){return _6n([1,function(_gh){return E(_gh)[0]==0?E(new T(function(){return B(A(_gg,[_7Z]));})):[2];}],new T(function(){return B(_6n([0,function(_gi){return E(E(_gi)[1])==39?E([0,function(_gj){var _gk=E(_gj);switch(E(_gk[1])){case 39:return [2];case 92:return E(new T(function(){return B(_ey(function(_gl){var _gm=E(_gl);return new F(function(){return (function(_gn,_go){var _gp=new T(function(){return B(A(_gg,[[0,_gn]]));});return !E(_go)?E(E(_gn)[1])==39?[2]:[0,function(_gq){return E(E(_gq)[1])==39?E(_gp):[2];}]:[0,function(_gr){return E(E(_gr)[1])==39?E(_gp):[2];}];})(_gm[1],_gm[2]);});}));}));default:return [0,function(_gs){return E(E(_gs)[1])==39?E(new T(function(){return B(A(_gg,[[0,_gk]]));})):[2];}];}}]):[2];}],new T(function(){return B(_6n([0,function(_gt){return E(E(_gt)[1])==34?E(new T(function(){return B(_fo(_2F,_gg));})):[2];}],new T(function(){return B(_6n([0,function(_gu){return !B(_9u(_74,_gu,_fD))?[2]:B(A(_gg,[[2,[1,_gu,_3]]]));}],new T(function(){return B(_6n([0,function(_gv){if(!B(_9u(_74,_gv,_9z))){return [2];}else{return new F(function(){return _fG(_9A,function(_gw){var _gx=[1,_gv,_gw];return !B(_9u(_7l,_gx,_ge))?B(A(_gg,[[4,_gx]])):B(A(_gg,[[2,_gx]]));});});}}],new T(function(){return B(_6n([0,function(_gy){var _gz=E(_gy),_gA=_gz[1],_gB=u_iswalpha(_gA),_gC=_gB;if(!E(_gC)){if(E(_gA)==95){return new F(function(){return _fG(_fB,function(_gD){return new F(function(){return A(_gg,[[3,[1,_gz,_gD]]]);});});});}else{return [2];}}else{return new F(function(){return _fG(_fB,function(_gE){return new F(function(){return A(_gg,[[3,[1,_gz,_gE]]]);});});});}}],new T(function(){return B(_7F(_9E,_9p,_gg));})));})));})));})));})));}));});},_gF=function(_gG){return [1,function(_gH){return new F(function(){return A(_eN,[_gH,function(_gI){return E(new T(function(){return B(_gf(_gG));}));}]);});}];},_gJ=[0,0],_gK=function(_gL,_gM){return new F(function(){return _gF(function(_gN){var _gO=E(_gN);if(_gO[0]==2){var _gP=E(_gO[1]);return _gP[0]==0?[2]:E(E(_gP[1])[1])==40?E(_gP[2])[0]==0?E(new T(function(){return B(A(_gL,[_gJ,function(_gQ){return new F(function(){return _gF(function(_gR){var _gS=E(_gR);if(_gS[0]==2){var _gT=E(_gS[1]);return _gT[0]==0?[2]:E(E(_gT[1])[1])==41?E(_gT[2])[0]==0?E(new T(function(){return B(A(_gM,[_gQ]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_gU=function(_gV,_gW,_gX){var _gY=function(_gZ,_h0){return new F(function(){return _6n(B(_gF(function(_h1){var _h2=E(_h1);if(_h2[0]==4){var _h3=E(_h2[1]);if(!_h3[0]){return new F(function(){return A(_gV,[_h2,_gZ,_h0]);});}else{return E(E(_h3[1])[1])==45?E(_h3[2])[0]==0?E([1,function(_h4){return new F(function(){return A(_eN,[_h4,function(_h5){return E(new T(function(){return B(_gf(function(_h6){return new F(function(){return A(_gV,[_h6,_gZ,function(_h7){return new F(function(){return A(_h0,[new T(function(){return [0, -E(_h7)[1]];})]);});}]);});}));}));}]);});}]):B(A(_gV,[_h2,_gZ,_h0])):B(A(_gV,[_h2,_gZ,_h0]));}}else{return new F(function(){return A(_gV,[_h2,_gZ,_h0]);});}})),new T(function(){return B(_gK(_gY,_h0));}));});};return new F(function(){return _gY(_gW,_gX);});},_h8=function(_h9,_ha){return [2];},_hb=function(_hc,_hd){return new F(function(){return _h8(_hc,_hd);});},_he=function(_hf){var _hg=E(_hf);return _hg[0]==0?[1,new T(function(){return B(_91(new T(function(){return B(_8R(E(_hg[1])[1]));}),_8Q,_hg[2]));})]:E(_hg[2])[0]==0?E(_hg[3])[0]==0?[1,new T(function(){return B(_91(_8P,_8Q,_hg[1]));})]:[0]:[0];},_hh=function(_hi){var _hj=E(_hi);if(_hj[0]==5){var _hk=B(_he(_hj[1]));return _hk[0]==0?E(_h8):function(_hl,_hm){return new F(function(){return A(_hm,[new T(function(){return [0,B(_9V(_hk[1]))];})]);});};}else{return E(_hb);}},_hn=function(_ho,_hp){while(1){var _hq=E(_ho);if(!_hq[0]){return E(_hp)[0]==0?true:false;}else{var _hr=E(_hp);if(!_hr[0]){return false;}else{if(E(_hq[1])[1]!=E(_hr[1])[1]){return false;}else{_ho=_hq[2];_hp=_hr[2];continue;}}}}},_hs=new T(function(){return B(unCStr("onSideIndex"));}),_ht=new T(function(){return B(unCStr("LeftSidePlacement"));}),_hu=new T(function(){return B(unCStr("RightSidePlacement"));}),_hv=function(_hw,_hx){var _hy=new T(function(){if(_hw>11){var _hz=[2];}else{var _hz=[1,function(_hA){return new F(function(){return A(_eN,[_hA,function(_hB){return E(new T(function(){return B(_gf(function(_hC){var _hD=E(_hC);return _hD[0]==3?!B(_hn(_hD[1],_hu))?[2]:E([1,function(_hE){return new F(function(){return A(_eN,[_hE,function(_hF){return E(new T(function(){return B(_gf(function(_hG){var _hH=E(_hG);if(_hH[0]==2){var _hI=E(_hH[1]);return _hI[0]==0?[2]:E(E(_hI[1])[1])==123?E(_hI[2])[0]==0?E([1,function(_hJ){return new F(function(){return A(_eN,[_hJ,function(_hK){return E(new T(function(){return B(_gf(function(_hL){var _hM=E(_hL);return _hM[0]==3?!B(_hn(_hM[1],_hs))?[2]:E([1,function(_hN){return new F(function(){return A(_eN,[_hN,function(_hO){return E(new T(function(){return B(_gf(function(_hP){var _hQ=E(_hP);if(_hQ[0]==2){var _hR=E(_hQ[1]);return _hR[0]==0?[2]:E(E(_hR[1])[1])==61?E(_hR[2])[0]==0?E(new T(function(){return B(_gU(_hh,_gJ,function(_hS){return new F(function(){return _gF(function(_hT){var _hU=E(_hT);if(_hU[0]==2){var _hV=E(_hU[1]);return _hV[0]==0?[2]:E(E(_hV[1])[1])==125?E(_hV[2])[0]==0?E(new T(function(){return B(A(_hx,[[3,_hS]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}];}return _hz;});if(_hw>11){return new F(function(){return _6n(_7x,_hy);});}else{return new F(function(){return _6n(B(_gF(function(_hW){var _hX=E(_hW);return _hX[0]==3?!B(_hn(_hX[1],_ht))?[2]:E([1,function(_hY){return new F(function(){return A(_eN,[_hY,function(_hZ){return E(new T(function(){return B(_gf(function(_i0){var _i1=E(_i0);if(_i1[0]==2){var _i2=E(_i1[1]);return _i2[0]==0?[2]:E(E(_i2[1])[1])==123?E(_i2[2])[0]==0?E([1,function(_i3){return new F(function(){return A(_eN,[_i3,function(_i4){return E(new T(function(){return B(_gf(function(_i5){var _i6=E(_i5);return _i6[0]==3?!B(_hn(_i6[1],_hs))?[2]:E([1,function(_i7){return new F(function(){return A(_eN,[_i7,function(_i8){return E(new T(function(){return B(_gf(function(_i9){var _ia=E(_i9);if(_ia[0]==2){var _ib=E(_ia[1]);return _ib[0]==0?[2]:E(E(_ib[1])[1])==61?E(_ib[2])[0]==0?E(new T(function(){return B(_gU(_hh,_gJ,function(_ic){return new F(function(){return _gF(function(_id){var _ie=E(_id);if(_ie[0]==2){var _if=E(_ie[1]);return _if[0]==0?[2]:E(E(_if[1])[1])==125?E(_if[2])[0]==0?E(new T(function(){return B(A(_hx,[[2,_ic]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),_hy);});}},_ig=new T(function(){return B(unCStr("onBarIndex"));}),_ih=new T(function(){return B(unCStr("BarPlacement"));}),_ii=function(_ij,_ik){if(_ij>11){return new F(function(){return _6n(_7x,new T(function(){return B(_hv(_ij,_ik));}));});}else{return new F(function(){return _6n(B(_gF(function(_il){var _im=E(_il);return _im[0]==3?!B(_hn(_im[1],_ih))?[2]:E([1,function(_in){return new F(function(){return A(_eN,[_in,function(_io){return E(new T(function(){return B(_gf(function(_ip){var _iq=E(_ip);if(_iq[0]==2){var _ir=E(_iq[1]);return _ir[0]==0?[2]:E(E(_ir[1])[1])==123?E(_ir[2])[0]==0?E([1,function(_is){return new F(function(){return A(_eN,[_is,function(_it){return E(new T(function(){return B(_gf(function(_iu){var _iv=E(_iu);return _iv[0]==3?!B(_hn(_iv[1],_ig))?[2]:E([1,function(_iw){return new F(function(){return A(_eN,[_iw,function(_ix){return E(new T(function(){return B(_gf(function(_iy){var _iz=E(_iy);if(_iz[0]==2){var _iA=E(_iz[1]);return _iA[0]==0?[2]:E(E(_iA[1])[1])==61?E(_iA[2])[0]==0?E(new T(function(){return B(_gU(_hh,_gJ,function(_iB){return new F(function(){return _gF(function(_iC){var _iD=E(_iC);if(_iD[0]==2){var _iE=E(_iD[1]);return _iE[0]==0?[2]:E(E(_iE[1])[1])==125?E(_iE[2])[0]==0?E(new T(function(){return B(A(_ik,[[1,_iB]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_hv(_ij,_ik));}));});}},_iF=new T(function(){return B(unCStr("onPointIndex"));}),_iG=new T(function(){return B(unCStr("pointIndex"));}),_iH=new T(function(){return B(unCStr("PointPlacement"));}),_iI=function(_iJ,_iK){if(_iJ>11){return new F(function(){return _6n(_7x,new T(function(){return B(_ii(_iJ,_iK));}));});}else{return new F(function(){return _6n(B(_gF(function(_iL){var _iM=E(_iL);return _iM[0]==3?!B(_hn(_iM[1],_iH))?[2]:E([1,function(_iN){return new F(function(){return A(_eN,[_iN,function(_iO){return E(new T(function(){return B(_gf(function(_iP){var _iQ=E(_iP);if(_iQ[0]==2){var _iR=E(_iQ[1]);return _iR[0]==0?[2]:E(E(_iR[1])[1])==123?E(_iR[2])[0]==0?E([1,function(_iS){return new F(function(){return A(_eN,[_iS,function(_iT){return E(new T(function(){return B(_gf(function(_iU){var _iV=E(_iU);return _iV[0]==3?!B(_hn(_iV[1],_iG))?[2]:E([1,function(_iW){return new F(function(){return A(_eN,[_iW,function(_iX){return E(new T(function(){return B(_gf(function(_iY){var _iZ=E(_iY);if(_iZ[0]==2){var _j0=E(_iZ[1]);return _j0[0]==0?[2]:E(E(_j0[1])[1])==61?E(_j0[2])[0]==0?E(new T(function(){return B(_gU(_hh,_gJ,function(_j1){return new F(function(){return _gF(function(_j2){var _j3=E(_j2);if(_j3[0]==2){var _j4=E(_j3[1]);return _j4[0]==0?[2]:E(E(_j4[1])[1])==44?E(_j4[2])[0]==0?E([1,function(_j5){return new F(function(){return A(_eN,[_j5,function(_j6){return E(new T(function(){return B(_gf(function(_j7){var _j8=E(_j7);return _j8[0]==3?!B(_hn(_j8[1],_iF))?[2]:E([1,function(_j9){return new F(function(){return A(_eN,[_j9,function(_ja){return E(new T(function(){return B(_gf(function(_jb){var _jc=E(_jb);if(_jc[0]==2){var _jd=E(_jc[1]);return _jd[0]==0?[2]:E(E(_jd[1])[1])==61?E(_jd[2])[0]==0?E(new T(function(){return B(_gU(_hh,_gJ,function(_je){return new F(function(){return _gF(function(_jf){var _jg=E(_jf);if(_jg[0]==2){var _jh=E(_jg[1]);return _jh[0]==0?[2]:E(E(_jh[1])[1])==125?E(_jh[2])[0]==0?E(new T(function(){return B(A(_iK,[[0,_j1,_je]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_ii(_iJ,_iK));}));});}},_ji=function(_jj,_jk){return new F(function(){return _iI(E(_jj)[1],_jk);});},_jl=function(_jm,_jn){var _jo=function(_jp){return function(_jq){return new F(function(){return _6n(B(A(new T(function(){return B(A(_jm,[_jp]));}),[_jq])),new T(function(){return B(_gK(_jo,_jq));}));});};};return new F(function(){return _jo(_jn);});},_jr=function(_js){return [1,function(_jt){return new F(function(){return A(_eN,[_jt,function(_ju){return E([3,_js,_7x]);}]);});}];},_jv=new T(function(){return B(A(_jl,[_ji,_gJ,_jr]));}),_jw=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_jx=new T(function(){return B(err(_jw));}),_jy=function(_jz,_jA){return new F(function(){return A(_jA,[_51]);});},_jB=[0,_1X,_jy],_jC=[1,_jB,_3],_jD=function(_jE,_jF){return new F(function(){return A(_jF,[_50]);});},_jG=[0,_1W,_jD],_jH=[1,_jG,_jC],_jI=function(_jJ,_jK,_jL){var _jM=E(_jJ);if(!_jM[0]){return [2];}else{var _jN=E(_jM[1]),_jO=_jN[1],_jP=new T(function(){return B(A(_jN[2],[_jK,_jL]));});return new F(function(){return _6n(B(_gF(function(_jQ){var _jR=E(_jQ);switch(_jR[0]){case 3:return !B(_hn(_jO,_jR[1]))?[2]:E(_jP);case 4:return !B(_hn(_jO,_jR[1]))?[2]:E(_jP);default:return [2];}})),new T(function(){return B(_jI(_jM[2],_jK,_jL));}));});}},_jS=function(_jT,_jU){return new F(function(){return _jI(_jH,_jT,_jU);});},_jV=new T(function(){return B(A(_jl,[_jS,_gJ,_jr]));}),_jW=new T(function(){return B(err(_jw));}),_jX=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_jY=new T(function(){return B(err(_jX));}),_jZ=new T(function(){return B(err(_jX));}),_k0=function(_k1,_k2,_k3){return _k3<=_k2?[1,[0,_k1],new T(function(){var _k4=_k2-_k1|0,_k5=function(_k6){return _k6>=(_k3-_k4|0)?[1,[0,_k6],new T(function(){return B(_k5(_k6+_k4|0));})]:[1,[0,_k6],_3];};return B(_k5(_k2));})]:_k3<=_k1?[1,[0,_k1],_3]:[0];},_k7=function(_k8,_k9,_ka){return _ka>=_k9?[1,[0,_k8],new T(function(){var _kb=_k9-_k8|0,_kc=function(_kd){return _kd<=(_ka-_kb|0)?[1,[0,_kd],new T(function(){return B(_kc(_kd+_kb|0));})]:[1,[0,_kd],_3];};return B(_kc(_k9));})]:_ka>=_k8?[1,[0,_k8],_3]:[0];},_ke=function(_kf,_kg){return _kg<_kf?B(_k0(_kf,_kg,-2147483648)):B(_k7(_kf,_kg,2147483647));},_kh=new T(function(){return B(_ke(135,150));}),_ki=function(_kj,_kk){var _kl=E(_kj);if(!_kl){return [0];}else{var _km=E(_kk);return _km[0]==0?[0]:[1,_km[1],new T(function(){return B(_ki(_kl-1|0,_km[2]));})];}},_kn=new T(function(){return B(_ki(6,_kh));}),_ko=function(_kp,_kq){var _kr=E(_kp);if(!_kr[0]){return E(_kn);}else{var _ks=_kr[1];return _kq>1?[1,_ks,new T(function(){return B(_ko(_kr[2],_kq-1|0));})]:[1,_ks,_kn];}},_kt=new T(function(){return B(_ke(25,40));}),_ku=new T(function(){return B(_ko(_kt,6));}),_kv=function(_kw){while(1){var _kx=(function(_ky){var _kz=E(_ky);if(!_kz[0]){return [0];}else{var _kA=_kz[2],_kB=E(_kz[1]);if(!E(_kB[2])[0]){return [1,_kB[1],new T(function(){return B(_kv(_kA));})];}else{_kw=_kA;return null;}}})(_kw);if(_kx!=null){return _kx;}}},_kC=function(_kD,_kE){var _kF=E(_kE);if(!_kF[0]){return [0,_3,_3];}else{var _kG=_kF[1];if(!B(A(_kD,[_kG]))){var _kH=new T(function(){var _kI=B(_kC(_kD,_kF[2]));return [0,_kI[1],_kI[2]];});return [0,[1,_kG,new T(function(){return E(E(_kH)[1]);})],new T(function(){return E(E(_kH)[2]);})];}else{return [0,_3,_kF];}}},_kJ=function(_kK,_kL){while(1){var _kM=E(_kL);if(!_kM[0]){return [0];}else{if(!B(A(_kK,[_kM[1]]))){return E(_kM);}else{_kL=_kM[2];continue;}}}},_kN=function(_kO){var _kP=E(_kO);switch(_kP){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _kQ=u_iswspace(_kP),_kR=_kQ;return E(_kR)==0?false:true;}},_kS=function(_kT){return new F(function(){return _kN(E(_kT)[1]);});},_kU=function(_kV){var _kW=B(_kJ(_kS,_kV));if(!_kW[0]){return [0];}else{var _kX=new T(function(){var _kY=B(_kC(_kS,_kW));return [0,_kY[1],_kY[2]];});return [1,new T(function(){return E(E(_kX)[1]);}),new T(function(){return B(_kU(E(_kX)[2]));})];}},_kZ=function(_l0,_){var _l1=jsFind(toJSStr(E(_5X))),_l2=_l1,_l3=E(_l2);if(!_l3[0]){return new F(function(){return _1Q(_5r,_);});}else{var _l4=jsSetCB(E(_l3[1])[1],E(_5x)[1],E(_6b)[1]),_l5=_l4,_l6=setDropCheckerCallback_ffi(function(_l7,_l8,_l9){var _la=E(_l0),_lb=_la[1],_lc=_la[6],_ld=new T(function(){return B(_kU(B(_5R(_l7))));}),_le=B(_kv(B(_6d(_jv,new T(function(){return B(_2O(_5T,B(_56(_ld,2))));})))));if(!_le[0]){return E(_jZ);}else{if(!E(_le[2])[0]){var _lf=E(_le[1]);if(!_lf[0]){var _lg=B(_5y(function(_lh){var _li=E(_lh)[1]-E(_l8)[1];return _li<0? -_li<7:_li<7;},_ku));if(!_lg[0]){return function(_7Y){return new F(function(){return _5h(_lf,_lf,_lc,_7Y);});};}else{var _lj=_lg[1],_lk=function(_ll,_lm,_){var _ln=E(_lf[1]),_lo=_ln[1];if(_ll<=_lo){return new F(function(){return _5h(_lf,_lf,_lc,_);});}else{var _lp=B(_kv(B(_6d(_jV,new T(function(){return B(_56(_ld,1));})))));if(!_lp[0]){return E(_jY);}else{var _lq=_lp[1];if(!E(_lp[2])[0]){if(_ll>=0){var _lr=B(_56(_lb,_ll)),_ls=function(_){var _lt=B(_5h(_lf,[0,_lm,new T(function(){if(_ll>=0){var _lu=E(B(_56(_lb,_ll))[2]);}else{var _lu=E(_53);}return _lu;})],_lc,_)),_lv=_lt;if(_lo>=0){var _lw=new T(function(){return B(_5K(function(_lx,_ly,_lz){return [1,new T(function(){var _lA=E(_lx)[1];return _lA!=_lo?_lA!=_ll?E(_ly):[0,new T(function(){if(_lo>=0){var _lB=E(B(_56(_lb,_lo))[1]);}else{var _lB=E(_53);}return _lB;}),new T(function(){return [0,E(E(_ly)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_ly)[1]);}),new T(function(){return [0,E(E(_ly)[2])[1]-1|0];})];}),_lz];},_3,_4q,_lb));}),_lC=B((function(_lD,_){while(1){var _lE=(function(_lF,_){var _lG=E(_lF);if(!_lG[0]){return _2y;}else{var _lH=_lG[1],_lI=B(_5h([0,_ln,_lH],[0,_ln,new T(function(){return [0,E(_lH)[1]-1|0];})],_lc,_)),_lJ=_lI;_lD=_lG[2];return null;}})(_lD,_);if(_lE!=null){return _lE;}}})(B(_5s(1,B(_4k(E(_lf[2])[1],E(B(_56(_lw,_lo))[2])[1])))),_)),_lK=_lC;return new F(function(){return _kZ([0,_lw,_la[2],_la[3],_la[4],_la[5],_lc,_la[7]],_);});}else{return E(_53);}},_lL=function(_){return E(_lr[2])[1]>=2?B(_5h(_lf,_lf,_lc,_)):B(_ls(_));};return E(_lr[1])==0?E(_lq)==0?B(_ls(_)):B(_lL(_)):E(_lq)==0?B(_lL(_)):B(_ls(_));}else{return E(_53);}}else{return E(_jW);}}}};if(E(_l9)[1]<=E(_5W)[1]){var _lM=E(_lj);return function(_7Y){return new F(function(){return _lk(_lM[1],_lM,_7Y);});};}else{var _lN=23-E(_lj)[1]|0;return function(_7Y){return new F(function(){return _lk(_lN,[0,_lN],_7Y);});};}}}else{return function(_7Y){return new F(function(){return _5h(_lf,_lf,_lc,_7Y);});};}}else{return E(_jx);}}});return _2y;}},_lO=function(_lP,_lQ){while(1){var _lR=E(_lP);if(!_lR[0]){return E(_lQ);}else{_lP=_lR[2];var _lS=[1,_lR[1],_lQ];_lQ=_lS;continue;}}},_lT=[0,2],_lU=[0,0],_lV=[1,_lU,_3],_lW=[1,_lU,_lV],_lX=[1,_lU,_lW],_lY=[1,_lU,_lX],_lZ=[1,_lU,_lY],_m0=[0,5],_m1=[1,_m0,_lZ],_m2=[1,_lU,_m1],_m3=[0,3],_m4=[1,_m3,_m2],_m5=[1,_lU,_m4],_m6=[1,_lU,_m5],_m7=[1,_lU,_m6],_m8=[1,_lU,_m7],_m9=[1,_m0,_m8],_ma=[1,_lU,_m9],_mb=[1,_lU,_ma],_mc=[1,_lU,_mb],_md=[1,_lU,_mc],_me=[1,_lU,_md],_mf=[1,_lU,_me],_mg=[1,_lU,_mf],_mh=[1,_lU,_mg],_mi=[1,_lU,_mh],_mj=[1,_lU,_mi],_mk=[1,_lT,_mj],_ml=function(_mm){var _mn=E(_mm);return _mn[0]==0?[0]:[1,[0,_51,_mn[1]],new T(function(){return B(_ml(_mn[2]));})];},_mo=new T(function(){return B(_ml(_mk));}),_mp=new T(function(){return B(_lO(_mo,_3));}),_mq=new T(function(){return B(_3R("main.hs:(251,20)-(252,55)|function whiteOrBlack"));}),_mr=function(_ms,_mt){var _mu=E(_ms);if(!_mu[0]){return [0];}else{var _mv=E(_mt);return _mv[0]==0?[0]:[1,new T(function(){var _mw=E(_mv[1]);if(!E(_mw[1])){var _mx=E(_mq);}else{if(!E(E(_mw[2])[1])){var _my=E(_mu[1]),_mz=E(_my[1])==0?E(_my):[0,_50,_my[2]];}else{var _mz=E(_mw);}var _mA=_mz,_mx=_mA;}var _mB=_mx;return _mB;}),new T(function(){return B(_mr(_mu[2],_mv[2]));})];}},_mC=new T(function(){return B(_mr(_mp,_mo));}),_mD=function(_mE,_mF){while(1){var _mG=E(_mE);if(!_mG[0]){return E(_mF);}else{_mE=_mG[2];var _mH=_mF+E(_mG[1])[1]|0;_mF=_mH;continue;}}},_mI=new T(function(){return [0,B(_mD(_mk,0))];}),_mJ=[0,_mC,_mI,_mI,_lU,_lU,_51,_51],_mK=function(_){var _mL=E(_mI)[1],_mM=B(_4u(_51,_51,_mL,_)),_mN=_mM,_mO=B(_4u(_50,_51,_mL,_)),_mP=_mO;return new F(function(){return _kZ(_mJ,_);});},_mQ=function(_){var _mR=jsFind(toJSStr(E(_1V))),_mS=_mR,_mT=E(_mS);if(!_mT[0]){var _mU=B(_1Q(_1U,_)),_mV=_mU;return new F(function(){return _mK(_);});}else{var _mW=jsSet(E(_mT[1])[1],toJSStr(E(_1T)),toJSStr(E(_1S)));return new F(function(){return _mK(_);});}},_mX=function(_){return new F(function(){return _mQ(_);});};
var hasteMain = function() {B(A(_mX, [0]));};window.onload = hasteMain;