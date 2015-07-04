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

var _0=[0],_1=function(_2,_3){while(1){var _4=E(_2);if(!_4[0]){return E(_3);}else{_2=_4[2];var _5=[1,_4[1],_3];_3=_5;continue;}}},_6=2,_7=[0,0],_8=[0,_6,_7],_9=[0,_6,_7],_a=[0,_6,_7],_b=[0,_6,_7],_c=[0,_6,_7],_d=[1,_c,_0],_e=[0,_6,_7],_f=[1,_e,_d],_g=[0,_6,_7],_h=[1,_g,_f],_i=[0,_6,_7],_j=[1,_i,_h],_k=[0,_6,_7],_l=[1,_k,_j],_m=1,_n=[0,5],_o=[0,_m,_n],_p=[1,_o,_l],_q=[0,_6,_7],_r=[1,_q,_p],_s=[0,3],_t=[0,_m,_s],_u=[1,_t,_r],_v=[0,_6,_7],_w=[1,_v,_u],_x=[0,_6,_7],_y=[1,_x,_w],_z=[0,_6,_7],_A=[1,_z,_y],_B=[0,_6,_7],_C=[1,_B,_A],_D=[0,_m,_n],_E=[1,_D,_C],_F=[0,_6,_7],_G=[1,_F,_E],_H=[0,_6,_7],_I=[1,_H,_G],_J=[0,_6,_7],_K=[1,_J,_I],_L=[0,_6,_7],_M=[1,_L,_K],_N=[1,_b,_M],_O=[1,_a,_N],_P=[1,_9,_O],_Q=[1,_8,_P],_R=[0,_6,_7],_S=[1,_R,_Q],_T=[0,_6,_7],_U=[1,_T,_S],_V=[0,2],_W=[0,_m,_V],_X=[1,_W,_U],_Y=new T(function(){return B(_1(_X,_0));}),_Z=0,_10=function(_11,_12){var _13=E(_11);if(!_13[0]){return [0];}else{var _14=E(_12);return _14[0]==0?[0]:[1,new T(function(){var _15=E(_14[1]);if(E(_15[1])==1){var _16=E(_15);}else{var _17=E(_13[1]),_16=E(_17[1])==1?[0,_Z,_17[2]]:E(_17);}var _18=_16;return _18;}),new T(function(){return B(_10(_13[2],_14[2]));})];}},_19=new T(function(){return B(_10(_Y,_X));}),_1a=[0,_19,_m,_m],_1b=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_1c=new T(function(){return B(err(_1b));}),_1d=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_1e=new T(function(){return B(err(_1d));}),_1f=function(_1g,_1h){while(1){var _1i=E(_1g);if(!_1i[0]){return E(_1e);}else{var _1j=E(_1h);if(!_1j){return E(_1i[1]);}else{_1g=_1i[2];_1h=_1j-1|0;continue;}}}},_1k=0,_1l=new T(function(){return B(unCStr("None"));}),_1m=new T(function(){return B(unCStr("White"));}),_1n=new T(function(){return B(unCStr("Black"));}),_1o=function(_1p,_1q,_1r,_1s){return new F(function(){return A(_1p,[new T(function(){return function(_){var _1t=jsSetAttr(E(_1q)[1],toJSStr(E(_1r)),toJSStr(E(_1s)));return _1k;};})]);});},_1u=function(_1v,_1w){var _1x=E(_1v);return _1x[0]==0?E(_1w):[1,_1x[1],new T(function(){return B(_1u(_1x[2],_1w));})];},_1y=function(_1z,_1A){var _1B=jsShowI(_1z),_1C=_1B;return new F(function(){return _1u(fromJSStr(_1C),_1A);});},_1D=[0,41],_1E=[0,40],_1F=function(_1G,_1H,_1I){return _1H>=0?B(_1y(_1H,_1I)):_1G<=6?B(_1y(_1H,_1I)):[1,_1E,new T(function(){var _1J=jsShowI(_1H),_1K=_1J;return B(_1u(fromJSStr(_1K),[1,_1D,_1I]));})];},_1L=function(_1M){return E(_1M);},_1N=new T(function(){return B(unCStr("class"));}),_1O=new T(function(){return B(unCStr("draggable "));}),_1P=function(_1Q,_1R,_1S,_1T,_1U){return new F(function(){return _1o(_1L,_1Q,_1N,new T(function(){var _1V=new T(function(){var _1W=new T(function(){return B(unAppCStr(" pi",new T(function(){return B(_1u(B(_1F(0,E(_1S)[1],_0)),new T(function(){return B(unAppCStr(" ci",new T(function(){return B(_1F(0,E(_1T)[1],_0));})));})));})));});switch(E(_1U)){case 0:var _1X=B(_1u(_1n,_1W));break;case 1:var _1X=B(_1u(_1m,_1W));break;default:var _1X=B(_1u(_1l,_1W));}return _1X;});switch(E(_1R)){case 0:switch(E(_1U)){case 0:var _1Y=B(_1u(_1O,_1V));break;case 1:var _1Y=E(_1V);break;default:var _1Y=E(_1V);}var _1Z=_1Y;break;case 1:var _1Z=E(_1U)==1?B(_1u(_1O,_1V)):E(_1V);break;default:var _1Z=E(_1U)==2?B(_1u(_1O,_1V)):E(_1V);}return _1Z;}));});},_20=function(_21,_22){return [0,new T(function(){var _23=E(_21)[1];if(_23>=12){var _24=23-_23|0;if(_24>=6){var _25=[0,25+(20+(imul(_24,15)|0)|0)|0];}else{var _25=[0,25+(imul(_24,15)|0)|0];}var _26=_25,_27=_26;}else{if(_23>=6){var _28=[0,25+(20+(imul(_23,15)|0)|0)|0];}else{var _28=[0,25+(imul(_23,15)|0)|0];}var _27=_28;}var _29=_27;return _29;}),new T(function(){if(E(_21)[1]>=12){var _2a=[0,203+(imul(imul(imul(-1,E(_22)[1])|0,2)|0,6)|0)|0];}else{var _2a=[0,7+(imul(imul(E(_22)[1],2)|0,6)|0)|0];}var _2b=_2a;return _2b;})];},_2c=function(_2d,_2e,_2f,_2g,_2h,_){var _2i=jsElemsByClassName(toJSStr(B(unAppCStr(" pi",new T(function(){return B(_1u(B(_1F(0,E(_2d)[1],_0)),new T(function(){return B(unAppCStr(" ci",new T(function(){return B(_1F(0,E(_2e)[1],_0));})));})));}))))),_2j=_2i,_2k=B(_1f(_2j,0)),_2l=B(_20(_2f,_2g)),_2m=animateCircle_ffi(_2k[1],E(_2l[1])[1],E(_2l[2])[1],300);return new F(function(){return A(_1P,[_2k,_2h,_2f,_2g,_2h,_]);});},_2n=function(_2o,_2p){while(1){var _2q=E(_2o);if(!_2q){return E(_2p);}else{var _2r=E(_2p);if(!_2r[0]){return [0];}else{_2o=_2q-1|0;_2p=_2r[2];continue;}}}},_2s=function(_2t,_2u){if(_2t<=_2u){var _2v=function(_2w){return [1,[0,_2w],new T(function(){if(_2w!=_2u){var _2x=B(_2v(_2w+1|0));}else{var _2x=[0];}return _2x;})];};return new F(function(){return _2v(_2t);});}else{return [0];}},_2y=function(_2z,_2A){var _2B=function(_2C,_2D){while(1){var _2E=(function(_2F,_2G){var _2H=E(_2G);if(!_2H[0]){return [0];}else{var _2I=_2H[2];if(!B(A(_2z,[_2H[1]]))){var _2J=_2F+1|0;_2D=_2I;_2C=_2J;return null;}else{return [1,[0,_2F],new T(function(){return B(_2B(_2F+1|0,_2I));})];}}})(_2C,_2D);if(_2E!=null){return _2E;}}};return new F(function(){return _2B(0,_2A);});},_2K=function(_2L,_2M,_2N,_2O){var _2P=E(_2N);if(!_2P[0]){return E(_2M);}else{var _2Q=E(_2O);if(!_2Q[0]){return E(_2M);}else{return new F(function(){return A(_2L,[_2P[1],_2Q[1],new T(function(){return B(_2K(_2L,_2M,_2P[2],_2Q[2]));})]);});}}},_2R=function(_2S){return new F(function(){return fromJSStr(E(_2S)[1]);});},_2T=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2U=new T(function(){return B(unCStr("base"));}),_2V=new T(function(){return B(unCStr("PatternMatchFail"));}),_2W=new T(function(){var _2X=hs_wordToWord64(18445595),_2Y=_2X,_2Z=hs_wordToWord64(52003073),_30=_2Z;return [0,_2Y,_30,[0,_2Y,_30,_2U,_2T,_2V],_0];}),_31=function(_32){return E(_2W);},_33=function(_34){return E(E(_34)[1]);},_35=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_36=new T(function(){return B(err(_35));}),_37=function(_38,_39,_3a){var _3b=new T(function(){var _3c=B(A(_38,[_3a])),_3d=B(A(_39,[new T(function(){var _3e=E(_3b);return _3e[0]==0?E(_36):E(_3e[1]);})])),_3f=hs_eqWord64(_3c[1],_3d[1]),_3g=_3f;if(!E(_3g)){var _3h=[0];}else{var _3i=hs_eqWord64(_3c[2],_3d[2]),_3j=_3i,_3h=E(_3j)==0?[0]:[1,_3a];}var _3k=_3h,_3l=_3k;return _3l;});return E(_3b);},_3m=function(_3n){var _3o=E(_3n);return new F(function(){return _37(B(_33(_3o[1])),_31,_3o[2]);});},_3p=function(_3q){return E(E(_3q)[1]);},_3r=function(_3s,_3t){return new F(function(){return _1u(E(_3s)[1],_3t);});},_3u=[0,44],_3v=[0,93],_3w=[0,91],_3x=function(_3y,_3z,_3A){var _3B=E(_3z);return _3B[0]==0?B(unAppCStr("[]",_3A)):[1,_3w,new T(function(){return B(A(_3y,[_3B[1],new T(function(){var _3C=function(_3D){var _3E=E(_3D);return _3E[0]==0?E([1,_3v,_3A]):[1,_3u,new T(function(){return B(A(_3y,[_3E[1],new T(function(){return B(_3C(_3E[2]));})]));})];};return B(_3C(_3B[2]));})]));})];},_3F=function(_3G,_3H){return new F(function(){return _3x(_3r,_3G,_3H);});},_3I=function(_3J,_3K,_3L){return new F(function(){return _1u(E(_3K)[1],_3L);});},_3M=[0,_3I,_3p,_3F],_3N=new T(function(){return [0,_31,_3M,_3O,_3m];}),_3O=function(_3P){return [0,_3N,_3P];},_3Q=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_3R=function(_3S,_3T){return new F(function(){return die(new T(function(){return B(A(_3T,[_3S]));}));});},_3U=function(_3V,_3W){var _3X=E(_3W);if(!_3X[0]){return [0,_0,_0];}else{var _3Y=_3X[1];if(!B(A(_3V,[_3Y]))){return [0,_0,_3X];}else{var _3Z=new T(function(){var _40=B(_3U(_3V,_3X[2]));return [0,_40[1],_40[2]];});return [0,[1,_3Y,new T(function(){return E(E(_3Z)[1]);})],new T(function(){return E(E(_3Z)[2]);})];}}},_41=[0,32],_42=[0,10],_43=[1,_42,_0],_44=function(_45){return E(E(_45)[1])==124?false:true;},_46=function(_47,_48){var _49=B(_3U(_44,B(unCStr(_47)))),_4a=_49[1],_4b=function(_4c,_4d){return new F(function(){return _1u(_4c,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_1u(_48,new T(function(){return B(_1u(_4d,_43));})));})));}));});},_4e=E(_49[2]);if(!_4e[0]){return new F(function(){return _4b(_4a,_0);});}else{return E(E(_4e[1])[1])==124?B(_4b(_4a,[1,_41,_4e[2]])):B(_4b(_4a,_0));}},_4f=function(_4g){return new F(function(){return _3R([0,new T(function(){return B(_46(_4g,_3Q));})],_3O);});},_4h=new T(function(){return B(_4f("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_4i=function(_4j,_4k){while(1){var _4l=(function(_4m,_4n){var _4o=E(_4m);switch(_4o[0]){case 0:var _4p=E(_4n);if(!_4p[0]){return [0];}else{_4j=B(A(_4o[1],[_4p[1]]));_4k=_4p[2];return null;}break;case 1:var _4q=B(A(_4o[1],[_4n])),_4r=_4n;_4j=_4q;_4k=_4r;return null;case 2:return [0];case 3:return [1,[0,_4o[1],_4n],new T(function(){return B(_4i(_4o[2],_4n));})];default:return E(_4o[1]);}})(_4j,_4k);if(_4l!=null){return _4l;}}},_4s=function(_4t,_4u){var _4v=new T(function(){var _4w=E(_4u);if(_4w[0]==3){var _4x=[3,_4w[1],new T(function(){return B(_4s(_4t,_4w[2]));})];}else{var _4y=E(_4t);if(_4y[0]==2){var _4z=E(_4w);}else{var _4A=E(_4w);if(_4A[0]==2){var _4B=E(_4y);}else{var _4C=new T(function(){var _4D=E(_4A);if(_4D[0]==4){var _4E=[1,function(_4F){return [4,new T(function(){return B(_1u(B(_4i(_4y,_4F)),_4D[1]));})];}];}else{var _4G=E(_4y);if(_4G[0]==1){var _4H=_4G[1],_4I=E(_4D);if(!_4I[0]){var _4J=[1,function(_4K){return new F(function(){return _4s(B(A(_4H,[_4K])),_4I);});}];}else{var _4J=[1,function(_4L){return new F(function(){return _4s(B(A(_4H,[_4L])),new T(function(){return B(A(_4I[1],[_4L]));}));});}];}var _4M=_4J;}else{var _4N=E(_4D);if(!_4N[0]){var _4O=E(_4h);}else{var _4O=[1,function(_4P){return new F(function(){return _4s(_4G,new T(function(){return B(A(_4N[1],[_4P]));}));});}];}var _4M=_4O;}var _4E=_4M;}return _4E;}),_4Q=E(_4y);switch(_4Q[0]){case 1:var _4R=E(_4A);if(_4R[0]==4){var _4S=[1,function(_4T){return [4,new T(function(){return B(_1u(B(_4i(B(A(_4Q[1],[_4T])),_4T)),_4R[1]));})];}];}else{var _4S=E(_4C);}var _4U=_4S;break;case 4:var _4V=_4Q[1],_4W=E(_4A);switch(_4W[0]){case 0:var _4X=[1,function(_4Y){return [4,new T(function(){return B(_1u(_4V,new T(function(){return B(_4i(_4W,_4Y));})));})];}];break;case 1:var _4X=[1,function(_4Z){return [4,new T(function(){return B(_1u(_4V,new T(function(){return B(_4i(B(A(_4W[1],[_4Z])),_4Z));})));})];}];break;default:var _4X=[4,new T(function(){return B(_1u(_4V,_4W[1]));})];}var _4U=_4X;break;default:var _4U=E(_4C);}var _4B=_4U;}var _4z=_4B;}var _4x=_4z;}return _4x;}),_50=E(_4t);switch(_50[0]){case 0:var _51=E(_4u);return _51[0]==0?[0,function(_52){return new F(function(){return _4s(B(A(_50[1],[_52])),new T(function(){return B(A(_51[1],[_52]));}));});}]:E(_4v);case 3:return [3,_50[1],new T(function(){return B(_4s(_50[2],_4u));})];default:return E(_4v);}},_53=function(_54,_55){return E(_54)[1]!=E(_55)[1];},_56=function(_57,_58){return E(_57)[1]==E(_58)[1];},_59=[0,_56,_53],_5a=function(_5b){return E(E(_5b)[1]);},_5c=function(_5d,_5e,_5f){while(1){var _5g=E(_5e);if(!_5g[0]){return E(_5f)[0]==0?true:false;}else{var _5h=E(_5f);if(!_5h[0]){return false;}else{if(!B(A(_5a,[_5d,_5g[1],_5h[1]]))){return false;}else{_5e=_5g[2];_5f=_5h[2];continue;}}}}},_5i=function(_5j,_5k,_5l){return !B(_5c(_5j,_5k,_5l))?true:false;},_5m=function(_5n){return [0,function(_5o,_5p){return new F(function(){return _5c(_5n,_5o,_5p);});},function(_5o,_5p){return new F(function(){return _5i(_5n,_5o,_5p);});}];},_5q=new T(function(){return B(_5m(_59));}),_5r=function(_5s,_5t){var _5u=E(_5s);switch(_5u[0]){case 0:return [0,function(_5v){return new F(function(){return _5r(B(A(_5u[1],[_5v])),_5t);});}];case 1:return [1,function(_5w){return new F(function(){return _5r(B(A(_5u[1],[_5w])),_5t);});}];case 2:return [2];case 3:return new F(function(){return _4s(B(A(_5t,[_5u[1]])),new T(function(){return B(_5r(_5u[2],_5t));}));});break;default:var _5x=function(_5y){var _5z=E(_5y);if(!_5z[0]){return [0];}else{var _5A=E(_5z[1]);return new F(function(){return _1u(B(_4i(B(A(_5t,[_5A[1]])),_5A[2])),new T(function(){return B(_5x(_5z[2]));}));});}},_5B=B(_5x(_5u[1]));return _5B[0]==0?[2]:[4,_5B];}},_5C=[2],_5D=function(_5E){return [3,_5E,_5C];},_5F=function(_5G,_5H){var _5I=E(_5G);if(!_5I){return new F(function(){return A(_5H,[_1k]);});}else{return [0,function(_5J){return E(new T(function(){return B(_5F(_5I-1|0,_5H));}));}];}},_5K=function(_5L,_5M,_5N){return [1,function(_5O){return new F(function(){return A(function(_5P,_5Q,_5R){while(1){var _5S=(function(_5T,_5U,_5V){var _5W=E(_5T);switch(_5W[0]){case 0:var _5X=E(_5U);if(!_5X[0]){return E(_5M);}else{_5P=B(A(_5W[1],[_5X[1]]));_5Q=_5X[2];var _5Y=_5V+1|0;_5R=_5Y;return null;}break;case 1:var _5Z=B(A(_5W[1],[_5U])),_60=_5U,_5Y=_5V;_5P=_5Z;_5Q=_60;_5R=_5Y;return null;case 2:return E(_5M);case 3:return function(_61){return new F(function(){return _5F(_5V,function(_62){return E(new T(function(){return B(_5r(_5W,_61));}));});});};default:return function(_63){return new F(function(){return _5r(_5W,_63);});};}})(_5P,_5Q,_5R);if(_5S!=null){return _5S;}}},[new T(function(){return B(A(_5L,[_5D]));}),_5O,0,_5N]);});}];},_64=[6],_65=new T(function(){return B(unCStr("valDig: Bad base"));}),_66=new T(function(){return B(err(_65));}),_67=function(_68,_69){var _6a=function(_6b,_6c){var _6d=E(_6b);if(!_6d[0]){return function(_6e){return new F(function(){return A(_6e,[new T(function(){return B(A(_6c,[_0]));})]);});};}else{var _6f=E(_6d[1])[1],_6g=function(_6h){return function(_6i){return [0,function(_6j){return E(new T(function(){return B(A(new T(function(){return B(_6a(_6d[2],function(_6k){return new F(function(){return A(_6c,[[1,_6h,_6k]]);});}));}),[_6i]));}));}];};};switch(E(E(_68)[1])){case 8:if(48>_6f){return function(_6l){return new F(function(){return A(_6l,[new T(function(){return B(A(_6c,[_0]));})]);});};}else{if(_6f>55){return function(_6m){return new F(function(){return A(_6m,[new T(function(){return B(A(_6c,[_0]));})]);});};}else{return new F(function(){return _6g([0,_6f-48|0]);});}}break;case 10:if(48>_6f){return function(_6n){return new F(function(){return A(_6n,[new T(function(){return B(A(_6c,[_0]));})]);});};}else{if(_6f>57){return function(_6o){return new F(function(){return A(_6o,[new T(function(){return B(A(_6c,[_0]));})]);});};}else{return new F(function(){return _6g([0,_6f-48|0]);});}}break;case 16:var _6p=new T(function(){if(97>_6f){if(65>_6f){var _6q=[0];}else{if(_6f>70){var _6r=[0];}else{var _6r=[1,[0,(_6f-65|0)+10|0]];}var _6q=_6r;}var _6s=_6q;}else{if(_6f>102){if(65>_6f){var _6t=[0];}else{if(_6f>70){var _6u=[0];}else{var _6u=[1,[0,(_6f-65|0)+10|0]];}var _6t=_6u;}var _6v=_6t;}else{var _6v=[1,[0,(_6f-97|0)+10|0]];}var _6s=_6v;}return _6s;});if(48>_6f){var _6w=E(_6p);if(!_6w[0]){return function(_6x){return new F(function(){return A(_6x,[new T(function(){return B(A(_6c,[_0]));})]);});};}else{return new F(function(){return _6g(_6w[1]);});}}else{if(_6f>57){var _6y=E(_6p);if(!_6y[0]){return function(_6z){return new F(function(){return A(_6z,[new T(function(){return B(A(_6c,[_0]));})]);});};}else{return new F(function(){return _6g(_6y[1]);});}}else{return new F(function(){return _6g([0,_6f-48|0]);});}}break;default:return E(_66);}}};return [1,function(_6A){return new F(function(){return A(_6a,[_6A,_1L,function(_6B){var _6C=E(_6B);return _6C[0]==0?[2]:B(A(_69,[_6C]));}]);});}];},_6D=[0,10],_6E=[0,1],_6F=[0,2147483647],_6G=function(_6H,_6I){while(1){var _6J=E(_6H);if(!_6J[0]){var _6K=_6J[1],_6L=E(_6I);if(!_6L[0]){var _6M=_6L[1],_6N=addC(_6K,_6M);if(!E(_6N[2])){return [0,_6N[1]];}else{_6H=[1,I_fromInt(_6K)];_6I=[1,I_fromInt(_6M)];continue;}}else{_6H=[1,I_fromInt(_6K)];_6I=_6L;continue;}}else{var _6O=E(_6I);if(!_6O[0]){_6H=_6J;_6I=[1,I_fromInt(_6O[1])];continue;}else{return [1,I_add(_6J[1],_6O[1])];}}}},_6P=new T(function(){return B(_6G(_6F,_6E));}),_6Q=function(_6R){var _6S=E(_6R);if(!_6S[0]){var _6T=E(_6S[1]);return _6T==(-2147483648)?E(_6P):[0, -_6T];}else{return [1,I_negate(_6S[1])];}},_6U=[0,10],_6V=[0,0],_6W=function(_6X){return [0,_6X];},_6Y=function(_6Z,_70){while(1){var _71=E(_6Z);if(!_71[0]){var _72=_71[1],_73=E(_70);if(!_73[0]){var _74=_73[1];if(!(imul(_72,_74)|0)){return [0,imul(_72,_74)|0];}else{_6Z=[1,I_fromInt(_72)];_70=[1,I_fromInt(_74)];continue;}}else{_6Z=[1,I_fromInt(_72)];_70=_73;continue;}}else{var _75=E(_70);if(!_75[0]){_6Z=_71;_70=[1,I_fromInt(_75[1])];continue;}else{return [1,I_mul(_71[1],_75[1])];}}}},_76=function(_77,_78,_79){while(1){var _7a=E(_79);if(!_7a[0]){return E(_78);}else{var _7b=B(_6G(B(_6Y(_78,_77)),B(_6W(E(_7a[1])[1]))));_79=_7a[2];_78=_7b;continue;}}},_7c=function(_7d){var _7e=new T(function(){return B(_4s(B(_4s([0,function(_7f){if(E(E(_7f)[1])==45){return new F(function(){return _67(_6D,function(_7g){return new F(function(){return A(_7d,[[1,new T(function(){return B(_6Q(B(_76(_6U,_6V,_7g))));})]]);});});});}else{return [2];}}],[0,function(_7h){if(E(E(_7h)[1])==43){return new F(function(){return _67(_6D,function(_7i){return new F(function(){return A(_7d,[[1,new T(function(){return B(_76(_6U,_6V,_7i));})]]);});});});}else{return [2];}}])),new T(function(){return B(_67(_6D,function(_7j){return new F(function(){return A(_7d,[[1,new T(function(){return B(_76(_6U,_6V,_7j));})]]);});}));})));});return new F(function(){return _4s([0,function(_7k){return E(E(_7k)[1])==101?E(_7e):[2];}],[0,function(_7l){return E(E(_7l)[1])==69?E(_7e):[2];}]);});},_7m=[0],_7n=function(_7o){return new F(function(){return A(_7o,[_7m]);});},_7p=function(_7q){return new F(function(){return A(_7q,[_7m]);});},_7r=function(_7s){return [0,function(_7t){return E(E(_7t)[1])==46?E(new T(function(){return B(_67(_6D,function(_7u){return new F(function(){return A(_7s,[[1,_7u]]);});}));})):[2];}];},_7v=function(_7w){return new F(function(){return _67(_6D,function(_7x){return new F(function(){return _5K(_7r,_7n,function(_7y){return new F(function(){return _5K(_7c,_7p,function(_7z){return new F(function(){return A(_7w,[[5,[1,_7x,_7y,_7z]]]);});});});});});});});},_7A=function(_7B,_7C,_7D){while(1){var _7E=E(_7D);if(!_7E[0]){return false;}else{if(!B(A(_5a,[_7B,_7C,_7E[1]]))){_7D=_7E[2];continue;}else{return true;}}}},_7F=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_7G=function(_7H){return new F(function(){return _7A(_59,_7H,_7F);});},_7I=[0,8],_7J=[0,16],_7K=function(_7L){return [0,function(_7M){return E(E(_7M)[1])==48?E([0,function(_7N){switch(E(E(_7N)[1])){case 79:return E(new T(function(){return B(_67(_7I,function(_7O){return new F(function(){return A(_7L,[[5,[0,_7I,_7O]]]);});}));}));case 88:return E(new T(function(){return B(_67(_7J,function(_7P){return new F(function(){return A(_7L,[[5,[0,_7J,_7P]]]);});}));}));case 111:return E(new T(function(){return B(_67(_7I,function(_7Q){return new F(function(){return A(_7L,[[5,[0,_7I,_7Q]]]);});}));}));case 120:return E(new T(function(){return B(_67(_7J,function(_7R){return new F(function(){return A(_7L,[[5,[0,_7J,_7R]]]);});}));}));default:return [2];}}]):[2];}];},_7S=false,_7T=true,_7U=function(_7V){return [0,function(_7W){switch(E(E(_7W)[1])){case 79:return E(new T(function(){return B(A(_7V,[_7I]));}));case 88:return E(new T(function(){return B(A(_7V,[_7J]));}));case 111:return E(new T(function(){return B(A(_7V,[_7I]));}));case 120:return E(new T(function(){return B(A(_7V,[_7J]));}));default:return [2];}}];},_7X=function(_7Y){return new F(function(){return A(_7Y,[_6D]);});},_7Z=function(_80){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_1F(9,_80,_0));}))));});},_81=function(_82){var _83=E(_82);return _83[0]==0?E(_83[1]):I_toInt(_83[1]);},_84=function(_85,_86){var _87=E(_85);if(!_87[0]){var _88=_87[1],_89=E(_86);return _89[0]==0?_88<=_89[1]:I_compareInt(_89[1],_88)>=0;}else{var _8a=_87[1],_8b=E(_86);return _8b[0]==0?I_compareInt(_8a,_8b[1])<=0:I_compare(_8a,_8b[1])<=0;}},_8c=function(_8d){return [2];},_8e=function(_8f){var _8g=E(_8f);if(!_8g[0]){return E(_8c);}else{var _8h=_8g[1],_8i=E(_8g[2]);return _8i[0]==0?E(_8h):function(_8j){return new F(function(){return _4s(B(A(_8h,[_8j])),new T(function(){return B(A(new T(function(){return B(_8e(_8i));}),[_8j]));}));});};}},_8k=new T(function(){return B(unCStr("NUL"));}),_8l=function(_8m){return [2];},_8n=function(_8o){return new F(function(){return _8l(_8o);});},_8p=function(_8q,_8r){var _8s=function(_8t,_8u){var _8v=E(_8t);if(!_8v[0]){return function(_8w){return new F(function(){return A(_8w,[_8q]);});};}else{var _8x=E(_8u);return _8x[0]==0?E(_8l):E(_8v[1])[1]!=E(_8x[1])[1]?E(_8n):function(_8y){return [0,function(_8z){return E(new T(function(){return B(A(new T(function(){return B(_8s(_8v[2],_8x[2]));}),[_8y]));}));}];};}};return [1,function(_8A){return new F(function(){return A(_8s,[_8q,_8A,_8r]);});}];},_8B=[0,0],_8C=function(_8D){return new F(function(){return _8p(_8k,function(_8E){return E(new T(function(){return B(A(_8D,[_8B]));}));});});},_8F=new T(function(){return B(unCStr("STX"));}),_8G=[0,2],_8H=function(_8I){return new F(function(){return _8p(_8F,function(_8J){return E(new T(function(){return B(A(_8I,[_8G]));}));});});},_8K=new T(function(){return B(unCStr("ETX"));}),_8L=[0,3],_8M=function(_8N){return new F(function(){return _8p(_8K,function(_8O){return E(new T(function(){return B(A(_8N,[_8L]));}));});});},_8P=new T(function(){return B(unCStr("EOT"));}),_8Q=[0,4],_8R=function(_8S){return new F(function(){return _8p(_8P,function(_8T){return E(new T(function(){return B(A(_8S,[_8Q]));}));});});},_8U=new T(function(){return B(unCStr("ENQ"));}),_8V=[0,5],_8W=function(_8X){return new F(function(){return _8p(_8U,function(_8Y){return E(new T(function(){return B(A(_8X,[_8V]));}));});});},_8Z=new T(function(){return B(unCStr("ACK"));}),_90=[0,6],_91=function(_92){return new F(function(){return _8p(_8Z,function(_93){return E(new T(function(){return B(A(_92,[_90]));}));});});},_94=new T(function(){return B(unCStr("BEL"));}),_95=[0,7],_96=function(_97){return new F(function(){return _8p(_94,function(_98){return E(new T(function(){return B(A(_97,[_95]));}));});});},_99=new T(function(){return B(unCStr("BS"));}),_9a=[0,8],_9b=function(_9c){return new F(function(){return _8p(_99,function(_9d){return E(new T(function(){return B(A(_9c,[_9a]));}));});});},_9e=new T(function(){return B(unCStr("HT"));}),_9f=[0,9],_9g=function(_9h){return new F(function(){return _8p(_9e,function(_9i){return E(new T(function(){return B(A(_9h,[_9f]));}));});});},_9j=new T(function(){return B(unCStr("LF"));}),_9k=[0,10],_9l=function(_9m){return new F(function(){return _8p(_9j,function(_9n){return E(new T(function(){return B(A(_9m,[_9k]));}));});});},_9o=new T(function(){return B(unCStr("VT"));}),_9p=[0,11],_9q=function(_9r){return new F(function(){return _8p(_9o,function(_9s){return E(new T(function(){return B(A(_9r,[_9p]));}));});});},_9t=new T(function(){return B(unCStr("FF"));}),_9u=[0,12],_9v=function(_9w){return new F(function(){return _8p(_9t,function(_9x){return E(new T(function(){return B(A(_9w,[_9u]));}));});});},_9y=new T(function(){return B(unCStr("CR"));}),_9z=[0,13],_9A=function(_9B){return new F(function(){return _8p(_9y,function(_9C){return E(new T(function(){return B(A(_9B,[_9z]));}));});});},_9D=new T(function(){return B(unCStr("SI"));}),_9E=[0,15],_9F=function(_9G){return new F(function(){return _8p(_9D,function(_9H){return E(new T(function(){return B(A(_9G,[_9E]));}));});});},_9I=new T(function(){return B(unCStr("DLE"));}),_9J=[0,16],_9K=function(_9L){return new F(function(){return _8p(_9I,function(_9M){return E(new T(function(){return B(A(_9L,[_9J]));}));});});},_9N=new T(function(){return B(unCStr("DC1"));}),_9O=[0,17],_9P=function(_9Q){return new F(function(){return _8p(_9N,function(_9R){return E(new T(function(){return B(A(_9Q,[_9O]));}));});});},_9S=new T(function(){return B(unCStr("DC2"));}),_9T=[0,18],_9U=function(_9V){return new F(function(){return _8p(_9S,function(_9W){return E(new T(function(){return B(A(_9V,[_9T]));}));});});},_9X=new T(function(){return B(unCStr("DC3"));}),_9Y=[0,19],_9Z=function(_a0){return new F(function(){return _8p(_9X,function(_a1){return E(new T(function(){return B(A(_a0,[_9Y]));}));});});},_a2=new T(function(){return B(unCStr("DC4"));}),_a3=[0,20],_a4=function(_a5){return new F(function(){return _8p(_a2,function(_a6){return E(new T(function(){return B(A(_a5,[_a3]));}));});});},_a7=new T(function(){return B(unCStr("NAK"));}),_a8=[0,21],_a9=function(_aa){return new F(function(){return _8p(_a7,function(_ab){return E(new T(function(){return B(A(_aa,[_a8]));}));});});},_ac=new T(function(){return B(unCStr("SYN"));}),_ad=[0,22],_ae=function(_af){return new F(function(){return _8p(_ac,function(_ag){return E(new T(function(){return B(A(_af,[_ad]));}));});});},_ah=new T(function(){return B(unCStr("ETB"));}),_ai=[0,23],_aj=function(_ak){return new F(function(){return _8p(_ah,function(_al){return E(new T(function(){return B(A(_ak,[_ai]));}));});});},_am=new T(function(){return B(unCStr("CAN"));}),_an=[0,24],_ao=function(_ap){return new F(function(){return _8p(_am,function(_aq){return E(new T(function(){return B(A(_ap,[_an]));}));});});},_ar=new T(function(){return B(unCStr("EM"));}),_as=[0,25],_at=function(_au){return new F(function(){return _8p(_ar,function(_av){return E(new T(function(){return B(A(_au,[_as]));}));});});},_aw=new T(function(){return B(unCStr("SUB"));}),_ax=[0,26],_ay=function(_az){return new F(function(){return _8p(_aw,function(_aA){return E(new T(function(){return B(A(_az,[_ax]));}));});});},_aB=new T(function(){return B(unCStr("ESC"));}),_aC=[0,27],_aD=function(_aE){return new F(function(){return _8p(_aB,function(_aF){return E(new T(function(){return B(A(_aE,[_aC]));}));});});},_aG=new T(function(){return B(unCStr("FS"));}),_aH=[0,28],_aI=function(_aJ){return new F(function(){return _8p(_aG,function(_aK){return E(new T(function(){return B(A(_aJ,[_aH]));}));});});},_aL=new T(function(){return B(unCStr("GS"));}),_aM=[0,29],_aN=function(_aO){return new F(function(){return _8p(_aL,function(_aP){return E(new T(function(){return B(A(_aO,[_aM]));}));});});},_aQ=new T(function(){return B(unCStr("RS"));}),_aR=[0,30],_aS=function(_aT){return new F(function(){return _8p(_aQ,function(_aU){return E(new T(function(){return B(A(_aT,[_aR]));}));});});},_aV=new T(function(){return B(unCStr("US"));}),_aW=[0,31],_aX=function(_aY){return new F(function(){return _8p(_aV,function(_aZ){return E(new T(function(){return B(A(_aY,[_aW]));}));});});},_b0=new T(function(){return B(unCStr("SP"));}),_b1=[0,32],_b2=function(_b3){return new F(function(){return _8p(_b0,function(_b4){return E(new T(function(){return B(A(_b3,[_b1]));}));});});},_b5=new T(function(){return B(unCStr("DEL"));}),_b6=[0,127],_b7=function(_b8){return new F(function(){return _8p(_b5,function(_b9){return E(new T(function(){return B(A(_b8,[_b6]));}));});});},_ba=[1,_b7,_0],_bb=[1,_b2,_ba],_bc=[1,_aX,_bb],_bd=[1,_aS,_bc],_be=[1,_aN,_bd],_bf=[1,_aI,_be],_bg=[1,_aD,_bf],_bh=[1,_ay,_bg],_bi=[1,_at,_bh],_bj=[1,_ao,_bi],_bk=[1,_aj,_bj],_bl=[1,_ae,_bk],_bm=[1,_a9,_bl],_bn=[1,_a4,_bm],_bo=[1,_9Z,_bn],_bp=[1,_9U,_bo],_bq=[1,_9P,_bp],_br=[1,_9K,_bq],_bs=[1,_9F,_br],_bt=[1,_9A,_bs],_bu=[1,_9v,_bt],_bv=[1,_9q,_bu],_bw=[1,_9l,_bv],_bx=[1,_9g,_bw],_by=[1,_9b,_bx],_bz=[1,_96,_by],_bA=[1,_91,_bz],_bB=[1,_8W,_bA],_bC=[1,_8R,_bB],_bD=[1,_8M,_bC],_bE=[1,_8H,_bD],_bF=[1,_8C,_bE],_bG=new T(function(){return B(unCStr("SOH"));}),_bH=[0,1],_bI=function(_bJ){return new F(function(){return _8p(_bG,function(_bK){return E(new T(function(){return B(A(_bJ,[_bH]));}));});});},_bL=new T(function(){return B(unCStr("SO"));}),_bM=[0,14],_bN=function(_bO){return new F(function(){return _8p(_bL,function(_bP){return E(new T(function(){return B(A(_bO,[_bM]));}));});});},_bQ=function(_bR){return new F(function(){return _5K(_bI,_bN,_bR);});},_bS=[1,_bQ,_bF],_bT=new T(function(){return B(_8e(_bS));}),_bU=[0,1114111],_bV=[0,34],_bW=[0,_bV,_7T],_bX=[0,39],_bY=[0,_bX,_7T],_bZ=[0,92],_c0=[0,_bZ,_7T],_c1=[0,_95,_7T],_c2=[0,_9a,_7T],_c3=[0,_9u,_7T],_c4=[0,_9k,_7T],_c5=[0,_9z,_7T],_c6=[0,_9f,_7T],_c7=[0,_9p,_7T],_c8=[0,_8B,_7T],_c9=[0,_bH,_7T],_ca=[0,_8G,_7T],_cb=[0,_8L,_7T],_cc=[0,_8Q,_7T],_cd=[0,_8V,_7T],_ce=[0,_90,_7T],_cf=[0,_95,_7T],_cg=[0,_9a,_7T],_ch=[0,_9f,_7T],_ci=[0,_9k,_7T],_cj=[0,_9p,_7T],_ck=[0,_9u,_7T],_cl=[0,_9z,_7T],_cm=[0,_bM,_7T],_cn=[0,_9E,_7T],_co=[0,_9J,_7T],_cp=[0,_9O,_7T],_cq=[0,_9T,_7T],_cr=[0,_9Y,_7T],_cs=[0,_a3,_7T],_ct=[0,_a8,_7T],_cu=[0,_ad,_7T],_cv=[0,_ai,_7T],_cw=[0,_an,_7T],_cx=[0,_as,_7T],_cy=[0,_ax,_7T],_cz=[0,_aC,_7T],_cA=[0,_aH,_7T],_cB=[0,_aM,_7T],_cC=[0,_aR,_7T],_cD=[0,_aW,_7T],_cE=function(_cF){return new F(function(){return _4s([0,function(_cG){switch(E(E(_cG)[1])){case 34:return E(new T(function(){return B(A(_cF,[_bW]));}));case 39:return E(new T(function(){return B(A(_cF,[_bY]));}));case 92:return E(new T(function(){return B(A(_cF,[_c0]));}));case 97:return E(new T(function(){return B(A(_cF,[_c1]));}));case 98:return E(new T(function(){return B(A(_cF,[_c2]));}));case 102:return E(new T(function(){return B(A(_cF,[_c3]));}));case 110:return E(new T(function(){return B(A(_cF,[_c4]));}));case 114:return E(new T(function(){return B(A(_cF,[_c5]));}));case 116:return E(new T(function(){return B(A(_cF,[_c6]));}));case 118:return E(new T(function(){return B(A(_cF,[_c7]));}));default:return [2];}}],new T(function(){return B(_4s(B(_5K(_7U,_7X,function(_cH){return new F(function(){return _67(_cH,function(_cI){var _cJ=B(_76(new T(function(){return B(_6W(E(_cH)[1]));}),_6V,_cI));return !B(_84(_cJ,_bU))?[2]:B(A(_cF,[[0,new T(function(){var _cK=B(_81(_cJ));if(_cK>>>0>1114111){var _cL=B(_7Z(_cK));}else{var _cL=[0,_cK];}var _cM=_cL,_cN=_cM;return _cN;}),_7T]]));});});})),new T(function(){return B(_4s([0,function(_cO){return E(E(_cO)[1])==94?E([0,function(_cP){switch(E(E(_cP)[1])){case 64:return E(new T(function(){return B(A(_cF,[_c8]));}));case 65:return E(new T(function(){return B(A(_cF,[_c9]));}));case 66:return E(new T(function(){return B(A(_cF,[_ca]));}));case 67:return E(new T(function(){return B(A(_cF,[_cb]));}));case 68:return E(new T(function(){return B(A(_cF,[_cc]));}));case 69:return E(new T(function(){return B(A(_cF,[_cd]));}));case 70:return E(new T(function(){return B(A(_cF,[_ce]));}));case 71:return E(new T(function(){return B(A(_cF,[_cf]));}));case 72:return E(new T(function(){return B(A(_cF,[_cg]));}));case 73:return E(new T(function(){return B(A(_cF,[_ch]));}));case 74:return E(new T(function(){return B(A(_cF,[_ci]));}));case 75:return E(new T(function(){return B(A(_cF,[_cj]));}));case 76:return E(new T(function(){return B(A(_cF,[_ck]));}));case 77:return E(new T(function(){return B(A(_cF,[_cl]));}));case 78:return E(new T(function(){return B(A(_cF,[_cm]));}));case 79:return E(new T(function(){return B(A(_cF,[_cn]));}));case 80:return E(new T(function(){return B(A(_cF,[_co]));}));case 81:return E(new T(function(){return B(A(_cF,[_cp]));}));case 82:return E(new T(function(){return B(A(_cF,[_cq]));}));case 83:return E(new T(function(){return B(A(_cF,[_cr]));}));case 84:return E(new T(function(){return B(A(_cF,[_cs]));}));case 85:return E(new T(function(){return B(A(_cF,[_ct]));}));case 86:return E(new T(function(){return B(A(_cF,[_cu]));}));case 87:return E(new T(function(){return B(A(_cF,[_cv]));}));case 88:return E(new T(function(){return B(A(_cF,[_cw]));}));case 89:return E(new T(function(){return B(A(_cF,[_cx]));}));case 90:return E(new T(function(){return B(A(_cF,[_cy]));}));case 91:return E(new T(function(){return B(A(_cF,[_cz]));}));case 92:return E(new T(function(){return B(A(_cF,[_cA]));}));case 93:return E(new T(function(){return B(A(_cF,[_cB]));}));case 94:return E(new T(function(){return B(A(_cF,[_cC]));}));case 95:return E(new T(function(){return B(A(_cF,[_cD]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_bT,[function(_cQ){return new F(function(){return A(_cF,[[0,_cQ,_7T]]);});}]));})));})));}));});},_cR=function(_cS){return new F(function(){return A(_cS,[_1k]);});},_cT=function(_cU){var _cV=E(_cU);if(!_cV[0]){return E(_cR);}else{var _cW=_cV[2],_cX=E(E(_cV[1])[1]);switch(_cX){case 9:return function(_cY){return [0,function(_cZ){return E(new T(function(){return B(A(new T(function(){return B(_cT(_cW));}),[_cY]));}));}];};case 10:return function(_d0){return [0,function(_d1){return E(new T(function(){return B(A(new T(function(){return B(_cT(_cW));}),[_d0]));}));}];};case 11:return function(_d2){return [0,function(_d3){return E(new T(function(){return B(A(new T(function(){return B(_cT(_cW));}),[_d2]));}));}];};case 12:return function(_d4){return [0,function(_d5){return E(new T(function(){return B(A(new T(function(){return B(_cT(_cW));}),[_d4]));}));}];};case 13:return function(_d6){return [0,function(_d7){return E(new T(function(){return B(A(new T(function(){return B(_cT(_cW));}),[_d6]));}));}];};case 32:return function(_d8){return [0,function(_d9){return E(new T(function(){return B(A(new T(function(){return B(_cT(_cW));}),[_d8]));}));}];};case 160:return function(_da){return [0,function(_db){return E(new T(function(){return B(A(new T(function(){return B(_cT(_cW));}),[_da]));}));}];};default:var _dc=u_iswspace(_cX),_dd=_dc;return E(_dd)==0?E(_cR):function(_de){return [0,function(_df){return E(new T(function(){return B(A(new T(function(){return B(_cT(_cW));}),[_de]));}));}];};}}},_dg=function(_dh){var _di=new T(function(){return B(_dg(_dh));}),_dj=[1,function(_dk){return new F(function(){return A(_cT,[_dk,function(_dl){return E([0,function(_dm){return E(E(_dm)[1])==92?E(_di):[2];}]);}]);});}];return new F(function(){return _4s([0,function(_dn){return E(E(_dn)[1])==92?E([0,function(_do){var _dp=E(E(_do)[1]);switch(_dp){case 9:return E(_dj);case 10:return E(_dj);case 11:return E(_dj);case 12:return E(_dj);case 13:return E(_dj);case 32:return E(_dj);case 38:return E(_di);case 160:return E(_dj);default:var _dq=u_iswspace(_dp),_dr=_dq;return E(_dr)==0?[2]:E(_dj);}}]):[2];}],[0,function(_ds){var _dt=E(_ds);return E(_dt[1])==92?E(new T(function(){return B(_cE(_dh));})):B(A(_dh,[[0,_dt,_7S]]));}]);});},_du=function(_dv,_dw){return new F(function(){return _dg(function(_dx){var _dy=E(_dx),_dz=E(_dy[1]);if(E(_dz[1])==34){if(!E(_dy[2])){return E(new T(function(){return B(A(_dw,[[1,new T(function(){return B(A(_dv,[_0]));})]]));}));}else{return new F(function(){return _du(function(_dA){return new F(function(){return A(_dv,[[1,_dz,_dA]]);});},_dw);});}}else{return new F(function(){return _du(function(_dB){return new F(function(){return A(_dv,[[1,_dz,_dB]]);});},_dw);});}});});},_dC=new T(function(){return B(unCStr("_\'"));}),_dD=function(_dE){var _dF=u_iswalnum(_dE),_dG=_dF;return E(_dG)==0?B(_7A(_59,[0,_dE],_dC)):true;},_dH=function(_dI){return new F(function(){return _dD(E(_dI)[1]);});},_dJ=new T(function(){return B(unCStr(",;()[]{}`"));}),_dK=function(_dL){return new F(function(){return A(_dL,[_0]);});},_dM=function(_dN,_dO){var _dP=function(_dQ){var _dR=E(_dQ);if(!_dR[0]){return E(_dK);}else{var _dS=_dR[1];return !B(A(_dN,[_dS]))?E(_dK):function(_dT){return [0,function(_dU){return E(new T(function(){return B(A(new T(function(){return B(_dP(_dR[2]));}),[function(_dV){return new F(function(){return A(_dT,[[1,_dS,_dV]]);});}]));}));}];};}};return [1,function(_dW){return new F(function(){return A(_dP,[_dW,_dO]);});}];},_dX=new T(function(){return B(unCStr(".."));}),_dY=new T(function(){return B(unCStr("::"));}),_dZ=new T(function(){return B(unCStr("->"));}),_e0=[0,64],_e1=[1,_e0,_0],_e2=[0,126],_e3=[1,_e2,_0],_e4=new T(function(){return B(unCStr("=>"));}),_e5=[1,_e4,_0],_e6=[1,_e3,_e5],_e7=[1,_e1,_e6],_e8=[1,_dZ,_e7],_e9=new T(function(){return B(unCStr("<-"));}),_ea=[1,_e9,_e8],_eb=[0,124],_ec=[1,_eb,_0],_ed=[1,_ec,_ea],_ee=[1,_bZ,_0],_ef=[1,_ee,_ed],_eg=[0,61],_eh=[1,_eg,_0],_ei=[1,_eh,_ef],_ej=[1,_dY,_ei],_ek=[1,_dX,_ej],_el=function(_em){return new F(function(){return _4s([1,function(_en){return E(_en)[0]==0?E(new T(function(){return B(A(_em,[_64]));})):[2];}],new T(function(){return B(_4s([0,function(_eo){return E(E(_eo)[1])==39?E([0,function(_ep){var _eq=E(_ep);switch(E(_eq[1])){case 39:return [2];case 92:return E(new T(function(){return B(_cE(function(_er){var _es=E(_er);return new F(function(){return (function(_et,_eu){var _ev=new T(function(){return B(A(_em,[[0,_et]]));});return !E(_eu)?E(E(_et)[1])==39?[2]:[0,function(_ew){return E(E(_ew)[1])==39?E(_ev):[2];}]:[0,function(_ex){return E(E(_ex)[1])==39?E(_ev):[2];}];})(_es[1],_es[2]);});}));}));default:return [0,function(_ey){return E(E(_ey)[1])==39?E(new T(function(){return B(A(_em,[[0,_eq]]));})):[2];}];}}]):[2];}],new T(function(){return B(_4s([0,function(_ez){return E(E(_ez)[1])==34?E(new T(function(){return B(_du(_1L,_em));})):[2];}],new T(function(){return B(_4s([0,function(_eA){return !B(_7A(_59,_eA,_dJ))?[2]:B(A(_em,[[2,[1,_eA,_0]]]));}],new T(function(){return B(_4s([0,function(_eB){if(!B(_7A(_59,_eB,_7F))){return [2];}else{return new F(function(){return _dM(_7G,function(_eC){var _eD=[1,_eB,_eC];return !B(_7A(_5q,_eD,_ek))?B(A(_em,[[4,_eD]])):B(A(_em,[[2,_eD]]));});});}}],new T(function(){return B(_4s([0,function(_eE){var _eF=E(_eE),_eG=_eF[1],_eH=u_iswalpha(_eG),_eI=_eH;if(!E(_eI)){if(E(_eG)==95){return new F(function(){return _dM(_dH,function(_eJ){return new F(function(){return A(_em,[[3,[1,_eF,_eJ]]]);});});});}else{return [2];}}else{return new F(function(){return _dM(_dH,function(_eK){return new F(function(){return A(_em,[[3,[1,_eF,_eK]]]);});});});}}],new T(function(){return B(_5K(_7K,_7v,_em));})));})));})));})));})));}));});},_eL=function(_eM){return [1,function(_eN){return new F(function(){return A(_cT,[_eN,function(_eO){return E(new T(function(){return B(_el(_eM));}));}]);});}];},_eP=[0,0],_eQ=function(_eR,_eS){return new F(function(){return _eL(function(_eT){var _eU=E(_eT);if(_eU[0]==2){var _eV=E(_eU[1]);return _eV[0]==0?[2]:E(E(_eV[1])[1])==40?E(_eV[2])[0]==0?E(new T(function(){return B(A(_eR,[_eP,function(_eW){return new F(function(){return _eL(function(_eX){var _eY=E(_eX);if(_eY[0]==2){var _eZ=E(_eY[1]);return _eZ[0]==0?[2]:E(E(_eZ[1])[1])==41?E(_eZ[2])[0]==0?E(new T(function(){return B(A(_eS,[_eW]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_f0=function(_f1,_f2,_f3){var _f4=function(_f5,_f6){return new F(function(){return _4s(B(_eL(function(_f7){var _f8=E(_f7);if(_f8[0]==4){var _f9=E(_f8[1]);if(!_f9[0]){return new F(function(){return A(_f1,[_f8,_f5,_f6]);});}else{return E(E(_f9[1])[1])==45?E(_f9[2])[0]==0?E([1,function(_fa){return new F(function(){return A(_cT,[_fa,function(_fb){return E(new T(function(){return B(_el(function(_fc){return new F(function(){return A(_f1,[_fc,_f5,function(_fd){return new F(function(){return A(_f6,[new T(function(){return [0, -E(_fd)[1]];})]);});}]);});}));}));}]);});}]):B(A(_f1,[_f8,_f5,_f6])):B(A(_f1,[_f8,_f5,_f6]));}}else{return new F(function(){return A(_f1,[_f8,_f5,_f6]);});}})),new T(function(){return B(_eQ(_f4,_f6));}));});};return new F(function(){return _f4(_f2,_f3);});},_fe=function(_ff,_fg){return [2];},_fh=function(_fi,_fj){return new F(function(){return _fe(_fi,_fj);});},_fk=function(_fl){var _fm=E(_fl);return _fm[0]==0?[1,new T(function(){return B(_76(new T(function(){return B(_6W(E(_fm[1])[1]));}),_6V,_fm[2]));})]:E(_fm[2])[0]==0?E(_fm[3])[0]==0?[1,new T(function(){return B(_76(_6U,_6V,_fm[1]));})]:[0]:[0];},_fn=function(_fo){var _fp=E(_fo);if(_fp[0]==5){var _fq=B(_fk(_fp[1]));return _fq[0]==0?E(_fe):function(_fr,_fs){return new F(function(){return A(_fs,[new T(function(){return [0,B(_81(_fq[1]))];})]);});};}else{return E(_fh);}},_ft=function(_fu){return [1,function(_fv){return new F(function(){return A(_cT,[_fv,function(_fw){return E([3,_fu,_5C]);}]);});}];},_fx=new T(function(){return B(_f0(_fn,_eP,_ft));}),_fy=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_fz=new T(function(){return B(err(_fy));}),_fA=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_fB=new T(function(){return B(err(_fA));}),_fC=function(_fD,_fE){if(_fD<=0){if(_fD>=0){return new F(function(){return quot(_fD,_fE);});}else{if(_fE<=0){return new F(function(){return quot(_fD,_fE);});}else{return quot(_fD+1|0,_fE)-1|0;}}}else{if(_fE>=0){if(_fD>=0){return new F(function(){return quot(_fD,_fE);});}else{if(_fE<=0){return new F(function(){return quot(_fD,_fE);});}else{return quot(_fD+1|0,_fE)-1|0;}}}else{return quot(_fD-1|0,_fE)-1|0;}}},_fF=new T(function(){return [0,B(_fC(210,2))];}),_fG=new T(function(){return B(_2s(0,2147483647));}),_fH=function(_fI,_fJ,_fK){return _fK<=_fJ?[1,[0,_fI],new T(function(){var _fL=_fJ-_fI|0,_fM=function(_fN){return _fN>=(_fK-_fL|0)?[1,[0,_fN],new T(function(){return B(_fM(_fN+_fL|0));})]:[1,[0,_fN],_0];};return B(_fM(_fJ));})]:_fK<=_fI?[1,[0,_fI],_0]:[0];},_fO=function(_fP,_fQ,_fR){return _fR>=_fQ?[1,[0,_fP],new T(function(){var _fS=_fQ-_fP|0,_fT=function(_fU){return _fU<=(_fR-_fS|0)?[1,[0,_fU],new T(function(){return B(_fT(_fU+_fS|0));})]:[1,[0,_fU],_0];};return B(_fT(_fQ));})]:_fR>=_fP?[1,[0,_fP],_0]:[0];},_fV=function(_fW,_fX){return _fX<_fW?B(_fH(_fW,_fX,-2147483648)):B(_fO(_fW,_fX,2147483647));},_fY=new T(function(){return B(_fV(135,150));}),_fZ=function(_g0,_g1){var _g2=E(_g0);if(!_g2){return [0];}else{var _g3=E(_g1);return _g3[0]==0?[0]:[1,_g3[1],new T(function(){return B(_fZ(_g2-1|0,_g3[2]));})];}},_g4=new T(function(){return B(_fZ(6,_fY));}),_g5=function(_g6,_g7){var _g8=E(_g6);if(!_g8[0]){return E(_g4);}else{var _g9=_g8[1];return _g7>1?[1,_g9,new T(function(){return B(_g5(_g8[2],_g7-1|0));})]:[1,_g9,_g4];}},_ga=new T(function(){return B(_fV(25,40));}),_gb=new T(function(){return B(_g5(_ga,6));}),_gc=function(_gd){while(1){var _ge=(function(_gf){var _gg=E(_gf);if(!_gg[0]){return [0];}else{var _gh=_gg[2],_gi=E(_gg[1]);if(!E(_gi[2])[0]){return [1,_gi[1],new T(function(){return B(_gc(_gh));})];}else{_gd=_gh;return null;}}})(_gd);if(_ge!=null){return _ge;}}},_gj=function(_gk,_gl){var _gm=E(_gl);if(!_gm[0]){return [0,_0,_0];}else{var _gn=_gm[1];if(!B(A(_gk,[_gn]))){var _go=new T(function(){var _gp=B(_gj(_gk,_gm[2]));return [0,_gp[1],_gp[2]];});return [0,[1,_gn,new T(function(){return E(E(_go)[1]);})],new T(function(){return E(E(_go)[2]);})];}else{return [0,_0,_gm];}}},_gq=function(_gr,_gs){while(1){var _gt=E(_gs);if(!_gt[0]){return [0];}else{if(!B(A(_gr,[_gt[1]]))){return E(_gt);}else{_gs=_gt[2];continue;}}}},_gu=function(_gv){var _gw=E(_gv);switch(_gw){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _gx=u_iswspace(_gw),_gy=_gx;return E(_gy)==0?false:true;}},_gz=function(_gA){return new F(function(){return _gu(E(_gA)[1]);});},_gB=function(_gC){var _gD=B(_gq(_gz,_gC));if(!_gD[0]){return [0];}else{var _gE=new T(function(){var _gF=B(_gj(_gz,_gD));return [0,_gF[1],_gF[2]];});return [1,new T(function(){return E(E(_gE)[1]);}),new T(function(){return B(_gB(E(_gE)[2]));})];}},_gG=function(_gH,_){var _gI=setDropCheckerCallback_ffi(function(_gJ,_gK,_gL){var _gM=E(_gH),_gN=_gM[1],_gO=_gM[2],_gP=new T(function(){return B(_gB(B(_2R(_gJ))));}),_gQ=new T(function(){var _gR=B(_gc(B(_4i(_fx,new T(function(){return B(_2n(2,B(_1f(_gP,2))));})))));return _gR[0]==0?E(_fB):E(_gR[2])[0]==0?E(_gR[1]):E(_fz);}),_gS=new T(function(){var _gT=B(_gc(B(_4i(_fx,new T(function(){return B(_2n(2,B(_1f(_gP,3))));})))));return _gT[0]==0?E(_fB):E(_gT[2])[0]==0?E(_gT[1]):E(_fz);}),_gU=B(_2y(function(_gV){var _gW=E(_gV)[1]-E(_gK)[1];return _gW<0? -_gW<7:_gW<7;},_gb));if(!_gU[0]){return function(_63){return new F(function(){return _2c(_gQ,_gS,_gQ,_gS,_gO,_63);});};}else{var _gX=_gU[1],_gY=function(_gZ,_h0,_){var _h1=E(_gQ),_h2=_h1[1];if(_gZ<=_h2){return new F(function(){return _2c(_h1,_gS,_h1,_gS,_gO,_);});}else{if(_gZ>=0){var _h3=B(_1f(_gN,_gZ)),_h4=new T(function(){return _h2<0;}),_h5=function(_){var _h6=B(_2c(_h1,_gS,_h0,new T(function(){if(_gZ>=0){var _h7=E(B(_1f(_gN,_gZ))[2]);}else{var _h7=E(_1c);}return _h7;}),_gO,_)),_h8=_h6;if(!E(_h4)){var _h9=new T(function(){return B(_2K(function(_ha,_hb,_hc){return [1,new T(function(){var _hd=E(_ha)[1];return _hd!=_h2?_hd!=_gZ?E(_hb):[0,new T(function(){if(_h2>=0){var _he=E(B(_1f(_gN,_h2))[1]);}else{var _he=E(_1c);}return _he;}),new T(function(){return [0,E(E(_hb)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_hb)[1]);}),new T(function(){return [0,E(E(_hb)[2])[1]-1|0];})];}),_hc];},_0,_fG,_gN));}),_hf=B((function(_hg,_){while(1){var _hh=(function(_hi,_){var _hj=E(_hi);if(!_hj[0]){return _1k;}else{var _hk=_hj[1],_hl=B(_2c(_h1,_hk,_h1,new T(function(){return [0,E(_hk)[1]-1|0];}),_gO,_)),_hm=_hl;_hg=_hj[2];return null;}})(_hg,_);if(_hh!=null){return _hh;}}})(B(_2n(1,B(_2s(E(_gS)[1],E(B(_1f(_h9,_h2))[2])[1])))),_)),_hn=_hf;return new F(function(){return _gG([0,_h9,_gO,_gM[3]],_);});}else{return E(_1c);}},_ho=function(_){return E(_h3[2])[1]>=2?B(_2c(_h1,_gS,_h1,_gS,_gO,_)):B(_h5(_));};switch(E(_h3[1])){case 0:if(!E(_h4)){switch(E(B(_1f(_gN,_h2))[1])){case 0:return new F(function(){return _h5(_);});break;case 1:return new F(function(){return _ho(_);});break;default:return new F(function(){return _ho(_);});}}else{return E(_1c);}break;case 1:return !E(_h4)?E(B(_1f(_gN,_h2))[1])==1?B(_h5(_)):B(_ho(_)):E(_1c);default:return !E(_h4)?E(B(_1f(_gN,_h2))[1])==2?B(_h5(_)):B(_ho(_)):E(_1c);}}else{return E(_1c);}}};if(E(_gL)[1]<=E(_fF)[1]){var _hp=E(_gX);return function(_63){return new F(function(){return _gY(_hp[1],_hp,_63);});};}else{var _hq=23-E(_gX)[1]|0;return function(_63){return new F(function(){return _gY(_hq,[0,_hq],_63);});};}}});return _1k;},_hr=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:129:5-10"));}),_hs=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_ht=new T(function(){return B(unCStr("base"));}),_hu=new T(function(){return B(unCStr("IOException"));}),_hv=new T(function(){var _hw=hs_wordToWord64(4053623282),_hx=_hw,_hy=hs_wordToWord64(3693590983),_hz=_hy;return [0,_hx,_hz,[0,_hx,_hz,_ht,_hs,_hu],_0];}),_hA=function(_hB){return E(_hv);},_hC=function(_hD){var _hE=E(_hD);return new F(function(){return _37(B(_33(_hE[1])),_hA,_hE[2]);});},_hF=new T(function(){return B(unCStr(": "));}),_hG=[0,41],_hH=new T(function(){return B(unCStr(" ("));}),_hI=new T(function(){return B(unCStr("already exists"));}),_hJ=new T(function(){return B(unCStr("does not exist"));}),_hK=new T(function(){return B(unCStr("protocol error"));}),_hL=new T(function(){return B(unCStr("failed"));}),_hM=new T(function(){return B(unCStr("invalid argument"));}),_hN=new T(function(){return B(unCStr("inappropriate type"));}),_hO=new T(function(){return B(unCStr("hardware fault"));}),_hP=new T(function(){return B(unCStr("unsupported operation"));}),_hQ=new T(function(){return B(unCStr("timeout"));}),_hR=new T(function(){return B(unCStr("resource vanished"));}),_hS=new T(function(){return B(unCStr("interrupted"));}),_hT=new T(function(){return B(unCStr("resource busy"));}),_hU=new T(function(){return B(unCStr("resource exhausted"));}),_hV=new T(function(){return B(unCStr("end of file"));}),_hW=new T(function(){return B(unCStr("illegal operation"));}),_hX=new T(function(){return B(unCStr("permission denied"));}),_hY=new T(function(){return B(unCStr("user error"));}),_hZ=new T(function(){return B(unCStr("unsatisified constraints"));}),_i0=new T(function(){return B(unCStr("system error"));}),_i1=function(_i2,_i3){switch(E(_i2)){case 0:return new F(function(){return _1u(_hI,_i3);});break;case 1:return new F(function(){return _1u(_hJ,_i3);});break;case 2:return new F(function(){return _1u(_hT,_i3);});break;case 3:return new F(function(){return _1u(_hU,_i3);});break;case 4:return new F(function(){return _1u(_hV,_i3);});break;case 5:return new F(function(){return _1u(_hW,_i3);});break;case 6:return new F(function(){return _1u(_hX,_i3);});break;case 7:return new F(function(){return _1u(_hY,_i3);});break;case 8:return new F(function(){return _1u(_hZ,_i3);});break;case 9:return new F(function(){return _1u(_i0,_i3);});break;case 10:return new F(function(){return _1u(_hK,_i3);});break;case 11:return new F(function(){return _1u(_hL,_i3);});break;case 12:return new F(function(){return _1u(_hM,_i3);});break;case 13:return new F(function(){return _1u(_hN,_i3);});break;case 14:return new F(function(){return _1u(_hO,_i3);});break;case 15:return new F(function(){return _1u(_hP,_i3);});break;case 16:return new F(function(){return _1u(_hQ,_i3);});break;case 17:return new F(function(){return _1u(_hR,_i3);});break;default:return new F(function(){return _1u(_hS,_i3);});}},_i4=[0,125],_i5=new T(function(){return B(unCStr("{handle: "));}),_i6=function(_i7,_i8,_i9,_ia,_ib,_ic){var _id=new T(function(){var _ie=new T(function(){return B(_i1(_i8,new T(function(){var _if=E(_ia);return _if[0]==0?E(_ic):B(_1u(_hH,new T(function(){return B(_1u(_if,[1,_hG,_ic]));})));})));}),_ig=E(_i9);return _ig[0]==0?E(_ie):B(_1u(_ig,new T(function(){return B(_1u(_hF,_ie));})));}),_ih=E(_ib);if(!_ih[0]){var _ii=E(_i7);if(!_ii[0]){return E(_id);}else{var _ij=E(_ii[1]);return _ij[0]==0?B(_1u(_i5,new T(function(){return B(_1u(_ij[1],[1,_i4,new T(function(){return B(_1u(_hF,_id));})]));}))):B(_1u(_i5,new T(function(){return B(_1u(_ij[1],[1,_i4,new T(function(){return B(_1u(_hF,_id));})]));})));}}else{return new F(function(){return _1u(_ih[1],new T(function(){return B(_1u(_hF,_id));}));});}},_ik=function(_il){var _im=E(_il);return new F(function(){return _i6(_im[1],_im[2],_im[3],_im[4],_im[6],_0);});},_in=function(_io,_ip){var _iq=E(_io);return new F(function(){return _i6(_iq[1],_iq[2],_iq[3],_iq[4],_iq[6],_ip);});},_ir=function(_is,_it){return new F(function(){return _3x(_in,_is,_it);});},_iu=function(_iv,_iw,_ix){var _iy=E(_iw);return new F(function(){return _i6(_iy[1],_iy[2],_iy[3],_iy[4],_iy[6],_ix);});},_iz=[0,_iu,_ik,_ir],_iA=new T(function(){return [0,_hA,_iz,_iB,_hC];}),_iB=function(_iC){return [0,_iA,_iC];},_iD=7,_iE=function(_iF){return [0,_7m,_iD,_0,_iF,_7m,_7m];},_iG=function(_iH,_){return new F(function(){return die(new T(function(){return B(_iB(new T(function(){return B(_iE(_iH));})));}));});},_iI=function(_iJ,_){return new F(function(){return _iG(_iJ,_);});},_iK=[0,114],_iL=[1,_iK,_0],_iM=new T(function(){return B(_1F(0,6,_0));}),_iN=new T(function(){return B(unCStr("cx"));}),_iO=new T(function(){return B(unCStr("cy"));}),_iP=new T(function(){return B(unCStr("circle"));}),_iQ=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_iR=new T(function(){return B(unCStr("board"));}),_iS=function(_){return _1k;},_iT=function(_iU,_iV,_){while(1){var _iW=(function(_iX,_iY,_){var _iZ=E(_iY);if(!_iZ[0]){return _1k;}else{var _j0=E(_iZ[1]),_j1=_j0[1],_j2=[0,_iX],_j3=B(A(_2K,[function(_j4,_j5,_j6,_){var _j7=jsFind(toJSStr(E(_iR))),_j8=_j7,_j9=E(_j8);if(!_j9[0]){var _ja=B(_iI(_hr,_)),_jb=_ja;return new F(function(){return A(_j6,[_]);});}else{var _jc=jsCreateElemNS(toJSStr(E(_iQ)),toJSStr(E(_iP))),_jd=_jc,_je=[0,_jd],_jf=B(A(_1o,[_1L,_je,_iL,_iM,_])),_jg=_jf,_jh=new T(function(){var _ji=B(_20(_j2,_j4));return [0,_ji[1],_ji[2]];}),_jj=B(A(_1o,[_1L,_je,_iN,new T(function(){return B(_1F(0,E(E(_jh)[1])[1],_0));}),_])),_jk=_jj,_jl=B(A(_1o,[_1L,_je,_iO,new T(function(){return B(_1F(0,E(E(_jh)[2])[1],_0));}),_])),_jm=_jl,_jn=B(A(_1P,[_je,_m,_j2,_j4,_j5,_])),_jo=_jn,_jp=jsAppendChild(_jd,E(_j9[1])[1]);return new F(function(){return A(_j6,[_]);});}},_iS,_fG,new T(function(){var _jq=E(_j0[2])[1];if(_jq>0){var _jr=function(_js){return _js>1?[1,_j1,new T(function(){return B(_jr(_js-1|0));})]:E([1,_j1,_0]);},_jt=B(_jr(_jq));}else{var _jt=[0];}var _ju=_jt;return _ju;}),_])),_jv=_j3,_jw=E(_iX);if(_jw==2147483647){return _1k;}else{_iU=_jw+1|0;_iV=_iZ[2];return null;}}})(_iU,_iV,_);if(_iW!=null){return _iW;}}},_jx=function(_){var _jy=B(_iT(0,_19,_)),_jz=_jy;return new F(function(){return _gG(_1a,_);});},_jA=function(_){return new F(function(){return _jx(_);});};
var hasteMain = function() {B(A(_jA, [0]));};window.onload = hasteMain;