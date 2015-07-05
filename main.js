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

var _0=[0],_1=function(_2,_3){while(1){var _4=E(_2);if(!_4[0]){return E(_3);}else{_2=_4[2];var _5=[1,_4[1],_3];_3=_5;continue;}}},_6=[0,2],_7=[0,0],_8=[1,_7,_0],_9=[1,_7,_8],_a=[1,_7,_9],_b=[1,_7,_a],_c=[1,_7,_b],_d=[0,5],_e=[1,_d,_c],_f=[1,_7,_e],_g=[0,3],_h=[1,_g,_f],_i=[1,_7,_h],_j=[1,_7,_i],_k=[1,_7,_j],_l=[1,_7,_k],_m=[1,_d,_l],_n=[1,_7,_m],_o=[1,_7,_n],_p=[1,_7,_o],_q=[1,_7,_p],_r=[1,_7,_q],_s=[1,_7,_r],_t=[1,_7,_s],_u=[1,_7,_t],_v=[1,_7,_u],_w=[1,_7,_v],_x=[1,_6,_w],_y=1,_z=function(_A){var _B=E(_A);return _B[0]==0?[0]:[1,[0,_y,_B[1]],new T(function(){return B(_z(_B[2]));})];},_C=new T(function(){return B(_z(_x));}),_D=new T(function(){return B(_1(_C,_0));}),_E=0,_F=new T(function(){return B(unCStr("Control.Exception.Base"));}),_G=new T(function(){return B(unCStr("base"));}),_H=new T(function(){return B(unCStr("PatternMatchFail"));}),_I=new T(function(){var _J=hs_wordToWord64(18445595),_K=_J,_L=hs_wordToWord64(52003073),_M=_L;return [0,_K,_M,[0,_K,_M,_G,_F,_H],_0];}),_N=function(_O){return E(_I);},_P=function(_Q){return E(E(_Q)[1]);},_R=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_S=new T(function(){return B(err(_R));}),_T=function(_U,_V,_W){var _X=new T(function(){var _Y=B(A(_U,[_W])),_Z=B(A(_V,[new T(function(){var _10=E(_X);return _10[0]==0?E(_S):E(_10[1]);})])),_11=hs_eqWord64(_Y[1],_Z[1]),_12=_11;if(!E(_12)){var _13=[0];}else{var _14=hs_eqWord64(_Y[2],_Z[2]),_15=_14,_13=E(_15)==0?[0]:[1,_W];}var _16=_13,_17=_16;return _17;});return E(_X);},_18=function(_19){var _1a=E(_19);return new F(function(){return _T(B(_P(_1a[1])),_N,_1a[2]);});},_1b=function(_1c){return E(E(_1c)[1]);},_1d=function(_1e,_1f){var _1g=E(_1e);return _1g[0]==0?E(_1f):[1,_1g[1],new T(function(){return B(_1d(_1g[2],_1f));})];},_1h=function(_1i,_1j){return new F(function(){return _1d(E(_1i)[1],_1j);});},_1k=[0,44],_1l=[0,93],_1m=[0,91],_1n=function(_1o,_1p,_1q){var _1r=E(_1p);return _1r[0]==0?B(unAppCStr("[]",_1q)):[1,_1m,new T(function(){return B(A(_1o,[_1r[1],new T(function(){var _1s=function(_1t){var _1u=E(_1t);return _1u[0]==0?E([1,_1l,_1q]):[1,_1k,new T(function(){return B(A(_1o,[_1u[1],new T(function(){return B(_1s(_1u[2]));})]));})];};return B(_1s(_1r[2]));})]));})];},_1v=function(_1w,_1x){return new F(function(){return _1n(_1h,_1w,_1x);});},_1y=function(_1z,_1A,_1B){return new F(function(){return _1d(E(_1A)[1],_1B);});},_1C=[0,_1y,_1b,_1v],_1D=new T(function(){return [0,_N,_1C,_1E,_18];}),_1E=function(_1F){return [0,_1D,_1F];},_1G=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_1H=function(_1I,_1J){return new F(function(){return die(new T(function(){return B(A(_1J,[_1I]));}));});},_1K=function(_1L,_1M){var _1N=E(_1M);if(!_1N[0]){return [0,_0,_0];}else{var _1O=_1N[1];if(!B(A(_1L,[_1O]))){return [0,_0,_1N];}else{var _1P=new T(function(){var _1Q=B(_1K(_1L,_1N[2]));return [0,_1Q[1],_1Q[2]];});return [0,[1,_1O,new T(function(){return E(E(_1P)[1]);})],new T(function(){return E(E(_1P)[2]);})];}}},_1R=[0,32],_1S=[0,10],_1T=[1,_1S,_0],_1U=function(_1V){return E(E(_1V)[1])==124?false:true;},_1W=function(_1X,_1Y){var _1Z=B(_1K(_1U,B(unCStr(_1X)))),_20=_1Z[1],_21=function(_22,_23){return new F(function(){return _1d(_22,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_1d(_1Y,new T(function(){return B(_1d(_23,_1T));})));})));}));});},_24=E(_1Z[2]);if(!_24[0]){return new F(function(){return _21(_20,_0);});}else{return E(E(_24[1])[1])==124?B(_21(_20,[1,_1R,_24[2]])):B(_21(_20,_0));}},_25=function(_26){return new F(function(){return _1H([0,new T(function(){return B(_1W(_26,_1G));})],_1E);});},_27=new T(function(){return B(_25("main.hs:(229,20)-(230,55)|function whiteOrBlack"));}),_28=function(_29,_2a){var _2b=E(_29);if(!_2b[0]){return [0];}else{var _2c=E(_2a);return _2c[0]==0?[0]:[1,new T(function(){var _2d=E(_2c[1]);if(!E(_2d[1])){var _2e=E(_27);}else{if(!E(E(_2d[2])[1])){var _2f=E(_2b[1]),_2g=E(_2f[1])==0?E(_2f):[0,_E,_2f[2]];}else{var _2g=E(_2d);}var _2h=_2g,_2e=_2h;}var _2i=_2e;return _2i;}),new T(function(){return B(_28(_2b[2],_2c[2]));})];}},_2j=new T(function(){return B(_28(_D,_C));}),_2k=[0,_2j,_7,_7,_7,_7,_y,_y],_2l=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_2m=new T(function(){return B(err(_2l));}),_2n=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_2o=new T(function(){return B(err(_2n));}),_2p=function(_2q,_2r){while(1){var _2s=E(_2q);if(!_2s[0]){return E(_2o);}else{var _2t=E(_2r);if(!_2t){return E(_2s[1]);}else{_2q=_2s[2];_2r=_2t-1|0;continue;}}}},_2u=0,_2v=new T(function(){return B(unCStr("White"));}),_2w=new T(function(){return B(unCStr("Black"));}),_2x=function(_2y,_2z,_2A,_2B){return new F(function(){return A(_2y,[new T(function(){return function(_){var _2C=jsSetAttr(E(_2z)[1],toJSStr(E(_2A)),toJSStr(E(_2B)));return _2u;};})]);});},_2D=function(_2E,_2F){var _2G=jsShowI(_2E),_2H=_2G;return new F(function(){return _1d(fromJSStr(_2H),_2F);});},_2I=[0,41],_2J=[0,40],_2K=function(_2L,_2M,_2N){return _2M>=0?B(_2D(_2M,_2N)):_2L<=6?B(_2D(_2M,_2N)):[1,_2J,new T(function(){var _2O=jsShowI(_2M),_2P=_2O;return B(_1d(fromJSStr(_2P),[1,_2I,_2N]));})];},_2Q=new T(function(){return B(_25("main.hs:115:1-82|function checkerPositionClass"));}),_2R=function(_2S){var _2T=E(_2S);return _2T[0]==0?B(unAppCStr(" pi",new T(function(){return B(_1d(B(_2K(0,E(_2T[1])[1],_0)),new T(function(){return B(unAppCStr(" ci",new T(function(){return B(_2K(0,E(_2T[2])[1],_0));})));})));}))):E(_2Q);},_2U=function(_2V){return E(_2V);},_2W=new T(function(){return B(unCStr("class"));}),_2X=new T(function(){return B(unCStr("draggable "));}),_2Y=function(_2Z,_30,_31,_32){return new F(function(){return _2x(_2U,_2Z,_2W,new T(function(){var _33=new T(function(){return E(_32)==0?B(_1d(_2w,new T(function(){return B(_2R(_31));}))):B(_1d(_2v,new T(function(){return B(_2R(_31));})));});return E(_30)==0?E(_32)==0?B(_1d(_2X,_33)):E(_33):E(_32)==0?E(_33):B(_1d(_2X,_33));}));});},_34=new T(function(){return B(_25("main.hs:(76,1)-(97,14)|function checkerPosition"));}),_35=function(_36){var _37=E(_36);if(!_37[0]){var _38=_37[1],_39=_37[2];return [0,new T(function(){var _3a=E(_38)[1];if(_3a>=12){var _3b=23-_3a|0;if(_3b>=6){var _3c=[0,25+(20+(imul(_3b,15)|0)|0)|0];}else{var _3c=[0,25+(imul(_3b,15)|0)|0];}var _3d=_3c,_3e=_3d;}else{if(_3a>=6){var _3f=[0,25+(20+(imul(_3a,15)|0)|0)|0];}else{var _3f=[0,25+(imul(_3a,15)|0)|0];}var _3e=_3f;}var _3g=_3e;return _3g;}),new T(function(){if(E(_38)[1]>=12){var _3h=[0,203+(imul(imul(imul(-1,E(_39)[1])|0,2)|0,6)|0)|0];}else{var _3h=[0,7+(imul(imul(E(_39)[1],2)|0,6)|0)|0];}var _3i=_3h;return _3i;})];}else{return E(_34);}},_3j=function(_3k,_3l,_3m,_){var _3n=jsElemsByClassName(toJSStr(B(_2R(_3k)))),_3o=_3n,_3p=B(_2p(_3o,0)),_3q=B(_35(_3l)),_3r=animateCircle_ffi(_3p[1],E(_3q[1])[1],E(_3q[2])[1],300);return new F(function(){return A(_2Y,[_3p,_3m,_3l,_3m,_]);});},_3s=function(_3t,_3u){while(1){var _3v=E(_3t);if(!_3v){return E(_3u);}else{var _3w=E(_3u);if(!_3w[0]){return [0];}else{_3t=_3v-1|0;_3u=_3w[2];continue;}}}},_3x=function(_3y,_3z){if(_3y<=_3z){var _3A=function(_3B){return [1,[0,_3B],new T(function(){if(_3B!=_3z){var _3C=B(_3A(_3B+1|0));}else{var _3C=[0];}return _3C;})];};return new F(function(){return _3A(_3y);});}else{return [0];}},_3D=function(_3E,_3F){var _3G=function(_3H,_3I){while(1){var _3J=(function(_3K,_3L){var _3M=E(_3L);if(!_3M[0]){return [0];}else{var _3N=_3M[2];if(!B(A(_3E,[_3M[1]]))){var _3O=_3K+1|0;_3I=_3N;_3H=_3O;return null;}else{return [1,[0,_3K],new T(function(){return B(_3G(_3K+1|0,_3N));})];}}})(_3H,_3I);if(_3J!=null){return _3J;}}};return new F(function(){return _3G(0,_3F);});},_3P=function(_3Q,_3R,_3S,_3T){var _3U=E(_3S);if(!_3U[0]){return E(_3R);}else{var _3V=E(_3T);if(!_3V[0]){return E(_3R);}else{return new F(function(){return A(_3Q,[_3U[1],_3V[1],new T(function(){return B(_3P(_3Q,_3R,_3U[2],_3V[2]));})]);});}}},_3W=function(_3X){return new F(function(){return fromJSStr(E(_3X)[1]);});},_3Y=function(_3Z,_40){if(_3Z<=0){if(_3Z>=0){return new F(function(){return quot(_3Z,_40);});}else{if(_40<=0){return new F(function(){return quot(_3Z,_40);});}else{return quot(_3Z+1|0,_40)-1|0;}}}else{if(_40>=0){if(_3Z>=0){return new F(function(){return quot(_3Z,_40);});}else{if(_40<=0){return new F(function(){return quot(_3Z,_40);});}else{return quot(_3Z+1|0,_40)-1|0;}}}else{return quot(_3Z-1|0,_40)-1|0;}}},_41=new T(function(){return [0,B(_3Y(210,2))];}),_42=new T(function(){return B(_3x(0,2147483647));}),_43=new T(function(){return B(_25("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_44=function(_45,_46){while(1){var _47=(function(_48,_49){var _4a=E(_48);switch(_4a[0]){case 0:var _4b=E(_49);if(!_4b[0]){return [0];}else{_45=B(A(_4a[1],[_4b[1]]));_46=_4b[2];return null;}break;case 1:var _4c=B(A(_4a[1],[_49])),_4d=_49;_45=_4c;_46=_4d;return null;case 2:return [0];case 3:return [1,[0,_4a[1],_49],new T(function(){return B(_44(_4a[2],_49));})];default:return E(_4a[1]);}})(_45,_46);if(_47!=null){return _47;}}},_4e=function(_4f,_4g){var _4h=new T(function(){var _4i=E(_4g);if(_4i[0]==3){var _4j=[3,_4i[1],new T(function(){return B(_4e(_4f,_4i[2]));})];}else{var _4k=E(_4f);if(_4k[0]==2){var _4l=E(_4i);}else{var _4m=E(_4i);if(_4m[0]==2){var _4n=E(_4k);}else{var _4o=new T(function(){var _4p=E(_4m);if(_4p[0]==4){var _4q=[1,function(_4r){return [4,new T(function(){return B(_1d(B(_44(_4k,_4r)),_4p[1]));})];}];}else{var _4s=E(_4k);if(_4s[0]==1){var _4t=_4s[1],_4u=E(_4p);if(!_4u[0]){var _4v=[1,function(_4w){return new F(function(){return _4e(B(A(_4t,[_4w])),_4u);});}];}else{var _4v=[1,function(_4x){return new F(function(){return _4e(B(A(_4t,[_4x])),new T(function(){return B(A(_4u[1],[_4x]));}));});}];}var _4y=_4v;}else{var _4z=E(_4p);if(!_4z[0]){var _4A=E(_43);}else{var _4A=[1,function(_4B){return new F(function(){return _4e(_4s,new T(function(){return B(A(_4z[1],[_4B]));}));});}];}var _4y=_4A;}var _4q=_4y;}return _4q;}),_4C=E(_4k);switch(_4C[0]){case 1:var _4D=E(_4m);if(_4D[0]==4){var _4E=[1,function(_4F){return [4,new T(function(){return B(_1d(B(_44(B(A(_4C[1],[_4F])),_4F)),_4D[1]));})];}];}else{var _4E=E(_4o);}var _4G=_4E;break;case 4:var _4H=_4C[1],_4I=E(_4m);switch(_4I[0]){case 0:var _4J=[1,function(_4K){return [4,new T(function(){return B(_1d(_4H,new T(function(){return B(_44(_4I,_4K));})));})];}];break;case 1:var _4J=[1,function(_4L){return [4,new T(function(){return B(_1d(_4H,new T(function(){return B(_44(B(A(_4I[1],[_4L])),_4L));})));})];}];break;default:var _4J=[4,new T(function(){return B(_1d(_4H,_4I[1]));})];}var _4G=_4J;break;default:var _4G=E(_4o);}var _4n=_4G;}var _4l=_4n;}var _4j=_4l;}return _4j;}),_4M=E(_4f);switch(_4M[0]){case 0:var _4N=E(_4g);return _4N[0]==0?[0,function(_4O){return new F(function(){return _4e(B(A(_4M[1],[_4O])),new T(function(){return B(A(_4N[1],[_4O]));}));});}]:E(_4h);case 3:return [3,_4M[1],new T(function(){return B(_4e(_4M[2],_4g));})];default:return E(_4h);}},_4P=function(_4Q,_4R){return E(_4Q)[1]!=E(_4R)[1];},_4S=function(_4T,_4U){return E(_4T)[1]==E(_4U)[1];},_4V=[0,_4S,_4P],_4W=function(_4X){return E(E(_4X)[1]);},_4Y=function(_4Z,_50,_51){while(1){var _52=E(_50);if(!_52[0]){return E(_51)[0]==0?true:false;}else{var _53=E(_51);if(!_53[0]){return false;}else{if(!B(A(_4W,[_4Z,_52[1],_53[1]]))){return false;}else{_50=_52[2];_51=_53[2];continue;}}}}},_54=function(_55,_56,_57){return !B(_4Y(_55,_56,_57))?true:false;},_58=function(_59){return [0,function(_5a,_5b){return new F(function(){return _4Y(_59,_5a,_5b);});},function(_5a,_5b){return new F(function(){return _54(_59,_5a,_5b);});}];},_5c=new T(function(){return B(_58(_4V));}),_5d=function(_5e,_5f){var _5g=E(_5e);switch(_5g[0]){case 0:return [0,function(_5h){return new F(function(){return _5d(B(A(_5g[1],[_5h])),_5f);});}];case 1:return [1,function(_5i){return new F(function(){return _5d(B(A(_5g[1],[_5i])),_5f);});}];case 2:return [2];case 3:return new F(function(){return _4e(B(A(_5f,[_5g[1]])),new T(function(){return B(_5d(_5g[2],_5f));}));});break;default:var _5j=function(_5k){var _5l=E(_5k);if(!_5l[0]){return [0];}else{var _5m=E(_5l[1]);return new F(function(){return _1d(B(_44(B(A(_5f,[_5m[1]])),_5m[2])),new T(function(){return B(_5j(_5l[2]));}));});}},_5n=B(_5j(_5g[1]));return _5n[0]==0?[2]:[4,_5n];}},_5o=[2],_5p=function(_5q){return [3,_5q,_5o];},_5r=function(_5s,_5t){var _5u=E(_5s);if(!_5u){return new F(function(){return A(_5t,[_2u]);});}else{return [0,function(_5v){return E(new T(function(){return B(_5r(_5u-1|0,_5t));}));}];}},_5w=function(_5x,_5y,_5z){return [1,function(_5A){return new F(function(){return A(function(_5B,_5C,_5D){while(1){var _5E=(function(_5F,_5G,_5H){var _5I=E(_5F);switch(_5I[0]){case 0:var _5J=E(_5G);if(!_5J[0]){return E(_5y);}else{_5B=B(A(_5I[1],[_5J[1]]));_5C=_5J[2];var _5K=_5H+1|0;_5D=_5K;return null;}break;case 1:var _5L=B(A(_5I[1],[_5G])),_5M=_5G,_5K=_5H;_5B=_5L;_5C=_5M;_5D=_5K;return null;case 2:return E(_5y);case 3:return function(_5N){return new F(function(){return _5r(_5H,function(_5O){return E(new T(function(){return B(_5d(_5I,_5N));}));});});};default:return function(_5P){return new F(function(){return _5d(_5I,_5P);});};}})(_5B,_5C,_5D);if(_5E!=null){return _5E;}}},[new T(function(){return B(A(_5x,[_5p]));}),_5A,0,_5z]);});}];},_5Q=[6],_5R=new T(function(){return B(unCStr("valDig: Bad base"));}),_5S=new T(function(){return B(err(_5R));}),_5T=function(_5U,_5V){var _5W=function(_5X,_5Y){var _5Z=E(_5X);if(!_5Z[0]){return function(_60){return new F(function(){return A(_60,[new T(function(){return B(A(_5Y,[_0]));})]);});};}else{var _61=E(_5Z[1])[1],_62=function(_63){return function(_64){return [0,function(_65){return E(new T(function(){return B(A(new T(function(){return B(_5W(_5Z[2],function(_66){return new F(function(){return A(_5Y,[[1,_63,_66]]);});}));}),[_64]));}));}];};};switch(E(E(_5U)[1])){case 8:if(48>_61){return function(_67){return new F(function(){return A(_67,[new T(function(){return B(A(_5Y,[_0]));})]);});};}else{if(_61>55){return function(_68){return new F(function(){return A(_68,[new T(function(){return B(A(_5Y,[_0]));})]);});};}else{return new F(function(){return _62([0,_61-48|0]);});}}break;case 10:if(48>_61){return function(_69){return new F(function(){return A(_69,[new T(function(){return B(A(_5Y,[_0]));})]);});};}else{if(_61>57){return function(_6a){return new F(function(){return A(_6a,[new T(function(){return B(A(_5Y,[_0]));})]);});};}else{return new F(function(){return _62([0,_61-48|0]);});}}break;case 16:var _6b=new T(function(){if(97>_61){if(65>_61){var _6c=[0];}else{if(_61>70){var _6d=[0];}else{var _6d=[1,[0,(_61-65|0)+10|0]];}var _6c=_6d;}var _6e=_6c;}else{if(_61>102){if(65>_61){var _6f=[0];}else{if(_61>70){var _6g=[0];}else{var _6g=[1,[0,(_61-65|0)+10|0]];}var _6f=_6g;}var _6h=_6f;}else{var _6h=[1,[0,(_61-97|0)+10|0]];}var _6e=_6h;}return _6e;});if(48>_61){var _6i=E(_6b);if(!_6i[0]){return function(_6j){return new F(function(){return A(_6j,[new T(function(){return B(A(_5Y,[_0]));})]);});};}else{return new F(function(){return _62(_6i[1]);});}}else{if(_61>57){var _6k=E(_6b);if(!_6k[0]){return function(_6l){return new F(function(){return A(_6l,[new T(function(){return B(A(_5Y,[_0]));})]);});};}else{return new F(function(){return _62(_6k[1]);});}}else{return new F(function(){return _62([0,_61-48|0]);});}}break;default:return E(_5S);}}};return [1,function(_6m){return new F(function(){return A(_5W,[_6m,_2U,function(_6n){var _6o=E(_6n);return _6o[0]==0?[2]:B(A(_5V,[_6o]));}]);});}];},_6p=[0,10],_6q=[0,1],_6r=[0,2147483647],_6s=function(_6t,_6u){while(1){var _6v=E(_6t);if(!_6v[0]){var _6w=_6v[1],_6x=E(_6u);if(!_6x[0]){var _6y=_6x[1],_6z=addC(_6w,_6y);if(!E(_6z[2])){return [0,_6z[1]];}else{_6t=[1,I_fromInt(_6w)];_6u=[1,I_fromInt(_6y)];continue;}}else{_6t=[1,I_fromInt(_6w)];_6u=_6x;continue;}}else{var _6A=E(_6u);if(!_6A[0]){_6t=_6v;_6u=[1,I_fromInt(_6A[1])];continue;}else{return [1,I_add(_6v[1],_6A[1])];}}}},_6B=new T(function(){return B(_6s(_6r,_6q));}),_6C=function(_6D){var _6E=E(_6D);if(!_6E[0]){var _6F=E(_6E[1]);return _6F==(-2147483648)?E(_6B):[0, -_6F];}else{return [1,I_negate(_6E[1])];}},_6G=[0,10],_6H=[0,0],_6I=function(_6J){return [0,_6J];},_6K=function(_6L,_6M){while(1){var _6N=E(_6L);if(!_6N[0]){var _6O=_6N[1],_6P=E(_6M);if(!_6P[0]){var _6Q=_6P[1];if(!(imul(_6O,_6Q)|0)){return [0,imul(_6O,_6Q)|0];}else{_6L=[1,I_fromInt(_6O)];_6M=[1,I_fromInt(_6Q)];continue;}}else{_6L=[1,I_fromInt(_6O)];_6M=_6P;continue;}}else{var _6R=E(_6M);if(!_6R[0]){_6L=_6N;_6M=[1,I_fromInt(_6R[1])];continue;}else{return [1,I_mul(_6N[1],_6R[1])];}}}},_6S=function(_6T,_6U,_6V){while(1){var _6W=E(_6V);if(!_6W[0]){return E(_6U);}else{var _6X=B(_6s(B(_6K(_6U,_6T)),B(_6I(E(_6W[1])[1]))));_6V=_6W[2];_6U=_6X;continue;}}},_6Y=function(_6Z){var _70=new T(function(){return B(_4e(B(_4e([0,function(_71){if(E(E(_71)[1])==45){return new F(function(){return _5T(_6p,function(_72){return new F(function(){return A(_6Z,[[1,new T(function(){return B(_6C(B(_6S(_6G,_6H,_72))));})]]);});});});}else{return [2];}}],[0,function(_73){if(E(E(_73)[1])==43){return new F(function(){return _5T(_6p,function(_74){return new F(function(){return A(_6Z,[[1,new T(function(){return B(_6S(_6G,_6H,_74));})]]);});});});}else{return [2];}}])),new T(function(){return B(_5T(_6p,function(_75){return new F(function(){return A(_6Z,[[1,new T(function(){return B(_6S(_6G,_6H,_75));})]]);});}));})));});return new F(function(){return _4e([0,function(_76){return E(E(_76)[1])==101?E(_70):[2];}],[0,function(_77){return E(E(_77)[1])==69?E(_70):[2];}]);});},_78=[0],_79=function(_7a){return new F(function(){return A(_7a,[_78]);});},_7b=function(_7c){return new F(function(){return A(_7c,[_78]);});},_7d=function(_7e){return [0,function(_7f){return E(E(_7f)[1])==46?E(new T(function(){return B(_5T(_6p,function(_7g){return new F(function(){return A(_7e,[[1,_7g]]);});}));})):[2];}];},_7h=function(_7i){return new F(function(){return _5T(_6p,function(_7j){return new F(function(){return _5w(_7d,_79,function(_7k){return new F(function(){return _5w(_6Y,_7b,function(_7l){return new F(function(){return A(_7i,[[5,[1,_7j,_7k,_7l]]]);});});});});});});});},_7m=function(_7n,_7o,_7p){while(1){var _7q=E(_7p);if(!_7q[0]){return false;}else{if(!B(A(_4W,[_7n,_7o,_7q[1]]))){_7p=_7q[2];continue;}else{return true;}}}},_7r=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_7s=function(_7t){return new F(function(){return _7m(_4V,_7t,_7r);});},_7u=[0,8],_7v=[0,16],_7w=function(_7x){return [0,function(_7y){return E(E(_7y)[1])==48?E([0,function(_7z){switch(E(E(_7z)[1])){case 79:return E(new T(function(){return B(_5T(_7u,function(_7A){return new F(function(){return A(_7x,[[5,[0,_7u,_7A]]]);});}));}));case 88:return E(new T(function(){return B(_5T(_7v,function(_7B){return new F(function(){return A(_7x,[[5,[0,_7v,_7B]]]);});}));}));case 111:return E(new T(function(){return B(_5T(_7u,function(_7C){return new F(function(){return A(_7x,[[5,[0,_7u,_7C]]]);});}));}));case 120:return E(new T(function(){return B(_5T(_7v,function(_7D){return new F(function(){return A(_7x,[[5,[0,_7v,_7D]]]);});}));}));default:return [2];}}]):[2];}];},_7E=false,_7F=true,_7G=function(_7H){return [0,function(_7I){switch(E(E(_7I)[1])){case 79:return E(new T(function(){return B(A(_7H,[_7u]));}));case 88:return E(new T(function(){return B(A(_7H,[_7v]));}));case 111:return E(new T(function(){return B(A(_7H,[_7u]));}));case 120:return E(new T(function(){return B(A(_7H,[_7v]));}));default:return [2];}}];},_7J=function(_7K){return new F(function(){return A(_7K,[_6p]);});},_7L=function(_7M){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_2K(9,_7M,_0));}))));});},_7N=function(_7O){var _7P=E(_7O);return _7P[0]==0?E(_7P[1]):I_toInt(_7P[1]);},_7Q=function(_7R,_7S){var _7T=E(_7R);if(!_7T[0]){var _7U=_7T[1],_7V=E(_7S);return _7V[0]==0?_7U<=_7V[1]:I_compareInt(_7V[1],_7U)>=0;}else{var _7W=_7T[1],_7X=E(_7S);return _7X[0]==0?I_compareInt(_7W,_7X[1])<=0:I_compare(_7W,_7X[1])<=0;}},_7Y=function(_7Z){return [2];},_80=function(_81){var _82=E(_81);if(!_82[0]){return E(_7Y);}else{var _83=_82[1],_84=E(_82[2]);return _84[0]==0?E(_83):function(_85){return new F(function(){return _4e(B(A(_83,[_85])),new T(function(){return B(A(new T(function(){return B(_80(_84));}),[_85]));}));});};}},_86=new T(function(){return B(unCStr("NUL"));}),_87=function(_88){return [2];},_89=function(_8a){return new F(function(){return _87(_8a);});},_8b=function(_8c,_8d){var _8e=function(_8f,_8g){var _8h=E(_8f);if(!_8h[0]){return function(_8i){return new F(function(){return A(_8i,[_8c]);});};}else{var _8j=E(_8g);return _8j[0]==0?E(_87):E(_8h[1])[1]!=E(_8j[1])[1]?E(_89):function(_8k){return [0,function(_8l){return E(new T(function(){return B(A(new T(function(){return B(_8e(_8h[2],_8j[2]));}),[_8k]));}));}];};}};return [1,function(_8m){return new F(function(){return A(_8e,[_8c,_8m,_8d]);});}];},_8n=[0,0],_8o=function(_8p){return new F(function(){return _8b(_86,function(_8q){return E(new T(function(){return B(A(_8p,[_8n]));}));});});},_8r=new T(function(){return B(unCStr("STX"));}),_8s=[0,2],_8t=function(_8u){return new F(function(){return _8b(_8r,function(_8v){return E(new T(function(){return B(A(_8u,[_8s]));}));});});},_8w=new T(function(){return B(unCStr("ETX"));}),_8x=[0,3],_8y=function(_8z){return new F(function(){return _8b(_8w,function(_8A){return E(new T(function(){return B(A(_8z,[_8x]));}));});});},_8B=new T(function(){return B(unCStr("EOT"));}),_8C=[0,4],_8D=function(_8E){return new F(function(){return _8b(_8B,function(_8F){return E(new T(function(){return B(A(_8E,[_8C]));}));});});},_8G=new T(function(){return B(unCStr("ENQ"));}),_8H=[0,5],_8I=function(_8J){return new F(function(){return _8b(_8G,function(_8K){return E(new T(function(){return B(A(_8J,[_8H]));}));});});},_8L=new T(function(){return B(unCStr("ACK"));}),_8M=[0,6],_8N=function(_8O){return new F(function(){return _8b(_8L,function(_8P){return E(new T(function(){return B(A(_8O,[_8M]));}));});});},_8Q=new T(function(){return B(unCStr("BEL"));}),_8R=[0,7],_8S=function(_8T){return new F(function(){return _8b(_8Q,function(_8U){return E(new T(function(){return B(A(_8T,[_8R]));}));});});},_8V=new T(function(){return B(unCStr("BS"));}),_8W=[0,8],_8X=function(_8Y){return new F(function(){return _8b(_8V,function(_8Z){return E(new T(function(){return B(A(_8Y,[_8W]));}));});});},_90=new T(function(){return B(unCStr("HT"));}),_91=[0,9],_92=function(_93){return new F(function(){return _8b(_90,function(_94){return E(new T(function(){return B(A(_93,[_91]));}));});});},_95=new T(function(){return B(unCStr("LF"));}),_96=[0,10],_97=function(_98){return new F(function(){return _8b(_95,function(_99){return E(new T(function(){return B(A(_98,[_96]));}));});});},_9a=new T(function(){return B(unCStr("VT"));}),_9b=[0,11],_9c=function(_9d){return new F(function(){return _8b(_9a,function(_9e){return E(new T(function(){return B(A(_9d,[_9b]));}));});});},_9f=new T(function(){return B(unCStr("FF"));}),_9g=[0,12],_9h=function(_9i){return new F(function(){return _8b(_9f,function(_9j){return E(new T(function(){return B(A(_9i,[_9g]));}));});});},_9k=new T(function(){return B(unCStr("CR"));}),_9l=[0,13],_9m=function(_9n){return new F(function(){return _8b(_9k,function(_9o){return E(new T(function(){return B(A(_9n,[_9l]));}));});});},_9p=new T(function(){return B(unCStr("SI"));}),_9q=[0,15],_9r=function(_9s){return new F(function(){return _8b(_9p,function(_9t){return E(new T(function(){return B(A(_9s,[_9q]));}));});});},_9u=new T(function(){return B(unCStr("DLE"));}),_9v=[0,16],_9w=function(_9x){return new F(function(){return _8b(_9u,function(_9y){return E(new T(function(){return B(A(_9x,[_9v]));}));});});},_9z=new T(function(){return B(unCStr("DC1"));}),_9A=[0,17],_9B=function(_9C){return new F(function(){return _8b(_9z,function(_9D){return E(new T(function(){return B(A(_9C,[_9A]));}));});});},_9E=new T(function(){return B(unCStr("DC2"));}),_9F=[0,18],_9G=function(_9H){return new F(function(){return _8b(_9E,function(_9I){return E(new T(function(){return B(A(_9H,[_9F]));}));});});},_9J=new T(function(){return B(unCStr("DC3"));}),_9K=[0,19],_9L=function(_9M){return new F(function(){return _8b(_9J,function(_9N){return E(new T(function(){return B(A(_9M,[_9K]));}));});});},_9O=new T(function(){return B(unCStr("DC4"));}),_9P=[0,20],_9Q=function(_9R){return new F(function(){return _8b(_9O,function(_9S){return E(new T(function(){return B(A(_9R,[_9P]));}));});});},_9T=new T(function(){return B(unCStr("NAK"));}),_9U=[0,21],_9V=function(_9W){return new F(function(){return _8b(_9T,function(_9X){return E(new T(function(){return B(A(_9W,[_9U]));}));});});},_9Y=new T(function(){return B(unCStr("SYN"));}),_9Z=[0,22],_a0=function(_a1){return new F(function(){return _8b(_9Y,function(_a2){return E(new T(function(){return B(A(_a1,[_9Z]));}));});});},_a3=new T(function(){return B(unCStr("ETB"));}),_a4=[0,23],_a5=function(_a6){return new F(function(){return _8b(_a3,function(_a7){return E(new T(function(){return B(A(_a6,[_a4]));}));});});},_a8=new T(function(){return B(unCStr("CAN"));}),_a9=[0,24],_aa=function(_ab){return new F(function(){return _8b(_a8,function(_ac){return E(new T(function(){return B(A(_ab,[_a9]));}));});});},_ad=new T(function(){return B(unCStr("EM"));}),_ae=[0,25],_af=function(_ag){return new F(function(){return _8b(_ad,function(_ah){return E(new T(function(){return B(A(_ag,[_ae]));}));});});},_ai=new T(function(){return B(unCStr("SUB"));}),_aj=[0,26],_ak=function(_al){return new F(function(){return _8b(_ai,function(_am){return E(new T(function(){return B(A(_al,[_aj]));}));});});},_an=new T(function(){return B(unCStr("ESC"));}),_ao=[0,27],_ap=function(_aq){return new F(function(){return _8b(_an,function(_ar){return E(new T(function(){return B(A(_aq,[_ao]));}));});});},_as=new T(function(){return B(unCStr("FS"));}),_at=[0,28],_au=function(_av){return new F(function(){return _8b(_as,function(_aw){return E(new T(function(){return B(A(_av,[_at]));}));});});},_ax=new T(function(){return B(unCStr("GS"));}),_ay=[0,29],_az=function(_aA){return new F(function(){return _8b(_ax,function(_aB){return E(new T(function(){return B(A(_aA,[_ay]));}));});});},_aC=new T(function(){return B(unCStr("RS"));}),_aD=[0,30],_aE=function(_aF){return new F(function(){return _8b(_aC,function(_aG){return E(new T(function(){return B(A(_aF,[_aD]));}));});});},_aH=new T(function(){return B(unCStr("US"));}),_aI=[0,31],_aJ=function(_aK){return new F(function(){return _8b(_aH,function(_aL){return E(new T(function(){return B(A(_aK,[_aI]));}));});});},_aM=new T(function(){return B(unCStr("SP"));}),_aN=[0,32],_aO=function(_aP){return new F(function(){return _8b(_aM,function(_aQ){return E(new T(function(){return B(A(_aP,[_aN]));}));});});},_aR=new T(function(){return B(unCStr("DEL"));}),_aS=[0,127],_aT=function(_aU){return new F(function(){return _8b(_aR,function(_aV){return E(new T(function(){return B(A(_aU,[_aS]));}));});});},_aW=[1,_aT,_0],_aX=[1,_aO,_aW],_aY=[1,_aJ,_aX],_aZ=[1,_aE,_aY],_b0=[1,_az,_aZ],_b1=[1,_au,_b0],_b2=[1,_ap,_b1],_b3=[1,_ak,_b2],_b4=[1,_af,_b3],_b5=[1,_aa,_b4],_b6=[1,_a5,_b5],_b7=[1,_a0,_b6],_b8=[1,_9V,_b7],_b9=[1,_9Q,_b8],_ba=[1,_9L,_b9],_bb=[1,_9G,_ba],_bc=[1,_9B,_bb],_bd=[1,_9w,_bc],_be=[1,_9r,_bd],_bf=[1,_9m,_be],_bg=[1,_9h,_bf],_bh=[1,_9c,_bg],_bi=[1,_97,_bh],_bj=[1,_92,_bi],_bk=[1,_8X,_bj],_bl=[1,_8S,_bk],_bm=[1,_8N,_bl],_bn=[1,_8I,_bm],_bo=[1,_8D,_bn],_bp=[1,_8y,_bo],_bq=[1,_8t,_bp],_br=[1,_8o,_bq],_bs=new T(function(){return B(unCStr("SOH"));}),_bt=[0,1],_bu=function(_bv){return new F(function(){return _8b(_bs,function(_bw){return E(new T(function(){return B(A(_bv,[_bt]));}));});});},_bx=new T(function(){return B(unCStr("SO"));}),_by=[0,14],_bz=function(_bA){return new F(function(){return _8b(_bx,function(_bB){return E(new T(function(){return B(A(_bA,[_by]));}));});});},_bC=function(_bD){return new F(function(){return _5w(_bu,_bz,_bD);});},_bE=[1,_bC,_br],_bF=new T(function(){return B(_80(_bE));}),_bG=[0,1114111],_bH=[0,34],_bI=[0,_bH,_7F],_bJ=[0,39],_bK=[0,_bJ,_7F],_bL=[0,92],_bM=[0,_bL,_7F],_bN=[0,_8R,_7F],_bO=[0,_8W,_7F],_bP=[0,_9g,_7F],_bQ=[0,_96,_7F],_bR=[0,_9l,_7F],_bS=[0,_91,_7F],_bT=[0,_9b,_7F],_bU=[0,_8n,_7F],_bV=[0,_bt,_7F],_bW=[0,_8s,_7F],_bX=[0,_8x,_7F],_bY=[0,_8C,_7F],_bZ=[0,_8H,_7F],_c0=[0,_8M,_7F],_c1=[0,_8R,_7F],_c2=[0,_8W,_7F],_c3=[0,_91,_7F],_c4=[0,_96,_7F],_c5=[0,_9b,_7F],_c6=[0,_9g,_7F],_c7=[0,_9l,_7F],_c8=[0,_by,_7F],_c9=[0,_9q,_7F],_ca=[0,_9v,_7F],_cb=[0,_9A,_7F],_cc=[0,_9F,_7F],_cd=[0,_9K,_7F],_ce=[0,_9P,_7F],_cf=[0,_9U,_7F],_cg=[0,_9Z,_7F],_ch=[0,_a4,_7F],_ci=[0,_a9,_7F],_cj=[0,_ae,_7F],_ck=[0,_aj,_7F],_cl=[0,_ao,_7F],_cm=[0,_at,_7F],_cn=[0,_ay,_7F],_co=[0,_aD,_7F],_cp=[0,_aI,_7F],_cq=function(_cr){return new F(function(){return _4e([0,function(_cs){switch(E(E(_cs)[1])){case 34:return E(new T(function(){return B(A(_cr,[_bI]));}));case 39:return E(new T(function(){return B(A(_cr,[_bK]));}));case 92:return E(new T(function(){return B(A(_cr,[_bM]));}));case 97:return E(new T(function(){return B(A(_cr,[_bN]));}));case 98:return E(new T(function(){return B(A(_cr,[_bO]));}));case 102:return E(new T(function(){return B(A(_cr,[_bP]));}));case 110:return E(new T(function(){return B(A(_cr,[_bQ]));}));case 114:return E(new T(function(){return B(A(_cr,[_bR]));}));case 116:return E(new T(function(){return B(A(_cr,[_bS]));}));case 118:return E(new T(function(){return B(A(_cr,[_bT]));}));default:return [2];}}],new T(function(){return B(_4e(B(_5w(_7G,_7J,function(_ct){return new F(function(){return _5T(_ct,function(_cu){var _cv=B(_6S(new T(function(){return B(_6I(E(_ct)[1]));}),_6H,_cu));return !B(_7Q(_cv,_bG))?[2]:B(A(_cr,[[0,new T(function(){var _cw=B(_7N(_cv));if(_cw>>>0>1114111){var _cx=B(_7L(_cw));}else{var _cx=[0,_cw];}var _cy=_cx,_cz=_cy;return _cz;}),_7F]]));});});})),new T(function(){return B(_4e([0,function(_cA){return E(E(_cA)[1])==94?E([0,function(_cB){switch(E(E(_cB)[1])){case 64:return E(new T(function(){return B(A(_cr,[_bU]));}));case 65:return E(new T(function(){return B(A(_cr,[_bV]));}));case 66:return E(new T(function(){return B(A(_cr,[_bW]));}));case 67:return E(new T(function(){return B(A(_cr,[_bX]));}));case 68:return E(new T(function(){return B(A(_cr,[_bY]));}));case 69:return E(new T(function(){return B(A(_cr,[_bZ]));}));case 70:return E(new T(function(){return B(A(_cr,[_c0]));}));case 71:return E(new T(function(){return B(A(_cr,[_c1]));}));case 72:return E(new T(function(){return B(A(_cr,[_c2]));}));case 73:return E(new T(function(){return B(A(_cr,[_c3]));}));case 74:return E(new T(function(){return B(A(_cr,[_c4]));}));case 75:return E(new T(function(){return B(A(_cr,[_c5]));}));case 76:return E(new T(function(){return B(A(_cr,[_c6]));}));case 77:return E(new T(function(){return B(A(_cr,[_c7]));}));case 78:return E(new T(function(){return B(A(_cr,[_c8]));}));case 79:return E(new T(function(){return B(A(_cr,[_c9]));}));case 80:return E(new T(function(){return B(A(_cr,[_ca]));}));case 81:return E(new T(function(){return B(A(_cr,[_cb]));}));case 82:return E(new T(function(){return B(A(_cr,[_cc]));}));case 83:return E(new T(function(){return B(A(_cr,[_cd]));}));case 84:return E(new T(function(){return B(A(_cr,[_ce]));}));case 85:return E(new T(function(){return B(A(_cr,[_cf]));}));case 86:return E(new T(function(){return B(A(_cr,[_cg]));}));case 87:return E(new T(function(){return B(A(_cr,[_ch]));}));case 88:return E(new T(function(){return B(A(_cr,[_ci]));}));case 89:return E(new T(function(){return B(A(_cr,[_cj]));}));case 90:return E(new T(function(){return B(A(_cr,[_ck]));}));case 91:return E(new T(function(){return B(A(_cr,[_cl]));}));case 92:return E(new T(function(){return B(A(_cr,[_cm]));}));case 93:return E(new T(function(){return B(A(_cr,[_cn]));}));case 94:return E(new T(function(){return B(A(_cr,[_co]));}));case 95:return E(new T(function(){return B(A(_cr,[_cp]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_bF,[function(_cC){return new F(function(){return A(_cr,[[0,_cC,_7F]]);});}]));})));})));}));});},_cD=function(_cE){return new F(function(){return A(_cE,[_2u]);});},_cF=function(_cG){var _cH=E(_cG);if(!_cH[0]){return E(_cD);}else{var _cI=_cH[2],_cJ=E(E(_cH[1])[1]);switch(_cJ){case 9:return function(_cK){return [0,function(_cL){return E(new T(function(){return B(A(new T(function(){return B(_cF(_cI));}),[_cK]));}));}];};case 10:return function(_cM){return [0,function(_cN){return E(new T(function(){return B(A(new T(function(){return B(_cF(_cI));}),[_cM]));}));}];};case 11:return function(_cO){return [0,function(_cP){return E(new T(function(){return B(A(new T(function(){return B(_cF(_cI));}),[_cO]));}));}];};case 12:return function(_cQ){return [0,function(_cR){return E(new T(function(){return B(A(new T(function(){return B(_cF(_cI));}),[_cQ]));}));}];};case 13:return function(_cS){return [0,function(_cT){return E(new T(function(){return B(A(new T(function(){return B(_cF(_cI));}),[_cS]));}));}];};case 32:return function(_cU){return [0,function(_cV){return E(new T(function(){return B(A(new T(function(){return B(_cF(_cI));}),[_cU]));}));}];};case 160:return function(_cW){return [0,function(_cX){return E(new T(function(){return B(A(new T(function(){return B(_cF(_cI));}),[_cW]));}));}];};default:var _cY=u_iswspace(_cJ),_cZ=_cY;return E(_cZ)==0?E(_cD):function(_d0){return [0,function(_d1){return E(new T(function(){return B(A(new T(function(){return B(_cF(_cI));}),[_d0]));}));}];};}}},_d2=function(_d3){var _d4=new T(function(){return B(_d2(_d3));}),_d5=[1,function(_d6){return new F(function(){return A(_cF,[_d6,function(_d7){return E([0,function(_d8){return E(E(_d8)[1])==92?E(_d4):[2];}]);}]);});}];return new F(function(){return _4e([0,function(_d9){return E(E(_d9)[1])==92?E([0,function(_da){var _db=E(E(_da)[1]);switch(_db){case 9:return E(_d5);case 10:return E(_d5);case 11:return E(_d5);case 12:return E(_d5);case 13:return E(_d5);case 32:return E(_d5);case 38:return E(_d4);case 160:return E(_d5);default:var _dc=u_iswspace(_db),_dd=_dc;return E(_dd)==0?[2]:E(_d5);}}]):[2];}],[0,function(_de){var _df=E(_de);return E(_df[1])==92?E(new T(function(){return B(_cq(_d3));})):B(A(_d3,[[0,_df,_7E]]));}]);});},_dg=function(_dh,_di){return new F(function(){return _d2(function(_dj){var _dk=E(_dj),_dl=E(_dk[1]);if(E(_dl[1])==34){if(!E(_dk[2])){return E(new T(function(){return B(A(_di,[[1,new T(function(){return B(A(_dh,[_0]));})]]));}));}else{return new F(function(){return _dg(function(_dm){return new F(function(){return A(_dh,[[1,_dl,_dm]]);});},_di);});}}else{return new F(function(){return _dg(function(_dn){return new F(function(){return A(_dh,[[1,_dl,_dn]]);});},_di);});}});});},_do=new T(function(){return B(unCStr("_\'"));}),_dp=function(_dq){var _dr=u_iswalnum(_dq),_ds=_dr;return E(_ds)==0?B(_7m(_4V,[0,_dq],_do)):true;},_dt=function(_du){return new F(function(){return _dp(E(_du)[1]);});},_dv=new T(function(){return B(unCStr(",;()[]{}`"));}),_dw=function(_dx){return new F(function(){return A(_dx,[_0]);});},_dy=function(_dz,_dA){var _dB=function(_dC){var _dD=E(_dC);if(!_dD[0]){return E(_dw);}else{var _dE=_dD[1];return !B(A(_dz,[_dE]))?E(_dw):function(_dF){return [0,function(_dG){return E(new T(function(){return B(A(new T(function(){return B(_dB(_dD[2]));}),[function(_dH){return new F(function(){return A(_dF,[[1,_dE,_dH]]);});}]));}));}];};}};return [1,function(_dI){return new F(function(){return A(_dB,[_dI,_dA]);});}];},_dJ=new T(function(){return B(unCStr(".."));}),_dK=new T(function(){return B(unCStr("::"));}),_dL=new T(function(){return B(unCStr("->"));}),_dM=[0,64],_dN=[1,_dM,_0],_dO=[0,126],_dP=[1,_dO,_0],_dQ=new T(function(){return B(unCStr("=>"));}),_dR=[1,_dQ,_0],_dS=[1,_dP,_dR],_dT=[1,_dN,_dS],_dU=[1,_dL,_dT],_dV=new T(function(){return B(unCStr("<-"));}),_dW=[1,_dV,_dU],_dX=[0,124],_dY=[1,_dX,_0],_dZ=[1,_dY,_dW],_e0=[1,_bL,_0],_e1=[1,_e0,_dZ],_e2=[0,61],_e3=[1,_e2,_0],_e4=[1,_e3,_e1],_e5=[1,_dK,_e4],_e6=[1,_dJ,_e5],_e7=function(_e8){return new F(function(){return _4e([1,function(_e9){return E(_e9)[0]==0?E(new T(function(){return B(A(_e8,[_5Q]));})):[2];}],new T(function(){return B(_4e([0,function(_ea){return E(E(_ea)[1])==39?E([0,function(_eb){var _ec=E(_eb);switch(E(_ec[1])){case 39:return [2];case 92:return E(new T(function(){return B(_cq(function(_ed){var _ee=E(_ed);return new F(function(){return (function(_ef,_eg){var _eh=new T(function(){return B(A(_e8,[[0,_ef]]));});return !E(_eg)?E(E(_ef)[1])==39?[2]:[0,function(_ei){return E(E(_ei)[1])==39?E(_eh):[2];}]:[0,function(_ej){return E(E(_ej)[1])==39?E(_eh):[2];}];})(_ee[1],_ee[2]);});}));}));default:return [0,function(_ek){return E(E(_ek)[1])==39?E(new T(function(){return B(A(_e8,[[0,_ec]]));})):[2];}];}}]):[2];}],new T(function(){return B(_4e([0,function(_el){return E(E(_el)[1])==34?E(new T(function(){return B(_dg(_2U,_e8));})):[2];}],new T(function(){return B(_4e([0,function(_em){return !B(_7m(_4V,_em,_dv))?[2]:B(A(_e8,[[2,[1,_em,_0]]]));}],new T(function(){return B(_4e([0,function(_en){if(!B(_7m(_4V,_en,_7r))){return [2];}else{return new F(function(){return _dy(_7s,function(_eo){var _ep=[1,_en,_eo];return !B(_7m(_5c,_ep,_e6))?B(A(_e8,[[4,_ep]])):B(A(_e8,[[2,_ep]]));});});}}],new T(function(){return B(_4e([0,function(_eq){var _er=E(_eq),_es=_er[1],_et=u_iswalpha(_es),_eu=_et;if(!E(_eu)){if(E(_es)==95){return new F(function(){return _dy(_dt,function(_ev){return new F(function(){return A(_e8,[[3,[1,_er,_ev]]]);});});});}else{return [2];}}else{return new F(function(){return _dy(_dt,function(_ew){return new F(function(){return A(_e8,[[3,[1,_er,_ew]]]);});});});}}],new T(function(){return B(_5w(_7w,_7h,_e8));})));})));})));})));})));}));});},_ex=function(_ey){return [1,function(_ez){return new F(function(){return A(_cF,[_ez,function(_eA){return E(new T(function(){return B(_e7(_ey));}));}]);});}];},_eB=[0,0],_eC=function(_eD,_eE){return new F(function(){return _ex(function(_eF){var _eG=E(_eF);if(_eG[0]==2){var _eH=E(_eG[1]);return _eH[0]==0?[2]:E(E(_eH[1])[1])==40?E(_eH[2])[0]==0?E(new T(function(){return B(A(_eD,[_eB,function(_eI){return new F(function(){return _ex(function(_eJ){var _eK=E(_eJ);if(_eK[0]==2){var _eL=E(_eK[1]);return _eL[0]==0?[2]:E(E(_eL[1])[1])==41?E(_eL[2])[0]==0?E(new T(function(){return B(A(_eE,[_eI]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_eM=function(_eN,_eO,_eP){var _eQ=function(_eR,_eS){return new F(function(){return _4e(B(_ex(function(_eT){var _eU=E(_eT);if(_eU[0]==4){var _eV=E(_eU[1]);if(!_eV[0]){return new F(function(){return A(_eN,[_eU,_eR,_eS]);});}else{return E(E(_eV[1])[1])==45?E(_eV[2])[0]==0?E([1,function(_eW){return new F(function(){return A(_cF,[_eW,function(_eX){return E(new T(function(){return B(_e7(function(_eY){return new F(function(){return A(_eN,[_eY,_eR,function(_eZ){return new F(function(){return A(_eS,[new T(function(){return [0, -E(_eZ)[1]];})]);});}]);});}));}));}]);});}]):B(A(_eN,[_eU,_eR,_eS])):B(A(_eN,[_eU,_eR,_eS]));}}else{return new F(function(){return A(_eN,[_eU,_eR,_eS]);});}})),new T(function(){return B(_eC(_eQ,_eS));}));});};return new F(function(){return _eQ(_eO,_eP);});},_f0=function(_f1,_f2){return [2];},_f3=function(_f4,_f5){return new F(function(){return _f0(_f4,_f5);});},_f6=function(_f7){var _f8=E(_f7);return _f8[0]==0?[1,new T(function(){return B(_6S(new T(function(){return B(_6I(E(_f8[1])[1]));}),_6H,_f8[2]));})]:E(_f8[2])[0]==0?E(_f8[3])[0]==0?[1,new T(function(){return B(_6S(_6G,_6H,_f8[1]));})]:[0]:[0];},_f9=function(_fa){var _fb=E(_fa);if(_fb[0]==5){var _fc=B(_f6(_fb[1]));return _fc[0]==0?E(_f0):function(_fd,_fe){return new F(function(){return A(_fe,[new T(function(){return [0,B(_7N(_fc[1]))];})]);});};}else{return E(_f3);}},_ff=function(_fg){return [1,function(_fh){return new F(function(){return A(_cF,[_fh,function(_fi){return E([3,_fg,_5o]);}]);});}];},_fj=new T(function(){return B(_eM(_f9,_eB,_ff));}),_fk=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_fl=new T(function(){return B(err(_fk));}),_fm=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_fn=new T(function(){return B(err(_fm));}),_fo=function(_fp,_fq,_fr){return _fr<=_fq?[1,[0,_fp],new T(function(){var _fs=_fq-_fp|0,_ft=function(_fu){return _fu>=(_fr-_fs|0)?[1,[0,_fu],new T(function(){return B(_ft(_fu+_fs|0));})]:[1,[0,_fu],_0];};return B(_ft(_fq));})]:_fr<=_fp?[1,[0,_fp],_0]:[0];},_fv=function(_fw,_fx,_fy){return _fy>=_fx?[1,[0,_fw],new T(function(){var _fz=_fx-_fw|0,_fA=function(_fB){return _fB<=(_fy-_fz|0)?[1,[0,_fB],new T(function(){return B(_fA(_fB+_fz|0));})]:[1,[0,_fB],_0];};return B(_fA(_fx));})]:_fy>=_fw?[1,[0,_fw],_0]:[0];},_fC=function(_fD,_fE){return _fE<_fD?B(_fo(_fD,_fE,-2147483648)):B(_fv(_fD,_fE,2147483647));},_fF=new T(function(){return B(_fC(135,150));}),_fG=function(_fH,_fI){var _fJ=E(_fH);if(!_fJ){return [0];}else{var _fK=E(_fI);return _fK[0]==0?[0]:[1,_fK[1],new T(function(){return B(_fG(_fJ-1|0,_fK[2]));})];}},_fL=new T(function(){return B(_fG(6,_fF));}),_fM=function(_fN,_fO){var _fP=E(_fN);if(!_fP[0]){return E(_fL);}else{var _fQ=_fP[1];return _fO>1?[1,_fQ,new T(function(){return B(_fM(_fP[2],_fO-1|0));})]:[1,_fQ,_fL];}},_fR=new T(function(){return B(_fC(25,40));}),_fS=new T(function(){return B(_fM(_fR,6));}),_fT=function(_fU){while(1){var _fV=(function(_fW){var _fX=E(_fW);if(!_fX[0]){return [0];}else{var _fY=_fX[2],_fZ=E(_fX[1]);if(!E(_fZ[2])[0]){return [1,_fZ[1],new T(function(){return B(_fT(_fY));})];}else{_fU=_fY;return null;}}})(_fU);if(_fV!=null){return _fV;}}},_g0=function(_g1,_g2){var _g3=E(_g2);if(!_g3[0]){return [0,_0,_0];}else{var _g4=_g3[1];if(!B(A(_g1,[_g4]))){var _g5=new T(function(){var _g6=B(_g0(_g1,_g3[2]));return [0,_g6[1],_g6[2]];});return [0,[1,_g4,new T(function(){return E(E(_g5)[1]);})],new T(function(){return E(E(_g5)[2]);})];}else{return [0,_0,_g3];}}},_g7=function(_g8,_g9){while(1){var _ga=E(_g9);if(!_ga[0]){return [0];}else{if(!B(A(_g8,[_ga[1]]))){return E(_ga);}else{_g9=_ga[2];continue;}}}},_gb=function(_gc){var _gd=E(_gc);switch(_gd){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _ge=u_iswspace(_gd),_gf=_ge;return E(_gf)==0?false:true;}},_gg=function(_gh){return new F(function(){return _gb(E(_gh)[1]);});},_gi=function(_gj){var _gk=B(_g7(_gg,_gj));if(!_gk[0]){return [0];}else{var _gl=new T(function(){var _gm=B(_g0(_gg,_gk));return [0,_gm[1],_gm[2]];});return [1,new T(function(){return E(E(_gl)[1]);}),new T(function(){return B(_gi(E(_gl)[2]));})];}},_gn=function(_go,_){var _gp=setDropCheckerCallback_ffi(function(_gq,_gr,_gs){var _gt=E(_go),_gu=_gt[1],_gv=_gt[6],_gw=new T(function(){return B(_gi(B(_3W(_gq))));}),_gx=new T(function(){var _gy=B(_fT(B(_44(_fj,new T(function(){return B(_3s(2,B(_2p(_gw,2))));})))));return _gy[0]==0?E(_fn):E(_gy[2])[0]==0?E(_gy[1]):E(_fl);}),_gz=new T(function(){var _gA=B(_fT(B(_44(_fj,new T(function(){return B(_3s(2,B(_2p(_gw,3))));})))));return _gA[0]==0?E(_fn):E(_gA[2])[0]==0?E(_gA[1]):E(_fl);}),_gB=[0,_gx,_gz],_gC=B(_3D(function(_gD){var _gE=E(_gD)[1]-E(_gr)[1];return _gE<0? -_gE<7:_gE<7;},_fS));if(!_gC[0]){return function(_5P){return new F(function(){return _3j(_gB,_gB,_gv,_5P);});};}else{var _gF=_gC[1],_gG=function(_gH,_gI,_){var _gJ=E(_gx),_gK=_gJ[1];if(_gH<=_gK){return new F(function(){return _3j(_gB,_gB,_gv,_);});}else{if(_gH>=0){var _gL=B(_2p(_gu,_gH)),_gM=new T(function(){return _gK<0;}),_gN=function(_){var _gO=B(_3j(_gB,[0,_gI,new T(function(){if(_gH>=0){var _gP=E(B(_2p(_gu,_gH))[2]);}else{var _gP=E(_2m);}return _gP;})],_gv,_)),_gQ=_gO;if(!E(_gM)){var _gR=new T(function(){return B(_3P(function(_gS,_gT,_gU){return [1,new T(function(){var _gV=E(_gS)[1];return _gV!=_gK?_gV!=_gH?E(_gT):[0,new T(function(){if(_gK>=0){var _gW=E(B(_2p(_gu,_gK))[1]);}else{var _gW=E(_2m);}return _gW;}),new T(function(){return [0,E(E(_gT)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_gT)[1]);}),new T(function(){return [0,E(E(_gT)[2])[1]-1|0];})];}),_gU];},_0,_42,_gu));}),_gX=B((function(_gY,_){while(1){var _gZ=(function(_h0,_){var _h1=E(_h0);if(!_h1[0]){return _2u;}else{var _h2=_h1[1],_h3=B(_3j([0,_gJ,_h2],[0,_gJ,new T(function(){return [0,E(_h2)[1]-1|0];})],_gv,_)),_h4=_h3;_gY=_h1[2];return null;}})(_gY,_);if(_gZ!=null){return _gZ;}}})(B(_3s(1,B(_3x(E(_gz)[1],E(B(_2p(_gR,_gK))[2])[1])))),_)),_h5=_gX;return new F(function(){return _gn([0,_gR,_gt[2],_gt[3],_gt[4],_gt[5],_gv,_gt[7]],_);});}else{return E(_2m);}},_h6=function(_){return E(_gL[2])[1]>=2?B(_3j(_gB,_gB,_gv,_)):B(_gN(_));};return E(_gL[1])==0?!E(_gM)?E(B(_2p(_gu,_gK))[1])==0?B(_gN(_)):B(_h6(_)):E(_2m):!E(_gM)?E(B(_2p(_gu,_gK))[1])==0?B(_h6(_)):B(_gN(_)):E(_2m);}else{return E(_2m);}}};if(E(_gs)[1]<=E(_41)[1]){var _h7=E(_gF);return function(_5P){return new F(function(){return _gG(_h7[1],_h7,_5P);});};}else{var _h8=23-E(_gF)[1]|0;return function(_5P){return new F(function(){return _gG(_h8,[0,_h8],_5P);});};}}});return _2u;},_h9=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:134:5-10"));}),_ha=function(_){return _2u;},_hb=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_hc=new T(function(){return B(unCStr("base"));}),_hd=new T(function(){return B(unCStr("IOException"));}),_he=new T(function(){var _hf=hs_wordToWord64(4053623282),_hg=_hf,_hh=hs_wordToWord64(3693590983),_hi=_hh;return [0,_hg,_hi,[0,_hg,_hi,_hc,_hb,_hd],_0];}),_hj=function(_hk){return E(_he);},_hl=function(_hm){var _hn=E(_hm);return new F(function(){return _T(B(_P(_hn[1])),_hj,_hn[2]);});},_ho=new T(function(){return B(unCStr(": "));}),_hp=[0,41],_hq=new T(function(){return B(unCStr(" ("));}),_hr=new T(function(){return B(unCStr("already exists"));}),_hs=new T(function(){return B(unCStr("does not exist"));}),_ht=new T(function(){return B(unCStr("protocol error"));}),_hu=new T(function(){return B(unCStr("failed"));}),_hv=new T(function(){return B(unCStr("invalid argument"));}),_hw=new T(function(){return B(unCStr("inappropriate type"));}),_hx=new T(function(){return B(unCStr("hardware fault"));}),_hy=new T(function(){return B(unCStr("unsupported operation"));}),_hz=new T(function(){return B(unCStr("timeout"));}),_hA=new T(function(){return B(unCStr("resource vanished"));}),_hB=new T(function(){return B(unCStr("interrupted"));}),_hC=new T(function(){return B(unCStr("resource busy"));}),_hD=new T(function(){return B(unCStr("resource exhausted"));}),_hE=new T(function(){return B(unCStr("end of file"));}),_hF=new T(function(){return B(unCStr("illegal operation"));}),_hG=new T(function(){return B(unCStr("permission denied"));}),_hH=new T(function(){return B(unCStr("user error"));}),_hI=new T(function(){return B(unCStr("unsatisified constraints"));}),_hJ=new T(function(){return B(unCStr("system error"));}),_hK=function(_hL,_hM){switch(E(_hL)){case 0:return new F(function(){return _1d(_hr,_hM);});break;case 1:return new F(function(){return _1d(_hs,_hM);});break;case 2:return new F(function(){return _1d(_hC,_hM);});break;case 3:return new F(function(){return _1d(_hD,_hM);});break;case 4:return new F(function(){return _1d(_hE,_hM);});break;case 5:return new F(function(){return _1d(_hF,_hM);});break;case 6:return new F(function(){return _1d(_hG,_hM);});break;case 7:return new F(function(){return _1d(_hH,_hM);});break;case 8:return new F(function(){return _1d(_hI,_hM);});break;case 9:return new F(function(){return _1d(_hJ,_hM);});break;case 10:return new F(function(){return _1d(_ht,_hM);});break;case 11:return new F(function(){return _1d(_hu,_hM);});break;case 12:return new F(function(){return _1d(_hv,_hM);});break;case 13:return new F(function(){return _1d(_hw,_hM);});break;case 14:return new F(function(){return _1d(_hx,_hM);});break;case 15:return new F(function(){return _1d(_hy,_hM);});break;case 16:return new F(function(){return _1d(_hz,_hM);});break;case 17:return new F(function(){return _1d(_hA,_hM);});break;default:return new F(function(){return _1d(_hB,_hM);});}},_hN=[0,125],_hO=new T(function(){return B(unCStr("{handle: "));}),_hP=function(_hQ,_hR,_hS,_hT,_hU,_hV){var _hW=new T(function(){var _hX=new T(function(){return B(_hK(_hR,new T(function(){var _hY=E(_hT);return _hY[0]==0?E(_hV):B(_1d(_hq,new T(function(){return B(_1d(_hY,[1,_hp,_hV]));})));})));}),_hZ=E(_hS);return _hZ[0]==0?E(_hX):B(_1d(_hZ,new T(function(){return B(_1d(_ho,_hX));})));}),_i0=E(_hU);if(!_i0[0]){var _i1=E(_hQ);if(!_i1[0]){return E(_hW);}else{var _i2=E(_i1[1]);return _i2[0]==0?B(_1d(_hO,new T(function(){return B(_1d(_i2[1],[1,_hN,new T(function(){return B(_1d(_ho,_hW));})]));}))):B(_1d(_hO,new T(function(){return B(_1d(_i2[1],[1,_hN,new T(function(){return B(_1d(_ho,_hW));})]));})));}}else{return new F(function(){return _1d(_i0[1],new T(function(){return B(_1d(_ho,_hW));}));});}},_i3=function(_i4){var _i5=E(_i4);return new F(function(){return _hP(_i5[1],_i5[2],_i5[3],_i5[4],_i5[6],_0);});},_i6=function(_i7,_i8){var _i9=E(_i7);return new F(function(){return _hP(_i9[1],_i9[2],_i9[3],_i9[4],_i9[6],_i8);});},_ia=function(_ib,_ic){return new F(function(){return _1n(_i6,_ib,_ic);});},_id=function(_ie,_if,_ig){var _ih=E(_if);return new F(function(){return _hP(_ih[1],_ih[2],_ih[3],_ih[4],_ih[6],_ig);});},_ii=[0,_id,_i3,_ia],_ij=new T(function(){return [0,_hj,_ii,_ik,_hl];}),_ik=function(_il){return [0,_ij,_il];},_im=7,_in=function(_io){return [0,_78,_im,_0,_io,_78,_78];},_ip=function(_iq,_){return new F(function(){return die(new T(function(){return B(_ik(new T(function(){return B(_in(_iq));})));}));});},_ir=function(_is,_){return new F(function(){return _ip(_is,_);});},_it=[0,114],_iu=[1,_it,_0],_iv=new T(function(){return B(_2K(0,6,_0));}),_iw=new T(function(){return B(unCStr("cx"));}),_ix=new T(function(){return B(unCStr("cy"));}),_iy=new T(function(){return B(unCStr("circle"));}),_iz=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_iA=new T(function(){return B(unCStr("board"));}),_iB=function(_iC,_iD,_){while(1){var _iE=(function(_iF,_iG,_){var _iH=E(_iG);if(!_iH[0]){return _2u;}else{var _iI=_iH[2],_iJ=E(_iH[1]),_iK=E(_iJ[2])[1];if(_iK>0){var _iL=function(_iM,_iN,_){var _iO=jsFind(toJSStr(E(_iA))),_iP=_iO,_iQ=E(_iP);if(!_iQ[0]){var _iR=B(_ir(_h9,_)),_iS=_iR;return new F(function(){return A(_iN,[_]);});}else{var _iT=jsCreateElemNS(toJSStr(E(_iz)),toJSStr(E(_iy))),_iU=_iT,_iV=[0,_iU],_iW=B(A(_2x,[_2U,_iV,_iu,_iv,_])),_iX=_iW,_iY=[0,[0,_iF],_iM],_iZ=new T(function(){var _j0=B(_35(_iY));return [0,_j0[1],_j0[2]];}),_j1=B(A(_2x,[_2U,_iV,_iw,new T(function(){return B(_2K(0,E(E(_iZ)[1])[1],_0));}),_])),_j2=_j1,_j3=B(A(_2x,[_2U,_iV,_ix,new T(function(){return B(_2K(0,E(E(_iZ)[2])[1],_0));}),_])),_j4=_j3,_j5=B(A(_2Y,[_iV,_y,_iY,_iJ[1],_])),_j6=_j5,_j7=jsAppendChild(_iU,E(_iQ[1])[1]);return new F(function(){return A(_iN,[_]);});}},_j8=function(_j9,_ja,_){var _jb=E(_j9);if(!_jb[0]){return _2u;}else{var _jc=_jb[1];if(_ja>1){return new F(function(){return _iL(_jc,function(_){return new F(function(){return _j8(_jb[2],_ja-1|0,_);});},_);});}else{return new F(function(){return _iL(_jc,_ha,_);});}}},_jd=B(_j8(_42,_iK,_)),_je=_jd,_jf=E(_iF);if(_jf==2147483647){return _2u;}else{_iC=_jf+1|0;_iD=_iI;return null;}}else{var _jg=E(_iF);if(_jg==2147483647){return _2u;}else{_iC=_jg+1|0;_iD=_iI;return null;}}}})(_iC,_iD,_);if(_iE!=null){return _iE;}}},_jh=function(_){var _ji=B(_iB(0,_2j,_)),_jj=_ji;return new F(function(){return _gn(_2k,_);});},_jk=function(_){return new F(function(){return _jh(_);});};
var hasteMain = function() {B(A(_jk, [0]));};window.onload = hasteMain;