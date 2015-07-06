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

var _0=new T(function(){return B(unCStr("hint found"));}),_1=new T(function(){return B(unCStr("You have not joined a game (yet)."));}),_2=new T(function(){return B(unCStr("hint not found"));}),_3=new T(function(){return B(unCStr("HintText"));}),_4=new T(function(){return B(unCStr("innerHTML"));}),_5=new T(function(){return B(unCStr("Black"));}),_6=new T(function(){return B(unCStr("White"));}),_7=[0,125],_8=new T(function(){return B(unCStr(", "));}),_9=function(_a,_b){var _c=E(_a);return _c[0]==0?E(_b):[1,_c[1],new T(function(){return B(_9(_c[2],_b));})];},_d=function(_e,_f){var _g=jsShowI(_e),_h=_g;return new F(function(){return _9(fromJSStr(_h),_f);});},_i=[0,41],_j=[0,40],_k=function(_l,_m,_n){return _m>=0?B(_d(_m,_n)):_l<=6?B(_d(_m,_n)):[1,_j,new T(function(){var _o=jsShowI(_m),_p=_o;return B(_9(fromJSStr(_p),[1,_i,_n]));})];},_q=new T(function(){return B(unCStr("onPointIndex = "));}),_r=new T(function(){return B(unCStr("BarPlacement {"));}),_s=new T(function(){return B(unCStr("onBarIndex = "));}),_t=new T(function(){return B(unCStr("LeftSidePlacement {"));}),_u=new T(function(){return B(unCStr("onSideIndex = "));}),_v=new T(function(){return B(unCStr("RightSidePlacement {"));}),_w=new T(function(){return B(unCStr("PointPlacement {"));}),_x=new T(function(){return B(unCStr("pointIndex = "));}),_y=function(_z,_A,_B){var _C=E(_A);switch(_C[0]){case 0:var _D=function(_E){return new F(function(){return _9(_x,new T(function(){return B(_k(0,E(_C[1])[1],new T(function(){return B(_9(_8,new T(function(){return B(_9(_q,new T(function(){return B(_k(0,E(_C[2])[1],[1,_7,_E]));})));})));})));}));});};return _z<11?B(_9(_w,new T(function(){return B(_D(_B));}))):[1,_j,new T(function(){return B(_9(_w,new T(function(){return B(_D([1,_i,_B]));})));})];case 1:var _F=function(_G){return new F(function(){return _9(_r,new T(function(){return B(_9(_s,new T(function(){return B(_k(0,E(_C[1])[1],[1,_7,_G]));})));}));});};return _z<11?B(_F(_B)):[1,_j,new T(function(){return B(_F([1,_i,_B]));})];case 2:var _H=function(_I){return new F(function(){return _9(_t,new T(function(){return B(_9(_u,new T(function(){return B(_k(0,E(_C[1])[1],[1,_7,_I]));})));}));});};return _z<11?B(_H(_B)):[1,_j,new T(function(){return B(_H([1,_i,_B]));})];default:var _J=function(_K){return new F(function(){return _9(_v,new T(function(){return B(_9(_u,new T(function(){return B(_k(0,E(_C[1])[1],[1,_7,_K]));})));}));});};return _z<11?B(_J(_B)):[1,_j,new T(function(){return B(_J([1,_i,_B]));})];}},_L=0,_M=function(_N,_O,_P,_Q){return new F(function(){return A(_N,[new T(function(){return function(_){var _R=jsSetAttr(E(_O)[1],toJSStr(E(_P)),toJSStr(E(_Q)));return _L;};})]);});},_S=[0],_T=function(_U){return E(_U);},_V=[0,95],_W=function(_X){var _Y=E(_X);return E(_Y[1])==32?E(_V):E(_Y);},_Z=new T(function(){return B(unCStr("class"));}),_10=new T(function(){return B(unCStr("draggable "));}),_11=[0,32],_12=function(_13,_14){var _15=E(_14);return _15[0]==0?[0]:[1,new T(function(){return B(A(_13,[_15[1]]));}),new T(function(){return B(_12(_13,_15[2]));})];},_16=function(_17,_18,_19,_1a){return new F(function(){return _M(_T,_17,_Z,new T(function(){var _1b=new T(function(){var _1c=new T(function(){return B(_12(_W,B(_y(0,_19,_S))));});return E(_1a)==0?B(_9(_5,[1,_11,_1c])):B(_9(_6,[1,_11,_1c]));});return E(_18)==0?E(_1a)==0?B(_9(_10,_1b)):E(_1b):E(_1a)==0?E(_1b):B(_9(_10,_1b));}));});},_1d=new T(function(){return B(unCStr("Control.Exception.Base"));}),_1e=new T(function(){return B(unCStr("base"));}),_1f=new T(function(){return B(unCStr("PatternMatchFail"));}),_1g=new T(function(){var _1h=hs_wordToWord64(18445595),_1i=_1h,_1j=hs_wordToWord64(52003073),_1k=_1j;return [0,_1i,_1k,[0,_1i,_1k,_1e,_1d,_1f],_S];}),_1l=function(_1m){return E(_1g);},_1n=function(_1o){return E(E(_1o)[1]);},_1p=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1q=new T(function(){return B(err(_1p));}),_1r=function(_1s,_1t,_1u){var _1v=new T(function(){var _1w=B(A(_1s,[_1u])),_1x=B(A(_1t,[new T(function(){var _1y=E(_1v);return _1y[0]==0?E(_1q):E(_1y[1]);})])),_1z=hs_eqWord64(_1w[1],_1x[1]),_1A=_1z;if(!E(_1A)){var _1B=[0];}else{var _1C=hs_eqWord64(_1w[2],_1x[2]),_1D=_1C,_1B=E(_1D)==0?[0]:[1,_1u];}var _1E=_1B,_1F=_1E;return _1F;});return E(_1v);},_1G=function(_1H){var _1I=E(_1H);return new F(function(){return _1r(B(_1n(_1I[1])),_1l,_1I[2]);});},_1J=function(_1K){return E(E(_1K)[1]);},_1L=function(_1M,_1N){return new F(function(){return _9(E(_1M)[1],_1N);});},_1O=[0,44],_1P=[0,93],_1Q=[0,91],_1R=function(_1S,_1T,_1U){var _1V=E(_1T);return _1V[0]==0?B(unAppCStr("[]",_1U)):[1,_1Q,new T(function(){return B(A(_1S,[_1V[1],new T(function(){var _1W=function(_1X){var _1Y=E(_1X);return _1Y[0]==0?E([1,_1P,_1U]):[1,_1O,new T(function(){return B(A(_1S,[_1Y[1],new T(function(){return B(_1W(_1Y[2]));})]));})];};return B(_1W(_1V[2]));})]));})];},_1Z=function(_20,_21){return new F(function(){return _1R(_1L,_20,_21);});},_22=function(_23,_24,_25){return new F(function(){return _9(E(_24)[1],_25);});},_26=[0,_22,_1J,_1Z],_27=new T(function(){return [0,_1l,_26,_28,_1G];}),_28=function(_29){return [0,_27,_29];},_2a=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_2b=function(_2c,_2d){return new F(function(){return die(new T(function(){return B(A(_2d,[_2c]));}));});},_2e=function(_2f,_2g){var _2h=E(_2g);if(!_2h[0]){return [0,_S,_S];}else{var _2i=_2h[1];if(!B(A(_2f,[_2i]))){return [0,_S,_2h];}else{var _2j=new T(function(){var _2k=B(_2e(_2f,_2h[2]));return [0,_2k[1],_2k[2]];});return [0,[1,_2i,new T(function(){return E(E(_2j)[1]);})],new T(function(){return E(E(_2j)[2]);})];}}},_2l=[0,32],_2m=[0,10],_2n=[1,_2m,_S],_2o=function(_2p){return E(E(_2p)[1])==124?false:true;},_2q=function(_2r,_2s){var _2t=B(_2e(_2o,B(unCStr(_2r)))),_2u=_2t[1],_2v=function(_2w,_2x){return new F(function(){return _9(_2w,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_9(_2s,new T(function(){return B(_9(_2x,_2n));})));})));}));});},_2y=E(_2t[2]);if(!_2y[0]){return new F(function(){return _2v(_2u,_S);});}else{return E(E(_2y[1])[1])==124?B(_2v(_2u,[1,_2l,_2y[2]])):B(_2v(_2u,_S));}},_2z=function(_2A){return new F(function(){return _2b([0,new T(function(){return B(_2q(_2A,_2a));})],_28);});},_2B=new T(function(){return B(_2z("main.hs:(87,1)-(114,116)|function checkerPosition"));}),_2C=function(_2D,_2E){if(_2D<=0){if(_2D>=0){return new F(function(){return quot(_2D,_2E);});}else{if(_2E<=0){return new F(function(){return quot(_2D,_2E);});}else{return quot(_2D+1|0,_2E)-1|0;}}}else{if(_2E>=0){if(_2D>=0){return new F(function(){return quot(_2D,_2E);});}else{if(_2E<=0){return new F(function(){return quot(_2D,_2E);});}else{return quot(_2D+1|0,_2E)-1|0;}}}else{return quot(_2D-1|0,_2E)-1|0;}}},_2F=new T(function(){return [0,B(_2C(15,2))];}),_2G=new T(function(){return [0,220+B(_2C(15,2))|0];}),_2H=function(_2I){var _2J=E(_2I);switch(_2J[0]){case 0:var _2K=_2J[1],_2L=_2J[2];return [0,new T(function(){var _2M=E(_2K)[1];if(_2M>=12){var _2N=23-_2M|0;if(_2N>=6){var _2O=[0,25+(20+(imul(_2N,15)|0)|0)|0];}else{var _2O=[0,25+(imul(_2N,15)|0)|0];}var _2P=_2O,_2Q=_2P;}else{if(_2M>=6){var _2R=[0,25+(20+(imul(_2M,15)|0)|0)|0];}else{var _2R=[0,25+(imul(_2M,15)|0)|0];}var _2Q=_2R;}var _2S=_2Q;return _2S;}),new T(function(){if(E(_2K)[1]>=12){var _2T=[0,203+(imul(imul(imul(-1,E(_2L)[1])|0,2)|0,6)|0)|0];}else{var _2T=[0,7+(imul(imul(E(_2L)[1],2)|0,6)|0)|0];}var _2U=_2T;return _2U;})];case 1:return E(_2B);case 2:return [0,_2F,new T(function(){return [0,203-(imul(imul(E(_2J[1])[1],2)|0,6)|0)|0];})];default:return [0,_2G,new T(function(){return [0,203-(imul(imul(E(_2J[1])[1],2)|0,6)|0)|0];})];}},_2V=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:151:5-10"));}),_2W=function(_){return _L;},_2X=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_2Y=new T(function(){return B(unCStr("base"));}),_2Z=new T(function(){return B(unCStr("IOException"));}),_30=new T(function(){var _31=hs_wordToWord64(4053623282),_32=_31,_33=hs_wordToWord64(3693590983),_34=_33;return [0,_32,_34,[0,_32,_34,_2Y,_2X,_2Z],_S];}),_35=function(_36){return E(_30);},_37=function(_38){var _39=E(_38);return new F(function(){return _1r(B(_1n(_39[1])),_35,_39[2]);});},_3a=new T(function(){return B(unCStr(": "));}),_3b=[0,41],_3c=new T(function(){return B(unCStr(" ("));}),_3d=new T(function(){return B(unCStr("already exists"));}),_3e=new T(function(){return B(unCStr("does not exist"));}),_3f=new T(function(){return B(unCStr("protocol error"));}),_3g=new T(function(){return B(unCStr("failed"));}),_3h=new T(function(){return B(unCStr("invalid argument"));}),_3i=new T(function(){return B(unCStr("inappropriate type"));}),_3j=new T(function(){return B(unCStr("hardware fault"));}),_3k=new T(function(){return B(unCStr("unsupported operation"));}),_3l=new T(function(){return B(unCStr("timeout"));}),_3m=new T(function(){return B(unCStr("resource vanished"));}),_3n=new T(function(){return B(unCStr("interrupted"));}),_3o=new T(function(){return B(unCStr("resource busy"));}),_3p=new T(function(){return B(unCStr("resource exhausted"));}),_3q=new T(function(){return B(unCStr("end of file"));}),_3r=new T(function(){return B(unCStr("illegal operation"));}),_3s=new T(function(){return B(unCStr("permission denied"));}),_3t=new T(function(){return B(unCStr("user error"));}),_3u=new T(function(){return B(unCStr("unsatisified constraints"));}),_3v=new T(function(){return B(unCStr("system error"));}),_3w=function(_3x,_3y){switch(E(_3x)){case 0:return new F(function(){return _9(_3d,_3y);});break;case 1:return new F(function(){return _9(_3e,_3y);});break;case 2:return new F(function(){return _9(_3o,_3y);});break;case 3:return new F(function(){return _9(_3p,_3y);});break;case 4:return new F(function(){return _9(_3q,_3y);});break;case 5:return new F(function(){return _9(_3r,_3y);});break;case 6:return new F(function(){return _9(_3s,_3y);});break;case 7:return new F(function(){return _9(_3t,_3y);});break;case 8:return new F(function(){return _9(_3u,_3y);});break;case 9:return new F(function(){return _9(_3v,_3y);});break;case 10:return new F(function(){return _9(_3f,_3y);});break;case 11:return new F(function(){return _9(_3g,_3y);});break;case 12:return new F(function(){return _9(_3h,_3y);});break;case 13:return new F(function(){return _9(_3i,_3y);});break;case 14:return new F(function(){return _9(_3j,_3y);});break;case 15:return new F(function(){return _9(_3k,_3y);});break;case 16:return new F(function(){return _9(_3l,_3y);});break;case 17:return new F(function(){return _9(_3m,_3y);});break;default:return new F(function(){return _9(_3n,_3y);});}},_3z=[0,125],_3A=new T(function(){return B(unCStr("{handle: "));}),_3B=function(_3C,_3D,_3E,_3F,_3G,_3H){var _3I=new T(function(){var _3J=new T(function(){return B(_3w(_3D,new T(function(){var _3K=E(_3F);return _3K[0]==0?E(_3H):B(_9(_3c,new T(function(){return B(_9(_3K,[1,_3b,_3H]));})));})));}),_3L=E(_3E);return _3L[0]==0?E(_3J):B(_9(_3L,new T(function(){return B(_9(_3a,_3J));})));}),_3M=E(_3G);if(!_3M[0]){var _3N=E(_3C);if(!_3N[0]){return E(_3I);}else{var _3O=E(_3N[1]);return _3O[0]==0?B(_9(_3A,new T(function(){return B(_9(_3O[1],[1,_3z,new T(function(){return B(_9(_3a,_3I));})]));}))):B(_9(_3A,new T(function(){return B(_9(_3O[1],[1,_3z,new T(function(){return B(_9(_3a,_3I));})]));})));}}else{return new F(function(){return _9(_3M[1],new T(function(){return B(_9(_3a,_3I));}));});}},_3P=function(_3Q){var _3R=E(_3Q);return new F(function(){return _3B(_3R[1],_3R[2],_3R[3],_3R[4],_3R[6],_S);});},_3S=function(_3T,_3U){var _3V=E(_3T);return new F(function(){return _3B(_3V[1],_3V[2],_3V[3],_3V[4],_3V[6],_3U);});},_3W=function(_3X,_3Y){return new F(function(){return _1R(_3S,_3X,_3Y);});},_3Z=function(_40,_41,_42){var _43=E(_41);return new F(function(){return _3B(_43[1],_43[2],_43[3],_43[4],_43[6],_42);});},_44=[0,_3Z,_3P,_3W],_45=new T(function(){return [0,_35,_44,_46,_37];}),_46=function(_47){return [0,_45,_47];},_48=[0],_49=7,_4a=function(_4b){return [0,_48,_49,_S,_4b,_48,_48];},_4c=function(_4d,_){return new F(function(){return die(new T(function(){return B(_46(new T(function(){return B(_4a(_4d));})));}));});},_4e=function(_4f,_){return new F(function(){return _4c(_4f,_);});},_4g=[0,114],_4h=[1,_4g,_S],_4i=new T(function(){return B(_k(0,6,_S));}),_4j=new T(function(){return B(unCStr("cx"));}),_4k=new T(function(){return B(unCStr("cy"));}),_4l=function(_4m,_4n){if(_4m<=_4n){var _4o=function(_4p){return [1,[0,_4p],new T(function(){if(_4p!=_4n){var _4q=B(_4o(_4p+1|0));}else{var _4q=[0];}return _4q;})];};return new F(function(){return _4o(_4m);});}else{return [0];}},_4r=new T(function(){return B(_4l(0,2147483647));}),_4s=new T(function(){return B(unCStr("circle"));}),_4t=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_4u=new T(function(){return B(unCStr("board"));}),_4v=function(_4w,_4x,_4y,_){if(_4y>0){var _4z=function(_4A,_4B,_){var _4C=jsFind(toJSStr(E(_4u))),_4D=_4C,_4E=E(_4D);if(!_4E[0]){var _4F=B(_4e(_2V,_)),_4G=_4F;return new F(function(){return A(_4B,[_]);});}else{var _4H=jsCreateElemNS(toJSStr(E(_4t)),toJSStr(E(_4s))),_4I=_4H,_4J=[0,_4I],_4K=B(A(_M,[_T,_4J,_4h,_4i,_])),_4L=_4K,_4M=new T(function(){return E(_4w)==0?[3,_4A]:[2,_4A];}),_4N=new T(function(){var _4O=B(_2H(_4M));return [0,_4O[1],_4O[2]];}),_4P=B(A(_M,[_T,_4J,_4j,new T(function(){return B(_k(0,E(E(_4N)[1])[1],_S));}),_])),_4Q=_4P,_4R=B(A(_M,[_T,_4J,_4k,new T(function(){return B(_k(0,E(E(_4N)[2])[1],_S));}),_])),_4S=_4R,_4T=B(A(_16,[_4J,_4x,_4M,_4w,_])),_4U=_4T,_4V=jsAppendChild(_4I,E(_4E[1])[1]);return new F(function(){return A(_4B,[_]);});}},_4W=function(_4X,_4Y,_){var _4Z=E(_4X);if(!_4Z[0]){return _L;}else{var _50=_4Z[1];if(_4Y>1){return new F(function(){return _4z(_50,function(_){return new F(function(){return _4W(_4Z[2],_4Y-1|0,_);});},_);});}else{return new F(function(){return _4z(_50,_2W,_);});}}};return new F(function(){return _4W(_4r,_4y,_);});}else{return _L;}},_51=0,_52=1,_53=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_54=new T(function(){return B(err(_53));}),_55=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_56=new T(function(){return B(err(_55));}),_57=function(_58,_59){while(1){var _5a=E(_58);if(!_5a[0]){return E(_56);}else{var _5b=E(_59);if(!_5b){return E(_5a[1]);}else{_58=_5a[2];_59=_5b-1|0;continue;}}}},_5c=new T(function(){return B(unCStr(": empty list"));}),_5d=new T(function(){return B(unCStr("Prelude."));}),_5e=function(_5f){return new F(function(){return err(B(_9(_5d,new T(function(){return B(_9(_5f,_5c));}))));});},_5g=new T(function(){return B(unCStr("head"));}),_5h=new T(function(){return B(_5e(_5g));}),_5i=function(_5j,_5k,_5l,_){var _5m=jsElemsByClassName(toJSStr(B(_12(_W,B(_y(0,_5j,_S)))))),_5n=_5m,_5o=E(_5n);if(!_5o[0]){return E(_5h);}else{var _5p=E(_5o[1]),_5q=B(_2H(_5k)),_5r=animateCircle_ffi(_5p[1],E(_5q[1])[1],E(_5q[2])[1],300);return new F(function(){return A(_16,[_5p,_5l,_5k,_5l,_]);});}},_5s=function(_5t,_5u){while(1){var _5v=E(_5t);if(!_5v){return E(_5u);}else{var _5w=E(_5u);if(!_5w[0]){return [0];}else{_5t=_5v-1|0;_5u=_5w[2];continue;}}}},_5x=new T(function(){return [0,"click"];}),_5y=function(_5z,_5A){var _5B=function(_5C,_5D){while(1){var _5E=(function(_5F,_5G){var _5H=E(_5G);if(!_5H[0]){return [0];}else{var _5I=_5H[2];if(!B(A(_5z,[_5H[1]]))){var _5J=_5F+1|0;_5D=_5I;_5C=_5J;return null;}else{return [1,[0,_5F],new T(function(){return B(_5B(_5F+1|0,_5I));})];}}})(_5C,_5D);if(_5E!=null){return _5E;}}};return new F(function(){return _5B(0,_5A);});},_5K=function(_5L,_5M,_5N,_5O){var _5P=E(_5N);if(!_5P[0]){return E(_5M);}else{var _5Q=E(_5O);if(!_5Q[0]){return E(_5M);}else{return new F(function(){return A(_5L,[_5P[1],_5Q[1],new T(function(){return B(_5K(_5L,_5M,_5P[2],_5Q[2]));})]);});}}},_5R=function(_5S){return new F(function(){return fromJSStr(E(_5S)[1]);});},_5T=function(_5U){var _5V=E(_5U);return E(_5V[1])==95?E(_11):E(_5V);},_5W=new T(function(){return [0,B(_2C(210,2))];}),_5X=new T(function(){return B(unCStr("joinGame"));}),_5Y=new T(function(){return B(unCStr("Clicked Join"));}),_5Z=function(_){var _60=showAlert_ffi(toJSStr(E(_5Y)));return _L;},_61=function(_62,_63,_){return new F(function(){return _5Z(_);});},_64=[0,_61],_65=new T(function(){return B(_2z("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_66=function(_67,_68){while(1){var _69=(function(_6a,_6b){var _6c=E(_6a);switch(_6c[0]){case 0:var _6d=E(_6b);if(!_6d[0]){return [0];}else{_67=B(A(_6c[1],[_6d[1]]));_68=_6d[2];return null;}break;case 1:var _6e=B(A(_6c[1],[_6b])),_6f=_6b;_67=_6e;_68=_6f;return null;case 2:return [0];case 3:return [1,[0,_6c[1],_6b],new T(function(){return B(_66(_6c[2],_6b));})];default:return E(_6c[1]);}})(_67,_68);if(_69!=null){return _69;}}},_6g=function(_6h,_6i){var _6j=new T(function(){var _6k=E(_6i);if(_6k[0]==3){var _6l=[3,_6k[1],new T(function(){return B(_6g(_6h,_6k[2]));})];}else{var _6m=E(_6h);if(_6m[0]==2){var _6n=E(_6k);}else{var _6o=E(_6k);if(_6o[0]==2){var _6p=E(_6m);}else{var _6q=new T(function(){var _6r=E(_6o);if(_6r[0]==4){var _6s=[1,function(_6t){return [4,new T(function(){return B(_9(B(_66(_6m,_6t)),_6r[1]));})];}];}else{var _6u=E(_6m);if(_6u[0]==1){var _6v=_6u[1],_6w=E(_6r);if(!_6w[0]){var _6x=[1,function(_6y){return new F(function(){return _6g(B(A(_6v,[_6y])),_6w);});}];}else{var _6x=[1,function(_6z){return new F(function(){return _6g(B(A(_6v,[_6z])),new T(function(){return B(A(_6w[1],[_6z]));}));});}];}var _6A=_6x;}else{var _6B=E(_6r);if(!_6B[0]){var _6C=E(_65);}else{var _6C=[1,function(_6D){return new F(function(){return _6g(_6u,new T(function(){return B(A(_6B[1],[_6D]));}));});}];}var _6A=_6C;}var _6s=_6A;}return _6s;}),_6E=E(_6m);switch(_6E[0]){case 1:var _6F=E(_6o);if(_6F[0]==4){var _6G=[1,function(_6H){return [4,new T(function(){return B(_9(B(_66(B(A(_6E[1],[_6H])),_6H)),_6F[1]));})];}];}else{var _6G=E(_6q);}var _6I=_6G;break;case 4:var _6J=_6E[1],_6K=E(_6o);switch(_6K[0]){case 0:var _6L=[1,function(_6M){return [4,new T(function(){return B(_9(_6J,new T(function(){return B(_66(_6K,_6M));})));})];}];break;case 1:var _6L=[1,function(_6N){return [4,new T(function(){return B(_9(_6J,new T(function(){return B(_66(B(A(_6K[1],[_6N])),_6N));})));})];}];break;default:var _6L=[4,new T(function(){return B(_9(_6J,_6K[1]));})];}var _6I=_6L;break;default:var _6I=E(_6q);}var _6p=_6I;}var _6n=_6p;}var _6l=_6n;}return _6l;}),_6O=E(_6h);switch(_6O[0]){case 0:var _6P=E(_6i);return _6P[0]==0?[0,function(_6Q){return new F(function(){return _6g(B(A(_6O[1],[_6Q])),new T(function(){return B(A(_6P[1],[_6Q]));}));});}]:E(_6j);case 3:return [3,_6O[1],new T(function(){return B(_6g(_6O[2],_6i));})];default:return E(_6j);}},_6R=function(_6S,_6T){return E(_6S)[1]!=E(_6T)[1];},_6U=function(_6V,_6W){return E(_6V)[1]==E(_6W)[1];},_6X=[0,_6U,_6R],_6Y=function(_6Z){return E(E(_6Z)[1]);},_70=function(_71,_72,_73){while(1){var _74=E(_72);if(!_74[0]){return E(_73)[0]==0?true:false;}else{var _75=E(_73);if(!_75[0]){return false;}else{if(!B(A(_6Y,[_71,_74[1],_75[1]]))){return false;}else{_72=_74[2];_73=_75[2];continue;}}}}},_76=function(_77,_78,_79){return !B(_70(_77,_78,_79))?true:false;},_7a=function(_7b){return [0,function(_7c,_7d){return new F(function(){return _70(_7b,_7c,_7d);});},function(_7c,_7d){return new F(function(){return _76(_7b,_7c,_7d);});}];},_7e=new T(function(){return B(_7a(_6X));}),_7f=function(_7g,_7h){var _7i=E(_7g);switch(_7i[0]){case 0:return [0,function(_7j){return new F(function(){return _7f(B(A(_7i[1],[_7j])),_7h);});}];case 1:return [1,function(_7k){return new F(function(){return _7f(B(A(_7i[1],[_7k])),_7h);});}];case 2:return [2];case 3:return new F(function(){return _6g(B(A(_7h,[_7i[1]])),new T(function(){return B(_7f(_7i[2],_7h));}));});break;default:var _7l=function(_7m){var _7n=E(_7m);if(!_7n[0]){return [0];}else{var _7o=E(_7n[1]);return new F(function(){return _9(B(_66(B(A(_7h,[_7o[1]])),_7o[2])),new T(function(){return B(_7l(_7n[2]));}));});}},_7p=B(_7l(_7i[1]));return _7p[0]==0?[2]:[4,_7p];}},_7q=[2],_7r=function(_7s){return [3,_7s,_7q];},_7t=function(_7u,_7v){var _7w=E(_7u);if(!_7w){return new F(function(){return A(_7v,[_L]);});}else{return [0,function(_7x){return E(new T(function(){return B(_7t(_7w-1|0,_7v));}));}];}},_7y=function(_7z,_7A,_7B){return [1,function(_7C){return new F(function(){return A(function(_7D,_7E,_7F){while(1){var _7G=(function(_7H,_7I,_7J){var _7K=E(_7H);switch(_7K[0]){case 0:var _7L=E(_7I);if(!_7L[0]){return E(_7A);}else{_7D=B(A(_7K[1],[_7L[1]]));_7E=_7L[2];var _7M=_7J+1|0;_7F=_7M;return null;}break;case 1:var _7N=B(A(_7K[1],[_7I])),_7O=_7I,_7M=_7J;_7D=_7N;_7E=_7O;_7F=_7M;return null;case 2:return E(_7A);case 3:return function(_7P){return new F(function(){return _7t(_7J,function(_7Q){return E(new T(function(){return B(_7f(_7K,_7P));}));});});};default:return function(_7R){return new F(function(){return _7f(_7K,_7R);});};}})(_7D,_7E,_7F);if(_7G!=null){return _7G;}}},[new T(function(){return B(A(_7z,[_7r]));}),_7C,0,_7B]);});}];},_7S=[6],_7T=new T(function(){return B(unCStr("valDig: Bad base"));}),_7U=new T(function(){return B(err(_7T));}),_7V=function(_7W,_7X){var _7Y=function(_7Z,_80){var _81=E(_7Z);if(!_81[0]){return function(_82){return new F(function(){return A(_82,[new T(function(){return B(A(_80,[_S]));})]);});};}else{var _83=E(_81[1])[1],_84=function(_85){return function(_86){return [0,function(_87){return E(new T(function(){return B(A(new T(function(){return B(_7Y(_81[2],function(_88){return new F(function(){return A(_80,[[1,_85,_88]]);});}));}),[_86]));}));}];};};switch(E(E(_7W)[1])){case 8:if(48>_83){return function(_89){return new F(function(){return A(_89,[new T(function(){return B(A(_80,[_S]));})]);});};}else{if(_83>55){return function(_8a){return new F(function(){return A(_8a,[new T(function(){return B(A(_80,[_S]));})]);});};}else{return new F(function(){return _84([0,_83-48|0]);});}}break;case 10:if(48>_83){return function(_8b){return new F(function(){return A(_8b,[new T(function(){return B(A(_80,[_S]));})]);});};}else{if(_83>57){return function(_8c){return new F(function(){return A(_8c,[new T(function(){return B(A(_80,[_S]));})]);});};}else{return new F(function(){return _84([0,_83-48|0]);});}}break;case 16:var _8d=new T(function(){if(97>_83){if(65>_83){var _8e=[0];}else{if(_83>70){var _8f=[0];}else{var _8f=[1,[0,(_83-65|0)+10|0]];}var _8e=_8f;}var _8g=_8e;}else{if(_83>102){if(65>_83){var _8h=[0];}else{if(_83>70){var _8i=[0];}else{var _8i=[1,[0,(_83-65|0)+10|0]];}var _8h=_8i;}var _8j=_8h;}else{var _8j=[1,[0,(_83-97|0)+10|0]];}var _8g=_8j;}return _8g;});if(48>_83){var _8k=E(_8d);if(!_8k[0]){return function(_8l){return new F(function(){return A(_8l,[new T(function(){return B(A(_80,[_S]));})]);});};}else{return new F(function(){return _84(_8k[1]);});}}else{if(_83>57){var _8m=E(_8d);if(!_8m[0]){return function(_8n){return new F(function(){return A(_8n,[new T(function(){return B(A(_80,[_S]));})]);});};}else{return new F(function(){return _84(_8m[1]);});}}else{return new F(function(){return _84([0,_83-48|0]);});}}break;default:return E(_7U);}}};return [1,function(_8o){return new F(function(){return A(_7Y,[_8o,_T,function(_8p){var _8q=E(_8p);return _8q[0]==0?[2]:B(A(_7X,[_8q]));}]);});}];},_8r=[0,10],_8s=[0,1],_8t=[0,2147483647],_8u=function(_8v,_8w){while(1){var _8x=E(_8v);if(!_8x[0]){var _8y=_8x[1],_8z=E(_8w);if(!_8z[0]){var _8A=_8z[1],_8B=addC(_8y,_8A);if(!E(_8B[2])){return [0,_8B[1]];}else{_8v=[1,I_fromInt(_8y)];_8w=[1,I_fromInt(_8A)];continue;}}else{_8v=[1,I_fromInt(_8y)];_8w=_8z;continue;}}else{var _8C=E(_8w);if(!_8C[0]){_8v=_8x;_8w=[1,I_fromInt(_8C[1])];continue;}else{return [1,I_add(_8x[1],_8C[1])];}}}},_8D=new T(function(){return B(_8u(_8t,_8s));}),_8E=function(_8F){var _8G=E(_8F);if(!_8G[0]){var _8H=E(_8G[1]);return _8H==(-2147483648)?E(_8D):[0, -_8H];}else{return [1,I_negate(_8G[1])];}},_8I=[0,10],_8J=[0,0],_8K=function(_8L){return [0,_8L];},_8M=function(_8N,_8O){while(1){var _8P=E(_8N);if(!_8P[0]){var _8Q=_8P[1],_8R=E(_8O);if(!_8R[0]){var _8S=_8R[1];if(!(imul(_8Q,_8S)|0)){return [0,imul(_8Q,_8S)|0];}else{_8N=[1,I_fromInt(_8Q)];_8O=[1,I_fromInt(_8S)];continue;}}else{_8N=[1,I_fromInt(_8Q)];_8O=_8R;continue;}}else{var _8T=E(_8O);if(!_8T[0]){_8N=_8P;_8O=[1,I_fromInt(_8T[1])];continue;}else{return [1,I_mul(_8P[1],_8T[1])];}}}},_8U=function(_8V,_8W,_8X){while(1){var _8Y=E(_8X);if(!_8Y[0]){return E(_8W);}else{var _8Z=B(_8u(B(_8M(_8W,_8V)),B(_8K(E(_8Y[1])[1]))));_8X=_8Y[2];_8W=_8Z;continue;}}},_90=function(_91){var _92=new T(function(){return B(_6g(B(_6g([0,function(_93){if(E(E(_93)[1])==45){return new F(function(){return _7V(_8r,function(_94){return new F(function(){return A(_91,[[1,new T(function(){return B(_8E(B(_8U(_8I,_8J,_94))));})]]);});});});}else{return [2];}}],[0,function(_95){if(E(E(_95)[1])==43){return new F(function(){return _7V(_8r,function(_96){return new F(function(){return A(_91,[[1,new T(function(){return B(_8U(_8I,_8J,_96));})]]);});});});}else{return [2];}}])),new T(function(){return B(_7V(_8r,function(_97){return new F(function(){return A(_91,[[1,new T(function(){return B(_8U(_8I,_8J,_97));})]]);});}));})));});return new F(function(){return _6g([0,function(_98){return E(E(_98)[1])==101?E(_92):[2];}],[0,function(_99){return E(E(_99)[1])==69?E(_92):[2];}]);});},_9a=function(_9b){return new F(function(){return A(_9b,[_48]);});},_9c=function(_9d){return new F(function(){return A(_9d,[_48]);});},_9e=function(_9f){return [0,function(_9g){return E(E(_9g)[1])==46?E(new T(function(){return B(_7V(_8r,function(_9h){return new F(function(){return A(_9f,[[1,_9h]]);});}));})):[2];}];},_9i=function(_9j){return new F(function(){return _7V(_8r,function(_9k){return new F(function(){return _7y(_9e,_9a,function(_9l){return new F(function(){return _7y(_90,_9c,function(_9m){return new F(function(){return A(_9j,[[5,[1,_9k,_9l,_9m]]]);});});});});});});});},_9n=function(_9o,_9p,_9q){while(1){var _9r=E(_9q);if(!_9r[0]){return false;}else{if(!B(A(_6Y,[_9o,_9p,_9r[1]]))){_9q=_9r[2];continue;}else{return true;}}}},_9s=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_9t=function(_9u){return new F(function(){return _9n(_6X,_9u,_9s);});},_9v=[0,8],_9w=[0,16],_9x=function(_9y){return [0,function(_9z){return E(E(_9z)[1])==48?E([0,function(_9A){switch(E(E(_9A)[1])){case 79:return E(new T(function(){return B(_7V(_9v,function(_9B){return new F(function(){return A(_9y,[[5,[0,_9v,_9B]]]);});}));}));case 88:return E(new T(function(){return B(_7V(_9w,function(_9C){return new F(function(){return A(_9y,[[5,[0,_9w,_9C]]]);});}));}));case 111:return E(new T(function(){return B(_7V(_9v,function(_9D){return new F(function(){return A(_9y,[[5,[0,_9v,_9D]]]);});}));}));case 120:return E(new T(function(){return B(_7V(_9w,function(_9E){return new F(function(){return A(_9y,[[5,[0,_9w,_9E]]]);});}));}));default:return [2];}}]):[2];}];},_9F=false,_9G=true,_9H=function(_9I){return [0,function(_9J){switch(E(E(_9J)[1])){case 79:return E(new T(function(){return B(A(_9I,[_9v]));}));case 88:return E(new T(function(){return B(A(_9I,[_9w]));}));case 111:return E(new T(function(){return B(A(_9I,[_9v]));}));case 120:return E(new T(function(){return B(A(_9I,[_9w]));}));default:return [2];}}];},_9K=function(_9L){return new F(function(){return A(_9L,[_8r]);});},_9M=function(_9N){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_k(9,_9N,_S));}))));});},_9O=function(_9P){var _9Q=E(_9P);return _9Q[0]==0?E(_9Q[1]):I_toInt(_9Q[1]);},_9R=function(_9S,_9T){var _9U=E(_9S);if(!_9U[0]){var _9V=_9U[1],_9W=E(_9T);return _9W[0]==0?_9V<=_9W[1]:I_compareInt(_9W[1],_9V)>=0;}else{var _9X=_9U[1],_9Y=E(_9T);return _9Y[0]==0?I_compareInt(_9X,_9Y[1])<=0:I_compare(_9X,_9Y[1])<=0;}},_9Z=function(_a0){return [2];},_a1=function(_a2){var _a3=E(_a2);if(!_a3[0]){return E(_9Z);}else{var _a4=_a3[1],_a5=E(_a3[2]);return _a5[0]==0?E(_a4):function(_a6){return new F(function(){return _6g(B(A(_a4,[_a6])),new T(function(){return B(A(new T(function(){return B(_a1(_a5));}),[_a6]));}));});};}},_a7=new T(function(){return B(unCStr("NUL"));}),_a8=function(_a9){return [2];},_aa=function(_ab){return new F(function(){return _a8(_ab);});},_ac=function(_ad,_ae){var _af=function(_ag,_ah){var _ai=E(_ag);if(!_ai[0]){return function(_aj){return new F(function(){return A(_aj,[_ad]);});};}else{var _ak=E(_ah);return _ak[0]==0?E(_a8):E(_ai[1])[1]!=E(_ak[1])[1]?E(_aa):function(_al){return [0,function(_am){return E(new T(function(){return B(A(new T(function(){return B(_af(_ai[2],_ak[2]));}),[_al]));}));}];};}};return [1,function(_an){return new F(function(){return A(_af,[_ad,_an,_ae]);});}];},_ao=[0,0],_ap=function(_aq){return new F(function(){return _ac(_a7,function(_ar){return E(new T(function(){return B(A(_aq,[_ao]));}));});});},_as=new T(function(){return B(unCStr("STX"));}),_at=[0,2],_au=function(_av){return new F(function(){return _ac(_as,function(_aw){return E(new T(function(){return B(A(_av,[_at]));}));});});},_ax=new T(function(){return B(unCStr("ETX"));}),_ay=[0,3],_az=function(_aA){return new F(function(){return _ac(_ax,function(_aB){return E(new T(function(){return B(A(_aA,[_ay]));}));});});},_aC=new T(function(){return B(unCStr("EOT"));}),_aD=[0,4],_aE=function(_aF){return new F(function(){return _ac(_aC,function(_aG){return E(new T(function(){return B(A(_aF,[_aD]));}));});});},_aH=new T(function(){return B(unCStr("ENQ"));}),_aI=[0,5],_aJ=function(_aK){return new F(function(){return _ac(_aH,function(_aL){return E(new T(function(){return B(A(_aK,[_aI]));}));});});},_aM=new T(function(){return B(unCStr("ACK"));}),_aN=[0,6],_aO=function(_aP){return new F(function(){return _ac(_aM,function(_aQ){return E(new T(function(){return B(A(_aP,[_aN]));}));});});},_aR=new T(function(){return B(unCStr("BEL"));}),_aS=[0,7],_aT=function(_aU){return new F(function(){return _ac(_aR,function(_aV){return E(new T(function(){return B(A(_aU,[_aS]));}));});});},_aW=new T(function(){return B(unCStr("BS"));}),_aX=[0,8],_aY=function(_aZ){return new F(function(){return _ac(_aW,function(_b0){return E(new T(function(){return B(A(_aZ,[_aX]));}));});});},_b1=new T(function(){return B(unCStr("HT"));}),_b2=[0,9],_b3=function(_b4){return new F(function(){return _ac(_b1,function(_b5){return E(new T(function(){return B(A(_b4,[_b2]));}));});});},_b6=new T(function(){return B(unCStr("LF"));}),_b7=[0,10],_b8=function(_b9){return new F(function(){return _ac(_b6,function(_ba){return E(new T(function(){return B(A(_b9,[_b7]));}));});});},_bb=new T(function(){return B(unCStr("VT"));}),_bc=[0,11],_bd=function(_be){return new F(function(){return _ac(_bb,function(_bf){return E(new T(function(){return B(A(_be,[_bc]));}));});});},_bg=new T(function(){return B(unCStr("FF"));}),_bh=[0,12],_bi=function(_bj){return new F(function(){return _ac(_bg,function(_bk){return E(new T(function(){return B(A(_bj,[_bh]));}));});});},_bl=new T(function(){return B(unCStr("CR"));}),_bm=[0,13],_bn=function(_bo){return new F(function(){return _ac(_bl,function(_bp){return E(new T(function(){return B(A(_bo,[_bm]));}));});});},_bq=new T(function(){return B(unCStr("SI"));}),_br=[0,15],_bs=function(_bt){return new F(function(){return _ac(_bq,function(_bu){return E(new T(function(){return B(A(_bt,[_br]));}));});});},_bv=new T(function(){return B(unCStr("DLE"));}),_bw=[0,16],_bx=function(_by){return new F(function(){return _ac(_bv,function(_bz){return E(new T(function(){return B(A(_by,[_bw]));}));});});},_bA=new T(function(){return B(unCStr("DC1"));}),_bB=[0,17],_bC=function(_bD){return new F(function(){return _ac(_bA,function(_bE){return E(new T(function(){return B(A(_bD,[_bB]));}));});});},_bF=new T(function(){return B(unCStr("DC2"));}),_bG=[0,18],_bH=function(_bI){return new F(function(){return _ac(_bF,function(_bJ){return E(new T(function(){return B(A(_bI,[_bG]));}));});});},_bK=new T(function(){return B(unCStr("DC3"));}),_bL=[0,19],_bM=function(_bN){return new F(function(){return _ac(_bK,function(_bO){return E(new T(function(){return B(A(_bN,[_bL]));}));});});},_bP=new T(function(){return B(unCStr("DC4"));}),_bQ=[0,20],_bR=function(_bS){return new F(function(){return _ac(_bP,function(_bT){return E(new T(function(){return B(A(_bS,[_bQ]));}));});});},_bU=new T(function(){return B(unCStr("NAK"));}),_bV=[0,21],_bW=function(_bX){return new F(function(){return _ac(_bU,function(_bY){return E(new T(function(){return B(A(_bX,[_bV]));}));});});},_bZ=new T(function(){return B(unCStr("SYN"));}),_c0=[0,22],_c1=function(_c2){return new F(function(){return _ac(_bZ,function(_c3){return E(new T(function(){return B(A(_c2,[_c0]));}));});});},_c4=new T(function(){return B(unCStr("ETB"));}),_c5=[0,23],_c6=function(_c7){return new F(function(){return _ac(_c4,function(_c8){return E(new T(function(){return B(A(_c7,[_c5]));}));});});},_c9=new T(function(){return B(unCStr("CAN"));}),_ca=[0,24],_cb=function(_cc){return new F(function(){return _ac(_c9,function(_cd){return E(new T(function(){return B(A(_cc,[_ca]));}));});});},_ce=new T(function(){return B(unCStr("EM"));}),_cf=[0,25],_cg=function(_ch){return new F(function(){return _ac(_ce,function(_ci){return E(new T(function(){return B(A(_ch,[_cf]));}));});});},_cj=new T(function(){return B(unCStr("SUB"));}),_ck=[0,26],_cl=function(_cm){return new F(function(){return _ac(_cj,function(_cn){return E(new T(function(){return B(A(_cm,[_ck]));}));});});},_co=new T(function(){return B(unCStr("ESC"));}),_cp=[0,27],_cq=function(_cr){return new F(function(){return _ac(_co,function(_cs){return E(new T(function(){return B(A(_cr,[_cp]));}));});});},_ct=new T(function(){return B(unCStr("FS"));}),_cu=[0,28],_cv=function(_cw){return new F(function(){return _ac(_ct,function(_cx){return E(new T(function(){return B(A(_cw,[_cu]));}));});});},_cy=new T(function(){return B(unCStr("GS"));}),_cz=[0,29],_cA=function(_cB){return new F(function(){return _ac(_cy,function(_cC){return E(new T(function(){return B(A(_cB,[_cz]));}));});});},_cD=new T(function(){return B(unCStr("RS"));}),_cE=[0,30],_cF=function(_cG){return new F(function(){return _ac(_cD,function(_cH){return E(new T(function(){return B(A(_cG,[_cE]));}));});});},_cI=new T(function(){return B(unCStr("US"));}),_cJ=[0,31],_cK=function(_cL){return new F(function(){return _ac(_cI,function(_cM){return E(new T(function(){return B(A(_cL,[_cJ]));}));});});},_cN=new T(function(){return B(unCStr("SP"));}),_cO=[0,32],_cP=function(_cQ){return new F(function(){return _ac(_cN,function(_cR){return E(new T(function(){return B(A(_cQ,[_cO]));}));});});},_cS=new T(function(){return B(unCStr("DEL"));}),_cT=[0,127],_cU=function(_cV){return new F(function(){return _ac(_cS,function(_cW){return E(new T(function(){return B(A(_cV,[_cT]));}));});});},_cX=[1,_cU,_S],_cY=[1,_cP,_cX],_cZ=[1,_cK,_cY],_d0=[1,_cF,_cZ],_d1=[1,_cA,_d0],_d2=[1,_cv,_d1],_d3=[1,_cq,_d2],_d4=[1,_cl,_d3],_d5=[1,_cg,_d4],_d6=[1,_cb,_d5],_d7=[1,_c6,_d6],_d8=[1,_c1,_d7],_d9=[1,_bW,_d8],_da=[1,_bR,_d9],_db=[1,_bM,_da],_dc=[1,_bH,_db],_dd=[1,_bC,_dc],_de=[1,_bx,_dd],_df=[1,_bs,_de],_dg=[1,_bn,_df],_dh=[1,_bi,_dg],_di=[1,_bd,_dh],_dj=[1,_b8,_di],_dk=[1,_b3,_dj],_dl=[1,_aY,_dk],_dm=[1,_aT,_dl],_dn=[1,_aO,_dm],_do=[1,_aJ,_dn],_dp=[1,_aE,_do],_dq=[1,_az,_dp],_dr=[1,_au,_dq],_ds=[1,_ap,_dr],_dt=new T(function(){return B(unCStr("SOH"));}),_du=[0,1],_dv=function(_dw){return new F(function(){return _ac(_dt,function(_dx){return E(new T(function(){return B(A(_dw,[_du]));}));});});},_dy=new T(function(){return B(unCStr("SO"));}),_dz=[0,14],_dA=function(_dB){return new F(function(){return _ac(_dy,function(_dC){return E(new T(function(){return B(A(_dB,[_dz]));}));});});},_dD=function(_dE){return new F(function(){return _7y(_dv,_dA,_dE);});},_dF=[1,_dD,_ds],_dG=new T(function(){return B(_a1(_dF));}),_dH=[0,1114111],_dI=[0,34],_dJ=[0,_dI,_9G],_dK=[0,39],_dL=[0,_dK,_9G],_dM=[0,92],_dN=[0,_dM,_9G],_dO=[0,_aS,_9G],_dP=[0,_aX,_9G],_dQ=[0,_bh,_9G],_dR=[0,_b7,_9G],_dS=[0,_bm,_9G],_dT=[0,_b2,_9G],_dU=[0,_bc,_9G],_dV=[0,_ao,_9G],_dW=[0,_du,_9G],_dX=[0,_at,_9G],_dY=[0,_ay,_9G],_dZ=[0,_aD,_9G],_e0=[0,_aI,_9G],_e1=[0,_aN,_9G],_e2=[0,_aS,_9G],_e3=[0,_aX,_9G],_e4=[0,_b2,_9G],_e5=[0,_b7,_9G],_e6=[0,_bc,_9G],_e7=[0,_bh,_9G],_e8=[0,_bm,_9G],_e9=[0,_dz,_9G],_ea=[0,_br,_9G],_eb=[0,_bw,_9G],_ec=[0,_bB,_9G],_ed=[0,_bG,_9G],_ee=[0,_bL,_9G],_ef=[0,_bQ,_9G],_eg=[0,_bV,_9G],_eh=[0,_c0,_9G],_ei=[0,_c5,_9G],_ej=[0,_ca,_9G],_ek=[0,_cf,_9G],_el=[0,_ck,_9G],_em=[0,_cp,_9G],_en=[0,_cu,_9G],_eo=[0,_cz,_9G],_ep=[0,_cE,_9G],_eq=[0,_cJ,_9G],_er=function(_es){return new F(function(){return _6g([0,function(_et){switch(E(E(_et)[1])){case 34:return E(new T(function(){return B(A(_es,[_dJ]));}));case 39:return E(new T(function(){return B(A(_es,[_dL]));}));case 92:return E(new T(function(){return B(A(_es,[_dN]));}));case 97:return E(new T(function(){return B(A(_es,[_dO]));}));case 98:return E(new T(function(){return B(A(_es,[_dP]));}));case 102:return E(new T(function(){return B(A(_es,[_dQ]));}));case 110:return E(new T(function(){return B(A(_es,[_dR]));}));case 114:return E(new T(function(){return B(A(_es,[_dS]));}));case 116:return E(new T(function(){return B(A(_es,[_dT]));}));case 118:return E(new T(function(){return B(A(_es,[_dU]));}));default:return [2];}}],new T(function(){return B(_6g(B(_7y(_9H,_9K,function(_eu){return new F(function(){return _7V(_eu,function(_ev){var _ew=B(_8U(new T(function(){return B(_8K(E(_eu)[1]));}),_8J,_ev));return !B(_9R(_ew,_dH))?[2]:B(A(_es,[[0,new T(function(){var _ex=B(_9O(_ew));if(_ex>>>0>1114111){var _ey=B(_9M(_ex));}else{var _ey=[0,_ex];}var _ez=_ey,_eA=_ez;return _eA;}),_9G]]));});});})),new T(function(){return B(_6g([0,function(_eB){return E(E(_eB)[1])==94?E([0,function(_eC){switch(E(E(_eC)[1])){case 64:return E(new T(function(){return B(A(_es,[_dV]));}));case 65:return E(new T(function(){return B(A(_es,[_dW]));}));case 66:return E(new T(function(){return B(A(_es,[_dX]));}));case 67:return E(new T(function(){return B(A(_es,[_dY]));}));case 68:return E(new T(function(){return B(A(_es,[_dZ]));}));case 69:return E(new T(function(){return B(A(_es,[_e0]));}));case 70:return E(new T(function(){return B(A(_es,[_e1]));}));case 71:return E(new T(function(){return B(A(_es,[_e2]));}));case 72:return E(new T(function(){return B(A(_es,[_e3]));}));case 73:return E(new T(function(){return B(A(_es,[_e4]));}));case 74:return E(new T(function(){return B(A(_es,[_e5]));}));case 75:return E(new T(function(){return B(A(_es,[_e6]));}));case 76:return E(new T(function(){return B(A(_es,[_e7]));}));case 77:return E(new T(function(){return B(A(_es,[_e8]));}));case 78:return E(new T(function(){return B(A(_es,[_e9]));}));case 79:return E(new T(function(){return B(A(_es,[_ea]));}));case 80:return E(new T(function(){return B(A(_es,[_eb]));}));case 81:return E(new T(function(){return B(A(_es,[_ec]));}));case 82:return E(new T(function(){return B(A(_es,[_ed]));}));case 83:return E(new T(function(){return B(A(_es,[_ee]));}));case 84:return E(new T(function(){return B(A(_es,[_ef]));}));case 85:return E(new T(function(){return B(A(_es,[_eg]));}));case 86:return E(new T(function(){return B(A(_es,[_eh]));}));case 87:return E(new T(function(){return B(A(_es,[_ei]));}));case 88:return E(new T(function(){return B(A(_es,[_ej]));}));case 89:return E(new T(function(){return B(A(_es,[_ek]));}));case 90:return E(new T(function(){return B(A(_es,[_el]));}));case 91:return E(new T(function(){return B(A(_es,[_em]));}));case 92:return E(new T(function(){return B(A(_es,[_en]));}));case 93:return E(new T(function(){return B(A(_es,[_eo]));}));case 94:return E(new T(function(){return B(A(_es,[_ep]));}));case 95:return E(new T(function(){return B(A(_es,[_eq]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_dG,[function(_eD){return new F(function(){return A(_es,[[0,_eD,_9G]]);});}]));})));})));}));});},_eE=function(_eF){return new F(function(){return A(_eF,[_L]);});},_eG=function(_eH){var _eI=E(_eH);if(!_eI[0]){return E(_eE);}else{var _eJ=_eI[2],_eK=E(E(_eI[1])[1]);switch(_eK){case 9:return function(_eL){return [0,function(_eM){return E(new T(function(){return B(A(new T(function(){return B(_eG(_eJ));}),[_eL]));}));}];};case 10:return function(_eN){return [0,function(_eO){return E(new T(function(){return B(A(new T(function(){return B(_eG(_eJ));}),[_eN]));}));}];};case 11:return function(_eP){return [0,function(_eQ){return E(new T(function(){return B(A(new T(function(){return B(_eG(_eJ));}),[_eP]));}));}];};case 12:return function(_eR){return [0,function(_eS){return E(new T(function(){return B(A(new T(function(){return B(_eG(_eJ));}),[_eR]));}));}];};case 13:return function(_eT){return [0,function(_eU){return E(new T(function(){return B(A(new T(function(){return B(_eG(_eJ));}),[_eT]));}));}];};case 32:return function(_eV){return [0,function(_eW){return E(new T(function(){return B(A(new T(function(){return B(_eG(_eJ));}),[_eV]));}));}];};case 160:return function(_eX){return [0,function(_eY){return E(new T(function(){return B(A(new T(function(){return B(_eG(_eJ));}),[_eX]));}));}];};default:var _eZ=u_iswspace(_eK),_f0=_eZ;return E(_f0)==0?E(_eE):function(_f1){return [0,function(_f2){return E(new T(function(){return B(A(new T(function(){return B(_eG(_eJ));}),[_f1]));}));}];};}}},_f3=function(_f4){var _f5=new T(function(){return B(_f3(_f4));}),_f6=[1,function(_f7){return new F(function(){return A(_eG,[_f7,function(_f8){return E([0,function(_f9){return E(E(_f9)[1])==92?E(_f5):[2];}]);}]);});}];return new F(function(){return _6g([0,function(_fa){return E(E(_fa)[1])==92?E([0,function(_fb){var _fc=E(E(_fb)[1]);switch(_fc){case 9:return E(_f6);case 10:return E(_f6);case 11:return E(_f6);case 12:return E(_f6);case 13:return E(_f6);case 32:return E(_f6);case 38:return E(_f5);case 160:return E(_f6);default:var _fd=u_iswspace(_fc),_fe=_fd;return E(_fe)==0?[2]:E(_f6);}}]):[2];}],[0,function(_ff){var _fg=E(_ff);return E(_fg[1])==92?E(new T(function(){return B(_er(_f4));})):B(A(_f4,[[0,_fg,_9F]]));}]);});},_fh=function(_fi,_fj){return new F(function(){return _f3(function(_fk){var _fl=E(_fk),_fm=E(_fl[1]);if(E(_fm[1])==34){if(!E(_fl[2])){return E(new T(function(){return B(A(_fj,[[1,new T(function(){return B(A(_fi,[_S]));})]]));}));}else{return new F(function(){return _fh(function(_fn){return new F(function(){return A(_fi,[[1,_fm,_fn]]);});},_fj);});}}else{return new F(function(){return _fh(function(_fo){return new F(function(){return A(_fi,[[1,_fm,_fo]]);});},_fj);});}});});},_fp=new T(function(){return B(unCStr("_\'"));}),_fq=function(_fr){var _fs=u_iswalnum(_fr),_ft=_fs;return E(_ft)==0?B(_9n(_6X,[0,_fr],_fp)):true;},_fu=function(_fv){return new F(function(){return _fq(E(_fv)[1]);});},_fw=new T(function(){return B(unCStr(",;()[]{}`"));}),_fx=function(_fy){return new F(function(){return A(_fy,[_S]);});},_fz=function(_fA,_fB){var _fC=function(_fD){var _fE=E(_fD);if(!_fE[0]){return E(_fx);}else{var _fF=_fE[1];return !B(A(_fA,[_fF]))?E(_fx):function(_fG){return [0,function(_fH){return E(new T(function(){return B(A(new T(function(){return B(_fC(_fE[2]));}),[function(_fI){return new F(function(){return A(_fG,[[1,_fF,_fI]]);});}]));}));}];};}};return [1,function(_fJ){return new F(function(){return A(_fC,[_fJ,_fB]);});}];},_fK=new T(function(){return B(unCStr(".."));}),_fL=new T(function(){return B(unCStr("::"));}),_fM=new T(function(){return B(unCStr("->"));}),_fN=[0,64],_fO=[1,_fN,_S],_fP=[0,126],_fQ=[1,_fP,_S],_fR=new T(function(){return B(unCStr("=>"));}),_fS=[1,_fR,_S],_fT=[1,_fQ,_fS],_fU=[1,_fO,_fT],_fV=[1,_fM,_fU],_fW=new T(function(){return B(unCStr("<-"));}),_fX=[1,_fW,_fV],_fY=[0,124],_fZ=[1,_fY,_S],_g0=[1,_fZ,_fX],_g1=[1,_dM,_S],_g2=[1,_g1,_g0],_g3=[0,61],_g4=[1,_g3,_S],_g5=[1,_g4,_g2],_g6=[1,_fL,_g5],_g7=[1,_fK,_g6],_g8=function(_g9){return new F(function(){return _6g([1,function(_ga){return E(_ga)[0]==0?E(new T(function(){return B(A(_g9,[_7S]));})):[2];}],new T(function(){return B(_6g([0,function(_gb){return E(E(_gb)[1])==39?E([0,function(_gc){var _gd=E(_gc);switch(E(_gd[1])){case 39:return [2];case 92:return E(new T(function(){return B(_er(function(_ge){var _gf=E(_ge);return new F(function(){return (function(_gg,_gh){var _gi=new T(function(){return B(A(_g9,[[0,_gg]]));});return !E(_gh)?E(E(_gg)[1])==39?[2]:[0,function(_gj){return E(E(_gj)[1])==39?E(_gi):[2];}]:[0,function(_gk){return E(E(_gk)[1])==39?E(_gi):[2];}];})(_gf[1],_gf[2]);});}));}));default:return [0,function(_gl){return E(E(_gl)[1])==39?E(new T(function(){return B(A(_g9,[[0,_gd]]));})):[2];}];}}]):[2];}],new T(function(){return B(_6g([0,function(_gm){return E(E(_gm)[1])==34?E(new T(function(){return B(_fh(_T,_g9));})):[2];}],new T(function(){return B(_6g([0,function(_gn){return !B(_9n(_6X,_gn,_fw))?[2]:B(A(_g9,[[2,[1,_gn,_S]]]));}],new T(function(){return B(_6g([0,function(_go){if(!B(_9n(_6X,_go,_9s))){return [2];}else{return new F(function(){return _fz(_9t,function(_gp){var _gq=[1,_go,_gp];return !B(_9n(_7e,_gq,_g7))?B(A(_g9,[[4,_gq]])):B(A(_g9,[[2,_gq]]));});});}}],new T(function(){return B(_6g([0,function(_gr){var _gs=E(_gr),_gt=_gs[1],_gu=u_iswalpha(_gt),_gv=_gu;if(!E(_gv)){if(E(_gt)==95){return new F(function(){return _fz(_fu,function(_gw){return new F(function(){return A(_g9,[[3,[1,_gs,_gw]]]);});});});}else{return [2];}}else{return new F(function(){return _fz(_fu,function(_gx){return new F(function(){return A(_g9,[[3,[1,_gs,_gx]]]);});});});}}],new T(function(){return B(_7y(_9x,_9i,_g9));})));})));})));})));})));}));});},_gy=function(_gz){return [1,function(_gA){return new F(function(){return A(_eG,[_gA,function(_gB){return E(new T(function(){return B(_g8(_gz));}));}]);});}];},_gC=[0,0],_gD=function(_gE,_gF){return new F(function(){return _gy(function(_gG){var _gH=E(_gG);if(_gH[0]==2){var _gI=E(_gH[1]);return _gI[0]==0?[2]:E(E(_gI[1])[1])==40?E(_gI[2])[0]==0?E(new T(function(){return B(A(_gE,[_gC,function(_gJ){return new F(function(){return _gy(function(_gK){var _gL=E(_gK);if(_gL[0]==2){var _gM=E(_gL[1]);return _gM[0]==0?[2]:E(E(_gM[1])[1])==41?E(_gM[2])[0]==0?E(new T(function(){return B(A(_gF,[_gJ]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_gN=function(_gO,_gP,_gQ){var _gR=function(_gS,_gT){return new F(function(){return _6g(B(_gy(function(_gU){var _gV=E(_gU);if(_gV[0]==4){var _gW=E(_gV[1]);if(!_gW[0]){return new F(function(){return A(_gO,[_gV,_gS,_gT]);});}else{return E(E(_gW[1])[1])==45?E(_gW[2])[0]==0?E([1,function(_gX){return new F(function(){return A(_eG,[_gX,function(_gY){return E(new T(function(){return B(_g8(function(_gZ){return new F(function(){return A(_gO,[_gZ,_gS,function(_h0){return new F(function(){return A(_gT,[new T(function(){return [0, -E(_h0)[1]];})]);});}]);});}));}));}]);});}]):B(A(_gO,[_gV,_gS,_gT])):B(A(_gO,[_gV,_gS,_gT]));}}else{return new F(function(){return A(_gO,[_gV,_gS,_gT]);});}})),new T(function(){return B(_gD(_gR,_gT));}));});};return new F(function(){return _gR(_gP,_gQ);});},_h1=function(_h2,_h3){return [2];},_h4=function(_h5,_h6){return new F(function(){return _h1(_h5,_h6);});},_h7=function(_h8){var _h9=E(_h8);return _h9[0]==0?[1,new T(function(){return B(_8U(new T(function(){return B(_8K(E(_h9[1])[1]));}),_8J,_h9[2]));})]:E(_h9[2])[0]==0?E(_h9[3])[0]==0?[1,new T(function(){return B(_8U(_8I,_8J,_h9[1]));})]:[0]:[0];},_ha=function(_hb){var _hc=E(_hb);if(_hc[0]==5){var _hd=B(_h7(_hc[1]));return _hd[0]==0?E(_h1):function(_he,_hf){return new F(function(){return A(_hf,[new T(function(){return [0,B(_9O(_hd[1]))];})]);});};}else{return E(_h4);}},_hg=function(_hh,_hi){while(1){var _hj=E(_hh);if(!_hj[0]){return E(_hi)[0]==0?true:false;}else{var _hk=E(_hi);if(!_hk[0]){return false;}else{if(E(_hj[1])[1]!=E(_hk[1])[1]){return false;}else{_hh=_hj[2];_hi=_hk[2];continue;}}}}},_hl=new T(function(){return B(unCStr("onSideIndex"));}),_hm=new T(function(){return B(unCStr("LeftSidePlacement"));}),_hn=new T(function(){return B(unCStr("RightSidePlacement"));}),_ho=function(_hp,_hq){var _hr=new T(function(){if(_hp>11){var _hs=[2];}else{var _hs=[1,function(_ht){return new F(function(){return A(_eG,[_ht,function(_hu){return E(new T(function(){return B(_g8(function(_hv){var _hw=E(_hv);return _hw[0]==3?!B(_hg(_hw[1],_hn))?[2]:E([1,function(_hx){return new F(function(){return A(_eG,[_hx,function(_hy){return E(new T(function(){return B(_g8(function(_hz){var _hA=E(_hz);if(_hA[0]==2){var _hB=E(_hA[1]);return _hB[0]==0?[2]:E(E(_hB[1])[1])==123?E(_hB[2])[0]==0?E([1,function(_hC){return new F(function(){return A(_eG,[_hC,function(_hD){return E(new T(function(){return B(_g8(function(_hE){var _hF=E(_hE);return _hF[0]==3?!B(_hg(_hF[1],_hl))?[2]:E([1,function(_hG){return new F(function(){return A(_eG,[_hG,function(_hH){return E(new T(function(){return B(_g8(function(_hI){var _hJ=E(_hI);if(_hJ[0]==2){var _hK=E(_hJ[1]);return _hK[0]==0?[2]:E(E(_hK[1])[1])==61?E(_hK[2])[0]==0?E(new T(function(){return B(_gN(_ha,_gC,function(_hL){return new F(function(){return _gy(function(_hM){var _hN=E(_hM);if(_hN[0]==2){var _hO=E(_hN[1]);return _hO[0]==0?[2]:E(E(_hO[1])[1])==125?E(_hO[2])[0]==0?E(new T(function(){return B(A(_hq,[[3,_hL]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}];}return _hs;});if(_hp>11){return new F(function(){return _6g(_7q,_hr);});}else{return new F(function(){return _6g(B(_gy(function(_hP){var _hQ=E(_hP);return _hQ[0]==3?!B(_hg(_hQ[1],_hm))?[2]:E([1,function(_hR){return new F(function(){return A(_eG,[_hR,function(_hS){return E(new T(function(){return B(_g8(function(_hT){var _hU=E(_hT);if(_hU[0]==2){var _hV=E(_hU[1]);return _hV[0]==0?[2]:E(E(_hV[1])[1])==123?E(_hV[2])[0]==0?E([1,function(_hW){return new F(function(){return A(_eG,[_hW,function(_hX){return E(new T(function(){return B(_g8(function(_hY){var _hZ=E(_hY);return _hZ[0]==3?!B(_hg(_hZ[1],_hl))?[2]:E([1,function(_i0){return new F(function(){return A(_eG,[_i0,function(_i1){return E(new T(function(){return B(_g8(function(_i2){var _i3=E(_i2);if(_i3[0]==2){var _i4=E(_i3[1]);return _i4[0]==0?[2]:E(E(_i4[1])[1])==61?E(_i4[2])[0]==0?E(new T(function(){return B(_gN(_ha,_gC,function(_i5){return new F(function(){return _gy(function(_i6){var _i7=E(_i6);if(_i7[0]==2){var _i8=E(_i7[1]);return _i8[0]==0?[2]:E(E(_i8[1])[1])==125?E(_i8[2])[0]==0?E(new T(function(){return B(A(_hq,[[2,_i5]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),_hr);});}},_i9=new T(function(){return B(unCStr("onBarIndex"));}),_ia=new T(function(){return B(unCStr("BarPlacement"));}),_ib=function(_ic,_id){if(_ic>11){return new F(function(){return _6g(_7q,new T(function(){return B(_ho(_ic,_id));}));});}else{return new F(function(){return _6g(B(_gy(function(_ie){var _if=E(_ie);return _if[0]==3?!B(_hg(_if[1],_ia))?[2]:E([1,function(_ig){return new F(function(){return A(_eG,[_ig,function(_ih){return E(new T(function(){return B(_g8(function(_ii){var _ij=E(_ii);if(_ij[0]==2){var _ik=E(_ij[1]);return _ik[0]==0?[2]:E(E(_ik[1])[1])==123?E(_ik[2])[0]==0?E([1,function(_il){return new F(function(){return A(_eG,[_il,function(_im){return E(new T(function(){return B(_g8(function(_in){var _io=E(_in);return _io[0]==3?!B(_hg(_io[1],_i9))?[2]:E([1,function(_ip){return new F(function(){return A(_eG,[_ip,function(_iq){return E(new T(function(){return B(_g8(function(_ir){var _is=E(_ir);if(_is[0]==2){var _it=E(_is[1]);return _it[0]==0?[2]:E(E(_it[1])[1])==61?E(_it[2])[0]==0?E(new T(function(){return B(_gN(_ha,_gC,function(_iu){return new F(function(){return _gy(function(_iv){var _iw=E(_iv);if(_iw[0]==2){var _ix=E(_iw[1]);return _ix[0]==0?[2]:E(E(_ix[1])[1])==125?E(_ix[2])[0]==0?E(new T(function(){return B(A(_id,[[1,_iu]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_ho(_ic,_id));}));});}},_iy=new T(function(){return B(unCStr("onPointIndex"));}),_iz=new T(function(){return B(unCStr("pointIndex"));}),_iA=new T(function(){return B(unCStr("PointPlacement"));}),_iB=function(_iC,_iD){if(_iC>11){return new F(function(){return _6g(_7q,new T(function(){return B(_ib(_iC,_iD));}));});}else{return new F(function(){return _6g(B(_gy(function(_iE){var _iF=E(_iE);return _iF[0]==3?!B(_hg(_iF[1],_iA))?[2]:E([1,function(_iG){return new F(function(){return A(_eG,[_iG,function(_iH){return E(new T(function(){return B(_g8(function(_iI){var _iJ=E(_iI);if(_iJ[0]==2){var _iK=E(_iJ[1]);return _iK[0]==0?[2]:E(E(_iK[1])[1])==123?E(_iK[2])[0]==0?E([1,function(_iL){return new F(function(){return A(_eG,[_iL,function(_iM){return E(new T(function(){return B(_g8(function(_iN){var _iO=E(_iN);return _iO[0]==3?!B(_hg(_iO[1],_iz))?[2]:E([1,function(_iP){return new F(function(){return A(_eG,[_iP,function(_iQ){return E(new T(function(){return B(_g8(function(_iR){var _iS=E(_iR);if(_iS[0]==2){var _iT=E(_iS[1]);return _iT[0]==0?[2]:E(E(_iT[1])[1])==61?E(_iT[2])[0]==0?E(new T(function(){return B(_gN(_ha,_gC,function(_iU){return new F(function(){return _gy(function(_iV){var _iW=E(_iV);if(_iW[0]==2){var _iX=E(_iW[1]);return _iX[0]==0?[2]:E(E(_iX[1])[1])==44?E(_iX[2])[0]==0?E([1,function(_iY){return new F(function(){return A(_eG,[_iY,function(_iZ){return E(new T(function(){return B(_g8(function(_j0){var _j1=E(_j0);return _j1[0]==3?!B(_hg(_j1[1],_iy))?[2]:E([1,function(_j2){return new F(function(){return A(_eG,[_j2,function(_j3){return E(new T(function(){return B(_g8(function(_j4){var _j5=E(_j4);if(_j5[0]==2){var _j6=E(_j5[1]);return _j6[0]==0?[2]:E(E(_j6[1])[1])==61?E(_j6[2])[0]==0?E(new T(function(){return B(_gN(_ha,_gC,function(_j7){return new F(function(){return _gy(function(_j8){var _j9=E(_j8);if(_j9[0]==2){var _ja=E(_j9[1]);return _ja[0]==0?[2]:E(E(_ja[1])[1])==125?E(_ja[2])[0]==0?E(new T(function(){return B(A(_iD,[[0,_iU,_j7]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_ib(_iC,_iD));}));});}},_jb=function(_jc,_jd){return new F(function(){return _iB(E(_jc)[1],_jd);});},_je=function(_jf,_jg){var _jh=function(_ji){return function(_jj){return new F(function(){return _6g(B(A(new T(function(){return B(A(_jf,[_ji]));}),[_jj])),new T(function(){return B(_gD(_jh,_jj));}));});};};return new F(function(){return _jh(_jg);});},_jk=function(_jl){return [1,function(_jm){return new F(function(){return A(_eG,[_jm,function(_jn){return E([3,_jl,_7q]);}]);});}];},_jo=new T(function(){return B(A(_je,[_jb,_gC,_jk]));}),_jp=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_jq=new T(function(){return B(err(_jp));}),_jr=function(_js,_jt){return new F(function(){return A(_jt,[_52]);});},_ju=[0,_6,_jr],_jv=[1,_ju,_S],_jw=function(_jx,_jy){return new F(function(){return A(_jy,[_51]);});},_jz=[0,_5,_jw],_jA=[1,_jz,_jv],_jB=function(_jC,_jD,_jE){var _jF=E(_jC);if(!_jF[0]){return [2];}else{var _jG=E(_jF[1]),_jH=_jG[1],_jI=new T(function(){return B(A(_jG[2],[_jD,_jE]));});return new F(function(){return _6g(B(_gy(function(_jJ){var _jK=E(_jJ);switch(_jK[0]){case 3:return !B(_hg(_jH,_jK[1]))?[2]:E(_jI);case 4:return !B(_hg(_jH,_jK[1]))?[2]:E(_jI);default:return [2];}})),new T(function(){return B(_jB(_jF[2],_jD,_jE));}));});}},_jL=function(_jM,_jN){return new F(function(){return _jB(_jA,_jM,_jN);});},_jO=new T(function(){return B(A(_je,[_jL,_gC,_jk]));}),_jP=new T(function(){return B(err(_jp));}),_jQ=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_jR=new T(function(){return B(err(_jQ));}),_jS=new T(function(){return B(err(_jQ));}),_jT=function(_jU,_jV,_jW){return _jW<=_jV?[1,[0,_jU],new T(function(){var _jX=_jV-_jU|0,_jY=function(_jZ){return _jZ>=(_jW-_jX|0)?[1,[0,_jZ],new T(function(){return B(_jY(_jZ+_jX|0));})]:[1,[0,_jZ],_S];};return B(_jY(_jV));})]:_jW<=_jU?[1,[0,_jU],_S]:[0];},_k0=function(_k1,_k2,_k3){return _k3>=_k2?[1,[0,_k1],new T(function(){var _k4=_k2-_k1|0,_k5=function(_k6){return _k6<=(_k3-_k4|0)?[1,[0,_k6],new T(function(){return B(_k5(_k6+_k4|0));})]:[1,[0,_k6],_S];};return B(_k5(_k2));})]:_k3>=_k1?[1,[0,_k1],_S]:[0];},_k7=function(_k8,_k9){return _k9<_k8?B(_jT(_k8,_k9,-2147483648)):B(_k0(_k8,_k9,2147483647));},_ka=new T(function(){return B(_k7(135,150));}),_kb=function(_kc,_kd){var _ke=E(_kc);if(!_ke){return [0];}else{var _kf=E(_kd);return _kf[0]==0?[0]:[1,_kf[1],new T(function(){return B(_kb(_ke-1|0,_kf[2]));})];}},_kg=new T(function(){return B(_kb(6,_ka));}),_kh=function(_ki,_kj){var _kk=E(_ki);if(!_kk[0]){return E(_kg);}else{var _kl=_kk[1];return _kj>1?[1,_kl,new T(function(){return B(_kh(_kk[2],_kj-1|0));})]:[1,_kl,_kg];}},_km=new T(function(){return B(_k7(25,40));}),_kn=new T(function(){return B(_kh(_km,6));}),_ko=function(_kp){while(1){var _kq=(function(_kr){var _ks=E(_kr);if(!_ks[0]){return [0];}else{var _kt=_ks[2],_ku=E(_ks[1]);if(!E(_ku[2])[0]){return [1,_ku[1],new T(function(){return B(_ko(_kt));})];}else{_kp=_kt;return null;}}})(_kp);if(_kq!=null){return _kq;}}},_kv=function(_kw,_kx){var _ky=E(_kx);if(!_ky[0]){return [0,_S,_S];}else{var _kz=_ky[1];if(!B(A(_kw,[_kz]))){var _kA=new T(function(){var _kB=B(_kv(_kw,_ky[2]));return [0,_kB[1],_kB[2]];});return [0,[1,_kz,new T(function(){return E(E(_kA)[1]);})],new T(function(){return E(E(_kA)[2]);})];}else{return [0,_S,_ky];}}},_kC=function(_kD,_kE){while(1){var _kF=E(_kE);if(!_kF[0]){return [0];}else{if(!B(A(_kD,[_kF[1]]))){return E(_kF);}else{_kE=_kF[2];continue;}}}},_kG=function(_kH){var _kI=E(_kH);switch(_kI){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _kJ=u_iswspace(_kI),_kK=_kJ;return E(_kK)==0?false:true;}},_kL=function(_kM){return new F(function(){return _kG(E(_kM)[1]);});},_kN=function(_kO){var _kP=B(_kC(_kL,_kO));if(!_kP[0]){return [0];}else{var _kQ=new T(function(){var _kR=B(_kv(_kL,_kP));return [0,_kR[1],_kR[2]];});return [1,new T(function(){return E(E(_kQ)[1]);}),new T(function(){return B(_kN(E(_kQ)[2]));})];}},_kS=function(_kT,_){var _kU=jsFind(toJSStr(E(_5X))),_kV=_kU,_kW=function(_){var _kX=setDropCheckerCallback_ffi(function(_kY,_kZ,_l0){var _l1=E(_kT),_l2=_l1[1],_l3=_l1[6],_l4=new T(function(){return B(_kN(B(_5R(_kY))));}),_l5=B(_ko(B(_66(_jo,new T(function(){return B(_12(_5T,B(_57(_l4,2))));})))));if(!_l5[0]){return E(_jS);}else{if(!E(_l5[2])[0]){var _l6=E(_l5[1]);if(!_l6[0]){var _l7=B(_5y(function(_l8){var _l9=E(_l8)[1]-E(_kZ)[1];return _l9<0? -_l9<7:_l9<7;},_kn));if(!_l7[0]){return function(_7R){return new F(function(){return _5i(_l6,_l6,_l3,_7R);});};}else{var _la=_l7[1],_lb=function(_lc,_ld,_){var _le=E(_l6[1]),_lf=_le[1];if(_lc<=_lf){return new F(function(){return _5i(_l6,_l6,_l3,_);});}else{var _lg=B(_ko(B(_66(_jO,new T(function(){return B(_57(_l4,1));})))));if(!_lg[0]){return E(_jR);}else{var _lh=_lg[1];if(!E(_lg[2])[0]){if(_lc>=0){var _li=B(_57(_l2,_lc)),_lj=function(_){var _lk=B(_5i(_l6,[0,_ld,new T(function(){if(_lc>=0){var _ll=E(B(_57(_l2,_lc))[2]);}else{var _ll=E(_54);}return _ll;})],_l3,_)),_lm=_lk;if(_lf>=0){var _ln=new T(function(){return B(_5K(function(_lo,_lp,_lq){return [1,new T(function(){var _lr=E(_lo)[1];return _lr!=_lf?_lr!=_lc?E(_lp):[0,new T(function(){if(_lf>=0){var _ls=E(B(_57(_l2,_lf))[1]);}else{var _ls=E(_54);}return _ls;}),new T(function(){return [0,E(E(_lp)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_lp)[1]);}),new T(function(){return [0,E(E(_lp)[2])[1]-1|0];})];}),_lq];},_S,_4r,_l2));}),_lt=B((function(_lu,_){while(1){var _lv=(function(_lw,_){var _lx=E(_lw);if(!_lx[0]){return _L;}else{var _ly=_lx[1],_lz=B(_5i([0,_le,_ly],[0,_le,new T(function(){return [0,E(_ly)[1]-1|0];})],_l3,_)),_lA=_lz;_lu=_lx[2];return null;}})(_lu,_);if(_lv!=null){return _lv;}}})(B(_5s(1,B(_4l(E(_l6[2])[1],E(B(_57(_ln,_lf))[2])[1])))),_)),_lB=_lt;return new F(function(){return _kS([0,_ln,_l1[2],_l1[3],_l1[4],_l1[5],_l3,_l1[7]],_);});}else{return E(_54);}},_lC=function(_){return E(_li[2])[1]>=2?B(_5i(_l6,_l6,_l3,_)):B(_lj(_));};return E(_li[1])==0?E(_lh)==0?B(_lj(_)):B(_lC(_)):E(_lh)==0?B(_lC(_)):B(_lj(_));}else{return E(_54);}}else{return E(_jP);}}}};if(E(_l0)[1]<=E(_5W)[1]){var _lD=E(_la);return function(_7R){return new F(function(){return _lb(_lD[1],_lD,_7R);});};}else{var _lE=23-E(_la)[1]|0;return function(_7R){return new F(function(){return _lb(_lE,[0,_lE],_7R);});};}}}else{return function(_7R){return new F(function(){return _5i(_l6,_l6,_l3,_7R);});};}}else{return E(_jq);}}});return _L;},_lF=E(_kV);if(!_lF[0]){return new F(function(){return _kW(_);});}else{var _lG=jsSetCB(E(_lF[1])[1],E(_5x)[1],E(_64)[1]),_lH=_lG;return new F(function(){return _kW(_);});}},_lI=function(_lJ,_lK){while(1){var _lL=E(_lJ);if(!_lL[0]){return E(_lK);}else{_lJ=_lL[2];var _lM=[1,_lL[1],_lK];_lK=_lM;continue;}}},_lN=[0,2],_lO=[0,0],_lP=[1,_lO,_S],_lQ=[1,_lO,_lP],_lR=[1,_lO,_lQ],_lS=[1,_lO,_lR],_lT=[1,_lO,_lS],_lU=[0,5],_lV=[1,_lU,_lT],_lW=[1,_lO,_lV],_lX=[0,3],_lY=[1,_lX,_lW],_lZ=[1,_lO,_lY],_m0=[1,_lO,_lZ],_m1=[1,_lO,_m0],_m2=[1,_lO,_m1],_m3=[1,_lU,_m2],_m4=[1,_lO,_m3],_m5=[1,_lO,_m4],_m6=[1,_lO,_m5],_m7=[1,_lO,_m6],_m8=[1,_lO,_m7],_m9=[1,_lO,_m8],_ma=[1,_lO,_m9],_mb=[1,_lO,_ma],_mc=[1,_lO,_mb],_md=[1,_lO,_mc],_me=[1,_lN,_md],_mf=function(_mg){var _mh=E(_mg);return _mh[0]==0?[0]:[1,[0,_52,_mh[1]],new T(function(){return B(_mf(_mh[2]));})];},_mi=new T(function(){return B(_mf(_me));}),_mj=new T(function(){return B(_lI(_mi,_S));}),_mk=new T(function(){return B(_2z("main.hs:(252,20)-(253,55)|function whiteOrBlack"));}),_ml=function(_mm,_mn){var _mo=E(_mm);if(!_mo[0]){return [0];}else{var _mp=E(_mn);return _mp[0]==0?[0]:[1,new T(function(){var _mq=E(_mp[1]);if(!E(_mq[1])){var _mr=E(_mk);}else{if(!E(E(_mq[2])[1])){var _ms=E(_mo[1]),_mt=E(_ms[1])==0?E(_ms):[0,_51,_ms[2]];}else{var _mt=E(_mq);}var _mu=_mt,_mr=_mu;}var _mv=_mr;return _mv;}),new T(function(){return B(_ml(_mo[2],_mp[2]));})];}},_mw=new T(function(){return B(_ml(_mj,_mi));}),_mx=function(_my,_mz){while(1){var _mA=E(_my);if(!_mA[0]){return E(_mz);}else{_my=_mA[2];var _mB=_mz+E(_mA[1])[1]|0;_mz=_mB;continue;}}},_mC=new T(function(){return [0,B(_mx(_me,0))];}),_mD=[0,_mw,_mC,_mC,_lO,_lO,_52,_52],_mE=function(_){var _mF=E(_mC)[1],_mG=B(_4v(_52,_52,_mF,_)),_mH=_mG,_mI=B(_4v(_51,_52,_mF,_)),_mJ=_mI;return new F(function(){return _kS(_mD,_);});},_mK=function(_){var _mL=jsFind(toJSStr(E(_3))),_mM=_mL,_mN=E(_mM);if(!_mN[0]){var _mO=consoleLog_ffi(toJSStr(E(_2)));return new F(function(){return _mE(_);});}else{var _mP=jsSet(E(_mN[1])[1],toJSStr(E(_4)),toJSStr(E(_1))),_mQ=consoleLog_ffi(toJSStr(E(_0)));return new F(function(){return _mE(_);});}},_mR=function(_){return new F(function(){return _mK(_);});};
var hasteMain = function() {B(A(_mR, [0]));};window.onload = hasteMain;