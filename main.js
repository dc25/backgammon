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

var _0=new T(function(){return B(unCStr("You have not joined a game (yet)."));}),_1=new T(function(){return B(unCStr("innerHTML"));}),_2=new T(function(){return B(unCStr("HintText"));}),_3=new T(function(){return B(unCStr("Black"));}),_4=new T(function(){return B(unCStr("White"));}),_5=[0,125],_6=new T(function(){return B(unCStr(", "));}),_7=function(_8,_9){var _a=E(_8);return _a[0]==0?E(_9):[1,_a[1],new T(function(){return B(_7(_a[2],_9));})];},_b=function(_c,_d){var _e=jsShowI(_c),_f=_e;return new F(function(){return _7(fromJSStr(_f),_d);});},_g=[0,41],_h=[0,40],_i=function(_j,_k,_l){return _k>=0?B(_b(_k,_l)):_j<=6?B(_b(_k,_l)):[1,_h,new T(function(){var _m=jsShowI(_k),_n=_m;return B(_7(fromJSStr(_n),[1,_g,_l]));})];},_o=new T(function(){return B(unCStr("onPointIndex = "));}),_p=new T(function(){return B(unCStr("BarPlacement {"));}),_q=new T(function(){return B(unCStr("onBarIndex = "));}),_r=new T(function(){return B(unCStr("LeftSidePlacement {"));}),_s=new T(function(){return B(unCStr("onSideIndex = "));}),_t=new T(function(){return B(unCStr("RightSidePlacement {"));}),_u=new T(function(){return B(unCStr("PointPlacement {"));}),_v=new T(function(){return B(unCStr("pointIndex = "));}),_w=function(_x,_y,_z){var _A=E(_y);switch(_A[0]){case 0:var _B=function(_C){return new F(function(){return _7(_v,new T(function(){return B(_i(0,E(_A[1])[1],new T(function(){return B(_7(_6,new T(function(){return B(_7(_o,new T(function(){return B(_i(0,E(_A[2])[1],[1,_5,_C]));})));})));})));}));});};return _x<11?B(_7(_u,new T(function(){return B(_B(_z));}))):[1,_h,new T(function(){return B(_7(_u,new T(function(){return B(_B([1,_g,_z]));})));})];case 1:var _D=function(_E){return new F(function(){return _7(_p,new T(function(){return B(_7(_q,new T(function(){return B(_i(0,E(_A[1])[1],[1,_5,_E]));})));}));});};return _x<11?B(_D(_z)):[1,_h,new T(function(){return B(_D([1,_g,_z]));})];case 2:var _F=function(_G){return new F(function(){return _7(_r,new T(function(){return B(_7(_s,new T(function(){return B(_i(0,E(_A[1])[1],[1,_5,_G]));})));}));});};return _x<11?B(_F(_z)):[1,_h,new T(function(){return B(_F([1,_g,_z]));})];default:var _H=function(_I){return new F(function(){return _7(_t,new T(function(){return B(_7(_s,new T(function(){return B(_i(0,E(_A[1])[1],[1,_5,_I]));})));}));});};return _x<11?B(_H(_z)):[1,_h,new T(function(){return B(_H([1,_g,_z]));})];}},_J=0,_K=function(_L,_M,_N,_O){return new F(function(){return A(_L,[new T(function(){return function(_){var _P=jsSetAttr(E(_M)[1],toJSStr(E(_N)),toJSStr(E(_O)));return _J;};})]);});},_Q=[0],_R=function(_S){return E(_S);},_T=[0,95],_U=function(_V){var _W=E(_V);return E(_W[1])==32?E(_T):E(_W);},_X=new T(function(){return B(unCStr("class"));}),_Y=new T(function(){return B(unCStr("draggable "));}),_Z=[0,32],_10=function(_11,_12){var _13=E(_12);return _13[0]==0?[0]:[1,new T(function(){return B(A(_11,[_13[1]]));}),new T(function(){return B(_10(_11,_13[2]));})];},_14=function(_15,_16,_17,_18){return new F(function(){return _K(_R,_15,_X,new T(function(){var _19=new T(function(){var _1a=new T(function(){return B(_10(_U,B(_w(0,_17,_Q))));});return E(_18)==0?B(_7(_3,[1,_Z,_1a])):B(_7(_4,[1,_Z,_1a]));});return E(_16)==0?E(_18)==0?B(_7(_Y,_19)):E(_19):E(_18)==0?E(_19):B(_7(_Y,_19));}));});},_1b=new T(function(){return B(unCStr("Control.Exception.Base"));}),_1c=new T(function(){return B(unCStr("base"));}),_1d=new T(function(){return B(unCStr("PatternMatchFail"));}),_1e=new T(function(){var _1f=hs_wordToWord64(18445595),_1g=_1f,_1h=hs_wordToWord64(52003073),_1i=_1h;return [0,_1g,_1i,[0,_1g,_1i,_1c,_1b,_1d],_Q];}),_1j=function(_1k){return E(_1e);},_1l=function(_1m){return E(E(_1m)[1]);},_1n=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_1o=new T(function(){return B(err(_1n));}),_1p=function(_1q,_1r,_1s){var _1t=new T(function(){var _1u=B(A(_1q,[_1s])),_1v=B(A(_1r,[new T(function(){var _1w=E(_1t);return _1w[0]==0?E(_1o):E(_1w[1]);})])),_1x=hs_eqWord64(_1u[1],_1v[1]),_1y=_1x;if(!E(_1y)){var _1z=[0];}else{var _1A=hs_eqWord64(_1u[2],_1v[2]),_1B=_1A,_1z=E(_1B)==0?[0]:[1,_1s];}var _1C=_1z,_1D=_1C;return _1D;});return E(_1t);},_1E=function(_1F){var _1G=E(_1F);return new F(function(){return _1p(B(_1l(_1G[1])),_1j,_1G[2]);});},_1H=function(_1I){return E(E(_1I)[1]);},_1J=function(_1K,_1L){return new F(function(){return _7(E(_1K)[1],_1L);});},_1M=[0,44],_1N=[0,93],_1O=[0,91],_1P=function(_1Q,_1R,_1S){var _1T=E(_1R);return _1T[0]==0?B(unAppCStr("[]",_1S)):[1,_1O,new T(function(){return B(A(_1Q,[_1T[1],new T(function(){var _1U=function(_1V){var _1W=E(_1V);return _1W[0]==0?E([1,_1N,_1S]):[1,_1M,new T(function(){return B(A(_1Q,[_1W[1],new T(function(){return B(_1U(_1W[2]));})]));})];};return B(_1U(_1T[2]));})]));})];},_1X=function(_1Y,_1Z){return new F(function(){return _1P(_1J,_1Y,_1Z);});},_20=function(_21,_22,_23){return new F(function(){return _7(E(_22)[1],_23);});},_24=[0,_20,_1H,_1X],_25=new T(function(){return [0,_1j,_24,_26,_1E];}),_26=function(_27){return [0,_25,_27];},_28=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_29=function(_2a,_2b){return new F(function(){return die(new T(function(){return B(A(_2b,[_2a]));}));});},_2c=function(_2d,_2e){var _2f=E(_2e);if(!_2f[0]){return [0,_Q,_Q];}else{var _2g=_2f[1];if(!B(A(_2d,[_2g]))){return [0,_Q,_2f];}else{var _2h=new T(function(){var _2i=B(_2c(_2d,_2f[2]));return [0,_2i[1],_2i[2]];});return [0,[1,_2g,new T(function(){return E(E(_2h)[1]);})],new T(function(){return E(E(_2h)[2]);})];}}},_2j=[0,32],_2k=[0,10],_2l=[1,_2k,_Q],_2m=function(_2n){return E(E(_2n)[1])==124?false:true;},_2o=function(_2p,_2q){var _2r=B(_2c(_2m,B(unCStr(_2p)))),_2s=_2r[1],_2t=function(_2u,_2v){return new F(function(){return _7(_2u,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_7(_2q,new T(function(){return B(_7(_2v,_2l));})));})));}));});},_2w=E(_2r[2]);if(!_2w[0]){return new F(function(){return _2t(_2s,_Q);});}else{return E(E(_2w[1])[1])==124?B(_2t(_2s,[1,_2j,_2w[2]])):B(_2t(_2s,_Q));}},_2x=function(_2y){return new F(function(){return _29([0,new T(function(){return B(_2o(_2y,_28));})],_26);});},_2z=new T(function(){return B(_2x("main.hs:(87,1)-(114,116)|function checkerPosition"));}),_2A=function(_2B,_2C){if(_2B<=0){if(_2B>=0){return new F(function(){return quot(_2B,_2C);});}else{if(_2C<=0){return new F(function(){return quot(_2B,_2C);});}else{return quot(_2B+1|0,_2C)-1|0;}}}else{if(_2C>=0){if(_2B>=0){return new F(function(){return quot(_2B,_2C);});}else{if(_2C<=0){return new F(function(){return quot(_2B,_2C);});}else{return quot(_2B+1|0,_2C)-1|0;}}}else{return quot(_2B-1|0,_2C)-1|0;}}},_2D=new T(function(){return [0,B(_2A(15,2))];}),_2E=new T(function(){return [0,220+B(_2A(15,2))|0];}),_2F=function(_2G){var _2H=E(_2G);switch(_2H[0]){case 0:var _2I=_2H[1],_2J=_2H[2];return [0,new T(function(){var _2K=E(_2I)[1];if(_2K>=12){var _2L=23-_2K|0;if(_2L>=6){var _2M=[0,25+(20+(imul(_2L,15)|0)|0)|0];}else{var _2M=[0,25+(imul(_2L,15)|0)|0];}var _2N=_2M,_2O=_2N;}else{if(_2K>=6){var _2P=[0,25+(20+(imul(_2K,15)|0)|0)|0];}else{var _2P=[0,25+(imul(_2K,15)|0)|0];}var _2O=_2P;}var _2Q=_2O;return _2Q;}),new T(function(){if(E(_2I)[1]>=12){var _2R=[0,203+(imul(imul(imul(-1,E(_2J)[1])|0,2)|0,6)|0)|0];}else{var _2R=[0,7+(imul(imul(E(_2J)[1],2)|0,6)|0)|0];}var _2S=_2R;return _2S;})];case 1:return E(_2z);case 2:return [0,_2D,new T(function(){return [0,203-(imul(imul(E(_2H[1])[1],2)|0,6)|0)|0];})];default:return [0,_2E,new T(function(){return [0,203-(imul(imul(E(_2H[1])[1],2)|0,6)|0)|0];})];}},_2T=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:151:5-10"));}),_2U=function(_){return _J;},_2V=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_2W=new T(function(){return B(unCStr("base"));}),_2X=new T(function(){return B(unCStr("IOException"));}),_2Y=new T(function(){var _2Z=hs_wordToWord64(4053623282),_30=_2Z,_31=hs_wordToWord64(3693590983),_32=_31;return [0,_30,_32,[0,_30,_32,_2W,_2V,_2X],_Q];}),_33=function(_34){return E(_2Y);},_35=function(_36){var _37=E(_36);return new F(function(){return _1p(B(_1l(_37[1])),_33,_37[2]);});},_38=new T(function(){return B(unCStr(": "));}),_39=[0,41],_3a=new T(function(){return B(unCStr(" ("));}),_3b=new T(function(){return B(unCStr("already exists"));}),_3c=new T(function(){return B(unCStr("does not exist"));}),_3d=new T(function(){return B(unCStr("protocol error"));}),_3e=new T(function(){return B(unCStr("failed"));}),_3f=new T(function(){return B(unCStr("invalid argument"));}),_3g=new T(function(){return B(unCStr("inappropriate type"));}),_3h=new T(function(){return B(unCStr("hardware fault"));}),_3i=new T(function(){return B(unCStr("unsupported operation"));}),_3j=new T(function(){return B(unCStr("timeout"));}),_3k=new T(function(){return B(unCStr("resource vanished"));}),_3l=new T(function(){return B(unCStr("interrupted"));}),_3m=new T(function(){return B(unCStr("resource busy"));}),_3n=new T(function(){return B(unCStr("resource exhausted"));}),_3o=new T(function(){return B(unCStr("end of file"));}),_3p=new T(function(){return B(unCStr("illegal operation"));}),_3q=new T(function(){return B(unCStr("permission denied"));}),_3r=new T(function(){return B(unCStr("user error"));}),_3s=new T(function(){return B(unCStr("unsatisified constraints"));}),_3t=new T(function(){return B(unCStr("system error"));}),_3u=function(_3v,_3w){switch(E(_3v)){case 0:return new F(function(){return _7(_3b,_3w);});break;case 1:return new F(function(){return _7(_3c,_3w);});break;case 2:return new F(function(){return _7(_3m,_3w);});break;case 3:return new F(function(){return _7(_3n,_3w);});break;case 4:return new F(function(){return _7(_3o,_3w);});break;case 5:return new F(function(){return _7(_3p,_3w);});break;case 6:return new F(function(){return _7(_3q,_3w);});break;case 7:return new F(function(){return _7(_3r,_3w);});break;case 8:return new F(function(){return _7(_3s,_3w);});break;case 9:return new F(function(){return _7(_3t,_3w);});break;case 10:return new F(function(){return _7(_3d,_3w);});break;case 11:return new F(function(){return _7(_3e,_3w);});break;case 12:return new F(function(){return _7(_3f,_3w);});break;case 13:return new F(function(){return _7(_3g,_3w);});break;case 14:return new F(function(){return _7(_3h,_3w);});break;case 15:return new F(function(){return _7(_3i,_3w);});break;case 16:return new F(function(){return _7(_3j,_3w);});break;case 17:return new F(function(){return _7(_3k,_3w);});break;default:return new F(function(){return _7(_3l,_3w);});}},_3x=[0,125],_3y=new T(function(){return B(unCStr("{handle: "));}),_3z=function(_3A,_3B,_3C,_3D,_3E,_3F){var _3G=new T(function(){var _3H=new T(function(){return B(_3u(_3B,new T(function(){var _3I=E(_3D);return _3I[0]==0?E(_3F):B(_7(_3a,new T(function(){return B(_7(_3I,[1,_39,_3F]));})));})));}),_3J=E(_3C);return _3J[0]==0?E(_3H):B(_7(_3J,new T(function(){return B(_7(_38,_3H));})));}),_3K=E(_3E);if(!_3K[0]){var _3L=E(_3A);if(!_3L[0]){return E(_3G);}else{var _3M=E(_3L[1]);return _3M[0]==0?B(_7(_3y,new T(function(){return B(_7(_3M[1],[1,_3x,new T(function(){return B(_7(_38,_3G));})]));}))):B(_7(_3y,new T(function(){return B(_7(_3M[1],[1,_3x,new T(function(){return B(_7(_38,_3G));})]));})));}}else{return new F(function(){return _7(_3K[1],new T(function(){return B(_7(_38,_3G));}));});}},_3N=function(_3O){var _3P=E(_3O);return new F(function(){return _3z(_3P[1],_3P[2],_3P[3],_3P[4],_3P[6],_Q);});},_3Q=function(_3R,_3S){var _3T=E(_3R);return new F(function(){return _3z(_3T[1],_3T[2],_3T[3],_3T[4],_3T[6],_3S);});},_3U=function(_3V,_3W){return new F(function(){return _1P(_3Q,_3V,_3W);});},_3X=function(_3Y,_3Z,_40){var _41=E(_3Z);return new F(function(){return _3z(_41[1],_41[2],_41[3],_41[4],_41[6],_40);});},_42=[0,_3X,_3N,_3U],_43=new T(function(){return [0,_33,_42,_44,_35];}),_44=function(_45){return [0,_43,_45];},_46=[0],_47=7,_48=function(_49){return [0,_46,_47,_Q,_49,_46,_46];},_4a=function(_4b,_){return new F(function(){return die(new T(function(){return B(_44(new T(function(){return B(_48(_4b));})));}));});},_4c=function(_4d,_){return new F(function(){return _4a(_4d,_);});},_4e=[0,114],_4f=[1,_4e,_Q],_4g=new T(function(){return B(_i(0,6,_Q));}),_4h=new T(function(){return B(unCStr("cx"));}),_4i=new T(function(){return B(unCStr("cy"));}),_4j=function(_4k,_4l){if(_4k<=_4l){var _4m=function(_4n){return [1,[0,_4n],new T(function(){if(_4n!=_4l){var _4o=B(_4m(_4n+1|0));}else{var _4o=[0];}return _4o;})];};return new F(function(){return _4m(_4k);});}else{return [0];}},_4p=new T(function(){return B(_4j(0,2147483647));}),_4q=new T(function(){return B(unCStr("circle"));}),_4r=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_4s=new T(function(){return B(unCStr("board"));}),_4t=function(_4u,_4v,_4w,_){if(_4w>0){var _4x=function(_4y,_4z,_){var _4A=jsFind(toJSStr(E(_4s))),_4B=_4A,_4C=E(_4B);if(!_4C[0]){var _4D=B(_4c(_2T,_)),_4E=_4D;return new F(function(){return A(_4z,[_]);});}else{var _4F=jsCreateElemNS(toJSStr(E(_4r)),toJSStr(E(_4q))),_4G=_4F,_4H=[0,_4G],_4I=B(A(_K,[_R,_4H,_4f,_4g,_])),_4J=_4I,_4K=new T(function(){return E(_4u)==0?[3,_4y]:[2,_4y];}),_4L=new T(function(){var _4M=B(_2F(_4K));return [0,_4M[1],_4M[2]];}),_4N=B(A(_K,[_R,_4H,_4h,new T(function(){return B(_i(0,E(E(_4L)[1])[1],_Q));}),_])),_4O=_4N,_4P=B(A(_K,[_R,_4H,_4i,new T(function(){return B(_i(0,E(E(_4L)[2])[1],_Q));}),_])),_4Q=_4P,_4R=B(A(_14,[_4H,_4v,_4K,_4u,_])),_4S=_4R,_4T=jsAppendChild(_4G,E(_4C[1])[1]);return new F(function(){return A(_4z,[_]);});}},_4U=function(_4V,_4W,_){var _4X=E(_4V);if(!_4X[0]){return _J;}else{var _4Y=_4X[1];if(_4W>1){return new F(function(){return _4x(_4Y,function(_){return new F(function(){return _4U(_4X[2],_4W-1|0,_);});},_);});}else{return new F(function(){return _4x(_4Y,_2U,_);});}}};return new F(function(){return _4U(_4p,_4w,_);});}else{return _J;}},_4Z=0,_50=1,_51=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_52=new T(function(){return B(err(_51));}),_53=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_54=new T(function(){return B(err(_53));}),_55=function(_56,_57){while(1){var _58=E(_56);if(!_58[0]){return E(_54);}else{var _59=E(_57);if(!_59){return E(_58[1]);}else{_56=_58[2];_57=_59-1|0;continue;}}}},_5a=new T(function(){return B(unCStr(": empty list"));}),_5b=new T(function(){return B(unCStr("Prelude."));}),_5c=function(_5d){return new F(function(){return err(B(_7(_5b,new T(function(){return B(_7(_5d,_5a));}))));});},_5e=new T(function(){return B(unCStr("head"));}),_5f=new T(function(){return B(_5c(_5e));}),_5g=function(_5h,_5i,_5j,_){var _5k=jsElemsByClassName(toJSStr(B(_10(_U,B(_w(0,_5h,_Q)))))),_5l=_5k,_5m=E(_5l);if(!_5m[0]){return E(_5f);}else{var _5n=E(_5m[1]),_5o=B(_2F(_5i)),_5p=animateCircle_ffi(_5n[1],E(_5o[1])[1],E(_5o[2])[1],300);return new F(function(){return A(_14,[_5n,_5j,_5i,_5j,_]);});}},_5q=function(_5r,_5s){while(1){var _5t=E(_5r);if(!_5t){return E(_5s);}else{var _5u=E(_5s);if(!_5u[0]){return [0];}else{_5r=_5t-1|0;_5s=_5u[2];continue;}}}},_5v=new T(function(){return [0,"click"];}),_5w=function(_5x,_5y){var _5z=function(_5A,_5B){while(1){var _5C=(function(_5D,_5E){var _5F=E(_5E);if(!_5F[0]){return [0];}else{var _5G=_5F[2];if(!B(A(_5x,[_5F[1]]))){var _5H=_5D+1|0;_5B=_5G;_5A=_5H;return null;}else{return [1,[0,_5D],new T(function(){return B(_5z(_5D+1|0,_5G));})];}}})(_5A,_5B);if(_5C!=null){return _5C;}}};return new F(function(){return _5z(0,_5y);});},_5I=function(_5J,_5K,_5L,_5M){var _5N=E(_5L);if(!_5N[0]){return E(_5K);}else{var _5O=E(_5M);if(!_5O[0]){return E(_5K);}else{return new F(function(){return A(_5J,[_5N[1],_5O[1],new T(function(){return B(_5I(_5J,_5K,_5N[2],_5O[2]));})]);});}}},_5P=function(_5Q){return new F(function(){return fromJSStr(E(_5Q)[1]);});},_5R=function(_5S){var _5T=E(_5S);return E(_5T[1])==95?E(_Z):E(_5T);},_5U=new T(function(){return [0,B(_2A(210,2))];}),_5V=new T(function(){return B(unCStr("joinGame"));}),_5W=new T(function(){return B(unCStr("Clicked Join"));}),_5X=function(_){var _5Y=showAlert_ffi(toJSStr(E(_5W)));return _J;},_5Z=function(_60,_61,_){return new F(function(){return _5X(_);});},_62=[0,_5Z],_63=new T(function(){return B(_2x("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_64=function(_65,_66){while(1){var _67=(function(_68,_69){var _6a=E(_68);switch(_6a[0]){case 0:var _6b=E(_69);if(!_6b[0]){return [0];}else{_65=B(A(_6a[1],[_6b[1]]));_66=_6b[2];return null;}break;case 1:var _6c=B(A(_6a[1],[_69])),_6d=_69;_65=_6c;_66=_6d;return null;case 2:return [0];case 3:return [1,[0,_6a[1],_69],new T(function(){return B(_64(_6a[2],_69));})];default:return E(_6a[1]);}})(_65,_66);if(_67!=null){return _67;}}},_6e=function(_6f,_6g){var _6h=new T(function(){var _6i=E(_6g);if(_6i[0]==3){var _6j=[3,_6i[1],new T(function(){return B(_6e(_6f,_6i[2]));})];}else{var _6k=E(_6f);if(_6k[0]==2){var _6l=E(_6i);}else{var _6m=E(_6i);if(_6m[0]==2){var _6n=E(_6k);}else{var _6o=new T(function(){var _6p=E(_6m);if(_6p[0]==4){var _6q=[1,function(_6r){return [4,new T(function(){return B(_7(B(_64(_6k,_6r)),_6p[1]));})];}];}else{var _6s=E(_6k);if(_6s[0]==1){var _6t=_6s[1],_6u=E(_6p);if(!_6u[0]){var _6v=[1,function(_6w){return new F(function(){return _6e(B(A(_6t,[_6w])),_6u);});}];}else{var _6v=[1,function(_6x){return new F(function(){return _6e(B(A(_6t,[_6x])),new T(function(){return B(A(_6u[1],[_6x]));}));});}];}var _6y=_6v;}else{var _6z=E(_6p);if(!_6z[0]){var _6A=E(_63);}else{var _6A=[1,function(_6B){return new F(function(){return _6e(_6s,new T(function(){return B(A(_6z[1],[_6B]));}));});}];}var _6y=_6A;}var _6q=_6y;}return _6q;}),_6C=E(_6k);switch(_6C[0]){case 1:var _6D=E(_6m);if(_6D[0]==4){var _6E=[1,function(_6F){return [4,new T(function(){return B(_7(B(_64(B(A(_6C[1],[_6F])),_6F)),_6D[1]));})];}];}else{var _6E=E(_6o);}var _6G=_6E;break;case 4:var _6H=_6C[1],_6I=E(_6m);switch(_6I[0]){case 0:var _6J=[1,function(_6K){return [4,new T(function(){return B(_7(_6H,new T(function(){return B(_64(_6I,_6K));})));})];}];break;case 1:var _6J=[1,function(_6L){return [4,new T(function(){return B(_7(_6H,new T(function(){return B(_64(B(A(_6I[1],[_6L])),_6L));})));})];}];break;default:var _6J=[4,new T(function(){return B(_7(_6H,_6I[1]));})];}var _6G=_6J;break;default:var _6G=E(_6o);}var _6n=_6G;}var _6l=_6n;}var _6j=_6l;}return _6j;}),_6M=E(_6f);switch(_6M[0]){case 0:var _6N=E(_6g);return _6N[0]==0?[0,function(_6O){return new F(function(){return _6e(B(A(_6M[1],[_6O])),new T(function(){return B(A(_6N[1],[_6O]));}));});}]:E(_6h);case 3:return [3,_6M[1],new T(function(){return B(_6e(_6M[2],_6g));})];default:return E(_6h);}},_6P=function(_6Q,_6R){return E(_6Q)[1]!=E(_6R)[1];},_6S=function(_6T,_6U){return E(_6T)[1]==E(_6U)[1];},_6V=[0,_6S,_6P],_6W=function(_6X){return E(E(_6X)[1]);},_6Y=function(_6Z,_70,_71){while(1){var _72=E(_70);if(!_72[0]){return E(_71)[0]==0?true:false;}else{var _73=E(_71);if(!_73[0]){return false;}else{if(!B(A(_6W,[_6Z,_72[1],_73[1]]))){return false;}else{_70=_72[2];_71=_73[2];continue;}}}}},_74=function(_75,_76,_77){return !B(_6Y(_75,_76,_77))?true:false;},_78=function(_79){return [0,function(_7a,_7b){return new F(function(){return _6Y(_79,_7a,_7b);});},function(_7a,_7b){return new F(function(){return _74(_79,_7a,_7b);});}];},_7c=new T(function(){return B(_78(_6V));}),_7d=function(_7e,_7f){var _7g=E(_7e);switch(_7g[0]){case 0:return [0,function(_7h){return new F(function(){return _7d(B(A(_7g[1],[_7h])),_7f);});}];case 1:return [1,function(_7i){return new F(function(){return _7d(B(A(_7g[1],[_7i])),_7f);});}];case 2:return [2];case 3:return new F(function(){return _6e(B(A(_7f,[_7g[1]])),new T(function(){return B(_7d(_7g[2],_7f));}));});break;default:var _7j=function(_7k){var _7l=E(_7k);if(!_7l[0]){return [0];}else{var _7m=E(_7l[1]);return new F(function(){return _7(B(_64(B(A(_7f,[_7m[1]])),_7m[2])),new T(function(){return B(_7j(_7l[2]));}));});}},_7n=B(_7j(_7g[1]));return _7n[0]==0?[2]:[4,_7n];}},_7o=[2],_7p=function(_7q){return [3,_7q,_7o];},_7r=function(_7s,_7t){var _7u=E(_7s);if(!_7u){return new F(function(){return A(_7t,[_J]);});}else{return [0,function(_7v){return E(new T(function(){return B(_7r(_7u-1|0,_7t));}));}];}},_7w=function(_7x,_7y,_7z){return [1,function(_7A){return new F(function(){return A(function(_7B,_7C,_7D){while(1){var _7E=(function(_7F,_7G,_7H){var _7I=E(_7F);switch(_7I[0]){case 0:var _7J=E(_7G);if(!_7J[0]){return E(_7y);}else{_7B=B(A(_7I[1],[_7J[1]]));_7C=_7J[2];var _7K=_7H+1|0;_7D=_7K;return null;}break;case 1:var _7L=B(A(_7I[1],[_7G])),_7M=_7G,_7K=_7H;_7B=_7L;_7C=_7M;_7D=_7K;return null;case 2:return E(_7y);case 3:return function(_7N){return new F(function(){return _7r(_7H,function(_7O){return E(new T(function(){return B(_7d(_7I,_7N));}));});});};default:return function(_7P){return new F(function(){return _7d(_7I,_7P);});};}})(_7B,_7C,_7D);if(_7E!=null){return _7E;}}},[new T(function(){return B(A(_7x,[_7p]));}),_7A,0,_7z]);});}];},_7Q=[6],_7R=new T(function(){return B(unCStr("valDig: Bad base"));}),_7S=new T(function(){return B(err(_7R));}),_7T=function(_7U,_7V){var _7W=function(_7X,_7Y){var _7Z=E(_7X);if(!_7Z[0]){return function(_80){return new F(function(){return A(_80,[new T(function(){return B(A(_7Y,[_Q]));})]);});};}else{var _81=E(_7Z[1])[1],_82=function(_83){return function(_84){return [0,function(_85){return E(new T(function(){return B(A(new T(function(){return B(_7W(_7Z[2],function(_86){return new F(function(){return A(_7Y,[[1,_83,_86]]);});}));}),[_84]));}));}];};};switch(E(E(_7U)[1])){case 8:if(48>_81){return function(_87){return new F(function(){return A(_87,[new T(function(){return B(A(_7Y,[_Q]));})]);});};}else{if(_81>55){return function(_88){return new F(function(){return A(_88,[new T(function(){return B(A(_7Y,[_Q]));})]);});};}else{return new F(function(){return _82([0,_81-48|0]);});}}break;case 10:if(48>_81){return function(_89){return new F(function(){return A(_89,[new T(function(){return B(A(_7Y,[_Q]));})]);});};}else{if(_81>57){return function(_8a){return new F(function(){return A(_8a,[new T(function(){return B(A(_7Y,[_Q]));})]);});};}else{return new F(function(){return _82([0,_81-48|0]);});}}break;case 16:var _8b=new T(function(){if(97>_81){if(65>_81){var _8c=[0];}else{if(_81>70){var _8d=[0];}else{var _8d=[1,[0,(_81-65|0)+10|0]];}var _8c=_8d;}var _8e=_8c;}else{if(_81>102){if(65>_81){var _8f=[0];}else{if(_81>70){var _8g=[0];}else{var _8g=[1,[0,(_81-65|0)+10|0]];}var _8f=_8g;}var _8h=_8f;}else{var _8h=[1,[0,(_81-97|0)+10|0]];}var _8e=_8h;}return _8e;});if(48>_81){var _8i=E(_8b);if(!_8i[0]){return function(_8j){return new F(function(){return A(_8j,[new T(function(){return B(A(_7Y,[_Q]));})]);});};}else{return new F(function(){return _82(_8i[1]);});}}else{if(_81>57){var _8k=E(_8b);if(!_8k[0]){return function(_8l){return new F(function(){return A(_8l,[new T(function(){return B(A(_7Y,[_Q]));})]);});};}else{return new F(function(){return _82(_8k[1]);});}}else{return new F(function(){return _82([0,_81-48|0]);});}}break;default:return E(_7S);}}};return [1,function(_8m){return new F(function(){return A(_7W,[_8m,_R,function(_8n){var _8o=E(_8n);return _8o[0]==0?[2]:B(A(_7V,[_8o]));}]);});}];},_8p=[0,10],_8q=[0,1],_8r=[0,2147483647],_8s=function(_8t,_8u){while(1){var _8v=E(_8t);if(!_8v[0]){var _8w=_8v[1],_8x=E(_8u);if(!_8x[0]){var _8y=_8x[1],_8z=addC(_8w,_8y);if(!E(_8z[2])){return [0,_8z[1]];}else{_8t=[1,I_fromInt(_8w)];_8u=[1,I_fromInt(_8y)];continue;}}else{_8t=[1,I_fromInt(_8w)];_8u=_8x;continue;}}else{var _8A=E(_8u);if(!_8A[0]){_8t=_8v;_8u=[1,I_fromInt(_8A[1])];continue;}else{return [1,I_add(_8v[1],_8A[1])];}}}},_8B=new T(function(){return B(_8s(_8r,_8q));}),_8C=function(_8D){var _8E=E(_8D);if(!_8E[0]){var _8F=E(_8E[1]);return _8F==(-2147483648)?E(_8B):[0, -_8F];}else{return [1,I_negate(_8E[1])];}},_8G=[0,10],_8H=[0,0],_8I=function(_8J){return [0,_8J];},_8K=function(_8L,_8M){while(1){var _8N=E(_8L);if(!_8N[0]){var _8O=_8N[1],_8P=E(_8M);if(!_8P[0]){var _8Q=_8P[1];if(!(imul(_8O,_8Q)|0)){return [0,imul(_8O,_8Q)|0];}else{_8L=[1,I_fromInt(_8O)];_8M=[1,I_fromInt(_8Q)];continue;}}else{_8L=[1,I_fromInt(_8O)];_8M=_8P;continue;}}else{var _8R=E(_8M);if(!_8R[0]){_8L=_8N;_8M=[1,I_fromInt(_8R[1])];continue;}else{return [1,I_mul(_8N[1],_8R[1])];}}}},_8S=function(_8T,_8U,_8V){while(1){var _8W=E(_8V);if(!_8W[0]){return E(_8U);}else{var _8X=B(_8s(B(_8K(_8U,_8T)),B(_8I(E(_8W[1])[1]))));_8V=_8W[2];_8U=_8X;continue;}}},_8Y=function(_8Z){var _90=new T(function(){return B(_6e(B(_6e([0,function(_91){if(E(E(_91)[1])==45){return new F(function(){return _7T(_8p,function(_92){return new F(function(){return A(_8Z,[[1,new T(function(){return B(_8C(B(_8S(_8G,_8H,_92))));})]]);});});});}else{return [2];}}],[0,function(_93){if(E(E(_93)[1])==43){return new F(function(){return _7T(_8p,function(_94){return new F(function(){return A(_8Z,[[1,new T(function(){return B(_8S(_8G,_8H,_94));})]]);});});});}else{return [2];}}])),new T(function(){return B(_7T(_8p,function(_95){return new F(function(){return A(_8Z,[[1,new T(function(){return B(_8S(_8G,_8H,_95));})]]);});}));})));});return new F(function(){return _6e([0,function(_96){return E(E(_96)[1])==101?E(_90):[2];}],[0,function(_97){return E(E(_97)[1])==69?E(_90):[2];}]);});},_98=function(_99){return new F(function(){return A(_99,[_46]);});},_9a=function(_9b){return new F(function(){return A(_9b,[_46]);});},_9c=function(_9d){return [0,function(_9e){return E(E(_9e)[1])==46?E(new T(function(){return B(_7T(_8p,function(_9f){return new F(function(){return A(_9d,[[1,_9f]]);});}));})):[2];}];},_9g=function(_9h){return new F(function(){return _7T(_8p,function(_9i){return new F(function(){return _7w(_9c,_98,function(_9j){return new F(function(){return _7w(_8Y,_9a,function(_9k){return new F(function(){return A(_9h,[[5,[1,_9i,_9j,_9k]]]);});});});});});});});},_9l=function(_9m,_9n,_9o){while(1){var _9p=E(_9o);if(!_9p[0]){return false;}else{if(!B(A(_6W,[_9m,_9n,_9p[1]]))){_9o=_9p[2];continue;}else{return true;}}}},_9q=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_9r=function(_9s){return new F(function(){return _9l(_6V,_9s,_9q);});},_9t=[0,8],_9u=[0,16],_9v=function(_9w){return [0,function(_9x){return E(E(_9x)[1])==48?E([0,function(_9y){switch(E(E(_9y)[1])){case 79:return E(new T(function(){return B(_7T(_9t,function(_9z){return new F(function(){return A(_9w,[[5,[0,_9t,_9z]]]);});}));}));case 88:return E(new T(function(){return B(_7T(_9u,function(_9A){return new F(function(){return A(_9w,[[5,[0,_9u,_9A]]]);});}));}));case 111:return E(new T(function(){return B(_7T(_9t,function(_9B){return new F(function(){return A(_9w,[[5,[0,_9t,_9B]]]);});}));}));case 120:return E(new T(function(){return B(_7T(_9u,function(_9C){return new F(function(){return A(_9w,[[5,[0,_9u,_9C]]]);});}));}));default:return [2];}}]):[2];}];},_9D=false,_9E=true,_9F=function(_9G){return [0,function(_9H){switch(E(E(_9H)[1])){case 79:return E(new T(function(){return B(A(_9G,[_9t]));}));case 88:return E(new T(function(){return B(A(_9G,[_9u]));}));case 111:return E(new T(function(){return B(A(_9G,[_9t]));}));case 120:return E(new T(function(){return B(A(_9G,[_9u]));}));default:return [2];}}];},_9I=function(_9J){return new F(function(){return A(_9J,[_8p]);});},_9K=function(_9L){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_i(9,_9L,_Q));}))));});},_9M=function(_9N){var _9O=E(_9N);return _9O[0]==0?E(_9O[1]):I_toInt(_9O[1]);},_9P=function(_9Q,_9R){var _9S=E(_9Q);if(!_9S[0]){var _9T=_9S[1],_9U=E(_9R);return _9U[0]==0?_9T<=_9U[1]:I_compareInt(_9U[1],_9T)>=0;}else{var _9V=_9S[1],_9W=E(_9R);return _9W[0]==0?I_compareInt(_9V,_9W[1])<=0:I_compare(_9V,_9W[1])<=0;}},_9X=function(_9Y){return [2];},_9Z=function(_a0){var _a1=E(_a0);if(!_a1[0]){return E(_9X);}else{var _a2=_a1[1],_a3=E(_a1[2]);return _a3[0]==0?E(_a2):function(_a4){return new F(function(){return _6e(B(A(_a2,[_a4])),new T(function(){return B(A(new T(function(){return B(_9Z(_a3));}),[_a4]));}));});};}},_a5=new T(function(){return B(unCStr("NUL"));}),_a6=function(_a7){return [2];},_a8=function(_a9){return new F(function(){return _a6(_a9);});},_aa=function(_ab,_ac){var _ad=function(_ae,_af){var _ag=E(_ae);if(!_ag[0]){return function(_ah){return new F(function(){return A(_ah,[_ab]);});};}else{var _ai=E(_af);return _ai[0]==0?E(_a6):E(_ag[1])[1]!=E(_ai[1])[1]?E(_a8):function(_aj){return [0,function(_ak){return E(new T(function(){return B(A(new T(function(){return B(_ad(_ag[2],_ai[2]));}),[_aj]));}));}];};}};return [1,function(_al){return new F(function(){return A(_ad,[_ab,_al,_ac]);});}];},_am=[0,0],_an=function(_ao){return new F(function(){return _aa(_a5,function(_ap){return E(new T(function(){return B(A(_ao,[_am]));}));});});},_aq=new T(function(){return B(unCStr("STX"));}),_ar=[0,2],_as=function(_at){return new F(function(){return _aa(_aq,function(_au){return E(new T(function(){return B(A(_at,[_ar]));}));});});},_av=new T(function(){return B(unCStr("ETX"));}),_aw=[0,3],_ax=function(_ay){return new F(function(){return _aa(_av,function(_az){return E(new T(function(){return B(A(_ay,[_aw]));}));});});},_aA=new T(function(){return B(unCStr("EOT"));}),_aB=[0,4],_aC=function(_aD){return new F(function(){return _aa(_aA,function(_aE){return E(new T(function(){return B(A(_aD,[_aB]));}));});});},_aF=new T(function(){return B(unCStr("ENQ"));}),_aG=[0,5],_aH=function(_aI){return new F(function(){return _aa(_aF,function(_aJ){return E(new T(function(){return B(A(_aI,[_aG]));}));});});},_aK=new T(function(){return B(unCStr("ACK"));}),_aL=[0,6],_aM=function(_aN){return new F(function(){return _aa(_aK,function(_aO){return E(new T(function(){return B(A(_aN,[_aL]));}));});});},_aP=new T(function(){return B(unCStr("BEL"));}),_aQ=[0,7],_aR=function(_aS){return new F(function(){return _aa(_aP,function(_aT){return E(new T(function(){return B(A(_aS,[_aQ]));}));});});},_aU=new T(function(){return B(unCStr("BS"));}),_aV=[0,8],_aW=function(_aX){return new F(function(){return _aa(_aU,function(_aY){return E(new T(function(){return B(A(_aX,[_aV]));}));});});},_aZ=new T(function(){return B(unCStr("HT"));}),_b0=[0,9],_b1=function(_b2){return new F(function(){return _aa(_aZ,function(_b3){return E(new T(function(){return B(A(_b2,[_b0]));}));});});},_b4=new T(function(){return B(unCStr("LF"));}),_b5=[0,10],_b6=function(_b7){return new F(function(){return _aa(_b4,function(_b8){return E(new T(function(){return B(A(_b7,[_b5]));}));});});},_b9=new T(function(){return B(unCStr("VT"));}),_ba=[0,11],_bb=function(_bc){return new F(function(){return _aa(_b9,function(_bd){return E(new T(function(){return B(A(_bc,[_ba]));}));});});},_be=new T(function(){return B(unCStr("FF"));}),_bf=[0,12],_bg=function(_bh){return new F(function(){return _aa(_be,function(_bi){return E(new T(function(){return B(A(_bh,[_bf]));}));});});},_bj=new T(function(){return B(unCStr("CR"));}),_bk=[0,13],_bl=function(_bm){return new F(function(){return _aa(_bj,function(_bn){return E(new T(function(){return B(A(_bm,[_bk]));}));});});},_bo=new T(function(){return B(unCStr("SI"));}),_bp=[0,15],_bq=function(_br){return new F(function(){return _aa(_bo,function(_bs){return E(new T(function(){return B(A(_br,[_bp]));}));});});},_bt=new T(function(){return B(unCStr("DLE"));}),_bu=[0,16],_bv=function(_bw){return new F(function(){return _aa(_bt,function(_bx){return E(new T(function(){return B(A(_bw,[_bu]));}));});});},_by=new T(function(){return B(unCStr("DC1"));}),_bz=[0,17],_bA=function(_bB){return new F(function(){return _aa(_by,function(_bC){return E(new T(function(){return B(A(_bB,[_bz]));}));});});},_bD=new T(function(){return B(unCStr("DC2"));}),_bE=[0,18],_bF=function(_bG){return new F(function(){return _aa(_bD,function(_bH){return E(new T(function(){return B(A(_bG,[_bE]));}));});});},_bI=new T(function(){return B(unCStr("DC3"));}),_bJ=[0,19],_bK=function(_bL){return new F(function(){return _aa(_bI,function(_bM){return E(new T(function(){return B(A(_bL,[_bJ]));}));});});},_bN=new T(function(){return B(unCStr("DC4"));}),_bO=[0,20],_bP=function(_bQ){return new F(function(){return _aa(_bN,function(_bR){return E(new T(function(){return B(A(_bQ,[_bO]));}));});});},_bS=new T(function(){return B(unCStr("NAK"));}),_bT=[0,21],_bU=function(_bV){return new F(function(){return _aa(_bS,function(_bW){return E(new T(function(){return B(A(_bV,[_bT]));}));});});},_bX=new T(function(){return B(unCStr("SYN"));}),_bY=[0,22],_bZ=function(_c0){return new F(function(){return _aa(_bX,function(_c1){return E(new T(function(){return B(A(_c0,[_bY]));}));});});},_c2=new T(function(){return B(unCStr("ETB"));}),_c3=[0,23],_c4=function(_c5){return new F(function(){return _aa(_c2,function(_c6){return E(new T(function(){return B(A(_c5,[_c3]));}));});});},_c7=new T(function(){return B(unCStr("CAN"));}),_c8=[0,24],_c9=function(_ca){return new F(function(){return _aa(_c7,function(_cb){return E(new T(function(){return B(A(_ca,[_c8]));}));});});},_cc=new T(function(){return B(unCStr("EM"));}),_cd=[0,25],_ce=function(_cf){return new F(function(){return _aa(_cc,function(_cg){return E(new T(function(){return B(A(_cf,[_cd]));}));});});},_ch=new T(function(){return B(unCStr("SUB"));}),_ci=[0,26],_cj=function(_ck){return new F(function(){return _aa(_ch,function(_cl){return E(new T(function(){return B(A(_ck,[_ci]));}));});});},_cm=new T(function(){return B(unCStr("ESC"));}),_cn=[0,27],_co=function(_cp){return new F(function(){return _aa(_cm,function(_cq){return E(new T(function(){return B(A(_cp,[_cn]));}));});});},_cr=new T(function(){return B(unCStr("FS"));}),_cs=[0,28],_ct=function(_cu){return new F(function(){return _aa(_cr,function(_cv){return E(new T(function(){return B(A(_cu,[_cs]));}));});});},_cw=new T(function(){return B(unCStr("GS"));}),_cx=[0,29],_cy=function(_cz){return new F(function(){return _aa(_cw,function(_cA){return E(new T(function(){return B(A(_cz,[_cx]));}));});});},_cB=new T(function(){return B(unCStr("RS"));}),_cC=[0,30],_cD=function(_cE){return new F(function(){return _aa(_cB,function(_cF){return E(new T(function(){return B(A(_cE,[_cC]));}));});});},_cG=new T(function(){return B(unCStr("US"));}),_cH=[0,31],_cI=function(_cJ){return new F(function(){return _aa(_cG,function(_cK){return E(new T(function(){return B(A(_cJ,[_cH]));}));});});},_cL=new T(function(){return B(unCStr("SP"));}),_cM=[0,32],_cN=function(_cO){return new F(function(){return _aa(_cL,function(_cP){return E(new T(function(){return B(A(_cO,[_cM]));}));});});},_cQ=new T(function(){return B(unCStr("DEL"));}),_cR=[0,127],_cS=function(_cT){return new F(function(){return _aa(_cQ,function(_cU){return E(new T(function(){return B(A(_cT,[_cR]));}));});});},_cV=[1,_cS,_Q],_cW=[1,_cN,_cV],_cX=[1,_cI,_cW],_cY=[1,_cD,_cX],_cZ=[1,_cy,_cY],_d0=[1,_ct,_cZ],_d1=[1,_co,_d0],_d2=[1,_cj,_d1],_d3=[1,_ce,_d2],_d4=[1,_c9,_d3],_d5=[1,_c4,_d4],_d6=[1,_bZ,_d5],_d7=[1,_bU,_d6],_d8=[1,_bP,_d7],_d9=[1,_bK,_d8],_da=[1,_bF,_d9],_db=[1,_bA,_da],_dc=[1,_bv,_db],_dd=[1,_bq,_dc],_de=[1,_bl,_dd],_df=[1,_bg,_de],_dg=[1,_bb,_df],_dh=[1,_b6,_dg],_di=[1,_b1,_dh],_dj=[1,_aW,_di],_dk=[1,_aR,_dj],_dl=[1,_aM,_dk],_dm=[1,_aH,_dl],_dn=[1,_aC,_dm],_do=[1,_ax,_dn],_dp=[1,_as,_do],_dq=[1,_an,_dp],_dr=new T(function(){return B(unCStr("SOH"));}),_ds=[0,1],_dt=function(_du){return new F(function(){return _aa(_dr,function(_dv){return E(new T(function(){return B(A(_du,[_ds]));}));});});},_dw=new T(function(){return B(unCStr("SO"));}),_dx=[0,14],_dy=function(_dz){return new F(function(){return _aa(_dw,function(_dA){return E(new T(function(){return B(A(_dz,[_dx]));}));});});},_dB=function(_dC){return new F(function(){return _7w(_dt,_dy,_dC);});},_dD=[1,_dB,_dq],_dE=new T(function(){return B(_9Z(_dD));}),_dF=[0,1114111],_dG=[0,34],_dH=[0,_dG,_9E],_dI=[0,39],_dJ=[0,_dI,_9E],_dK=[0,92],_dL=[0,_dK,_9E],_dM=[0,_aQ,_9E],_dN=[0,_aV,_9E],_dO=[0,_bf,_9E],_dP=[0,_b5,_9E],_dQ=[0,_bk,_9E],_dR=[0,_b0,_9E],_dS=[0,_ba,_9E],_dT=[0,_am,_9E],_dU=[0,_ds,_9E],_dV=[0,_ar,_9E],_dW=[0,_aw,_9E],_dX=[0,_aB,_9E],_dY=[0,_aG,_9E],_dZ=[0,_aL,_9E],_e0=[0,_aQ,_9E],_e1=[0,_aV,_9E],_e2=[0,_b0,_9E],_e3=[0,_b5,_9E],_e4=[0,_ba,_9E],_e5=[0,_bf,_9E],_e6=[0,_bk,_9E],_e7=[0,_dx,_9E],_e8=[0,_bp,_9E],_e9=[0,_bu,_9E],_ea=[0,_bz,_9E],_eb=[0,_bE,_9E],_ec=[0,_bJ,_9E],_ed=[0,_bO,_9E],_ee=[0,_bT,_9E],_ef=[0,_bY,_9E],_eg=[0,_c3,_9E],_eh=[0,_c8,_9E],_ei=[0,_cd,_9E],_ej=[0,_ci,_9E],_ek=[0,_cn,_9E],_el=[0,_cs,_9E],_em=[0,_cx,_9E],_en=[0,_cC,_9E],_eo=[0,_cH,_9E],_ep=function(_eq){return new F(function(){return _6e([0,function(_er){switch(E(E(_er)[1])){case 34:return E(new T(function(){return B(A(_eq,[_dH]));}));case 39:return E(new T(function(){return B(A(_eq,[_dJ]));}));case 92:return E(new T(function(){return B(A(_eq,[_dL]));}));case 97:return E(new T(function(){return B(A(_eq,[_dM]));}));case 98:return E(new T(function(){return B(A(_eq,[_dN]));}));case 102:return E(new T(function(){return B(A(_eq,[_dO]));}));case 110:return E(new T(function(){return B(A(_eq,[_dP]));}));case 114:return E(new T(function(){return B(A(_eq,[_dQ]));}));case 116:return E(new T(function(){return B(A(_eq,[_dR]));}));case 118:return E(new T(function(){return B(A(_eq,[_dS]));}));default:return [2];}}],new T(function(){return B(_6e(B(_7w(_9F,_9I,function(_es){return new F(function(){return _7T(_es,function(_et){var _eu=B(_8S(new T(function(){return B(_8I(E(_es)[1]));}),_8H,_et));return !B(_9P(_eu,_dF))?[2]:B(A(_eq,[[0,new T(function(){var _ev=B(_9M(_eu));if(_ev>>>0>1114111){var _ew=B(_9K(_ev));}else{var _ew=[0,_ev];}var _ex=_ew,_ey=_ex;return _ey;}),_9E]]));});});})),new T(function(){return B(_6e([0,function(_ez){return E(E(_ez)[1])==94?E([0,function(_eA){switch(E(E(_eA)[1])){case 64:return E(new T(function(){return B(A(_eq,[_dT]));}));case 65:return E(new T(function(){return B(A(_eq,[_dU]));}));case 66:return E(new T(function(){return B(A(_eq,[_dV]));}));case 67:return E(new T(function(){return B(A(_eq,[_dW]));}));case 68:return E(new T(function(){return B(A(_eq,[_dX]));}));case 69:return E(new T(function(){return B(A(_eq,[_dY]));}));case 70:return E(new T(function(){return B(A(_eq,[_dZ]));}));case 71:return E(new T(function(){return B(A(_eq,[_e0]));}));case 72:return E(new T(function(){return B(A(_eq,[_e1]));}));case 73:return E(new T(function(){return B(A(_eq,[_e2]));}));case 74:return E(new T(function(){return B(A(_eq,[_e3]));}));case 75:return E(new T(function(){return B(A(_eq,[_e4]));}));case 76:return E(new T(function(){return B(A(_eq,[_e5]));}));case 77:return E(new T(function(){return B(A(_eq,[_e6]));}));case 78:return E(new T(function(){return B(A(_eq,[_e7]));}));case 79:return E(new T(function(){return B(A(_eq,[_e8]));}));case 80:return E(new T(function(){return B(A(_eq,[_e9]));}));case 81:return E(new T(function(){return B(A(_eq,[_ea]));}));case 82:return E(new T(function(){return B(A(_eq,[_eb]));}));case 83:return E(new T(function(){return B(A(_eq,[_ec]));}));case 84:return E(new T(function(){return B(A(_eq,[_ed]));}));case 85:return E(new T(function(){return B(A(_eq,[_ee]));}));case 86:return E(new T(function(){return B(A(_eq,[_ef]));}));case 87:return E(new T(function(){return B(A(_eq,[_eg]));}));case 88:return E(new T(function(){return B(A(_eq,[_eh]));}));case 89:return E(new T(function(){return B(A(_eq,[_ei]));}));case 90:return E(new T(function(){return B(A(_eq,[_ej]));}));case 91:return E(new T(function(){return B(A(_eq,[_ek]));}));case 92:return E(new T(function(){return B(A(_eq,[_el]));}));case 93:return E(new T(function(){return B(A(_eq,[_em]));}));case 94:return E(new T(function(){return B(A(_eq,[_en]));}));case 95:return E(new T(function(){return B(A(_eq,[_eo]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_dE,[function(_eB){return new F(function(){return A(_eq,[[0,_eB,_9E]]);});}]));})));})));}));});},_eC=function(_eD){return new F(function(){return A(_eD,[_J]);});},_eE=function(_eF){var _eG=E(_eF);if(!_eG[0]){return E(_eC);}else{var _eH=_eG[2],_eI=E(E(_eG[1])[1]);switch(_eI){case 9:return function(_eJ){return [0,function(_eK){return E(new T(function(){return B(A(new T(function(){return B(_eE(_eH));}),[_eJ]));}));}];};case 10:return function(_eL){return [0,function(_eM){return E(new T(function(){return B(A(new T(function(){return B(_eE(_eH));}),[_eL]));}));}];};case 11:return function(_eN){return [0,function(_eO){return E(new T(function(){return B(A(new T(function(){return B(_eE(_eH));}),[_eN]));}));}];};case 12:return function(_eP){return [0,function(_eQ){return E(new T(function(){return B(A(new T(function(){return B(_eE(_eH));}),[_eP]));}));}];};case 13:return function(_eR){return [0,function(_eS){return E(new T(function(){return B(A(new T(function(){return B(_eE(_eH));}),[_eR]));}));}];};case 32:return function(_eT){return [0,function(_eU){return E(new T(function(){return B(A(new T(function(){return B(_eE(_eH));}),[_eT]));}));}];};case 160:return function(_eV){return [0,function(_eW){return E(new T(function(){return B(A(new T(function(){return B(_eE(_eH));}),[_eV]));}));}];};default:var _eX=u_iswspace(_eI),_eY=_eX;return E(_eY)==0?E(_eC):function(_eZ){return [0,function(_f0){return E(new T(function(){return B(A(new T(function(){return B(_eE(_eH));}),[_eZ]));}));}];};}}},_f1=function(_f2){var _f3=new T(function(){return B(_f1(_f2));}),_f4=[1,function(_f5){return new F(function(){return A(_eE,[_f5,function(_f6){return E([0,function(_f7){return E(E(_f7)[1])==92?E(_f3):[2];}]);}]);});}];return new F(function(){return _6e([0,function(_f8){return E(E(_f8)[1])==92?E([0,function(_f9){var _fa=E(E(_f9)[1]);switch(_fa){case 9:return E(_f4);case 10:return E(_f4);case 11:return E(_f4);case 12:return E(_f4);case 13:return E(_f4);case 32:return E(_f4);case 38:return E(_f3);case 160:return E(_f4);default:var _fb=u_iswspace(_fa),_fc=_fb;return E(_fc)==0?[2]:E(_f4);}}]):[2];}],[0,function(_fd){var _fe=E(_fd);return E(_fe[1])==92?E(new T(function(){return B(_ep(_f2));})):B(A(_f2,[[0,_fe,_9D]]));}]);});},_ff=function(_fg,_fh){return new F(function(){return _f1(function(_fi){var _fj=E(_fi),_fk=E(_fj[1]);if(E(_fk[1])==34){if(!E(_fj[2])){return E(new T(function(){return B(A(_fh,[[1,new T(function(){return B(A(_fg,[_Q]));})]]));}));}else{return new F(function(){return _ff(function(_fl){return new F(function(){return A(_fg,[[1,_fk,_fl]]);});},_fh);});}}else{return new F(function(){return _ff(function(_fm){return new F(function(){return A(_fg,[[1,_fk,_fm]]);});},_fh);});}});});},_fn=new T(function(){return B(unCStr("_\'"));}),_fo=function(_fp){var _fq=u_iswalnum(_fp),_fr=_fq;return E(_fr)==0?B(_9l(_6V,[0,_fp],_fn)):true;},_fs=function(_ft){return new F(function(){return _fo(E(_ft)[1]);});},_fu=new T(function(){return B(unCStr(",;()[]{}`"));}),_fv=function(_fw){return new F(function(){return A(_fw,[_Q]);});},_fx=function(_fy,_fz){var _fA=function(_fB){var _fC=E(_fB);if(!_fC[0]){return E(_fv);}else{var _fD=_fC[1];return !B(A(_fy,[_fD]))?E(_fv):function(_fE){return [0,function(_fF){return E(new T(function(){return B(A(new T(function(){return B(_fA(_fC[2]));}),[function(_fG){return new F(function(){return A(_fE,[[1,_fD,_fG]]);});}]));}));}];};}};return [1,function(_fH){return new F(function(){return A(_fA,[_fH,_fz]);});}];},_fI=new T(function(){return B(unCStr(".."));}),_fJ=new T(function(){return B(unCStr("::"));}),_fK=new T(function(){return B(unCStr("->"));}),_fL=[0,64],_fM=[1,_fL,_Q],_fN=[0,126],_fO=[1,_fN,_Q],_fP=new T(function(){return B(unCStr("=>"));}),_fQ=[1,_fP,_Q],_fR=[1,_fO,_fQ],_fS=[1,_fM,_fR],_fT=[1,_fK,_fS],_fU=new T(function(){return B(unCStr("<-"));}),_fV=[1,_fU,_fT],_fW=[0,124],_fX=[1,_fW,_Q],_fY=[1,_fX,_fV],_fZ=[1,_dK,_Q],_g0=[1,_fZ,_fY],_g1=[0,61],_g2=[1,_g1,_Q],_g3=[1,_g2,_g0],_g4=[1,_fJ,_g3],_g5=[1,_fI,_g4],_g6=function(_g7){return new F(function(){return _6e([1,function(_g8){return E(_g8)[0]==0?E(new T(function(){return B(A(_g7,[_7Q]));})):[2];}],new T(function(){return B(_6e([0,function(_g9){return E(E(_g9)[1])==39?E([0,function(_ga){var _gb=E(_ga);switch(E(_gb[1])){case 39:return [2];case 92:return E(new T(function(){return B(_ep(function(_gc){var _gd=E(_gc);return new F(function(){return (function(_ge,_gf){var _gg=new T(function(){return B(A(_g7,[[0,_ge]]));});return !E(_gf)?E(E(_ge)[1])==39?[2]:[0,function(_gh){return E(E(_gh)[1])==39?E(_gg):[2];}]:[0,function(_gi){return E(E(_gi)[1])==39?E(_gg):[2];}];})(_gd[1],_gd[2]);});}));}));default:return [0,function(_gj){return E(E(_gj)[1])==39?E(new T(function(){return B(A(_g7,[[0,_gb]]));})):[2];}];}}]):[2];}],new T(function(){return B(_6e([0,function(_gk){return E(E(_gk)[1])==34?E(new T(function(){return B(_ff(_R,_g7));})):[2];}],new T(function(){return B(_6e([0,function(_gl){return !B(_9l(_6V,_gl,_fu))?[2]:B(A(_g7,[[2,[1,_gl,_Q]]]));}],new T(function(){return B(_6e([0,function(_gm){if(!B(_9l(_6V,_gm,_9q))){return [2];}else{return new F(function(){return _fx(_9r,function(_gn){var _go=[1,_gm,_gn];return !B(_9l(_7c,_go,_g5))?B(A(_g7,[[4,_go]])):B(A(_g7,[[2,_go]]));});});}}],new T(function(){return B(_6e([0,function(_gp){var _gq=E(_gp),_gr=_gq[1],_gs=u_iswalpha(_gr),_gt=_gs;if(!E(_gt)){if(E(_gr)==95){return new F(function(){return _fx(_fs,function(_gu){return new F(function(){return A(_g7,[[3,[1,_gq,_gu]]]);});});});}else{return [2];}}else{return new F(function(){return _fx(_fs,function(_gv){return new F(function(){return A(_g7,[[3,[1,_gq,_gv]]]);});});});}}],new T(function(){return B(_7w(_9v,_9g,_g7));})));})));})));})));})));}));});},_gw=function(_gx){return [1,function(_gy){return new F(function(){return A(_eE,[_gy,function(_gz){return E(new T(function(){return B(_g6(_gx));}));}]);});}];},_gA=[0,0],_gB=function(_gC,_gD){return new F(function(){return _gw(function(_gE){var _gF=E(_gE);if(_gF[0]==2){var _gG=E(_gF[1]);return _gG[0]==0?[2]:E(E(_gG[1])[1])==40?E(_gG[2])[0]==0?E(new T(function(){return B(A(_gC,[_gA,function(_gH){return new F(function(){return _gw(function(_gI){var _gJ=E(_gI);if(_gJ[0]==2){var _gK=E(_gJ[1]);return _gK[0]==0?[2]:E(E(_gK[1])[1])==41?E(_gK[2])[0]==0?E(new T(function(){return B(A(_gD,[_gH]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_gL=function(_gM,_gN,_gO){var _gP=function(_gQ,_gR){return new F(function(){return _6e(B(_gw(function(_gS){var _gT=E(_gS);if(_gT[0]==4){var _gU=E(_gT[1]);if(!_gU[0]){return new F(function(){return A(_gM,[_gT,_gQ,_gR]);});}else{return E(E(_gU[1])[1])==45?E(_gU[2])[0]==0?E([1,function(_gV){return new F(function(){return A(_eE,[_gV,function(_gW){return E(new T(function(){return B(_g6(function(_gX){return new F(function(){return A(_gM,[_gX,_gQ,function(_gY){return new F(function(){return A(_gR,[new T(function(){return [0, -E(_gY)[1]];})]);});}]);});}));}));}]);});}]):B(A(_gM,[_gT,_gQ,_gR])):B(A(_gM,[_gT,_gQ,_gR]));}}else{return new F(function(){return A(_gM,[_gT,_gQ,_gR]);});}})),new T(function(){return B(_gB(_gP,_gR));}));});};return new F(function(){return _gP(_gN,_gO);});},_gZ=function(_h0,_h1){return [2];},_h2=function(_h3,_h4){return new F(function(){return _gZ(_h3,_h4);});},_h5=function(_h6){var _h7=E(_h6);return _h7[0]==0?[1,new T(function(){return B(_8S(new T(function(){return B(_8I(E(_h7[1])[1]));}),_8H,_h7[2]));})]:E(_h7[2])[0]==0?E(_h7[3])[0]==0?[1,new T(function(){return B(_8S(_8G,_8H,_h7[1]));})]:[0]:[0];},_h8=function(_h9){var _ha=E(_h9);if(_ha[0]==5){var _hb=B(_h5(_ha[1]));return _hb[0]==0?E(_gZ):function(_hc,_hd){return new F(function(){return A(_hd,[new T(function(){return [0,B(_9M(_hb[1]))];})]);});};}else{return E(_h2);}},_he=function(_hf,_hg){while(1){var _hh=E(_hf);if(!_hh[0]){return E(_hg)[0]==0?true:false;}else{var _hi=E(_hg);if(!_hi[0]){return false;}else{if(E(_hh[1])[1]!=E(_hi[1])[1]){return false;}else{_hf=_hh[2];_hg=_hi[2];continue;}}}}},_hj=new T(function(){return B(unCStr("onSideIndex"));}),_hk=new T(function(){return B(unCStr("LeftSidePlacement"));}),_hl=new T(function(){return B(unCStr("RightSidePlacement"));}),_hm=function(_hn,_ho){var _hp=new T(function(){if(_hn>11){var _hq=[2];}else{var _hq=[1,function(_hr){return new F(function(){return A(_eE,[_hr,function(_hs){return E(new T(function(){return B(_g6(function(_ht){var _hu=E(_ht);return _hu[0]==3?!B(_he(_hu[1],_hl))?[2]:E([1,function(_hv){return new F(function(){return A(_eE,[_hv,function(_hw){return E(new T(function(){return B(_g6(function(_hx){var _hy=E(_hx);if(_hy[0]==2){var _hz=E(_hy[1]);return _hz[0]==0?[2]:E(E(_hz[1])[1])==123?E(_hz[2])[0]==0?E([1,function(_hA){return new F(function(){return A(_eE,[_hA,function(_hB){return E(new T(function(){return B(_g6(function(_hC){var _hD=E(_hC);return _hD[0]==3?!B(_he(_hD[1],_hj))?[2]:E([1,function(_hE){return new F(function(){return A(_eE,[_hE,function(_hF){return E(new T(function(){return B(_g6(function(_hG){var _hH=E(_hG);if(_hH[0]==2){var _hI=E(_hH[1]);return _hI[0]==0?[2]:E(E(_hI[1])[1])==61?E(_hI[2])[0]==0?E(new T(function(){return B(_gL(_h8,_gA,function(_hJ){return new F(function(){return _gw(function(_hK){var _hL=E(_hK);if(_hL[0]==2){var _hM=E(_hL[1]);return _hM[0]==0?[2]:E(E(_hM[1])[1])==125?E(_hM[2])[0]==0?E(new T(function(){return B(A(_ho,[[3,_hJ]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}];}return _hq;});if(_hn>11){return new F(function(){return _6e(_7o,_hp);});}else{return new F(function(){return _6e(B(_gw(function(_hN){var _hO=E(_hN);return _hO[0]==3?!B(_he(_hO[1],_hk))?[2]:E([1,function(_hP){return new F(function(){return A(_eE,[_hP,function(_hQ){return E(new T(function(){return B(_g6(function(_hR){var _hS=E(_hR);if(_hS[0]==2){var _hT=E(_hS[1]);return _hT[0]==0?[2]:E(E(_hT[1])[1])==123?E(_hT[2])[0]==0?E([1,function(_hU){return new F(function(){return A(_eE,[_hU,function(_hV){return E(new T(function(){return B(_g6(function(_hW){var _hX=E(_hW);return _hX[0]==3?!B(_he(_hX[1],_hj))?[2]:E([1,function(_hY){return new F(function(){return A(_eE,[_hY,function(_hZ){return E(new T(function(){return B(_g6(function(_i0){var _i1=E(_i0);if(_i1[0]==2){var _i2=E(_i1[1]);return _i2[0]==0?[2]:E(E(_i2[1])[1])==61?E(_i2[2])[0]==0?E(new T(function(){return B(_gL(_h8,_gA,function(_i3){return new F(function(){return _gw(function(_i4){var _i5=E(_i4);if(_i5[0]==2){var _i6=E(_i5[1]);return _i6[0]==0?[2]:E(E(_i6[1])[1])==125?E(_i6[2])[0]==0?E(new T(function(){return B(A(_ho,[[2,_i3]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),_hp);});}},_i7=new T(function(){return B(unCStr("onBarIndex"));}),_i8=new T(function(){return B(unCStr("BarPlacement"));}),_i9=function(_ia,_ib){if(_ia>11){return new F(function(){return _6e(_7o,new T(function(){return B(_hm(_ia,_ib));}));});}else{return new F(function(){return _6e(B(_gw(function(_ic){var _id=E(_ic);return _id[0]==3?!B(_he(_id[1],_i8))?[2]:E([1,function(_ie){return new F(function(){return A(_eE,[_ie,function(_if){return E(new T(function(){return B(_g6(function(_ig){var _ih=E(_ig);if(_ih[0]==2){var _ii=E(_ih[1]);return _ii[0]==0?[2]:E(E(_ii[1])[1])==123?E(_ii[2])[0]==0?E([1,function(_ij){return new F(function(){return A(_eE,[_ij,function(_ik){return E(new T(function(){return B(_g6(function(_il){var _im=E(_il);return _im[0]==3?!B(_he(_im[1],_i7))?[2]:E([1,function(_in){return new F(function(){return A(_eE,[_in,function(_io){return E(new T(function(){return B(_g6(function(_ip){var _iq=E(_ip);if(_iq[0]==2){var _ir=E(_iq[1]);return _ir[0]==0?[2]:E(E(_ir[1])[1])==61?E(_ir[2])[0]==0?E(new T(function(){return B(_gL(_h8,_gA,function(_is){return new F(function(){return _gw(function(_it){var _iu=E(_it);if(_iu[0]==2){var _iv=E(_iu[1]);return _iv[0]==0?[2]:E(E(_iv[1])[1])==125?E(_iv[2])[0]==0?E(new T(function(){return B(A(_ib,[[1,_is]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_hm(_ia,_ib));}));});}},_iw=new T(function(){return B(unCStr("onPointIndex"));}),_ix=new T(function(){return B(unCStr("pointIndex"));}),_iy=new T(function(){return B(unCStr("PointPlacement"));}),_iz=function(_iA,_iB){if(_iA>11){return new F(function(){return _6e(_7o,new T(function(){return B(_i9(_iA,_iB));}));});}else{return new F(function(){return _6e(B(_gw(function(_iC){var _iD=E(_iC);return _iD[0]==3?!B(_he(_iD[1],_iy))?[2]:E([1,function(_iE){return new F(function(){return A(_eE,[_iE,function(_iF){return E(new T(function(){return B(_g6(function(_iG){var _iH=E(_iG);if(_iH[0]==2){var _iI=E(_iH[1]);return _iI[0]==0?[2]:E(E(_iI[1])[1])==123?E(_iI[2])[0]==0?E([1,function(_iJ){return new F(function(){return A(_eE,[_iJ,function(_iK){return E(new T(function(){return B(_g6(function(_iL){var _iM=E(_iL);return _iM[0]==3?!B(_he(_iM[1],_ix))?[2]:E([1,function(_iN){return new F(function(){return A(_eE,[_iN,function(_iO){return E(new T(function(){return B(_g6(function(_iP){var _iQ=E(_iP);if(_iQ[0]==2){var _iR=E(_iQ[1]);return _iR[0]==0?[2]:E(E(_iR[1])[1])==61?E(_iR[2])[0]==0?E(new T(function(){return B(_gL(_h8,_gA,function(_iS){return new F(function(){return _gw(function(_iT){var _iU=E(_iT);if(_iU[0]==2){var _iV=E(_iU[1]);return _iV[0]==0?[2]:E(E(_iV[1])[1])==44?E(_iV[2])[0]==0?E([1,function(_iW){return new F(function(){return A(_eE,[_iW,function(_iX){return E(new T(function(){return B(_g6(function(_iY){var _iZ=E(_iY);return _iZ[0]==3?!B(_he(_iZ[1],_iw))?[2]:E([1,function(_j0){return new F(function(){return A(_eE,[_j0,function(_j1){return E(new T(function(){return B(_g6(function(_j2){var _j3=E(_j2);if(_j3[0]==2){var _j4=E(_j3[1]);return _j4[0]==0?[2]:E(E(_j4[1])[1])==61?E(_j4[2])[0]==0?E(new T(function(){return B(_gL(_h8,_gA,function(_j5){return new F(function(){return _gw(function(_j6){var _j7=E(_j6);if(_j7[0]==2){var _j8=E(_j7[1]);return _j8[0]==0?[2]:E(E(_j8[1])[1])==125?E(_j8[2])[0]==0?E(new T(function(){return B(A(_iB,[[0,_iS,_j5]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_i9(_iA,_iB));}));});}},_j9=function(_ja,_jb){return new F(function(){return _iz(E(_ja)[1],_jb);});},_jc=function(_jd,_je){var _jf=function(_jg){return function(_jh){return new F(function(){return _6e(B(A(new T(function(){return B(A(_jd,[_jg]));}),[_jh])),new T(function(){return B(_gB(_jf,_jh));}));});};};return new F(function(){return _jf(_je);});},_ji=function(_jj){return [1,function(_jk){return new F(function(){return A(_eE,[_jk,function(_jl){return E([3,_jj,_7o]);}]);});}];},_jm=new T(function(){return B(A(_jc,[_j9,_gA,_ji]));}),_jn=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_jo=new T(function(){return B(err(_jn));}),_jp=function(_jq,_jr){return new F(function(){return A(_jr,[_50]);});},_js=[0,_4,_jp],_jt=[1,_js,_Q],_ju=function(_jv,_jw){return new F(function(){return A(_jw,[_4Z]);});},_jx=[0,_3,_ju],_jy=[1,_jx,_jt],_jz=function(_jA,_jB,_jC){var _jD=E(_jA);if(!_jD[0]){return [2];}else{var _jE=E(_jD[1]),_jF=_jE[1],_jG=new T(function(){return B(A(_jE[2],[_jB,_jC]));});return new F(function(){return _6e(B(_gw(function(_jH){var _jI=E(_jH);switch(_jI[0]){case 3:return !B(_he(_jF,_jI[1]))?[2]:E(_jG);case 4:return !B(_he(_jF,_jI[1]))?[2]:E(_jG);default:return [2];}})),new T(function(){return B(_jz(_jD[2],_jB,_jC));}));});}},_jJ=function(_jK,_jL){return new F(function(){return _jz(_jy,_jK,_jL);});},_jM=new T(function(){return B(A(_jc,[_jJ,_gA,_ji]));}),_jN=new T(function(){return B(err(_jn));}),_jO=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_jP=new T(function(){return B(err(_jO));}),_jQ=new T(function(){return B(err(_jO));}),_jR=function(_jS,_jT,_jU){return _jU<=_jT?[1,[0,_jS],new T(function(){var _jV=_jT-_jS|0,_jW=function(_jX){return _jX>=(_jU-_jV|0)?[1,[0,_jX],new T(function(){return B(_jW(_jX+_jV|0));})]:[1,[0,_jX],_Q];};return B(_jW(_jT));})]:_jU<=_jS?[1,[0,_jS],_Q]:[0];},_jY=function(_jZ,_k0,_k1){return _k1>=_k0?[1,[0,_jZ],new T(function(){var _k2=_k0-_jZ|0,_k3=function(_k4){return _k4<=(_k1-_k2|0)?[1,[0,_k4],new T(function(){return B(_k3(_k4+_k2|0));})]:[1,[0,_k4],_Q];};return B(_k3(_k0));})]:_k1>=_jZ?[1,[0,_jZ],_Q]:[0];},_k5=function(_k6,_k7){return _k7<_k6?B(_jR(_k6,_k7,-2147483648)):B(_jY(_k6,_k7,2147483647));},_k8=new T(function(){return B(_k5(135,150));}),_k9=function(_ka,_kb){var _kc=E(_ka);if(!_kc){return [0];}else{var _kd=E(_kb);return _kd[0]==0?[0]:[1,_kd[1],new T(function(){return B(_k9(_kc-1|0,_kd[2]));})];}},_ke=new T(function(){return B(_k9(6,_k8));}),_kf=function(_kg,_kh){var _ki=E(_kg);if(!_ki[0]){return E(_ke);}else{var _kj=_ki[1];return _kh>1?[1,_kj,new T(function(){return B(_kf(_ki[2],_kh-1|0));})]:[1,_kj,_ke];}},_kk=new T(function(){return B(_k5(25,40));}),_kl=new T(function(){return B(_kf(_kk,6));}),_km=function(_kn){while(1){var _ko=(function(_kp){var _kq=E(_kp);if(!_kq[0]){return [0];}else{var _kr=_kq[2],_ks=E(_kq[1]);if(!E(_ks[2])[0]){return [1,_ks[1],new T(function(){return B(_km(_kr));})];}else{_kn=_kr;return null;}}})(_kn);if(_ko!=null){return _ko;}}},_kt=function(_ku,_kv){var _kw=E(_kv);if(!_kw[0]){return [0,_Q,_Q];}else{var _kx=_kw[1];if(!B(A(_ku,[_kx]))){var _ky=new T(function(){var _kz=B(_kt(_ku,_kw[2]));return [0,_kz[1],_kz[2]];});return [0,[1,_kx,new T(function(){return E(E(_ky)[1]);})],new T(function(){return E(E(_ky)[2]);})];}else{return [0,_Q,_kw];}}},_kA=function(_kB,_kC){while(1){var _kD=E(_kC);if(!_kD[0]){return [0];}else{if(!B(A(_kB,[_kD[1]]))){return E(_kD);}else{_kC=_kD[2];continue;}}}},_kE=function(_kF){var _kG=E(_kF);switch(_kG){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _kH=u_iswspace(_kG),_kI=_kH;return E(_kI)==0?false:true;}},_kJ=function(_kK){return new F(function(){return _kE(E(_kK)[1]);});},_kL=function(_kM){var _kN=B(_kA(_kJ,_kM));if(!_kN[0]){return [0];}else{var _kO=new T(function(){var _kP=B(_kt(_kJ,_kN));return [0,_kP[1],_kP[2]];});return [1,new T(function(){return E(E(_kO)[1]);}),new T(function(){return B(_kL(E(_kO)[2]));})];}},_kQ=function(_kR,_){var _kS=jsFind(toJSStr(E(_5V))),_kT=_kS,_kU=function(_){var _kV=setDropCheckerCallback_ffi(function(_kW,_kX,_kY){var _kZ=E(_kR),_l0=_kZ[1],_l1=_kZ[6],_l2=new T(function(){return B(_kL(B(_5P(_kW))));}),_l3=B(_km(B(_64(_jm,new T(function(){return B(_10(_5R,B(_55(_l2,2))));})))));if(!_l3[0]){return E(_jQ);}else{if(!E(_l3[2])[0]){var _l4=E(_l3[1]);if(!_l4[0]){var _l5=B(_5w(function(_l6){var _l7=E(_l6)[1]-E(_kX)[1];return _l7<0? -_l7<7:_l7<7;},_kl));if(!_l5[0]){return function(_7P){return new F(function(){return _5g(_l4,_l4,_l1,_7P);});};}else{var _l8=_l5[1],_l9=function(_la,_lb,_){var _lc=E(_l4[1]),_ld=_lc[1];if(_la<=_ld){return new F(function(){return _5g(_l4,_l4,_l1,_);});}else{var _le=B(_km(B(_64(_jM,new T(function(){return B(_55(_l2,1));})))));if(!_le[0]){return E(_jP);}else{var _lf=_le[1];if(!E(_le[2])[0]){if(_la>=0){var _lg=B(_55(_l0,_la)),_lh=function(_){var _li=B(_5g(_l4,[0,_lb,new T(function(){if(_la>=0){var _lj=E(B(_55(_l0,_la))[2]);}else{var _lj=E(_52);}return _lj;})],_l1,_)),_lk=_li;if(_ld>=0){var _ll=new T(function(){return B(_5I(function(_lm,_ln,_lo){return [1,new T(function(){var _lp=E(_lm)[1];return _lp!=_ld?_lp!=_la?E(_ln):[0,new T(function(){if(_ld>=0){var _lq=E(B(_55(_l0,_ld))[1]);}else{var _lq=E(_52);}return _lq;}),new T(function(){return [0,E(E(_ln)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_ln)[1]);}),new T(function(){return [0,E(E(_ln)[2])[1]-1|0];})];}),_lo];},_Q,_4p,_l0));}),_lr=B((function(_ls,_){while(1){var _lt=(function(_lu,_){var _lv=E(_lu);if(!_lv[0]){return _J;}else{var _lw=_lv[1],_lx=B(_5g([0,_lc,_lw],[0,_lc,new T(function(){return [0,E(_lw)[1]-1|0];})],_l1,_)),_ly=_lx;_ls=_lv[2];return null;}})(_ls,_);if(_lt!=null){return _lt;}}})(B(_5q(1,B(_4j(E(_l4[2])[1],E(B(_55(_ll,_ld))[2])[1])))),_)),_lz=_lr;return new F(function(){return _kQ([0,_ll,_kZ[2],_kZ[3],_kZ[4],_kZ[5],_l1,_kZ[7]],_);});}else{return E(_52);}},_lA=function(_){return E(_lg[2])[1]>=2?B(_5g(_l4,_l4,_l1,_)):B(_lh(_));};return E(_lg[1])==0?E(_lf)==0?B(_lh(_)):B(_lA(_)):E(_lf)==0?B(_lA(_)):B(_lh(_));}else{return E(_52);}}else{return E(_jN);}}}};if(E(_kY)[1]<=E(_5U)[1]){var _lB=E(_l8);return function(_7P){return new F(function(){return _l9(_lB[1],_lB,_7P);});};}else{var _lC=23-E(_l8)[1]|0;return function(_7P){return new F(function(){return _l9(_lC,[0,_lC],_7P);});};}}}else{return function(_7P){return new F(function(){return _5g(_l4,_l4,_l1,_7P);});};}}else{return E(_jo);}}});return _J;},_lD=E(_kT);if(!_lD[0]){return new F(function(){return _kU(_);});}else{var _lE=jsSetCB(E(_lD[1])[1],E(_5v)[1],E(_62)[1]),_lF=_lE;return new F(function(){return _kU(_);});}},_lG=function(_lH,_lI){while(1){var _lJ=E(_lH);if(!_lJ[0]){return E(_lI);}else{_lH=_lJ[2];var _lK=[1,_lJ[1],_lI];_lI=_lK;continue;}}},_lL=[0,2],_lM=[0,0],_lN=[1,_lM,_Q],_lO=[1,_lM,_lN],_lP=[1,_lM,_lO],_lQ=[1,_lM,_lP],_lR=[1,_lM,_lQ],_lS=[0,5],_lT=[1,_lS,_lR],_lU=[1,_lM,_lT],_lV=[0,3],_lW=[1,_lV,_lU],_lX=[1,_lM,_lW],_lY=[1,_lM,_lX],_lZ=[1,_lM,_lY],_m0=[1,_lM,_lZ],_m1=[1,_lS,_m0],_m2=[1,_lM,_m1],_m3=[1,_lM,_m2],_m4=[1,_lM,_m3],_m5=[1,_lM,_m4],_m6=[1,_lM,_m5],_m7=[1,_lM,_m6],_m8=[1,_lM,_m7],_m9=[1,_lM,_m8],_ma=[1,_lM,_m9],_mb=[1,_lM,_ma],_mc=[1,_lL,_mb],_md=function(_me){var _mf=E(_me);return _mf[0]==0?[0]:[1,[0,_50,_mf[1]],new T(function(){return B(_md(_mf[2]));})];},_mg=new T(function(){return B(_md(_mc));}),_mh=new T(function(){return B(_lG(_mg,_Q));}),_mi=new T(function(){return B(_2x("main.hs:(252,20)-(253,55)|function whiteOrBlack"));}),_mj=function(_mk,_ml){var _mm=E(_mk);if(!_mm[0]){return [0];}else{var _mn=E(_ml);return _mn[0]==0?[0]:[1,new T(function(){var _mo=E(_mn[1]);if(!E(_mo[1])){var _mp=E(_mi);}else{if(!E(E(_mo[2])[1])){var _mq=E(_mm[1]),_mr=E(_mq[1])==0?E(_mq):[0,_4Z,_mq[2]];}else{var _mr=E(_mo);}var _ms=_mr,_mp=_ms;}var _mt=_mp;return _mt;}),new T(function(){return B(_mj(_mm[2],_mn[2]));})];}},_mu=new T(function(){return B(_mj(_mh,_mg));}),_mv=function(_mw,_mx){while(1){var _my=E(_mw);if(!_my[0]){return E(_mx);}else{_mw=_my[2];var _mz=_mx+E(_my[1])[1]|0;_mx=_mz;continue;}}},_mA=new T(function(){return [0,B(_mv(_mc,0))];}),_mB=[0,_mu,_mA,_mA,_lM,_lM,_50,_50],_mC=function(_){var _mD=E(_mA)[1],_mE=B(_4t(_50,_50,_mD,_)),_mF=_mE,_mG=B(_4t(_4Z,_50,_mD,_)),_mH=_mG;return new F(function(){return _kQ(_mB,_);});},_mI=function(_){var _mJ=jsFind(toJSStr(E(_2))),_mK=_mJ,_mL=E(_mK);if(!_mL[0]){return new F(function(){return _mC(_);});}else{var _mM=jsSet(E(_mL[1])[1],toJSStr(E(_1)),toJSStr(E(_0)));return new F(function(){return _mC(_);});}},_mN=function(_){return new F(function(){return _mI(_);});};
var hasteMain = function() {B(A(_mN, [0]));};window.onload = hasteMain;