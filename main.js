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

var _0=[0],_1=function(_2,_3){while(1){var _4=E(_2);if(!_4[0]){return E(_3);}else{_2=_4[2];var _5=[1,_4[1],_3];_3=_5;continue;}}},_6=[0,2],_7=[0,0],_8=[1,_7,_0],_9=[1,_7,_8],_a=[1,_7,_9],_b=[1,_7,_a],_c=[1,_7,_b],_d=[0,5],_e=[1,_d,_c],_f=[1,_7,_e],_g=[0,3],_h=[1,_g,_f],_i=[1,_7,_h],_j=[1,_7,_i],_k=[1,_7,_j],_l=[1,_7,_k],_m=[1,_d,_l],_n=[1,_7,_m],_o=[1,_7,_n],_p=[1,_7,_o],_q=[1,_7,_p],_r=[1,_7,_q],_s=[1,_7,_r],_t=[1,_7,_s],_u=[1,_7,_t],_v=[1,_7,_u],_w=[1,_7,_v],_x=[1,_6,_w],_y=1,_z=function(_A){var _B=E(_A);return _B[0]==0?[0]:[1,[0,_y,_B[1]],new T(function(){return B(_z(_B[2]));})];},_C=new T(function(){return B(_z(_x));}),_D=new T(function(){return B(_1(_C,_0));}),_E=0,_F=new T(function(){return B(unCStr("Control.Exception.Base"));}),_G=new T(function(){return B(unCStr("base"));}),_H=new T(function(){return B(unCStr("PatternMatchFail"));}),_I=new T(function(){var _J=hs_wordToWord64(18445595),_K=_J,_L=hs_wordToWord64(52003073),_M=_L;return [0,_K,_M,[0,_K,_M,_G,_F,_H],_0];}),_N=function(_O){return E(_I);},_P=function(_Q){return E(E(_Q)[1]);},_R=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_S=new T(function(){return B(err(_R));}),_T=function(_U,_V,_W){var _X=new T(function(){var _Y=B(A(_U,[_W])),_Z=B(A(_V,[new T(function(){var _10=E(_X);return _10[0]==0?E(_S):E(_10[1]);})])),_11=hs_eqWord64(_Y[1],_Z[1]),_12=_11;if(!E(_12)){var _13=[0];}else{var _14=hs_eqWord64(_Y[2],_Z[2]),_15=_14,_13=E(_15)==0?[0]:[1,_W];}var _16=_13,_17=_16;return _17;});return E(_X);},_18=function(_19){var _1a=E(_19);return new F(function(){return _T(B(_P(_1a[1])),_N,_1a[2]);});},_1b=function(_1c){return E(E(_1c)[1]);},_1d=function(_1e,_1f){var _1g=E(_1e);return _1g[0]==0?E(_1f):[1,_1g[1],new T(function(){return B(_1d(_1g[2],_1f));})];},_1h=function(_1i,_1j){return new F(function(){return _1d(E(_1i)[1],_1j);});},_1k=[0,44],_1l=[0,93],_1m=[0,91],_1n=function(_1o,_1p,_1q){var _1r=E(_1p);return _1r[0]==0?B(unAppCStr("[]",_1q)):[1,_1m,new T(function(){return B(A(_1o,[_1r[1],new T(function(){var _1s=function(_1t){var _1u=E(_1t);return _1u[0]==0?E([1,_1l,_1q]):[1,_1k,new T(function(){return B(A(_1o,[_1u[1],new T(function(){return B(_1s(_1u[2]));})]));})];};return B(_1s(_1r[2]));})]));})];},_1v=function(_1w,_1x){return new F(function(){return _1n(_1h,_1w,_1x);});},_1y=function(_1z,_1A,_1B){return new F(function(){return _1d(E(_1A)[1],_1B);});},_1C=[0,_1y,_1b,_1v],_1D=new T(function(){return [0,_N,_1C,_1E,_18];}),_1E=function(_1F){return [0,_1D,_1F];},_1G=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_1H=function(_1I,_1J){return new F(function(){return die(new T(function(){return B(A(_1J,[_1I]));}));});},_1K=function(_1L,_1M){var _1N=E(_1M);if(!_1N[0]){return [0,_0,_0];}else{var _1O=_1N[1];if(!B(A(_1L,[_1O]))){return [0,_0,_1N];}else{var _1P=new T(function(){var _1Q=B(_1K(_1L,_1N[2]));return [0,_1Q[1],_1Q[2]];});return [0,[1,_1O,new T(function(){return E(E(_1P)[1]);})],new T(function(){return E(E(_1P)[2]);})];}}},_1R=[0,32],_1S=[0,10],_1T=[1,_1S,_0],_1U=function(_1V){return E(E(_1V)[1])==124?false:true;},_1W=function(_1X,_1Y){var _1Z=B(_1K(_1U,B(unCStr(_1X)))),_20=_1Z[1],_21=function(_22,_23){return new F(function(){return _1d(_22,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_1d(_1Y,new T(function(){return B(_1d(_23,_1T));})));})));}));});},_24=E(_1Z[2]);if(!_24[0]){return new F(function(){return _21(_20,_0);});}else{return E(E(_24[1])[1])==124?B(_21(_20,[1,_1R,_24[2]])):B(_21(_20,_0));}},_25=function(_26){return new F(function(){return _1H([0,new T(function(){return B(_1W(_26,_1G));})],_1E);});},_27=new T(function(){return B(_25("main.hs:(228,20)-(229,55)|function whiteOrBlack"));}),_28=function(_29,_2a){var _2b=E(_29);if(!_2b[0]){return [0];}else{var _2c=E(_2a);return _2c[0]==0?[0]:[1,new T(function(){var _2d=E(_2c[1]);if(!E(_2d[1])){var _2e=E(_27);}else{if(!E(E(_2d[2])[1])){var _2f=E(_2b[1]),_2g=E(_2f[1])==0?E(_2f):[0,_E,_2f[2]];}else{var _2g=E(_2d);}var _2h=_2g,_2e=_2h;}var _2i=_2e;return _2i;}),new T(function(){return B(_28(_2b[2],_2c[2]));})];}},_2j=new T(function(){return B(_28(_D,_C));}),_2k=[0,_2j,_7,_7,_7,_7,_y,_y],_2l=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_2m=new T(function(){return B(err(_2l));}),_2n=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_2o=new T(function(){return B(err(_2n));}),_2p=function(_2q,_2r){while(1){var _2s=E(_2q);if(!_2s[0]){return E(_2o);}else{var _2t=E(_2r);if(!_2t){return E(_2s[1]);}else{_2q=_2s[2];_2r=_2t-1|0;continue;}}}},_2u=0,_2v=new T(function(){return B(unCStr("Black"));}),_2w=new T(function(){return B(unCStr("White"));}),_2x=new T(function(){return B(unCStr("pointIndex = "));}),_2y=new T(function(){return B(unCStr("onSideIndex = "));}),_2z=new T(function(){return B(unCStr("SidePlacement {"));}),_2A=new T(function(){return B(unCStr("onBarIndex = "));}),_2B=new T(function(){return B(unCStr("BarPlacement {"));}),_2C=new T(function(){return B(unCStr("PointPlacement {"));}),_2D=[0,125],_2E=new T(function(){return B(unCStr("onPointIndex = "));}),_2F=new T(function(){return B(unCStr(", "));}),_2G=function(_2H,_2I){var _2J=jsShowI(_2H),_2K=_2J;return new F(function(){return _1d(fromJSStr(_2K),_2I);});},_2L=[0,41],_2M=[0,40],_2N=function(_2O,_2P,_2Q){return _2P>=0?B(_2G(_2P,_2Q)):_2O<=6?B(_2G(_2P,_2Q)):[1,_2M,new T(function(){var _2R=jsShowI(_2P),_2S=_2R;return B(_1d(fromJSStr(_2S),[1,_2L,_2Q]));})];},_2T=function(_2U,_2V,_2W){var _2X=E(_2V);switch(_2X[0]){case 0:var _2Y=function(_2Z){return new F(function(){return _1d(_2x,new T(function(){return B(_2N(0,E(_2X[1])[1],new T(function(){return B(_1d(_2F,new T(function(){return B(_1d(_2E,new T(function(){return B(_2N(0,E(_2X[2])[1],[1,_2D,_2Z]));})));})));})));}));});};return _2U<11?B(_1d(_2C,new T(function(){return B(_2Y(_2W));}))):[1,_2M,new T(function(){return B(_1d(_2C,new T(function(){return B(_2Y([1,_2L,_2W]));})));})];case 1:var _30=function(_31){return new F(function(){return _1d(_2B,new T(function(){return B(_1d(_2A,new T(function(){return B(_2N(0,E(_2X[1])[1],[1,_2D,_31]));})));}));});};return _2U<11?B(_30(_2W)):[1,_2M,new T(function(){return B(_30([1,_2L,_2W]));})];default:var _32=function(_33){return new F(function(){return _1d(_2z,new T(function(){return B(_1d(_2y,new T(function(){return B(_2N(0,E(_2X[1])[1],[1,_2D,_33]));})));}));});};return _2U<11?B(_32(_2W)):[1,_2M,new T(function(){return B(_32([1,_2L,_2W]));})];}},_34=function(_35,_36,_37,_38){return new F(function(){return A(_35,[new T(function(){return function(_){var _39=jsSetAttr(E(_36)[1],toJSStr(E(_37)),toJSStr(E(_38)));return _2u;};})]);});},_3a=function(_3b){return E(_3b);},_3c=[0,95],_3d=function(_3e){var _3f=E(_3e);return E(_3f[1])==32?E(_3c):E(_3f);},_3g=new T(function(){return B(unCStr("class"));}),_3h=new T(function(){return B(unCStr("draggable "));}),_3i=[0,32],_3j=function(_3k,_3l){var _3m=E(_3l);return _3m[0]==0?[0]:[1,new T(function(){return B(A(_3k,[_3m[1]]));}),new T(function(){return B(_3j(_3k,_3m[2]));})];},_3n=function(_3o,_3p,_3q,_3r){return new F(function(){return _34(_3a,_3o,_3g,new T(function(){var _3s=new T(function(){var _3t=new T(function(){return B(_3j(_3d,B(_2T(0,_3q,_0))));});return E(_3r)==0?B(_1d(_2v,[1,_3i,_3t])):B(_1d(_2w,[1,_3i,_3t]));});return E(_3p)==0?E(_3r)==0?B(_1d(_3h,_3s)):E(_3s):E(_3r)==0?E(_3s):B(_1d(_3h,_3s));}));});},_3u=new T(function(){return B(_25("main.hs:(81,1)-(102,14)|function checkerPosition"));}),_3v=function(_3w){var _3x=E(_3w);if(!_3x[0]){var _3y=_3x[1],_3z=_3x[2];return [0,new T(function(){var _3A=E(_3y)[1];if(_3A>=12){var _3B=23-_3A|0;if(_3B>=6){var _3C=[0,25+(20+(imul(_3B,15)|0)|0)|0];}else{var _3C=[0,25+(imul(_3B,15)|0)|0];}var _3D=_3C,_3E=_3D;}else{if(_3A>=6){var _3F=[0,25+(20+(imul(_3A,15)|0)|0)|0];}else{var _3F=[0,25+(imul(_3A,15)|0)|0];}var _3E=_3F;}var _3G=_3E;return _3G;}),new T(function(){if(E(_3y)[1]>=12){var _3H=[0,203+(imul(imul(imul(-1,E(_3z)[1])|0,2)|0,6)|0)|0];}else{var _3H=[0,7+(imul(imul(E(_3z)[1],2)|0,6)|0)|0];}var _3I=_3H;return _3I;})];}else{return E(_3u);}},_3J=new T(function(){return B(unCStr(": empty list"));}),_3K=new T(function(){return B(unCStr("Prelude."));}),_3L=function(_3M){return new F(function(){return err(B(_1d(_3K,new T(function(){return B(_1d(_3M,_3J));}))));});},_3N=new T(function(){return B(unCStr("head"));}),_3O=new T(function(){return B(_3L(_3N));}),_3P=function(_3Q,_3R,_3S,_){var _3T=jsElemsByClassName(toJSStr(B(_3j(_3d,B(_2T(0,_3Q,_0)))))),_3U=_3T,_3V=E(_3U);if(!_3V[0]){return E(_3O);}else{var _3W=E(_3V[1]),_3X=B(_3v(_3R)),_3Y=animateCircle_ffi(_3W[1],E(_3X[1])[1],E(_3X[2])[1],300);return new F(function(){return A(_3n,[_3W,_3S,_3R,_3S,_]);});}},_3Z=function(_40,_41){while(1){var _42=E(_40);if(!_42){return E(_41);}else{var _43=E(_41);if(!_43[0]){return [0];}else{_40=_42-1|0;_41=_43[2];continue;}}}},_44=function(_45,_46){if(_45<=_46){var _47=function(_48){return [1,[0,_48],new T(function(){if(_48!=_46){var _49=B(_47(_48+1|0));}else{var _49=[0];}return _49;})];};return new F(function(){return _47(_45);});}else{return [0];}},_4a=function(_4b,_4c){var _4d=function(_4e,_4f){while(1){var _4g=(function(_4h,_4i){var _4j=E(_4i);if(!_4j[0]){return [0];}else{var _4k=_4j[2];if(!B(A(_4b,[_4j[1]]))){var _4l=_4h+1|0;_4f=_4k;_4e=_4l;return null;}else{return [1,[0,_4h],new T(function(){return B(_4d(_4h+1|0,_4k));})];}}})(_4e,_4f);if(_4g!=null){return _4g;}}};return new F(function(){return _4d(0,_4c);});},_4m=function(_4n,_4o,_4p,_4q){var _4r=E(_4p);if(!_4r[0]){return E(_4o);}else{var _4s=E(_4q);if(!_4s[0]){return E(_4o);}else{return new F(function(){return A(_4n,[_4r[1],_4s[1],new T(function(){return B(_4m(_4n,_4o,_4r[2],_4s[2]));})]);});}}},_4t=function(_4u){return new F(function(){return fromJSStr(E(_4u)[1]);});},_4v=function(_4w){var _4x=E(_4w);return E(_4x[1])==95?E(_3i):E(_4x);},_4y=function(_4z,_4A){if(_4z<=0){if(_4z>=0){return new F(function(){return quot(_4z,_4A);});}else{if(_4A<=0){return new F(function(){return quot(_4z,_4A);});}else{return quot(_4z+1|0,_4A)-1|0;}}}else{if(_4A>=0){if(_4z>=0){return new F(function(){return quot(_4z,_4A);});}else{if(_4A<=0){return new F(function(){return quot(_4z,_4A);});}else{return quot(_4z+1|0,_4A)-1|0;}}}else{return quot(_4z-1|0,_4A)-1|0;}}},_4B=new T(function(){return [0,B(_4y(210,2))];}),_4C=new T(function(){return B(_44(0,2147483647));}),_4D=new T(function(){return B(_25("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_4E=function(_4F,_4G){while(1){var _4H=(function(_4I,_4J){var _4K=E(_4I);switch(_4K[0]){case 0:var _4L=E(_4J);if(!_4L[0]){return [0];}else{_4F=B(A(_4K[1],[_4L[1]]));_4G=_4L[2];return null;}break;case 1:var _4M=B(A(_4K[1],[_4J])),_4N=_4J;_4F=_4M;_4G=_4N;return null;case 2:return [0];case 3:return [1,[0,_4K[1],_4J],new T(function(){return B(_4E(_4K[2],_4J));})];default:return E(_4K[1]);}})(_4F,_4G);if(_4H!=null){return _4H;}}},_4O=function(_4P,_4Q){var _4R=new T(function(){var _4S=E(_4Q);if(_4S[0]==3){var _4T=[3,_4S[1],new T(function(){return B(_4O(_4P,_4S[2]));})];}else{var _4U=E(_4P);if(_4U[0]==2){var _4V=E(_4S);}else{var _4W=E(_4S);if(_4W[0]==2){var _4X=E(_4U);}else{var _4Y=new T(function(){var _4Z=E(_4W);if(_4Z[0]==4){var _50=[1,function(_51){return [4,new T(function(){return B(_1d(B(_4E(_4U,_51)),_4Z[1]));})];}];}else{var _52=E(_4U);if(_52[0]==1){var _53=_52[1],_54=E(_4Z);if(!_54[0]){var _55=[1,function(_56){return new F(function(){return _4O(B(A(_53,[_56])),_54);});}];}else{var _55=[1,function(_57){return new F(function(){return _4O(B(A(_53,[_57])),new T(function(){return B(A(_54[1],[_57]));}));});}];}var _58=_55;}else{var _59=E(_4Z);if(!_59[0]){var _5a=E(_4D);}else{var _5a=[1,function(_5b){return new F(function(){return _4O(_52,new T(function(){return B(A(_59[1],[_5b]));}));});}];}var _58=_5a;}var _50=_58;}return _50;}),_5c=E(_4U);switch(_5c[0]){case 1:var _5d=E(_4W);if(_5d[0]==4){var _5e=[1,function(_5f){return [4,new T(function(){return B(_1d(B(_4E(B(A(_5c[1],[_5f])),_5f)),_5d[1]));})];}];}else{var _5e=E(_4Y);}var _5g=_5e;break;case 4:var _5h=_5c[1],_5i=E(_4W);switch(_5i[0]){case 0:var _5j=[1,function(_5k){return [4,new T(function(){return B(_1d(_5h,new T(function(){return B(_4E(_5i,_5k));})));})];}];break;case 1:var _5j=[1,function(_5l){return [4,new T(function(){return B(_1d(_5h,new T(function(){return B(_4E(B(A(_5i[1],[_5l])),_5l));})));})];}];break;default:var _5j=[4,new T(function(){return B(_1d(_5h,_5i[1]));})];}var _5g=_5j;break;default:var _5g=E(_4Y);}var _4X=_5g;}var _4V=_4X;}var _4T=_4V;}return _4T;}),_5m=E(_4P);switch(_5m[0]){case 0:var _5n=E(_4Q);return _5n[0]==0?[0,function(_5o){return new F(function(){return _4O(B(A(_5m[1],[_5o])),new T(function(){return B(A(_5n[1],[_5o]));}));});}]:E(_4R);case 3:return [3,_5m[1],new T(function(){return B(_4O(_5m[2],_4Q));})];default:return E(_4R);}},_5p=function(_5q,_5r){return E(_5q)[1]!=E(_5r)[1];},_5s=function(_5t,_5u){return E(_5t)[1]==E(_5u)[1];},_5v=[0,_5s,_5p],_5w=function(_5x){return E(E(_5x)[1]);},_5y=function(_5z,_5A,_5B){while(1){var _5C=E(_5A);if(!_5C[0]){return E(_5B)[0]==0?true:false;}else{var _5D=E(_5B);if(!_5D[0]){return false;}else{if(!B(A(_5w,[_5z,_5C[1],_5D[1]]))){return false;}else{_5A=_5C[2];_5B=_5D[2];continue;}}}}},_5E=function(_5F,_5G,_5H){return !B(_5y(_5F,_5G,_5H))?true:false;},_5I=function(_5J){return [0,function(_5K,_5L){return new F(function(){return _5y(_5J,_5K,_5L);});},function(_5K,_5L){return new F(function(){return _5E(_5J,_5K,_5L);});}];},_5M=new T(function(){return B(_5I(_5v));}),_5N=function(_5O,_5P){var _5Q=E(_5O);switch(_5Q[0]){case 0:return [0,function(_5R){return new F(function(){return _5N(B(A(_5Q[1],[_5R])),_5P);});}];case 1:return [1,function(_5S){return new F(function(){return _5N(B(A(_5Q[1],[_5S])),_5P);});}];case 2:return [2];case 3:return new F(function(){return _4O(B(A(_5P,[_5Q[1]])),new T(function(){return B(_5N(_5Q[2],_5P));}));});break;default:var _5T=function(_5U){var _5V=E(_5U);if(!_5V[0]){return [0];}else{var _5W=E(_5V[1]);return new F(function(){return _1d(B(_4E(B(A(_5P,[_5W[1]])),_5W[2])),new T(function(){return B(_5T(_5V[2]));}));});}},_5X=B(_5T(_5Q[1]));return _5X[0]==0?[2]:[4,_5X];}},_5Y=[2],_5Z=function(_60){return [3,_60,_5Y];},_61=function(_62,_63){var _64=E(_62);if(!_64){return new F(function(){return A(_63,[_2u]);});}else{return [0,function(_65){return E(new T(function(){return B(_61(_64-1|0,_63));}));}];}},_66=function(_67,_68,_69){return [1,function(_6a){return new F(function(){return A(function(_6b,_6c,_6d){while(1){var _6e=(function(_6f,_6g,_6h){var _6i=E(_6f);switch(_6i[0]){case 0:var _6j=E(_6g);if(!_6j[0]){return E(_68);}else{_6b=B(A(_6i[1],[_6j[1]]));_6c=_6j[2];var _6k=_6h+1|0;_6d=_6k;return null;}break;case 1:var _6l=B(A(_6i[1],[_6g])),_6m=_6g,_6k=_6h;_6b=_6l;_6c=_6m;_6d=_6k;return null;case 2:return E(_68);case 3:return function(_6n){return new F(function(){return _61(_6h,function(_6o){return E(new T(function(){return B(_5N(_6i,_6n));}));});});};default:return function(_6p){return new F(function(){return _5N(_6i,_6p);});};}})(_6b,_6c,_6d);if(_6e!=null){return _6e;}}},[new T(function(){return B(A(_67,[_5Z]));}),_6a,0,_69]);});}];},_6q=[6],_6r=new T(function(){return B(unCStr("valDig: Bad base"));}),_6s=new T(function(){return B(err(_6r));}),_6t=function(_6u,_6v){var _6w=function(_6x,_6y){var _6z=E(_6x);if(!_6z[0]){return function(_6A){return new F(function(){return A(_6A,[new T(function(){return B(A(_6y,[_0]));})]);});};}else{var _6B=E(_6z[1])[1],_6C=function(_6D){return function(_6E){return [0,function(_6F){return E(new T(function(){return B(A(new T(function(){return B(_6w(_6z[2],function(_6G){return new F(function(){return A(_6y,[[1,_6D,_6G]]);});}));}),[_6E]));}));}];};};switch(E(E(_6u)[1])){case 8:if(48>_6B){return function(_6H){return new F(function(){return A(_6H,[new T(function(){return B(A(_6y,[_0]));})]);});};}else{if(_6B>55){return function(_6I){return new F(function(){return A(_6I,[new T(function(){return B(A(_6y,[_0]));})]);});};}else{return new F(function(){return _6C([0,_6B-48|0]);});}}break;case 10:if(48>_6B){return function(_6J){return new F(function(){return A(_6J,[new T(function(){return B(A(_6y,[_0]));})]);});};}else{if(_6B>57){return function(_6K){return new F(function(){return A(_6K,[new T(function(){return B(A(_6y,[_0]));})]);});};}else{return new F(function(){return _6C([0,_6B-48|0]);});}}break;case 16:var _6L=new T(function(){if(97>_6B){if(65>_6B){var _6M=[0];}else{if(_6B>70){var _6N=[0];}else{var _6N=[1,[0,(_6B-65|0)+10|0]];}var _6M=_6N;}var _6O=_6M;}else{if(_6B>102){if(65>_6B){var _6P=[0];}else{if(_6B>70){var _6Q=[0];}else{var _6Q=[1,[0,(_6B-65|0)+10|0]];}var _6P=_6Q;}var _6R=_6P;}else{var _6R=[1,[0,(_6B-97|0)+10|0]];}var _6O=_6R;}return _6O;});if(48>_6B){var _6S=E(_6L);if(!_6S[0]){return function(_6T){return new F(function(){return A(_6T,[new T(function(){return B(A(_6y,[_0]));})]);});};}else{return new F(function(){return _6C(_6S[1]);});}}else{if(_6B>57){var _6U=E(_6L);if(!_6U[0]){return function(_6V){return new F(function(){return A(_6V,[new T(function(){return B(A(_6y,[_0]));})]);});};}else{return new F(function(){return _6C(_6U[1]);});}}else{return new F(function(){return _6C([0,_6B-48|0]);});}}break;default:return E(_6s);}}};return [1,function(_6W){return new F(function(){return A(_6w,[_6W,_3a,function(_6X){var _6Y=E(_6X);return _6Y[0]==0?[2]:B(A(_6v,[_6Y]));}]);});}];},_6Z=[0,10],_70=[0,1],_71=[0,2147483647],_72=function(_73,_74){while(1){var _75=E(_73);if(!_75[0]){var _76=_75[1],_77=E(_74);if(!_77[0]){var _78=_77[1],_79=addC(_76,_78);if(!E(_79[2])){return [0,_79[1]];}else{_73=[1,I_fromInt(_76)];_74=[1,I_fromInt(_78)];continue;}}else{_73=[1,I_fromInt(_76)];_74=_77;continue;}}else{var _7a=E(_74);if(!_7a[0]){_73=_75;_74=[1,I_fromInt(_7a[1])];continue;}else{return [1,I_add(_75[1],_7a[1])];}}}},_7b=new T(function(){return B(_72(_71,_70));}),_7c=function(_7d){var _7e=E(_7d);if(!_7e[0]){var _7f=E(_7e[1]);return _7f==(-2147483648)?E(_7b):[0, -_7f];}else{return [1,I_negate(_7e[1])];}},_7g=[0,10],_7h=[0,0],_7i=function(_7j){return [0,_7j];},_7k=function(_7l,_7m){while(1){var _7n=E(_7l);if(!_7n[0]){var _7o=_7n[1],_7p=E(_7m);if(!_7p[0]){var _7q=_7p[1];if(!(imul(_7o,_7q)|0)){return [0,imul(_7o,_7q)|0];}else{_7l=[1,I_fromInt(_7o)];_7m=[1,I_fromInt(_7q)];continue;}}else{_7l=[1,I_fromInt(_7o)];_7m=_7p;continue;}}else{var _7r=E(_7m);if(!_7r[0]){_7l=_7n;_7m=[1,I_fromInt(_7r[1])];continue;}else{return [1,I_mul(_7n[1],_7r[1])];}}}},_7s=function(_7t,_7u,_7v){while(1){var _7w=E(_7v);if(!_7w[0]){return E(_7u);}else{var _7x=B(_72(B(_7k(_7u,_7t)),B(_7i(E(_7w[1])[1]))));_7v=_7w[2];_7u=_7x;continue;}}},_7y=function(_7z){var _7A=new T(function(){return B(_4O(B(_4O([0,function(_7B){if(E(E(_7B)[1])==45){return new F(function(){return _6t(_6Z,function(_7C){return new F(function(){return A(_7z,[[1,new T(function(){return B(_7c(B(_7s(_7g,_7h,_7C))));})]]);});});});}else{return [2];}}],[0,function(_7D){if(E(E(_7D)[1])==43){return new F(function(){return _6t(_6Z,function(_7E){return new F(function(){return A(_7z,[[1,new T(function(){return B(_7s(_7g,_7h,_7E));})]]);});});});}else{return [2];}}])),new T(function(){return B(_6t(_6Z,function(_7F){return new F(function(){return A(_7z,[[1,new T(function(){return B(_7s(_7g,_7h,_7F));})]]);});}));})));});return new F(function(){return _4O([0,function(_7G){return E(E(_7G)[1])==101?E(_7A):[2];}],[0,function(_7H){return E(E(_7H)[1])==69?E(_7A):[2];}]);});},_7I=[0],_7J=function(_7K){return new F(function(){return A(_7K,[_7I]);});},_7L=function(_7M){return new F(function(){return A(_7M,[_7I]);});},_7N=function(_7O){return [0,function(_7P){return E(E(_7P)[1])==46?E(new T(function(){return B(_6t(_6Z,function(_7Q){return new F(function(){return A(_7O,[[1,_7Q]]);});}));})):[2];}];},_7R=function(_7S){return new F(function(){return _6t(_6Z,function(_7T){return new F(function(){return _66(_7N,_7J,function(_7U){return new F(function(){return _66(_7y,_7L,function(_7V){return new F(function(){return A(_7S,[[5,[1,_7T,_7U,_7V]]]);});});});});});});});},_7W=function(_7X,_7Y,_7Z){while(1){var _80=E(_7Z);if(!_80[0]){return false;}else{if(!B(A(_5w,[_7X,_7Y,_80[1]]))){_7Z=_80[2];continue;}else{return true;}}}},_81=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_82=function(_83){return new F(function(){return _7W(_5v,_83,_81);});},_84=[0,8],_85=[0,16],_86=function(_87){return [0,function(_88){return E(E(_88)[1])==48?E([0,function(_89){switch(E(E(_89)[1])){case 79:return E(new T(function(){return B(_6t(_84,function(_8a){return new F(function(){return A(_87,[[5,[0,_84,_8a]]]);});}));}));case 88:return E(new T(function(){return B(_6t(_85,function(_8b){return new F(function(){return A(_87,[[5,[0,_85,_8b]]]);});}));}));case 111:return E(new T(function(){return B(_6t(_84,function(_8c){return new F(function(){return A(_87,[[5,[0,_84,_8c]]]);});}));}));case 120:return E(new T(function(){return B(_6t(_85,function(_8d){return new F(function(){return A(_87,[[5,[0,_85,_8d]]]);});}));}));default:return [2];}}]):[2];}];},_8e=false,_8f=true,_8g=function(_8h){return [0,function(_8i){switch(E(E(_8i)[1])){case 79:return E(new T(function(){return B(A(_8h,[_84]));}));case 88:return E(new T(function(){return B(A(_8h,[_85]));}));case 111:return E(new T(function(){return B(A(_8h,[_84]));}));case 120:return E(new T(function(){return B(A(_8h,[_85]));}));default:return [2];}}];},_8j=function(_8k){return new F(function(){return A(_8k,[_6Z]);});},_8l=function(_8m){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_2N(9,_8m,_0));}))));});},_8n=function(_8o){var _8p=E(_8o);return _8p[0]==0?E(_8p[1]):I_toInt(_8p[1]);},_8q=function(_8r,_8s){var _8t=E(_8r);if(!_8t[0]){var _8u=_8t[1],_8v=E(_8s);return _8v[0]==0?_8u<=_8v[1]:I_compareInt(_8v[1],_8u)>=0;}else{var _8w=_8t[1],_8x=E(_8s);return _8x[0]==0?I_compareInt(_8w,_8x[1])<=0:I_compare(_8w,_8x[1])<=0;}},_8y=function(_8z){return [2];},_8A=function(_8B){var _8C=E(_8B);if(!_8C[0]){return E(_8y);}else{var _8D=_8C[1],_8E=E(_8C[2]);return _8E[0]==0?E(_8D):function(_8F){return new F(function(){return _4O(B(A(_8D,[_8F])),new T(function(){return B(A(new T(function(){return B(_8A(_8E));}),[_8F]));}));});};}},_8G=new T(function(){return B(unCStr("NUL"));}),_8H=function(_8I){return [2];},_8J=function(_8K){return new F(function(){return _8H(_8K);});},_8L=function(_8M,_8N){var _8O=function(_8P,_8Q){var _8R=E(_8P);if(!_8R[0]){return function(_8S){return new F(function(){return A(_8S,[_8M]);});};}else{var _8T=E(_8Q);return _8T[0]==0?E(_8H):E(_8R[1])[1]!=E(_8T[1])[1]?E(_8J):function(_8U){return [0,function(_8V){return E(new T(function(){return B(A(new T(function(){return B(_8O(_8R[2],_8T[2]));}),[_8U]));}));}];};}};return [1,function(_8W){return new F(function(){return A(_8O,[_8M,_8W,_8N]);});}];},_8X=[0,0],_8Y=function(_8Z){return new F(function(){return _8L(_8G,function(_90){return E(new T(function(){return B(A(_8Z,[_8X]));}));});});},_91=new T(function(){return B(unCStr("STX"));}),_92=[0,2],_93=function(_94){return new F(function(){return _8L(_91,function(_95){return E(new T(function(){return B(A(_94,[_92]));}));});});},_96=new T(function(){return B(unCStr("ETX"));}),_97=[0,3],_98=function(_99){return new F(function(){return _8L(_96,function(_9a){return E(new T(function(){return B(A(_99,[_97]));}));});});},_9b=new T(function(){return B(unCStr("EOT"));}),_9c=[0,4],_9d=function(_9e){return new F(function(){return _8L(_9b,function(_9f){return E(new T(function(){return B(A(_9e,[_9c]));}));});});},_9g=new T(function(){return B(unCStr("ENQ"));}),_9h=[0,5],_9i=function(_9j){return new F(function(){return _8L(_9g,function(_9k){return E(new T(function(){return B(A(_9j,[_9h]));}));});});},_9l=new T(function(){return B(unCStr("ACK"));}),_9m=[0,6],_9n=function(_9o){return new F(function(){return _8L(_9l,function(_9p){return E(new T(function(){return B(A(_9o,[_9m]));}));});});},_9q=new T(function(){return B(unCStr("BEL"));}),_9r=[0,7],_9s=function(_9t){return new F(function(){return _8L(_9q,function(_9u){return E(new T(function(){return B(A(_9t,[_9r]));}));});});},_9v=new T(function(){return B(unCStr("BS"));}),_9w=[0,8],_9x=function(_9y){return new F(function(){return _8L(_9v,function(_9z){return E(new T(function(){return B(A(_9y,[_9w]));}));});});},_9A=new T(function(){return B(unCStr("HT"));}),_9B=[0,9],_9C=function(_9D){return new F(function(){return _8L(_9A,function(_9E){return E(new T(function(){return B(A(_9D,[_9B]));}));});});},_9F=new T(function(){return B(unCStr("LF"));}),_9G=[0,10],_9H=function(_9I){return new F(function(){return _8L(_9F,function(_9J){return E(new T(function(){return B(A(_9I,[_9G]));}));});});},_9K=new T(function(){return B(unCStr("VT"));}),_9L=[0,11],_9M=function(_9N){return new F(function(){return _8L(_9K,function(_9O){return E(new T(function(){return B(A(_9N,[_9L]));}));});});},_9P=new T(function(){return B(unCStr("FF"));}),_9Q=[0,12],_9R=function(_9S){return new F(function(){return _8L(_9P,function(_9T){return E(new T(function(){return B(A(_9S,[_9Q]));}));});});},_9U=new T(function(){return B(unCStr("CR"));}),_9V=[0,13],_9W=function(_9X){return new F(function(){return _8L(_9U,function(_9Y){return E(new T(function(){return B(A(_9X,[_9V]));}));});});},_9Z=new T(function(){return B(unCStr("SI"));}),_a0=[0,15],_a1=function(_a2){return new F(function(){return _8L(_9Z,function(_a3){return E(new T(function(){return B(A(_a2,[_a0]));}));});});},_a4=new T(function(){return B(unCStr("DLE"));}),_a5=[0,16],_a6=function(_a7){return new F(function(){return _8L(_a4,function(_a8){return E(new T(function(){return B(A(_a7,[_a5]));}));});});},_a9=new T(function(){return B(unCStr("DC1"));}),_aa=[0,17],_ab=function(_ac){return new F(function(){return _8L(_a9,function(_ad){return E(new T(function(){return B(A(_ac,[_aa]));}));});});},_ae=new T(function(){return B(unCStr("DC2"));}),_af=[0,18],_ag=function(_ah){return new F(function(){return _8L(_ae,function(_ai){return E(new T(function(){return B(A(_ah,[_af]));}));});});},_aj=new T(function(){return B(unCStr("DC3"));}),_ak=[0,19],_al=function(_am){return new F(function(){return _8L(_aj,function(_an){return E(new T(function(){return B(A(_am,[_ak]));}));});});},_ao=new T(function(){return B(unCStr("DC4"));}),_ap=[0,20],_aq=function(_ar){return new F(function(){return _8L(_ao,function(_as){return E(new T(function(){return B(A(_ar,[_ap]));}));});});},_at=new T(function(){return B(unCStr("NAK"));}),_au=[0,21],_av=function(_aw){return new F(function(){return _8L(_at,function(_ax){return E(new T(function(){return B(A(_aw,[_au]));}));});});},_ay=new T(function(){return B(unCStr("SYN"));}),_az=[0,22],_aA=function(_aB){return new F(function(){return _8L(_ay,function(_aC){return E(new T(function(){return B(A(_aB,[_az]));}));});});},_aD=new T(function(){return B(unCStr("ETB"));}),_aE=[0,23],_aF=function(_aG){return new F(function(){return _8L(_aD,function(_aH){return E(new T(function(){return B(A(_aG,[_aE]));}));});});},_aI=new T(function(){return B(unCStr("CAN"));}),_aJ=[0,24],_aK=function(_aL){return new F(function(){return _8L(_aI,function(_aM){return E(new T(function(){return B(A(_aL,[_aJ]));}));});});},_aN=new T(function(){return B(unCStr("EM"));}),_aO=[0,25],_aP=function(_aQ){return new F(function(){return _8L(_aN,function(_aR){return E(new T(function(){return B(A(_aQ,[_aO]));}));});});},_aS=new T(function(){return B(unCStr("SUB"));}),_aT=[0,26],_aU=function(_aV){return new F(function(){return _8L(_aS,function(_aW){return E(new T(function(){return B(A(_aV,[_aT]));}));});});},_aX=new T(function(){return B(unCStr("ESC"));}),_aY=[0,27],_aZ=function(_b0){return new F(function(){return _8L(_aX,function(_b1){return E(new T(function(){return B(A(_b0,[_aY]));}));});});},_b2=new T(function(){return B(unCStr("FS"));}),_b3=[0,28],_b4=function(_b5){return new F(function(){return _8L(_b2,function(_b6){return E(new T(function(){return B(A(_b5,[_b3]));}));});});},_b7=new T(function(){return B(unCStr("GS"));}),_b8=[0,29],_b9=function(_ba){return new F(function(){return _8L(_b7,function(_bb){return E(new T(function(){return B(A(_ba,[_b8]));}));});});},_bc=new T(function(){return B(unCStr("RS"));}),_bd=[0,30],_be=function(_bf){return new F(function(){return _8L(_bc,function(_bg){return E(new T(function(){return B(A(_bf,[_bd]));}));});});},_bh=new T(function(){return B(unCStr("US"));}),_bi=[0,31],_bj=function(_bk){return new F(function(){return _8L(_bh,function(_bl){return E(new T(function(){return B(A(_bk,[_bi]));}));});});},_bm=new T(function(){return B(unCStr("SP"));}),_bn=[0,32],_bo=function(_bp){return new F(function(){return _8L(_bm,function(_bq){return E(new T(function(){return B(A(_bp,[_bn]));}));});});},_br=new T(function(){return B(unCStr("DEL"));}),_bs=[0,127],_bt=function(_bu){return new F(function(){return _8L(_br,function(_bv){return E(new T(function(){return B(A(_bu,[_bs]));}));});});},_bw=[1,_bt,_0],_bx=[1,_bo,_bw],_by=[1,_bj,_bx],_bz=[1,_be,_by],_bA=[1,_b9,_bz],_bB=[1,_b4,_bA],_bC=[1,_aZ,_bB],_bD=[1,_aU,_bC],_bE=[1,_aP,_bD],_bF=[1,_aK,_bE],_bG=[1,_aF,_bF],_bH=[1,_aA,_bG],_bI=[1,_av,_bH],_bJ=[1,_aq,_bI],_bK=[1,_al,_bJ],_bL=[1,_ag,_bK],_bM=[1,_ab,_bL],_bN=[1,_a6,_bM],_bO=[1,_a1,_bN],_bP=[1,_9W,_bO],_bQ=[1,_9R,_bP],_bR=[1,_9M,_bQ],_bS=[1,_9H,_bR],_bT=[1,_9C,_bS],_bU=[1,_9x,_bT],_bV=[1,_9s,_bU],_bW=[1,_9n,_bV],_bX=[1,_9i,_bW],_bY=[1,_9d,_bX],_bZ=[1,_98,_bY],_c0=[1,_93,_bZ],_c1=[1,_8Y,_c0],_c2=new T(function(){return B(unCStr("SOH"));}),_c3=[0,1],_c4=function(_c5){return new F(function(){return _8L(_c2,function(_c6){return E(new T(function(){return B(A(_c5,[_c3]));}));});});},_c7=new T(function(){return B(unCStr("SO"));}),_c8=[0,14],_c9=function(_ca){return new F(function(){return _8L(_c7,function(_cb){return E(new T(function(){return B(A(_ca,[_c8]));}));});});},_cc=function(_cd){return new F(function(){return _66(_c4,_c9,_cd);});},_ce=[1,_cc,_c1],_cf=new T(function(){return B(_8A(_ce));}),_cg=[0,1114111],_ch=[0,34],_ci=[0,_ch,_8f],_cj=[0,39],_ck=[0,_cj,_8f],_cl=[0,92],_cm=[0,_cl,_8f],_cn=[0,_9r,_8f],_co=[0,_9w,_8f],_cp=[0,_9Q,_8f],_cq=[0,_9G,_8f],_cr=[0,_9V,_8f],_cs=[0,_9B,_8f],_ct=[0,_9L,_8f],_cu=[0,_8X,_8f],_cv=[0,_c3,_8f],_cw=[0,_92,_8f],_cx=[0,_97,_8f],_cy=[0,_9c,_8f],_cz=[0,_9h,_8f],_cA=[0,_9m,_8f],_cB=[0,_9r,_8f],_cC=[0,_9w,_8f],_cD=[0,_9B,_8f],_cE=[0,_9G,_8f],_cF=[0,_9L,_8f],_cG=[0,_9Q,_8f],_cH=[0,_9V,_8f],_cI=[0,_c8,_8f],_cJ=[0,_a0,_8f],_cK=[0,_a5,_8f],_cL=[0,_aa,_8f],_cM=[0,_af,_8f],_cN=[0,_ak,_8f],_cO=[0,_ap,_8f],_cP=[0,_au,_8f],_cQ=[0,_az,_8f],_cR=[0,_aE,_8f],_cS=[0,_aJ,_8f],_cT=[0,_aO,_8f],_cU=[0,_aT,_8f],_cV=[0,_aY,_8f],_cW=[0,_b3,_8f],_cX=[0,_b8,_8f],_cY=[0,_bd,_8f],_cZ=[0,_bi,_8f],_d0=function(_d1){return new F(function(){return _4O([0,function(_d2){switch(E(E(_d2)[1])){case 34:return E(new T(function(){return B(A(_d1,[_ci]));}));case 39:return E(new T(function(){return B(A(_d1,[_ck]));}));case 92:return E(new T(function(){return B(A(_d1,[_cm]));}));case 97:return E(new T(function(){return B(A(_d1,[_cn]));}));case 98:return E(new T(function(){return B(A(_d1,[_co]));}));case 102:return E(new T(function(){return B(A(_d1,[_cp]));}));case 110:return E(new T(function(){return B(A(_d1,[_cq]));}));case 114:return E(new T(function(){return B(A(_d1,[_cr]));}));case 116:return E(new T(function(){return B(A(_d1,[_cs]));}));case 118:return E(new T(function(){return B(A(_d1,[_ct]));}));default:return [2];}}],new T(function(){return B(_4O(B(_66(_8g,_8j,function(_d3){return new F(function(){return _6t(_d3,function(_d4){var _d5=B(_7s(new T(function(){return B(_7i(E(_d3)[1]));}),_7h,_d4));return !B(_8q(_d5,_cg))?[2]:B(A(_d1,[[0,new T(function(){var _d6=B(_8n(_d5));if(_d6>>>0>1114111){var _d7=B(_8l(_d6));}else{var _d7=[0,_d6];}var _d8=_d7,_d9=_d8;return _d9;}),_8f]]));});});})),new T(function(){return B(_4O([0,function(_da){return E(E(_da)[1])==94?E([0,function(_db){switch(E(E(_db)[1])){case 64:return E(new T(function(){return B(A(_d1,[_cu]));}));case 65:return E(new T(function(){return B(A(_d1,[_cv]));}));case 66:return E(new T(function(){return B(A(_d1,[_cw]));}));case 67:return E(new T(function(){return B(A(_d1,[_cx]));}));case 68:return E(new T(function(){return B(A(_d1,[_cy]));}));case 69:return E(new T(function(){return B(A(_d1,[_cz]));}));case 70:return E(new T(function(){return B(A(_d1,[_cA]));}));case 71:return E(new T(function(){return B(A(_d1,[_cB]));}));case 72:return E(new T(function(){return B(A(_d1,[_cC]));}));case 73:return E(new T(function(){return B(A(_d1,[_cD]));}));case 74:return E(new T(function(){return B(A(_d1,[_cE]));}));case 75:return E(new T(function(){return B(A(_d1,[_cF]));}));case 76:return E(new T(function(){return B(A(_d1,[_cG]));}));case 77:return E(new T(function(){return B(A(_d1,[_cH]));}));case 78:return E(new T(function(){return B(A(_d1,[_cI]));}));case 79:return E(new T(function(){return B(A(_d1,[_cJ]));}));case 80:return E(new T(function(){return B(A(_d1,[_cK]));}));case 81:return E(new T(function(){return B(A(_d1,[_cL]));}));case 82:return E(new T(function(){return B(A(_d1,[_cM]));}));case 83:return E(new T(function(){return B(A(_d1,[_cN]));}));case 84:return E(new T(function(){return B(A(_d1,[_cO]));}));case 85:return E(new T(function(){return B(A(_d1,[_cP]));}));case 86:return E(new T(function(){return B(A(_d1,[_cQ]));}));case 87:return E(new T(function(){return B(A(_d1,[_cR]));}));case 88:return E(new T(function(){return B(A(_d1,[_cS]));}));case 89:return E(new T(function(){return B(A(_d1,[_cT]));}));case 90:return E(new T(function(){return B(A(_d1,[_cU]));}));case 91:return E(new T(function(){return B(A(_d1,[_cV]));}));case 92:return E(new T(function(){return B(A(_d1,[_cW]));}));case 93:return E(new T(function(){return B(A(_d1,[_cX]));}));case 94:return E(new T(function(){return B(A(_d1,[_cY]));}));case 95:return E(new T(function(){return B(A(_d1,[_cZ]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_cf,[function(_dc){return new F(function(){return A(_d1,[[0,_dc,_8f]]);});}]));})));})));}));});},_dd=function(_de){return new F(function(){return A(_de,[_2u]);});},_df=function(_dg){var _dh=E(_dg);if(!_dh[0]){return E(_dd);}else{var _di=_dh[2],_dj=E(E(_dh[1])[1]);switch(_dj){case 9:return function(_dk){return [0,function(_dl){return E(new T(function(){return B(A(new T(function(){return B(_df(_di));}),[_dk]));}));}];};case 10:return function(_dm){return [0,function(_dn){return E(new T(function(){return B(A(new T(function(){return B(_df(_di));}),[_dm]));}));}];};case 11:return function(_do){return [0,function(_dp){return E(new T(function(){return B(A(new T(function(){return B(_df(_di));}),[_do]));}));}];};case 12:return function(_dq){return [0,function(_dr){return E(new T(function(){return B(A(new T(function(){return B(_df(_di));}),[_dq]));}));}];};case 13:return function(_ds){return [0,function(_dt){return E(new T(function(){return B(A(new T(function(){return B(_df(_di));}),[_ds]));}));}];};case 32:return function(_du){return [0,function(_dv){return E(new T(function(){return B(A(new T(function(){return B(_df(_di));}),[_du]));}));}];};case 160:return function(_dw){return [0,function(_dx){return E(new T(function(){return B(A(new T(function(){return B(_df(_di));}),[_dw]));}));}];};default:var _dy=u_iswspace(_dj),_dz=_dy;return E(_dz)==0?E(_dd):function(_dA){return [0,function(_dB){return E(new T(function(){return B(A(new T(function(){return B(_df(_di));}),[_dA]));}));}];};}}},_dC=function(_dD){var _dE=new T(function(){return B(_dC(_dD));}),_dF=[1,function(_dG){return new F(function(){return A(_df,[_dG,function(_dH){return E([0,function(_dI){return E(E(_dI)[1])==92?E(_dE):[2];}]);}]);});}];return new F(function(){return _4O([0,function(_dJ){return E(E(_dJ)[1])==92?E([0,function(_dK){var _dL=E(E(_dK)[1]);switch(_dL){case 9:return E(_dF);case 10:return E(_dF);case 11:return E(_dF);case 12:return E(_dF);case 13:return E(_dF);case 32:return E(_dF);case 38:return E(_dE);case 160:return E(_dF);default:var _dM=u_iswspace(_dL),_dN=_dM;return E(_dN)==0?[2]:E(_dF);}}]):[2];}],[0,function(_dO){var _dP=E(_dO);return E(_dP[1])==92?E(new T(function(){return B(_d0(_dD));})):B(A(_dD,[[0,_dP,_8e]]));}]);});},_dQ=function(_dR,_dS){return new F(function(){return _dC(function(_dT){var _dU=E(_dT),_dV=E(_dU[1]);if(E(_dV[1])==34){if(!E(_dU[2])){return E(new T(function(){return B(A(_dS,[[1,new T(function(){return B(A(_dR,[_0]));})]]));}));}else{return new F(function(){return _dQ(function(_dW){return new F(function(){return A(_dR,[[1,_dV,_dW]]);});},_dS);});}}else{return new F(function(){return _dQ(function(_dX){return new F(function(){return A(_dR,[[1,_dV,_dX]]);});},_dS);});}});});},_dY=new T(function(){return B(unCStr("_\'"));}),_dZ=function(_e0){var _e1=u_iswalnum(_e0),_e2=_e1;return E(_e2)==0?B(_7W(_5v,[0,_e0],_dY)):true;},_e3=function(_e4){return new F(function(){return _dZ(E(_e4)[1]);});},_e5=new T(function(){return B(unCStr(",;()[]{}`"));}),_e6=function(_e7){return new F(function(){return A(_e7,[_0]);});},_e8=function(_e9,_ea){var _eb=function(_ec){var _ed=E(_ec);if(!_ed[0]){return E(_e6);}else{var _ee=_ed[1];return !B(A(_e9,[_ee]))?E(_e6):function(_ef){return [0,function(_eg){return E(new T(function(){return B(A(new T(function(){return B(_eb(_ed[2]));}),[function(_eh){return new F(function(){return A(_ef,[[1,_ee,_eh]]);});}]));}));}];};}};return [1,function(_ei){return new F(function(){return A(_eb,[_ei,_ea]);});}];},_ej=new T(function(){return B(unCStr(".."));}),_ek=new T(function(){return B(unCStr("::"));}),_el=new T(function(){return B(unCStr("->"));}),_em=[0,64],_en=[1,_em,_0],_eo=[0,126],_ep=[1,_eo,_0],_eq=new T(function(){return B(unCStr("=>"));}),_er=[1,_eq,_0],_es=[1,_ep,_er],_et=[1,_en,_es],_eu=[1,_el,_et],_ev=new T(function(){return B(unCStr("<-"));}),_ew=[1,_ev,_eu],_ex=[0,124],_ey=[1,_ex,_0],_ez=[1,_ey,_ew],_eA=[1,_cl,_0],_eB=[1,_eA,_ez],_eC=[0,61],_eD=[1,_eC,_0],_eE=[1,_eD,_eB],_eF=[1,_ek,_eE],_eG=[1,_ej,_eF],_eH=function(_eI){return new F(function(){return _4O([1,function(_eJ){return E(_eJ)[0]==0?E(new T(function(){return B(A(_eI,[_6q]));})):[2];}],new T(function(){return B(_4O([0,function(_eK){return E(E(_eK)[1])==39?E([0,function(_eL){var _eM=E(_eL);switch(E(_eM[1])){case 39:return [2];case 92:return E(new T(function(){return B(_d0(function(_eN){var _eO=E(_eN);return new F(function(){return (function(_eP,_eQ){var _eR=new T(function(){return B(A(_eI,[[0,_eP]]));});return !E(_eQ)?E(E(_eP)[1])==39?[2]:[0,function(_eS){return E(E(_eS)[1])==39?E(_eR):[2];}]:[0,function(_eT){return E(E(_eT)[1])==39?E(_eR):[2];}];})(_eO[1],_eO[2]);});}));}));default:return [0,function(_eU){return E(E(_eU)[1])==39?E(new T(function(){return B(A(_eI,[[0,_eM]]));})):[2];}];}}]):[2];}],new T(function(){return B(_4O([0,function(_eV){return E(E(_eV)[1])==34?E(new T(function(){return B(_dQ(_3a,_eI));})):[2];}],new T(function(){return B(_4O([0,function(_eW){return !B(_7W(_5v,_eW,_e5))?[2]:B(A(_eI,[[2,[1,_eW,_0]]]));}],new T(function(){return B(_4O([0,function(_eX){if(!B(_7W(_5v,_eX,_81))){return [2];}else{return new F(function(){return _e8(_82,function(_eY){var _eZ=[1,_eX,_eY];return !B(_7W(_5M,_eZ,_eG))?B(A(_eI,[[4,_eZ]])):B(A(_eI,[[2,_eZ]]));});});}}],new T(function(){return B(_4O([0,function(_f0){var _f1=E(_f0),_f2=_f1[1],_f3=u_iswalpha(_f2),_f4=_f3;if(!E(_f4)){if(E(_f2)==95){return new F(function(){return _e8(_e3,function(_f5){return new F(function(){return A(_eI,[[3,[1,_f1,_f5]]]);});});});}else{return [2];}}else{return new F(function(){return _e8(_e3,function(_f6){return new F(function(){return A(_eI,[[3,[1,_f1,_f6]]]);});});});}}],new T(function(){return B(_66(_86,_7R,_eI));})));})));})));})));})));}));});},_f7=function(_f8){return [1,function(_f9){return new F(function(){return A(_df,[_f9,function(_fa){return E(new T(function(){return B(_eH(_f8));}));}]);});}];},_fb=[0,0],_fc=function(_fd,_fe){return new F(function(){return _f7(function(_ff){var _fg=E(_ff);if(_fg[0]==2){var _fh=E(_fg[1]);return _fh[0]==0?[2]:E(E(_fh[1])[1])==40?E(_fh[2])[0]==0?E(new T(function(){return B(A(_fd,[_fb,function(_fi){return new F(function(){return _f7(function(_fj){var _fk=E(_fj);if(_fk[0]==2){var _fl=E(_fk[1]);return _fl[0]==0?[2]:E(E(_fl[1])[1])==41?E(_fl[2])[0]==0?E(new T(function(){return B(A(_fe,[_fi]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_fm=function(_fn,_fo,_fp){var _fq=function(_fr,_fs){return new F(function(){return _4O(B(_f7(function(_ft){var _fu=E(_ft);if(_fu[0]==4){var _fv=E(_fu[1]);if(!_fv[0]){return new F(function(){return A(_fn,[_fu,_fr,_fs]);});}else{return E(E(_fv[1])[1])==45?E(_fv[2])[0]==0?E([1,function(_fw){return new F(function(){return A(_df,[_fw,function(_fx){return E(new T(function(){return B(_eH(function(_fy){return new F(function(){return A(_fn,[_fy,_fr,function(_fz){return new F(function(){return A(_fs,[new T(function(){return [0, -E(_fz)[1]];})]);});}]);});}));}));}]);});}]):B(A(_fn,[_fu,_fr,_fs])):B(A(_fn,[_fu,_fr,_fs]));}}else{return new F(function(){return A(_fn,[_fu,_fr,_fs]);});}})),new T(function(){return B(_fc(_fq,_fs));}));});};return new F(function(){return _fq(_fo,_fp);});},_fA=function(_fB,_fC){return [2];},_fD=function(_fE,_fF){return new F(function(){return _fA(_fE,_fF);});},_fG=function(_fH){var _fI=E(_fH);return _fI[0]==0?[1,new T(function(){return B(_7s(new T(function(){return B(_7i(E(_fI[1])[1]));}),_7h,_fI[2]));})]:E(_fI[2])[0]==0?E(_fI[3])[0]==0?[1,new T(function(){return B(_7s(_7g,_7h,_fI[1]));})]:[0]:[0];},_fJ=function(_fK){var _fL=E(_fK);if(_fL[0]==5){var _fM=B(_fG(_fL[1]));return _fM[0]==0?E(_fA):function(_fN,_fO){return new F(function(){return A(_fO,[new T(function(){return [0,B(_8n(_fM[1]))];})]);});};}else{return E(_fD);}},_fP=function(_fQ,_fR){while(1){var _fS=E(_fQ);if(!_fS[0]){return E(_fR)[0]==0?true:false;}else{var _fT=E(_fR);if(!_fT[0]){return false;}else{if(E(_fS[1])[1]!=E(_fT[1])[1]){return false;}else{_fQ=_fS[2];_fR=_fT[2];continue;}}}}},_fU=new T(function(){return B(unCStr("onBarIndex"));}),_fV=new T(function(){return B(unCStr("BarPlacement"));}),_fW=new T(function(){return B(unCStr("onSideIndex"));}),_fX=new T(function(){return B(unCStr("SidePlacement"));}),_fY=function(_fZ,_g0){var _g1=new T(function(){if(_fZ>11){var _g2=[2];}else{var _g2=[1,function(_g3){return new F(function(){return A(_df,[_g3,function(_g4){return E(new T(function(){return B(_eH(function(_g5){var _g6=E(_g5);return _g6[0]==3?!B(_fP(_g6[1],_fX))?[2]:E([1,function(_g7){return new F(function(){return A(_df,[_g7,function(_g8){return E(new T(function(){return B(_eH(function(_g9){var _ga=E(_g9);if(_ga[0]==2){var _gb=E(_ga[1]);return _gb[0]==0?[2]:E(E(_gb[1])[1])==123?E(_gb[2])[0]==0?E([1,function(_gc){return new F(function(){return A(_df,[_gc,function(_gd){return E(new T(function(){return B(_eH(function(_ge){var _gf=E(_ge);return _gf[0]==3?!B(_fP(_gf[1],_fW))?[2]:E([1,function(_gg){return new F(function(){return A(_df,[_gg,function(_gh){return E(new T(function(){return B(_eH(function(_gi){var _gj=E(_gi);if(_gj[0]==2){var _gk=E(_gj[1]);return _gk[0]==0?[2]:E(E(_gk[1])[1])==61?E(_gk[2])[0]==0?E(new T(function(){return B(_fm(_fJ,_fb,function(_gl){return new F(function(){return _f7(function(_gm){var _gn=E(_gm);if(_gn[0]==2){var _go=E(_gn[1]);return _go[0]==0?[2]:E(E(_go[1])[1])==125?E(_go[2])[0]==0?E(new T(function(){return B(A(_g0,[[2,_gl]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}];}return _g2;});if(_fZ>11){return new F(function(){return _4O(_5Y,_g1);});}else{return new F(function(){return _4O(B(_f7(function(_gp){var _gq=E(_gp);return _gq[0]==3?!B(_fP(_gq[1],_fV))?[2]:E([1,function(_gr){return new F(function(){return A(_df,[_gr,function(_gs){return E(new T(function(){return B(_eH(function(_gt){var _gu=E(_gt);if(_gu[0]==2){var _gv=E(_gu[1]);return _gv[0]==0?[2]:E(E(_gv[1])[1])==123?E(_gv[2])[0]==0?E([1,function(_gw){return new F(function(){return A(_df,[_gw,function(_gx){return E(new T(function(){return B(_eH(function(_gy){var _gz=E(_gy);return _gz[0]==3?!B(_fP(_gz[1],_fU))?[2]:E([1,function(_gA){return new F(function(){return A(_df,[_gA,function(_gB){return E(new T(function(){return B(_eH(function(_gC){var _gD=E(_gC);if(_gD[0]==2){var _gE=E(_gD[1]);return _gE[0]==0?[2]:E(E(_gE[1])[1])==61?E(_gE[2])[0]==0?E(new T(function(){return B(_fm(_fJ,_fb,function(_gF){return new F(function(){return _f7(function(_gG){var _gH=E(_gG);if(_gH[0]==2){var _gI=E(_gH[1]);return _gI[0]==0?[2]:E(E(_gI[1])[1])==125?E(_gI[2])[0]==0?E(new T(function(){return B(A(_g0,[[1,_gF]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),_g1);});}},_gJ=new T(function(){return B(unCStr("onPointIndex"));}),_gK=new T(function(){return B(unCStr("pointIndex"));}),_gL=new T(function(){return B(unCStr("PointPlacement"));}),_gM=function(_gN,_gO){if(_gN>11){return new F(function(){return _4O(_5Y,new T(function(){return B(_fY(_gN,_gO));}));});}else{return new F(function(){return _4O(B(_f7(function(_gP){var _gQ=E(_gP);return _gQ[0]==3?!B(_fP(_gQ[1],_gL))?[2]:E([1,function(_gR){return new F(function(){return A(_df,[_gR,function(_gS){return E(new T(function(){return B(_eH(function(_gT){var _gU=E(_gT);if(_gU[0]==2){var _gV=E(_gU[1]);return _gV[0]==0?[2]:E(E(_gV[1])[1])==123?E(_gV[2])[0]==0?E([1,function(_gW){return new F(function(){return A(_df,[_gW,function(_gX){return E(new T(function(){return B(_eH(function(_gY){var _gZ=E(_gY);return _gZ[0]==3?!B(_fP(_gZ[1],_gK))?[2]:E([1,function(_h0){return new F(function(){return A(_df,[_h0,function(_h1){return E(new T(function(){return B(_eH(function(_h2){var _h3=E(_h2);if(_h3[0]==2){var _h4=E(_h3[1]);return _h4[0]==0?[2]:E(E(_h4[1])[1])==61?E(_h4[2])[0]==0?E(new T(function(){return B(_fm(_fJ,_fb,function(_h5){return new F(function(){return _f7(function(_h6){var _h7=E(_h6);if(_h7[0]==2){var _h8=E(_h7[1]);return _h8[0]==0?[2]:E(E(_h8[1])[1])==44?E(_h8[2])[0]==0?E([1,function(_h9){return new F(function(){return A(_df,[_h9,function(_ha){return E(new T(function(){return B(_eH(function(_hb){var _hc=E(_hb);return _hc[0]==3?!B(_fP(_hc[1],_gJ))?[2]:E([1,function(_hd){return new F(function(){return A(_df,[_hd,function(_he){return E(new T(function(){return B(_eH(function(_hf){var _hg=E(_hf);if(_hg[0]==2){var _hh=E(_hg[1]);return _hh[0]==0?[2]:E(E(_hh[1])[1])==61?E(_hh[2])[0]==0?E(new T(function(){return B(_fm(_fJ,_fb,function(_hi){return new F(function(){return _f7(function(_hj){var _hk=E(_hj);if(_hk[0]==2){var _hl=E(_hk[1]);return _hl[0]==0?[2]:E(E(_hl[1])[1])==125?E(_hl[2])[0]==0?E(new T(function(){return B(A(_gO,[[0,_h5,_hi]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_fY(_gN,_gO));}));});}},_hm=function(_hn,_ho){return new F(function(){return _gM(E(_hn)[1],_ho);});},_hp=function(_hq,_hr){var _hs=function(_ht){return function(_hu){return new F(function(){return _4O(B(A(new T(function(){return B(A(_hq,[_ht]));}),[_hu])),new T(function(){return B(_fc(_hs,_hu));}));});};};return new F(function(){return _hs(_hr);});},_hv=function(_hw){return [1,function(_hx){return new F(function(){return A(_df,[_hx,function(_hy){return E([3,_hw,_5Y]);}]);});}];},_hz=new T(function(){return B(A(_hp,[_hm,_fb,_hv]));}),_hA=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_hB=new T(function(){return B(err(_hA));}),_hC=function(_hD,_hE){return new F(function(){return A(_hE,[_y]);});},_hF=[0,_2w,_hC],_hG=[1,_hF,_0],_hH=function(_hI,_hJ){return new F(function(){return A(_hJ,[_E]);});},_hK=[0,_2v,_hH],_hL=[1,_hK,_hG],_hM=function(_hN,_hO,_hP){var _hQ=E(_hN);if(!_hQ[0]){return [2];}else{var _hR=E(_hQ[1]),_hS=_hR[1],_hT=new T(function(){return B(A(_hR[2],[_hO,_hP]));});return new F(function(){return _4O(B(_f7(function(_hU){var _hV=E(_hU);switch(_hV[0]){case 3:return !B(_fP(_hS,_hV[1]))?[2]:E(_hT);case 4:return !B(_fP(_hS,_hV[1]))?[2]:E(_hT);default:return [2];}})),new T(function(){return B(_hM(_hQ[2],_hO,_hP));}));});}},_hW=function(_hX,_hY){return new F(function(){return _hM(_hL,_hX,_hY);});},_hZ=new T(function(){return B(A(_hp,[_hW,_fb,_hv]));}),_i0=new T(function(){return B(err(_hA));}),_i1=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_i2=new T(function(){return B(err(_i1));}),_i3=new T(function(){return B(err(_i1));}),_i4=function(_i5,_i6,_i7){return _i7<=_i6?[1,[0,_i5],new T(function(){var _i8=_i6-_i5|0,_i9=function(_ia){return _ia>=(_i7-_i8|0)?[1,[0,_ia],new T(function(){return B(_i9(_ia+_i8|0));})]:[1,[0,_ia],_0];};return B(_i9(_i6));})]:_i7<=_i5?[1,[0,_i5],_0]:[0];},_ib=function(_ic,_id,_ie){return _ie>=_id?[1,[0,_ic],new T(function(){var _if=_id-_ic|0,_ig=function(_ih){return _ih<=(_ie-_if|0)?[1,[0,_ih],new T(function(){return B(_ig(_ih+_if|0));})]:[1,[0,_ih],_0];};return B(_ig(_id));})]:_ie>=_ic?[1,[0,_ic],_0]:[0];},_ii=function(_ij,_ik){return _ik<_ij?B(_i4(_ij,_ik,-2147483648)):B(_ib(_ij,_ik,2147483647));},_il=new T(function(){return B(_ii(135,150));}),_im=function(_in,_io){var _ip=E(_in);if(!_ip){return [0];}else{var _iq=E(_io);return _iq[0]==0?[0]:[1,_iq[1],new T(function(){return B(_im(_ip-1|0,_iq[2]));})];}},_ir=new T(function(){return B(_im(6,_il));}),_is=function(_it,_iu){var _iv=E(_it);if(!_iv[0]){return E(_ir);}else{var _iw=_iv[1];return _iu>1?[1,_iw,new T(function(){return B(_is(_iv[2],_iu-1|0));})]:[1,_iw,_ir];}},_ix=new T(function(){return B(_ii(25,40));}),_iy=new T(function(){return B(_is(_ix,6));}),_iz=function(_iA){while(1){var _iB=(function(_iC){var _iD=E(_iC);if(!_iD[0]){return [0];}else{var _iE=_iD[2],_iF=E(_iD[1]);if(!E(_iF[2])[0]){return [1,_iF[1],new T(function(){return B(_iz(_iE));})];}else{_iA=_iE;return null;}}})(_iA);if(_iB!=null){return _iB;}}},_iG=function(_iH,_iI){var _iJ=E(_iI);if(!_iJ[0]){return [0,_0,_0];}else{var _iK=_iJ[1];if(!B(A(_iH,[_iK]))){var _iL=new T(function(){var _iM=B(_iG(_iH,_iJ[2]));return [0,_iM[1],_iM[2]];});return [0,[1,_iK,new T(function(){return E(E(_iL)[1]);})],new T(function(){return E(E(_iL)[2]);})];}else{return [0,_0,_iJ];}}},_iN=function(_iO,_iP){while(1){var _iQ=E(_iP);if(!_iQ[0]){return [0];}else{if(!B(A(_iO,[_iQ[1]]))){return E(_iQ);}else{_iP=_iQ[2];continue;}}}},_iR=function(_iS){var _iT=E(_iS);switch(_iT){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _iU=u_iswspace(_iT),_iV=_iU;return E(_iV)==0?false:true;}},_iW=function(_iX){return new F(function(){return _iR(E(_iX)[1]);});},_iY=function(_iZ){var _j0=B(_iN(_iW,_iZ));if(!_j0[0]){return [0];}else{var _j1=new T(function(){var _j2=B(_iG(_iW,_j0));return [0,_j2[1],_j2[2]];});return [1,new T(function(){return E(E(_j1)[1]);}),new T(function(){return B(_iY(E(_j1)[2]));})];}},_j3=function(_j4,_){var _j5=setDropCheckerCallback_ffi(function(_j6,_j7,_j8){var _j9=E(_j4),_ja=_j9[1],_jb=_j9[6],_jc=new T(function(){return B(_iY(B(_4t(_j6))));}),_jd=B(_iz(B(_4E(_hz,new T(function(){return B(_3j(_4v,B(_2p(_jc,2))));})))));if(!_jd[0]){return E(_i3);}else{if(!E(_jd[2])[0]){var _je=E(_jd[1]);if(!_je[0]){var _jf=B(_4a(function(_jg){var _jh=E(_jg)[1]-E(_j7)[1];return _jh<0? -_jh<7:_jh<7;},_iy));if(!_jf[0]){return function(_6p){return new F(function(){return _3P(_je,_je,_jb,_6p);});};}else{var _ji=_jf[1],_jj=function(_jk,_jl,_){var _jm=E(_je[1]),_jn=_jm[1];if(_jk<=_jn){return new F(function(){return _3P(_je,_je,_jb,_);});}else{var _jo=B(_iz(B(_4E(_hZ,new T(function(){return B(_2p(_jc,1));})))));if(!_jo[0]){return E(_i2);}else{var _jp=_jo[1];if(!E(_jo[2])[0]){if(_jk>=0){var _jq=B(_2p(_ja,_jk)),_jr=function(_){var _js=B(_3P(_je,[0,_jl,new T(function(){if(_jk>=0){var _jt=E(B(_2p(_ja,_jk))[2]);}else{var _jt=E(_2m);}return _jt;})],_jb,_)),_ju=_js;if(_jn>=0){var _jv=new T(function(){return B(_4m(function(_jw,_jx,_jy){return [1,new T(function(){var _jz=E(_jw)[1];return _jz!=_jn?_jz!=_jk?E(_jx):[0,new T(function(){if(_jn>=0){var _jA=E(B(_2p(_ja,_jn))[1]);}else{var _jA=E(_2m);}return _jA;}),new T(function(){return [0,E(E(_jx)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_jx)[1]);}),new T(function(){return [0,E(E(_jx)[2])[1]-1|0];})];}),_jy];},_0,_4C,_ja));}),_jB=B((function(_jC,_){while(1){var _jD=(function(_jE,_){var _jF=E(_jE);if(!_jF[0]){return _2u;}else{var _jG=_jF[1],_jH=B(_3P([0,_jm,_jG],[0,_jm,new T(function(){return [0,E(_jG)[1]-1|0];})],_jb,_)),_jI=_jH;_jC=_jF[2];return null;}})(_jC,_);if(_jD!=null){return _jD;}}})(B(_3Z(1,B(_44(E(_je[2])[1],E(B(_2p(_jv,_jn))[2])[1])))),_)),_jJ=_jB;return new F(function(){return _j3([0,_jv,_j9[2],_j9[3],_j9[4],_j9[5],_jb,_j9[7]],_);});}else{return E(_2m);}},_jK=function(_){return E(_jq[2])[1]>=2?B(_3P(_je,_je,_jb,_)):B(_jr(_));};return E(_jq[1])==0?E(_jp)==0?B(_jr(_)):B(_jK(_)):E(_jp)==0?B(_jK(_)):B(_jr(_));}else{return E(_2m);}}else{return E(_i0);}}}};if(E(_j8)[1]<=E(_4B)[1]){var _jL=E(_ji);return function(_6p){return new F(function(){return _jj(_jL[1],_jL,_6p);});};}else{var _jM=23-E(_ji)[1]|0;return function(_6p){return new F(function(){return _jj(_jM,[0,_jM],_6p);});};}}}else{return function(_6p){return new F(function(){return _3P(_je,_je,_jb,_6p);});};}}else{return E(_hB);}}});return _2u;},_jN=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:139:5-10"));}),_jO=function(_){return _2u;},_jP=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_jQ=new T(function(){return B(unCStr("base"));}),_jR=new T(function(){return B(unCStr("IOException"));}),_jS=new T(function(){var _jT=hs_wordToWord64(4053623282),_jU=_jT,_jV=hs_wordToWord64(3693590983),_jW=_jV;return [0,_jU,_jW,[0,_jU,_jW,_jQ,_jP,_jR],_0];}),_jX=function(_jY){return E(_jS);},_jZ=function(_k0){var _k1=E(_k0);return new F(function(){return _T(B(_P(_k1[1])),_jX,_k1[2]);});},_k2=new T(function(){return B(unCStr(": "));}),_k3=[0,41],_k4=new T(function(){return B(unCStr(" ("));}),_k5=new T(function(){return B(unCStr("already exists"));}),_k6=new T(function(){return B(unCStr("does not exist"));}),_k7=new T(function(){return B(unCStr("protocol error"));}),_k8=new T(function(){return B(unCStr("failed"));}),_k9=new T(function(){return B(unCStr("invalid argument"));}),_ka=new T(function(){return B(unCStr("inappropriate type"));}),_kb=new T(function(){return B(unCStr("hardware fault"));}),_kc=new T(function(){return B(unCStr("unsupported operation"));}),_kd=new T(function(){return B(unCStr("timeout"));}),_ke=new T(function(){return B(unCStr("resource vanished"));}),_kf=new T(function(){return B(unCStr("interrupted"));}),_kg=new T(function(){return B(unCStr("resource busy"));}),_kh=new T(function(){return B(unCStr("resource exhausted"));}),_ki=new T(function(){return B(unCStr("end of file"));}),_kj=new T(function(){return B(unCStr("illegal operation"));}),_kk=new T(function(){return B(unCStr("permission denied"));}),_kl=new T(function(){return B(unCStr("user error"));}),_km=new T(function(){return B(unCStr("unsatisified constraints"));}),_kn=new T(function(){return B(unCStr("system error"));}),_ko=function(_kp,_kq){switch(E(_kp)){case 0:return new F(function(){return _1d(_k5,_kq);});break;case 1:return new F(function(){return _1d(_k6,_kq);});break;case 2:return new F(function(){return _1d(_kg,_kq);});break;case 3:return new F(function(){return _1d(_kh,_kq);});break;case 4:return new F(function(){return _1d(_ki,_kq);});break;case 5:return new F(function(){return _1d(_kj,_kq);});break;case 6:return new F(function(){return _1d(_kk,_kq);});break;case 7:return new F(function(){return _1d(_kl,_kq);});break;case 8:return new F(function(){return _1d(_km,_kq);});break;case 9:return new F(function(){return _1d(_kn,_kq);});break;case 10:return new F(function(){return _1d(_k7,_kq);});break;case 11:return new F(function(){return _1d(_k8,_kq);});break;case 12:return new F(function(){return _1d(_k9,_kq);});break;case 13:return new F(function(){return _1d(_ka,_kq);});break;case 14:return new F(function(){return _1d(_kb,_kq);});break;case 15:return new F(function(){return _1d(_kc,_kq);});break;case 16:return new F(function(){return _1d(_kd,_kq);});break;case 17:return new F(function(){return _1d(_ke,_kq);});break;default:return new F(function(){return _1d(_kf,_kq);});}},_kr=[0,125],_ks=new T(function(){return B(unCStr("{handle: "));}),_kt=function(_ku,_kv,_kw,_kx,_ky,_kz){var _kA=new T(function(){var _kB=new T(function(){return B(_ko(_kv,new T(function(){var _kC=E(_kx);return _kC[0]==0?E(_kz):B(_1d(_k4,new T(function(){return B(_1d(_kC,[1,_k3,_kz]));})));})));}),_kD=E(_kw);return _kD[0]==0?E(_kB):B(_1d(_kD,new T(function(){return B(_1d(_k2,_kB));})));}),_kE=E(_ky);if(!_kE[0]){var _kF=E(_ku);if(!_kF[0]){return E(_kA);}else{var _kG=E(_kF[1]);return _kG[0]==0?B(_1d(_ks,new T(function(){return B(_1d(_kG[1],[1,_kr,new T(function(){return B(_1d(_k2,_kA));})]));}))):B(_1d(_ks,new T(function(){return B(_1d(_kG[1],[1,_kr,new T(function(){return B(_1d(_k2,_kA));})]));})));}}else{return new F(function(){return _1d(_kE[1],new T(function(){return B(_1d(_k2,_kA));}));});}},_kH=function(_kI){var _kJ=E(_kI);return new F(function(){return _kt(_kJ[1],_kJ[2],_kJ[3],_kJ[4],_kJ[6],_0);});},_kK=function(_kL,_kM){var _kN=E(_kL);return new F(function(){return _kt(_kN[1],_kN[2],_kN[3],_kN[4],_kN[6],_kM);});},_kO=function(_kP,_kQ){return new F(function(){return _1n(_kK,_kP,_kQ);});},_kR=function(_kS,_kT,_kU){var _kV=E(_kT);return new F(function(){return _kt(_kV[1],_kV[2],_kV[3],_kV[4],_kV[6],_kU);});},_kW=[0,_kR,_kH,_kO],_kX=new T(function(){return [0,_jX,_kW,_kY,_jZ];}),_kY=function(_kZ){return [0,_kX,_kZ];},_l0=7,_l1=function(_l2){return [0,_7I,_l0,_0,_l2,_7I,_7I];},_l3=function(_l4,_){return new F(function(){return die(new T(function(){return B(_kY(new T(function(){return B(_l1(_l4));})));}));});},_l5=function(_l6,_){return new F(function(){return _l3(_l6,_);});},_l7=[0,114],_l8=[1,_l7,_0],_l9=new T(function(){return B(_2N(0,6,_0));}),_la=new T(function(){return B(unCStr("cx"));}),_lb=new T(function(){return B(unCStr("cy"));}),_lc=new T(function(){return B(unCStr("circle"));}),_ld=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_le=new T(function(){return B(unCStr("board"));}),_lf=function(_lg,_lh,_){while(1){var _li=(function(_lj,_lk,_){var _ll=E(_lk);if(!_ll[0]){return _2u;}else{var _lm=_ll[2],_ln=E(_ll[1]),_lo=E(_ln[2])[1];if(_lo>0){var _lp=function(_lq,_lr,_){var _ls=jsFind(toJSStr(E(_le))),_lt=_ls,_lu=E(_lt);if(!_lu[0]){var _lv=B(_l5(_jN,_)),_lw=_lv;return new F(function(){return A(_lr,[_]);});}else{var _lx=jsCreateElemNS(toJSStr(E(_ld)),toJSStr(E(_lc))),_ly=_lx,_lz=[0,_ly],_lA=B(A(_34,[_3a,_lz,_l8,_l9,_])),_lB=_lA,_lC=[0,[0,_lj],_lq],_lD=new T(function(){var _lE=B(_3v(_lC));return [0,_lE[1],_lE[2]];}),_lF=B(A(_34,[_3a,_lz,_la,new T(function(){return B(_2N(0,E(E(_lD)[1])[1],_0));}),_])),_lG=_lF,_lH=B(A(_34,[_3a,_lz,_lb,new T(function(){return B(_2N(0,E(E(_lD)[2])[1],_0));}),_])),_lI=_lH,_lJ=B(A(_3n,[_lz,_y,_lC,_ln[1],_])),_lK=_lJ,_lL=jsAppendChild(_ly,E(_lu[1])[1]);return new F(function(){return A(_lr,[_]);});}},_lM=function(_lN,_lO,_){var _lP=E(_lN);if(!_lP[0]){return _2u;}else{var _lQ=_lP[1];if(_lO>1){return new F(function(){return _lp(_lQ,function(_){return new F(function(){return _lM(_lP[2],_lO-1|0,_);});},_);});}else{return new F(function(){return _lp(_lQ,_jO,_);});}}},_lR=B(_lM(_4C,_lo,_)),_lS=_lR,_lT=E(_lj);if(_lT==2147483647){return _2u;}else{_lg=_lT+1|0;_lh=_lm;return null;}}else{var _lU=E(_lj);if(_lU==2147483647){return _2u;}else{_lg=_lU+1|0;_lh=_lm;return null;}}}})(_lg,_lh,_);if(_li!=null){return _li;}}},_lV=function(_){var _lW=B(_lf(0,_2j,_)),_lX=_lW;return new F(function(){return _j3(_2k,_);});},_lY=function(_){return new F(function(){return _lV(_);});};
var hasteMain = function() {B(A(_lY, [0]));};window.onload = hasteMain;