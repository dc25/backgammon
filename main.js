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

var _0=[0],_1=function(_2,_3){while(1){var _4=E(_2);if(!_4[0]){return E(_3);}else{_2=_4[2];var _5=[1,_4[1],_3];_3=_5;continue;}}},_6=2,_7=[0,0],_8=[0,_6,_7],_9=[0,_6,_7],_a=[0,_6,_7],_b=[0,_6,_7],_c=[0,_6,_7],_d=[1,_c,_0],_e=[0,_6,_7],_f=[1,_e,_d],_g=[0,_6,_7],_h=[1,_g,_f],_i=[0,_6,_7],_j=[1,_i,_h],_k=[0,_6,_7],_l=[1,_k,_j],_m=1,_n=[0,5],_o=[0,_m,_n],_p=[1,_o,_l],_q=[0,_6,_7],_r=[1,_q,_p],_s=[0,3],_t=[0,_m,_s],_u=[1,_t,_r],_v=[0,_6,_7],_w=[1,_v,_u],_x=[0,_6,_7],_y=[1,_x,_w],_z=[0,_6,_7],_A=[1,_z,_y],_B=[0,_6,_7],_C=[1,_B,_A],_D=[0,_m,_n],_E=[1,_D,_C],_F=[0,_6,_7],_G=[1,_F,_E],_H=[0,_6,_7],_I=[1,_H,_G],_J=[0,_6,_7],_K=[1,_J,_I],_L=[0,_6,_7],_M=[1,_L,_K],_N=[0,_6,_7],_O=[1,_N,_M],_P=[1,_b,_O],_Q=[1,_a,_P],_R=[1,_9,_Q],_S=[1,_8,_R],_T=[0,_6,_7],_U=[1,_T,_S],_V=[0,2],_W=[0,_m,_V],_X=[1,_W,_U],_Y=new T(function(){return B(_1(_X,_0));}),_Z=0,_10=function(_11,_12){var _13=E(_11);if(!_13[0]){return [0];}else{var _14=E(_12);return _14[0]==0?[0]:[1,new T(function(){var _15=E(_14[1]);if(E(_15[1])==1){var _16=E(_15);}else{var _17=E(_13[1]),_16=E(_17[1])==1?[0,_Z,_17[2]]:E(_17);}var _18=_16;return _18;}),new T(function(){return B(_10(_13[2],_14[2]));})];}},_19=new T(function(){return B(_10(_Y,_X));}),_1a=[0,_19,_7,_7,_7,_7,_m,_m],_1b=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_1c=new T(function(){return B(err(_1b));}),_1d=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_1e=new T(function(){return B(err(_1d));}),_1f=function(_1g,_1h){while(1){var _1i=E(_1g);if(!_1i[0]){return E(_1e);}else{var _1j=E(_1h);if(!_1j){return E(_1i[1]);}else{_1g=_1i[2];_1h=_1j-1|0;continue;}}}},_1k=0,_1l=new T(function(){return B(unCStr("None"));}),_1m=new T(function(){return B(unCStr("White"));}),_1n=new T(function(){return B(unCStr("Black"));}),_1o=function(_1p,_1q,_1r,_1s){return new F(function(){return A(_1p,[new T(function(){return function(_){var _1t=jsSetAttr(E(_1q)[1],toJSStr(E(_1r)),toJSStr(E(_1s)));return _1k;};})]);});},_1u=function(_1v,_1w){var _1x=E(_1v);return _1x[0]==0?E(_1w):[1,_1x[1],new T(function(){return B(_1u(_1x[2],_1w));})];},_1y=function(_1z,_1A){var _1B=jsShowI(_1z),_1C=_1B;return new F(function(){return _1u(fromJSStr(_1C),_1A);});},_1D=[0,41],_1E=[0,40],_1F=function(_1G,_1H,_1I){return _1H>=0?B(_1y(_1H,_1I)):_1G<=6?B(_1y(_1H,_1I)):[1,_1E,new T(function(){var _1J=jsShowI(_1H),_1K=_1J;return B(_1u(fromJSStr(_1K),[1,_1D,_1I]));})];},_1L=function(_1M){return E(_1M);},_1N=new T(function(){return B(unCStr("class"));}),_1O=new T(function(){return B(unCStr("draggable "));}),_1P=function(_1Q,_1R,_1S,_1T,_1U){return new F(function(){return _1o(_1L,_1Q,_1N,new T(function(){var _1V=new T(function(){var _1W=new T(function(){return B(unAppCStr(" pi",new T(function(){return B(_1u(B(_1F(0,E(_1S)[1],_0)),new T(function(){return B(unAppCStr(" ci",new T(function(){return B(_1F(0,E(_1T)[1],_0));})));})));})));});switch(E(_1U)){case 0:var _1X=B(_1u(_1n,_1W));break;case 1:var _1X=B(_1u(_1m,_1W));break;default:var _1X=B(_1u(_1l,_1W));}return _1X;});switch(E(_1R)){case 0:switch(E(_1U)){case 0:var _1Y=B(_1u(_1O,_1V));break;case 1:var _1Y=E(_1V);break;default:var _1Y=E(_1V);}var _1Z=_1Y;break;case 1:var _1Z=E(_1U)==1?B(_1u(_1O,_1V)):E(_1V);break;default:var _1Z=E(_1U)==2?B(_1u(_1O,_1V)):E(_1V);}return _1Z;}));});},_20=function(_21,_22){return [0,new T(function(){var _23=E(_21)[1];if(_23>=12){var _24=23-_23|0;if(_24>=6){var _25=[0,25+(20+(imul(_24,15)|0)|0)|0];}else{var _25=[0,25+(imul(_24,15)|0)|0];}var _26=_25,_27=_26;}else{if(_23>=6){var _28=[0,25+(20+(imul(_23,15)|0)|0)|0];}else{var _28=[0,25+(imul(_23,15)|0)|0];}var _27=_28;}var _29=_27;return _29;}),new T(function(){if(E(_21)[1]>=12){var _2a=[0,203+(imul(imul(imul(-1,E(_22)[1])|0,2)|0,6)|0)|0];}else{var _2a=[0,7+(imul(imul(E(_22)[1],2)|0,6)|0)|0];}var _2b=_2a;return _2b;})];},_2c=function(_2d,_2e,_2f,_2g,_2h,_){var _2i=jsElemsByClassName(toJSStr(B(unAppCStr(" pi",new T(function(){return B(_1u(B(_1F(0,E(_2d)[1],_0)),new T(function(){return B(unAppCStr(" ci",new T(function(){return B(_1F(0,E(_2e)[1],_0));})));})));}))))),_2j=_2i,_2k=B(_1f(_2j,0)),_2l=B(_20(_2f,_2g)),_2m=animateCircle_ffi(_2k[1],E(_2l[1])[1],E(_2l[2])[1],300);return new F(function(){return A(_1P,[_2k,_2h,_2f,_2g,_2h,_]);});},_2n=function(_2o,_2p){while(1){var _2q=E(_2o);if(!_2q){return E(_2p);}else{var _2r=E(_2p);if(!_2r[0]){return [0];}else{_2o=_2q-1|0;_2p=_2r[2];continue;}}}},_2s=function(_2t,_2u){if(_2t<=_2u){var _2v=function(_2w){return [1,[0,_2w],new T(function(){if(_2w!=_2u){var _2x=B(_2v(_2w+1|0));}else{var _2x=[0];}return _2x;})];};return new F(function(){return _2v(_2t);});}else{return [0];}},_2y=function(_2z,_2A){var _2B=function(_2C,_2D){while(1){var _2E=(function(_2F,_2G){var _2H=E(_2G);if(!_2H[0]){return [0];}else{var _2I=_2H[2];if(!B(A(_2z,[_2H[1]]))){var _2J=_2F+1|0;_2D=_2I;_2C=_2J;return null;}else{return [1,[0,_2F],new T(function(){return B(_2B(_2F+1|0,_2I));})];}}})(_2C,_2D);if(_2E!=null){return _2E;}}};return new F(function(){return _2B(0,_2A);});},_2K=function(_2L,_2M,_2N,_2O){var _2P=E(_2N);if(!_2P[0]){return E(_2M);}else{var _2Q=E(_2O);if(!_2Q[0]){return E(_2M);}else{return new F(function(){return A(_2L,[_2P[1],_2Q[1],new T(function(){return B(_2K(_2L,_2M,_2P[2],_2Q[2]));})]);});}}},_2R=function(_2S){return new F(function(){return fromJSStr(E(_2S)[1]);});},_2T=function(_2U,_2V){if(_2U<=0){if(_2U>=0){return new F(function(){return quot(_2U,_2V);});}else{if(_2V<=0){return new F(function(){return quot(_2U,_2V);});}else{return quot(_2U+1|0,_2V)-1|0;}}}else{if(_2V>=0){if(_2U>=0){return new F(function(){return quot(_2U,_2V);});}else{if(_2V<=0){return new F(function(){return quot(_2U,_2V);});}else{return quot(_2U+1|0,_2V)-1|0;}}}else{return quot(_2U-1|0,_2V)-1|0;}}},_2W=new T(function(){return [0,B(_2T(210,2))];}),_2X=new T(function(){return B(_2s(0,2147483647));}),_2Y=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2Z=new T(function(){return B(unCStr("base"));}),_30=new T(function(){return B(unCStr("PatternMatchFail"));}),_31=new T(function(){var _32=hs_wordToWord64(18445595),_33=_32,_34=hs_wordToWord64(52003073),_35=_34;return [0,_33,_35,[0,_33,_35,_2Z,_2Y,_30],_0];}),_36=function(_37){return E(_31);},_38=function(_39){return E(E(_39)[1]);},_3a=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_3b=new T(function(){return B(err(_3a));}),_3c=function(_3d,_3e,_3f){var _3g=new T(function(){var _3h=B(A(_3d,[_3f])),_3i=B(A(_3e,[new T(function(){var _3j=E(_3g);return _3j[0]==0?E(_3b):E(_3j[1]);})])),_3k=hs_eqWord64(_3h[1],_3i[1]),_3l=_3k;if(!E(_3l)){var _3m=[0];}else{var _3n=hs_eqWord64(_3h[2],_3i[2]),_3o=_3n,_3m=E(_3o)==0?[0]:[1,_3f];}var _3p=_3m,_3q=_3p;return _3q;});return E(_3g);},_3r=function(_3s){var _3t=E(_3s);return new F(function(){return _3c(B(_38(_3t[1])),_36,_3t[2]);});},_3u=function(_3v){return E(E(_3v)[1]);},_3w=function(_3x,_3y){return new F(function(){return _1u(E(_3x)[1],_3y);});},_3z=[0,44],_3A=[0,93],_3B=[0,91],_3C=function(_3D,_3E,_3F){var _3G=E(_3E);return _3G[0]==0?B(unAppCStr("[]",_3F)):[1,_3B,new T(function(){return B(A(_3D,[_3G[1],new T(function(){var _3H=function(_3I){var _3J=E(_3I);return _3J[0]==0?E([1,_3A,_3F]):[1,_3z,new T(function(){return B(A(_3D,[_3J[1],new T(function(){return B(_3H(_3J[2]));})]));})];};return B(_3H(_3G[2]));})]));})];},_3K=function(_3L,_3M){return new F(function(){return _3C(_3w,_3L,_3M);});},_3N=function(_3O,_3P,_3Q){return new F(function(){return _1u(E(_3P)[1],_3Q);});},_3R=[0,_3N,_3u,_3K],_3S=new T(function(){return [0,_36,_3R,_3T,_3r];}),_3T=function(_3U){return [0,_3S,_3U];},_3V=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_3W=function(_3X,_3Y){return new F(function(){return die(new T(function(){return B(A(_3Y,[_3X]));}));});},_3Z=function(_40,_41){var _42=E(_41);if(!_42[0]){return [0,_0,_0];}else{var _43=_42[1];if(!B(A(_40,[_43]))){return [0,_0,_42];}else{var _44=new T(function(){var _45=B(_3Z(_40,_42[2]));return [0,_45[1],_45[2]];});return [0,[1,_43,new T(function(){return E(E(_44)[1]);})],new T(function(){return E(E(_44)[2]);})];}}},_46=[0,32],_47=[0,10],_48=[1,_47,_0],_49=function(_4a){return E(E(_4a)[1])==124?false:true;},_4b=function(_4c,_4d){var _4e=B(_3Z(_49,B(unCStr(_4c)))),_4f=_4e[1],_4g=function(_4h,_4i){return new F(function(){return _1u(_4h,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_1u(_4d,new T(function(){return B(_1u(_4i,_48));})));})));}));});},_4j=E(_4e[2]);if(!_4j[0]){return new F(function(){return _4g(_4f,_0);});}else{return E(E(_4j[1])[1])==124?B(_4g(_4f,[1,_46,_4j[2]])):B(_4g(_4f,_0));}},_4k=function(_4l){return new F(function(){return _3W([0,new T(function(){return B(_4b(_4l,_3V));})],_3T);});},_4m=new T(function(){return B(_4k("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_4n=function(_4o,_4p){while(1){var _4q=(function(_4r,_4s){var _4t=E(_4r);switch(_4t[0]){case 0:var _4u=E(_4s);if(!_4u[0]){return [0];}else{_4o=B(A(_4t[1],[_4u[1]]));_4p=_4u[2];return null;}break;case 1:var _4v=B(A(_4t[1],[_4s])),_4w=_4s;_4o=_4v;_4p=_4w;return null;case 2:return [0];case 3:return [1,[0,_4t[1],_4s],new T(function(){return B(_4n(_4t[2],_4s));})];default:return E(_4t[1]);}})(_4o,_4p);if(_4q!=null){return _4q;}}},_4x=function(_4y,_4z){var _4A=new T(function(){var _4B=E(_4z);if(_4B[0]==3){var _4C=[3,_4B[1],new T(function(){return B(_4x(_4y,_4B[2]));})];}else{var _4D=E(_4y);if(_4D[0]==2){var _4E=E(_4B);}else{var _4F=E(_4B);if(_4F[0]==2){var _4G=E(_4D);}else{var _4H=new T(function(){var _4I=E(_4F);if(_4I[0]==4){var _4J=[1,function(_4K){return [4,new T(function(){return B(_1u(B(_4n(_4D,_4K)),_4I[1]));})];}];}else{var _4L=E(_4D);if(_4L[0]==1){var _4M=_4L[1],_4N=E(_4I);if(!_4N[0]){var _4O=[1,function(_4P){return new F(function(){return _4x(B(A(_4M,[_4P])),_4N);});}];}else{var _4O=[1,function(_4Q){return new F(function(){return _4x(B(A(_4M,[_4Q])),new T(function(){return B(A(_4N[1],[_4Q]));}));});}];}var _4R=_4O;}else{var _4S=E(_4I);if(!_4S[0]){var _4T=E(_4m);}else{var _4T=[1,function(_4U){return new F(function(){return _4x(_4L,new T(function(){return B(A(_4S[1],[_4U]));}));});}];}var _4R=_4T;}var _4J=_4R;}return _4J;}),_4V=E(_4D);switch(_4V[0]){case 1:var _4W=E(_4F);if(_4W[0]==4){var _4X=[1,function(_4Y){return [4,new T(function(){return B(_1u(B(_4n(B(A(_4V[1],[_4Y])),_4Y)),_4W[1]));})];}];}else{var _4X=E(_4H);}var _4Z=_4X;break;case 4:var _50=_4V[1],_51=E(_4F);switch(_51[0]){case 0:var _52=[1,function(_53){return [4,new T(function(){return B(_1u(_50,new T(function(){return B(_4n(_51,_53));})));})];}];break;case 1:var _52=[1,function(_54){return [4,new T(function(){return B(_1u(_50,new T(function(){return B(_4n(B(A(_51[1],[_54])),_54));})));})];}];break;default:var _52=[4,new T(function(){return B(_1u(_50,_51[1]));})];}var _4Z=_52;break;default:var _4Z=E(_4H);}var _4G=_4Z;}var _4E=_4G;}var _4C=_4E;}return _4C;}),_55=E(_4y);switch(_55[0]){case 0:var _56=E(_4z);return _56[0]==0?[0,function(_57){return new F(function(){return _4x(B(A(_55[1],[_57])),new T(function(){return B(A(_56[1],[_57]));}));});}]:E(_4A);case 3:return [3,_55[1],new T(function(){return B(_4x(_55[2],_4z));})];default:return E(_4A);}},_58=function(_59,_5a){return E(_59)[1]!=E(_5a)[1];},_5b=function(_5c,_5d){return E(_5c)[1]==E(_5d)[1];},_5e=[0,_5b,_58],_5f=function(_5g){return E(E(_5g)[1]);},_5h=function(_5i,_5j,_5k){while(1){var _5l=E(_5j);if(!_5l[0]){return E(_5k)[0]==0?true:false;}else{var _5m=E(_5k);if(!_5m[0]){return false;}else{if(!B(A(_5f,[_5i,_5l[1],_5m[1]]))){return false;}else{_5j=_5l[2];_5k=_5m[2];continue;}}}}},_5n=function(_5o,_5p,_5q){return !B(_5h(_5o,_5p,_5q))?true:false;},_5r=function(_5s){return [0,function(_5t,_5u){return new F(function(){return _5h(_5s,_5t,_5u);});},function(_5t,_5u){return new F(function(){return _5n(_5s,_5t,_5u);});}];},_5v=new T(function(){return B(_5r(_5e));}),_5w=function(_5x,_5y){var _5z=E(_5x);switch(_5z[0]){case 0:return [0,function(_5A){return new F(function(){return _5w(B(A(_5z[1],[_5A])),_5y);});}];case 1:return [1,function(_5B){return new F(function(){return _5w(B(A(_5z[1],[_5B])),_5y);});}];case 2:return [2];case 3:return new F(function(){return _4x(B(A(_5y,[_5z[1]])),new T(function(){return B(_5w(_5z[2],_5y));}));});break;default:var _5C=function(_5D){var _5E=E(_5D);if(!_5E[0]){return [0];}else{var _5F=E(_5E[1]);return new F(function(){return _1u(B(_4n(B(A(_5y,[_5F[1]])),_5F[2])),new T(function(){return B(_5C(_5E[2]));}));});}},_5G=B(_5C(_5z[1]));return _5G[0]==0?[2]:[4,_5G];}},_5H=[2],_5I=function(_5J){return [3,_5J,_5H];},_5K=function(_5L,_5M){var _5N=E(_5L);if(!_5N){return new F(function(){return A(_5M,[_1k]);});}else{return [0,function(_5O){return E(new T(function(){return B(_5K(_5N-1|0,_5M));}));}];}},_5P=function(_5Q,_5R,_5S){return [1,function(_5T){return new F(function(){return A(function(_5U,_5V,_5W){while(1){var _5X=(function(_5Y,_5Z,_60){var _61=E(_5Y);switch(_61[0]){case 0:var _62=E(_5Z);if(!_62[0]){return E(_5R);}else{_5U=B(A(_61[1],[_62[1]]));_5V=_62[2];var _63=_60+1|0;_5W=_63;return null;}break;case 1:var _64=B(A(_61[1],[_5Z])),_65=_5Z,_63=_60;_5U=_64;_5V=_65;_5W=_63;return null;case 2:return E(_5R);case 3:return function(_66){return new F(function(){return _5K(_60,function(_67){return E(new T(function(){return B(_5w(_61,_66));}));});});};default:return function(_68){return new F(function(){return _5w(_61,_68);});};}})(_5U,_5V,_5W);if(_5X!=null){return _5X;}}},[new T(function(){return B(A(_5Q,[_5I]));}),_5T,0,_5S]);});}];},_69=[6],_6a=new T(function(){return B(unCStr("valDig: Bad base"));}),_6b=new T(function(){return B(err(_6a));}),_6c=function(_6d,_6e){var _6f=function(_6g,_6h){var _6i=E(_6g);if(!_6i[0]){return function(_6j){return new F(function(){return A(_6j,[new T(function(){return B(A(_6h,[_0]));})]);});};}else{var _6k=E(_6i[1])[1],_6l=function(_6m){return function(_6n){return [0,function(_6o){return E(new T(function(){return B(A(new T(function(){return B(_6f(_6i[2],function(_6p){return new F(function(){return A(_6h,[[1,_6m,_6p]]);});}));}),[_6n]));}));}];};};switch(E(E(_6d)[1])){case 8:if(48>_6k){return function(_6q){return new F(function(){return A(_6q,[new T(function(){return B(A(_6h,[_0]));})]);});};}else{if(_6k>55){return function(_6r){return new F(function(){return A(_6r,[new T(function(){return B(A(_6h,[_0]));})]);});};}else{return new F(function(){return _6l([0,_6k-48|0]);});}}break;case 10:if(48>_6k){return function(_6s){return new F(function(){return A(_6s,[new T(function(){return B(A(_6h,[_0]));})]);});};}else{if(_6k>57){return function(_6t){return new F(function(){return A(_6t,[new T(function(){return B(A(_6h,[_0]));})]);});};}else{return new F(function(){return _6l([0,_6k-48|0]);});}}break;case 16:var _6u=new T(function(){if(97>_6k){if(65>_6k){var _6v=[0];}else{if(_6k>70){var _6w=[0];}else{var _6w=[1,[0,(_6k-65|0)+10|0]];}var _6v=_6w;}var _6x=_6v;}else{if(_6k>102){if(65>_6k){var _6y=[0];}else{if(_6k>70){var _6z=[0];}else{var _6z=[1,[0,(_6k-65|0)+10|0]];}var _6y=_6z;}var _6A=_6y;}else{var _6A=[1,[0,(_6k-97|0)+10|0]];}var _6x=_6A;}return _6x;});if(48>_6k){var _6B=E(_6u);if(!_6B[0]){return function(_6C){return new F(function(){return A(_6C,[new T(function(){return B(A(_6h,[_0]));})]);});};}else{return new F(function(){return _6l(_6B[1]);});}}else{if(_6k>57){var _6D=E(_6u);if(!_6D[0]){return function(_6E){return new F(function(){return A(_6E,[new T(function(){return B(A(_6h,[_0]));})]);});};}else{return new F(function(){return _6l(_6D[1]);});}}else{return new F(function(){return _6l([0,_6k-48|0]);});}}break;default:return E(_6b);}}};return [1,function(_6F){return new F(function(){return A(_6f,[_6F,_1L,function(_6G){var _6H=E(_6G);return _6H[0]==0?[2]:B(A(_6e,[_6H]));}]);});}];},_6I=[0,10],_6J=[0,1],_6K=[0,2147483647],_6L=function(_6M,_6N){while(1){var _6O=E(_6M);if(!_6O[0]){var _6P=_6O[1],_6Q=E(_6N);if(!_6Q[0]){var _6R=_6Q[1],_6S=addC(_6P,_6R);if(!E(_6S[2])){return [0,_6S[1]];}else{_6M=[1,I_fromInt(_6P)];_6N=[1,I_fromInt(_6R)];continue;}}else{_6M=[1,I_fromInt(_6P)];_6N=_6Q;continue;}}else{var _6T=E(_6N);if(!_6T[0]){_6M=_6O;_6N=[1,I_fromInt(_6T[1])];continue;}else{return [1,I_add(_6O[1],_6T[1])];}}}},_6U=new T(function(){return B(_6L(_6K,_6J));}),_6V=function(_6W){var _6X=E(_6W);if(!_6X[0]){var _6Y=E(_6X[1]);return _6Y==(-2147483648)?E(_6U):[0, -_6Y];}else{return [1,I_negate(_6X[1])];}},_6Z=[0,10],_70=[0,0],_71=function(_72){return [0,_72];},_73=function(_74,_75){while(1){var _76=E(_74);if(!_76[0]){var _77=_76[1],_78=E(_75);if(!_78[0]){var _79=_78[1];if(!(imul(_77,_79)|0)){return [0,imul(_77,_79)|0];}else{_74=[1,I_fromInt(_77)];_75=[1,I_fromInt(_79)];continue;}}else{_74=[1,I_fromInt(_77)];_75=_78;continue;}}else{var _7a=E(_75);if(!_7a[0]){_74=_76;_75=[1,I_fromInt(_7a[1])];continue;}else{return [1,I_mul(_76[1],_7a[1])];}}}},_7b=function(_7c,_7d,_7e){while(1){var _7f=E(_7e);if(!_7f[0]){return E(_7d);}else{var _7g=B(_6L(B(_73(_7d,_7c)),B(_71(E(_7f[1])[1]))));_7e=_7f[2];_7d=_7g;continue;}}},_7h=function(_7i){var _7j=new T(function(){return B(_4x(B(_4x([0,function(_7k){if(E(E(_7k)[1])==45){return new F(function(){return _6c(_6I,function(_7l){return new F(function(){return A(_7i,[[1,new T(function(){return B(_6V(B(_7b(_6Z,_70,_7l))));})]]);});});});}else{return [2];}}],[0,function(_7m){if(E(E(_7m)[1])==43){return new F(function(){return _6c(_6I,function(_7n){return new F(function(){return A(_7i,[[1,new T(function(){return B(_7b(_6Z,_70,_7n));})]]);});});});}else{return [2];}}])),new T(function(){return B(_6c(_6I,function(_7o){return new F(function(){return A(_7i,[[1,new T(function(){return B(_7b(_6Z,_70,_7o));})]]);});}));})));});return new F(function(){return _4x([0,function(_7p){return E(E(_7p)[1])==101?E(_7j):[2];}],[0,function(_7q){return E(E(_7q)[1])==69?E(_7j):[2];}]);});},_7r=[0],_7s=function(_7t){return new F(function(){return A(_7t,[_7r]);});},_7u=function(_7v){return new F(function(){return A(_7v,[_7r]);});},_7w=function(_7x){return [0,function(_7y){return E(E(_7y)[1])==46?E(new T(function(){return B(_6c(_6I,function(_7z){return new F(function(){return A(_7x,[[1,_7z]]);});}));})):[2];}];},_7A=function(_7B){return new F(function(){return _6c(_6I,function(_7C){return new F(function(){return _5P(_7w,_7s,function(_7D){return new F(function(){return _5P(_7h,_7u,function(_7E){return new F(function(){return A(_7B,[[5,[1,_7C,_7D,_7E]]]);});});});});});});});},_7F=function(_7G,_7H,_7I){while(1){var _7J=E(_7I);if(!_7J[0]){return false;}else{if(!B(A(_5f,[_7G,_7H,_7J[1]]))){_7I=_7J[2];continue;}else{return true;}}}},_7K=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_7L=function(_7M){return new F(function(){return _7F(_5e,_7M,_7K);});},_7N=[0,8],_7O=[0,16],_7P=function(_7Q){return [0,function(_7R){return E(E(_7R)[1])==48?E([0,function(_7S){switch(E(E(_7S)[1])){case 79:return E(new T(function(){return B(_6c(_7N,function(_7T){return new F(function(){return A(_7Q,[[5,[0,_7N,_7T]]]);});}));}));case 88:return E(new T(function(){return B(_6c(_7O,function(_7U){return new F(function(){return A(_7Q,[[5,[0,_7O,_7U]]]);});}));}));case 111:return E(new T(function(){return B(_6c(_7N,function(_7V){return new F(function(){return A(_7Q,[[5,[0,_7N,_7V]]]);});}));}));case 120:return E(new T(function(){return B(_6c(_7O,function(_7W){return new F(function(){return A(_7Q,[[5,[0,_7O,_7W]]]);});}));}));default:return [2];}}]):[2];}];},_7X=false,_7Y=true,_7Z=function(_80){return [0,function(_81){switch(E(E(_81)[1])){case 79:return E(new T(function(){return B(A(_80,[_7N]));}));case 88:return E(new T(function(){return B(A(_80,[_7O]));}));case 111:return E(new T(function(){return B(A(_80,[_7N]));}));case 120:return E(new T(function(){return B(A(_80,[_7O]));}));default:return [2];}}];},_82=function(_83){return new F(function(){return A(_83,[_6I]);});},_84=function(_85){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_1F(9,_85,_0));}))));});},_86=function(_87){var _88=E(_87);return _88[0]==0?E(_88[1]):I_toInt(_88[1]);},_89=function(_8a,_8b){var _8c=E(_8a);if(!_8c[0]){var _8d=_8c[1],_8e=E(_8b);return _8e[0]==0?_8d<=_8e[1]:I_compareInt(_8e[1],_8d)>=0;}else{var _8f=_8c[1],_8g=E(_8b);return _8g[0]==0?I_compareInt(_8f,_8g[1])<=0:I_compare(_8f,_8g[1])<=0;}},_8h=function(_8i){return [2];},_8j=function(_8k){var _8l=E(_8k);if(!_8l[0]){return E(_8h);}else{var _8m=_8l[1],_8n=E(_8l[2]);return _8n[0]==0?E(_8m):function(_8o){return new F(function(){return _4x(B(A(_8m,[_8o])),new T(function(){return B(A(new T(function(){return B(_8j(_8n));}),[_8o]));}));});};}},_8p=new T(function(){return B(unCStr("NUL"));}),_8q=function(_8r){return [2];},_8s=function(_8t){return new F(function(){return _8q(_8t);});},_8u=function(_8v,_8w){var _8x=function(_8y,_8z){var _8A=E(_8y);if(!_8A[0]){return function(_8B){return new F(function(){return A(_8B,[_8v]);});};}else{var _8C=E(_8z);return _8C[0]==0?E(_8q):E(_8A[1])[1]!=E(_8C[1])[1]?E(_8s):function(_8D){return [0,function(_8E){return E(new T(function(){return B(A(new T(function(){return B(_8x(_8A[2],_8C[2]));}),[_8D]));}));}];};}};return [1,function(_8F){return new F(function(){return A(_8x,[_8v,_8F,_8w]);});}];},_8G=[0,0],_8H=function(_8I){return new F(function(){return _8u(_8p,function(_8J){return E(new T(function(){return B(A(_8I,[_8G]));}));});});},_8K=new T(function(){return B(unCStr("STX"));}),_8L=[0,2],_8M=function(_8N){return new F(function(){return _8u(_8K,function(_8O){return E(new T(function(){return B(A(_8N,[_8L]));}));});});},_8P=new T(function(){return B(unCStr("ETX"));}),_8Q=[0,3],_8R=function(_8S){return new F(function(){return _8u(_8P,function(_8T){return E(new T(function(){return B(A(_8S,[_8Q]));}));});});},_8U=new T(function(){return B(unCStr("EOT"));}),_8V=[0,4],_8W=function(_8X){return new F(function(){return _8u(_8U,function(_8Y){return E(new T(function(){return B(A(_8X,[_8V]));}));});});},_8Z=new T(function(){return B(unCStr("ENQ"));}),_90=[0,5],_91=function(_92){return new F(function(){return _8u(_8Z,function(_93){return E(new T(function(){return B(A(_92,[_90]));}));});});},_94=new T(function(){return B(unCStr("ACK"));}),_95=[0,6],_96=function(_97){return new F(function(){return _8u(_94,function(_98){return E(new T(function(){return B(A(_97,[_95]));}));});});},_99=new T(function(){return B(unCStr("BEL"));}),_9a=[0,7],_9b=function(_9c){return new F(function(){return _8u(_99,function(_9d){return E(new T(function(){return B(A(_9c,[_9a]));}));});});},_9e=new T(function(){return B(unCStr("BS"));}),_9f=[0,8],_9g=function(_9h){return new F(function(){return _8u(_9e,function(_9i){return E(new T(function(){return B(A(_9h,[_9f]));}));});});},_9j=new T(function(){return B(unCStr("HT"));}),_9k=[0,9],_9l=function(_9m){return new F(function(){return _8u(_9j,function(_9n){return E(new T(function(){return B(A(_9m,[_9k]));}));});});},_9o=new T(function(){return B(unCStr("LF"));}),_9p=[0,10],_9q=function(_9r){return new F(function(){return _8u(_9o,function(_9s){return E(new T(function(){return B(A(_9r,[_9p]));}));});});},_9t=new T(function(){return B(unCStr("VT"));}),_9u=[0,11],_9v=function(_9w){return new F(function(){return _8u(_9t,function(_9x){return E(new T(function(){return B(A(_9w,[_9u]));}));});});},_9y=new T(function(){return B(unCStr("FF"));}),_9z=[0,12],_9A=function(_9B){return new F(function(){return _8u(_9y,function(_9C){return E(new T(function(){return B(A(_9B,[_9z]));}));});});},_9D=new T(function(){return B(unCStr("CR"));}),_9E=[0,13],_9F=function(_9G){return new F(function(){return _8u(_9D,function(_9H){return E(new T(function(){return B(A(_9G,[_9E]));}));});});},_9I=new T(function(){return B(unCStr("SI"));}),_9J=[0,15],_9K=function(_9L){return new F(function(){return _8u(_9I,function(_9M){return E(new T(function(){return B(A(_9L,[_9J]));}));});});},_9N=new T(function(){return B(unCStr("DLE"));}),_9O=[0,16],_9P=function(_9Q){return new F(function(){return _8u(_9N,function(_9R){return E(new T(function(){return B(A(_9Q,[_9O]));}));});});},_9S=new T(function(){return B(unCStr("DC1"));}),_9T=[0,17],_9U=function(_9V){return new F(function(){return _8u(_9S,function(_9W){return E(new T(function(){return B(A(_9V,[_9T]));}));});});},_9X=new T(function(){return B(unCStr("DC2"));}),_9Y=[0,18],_9Z=function(_a0){return new F(function(){return _8u(_9X,function(_a1){return E(new T(function(){return B(A(_a0,[_9Y]));}));});});},_a2=new T(function(){return B(unCStr("DC3"));}),_a3=[0,19],_a4=function(_a5){return new F(function(){return _8u(_a2,function(_a6){return E(new T(function(){return B(A(_a5,[_a3]));}));});});},_a7=new T(function(){return B(unCStr("DC4"));}),_a8=[0,20],_a9=function(_aa){return new F(function(){return _8u(_a7,function(_ab){return E(new T(function(){return B(A(_aa,[_a8]));}));});});},_ac=new T(function(){return B(unCStr("NAK"));}),_ad=[0,21],_ae=function(_af){return new F(function(){return _8u(_ac,function(_ag){return E(new T(function(){return B(A(_af,[_ad]));}));});});},_ah=new T(function(){return B(unCStr("SYN"));}),_ai=[0,22],_aj=function(_ak){return new F(function(){return _8u(_ah,function(_al){return E(new T(function(){return B(A(_ak,[_ai]));}));});});},_am=new T(function(){return B(unCStr("ETB"));}),_an=[0,23],_ao=function(_ap){return new F(function(){return _8u(_am,function(_aq){return E(new T(function(){return B(A(_ap,[_an]));}));});});},_ar=new T(function(){return B(unCStr("CAN"));}),_as=[0,24],_at=function(_au){return new F(function(){return _8u(_ar,function(_av){return E(new T(function(){return B(A(_au,[_as]));}));});});},_aw=new T(function(){return B(unCStr("EM"));}),_ax=[0,25],_ay=function(_az){return new F(function(){return _8u(_aw,function(_aA){return E(new T(function(){return B(A(_az,[_ax]));}));});});},_aB=new T(function(){return B(unCStr("SUB"));}),_aC=[0,26],_aD=function(_aE){return new F(function(){return _8u(_aB,function(_aF){return E(new T(function(){return B(A(_aE,[_aC]));}));});});},_aG=new T(function(){return B(unCStr("ESC"));}),_aH=[0,27],_aI=function(_aJ){return new F(function(){return _8u(_aG,function(_aK){return E(new T(function(){return B(A(_aJ,[_aH]));}));});});},_aL=new T(function(){return B(unCStr("FS"));}),_aM=[0,28],_aN=function(_aO){return new F(function(){return _8u(_aL,function(_aP){return E(new T(function(){return B(A(_aO,[_aM]));}));});});},_aQ=new T(function(){return B(unCStr("GS"));}),_aR=[0,29],_aS=function(_aT){return new F(function(){return _8u(_aQ,function(_aU){return E(new T(function(){return B(A(_aT,[_aR]));}));});});},_aV=new T(function(){return B(unCStr("RS"));}),_aW=[0,30],_aX=function(_aY){return new F(function(){return _8u(_aV,function(_aZ){return E(new T(function(){return B(A(_aY,[_aW]));}));});});},_b0=new T(function(){return B(unCStr("US"));}),_b1=[0,31],_b2=function(_b3){return new F(function(){return _8u(_b0,function(_b4){return E(new T(function(){return B(A(_b3,[_b1]));}));});});},_b5=new T(function(){return B(unCStr("SP"));}),_b6=[0,32],_b7=function(_b8){return new F(function(){return _8u(_b5,function(_b9){return E(new T(function(){return B(A(_b8,[_b6]));}));});});},_ba=new T(function(){return B(unCStr("DEL"));}),_bb=[0,127],_bc=function(_bd){return new F(function(){return _8u(_ba,function(_be){return E(new T(function(){return B(A(_bd,[_bb]));}));});});},_bf=[1,_bc,_0],_bg=[1,_b7,_bf],_bh=[1,_b2,_bg],_bi=[1,_aX,_bh],_bj=[1,_aS,_bi],_bk=[1,_aN,_bj],_bl=[1,_aI,_bk],_bm=[1,_aD,_bl],_bn=[1,_ay,_bm],_bo=[1,_at,_bn],_bp=[1,_ao,_bo],_bq=[1,_aj,_bp],_br=[1,_ae,_bq],_bs=[1,_a9,_br],_bt=[1,_a4,_bs],_bu=[1,_9Z,_bt],_bv=[1,_9U,_bu],_bw=[1,_9P,_bv],_bx=[1,_9K,_bw],_by=[1,_9F,_bx],_bz=[1,_9A,_by],_bA=[1,_9v,_bz],_bB=[1,_9q,_bA],_bC=[1,_9l,_bB],_bD=[1,_9g,_bC],_bE=[1,_9b,_bD],_bF=[1,_96,_bE],_bG=[1,_91,_bF],_bH=[1,_8W,_bG],_bI=[1,_8R,_bH],_bJ=[1,_8M,_bI],_bK=[1,_8H,_bJ],_bL=new T(function(){return B(unCStr("SOH"));}),_bM=[0,1],_bN=function(_bO){return new F(function(){return _8u(_bL,function(_bP){return E(new T(function(){return B(A(_bO,[_bM]));}));});});},_bQ=new T(function(){return B(unCStr("SO"));}),_bR=[0,14],_bS=function(_bT){return new F(function(){return _8u(_bQ,function(_bU){return E(new T(function(){return B(A(_bT,[_bR]));}));});});},_bV=function(_bW){return new F(function(){return _5P(_bN,_bS,_bW);});},_bX=[1,_bV,_bK],_bY=new T(function(){return B(_8j(_bX));}),_bZ=[0,1114111],_c0=[0,34],_c1=[0,_c0,_7Y],_c2=[0,39],_c3=[0,_c2,_7Y],_c4=[0,92],_c5=[0,_c4,_7Y],_c6=[0,_9a,_7Y],_c7=[0,_9f,_7Y],_c8=[0,_9z,_7Y],_c9=[0,_9p,_7Y],_ca=[0,_9E,_7Y],_cb=[0,_9k,_7Y],_cc=[0,_9u,_7Y],_cd=[0,_8G,_7Y],_ce=[0,_bM,_7Y],_cf=[0,_8L,_7Y],_cg=[0,_8Q,_7Y],_ch=[0,_8V,_7Y],_ci=[0,_90,_7Y],_cj=[0,_95,_7Y],_ck=[0,_9a,_7Y],_cl=[0,_9f,_7Y],_cm=[0,_9k,_7Y],_cn=[0,_9p,_7Y],_co=[0,_9u,_7Y],_cp=[0,_9z,_7Y],_cq=[0,_9E,_7Y],_cr=[0,_bR,_7Y],_cs=[0,_9J,_7Y],_ct=[0,_9O,_7Y],_cu=[0,_9T,_7Y],_cv=[0,_9Y,_7Y],_cw=[0,_a3,_7Y],_cx=[0,_a8,_7Y],_cy=[0,_ad,_7Y],_cz=[0,_ai,_7Y],_cA=[0,_an,_7Y],_cB=[0,_as,_7Y],_cC=[0,_ax,_7Y],_cD=[0,_aC,_7Y],_cE=[0,_aH,_7Y],_cF=[0,_aM,_7Y],_cG=[0,_aR,_7Y],_cH=[0,_aW,_7Y],_cI=[0,_b1,_7Y],_cJ=function(_cK){return new F(function(){return _4x([0,function(_cL){switch(E(E(_cL)[1])){case 34:return E(new T(function(){return B(A(_cK,[_c1]));}));case 39:return E(new T(function(){return B(A(_cK,[_c3]));}));case 92:return E(new T(function(){return B(A(_cK,[_c5]));}));case 97:return E(new T(function(){return B(A(_cK,[_c6]));}));case 98:return E(new T(function(){return B(A(_cK,[_c7]));}));case 102:return E(new T(function(){return B(A(_cK,[_c8]));}));case 110:return E(new T(function(){return B(A(_cK,[_c9]));}));case 114:return E(new T(function(){return B(A(_cK,[_ca]));}));case 116:return E(new T(function(){return B(A(_cK,[_cb]));}));case 118:return E(new T(function(){return B(A(_cK,[_cc]));}));default:return [2];}}],new T(function(){return B(_4x(B(_5P(_7Z,_82,function(_cM){return new F(function(){return _6c(_cM,function(_cN){var _cO=B(_7b(new T(function(){return B(_71(E(_cM)[1]));}),_70,_cN));return !B(_89(_cO,_bZ))?[2]:B(A(_cK,[[0,new T(function(){var _cP=B(_86(_cO));if(_cP>>>0>1114111){var _cQ=B(_84(_cP));}else{var _cQ=[0,_cP];}var _cR=_cQ,_cS=_cR;return _cS;}),_7Y]]));});});})),new T(function(){return B(_4x([0,function(_cT){return E(E(_cT)[1])==94?E([0,function(_cU){switch(E(E(_cU)[1])){case 64:return E(new T(function(){return B(A(_cK,[_cd]));}));case 65:return E(new T(function(){return B(A(_cK,[_ce]));}));case 66:return E(new T(function(){return B(A(_cK,[_cf]));}));case 67:return E(new T(function(){return B(A(_cK,[_cg]));}));case 68:return E(new T(function(){return B(A(_cK,[_ch]));}));case 69:return E(new T(function(){return B(A(_cK,[_ci]));}));case 70:return E(new T(function(){return B(A(_cK,[_cj]));}));case 71:return E(new T(function(){return B(A(_cK,[_ck]));}));case 72:return E(new T(function(){return B(A(_cK,[_cl]));}));case 73:return E(new T(function(){return B(A(_cK,[_cm]));}));case 74:return E(new T(function(){return B(A(_cK,[_cn]));}));case 75:return E(new T(function(){return B(A(_cK,[_co]));}));case 76:return E(new T(function(){return B(A(_cK,[_cp]));}));case 77:return E(new T(function(){return B(A(_cK,[_cq]));}));case 78:return E(new T(function(){return B(A(_cK,[_cr]));}));case 79:return E(new T(function(){return B(A(_cK,[_cs]));}));case 80:return E(new T(function(){return B(A(_cK,[_ct]));}));case 81:return E(new T(function(){return B(A(_cK,[_cu]));}));case 82:return E(new T(function(){return B(A(_cK,[_cv]));}));case 83:return E(new T(function(){return B(A(_cK,[_cw]));}));case 84:return E(new T(function(){return B(A(_cK,[_cx]));}));case 85:return E(new T(function(){return B(A(_cK,[_cy]));}));case 86:return E(new T(function(){return B(A(_cK,[_cz]));}));case 87:return E(new T(function(){return B(A(_cK,[_cA]));}));case 88:return E(new T(function(){return B(A(_cK,[_cB]));}));case 89:return E(new T(function(){return B(A(_cK,[_cC]));}));case 90:return E(new T(function(){return B(A(_cK,[_cD]));}));case 91:return E(new T(function(){return B(A(_cK,[_cE]));}));case 92:return E(new T(function(){return B(A(_cK,[_cF]));}));case 93:return E(new T(function(){return B(A(_cK,[_cG]));}));case 94:return E(new T(function(){return B(A(_cK,[_cH]));}));case 95:return E(new T(function(){return B(A(_cK,[_cI]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_bY,[function(_cV){return new F(function(){return A(_cK,[[0,_cV,_7Y]]);});}]));})));})));}));});},_cW=function(_cX){return new F(function(){return A(_cX,[_1k]);});},_cY=function(_cZ){var _d0=E(_cZ);if(!_d0[0]){return E(_cW);}else{var _d1=_d0[2],_d2=E(E(_d0[1])[1]);switch(_d2){case 9:return function(_d3){return [0,function(_d4){return E(new T(function(){return B(A(new T(function(){return B(_cY(_d1));}),[_d3]));}));}];};case 10:return function(_d5){return [0,function(_d6){return E(new T(function(){return B(A(new T(function(){return B(_cY(_d1));}),[_d5]));}));}];};case 11:return function(_d7){return [0,function(_d8){return E(new T(function(){return B(A(new T(function(){return B(_cY(_d1));}),[_d7]));}));}];};case 12:return function(_d9){return [0,function(_da){return E(new T(function(){return B(A(new T(function(){return B(_cY(_d1));}),[_d9]));}));}];};case 13:return function(_db){return [0,function(_dc){return E(new T(function(){return B(A(new T(function(){return B(_cY(_d1));}),[_db]));}));}];};case 32:return function(_dd){return [0,function(_de){return E(new T(function(){return B(A(new T(function(){return B(_cY(_d1));}),[_dd]));}));}];};case 160:return function(_df){return [0,function(_dg){return E(new T(function(){return B(A(new T(function(){return B(_cY(_d1));}),[_df]));}));}];};default:var _dh=u_iswspace(_d2),_di=_dh;return E(_di)==0?E(_cW):function(_dj){return [0,function(_dk){return E(new T(function(){return B(A(new T(function(){return B(_cY(_d1));}),[_dj]));}));}];};}}},_dl=function(_dm){var _dn=new T(function(){return B(_dl(_dm));}),_do=[1,function(_dp){return new F(function(){return A(_cY,[_dp,function(_dq){return E([0,function(_dr){return E(E(_dr)[1])==92?E(_dn):[2];}]);}]);});}];return new F(function(){return _4x([0,function(_ds){return E(E(_ds)[1])==92?E([0,function(_dt){var _du=E(E(_dt)[1]);switch(_du){case 9:return E(_do);case 10:return E(_do);case 11:return E(_do);case 12:return E(_do);case 13:return E(_do);case 32:return E(_do);case 38:return E(_dn);case 160:return E(_do);default:var _dv=u_iswspace(_du),_dw=_dv;return E(_dw)==0?[2]:E(_do);}}]):[2];}],[0,function(_dx){var _dy=E(_dx);return E(_dy[1])==92?E(new T(function(){return B(_cJ(_dm));})):B(A(_dm,[[0,_dy,_7X]]));}]);});},_dz=function(_dA,_dB){return new F(function(){return _dl(function(_dC){var _dD=E(_dC),_dE=E(_dD[1]);if(E(_dE[1])==34){if(!E(_dD[2])){return E(new T(function(){return B(A(_dB,[[1,new T(function(){return B(A(_dA,[_0]));})]]));}));}else{return new F(function(){return _dz(function(_dF){return new F(function(){return A(_dA,[[1,_dE,_dF]]);});},_dB);});}}else{return new F(function(){return _dz(function(_dG){return new F(function(){return A(_dA,[[1,_dE,_dG]]);});},_dB);});}});});},_dH=new T(function(){return B(unCStr("_\'"));}),_dI=function(_dJ){var _dK=u_iswalnum(_dJ),_dL=_dK;return E(_dL)==0?B(_7F(_5e,[0,_dJ],_dH)):true;},_dM=function(_dN){return new F(function(){return _dI(E(_dN)[1]);});},_dO=new T(function(){return B(unCStr(",;()[]{}`"));}),_dP=function(_dQ){return new F(function(){return A(_dQ,[_0]);});},_dR=function(_dS,_dT){var _dU=function(_dV){var _dW=E(_dV);if(!_dW[0]){return E(_dP);}else{var _dX=_dW[1];return !B(A(_dS,[_dX]))?E(_dP):function(_dY){return [0,function(_dZ){return E(new T(function(){return B(A(new T(function(){return B(_dU(_dW[2]));}),[function(_e0){return new F(function(){return A(_dY,[[1,_dX,_e0]]);});}]));}));}];};}};return [1,function(_e1){return new F(function(){return A(_dU,[_e1,_dT]);});}];},_e2=new T(function(){return B(unCStr(".."));}),_e3=new T(function(){return B(unCStr("::"));}),_e4=new T(function(){return B(unCStr("->"));}),_e5=[0,64],_e6=[1,_e5,_0],_e7=[0,126],_e8=[1,_e7,_0],_e9=new T(function(){return B(unCStr("=>"));}),_ea=[1,_e9,_0],_eb=[1,_e8,_ea],_ec=[1,_e6,_eb],_ed=[1,_e4,_ec],_ee=new T(function(){return B(unCStr("<-"));}),_ef=[1,_ee,_ed],_eg=[0,124],_eh=[1,_eg,_0],_ei=[1,_eh,_ef],_ej=[1,_c4,_0],_ek=[1,_ej,_ei],_el=[0,61],_em=[1,_el,_0],_en=[1,_em,_ek],_eo=[1,_e3,_en],_ep=[1,_e2,_eo],_eq=function(_er){return new F(function(){return _4x([1,function(_es){return E(_es)[0]==0?E(new T(function(){return B(A(_er,[_69]));})):[2];}],new T(function(){return B(_4x([0,function(_et){return E(E(_et)[1])==39?E([0,function(_eu){var _ev=E(_eu);switch(E(_ev[1])){case 39:return [2];case 92:return E(new T(function(){return B(_cJ(function(_ew){var _ex=E(_ew);return new F(function(){return (function(_ey,_ez){var _eA=new T(function(){return B(A(_er,[[0,_ey]]));});return !E(_ez)?E(E(_ey)[1])==39?[2]:[0,function(_eB){return E(E(_eB)[1])==39?E(_eA):[2];}]:[0,function(_eC){return E(E(_eC)[1])==39?E(_eA):[2];}];})(_ex[1],_ex[2]);});}));}));default:return [0,function(_eD){return E(E(_eD)[1])==39?E(new T(function(){return B(A(_er,[[0,_ev]]));})):[2];}];}}]):[2];}],new T(function(){return B(_4x([0,function(_eE){return E(E(_eE)[1])==34?E(new T(function(){return B(_dz(_1L,_er));})):[2];}],new T(function(){return B(_4x([0,function(_eF){return !B(_7F(_5e,_eF,_dO))?[2]:B(A(_er,[[2,[1,_eF,_0]]]));}],new T(function(){return B(_4x([0,function(_eG){if(!B(_7F(_5e,_eG,_7K))){return [2];}else{return new F(function(){return _dR(_7L,function(_eH){var _eI=[1,_eG,_eH];return !B(_7F(_5v,_eI,_ep))?B(A(_er,[[4,_eI]])):B(A(_er,[[2,_eI]]));});});}}],new T(function(){return B(_4x([0,function(_eJ){var _eK=E(_eJ),_eL=_eK[1],_eM=u_iswalpha(_eL),_eN=_eM;if(!E(_eN)){if(E(_eL)==95){return new F(function(){return _dR(_dM,function(_eO){return new F(function(){return A(_er,[[3,[1,_eK,_eO]]]);});});});}else{return [2];}}else{return new F(function(){return _dR(_dM,function(_eP){return new F(function(){return A(_er,[[3,[1,_eK,_eP]]]);});});});}}],new T(function(){return B(_5P(_7P,_7A,_er));})));})));})));})));})));}));});},_eQ=function(_eR){return [1,function(_eS){return new F(function(){return A(_cY,[_eS,function(_eT){return E(new T(function(){return B(_eq(_eR));}));}]);});}];},_eU=[0,0],_eV=function(_eW,_eX){return new F(function(){return _eQ(function(_eY){var _eZ=E(_eY);if(_eZ[0]==2){var _f0=E(_eZ[1]);return _f0[0]==0?[2]:E(E(_f0[1])[1])==40?E(_f0[2])[0]==0?E(new T(function(){return B(A(_eW,[_eU,function(_f1){return new F(function(){return _eQ(function(_f2){var _f3=E(_f2);if(_f3[0]==2){var _f4=E(_f3[1]);return _f4[0]==0?[2]:E(E(_f4[1])[1])==41?E(_f4[2])[0]==0?E(new T(function(){return B(A(_eX,[_f1]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_f5=function(_f6,_f7,_f8){var _f9=function(_fa,_fb){return new F(function(){return _4x(B(_eQ(function(_fc){var _fd=E(_fc);if(_fd[0]==4){var _fe=E(_fd[1]);if(!_fe[0]){return new F(function(){return A(_f6,[_fd,_fa,_fb]);});}else{return E(E(_fe[1])[1])==45?E(_fe[2])[0]==0?E([1,function(_ff){return new F(function(){return A(_cY,[_ff,function(_fg){return E(new T(function(){return B(_eq(function(_fh){return new F(function(){return A(_f6,[_fh,_fa,function(_fi){return new F(function(){return A(_fb,[new T(function(){return [0, -E(_fi)[1]];})]);});}]);});}));}));}]);});}]):B(A(_f6,[_fd,_fa,_fb])):B(A(_f6,[_fd,_fa,_fb]));}}else{return new F(function(){return A(_f6,[_fd,_fa,_fb]);});}})),new T(function(){return B(_eV(_f9,_fb));}));});};return new F(function(){return _f9(_f7,_f8);});},_fj=function(_fk,_fl){return [2];},_fm=function(_fn,_fo){return new F(function(){return _fj(_fn,_fo);});},_fp=function(_fq){var _fr=E(_fq);return _fr[0]==0?[1,new T(function(){return B(_7b(new T(function(){return B(_71(E(_fr[1])[1]));}),_70,_fr[2]));})]:E(_fr[2])[0]==0?E(_fr[3])[0]==0?[1,new T(function(){return B(_7b(_6Z,_70,_fr[1]));})]:[0]:[0];},_fs=function(_ft){var _fu=E(_ft);if(_fu[0]==5){var _fv=B(_fp(_fu[1]));return _fv[0]==0?E(_fj):function(_fw,_fx){return new F(function(){return A(_fx,[new T(function(){return [0,B(_86(_fv[1]))];})]);});};}else{return E(_fm);}},_fy=function(_fz){return [1,function(_fA){return new F(function(){return A(_cY,[_fA,function(_fB){return E([3,_fz,_5H]);}]);});}];},_fC=new T(function(){return B(_f5(_fs,_eU,_fy));}),_fD=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_fE=new T(function(){return B(err(_fD));}),_fF=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_fG=new T(function(){return B(err(_fF));}),_fH=function(_fI,_fJ,_fK){return _fK<=_fJ?[1,[0,_fI],new T(function(){var _fL=_fJ-_fI|0,_fM=function(_fN){return _fN>=(_fK-_fL|0)?[1,[0,_fN],new T(function(){return B(_fM(_fN+_fL|0));})]:[1,[0,_fN],_0];};return B(_fM(_fJ));})]:_fK<=_fI?[1,[0,_fI],_0]:[0];},_fO=function(_fP,_fQ,_fR){return _fR>=_fQ?[1,[0,_fP],new T(function(){var _fS=_fQ-_fP|0,_fT=function(_fU){return _fU<=(_fR-_fS|0)?[1,[0,_fU],new T(function(){return B(_fT(_fU+_fS|0));})]:[1,[0,_fU],_0];};return B(_fT(_fQ));})]:_fR>=_fP?[1,[0,_fP],_0]:[0];},_fV=function(_fW,_fX){return _fX<_fW?B(_fH(_fW,_fX,-2147483648)):B(_fO(_fW,_fX,2147483647));},_fY=new T(function(){return B(_fV(135,150));}),_fZ=function(_g0,_g1){var _g2=E(_g0);if(!_g2){return [0];}else{var _g3=E(_g1);return _g3[0]==0?[0]:[1,_g3[1],new T(function(){return B(_fZ(_g2-1|0,_g3[2]));})];}},_g4=new T(function(){return B(_fZ(6,_fY));}),_g5=function(_g6,_g7){var _g8=E(_g6);if(!_g8[0]){return E(_g4);}else{var _g9=_g8[1];return _g7>1?[1,_g9,new T(function(){return B(_g5(_g8[2],_g7-1|0));})]:[1,_g9,_g4];}},_ga=new T(function(){return B(_fV(25,40));}),_gb=new T(function(){return B(_g5(_ga,6));}),_gc=function(_gd){while(1){var _ge=(function(_gf){var _gg=E(_gf);if(!_gg[0]){return [0];}else{var _gh=_gg[2],_gi=E(_gg[1]);if(!E(_gi[2])[0]){return [1,_gi[1],new T(function(){return B(_gc(_gh));})];}else{_gd=_gh;return null;}}})(_gd);if(_ge!=null){return _ge;}}},_gj=function(_gk,_gl){var _gm=E(_gl);if(!_gm[0]){return [0,_0,_0];}else{var _gn=_gm[1];if(!B(A(_gk,[_gn]))){var _go=new T(function(){var _gp=B(_gj(_gk,_gm[2]));return [0,_gp[1],_gp[2]];});return [0,[1,_gn,new T(function(){return E(E(_go)[1]);})],new T(function(){return E(E(_go)[2]);})];}else{return [0,_0,_gm];}}},_gq=function(_gr,_gs){while(1){var _gt=E(_gs);if(!_gt[0]){return [0];}else{if(!B(A(_gr,[_gt[1]]))){return E(_gt);}else{_gs=_gt[2];continue;}}}},_gu=function(_gv){var _gw=E(_gv);switch(_gw){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _gx=u_iswspace(_gw),_gy=_gx;return E(_gy)==0?false:true;}},_gz=function(_gA){return new F(function(){return _gu(E(_gA)[1]);});},_gB=function(_gC){var _gD=B(_gq(_gz,_gC));if(!_gD[0]){return [0];}else{var _gE=new T(function(){var _gF=B(_gj(_gz,_gD));return [0,_gF[1],_gF[2]];});return [1,new T(function(){return E(E(_gE)[1]);}),new T(function(){return B(_gB(E(_gE)[2]));})];}},_gG=function(_gH,_){var _gI=setDropCheckerCallback_ffi(function(_gJ,_gK,_gL){var _gM=E(_gH),_gN=_gM[1],_gO=_gM[6],_gP=new T(function(){return B(_gB(B(_2R(_gJ))));}),_gQ=new T(function(){var _gR=B(_gc(B(_4n(_fC,new T(function(){return B(_2n(2,B(_1f(_gP,2))));})))));return _gR[0]==0?E(_fG):E(_gR[2])[0]==0?E(_gR[1]):E(_fE);}),_gS=new T(function(){var _gT=B(_gc(B(_4n(_fC,new T(function(){return B(_2n(2,B(_1f(_gP,3))));})))));return _gT[0]==0?E(_fG):E(_gT[2])[0]==0?E(_gT[1]):E(_fE);}),_gU=B(_2y(function(_gV){var _gW=E(_gV)[1]-E(_gK)[1];return _gW<0? -_gW<7:_gW<7;},_gb));if(!_gU[0]){return function(_68){return new F(function(){return _2c(_gQ,_gS,_gQ,_gS,_gO,_68);});};}else{var _gX=_gU[1],_gY=function(_gZ,_h0,_){var _h1=E(_gQ),_h2=_h1[1];if(_gZ<=_h2){return new F(function(){return _2c(_h1,_gS,_h1,_gS,_gO,_);});}else{if(_gZ>=0){var _h3=B(_1f(_gN,_gZ)),_h4=new T(function(){return _h2<0;}),_h5=function(_){var _h6=B(_2c(_h1,_gS,_h0,new T(function(){if(_gZ>=0){var _h7=E(B(_1f(_gN,_gZ))[2]);}else{var _h7=E(_1c);}return _h7;}),_gO,_)),_h8=_h6;if(!E(_h4)){var _h9=new T(function(){return B(_2K(function(_ha,_hb,_hc){return [1,new T(function(){var _hd=E(_ha)[1];return _hd!=_h2?_hd!=_gZ?E(_hb):[0,new T(function(){if(_h2>=0){var _he=E(B(_1f(_gN,_h2))[1]);}else{var _he=E(_1c);}return _he;}),new T(function(){return [0,E(E(_hb)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_hb)[1]);}),new T(function(){return [0,E(E(_hb)[2])[1]-1|0];})];}),_hc];},_0,_2X,_gN));}),_hf=B((function(_hg,_){while(1){var _hh=(function(_hi,_){var _hj=E(_hi);if(!_hj[0]){return _1k;}else{var _hk=_hj[1],_hl=B(_2c(_h1,_hk,_h1,new T(function(){return [0,E(_hk)[1]-1|0];}),_gO,_)),_hm=_hl;_hg=_hj[2];return null;}})(_hg,_);if(_hh!=null){return _hh;}}})(B(_2n(1,B(_2s(E(_gS)[1],E(B(_1f(_h9,_h2))[2])[1])))),_)),_hn=_hf;return new F(function(){return _gG([0,_h9,_gM[2],_gM[3],_gM[4],_gM[5],_gO,_gM[7]],_);});}else{return E(_1c);}},_ho=function(_){return E(_h3[2])[1]>=2?B(_2c(_h1,_gS,_h1,_gS,_gO,_)):B(_h5(_));};switch(E(_h3[1])){case 0:if(!E(_h4)){switch(E(B(_1f(_gN,_h2))[1])){case 0:return new F(function(){return _h5(_);});break;case 1:return new F(function(){return _ho(_);});break;default:return new F(function(){return _ho(_);});}}else{return E(_1c);}break;case 1:return !E(_h4)?E(B(_1f(_gN,_h2))[1])==1?B(_h5(_)):B(_ho(_)):E(_1c);default:return !E(_h4)?E(B(_1f(_gN,_h2))[1])==2?B(_h5(_)):B(_ho(_)):E(_1c);}}else{return E(_1c);}}};if(E(_gL)[1]<=E(_2W)[1]){var _hp=E(_gX);return function(_68){return new F(function(){return _gY(_hp[1],_hp,_68);});};}else{var _hq=23-E(_gX)[1]|0;return function(_68){return new F(function(){return _gY(_hq,[0,_hq],_68);});};}}});return _1k;},_hr=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:136:5-10"));}),_hs=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_ht=new T(function(){return B(unCStr("base"));}),_hu=new T(function(){return B(unCStr("IOException"));}),_hv=new T(function(){var _hw=hs_wordToWord64(4053623282),_hx=_hw,_hy=hs_wordToWord64(3693590983),_hz=_hy;return [0,_hx,_hz,[0,_hx,_hz,_ht,_hs,_hu],_0];}),_hA=function(_hB){return E(_hv);},_hC=function(_hD){var _hE=E(_hD);return new F(function(){return _3c(B(_38(_hE[1])),_hA,_hE[2]);});},_hF=new T(function(){return B(unCStr(": "));}),_hG=[0,41],_hH=new T(function(){return B(unCStr(" ("));}),_hI=new T(function(){return B(unCStr("already exists"));}),_hJ=new T(function(){return B(unCStr("does not exist"));}),_hK=new T(function(){return B(unCStr("protocol error"));}),_hL=new T(function(){return B(unCStr("failed"));}),_hM=new T(function(){return B(unCStr("invalid argument"));}),_hN=new T(function(){return B(unCStr("inappropriate type"));}),_hO=new T(function(){return B(unCStr("hardware fault"));}),_hP=new T(function(){return B(unCStr("unsupported operation"));}),_hQ=new T(function(){return B(unCStr("timeout"));}),_hR=new T(function(){return B(unCStr("resource vanished"));}),_hS=new T(function(){return B(unCStr("interrupted"));}),_hT=new T(function(){return B(unCStr("resource busy"));}),_hU=new T(function(){return B(unCStr("resource exhausted"));}),_hV=new T(function(){return B(unCStr("end of file"));}),_hW=new T(function(){return B(unCStr("illegal operation"));}),_hX=new T(function(){return B(unCStr("permission denied"));}),_hY=new T(function(){return B(unCStr("user error"));}),_hZ=new T(function(){return B(unCStr("unsatisified constraints"));}),_i0=new T(function(){return B(unCStr("system error"));}),_i1=function(_i2,_i3){switch(E(_i2)){case 0:return new F(function(){return _1u(_hI,_i3);});break;case 1:return new F(function(){return _1u(_hJ,_i3);});break;case 2:return new F(function(){return _1u(_hT,_i3);});break;case 3:return new F(function(){return _1u(_hU,_i3);});break;case 4:return new F(function(){return _1u(_hV,_i3);});break;case 5:return new F(function(){return _1u(_hW,_i3);});break;case 6:return new F(function(){return _1u(_hX,_i3);});break;case 7:return new F(function(){return _1u(_hY,_i3);});break;case 8:return new F(function(){return _1u(_hZ,_i3);});break;case 9:return new F(function(){return _1u(_i0,_i3);});break;case 10:return new F(function(){return _1u(_hK,_i3);});break;case 11:return new F(function(){return _1u(_hL,_i3);});break;case 12:return new F(function(){return _1u(_hM,_i3);});break;case 13:return new F(function(){return _1u(_hN,_i3);});break;case 14:return new F(function(){return _1u(_hO,_i3);});break;case 15:return new F(function(){return _1u(_hP,_i3);});break;case 16:return new F(function(){return _1u(_hQ,_i3);});break;case 17:return new F(function(){return _1u(_hR,_i3);});break;default:return new F(function(){return _1u(_hS,_i3);});}},_i4=[0,125],_i5=new T(function(){return B(unCStr("{handle: "));}),_i6=function(_i7,_i8,_i9,_ia,_ib,_ic){var _id=new T(function(){var _ie=new T(function(){return B(_i1(_i8,new T(function(){var _if=E(_ia);return _if[0]==0?E(_ic):B(_1u(_hH,new T(function(){return B(_1u(_if,[1,_hG,_ic]));})));})));}),_ig=E(_i9);return _ig[0]==0?E(_ie):B(_1u(_ig,new T(function(){return B(_1u(_hF,_ie));})));}),_ih=E(_ib);if(!_ih[0]){var _ii=E(_i7);if(!_ii[0]){return E(_id);}else{var _ij=E(_ii[1]);return _ij[0]==0?B(_1u(_i5,new T(function(){return B(_1u(_ij[1],[1,_i4,new T(function(){return B(_1u(_hF,_id));})]));}))):B(_1u(_i5,new T(function(){return B(_1u(_ij[1],[1,_i4,new T(function(){return B(_1u(_hF,_id));})]));})));}}else{return new F(function(){return _1u(_ih[1],new T(function(){return B(_1u(_hF,_id));}));});}},_ik=function(_il){var _im=E(_il);return new F(function(){return _i6(_im[1],_im[2],_im[3],_im[4],_im[6],_0);});},_in=function(_io,_ip){var _iq=E(_io);return new F(function(){return _i6(_iq[1],_iq[2],_iq[3],_iq[4],_iq[6],_ip);});},_ir=function(_is,_it){return new F(function(){return _3C(_in,_is,_it);});},_iu=function(_iv,_iw,_ix){var _iy=E(_iw);return new F(function(){return _i6(_iy[1],_iy[2],_iy[3],_iy[4],_iy[6],_ix);});},_iz=[0,_iu,_ik,_ir],_iA=new T(function(){return [0,_hA,_iz,_iB,_hC];}),_iB=function(_iC){return [0,_iA,_iC];},_iD=7,_iE=function(_iF){return [0,_7r,_iD,_0,_iF,_7r,_7r];},_iG=function(_iH,_){return new F(function(){return die(new T(function(){return B(_iB(new T(function(){return B(_iE(_iH));})));}));});},_iI=function(_iJ,_){return new F(function(){return _iG(_iJ,_);});},_iK=[0,114],_iL=[1,_iK,_0],_iM=new T(function(){return B(_1F(0,6,_0));}),_iN=new T(function(){return B(unCStr("cx"));}),_iO=new T(function(){return B(unCStr("cy"));}),_iP=new T(function(){return B(unCStr("circle"));}),_iQ=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_iR=new T(function(){return B(unCStr("board"));}),_iS=function(_){return _1k;},_iT=function(_iU,_iV,_){while(1){var _iW=(function(_iX,_iY,_){var _iZ=E(_iY);if(!_iZ[0]){return _1k;}else{var _j0=E(_iZ[1]),_j1=_j0[1],_j2=[0,_iX],_j3=B(A(_2K,[function(_j4,_j5,_j6,_){var _j7=jsFind(toJSStr(E(_iR))),_j8=_j7,_j9=E(_j8);if(!_j9[0]){var _ja=B(_iI(_hr,_)),_jb=_ja;return new F(function(){return A(_j6,[_]);});}else{var _jc=jsCreateElemNS(toJSStr(E(_iQ)),toJSStr(E(_iP))),_jd=_jc,_je=[0,_jd],_jf=B(A(_1o,[_1L,_je,_iL,_iM,_])),_jg=_jf,_jh=new T(function(){var _ji=B(_20(_j2,_j4));return [0,_ji[1],_ji[2]];}),_jj=B(A(_1o,[_1L,_je,_iN,new T(function(){return B(_1F(0,E(E(_jh)[1])[1],_0));}),_])),_jk=_jj,_jl=B(A(_1o,[_1L,_je,_iO,new T(function(){return B(_1F(0,E(E(_jh)[2])[1],_0));}),_])),_jm=_jl,_jn=B(A(_1P,[_je,_m,_j2,_j4,_j5,_])),_jo=_jn,_jp=jsAppendChild(_jd,E(_j9[1])[1]);return new F(function(){return A(_j6,[_]);});}},_iS,_2X,new T(function(){var _jq=E(_j0[2])[1];if(_jq>0){var _jr=function(_js){return _js>1?[1,_j1,new T(function(){return B(_jr(_js-1|0));})]:E([1,_j1,_0]);},_jt=B(_jr(_jq));}else{var _jt=[0];}var _ju=_jt;return _ju;}),_])),_jv=_j3,_jw=E(_iX);if(_jw==2147483647){return _1k;}else{_iU=_jw+1|0;_iV=_iZ[2];return null;}}})(_iU,_iV,_);if(_iW!=null){return _iW;}}},_jx=function(_){var _jy=B(_iT(0,_19,_)),_jz=_jy;return new F(function(){return _gG(_1a,_);});},_jA=function(_){return new F(function(){return _jx(_);});};
var hasteMain = function() {B(A(_jA, [0]));};window.onload = hasteMain;