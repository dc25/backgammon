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

var _0=[0],_1=function(_2,_3){while(1){var _4=E(_2);if(!_4[0]){return E(_3);}else{_2=_4[2];var _5=[1,_4[1],_3];_3=_5;continue;}}},_6=[0,2],_7=[0,0],_8=[1,_7,_0],_9=[1,_7,_8],_a=[1,_7,_9],_b=[1,_7,_a],_c=[1,_7,_b],_d=[0,5],_e=[1,_d,_c],_f=[1,_7,_e],_g=[0,3],_h=[1,_g,_f],_i=[1,_7,_h],_j=[1,_7,_i],_k=[1,_7,_j],_l=[1,_7,_k],_m=[1,_d,_l],_n=[1,_7,_m],_o=[1,_7,_n],_p=[1,_7,_o],_q=[1,_7,_p],_r=[1,_7,_q],_s=[1,_7,_r],_t=[1,_7,_s],_u=[1,_7,_t],_v=[1,_7,_u],_w=[1,_7,_v],_x=[1,_6,_w],_y=1,_z=function(_A){var _B=E(_A);return _B[0]==0?[0]:[1,[0,_y,_B[1]],new T(function(){return B(_z(_B[2]));})];},_C=new T(function(){return B(_z(_x));}),_D=new T(function(){return B(_1(_C,_0));}),_E=0,_F=new T(function(){return B(unCStr("Control.Exception.Base"));}),_G=new T(function(){return B(unCStr("base"));}),_H=new T(function(){return B(unCStr("PatternMatchFail"));}),_I=new T(function(){var _J=hs_wordToWord64(18445595),_K=_J,_L=hs_wordToWord64(52003073),_M=_L;return [0,_K,_M,[0,_K,_M,_G,_F,_H],_0];}),_N=function(_O){return E(_I);},_P=function(_Q){return E(E(_Q)[1]);},_R=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_S=new T(function(){return B(err(_R));}),_T=function(_U,_V,_W){var _X=new T(function(){var _Y=B(A(_U,[_W])),_Z=B(A(_V,[new T(function(){var _10=E(_X);return _10[0]==0?E(_S):E(_10[1]);})])),_11=hs_eqWord64(_Y[1],_Z[1]),_12=_11;if(!E(_12)){var _13=[0];}else{var _14=hs_eqWord64(_Y[2],_Z[2]),_15=_14,_13=E(_15)==0?[0]:[1,_W];}var _16=_13,_17=_16;return _17;});return E(_X);},_18=function(_19){var _1a=E(_19);return new F(function(){return _T(B(_P(_1a[1])),_N,_1a[2]);});},_1b=function(_1c){return E(E(_1c)[1]);},_1d=function(_1e,_1f){var _1g=E(_1e);return _1g[0]==0?E(_1f):[1,_1g[1],new T(function(){return B(_1d(_1g[2],_1f));})];},_1h=function(_1i,_1j){return new F(function(){return _1d(E(_1i)[1],_1j);});},_1k=[0,44],_1l=[0,93],_1m=[0,91],_1n=function(_1o,_1p,_1q){var _1r=E(_1p);return _1r[0]==0?B(unAppCStr("[]",_1q)):[1,_1m,new T(function(){return B(A(_1o,[_1r[1],new T(function(){var _1s=function(_1t){var _1u=E(_1t);return _1u[0]==0?E([1,_1l,_1q]):[1,_1k,new T(function(){return B(A(_1o,[_1u[1],new T(function(){return B(_1s(_1u[2]));})]));})];};return B(_1s(_1r[2]));})]));})];},_1v=function(_1w,_1x){return new F(function(){return _1n(_1h,_1w,_1x);});},_1y=function(_1z,_1A,_1B){return new F(function(){return _1d(E(_1A)[1],_1B);});},_1C=[0,_1y,_1b,_1v],_1D=new T(function(){return [0,_N,_1C,_1E,_18];}),_1E=function(_1F){return [0,_1D,_1F];},_1G=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_1H=function(_1I,_1J){return new F(function(){return die(new T(function(){return B(A(_1J,[_1I]));}));});},_1K=function(_1L,_1M){var _1N=E(_1M);if(!_1N[0]){return [0,_0,_0];}else{var _1O=_1N[1];if(!B(A(_1L,[_1O]))){return [0,_0,_1N];}else{var _1P=new T(function(){var _1Q=B(_1K(_1L,_1N[2]));return [0,_1Q[1],_1Q[2]];});return [0,[1,_1O,new T(function(){return E(E(_1P)[1]);})],new T(function(){return E(E(_1P)[2]);})];}}},_1R=[0,32],_1S=[0,10],_1T=[1,_1S,_0],_1U=function(_1V){return E(E(_1V)[1])==124?false:true;},_1W=function(_1X,_1Y){var _1Z=B(_1K(_1U,B(unCStr(_1X)))),_20=_1Z[1],_21=function(_22,_23){return new F(function(){return _1d(_22,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_1d(_1Y,new T(function(){return B(_1d(_23,_1T));})));})));}));});},_24=E(_1Z[2]);if(!_24[0]){return new F(function(){return _21(_20,_0);});}else{return E(E(_24[1])[1])==124?B(_21(_20,[1,_1R,_24[2]])):B(_21(_20,_0));}},_25=function(_26){return new F(function(){return _1H([0,new T(function(){return B(_1W(_26,_1G));})],_1E);});},_27=new T(function(){return B(_25("main.hs:(219,20)-(220,55)|function whiteOrBlack"));}),_28=function(_29,_2a){var _2b=E(_29);if(!_2b[0]){return [0];}else{var _2c=E(_2a);return _2c[0]==0?[0]:[1,new T(function(){var _2d=E(_2c[1]);if(!E(_2d[1])){var _2e=E(_27);}else{if(!E(E(_2d[2])[1])){var _2f=E(_2b[1]),_2g=E(_2f[1])==0?E(_2f):[0,_E,_2f[2]];}else{var _2g=E(_2d);}var _2h=_2g,_2e=_2h;}var _2i=_2e;return _2i;}),new T(function(){return B(_28(_2b[2],_2c[2]));})];}},_2j=new T(function(){return B(_28(_D,_C));}),_2k=[0,_2j,_7,_7,_7,_7,_y,_y],_2l=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_2m=new T(function(){return B(err(_2l));}),_2n=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_2o=new T(function(){return B(err(_2n));}),_2p=function(_2q,_2r){while(1){var _2s=E(_2q);if(!_2s[0]){return E(_2o);}else{var _2t=E(_2r);if(!_2t){return E(_2s[1]);}else{_2q=_2s[2];_2r=_2t-1|0;continue;}}}},_2u=0,_2v=new T(function(){return B(unCStr("White"));}),_2w=new T(function(){return B(unCStr("Black"));}),_2x=function(_2y,_2z,_2A,_2B){return new F(function(){return A(_2y,[new T(function(){return function(_){var _2C=jsSetAttr(E(_2z)[1],toJSStr(E(_2A)),toJSStr(E(_2B)));return _2u;};})]);});},_2D=function(_2E,_2F){var _2G=jsShowI(_2E),_2H=_2G;return new F(function(){return _1d(fromJSStr(_2H),_2F);});},_2I=[0,41],_2J=[0,40],_2K=function(_2L,_2M,_2N){return _2M>=0?B(_2D(_2M,_2N)):_2L<=6?B(_2D(_2M,_2N)):[1,_2J,new T(function(){var _2O=jsShowI(_2M),_2P=_2O;return B(_1d(fromJSStr(_2P),[1,_2I,_2N]));})];},_2Q=function(_2R){return E(_2R);},_2S=new T(function(){return B(unCStr("class"));}),_2T=new T(function(){return B(unCStr("draggable "));}),_2U=function(_2V,_2W,_2X,_2Y,_2Z){return new F(function(){return _2x(_2Q,_2V,_2S,new T(function(){var _30=new T(function(){var _31=new T(function(){return B(unAppCStr(" pi",new T(function(){return B(_1d(B(_2K(0,E(_2X)[1],_0)),new T(function(){return B(unAppCStr(" ci",new T(function(){return B(_2K(0,E(_2Y)[1],_0));})));})));})));});return E(_2Z)==0?B(_1d(_2w,_31)):B(_1d(_2v,_31));});return E(_2W)==0?E(_2Z)==0?B(_1d(_2T,_30)):E(_30):E(_2Z)==0?E(_30):B(_1d(_2T,_30));}));});},_32=function(_33,_34){return [0,new T(function(){var _35=E(_33)[1];if(_35>=12){var _36=23-_35|0;if(_36>=6){var _37=[0,25+(20+(imul(_36,15)|0)|0)|0];}else{var _37=[0,25+(imul(_36,15)|0)|0];}var _38=_37,_39=_38;}else{if(_35>=6){var _3a=[0,25+(20+(imul(_35,15)|0)|0)|0];}else{var _3a=[0,25+(imul(_35,15)|0)|0];}var _39=_3a;}var _3b=_39;return _3b;}),new T(function(){if(E(_33)[1]>=12){var _3c=[0,203+(imul(imul(imul(-1,E(_34)[1])|0,2)|0,6)|0)|0];}else{var _3c=[0,7+(imul(imul(E(_34)[1],2)|0,6)|0)|0];}var _3d=_3c;return _3d;})];},_3e=function(_3f,_3g,_3h,_3i,_3j,_){var _3k=jsElemsByClassName(toJSStr(B(unAppCStr(" pi",new T(function(){return B(_1d(B(_2K(0,E(_3f)[1],_0)),new T(function(){return B(unAppCStr(" ci",new T(function(){return B(_2K(0,E(_3g)[1],_0));})));})));}))))),_3l=_3k,_3m=B(_2p(_3l,0)),_3n=B(_32(_3h,_3i)),_3o=animateCircle_ffi(_3m[1],E(_3n[1])[1],E(_3n[2])[1],300);return new F(function(){return A(_2U,[_3m,_3j,_3h,_3i,_3j,_]);});},_3p=function(_3q,_3r){while(1){var _3s=E(_3q);if(!_3s){return E(_3r);}else{var _3t=E(_3r);if(!_3t[0]){return [0];}else{_3q=_3s-1|0;_3r=_3t[2];continue;}}}},_3u=function(_3v,_3w){if(_3v<=_3w){var _3x=function(_3y){return [1,[0,_3y],new T(function(){if(_3y!=_3w){var _3z=B(_3x(_3y+1|0));}else{var _3z=[0];}return _3z;})];};return new F(function(){return _3x(_3v);});}else{return [0];}},_3A=function(_3B,_3C){var _3D=function(_3E,_3F){while(1){var _3G=(function(_3H,_3I){var _3J=E(_3I);if(!_3J[0]){return [0];}else{var _3K=_3J[2];if(!B(A(_3B,[_3J[1]]))){var _3L=_3H+1|0;_3F=_3K;_3E=_3L;return null;}else{return [1,[0,_3H],new T(function(){return B(_3D(_3H+1|0,_3K));})];}}})(_3E,_3F);if(_3G!=null){return _3G;}}};return new F(function(){return _3D(0,_3C);});},_3M=function(_3N,_3O,_3P,_3Q){var _3R=E(_3P);if(!_3R[0]){return E(_3O);}else{var _3S=E(_3Q);if(!_3S[0]){return E(_3O);}else{return new F(function(){return A(_3N,[_3R[1],_3S[1],new T(function(){return B(_3M(_3N,_3O,_3R[2],_3S[2]));})]);});}}},_3T=function(_3U){return new F(function(){return fromJSStr(E(_3U)[1]);});},_3V=function(_3W,_3X){if(_3W<=0){if(_3W>=0){return new F(function(){return quot(_3W,_3X);});}else{if(_3X<=0){return new F(function(){return quot(_3W,_3X);});}else{return quot(_3W+1|0,_3X)-1|0;}}}else{if(_3X>=0){if(_3W>=0){return new F(function(){return quot(_3W,_3X);});}else{if(_3X<=0){return new F(function(){return quot(_3W,_3X);});}else{return quot(_3W+1|0,_3X)-1|0;}}}else{return quot(_3W-1|0,_3X)-1|0;}}},_3Y=new T(function(){return [0,B(_3V(210,2))];}),_3Z=new T(function(){return B(_3u(0,2147483647));}),_40=new T(function(){return B(_25("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_41=function(_42,_43){while(1){var _44=(function(_45,_46){var _47=E(_45);switch(_47[0]){case 0:var _48=E(_46);if(!_48[0]){return [0];}else{_42=B(A(_47[1],[_48[1]]));_43=_48[2];return null;}break;case 1:var _49=B(A(_47[1],[_46])),_4a=_46;_42=_49;_43=_4a;return null;case 2:return [0];case 3:return [1,[0,_47[1],_46],new T(function(){return B(_41(_47[2],_46));})];default:return E(_47[1]);}})(_42,_43);if(_44!=null){return _44;}}},_4b=function(_4c,_4d){var _4e=new T(function(){var _4f=E(_4d);if(_4f[0]==3){var _4g=[3,_4f[1],new T(function(){return B(_4b(_4c,_4f[2]));})];}else{var _4h=E(_4c);if(_4h[0]==2){var _4i=E(_4f);}else{var _4j=E(_4f);if(_4j[0]==2){var _4k=E(_4h);}else{var _4l=new T(function(){var _4m=E(_4j);if(_4m[0]==4){var _4n=[1,function(_4o){return [4,new T(function(){return B(_1d(B(_41(_4h,_4o)),_4m[1]));})];}];}else{var _4p=E(_4h);if(_4p[0]==1){var _4q=_4p[1],_4r=E(_4m);if(!_4r[0]){var _4s=[1,function(_4t){return new F(function(){return _4b(B(A(_4q,[_4t])),_4r);});}];}else{var _4s=[1,function(_4u){return new F(function(){return _4b(B(A(_4q,[_4u])),new T(function(){return B(A(_4r[1],[_4u]));}));});}];}var _4v=_4s;}else{var _4w=E(_4m);if(!_4w[0]){var _4x=E(_40);}else{var _4x=[1,function(_4y){return new F(function(){return _4b(_4p,new T(function(){return B(A(_4w[1],[_4y]));}));});}];}var _4v=_4x;}var _4n=_4v;}return _4n;}),_4z=E(_4h);switch(_4z[0]){case 1:var _4A=E(_4j);if(_4A[0]==4){var _4B=[1,function(_4C){return [4,new T(function(){return B(_1d(B(_41(B(A(_4z[1],[_4C])),_4C)),_4A[1]));})];}];}else{var _4B=E(_4l);}var _4D=_4B;break;case 4:var _4E=_4z[1],_4F=E(_4j);switch(_4F[0]){case 0:var _4G=[1,function(_4H){return [4,new T(function(){return B(_1d(_4E,new T(function(){return B(_41(_4F,_4H));})));})];}];break;case 1:var _4G=[1,function(_4I){return [4,new T(function(){return B(_1d(_4E,new T(function(){return B(_41(B(A(_4F[1],[_4I])),_4I));})));})];}];break;default:var _4G=[4,new T(function(){return B(_1d(_4E,_4F[1]));})];}var _4D=_4G;break;default:var _4D=E(_4l);}var _4k=_4D;}var _4i=_4k;}var _4g=_4i;}return _4g;}),_4J=E(_4c);switch(_4J[0]){case 0:var _4K=E(_4d);return _4K[0]==0?[0,function(_4L){return new F(function(){return _4b(B(A(_4J[1],[_4L])),new T(function(){return B(A(_4K[1],[_4L]));}));});}]:E(_4e);case 3:return [3,_4J[1],new T(function(){return B(_4b(_4J[2],_4d));})];default:return E(_4e);}},_4M=function(_4N,_4O){return E(_4N)[1]!=E(_4O)[1];},_4P=function(_4Q,_4R){return E(_4Q)[1]==E(_4R)[1];},_4S=[0,_4P,_4M],_4T=function(_4U){return E(E(_4U)[1]);},_4V=function(_4W,_4X,_4Y){while(1){var _4Z=E(_4X);if(!_4Z[0]){return E(_4Y)[0]==0?true:false;}else{var _50=E(_4Y);if(!_50[0]){return false;}else{if(!B(A(_4T,[_4W,_4Z[1],_50[1]]))){return false;}else{_4X=_4Z[2];_4Y=_50[2];continue;}}}}},_51=function(_52,_53,_54){return !B(_4V(_52,_53,_54))?true:false;},_55=function(_56){return [0,function(_57,_58){return new F(function(){return _4V(_56,_57,_58);});},function(_57,_58){return new F(function(){return _51(_56,_57,_58);});}];},_59=new T(function(){return B(_55(_4S));}),_5a=function(_5b,_5c){var _5d=E(_5b);switch(_5d[0]){case 0:return [0,function(_5e){return new F(function(){return _5a(B(A(_5d[1],[_5e])),_5c);});}];case 1:return [1,function(_5f){return new F(function(){return _5a(B(A(_5d[1],[_5f])),_5c);});}];case 2:return [2];case 3:return new F(function(){return _4b(B(A(_5c,[_5d[1]])),new T(function(){return B(_5a(_5d[2],_5c));}));});break;default:var _5g=function(_5h){var _5i=E(_5h);if(!_5i[0]){return [0];}else{var _5j=E(_5i[1]);return new F(function(){return _1d(B(_41(B(A(_5c,[_5j[1]])),_5j[2])),new T(function(){return B(_5g(_5i[2]));}));});}},_5k=B(_5g(_5d[1]));return _5k[0]==0?[2]:[4,_5k];}},_5l=[2],_5m=function(_5n){return [3,_5n,_5l];},_5o=function(_5p,_5q){var _5r=E(_5p);if(!_5r){return new F(function(){return A(_5q,[_2u]);});}else{return [0,function(_5s){return E(new T(function(){return B(_5o(_5r-1|0,_5q));}));}];}},_5t=function(_5u,_5v,_5w){return [1,function(_5x){return new F(function(){return A(function(_5y,_5z,_5A){while(1){var _5B=(function(_5C,_5D,_5E){var _5F=E(_5C);switch(_5F[0]){case 0:var _5G=E(_5D);if(!_5G[0]){return E(_5v);}else{_5y=B(A(_5F[1],[_5G[1]]));_5z=_5G[2];var _5H=_5E+1|0;_5A=_5H;return null;}break;case 1:var _5I=B(A(_5F[1],[_5D])),_5J=_5D,_5H=_5E;_5y=_5I;_5z=_5J;_5A=_5H;return null;case 2:return E(_5v);case 3:return function(_5K){return new F(function(){return _5o(_5E,function(_5L){return E(new T(function(){return B(_5a(_5F,_5K));}));});});};default:return function(_5M){return new F(function(){return _5a(_5F,_5M);});};}})(_5y,_5z,_5A);if(_5B!=null){return _5B;}}},[new T(function(){return B(A(_5u,[_5m]));}),_5x,0,_5w]);});}];},_5N=[6],_5O=new T(function(){return B(unCStr("valDig: Bad base"));}),_5P=new T(function(){return B(err(_5O));}),_5Q=function(_5R,_5S){var _5T=function(_5U,_5V){var _5W=E(_5U);if(!_5W[0]){return function(_5X){return new F(function(){return A(_5X,[new T(function(){return B(A(_5V,[_0]));})]);});};}else{var _5Y=E(_5W[1])[1],_5Z=function(_60){return function(_61){return [0,function(_62){return E(new T(function(){return B(A(new T(function(){return B(_5T(_5W[2],function(_63){return new F(function(){return A(_5V,[[1,_60,_63]]);});}));}),[_61]));}));}];};};switch(E(E(_5R)[1])){case 8:if(48>_5Y){return function(_64){return new F(function(){return A(_64,[new T(function(){return B(A(_5V,[_0]));})]);});};}else{if(_5Y>55){return function(_65){return new F(function(){return A(_65,[new T(function(){return B(A(_5V,[_0]));})]);});};}else{return new F(function(){return _5Z([0,_5Y-48|0]);});}}break;case 10:if(48>_5Y){return function(_66){return new F(function(){return A(_66,[new T(function(){return B(A(_5V,[_0]));})]);});};}else{if(_5Y>57){return function(_67){return new F(function(){return A(_67,[new T(function(){return B(A(_5V,[_0]));})]);});};}else{return new F(function(){return _5Z([0,_5Y-48|0]);});}}break;case 16:var _68=new T(function(){if(97>_5Y){if(65>_5Y){var _69=[0];}else{if(_5Y>70){var _6a=[0];}else{var _6a=[1,[0,(_5Y-65|0)+10|0]];}var _69=_6a;}var _6b=_69;}else{if(_5Y>102){if(65>_5Y){var _6c=[0];}else{if(_5Y>70){var _6d=[0];}else{var _6d=[1,[0,(_5Y-65|0)+10|0]];}var _6c=_6d;}var _6e=_6c;}else{var _6e=[1,[0,(_5Y-97|0)+10|0]];}var _6b=_6e;}return _6b;});if(48>_5Y){var _6f=E(_68);if(!_6f[0]){return function(_6g){return new F(function(){return A(_6g,[new T(function(){return B(A(_5V,[_0]));})]);});};}else{return new F(function(){return _5Z(_6f[1]);});}}else{if(_5Y>57){var _6h=E(_68);if(!_6h[0]){return function(_6i){return new F(function(){return A(_6i,[new T(function(){return B(A(_5V,[_0]));})]);});};}else{return new F(function(){return _5Z(_6h[1]);});}}else{return new F(function(){return _5Z([0,_5Y-48|0]);});}}break;default:return E(_5P);}}};return [1,function(_6j){return new F(function(){return A(_5T,[_6j,_2Q,function(_6k){var _6l=E(_6k);return _6l[0]==0?[2]:B(A(_5S,[_6l]));}]);});}];},_6m=[0,10],_6n=[0,1],_6o=[0,2147483647],_6p=function(_6q,_6r){while(1){var _6s=E(_6q);if(!_6s[0]){var _6t=_6s[1],_6u=E(_6r);if(!_6u[0]){var _6v=_6u[1],_6w=addC(_6t,_6v);if(!E(_6w[2])){return [0,_6w[1]];}else{_6q=[1,I_fromInt(_6t)];_6r=[1,I_fromInt(_6v)];continue;}}else{_6q=[1,I_fromInt(_6t)];_6r=_6u;continue;}}else{var _6x=E(_6r);if(!_6x[0]){_6q=_6s;_6r=[1,I_fromInt(_6x[1])];continue;}else{return [1,I_add(_6s[1],_6x[1])];}}}},_6y=new T(function(){return B(_6p(_6o,_6n));}),_6z=function(_6A){var _6B=E(_6A);if(!_6B[0]){var _6C=E(_6B[1]);return _6C==(-2147483648)?E(_6y):[0, -_6C];}else{return [1,I_negate(_6B[1])];}},_6D=[0,10],_6E=[0,0],_6F=function(_6G){return [0,_6G];},_6H=function(_6I,_6J){while(1){var _6K=E(_6I);if(!_6K[0]){var _6L=_6K[1],_6M=E(_6J);if(!_6M[0]){var _6N=_6M[1];if(!(imul(_6L,_6N)|0)){return [0,imul(_6L,_6N)|0];}else{_6I=[1,I_fromInt(_6L)];_6J=[1,I_fromInt(_6N)];continue;}}else{_6I=[1,I_fromInt(_6L)];_6J=_6M;continue;}}else{var _6O=E(_6J);if(!_6O[0]){_6I=_6K;_6J=[1,I_fromInt(_6O[1])];continue;}else{return [1,I_mul(_6K[1],_6O[1])];}}}},_6P=function(_6Q,_6R,_6S){while(1){var _6T=E(_6S);if(!_6T[0]){return E(_6R);}else{var _6U=B(_6p(B(_6H(_6R,_6Q)),B(_6F(E(_6T[1])[1]))));_6S=_6T[2];_6R=_6U;continue;}}},_6V=function(_6W){var _6X=new T(function(){return B(_4b(B(_4b([0,function(_6Y){if(E(E(_6Y)[1])==45){return new F(function(){return _5Q(_6m,function(_6Z){return new F(function(){return A(_6W,[[1,new T(function(){return B(_6z(B(_6P(_6D,_6E,_6Z))));})]]);});});});}else{return [2];}}],[0,function(_70){if(E(E(_70)[1])==43){return new F(function(){return _5Q(_6m,function(_71){return new F(function(){return A(_6W,[[1,new T(function(){return B(_6P(_6D,_6E,_71));})]]);});});});}else{return [2];}}])),new T(function(){return B(_5Q(_6m,function(_72){return new F(function(){return A(_6W,[[1,new T(function(){return B(_6P(_6D,_6E,_72));})]]);});}));})));});return new F(function(){return _4b([0,function(_73){return E(E(_73)[1])==101?E(_6X):[2];}],[0,function(_74){return E(E(_74)[1])==69?E(_6X):[2];}]);});},_75=[0],_76=function(_77){return new F(function(){return A(_77,[_75]);});},_78=function(_79){return new F(function(){return A(_79,[_75]);});},_7a=function(_7b){return [0,function(_7c){return E(E(_7c)[1])==46?E(new T(function(){return B(_5Q(_6m,function(_7d){return new F(function(){return A(_7b,[[1,_7d]]);});}));})):[2];}];},_7e=function(_7f){return new F(function(){return _5Q(_6m,function(_7g){return new F(function(){return _5t(_7a,_76,function(_7h){return new F(function(){return _5t(_6V,_78,function(_7i){return new F(function(){return A(_7f,[[5,[1,_7g,_7h,_7i]]]);});});});});});});});},_7j=function(_7k,_7l,_7m){while(1){var _7n=E(_7m);if(!_7n[0]){return false;}else{if(!B(A(_4T,[_7k,_7l,_7n[1]]))){_7m=_7n[2];continue;}else{return true;}}}},_7o=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_7p=function(_7q){return new F(function(){return _7j(_4S,_7q,_7o);});},_7r=[0,8],_7s=[0,16],_7t=function(_7u){return [0,function(_7v){return E(E(_7v)[1])==48?E([0,function(_7w){switch(E(E(_7w)[1])){case 79:return E(new T(function(){return B(_5Q(_7r,function(_7x){return new F(function(){return A(_7u,[[5,[0,_7r,_7x]]]);});}));}));case 88:return E(new T(function(){return B(_5Q(_7s,function(_7y){return new F(function(){return A(_7u,[[5,[0,_7s,_7y]]]);});}));}));case 111:return E(new T(function(){return B(_5Q(_7r,function(_7z){return new F(function(){return A(_7u,[[5,[0,_7r,_7z]]]);});}));}));case 120:return E(new T(function(){return B(_5Q(_7s,function(_7A){return new F(function(){return A(_7u,[[5,[0,_7s,_7A]]]);});}));}));default:return [2];}}]):[2];}];},_7B=false,_7C=true,_7D=function(_7E){return [0,function(_7F){switch(E(E(_7F)[1])){case 79:return E(new T(function(){return B(A(_7E,[_7r]));}));case 88:return E(new T(function(){return B(A(_7E,[_7s]));}));case 111:return E(new T(function(){return B(A(_7E,[_7r]));}));case 120:return E(new T(function(){return B(A(_7E,[_7s]));}));default:return [2];}}];},_7G=function(_7H){return new F(function(){return A(_7H,[_6m]);});},_7I=function(_7J){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_2K(9,_7J,_0));}))));});},_7K=function(_7L){var _7M=E(_7L);return _7M[0]==0?E(_7M[1]):I_toInt(_7M[1]);},_7N=function(_7O,_7P){var _7Q=E(_7O);if(!_7Q[0]){var _7R=_7Q[1],_7S=E(_7P);return _7S[0]==0?_7R<=_7S[1]:I_compareInt(_7S[1],_7R)>=0;}else{var _7T=_7Q[1],_7U=E(_7P);return _7U[0]==0?I_compareInt(_7T,_7U[1])<=0:I_compare(_7T,_7U[1])<=0;}},_7V=function(_7W){return [2];},_7X=function(_7Y){var _7Z=E(_7Y);if(!_7Z[0]){return E(_7V);}else{var _80=_7Z[1],_81=E(_7Z[2]);return _81[0]==0?E(_80):function(_82){return new F(function(){return _4b(B(A(_80,[_82])),new T(function(){return B(A(new T(function(){return B(_7X(_81));}),[_82]));}));});};}},_83=new T(function(){return B(unCStr("NUL"));}),_84=function(_85){return [2];},_86=function(_87){return new F(function(){return _84(_87);});},_88=function(_89,_8a){var _8b=function(_8c,_8d){var _8e=E(_8c);if(!_8e[0]){return function(_8f){return new F(function(){return A(_8f,[_89]);});};}else{var _8g=E(_8d);return _8g[0]==0?E(_84):E(_8e[1])[1]!=E(_8g[1])[1]?E(_86):function(_8h){return [0,function(_8i){return E(new T(function(){return B(A(new T(function(){return B(_8b(_8e[2],_8g[2]));}),[_8h]));}));}];};}};return [1,function(_8j){return new F(function(){return A(_8b,[_89,_8j,_8a]);});}];},_8k=[0,0],_8l=function(_8m){return new F(function(){return _88(_83,function(_8n){return E(new T(function(){return B(A(_8m,[_8k]));}));});});},_8o=new T(function(){return B(unCStr("STX"));}),_8p=[0,2],_8q=function(_8r){return new F(function(){return _88(_8o,function(_8s){return E(new T(function(){return B(A(_8r,[_8p]));}));});});},_8t=new T(function(){return B(unCStr("ETX"));}),_8u=[0,3],_8v=function(_8w){return new F(function(){return _88(_8t,function(_8x){return E(new T(function(){return B(A(_8w,[_8u]));}));});});},_8y=new T(function(){return B(unCStr("EOT"));}),_8z=[0,4],_8A=function(_8B){return new F(function(){return _88(_8y,function(_8C){return E(new T(function(){return B(A(_8B,[_8z]));}));});});},_8D=new T(function(){return B(unCStr("ENQ"));}),_8E=[0,5],_8F=function(_8G){return new F(function(){return _88(_8D,function(_8H){return E(new T(function(){return B(A(_8G,[_8E]));}));});});},_8I=new T(function(){return B(unCStr("ACK"));}),_8J=[0,6],_8K=function(_8L){return new F(function(){return _88(_8I,function(_8M){return E(new T(function(){return B(A(_8L,[_8J]));}));});});},_8N=new T(function(){return B(unCStr("BEL"));}),_8O=[0,7],_8P=function(_8Q){return new F(function(){return _88(_8N,function(_8R){return E(new T(function(){return B(A(_8Q,[_8O]));}));});});},_8S=new T(function(){return B(unCStr("BS"));}),_8T=[0,8],_8U=function(_8V){return new F(function(){return _88(_8S,function(_8W){return E(new T(function(){return B(A(_8V,[_8T]));}));});});},_8X=new T(function(){return B(unCStr("HT"));}),_8Y=[0,9],_8Z=function(_90){return new F(function(){return _88(_8X,function(_91){return E(new T(function(){return B(A(_90,[_8Y]));}));});});},_92=new T(function(){return B(unCStr("LF"));}),_93=[0,10],_94=function(_95){return new F(function(){return _88(_92,function(_96){return E(new T(function(){return B(A(_95,[_93]));}));});});},_97=new T(function(){return B(unCStr("VT"));}),_98=[0,11],_99=function(_9a){return new F(function(){return _88(_97,function(_9b){return E(new T(function(){return B(A(_9a,[_98]));}));});});},_9c=new T(function(){return B(unCStr("FF"));}),_9d=[0,12],_9e=function(_9f){return new F(function(){return _88(_9c,function(_9g){return E(new T(function(){return B(A(_9f,[_9d]));}));});});},_9h=new T(function(){return B(unCStr("CR"));}),_9i=[0,13],_9j=function(_9k){return new F(function(){return _88(_9h,function(_9l){return E(new T(function(){return B(A(_9k,[_9i]));}));});});},_9m=new T(function(){return B(unCStr("SI"));}),_9n=[0,15],_9o=function(_9p){return new F(function(){return _88(_9m,function(_9q){return E(new T(function(){return B(A(_9p,[_9n]));}));});});},_9r=new T(function(){return B(unCStr("DLE"));}),_9s=[0,16],_9t=function(_9u){return new F(function(){return _88(_9r,function(_9v){return E(new T(function(){return B(A(_9u,[_9s]));}));});});},_9w=new T(function(){return B(unCStr("DC1"));}),_9x=[0,17],_9y=function(_9z){return new F(function(){return _88(_9w,function(_9A){return E(new T(function(){return B(A(_9z,[_9x]));}));});});},_9B=new T(function(){return B(unCStr("DC2"));}),_9C=[0,18],_9D=function(_9E){return new F(function(){return _88(_9B,function(_9F){return E(new T(function(){return B(A(_9E,[_9C]));}));});});},_9G=new T(function(){return B(unCStr("DC3"));}),_9H=[0,19],_9I=function(_9J){return new F(function(){return _88(_9G,function(_9K){return E(new T(function(){return B(A(_9J,[_9H]));}));});});},_9L=new T(function(){return B(unCStr("DC4"));}),_9M=[0,20],_9N=function(_9O){return new F(function(){return _88(_9L,function(_9P){return E(new T(function(){return B(A(_9O,[_9M]));}));});});},_9Q=new T(function(){return B(unCStr("NAK"));}),_9R=[0,21],_9S=function(_9T){return new F(function(){return _88(_9Q,function(_9U){return E(new T(function(){return B(A(_9T,[_9R]));}));});});},_9V=new T(function(){return B(unCStr("SYN"));}),_9W=[0,22],_9X=function(_9Y){return new F(function(){return _88(_9V,function(_9Z){return E(new T(function(){return B(A(_9Y,[_9W]));}));});});},_a0=new T(function(){return B(unCStr("ETB"));}),_a1=[0,23],_a2=function(_a3){return new F(function(){return _88(_a0,function(_a4){return E(new T(function(){return B(A(_a3,[_a1]));}));});});},_a5=new T(function(){return B(unCStr("CAN"));}),_a6=[0,24],_a7=function(_a8){return new F(function(){return _88(_a5,function(_a9){return E(new T(function(){return B(A(_a8,[_a6]));}));});});},_aa=new T(function(){return B(unCStr("EM"));}),_ab=[0,25],_ac=function(_ad){return new F(function(){return _88(_aa,function(_ae){return E(new T(function(){return B(A(_ad,[_ab]));}));});});},_af=new T(function(){return B(unCStr("SUB"));}),_ag=[0,26],_ah=function(_ai){return new F(function(){return _88(_af,function(_aj){return E(new T(function(){return B(A(_ai,[_ag]));}));});});},_ak=new T(function(){return B(unCStr("ESC"));}),_al=[0,27],_am=function(_an){return new F(function(){return _88(_ak,function(_ao){return E(new T(function(){return B(A(_an,[_al]));}));});});},_ap=new T(function(){return B(unCStr("FS"));}),_aq=[0,28],_ar=function(_as){return new F(function(){return _88(_ap,function(_at){return E(new T(function(){return B(A(_as,[_aq]));}));});});},_au=new T(function(){return B(unCStr("GS"));}),_av=[0,29],_aw=function(_ax){return new F(function(){return _88(_au,function(_ay){return E(new T(function(){return B(A(_ax,[_av]));}));});});},_az=new T(function(){return B(unCStr("RS"));}),_aA=[0,30],_aB=function(_aC){return new F(function(){return _88(_az,function(_aD){return E(new T(function(){return B(A(_aC,[_aA]));}));});});},_aE=new T(function(){return B(unCStr("US"));}),_aF=[0,31],_aG=function(_aH){return new F(function(){return _88(_aE,function(_aI){return E(new T(function(){return B(A(_aH,[_aF]));}));});});},_aJ=new T(function(){return B(unCStr("SP"));}),_aK=[0,32],_aL=function(_aM){return new F(function(){return _88(_aJ,function(_aN){return E(new T(function(){return B(A(_aM,[_aK]));}));});});},_aO=new T(function(){return B(unCStr("DEL"));}),_aP=[0,127],_aQ=function(_aR){return new F(function(){return _88(_aO,function(_aS){return E(new T(function(){return B(A(_aR,[_aP]));}));});});},_aT=[1,_aQ,_0],_aU=[1,_aL,_aT],_aV=[1,_aG,_aU],_aW=[1,_aB,_aV],_aX=[1,_aw,_aW],_aY=[1,_ar,_aX],_aZ=[1,_am,_aY],_b0=[1,_ah,_aZ],_b1=[1,_ac,_b0],_b2=[1,_a7,_b1],_b3=[1,_a2,_b2],_b4=[1,_9X,_b3],_b5=[1,_9S,_b4],_b6=[1,_9N,_b5],_b7=[1,_9I,_b6],_b8=[1,_9D,_b7],_b9=[1,_9y,_b8],_ba=[1,_9t,_b9],_bb=[1,_9o,_ba],_bc=[1,_9j,_bb],_bd=[1,_9e,_bc],_be=[1,_99,_bd],_bf=[1,_94,_be],_bg=[1,_8Z,_bf],_bh=[1,_8U,_bg],_bi=[1,_8P,_bh],_bj=[1,_8K,_bi],_bk=[1,_8F,_bj],_bl=[1,_8A,_bk],_bm=[1,_8v,_bl],_bn=[1,_8q,_bm],_bo=[1,_8l,_bn],_bp=new T(function(){return B(unCStr("SOH"));}),_bq=[0,1],_br=function(_bs){return new F(function(){return _88(_bp,function(_bt){return E(new T(function(){return B(A(_bs,[_bq]));}));});});},_bu=new T(function(){return B(unCStr("SO"));}),_bv=[0,14],_bw=function(_bx){return new F(function(){return _88(_bu,function(_by){return E(new T(function(){return B(A(_bx,[_bv]));}));});});},_bz=function(_bA){return new F(function(){return _5t(_br,_bw,_bA);});},_bB=[1,_bz,_bo],_bC=new T(function(){return B(_7X(_bB));}),_bD=[0,1114111],_bE=[0,34],_bF=[0,_bE,_7C],_bG=[0,39],_bH=[0,_bG,_7C],_bI=[0,92],_bJ=[0,_bI,_7C],_bK=[0,_8O,_7C],_bL=[0,_8T,_7C],_bM=[0,_9d,_7C],_bN=[0,_93,_7C],_bO=[0,_9i,_7C],_bP=[0,_8Y,_7C],_bQ=[0,_98,_7C],_bR=[0,_8k,_7C],_bS=[0,_bq,_7C],_bT=[0,_8p,_7C],_bU=[0,_8u,_7C],_bV=[0,_8z,_7C],_bW=[0,_8E,_7C],_bX=[0,_8J,_7C],_bY=[0,_8O,_7C],_bZ=[0,_8T,_7C],_c0=[0,_8Y,_7C],_c1=[0,_93,_7C],_c2=[0,_98,_7C],_c3=[0,_9d,_7C],_c4=[0,_9i,_7C],_c5=[0,_bv,_7C],_c6=[0,_9n,_7C],_c7=[0,_9s,_7C],_c8=[0,_9x,_7C],_c9=[0,_9C,_7C],_ca=[0,_9H,_7C],_cb=[0,_9M,_7C],_cc=[0,_9R,_7C],_cd=[0,_9W,_7C],_ce=[0,_a1,_7C],_cf=[0,_a6,_7C],_cg=[0,_ab,_7C],_ch=[0,_ag,_7C],_ci=[0,_al,_7C],_cj=[0,_aq,_7C],_ck=[0,_av,_7C],_cl=[0,_aA,_7C],_cm=[0,_aF,_7C],_cn=function(_co){return new F(function(){return _4b([0,function(_cp){switch(E(E(_cp)[1])){case 34:return E(new T(function(){return B(A(_co,[_bF]));}));case 39:return E(new T(function(){return B(A(_co,[_bH]));}));case 92:return E(new T(function(){return B(A(_co,[_bJ]));}));case 97:return E(new T(function(){return B(A(_co,[_bK]));}));case 98:return E(new T(function(){return B(A(_co,[_bL]));}));case 102:return E(new T(function(){return B(A(_co,[_bM]));}));case 110:return E(new T(function(){return B(A(_co,[_bN]));}));case 114:return E(new T(function(){return B(A(_co,[_bO]));}));case 116:return E(new T(function(){return B(A(_co,[_bP]));}));case 118:return E(new T(function(){return B(A(_co,[_bQ]));}));default:return [2];}}],new T(function(){return B(_4b(B(_5t(_7D,_7G,function(_cq){return new F(function(){return _5Q(_cq,function(_cr){var _cs=B(_6P(new T(function(){return B(_6F(E(_cq)[1]));}),_6E,_cr));return !B(_7N(_cs,_bD))?[2]:B(A(_co,[[0,new T(function(){var _ct=B(_7K(_cs));if(_ct>>>0>1114111){var _cu=B(_7I(_ct));}else{var _cu=[0,_ct];}var _cv=_cu,_cw=_cv;return _cw;}),_7C]]));});});})),new T(function(){return B(_4b([0,function(_cx){return E(E(_cx)[1])==94?E([0,function(_cy){switch(E(E(_cy)[1])){case 64:return E(new T(function(){return B(A(_co,[_bR]));}));case 65:return E(new T(function(){return B(A(_co,[_bS]));}));case 66:return E(new T(function(){return B(A(_co,[_bT]));}));case 67:return E(new T(function(){return B(A(_co,[_bU]));}));case 68:return E(new T(function(){return B(A(_co,[_bV]));}));case 69:return E(new T(function(){return B(A(_co,[_bW]));}));case 70:return E(new T(function(){return B(A(_co,[_bX]));}));case 71:return E(new T(function(){return B(A(_co,[_bY]));}));case 72:return E(new T(function(){return B(A(_co,[_bZ]));}));case 73:return E(new T(function(){return B(A(_co,[_c0]));}));case 74:return E(new T(function(){return B(A(_co,[_c1]));}));case 75:return E(new T(function(){return B(A(_co,[_c2]));}));case 76:return E(new T(function(){return B(A(_co,[_c3]));}));case 77:return E(new T(function(){return B(A(_co,[_c4]));}));case 78:return E(new T(function(){return B(A(_co,[_c5]));}));case 79:return E(new T(function(){return B(A(_co,[_c6]));}));case 80:return E(new T(function(){return B(A(_co,[_c7]));}));case 81:return E(new T(function(){return B(A(_co,[_c8]));}));case 82:return E(new T(function(){return B(A(_co,[_c9]));}));case 83:return E(new T(function(){return B(A(_co,[_ca]));}));case 84:return E(new T(function(){return B(A(_co,[_cb]));}));case 85:return E(new T(function(){return B(A(_co,[_cc]));}));case 86:return E(new T(function(){return B(A(_co,[_cd]));}));case 87:return E(new T(function(){return B(A(_co,[_ce]));}));case 88:return E(new T(function(){return B(A(_co,[_cf]));}));case 89:return E(new T(function(){return B(A(_co,[_cg]));}));case 90:return E(new T(function(){return B(A(_co,[_ch]));}));case 91:return E(new T(function(){return B(A(_co,[_ci]));}));case 92:return E(new T(function(){return B(A(_co,[_cj]));}));case 93:return E(new T(function(){return B(A(_co,[_ck]));}));case 94:return E(new T(function(){return B(A(_co,[_cl]));}));case 95:return E(new T(function(){return B(A(_co,[_cm]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_bC,[function(_cz){return new F(function(){return A(_co,[[0,_cz,_7C]]);});}]));})));})));}));});},_cA=function(_cB){return new F(function(){return A(_cB,[_2u]);});},_cC=function(_cD){var _cE=E(_cD);if(!_cE[0]){return E(_cA);}else{var _cF=_cE[2],_cG=E(E(_cE[1])[1]);switch(_cG){case 9:return function(_cH){return [0,function(_cI){return E(new T(function(){return B(A(new T(function(){return B(_cC(_cF));}),[_cH]));}));}];};case 10:return function(_cJ){return [0,function(_cK){return E(new T(function(){return B(A(new T(function(){return B(_cC(_cF));}),[_cJ]));}));}];};case 11:return function(_cL){return [0,function(_cM){return E(new T(function(){return B(A(new T(function(){return B(_cC(_cF));}),[_cL]));}));}];};case 12:return function(_cN){return [0,function(_cO){return E(new T(function(){return B(A(new T(function(){return B(_cC(_cF));}),[_cN]));}));}];};case 13:return function(_cP){return [0,function(_cQ){return E(new T(function(){return B(A(new T(function(){return B(_cC(_cF));}),[_cP]));}));}];};case 32:return function(_cR){return [0,function(_cS){return E(new T(function(){return B(A(new T(function(){return B(_cC(_cF));}),[_cR]));}));}];};case 160:return function(_cT){return [0,function(_cU){return E(new T(function(){return B(A(new T(function(){return B(_cC(_cF));}),[_cT]));}));}];};default:var _cV=u_iswspace(_cG),_cW=_cV;return E(_cW)==0?E(_cA):function(_cX){return [0,function(_cY){return E(new T(function(){return B(A(new T(function(){return B(_cC(_cF));}),[_cX]));}));}];};}}},_cZ=function(_d0){var _d1=new T(function(){return B(_cZ(_d0));}),_d2=[1,function(_d3){return new F(function(){return A(_cC,[_d3,function(_d4){return E([0,function(_d5){return E(E(_d5)[1])==92?E(_d1):[2];}]);}]);});}];return new F(function(){return _4b([0,function(_d6){return E(E(_d6)[1])==92?E([0,function(_d7){var _d8=E(E(_d7)[1]);switch(_d8){case 9:return E(_d2);case 10:return E(_d2);case 11:return E(_d2);case 12:return E(_d2);case 13:return E(_d2);case 32:return E(_d2);case 38:return E(_d1);case 160:return E(_d2);default:var _d9=u_iswspace(_d8),_da=_d9;return E(_da)==0?[2]:E(_d2);}}]):[2];}],[0,function(_db){var _dc=E(_db);return E(_dc[1])==92?E(new T(function(){return B(_cn(_d0));})):B(A(_d0,[[0,_dc,_7B]]));}]);});},_dd=function(_de,_df){return new F(function(){return _cZ(function(_dg){var _dh=E(_dg),_di=E(_dh[1]);if(E(_di[1])==34){if(!E(_dh[2])){return E(new T(function(){return B(A(_df,[[1,new T(function(){return B(A(_de,[_0]));})]]));}));}else{return new F(function(){return _dd(function(_dj){return new F(function(){return A(_de,[[1,_di,_dj]]);});},_df);});}}else{return new F(function(){return _dd(function(_dk){return new F(function(){return A(_de,[[1,_di,_dk]]);});},_df);});}});});},_dl=new T(function(){return B(unCStr("_\'"));}),_dm=function(_dn){var _do=u_iswalnum(_dn),_dp=_do;return E(_dp)==0?B(_7j(_4S,[0,_dn],_dl)):true;},_dq=function(_dr){return new F(function(){return _dm(E(_dr)[1]);});},_ds=new T(function(){return B(unCStr(",;()[]{}`"));}),_dt=function(_du){return new F(function(){return A(_du,[_0]);});},_dv=function(_dw,_dx){var _dy=function(_dz){var _dA=E(_dz);if(!_dA[0]){return E(_dt);}else{var _dB=_dA[1];return !B(A(_dw,[_dB]))?E(_dt):function(_dC){return [0,function(_dD){return E(new T(function(){return B(A(new T(function(){return B(_dy(_dA[2]));}),[function(_dE){return new F(function(){return A(_dC,[[1,_dB,_dE]]);});}]));}));}];};}};return [1,function(_dF){return new F(function(){return A(_dy,[_dF,_dx]);});}];},_dG=new T(function(){return B(unCStr(".."));}),_dH=new T(function(){return B(unCStr("::"));}),_dI=new T(function(){return B(unCStr("->"));}),_dJ=[0,64],_dK=[1,_dJ,_0],_dL=[0,126],_dM=[1,_dL,_0],_dN=new T(function(){return B(unCStr("=>"));}),_dO=[1,_dN,_0],_dP=[1,_dM,_dO],_dQ=[1,_dK,_dP],_dR=[1,_dI,_dQ],_dS=new T(function(){return B(unCStr("<-"));}),_dT=[1,_dS,_dR],_dU=[0,124],_dV=[1,_dU,_0],_dW=[1,_dV,_dT],_dX=[1,_bI,_0],_dY=[1,_dX,_dW],_dZ=[0,61],_e0=[1,_dZ,_0],_e1=[1,_e0,_dY],_e2=[1,_dH,_e1],_e3=[1,_dG,_e2],_e4=function(_e5){return new F(function(){return _4b([1,function(_e6){return E(_e6)[0]==0?E(new T(function(){return B(A(_e5,[_5N]));})):[2];}],new T(function(){return B(_4b([0,function(_e7){return E(E(_e7)[1])==39?E([0,function(_e8){var _e9=E(_e8);switch(E(_e9[1])){case 39:return [2];case 92:return E(new T(function(){return B(_cn(function(_ea){var _eb=E(_ea);return new F(function(){return (function(_ec,_ed){var _ee=new T(function(){return B(A(_e5,[[0,_ec]]));});return !E(_ed)?E(E(_ec)[1])==39?[2]:[0,function(_ef){return E(E(_ef)[1])==39?E(_ee):[2];}]:[0,function(_eg){return E(E(_eg)[1])==39?E(_ee):[2];}];})(_eb[1],_eb[2]);});}));}));default:return [0,function(_eh){return E(E(_eh)[1])==39?E(new T(function(){return B(A(_e5,[[0,_e9]]));})):[2];}];}}]):[2];}],new T(function(){return B(_4b([0,function(_ei){return E(E(_ei)[1])==34?E(new T(function(){return B(_dd(_2Q,_e5));})):[2];}],new T(function(){return B(_4b([0,function(_ej){return !B(_7j(_4S,_ej,_ds))?[2]:B(A(_e5,[[2,[1,_ej,_0]]]));}],new T(function(){return B(_4b([0,function(_ek){if(!B(_7j(_4S,_ek,_7o))){return [2];}else{return new F(function(){return _dv(_7p,function(_el){var _em=[1,_ek,_el];return !B(_7j(_59,_em,_e3))?B(A(_e5,[[4,_em]])):B(A(_e5,[[2,_em]]));});});}}],new T(function(){return B(_4b([0,function(_en){var _eo=E(_en),_ep=_eo[1],_eq=u_iswalpha(_ep),_er=_eq;if(!E(_er)){if(E(_ep)==95){return new F(function(){return _dv(_dq,function(_es){return new F(function(){return A(_e5,[[3,[1,_eo,_es]]]);});});});}else{return [2];}}else{return new F(function(){return _dv(_dq,function(_et){return new F(function(){return A(_e5,[[3,[1,_eo,_et]]]);});});});}}],new T(function(){return B(_5t(_7t,_7e,_e5));})));})));})));})));})));}));});},_eu=function(_ev){return [1,function(_ew){return new F(function(){return A(_cC,[_ew,function(_ex){return E(new T(function(){return B(_e4(_ev));}));}]);});}];},_ey=[0,0],_ez=function(_eA,_eB){return new F(function(){return _eu(function(_eC){var _eD=E(_eC);if(_eD[0]==2){var _eE=E(_eD[1]);return _eE[0]==0?[2]:E(E(_eE[1])[1])==40?E(_eE[2])[0]==0?E(new T(function(){return B(A(_eA,[_ey,function(_eF){return new F(function(){return _eu(function(_eG){var _eH=E(_eG);if(_eH[0]==2){var _eI=E(_eH[1]);return _eI[0]==0?[2]:E(E(_eI[1])[1])==41?E(_eI[2])[0]==0?E(new T(function(){return B(A(_eB,[_eF]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_eJ=function(_eK,_eL,_eM){var _eN=function(_eO,_eP){return new F(function(){return _4b(B(_eu(function(_eQ){var _eR=E(_eQ);if(_eR[0]==4){var _eS=E(_eR[1]);if(!_eS[0]){return new F(function(){return A(_eK,[_eR,_eO,_eP]);});}else{return E(E(_eS[1])[1])==45?E(_eS[2])[0]==0?E([1,function(_eT){return new F(function(){return A(_cC,[_eT,function(_eU){return E(new T(function(){return B(_e4(function(_eV){return new F(function(){return A(_eK,[_eV,_eO,function(_eW){return new F(function(){return A(_eP,[new T(function(){return [0, -E(_eW)[1]];})]);});}]);});}));}));}]);});}]):B(A(_eK,[_eR,_eO,_eP])):B(A(_eK,[_eR,_eO,_eP]));}}else{return new F(function(){return A(_eK,[_eR,_eO,_eP]);});}})),new T(function(){return B(_ez(_eN,_eP));}));});};return new F(function(){return _eN(_eL,_eM);});},_eX=function(_eY,_eZ){return [2];},_f0=function(_f1,_f2){return new F(function(){return _eX(_f1,_f2);});},_f3=function(_f4){var _f5=E(_f4);return _f5[0]==0?[1,new T(function(){return B(_6P(new T(function(){return B(_6F(E(_f5[1])[1]));}),_6E,_f5[2]));})]:E(_f5[2])[0]==0?E(_f5[3])[0]==0?[1,new T(function(){return B(_6P(_6D,_6E,_f5[1]));})]:[0]:[0];},_f6=function(_f7){var _f8=E(_f7);if(_f8[0]==5){var _f9=B(_f3(_f8[1]));return _f9[0]==0?E(_eX):function(_fa,_fb){return new F(function(){return A(_fb,[new T(function(){return [0,B(_7K(_f9[1]))];})]);});};}else{return E(_f0);}},_fc=function(_fd){return [1,function(_fe){return new F(function(){return A(_cC,[_fe,function(_ff){return E([3,_fd,_5l]);}]);});}];},_fg=new T(function(){return B(_eJ(_f6,_ey,_fc));}),_fh=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_fi=new T(function(){return B(err(_fh));}),_fj=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_fk=new T(function(){return B(err(_fj));}),_fl=function(_fm,_fn,_fo){return _fo<=_fn?[1,[0,_fm],new T(function(){var _fp=_fn-_fm|0,_fq=function(_fr){return _fr>=(_fo-_fp|0)?[1,[0,_fr],new T(function(){return B(_fq(_fr+_fp|0));})]:[1,[0,_fr],_0];};return B(_fq(_fn));})]:_fo<=_fm?[1,[0,_fm],_0]:[0];},_fs=function(_ft,_fu,_fv){return _fv>=_fu?[1,[0,_ft],new T(function(){var _fw=_fu-_ft|0,_fx=function(_fy){return _fy<=(_fv-_fw|0)?[1,[0,_fy],new T(function(){return B(_fx(_fy+_fw|0));})]:[1,[0,_fy],_0];};return B(_fx(_fu));})]:_fv>=_ft?[1,[0,_ft],_0]:[0];},_fz=function(_fA,_fB){return _fB<_fA?B(_fl(_fA,_fB,-2147483648)):B(_fs(_fA,_fB,2147483647));},_fC=new T(function(){return B(_fz(135,150));}),_fD=function(_fE,_fF){var _fG=E(_fE);if(!_fG){return [0];}else{var _fH=E(_fF);return _fH[0]==0?[0]:[1,_fH[1],new T(function(){return B(_fD(_fG-1|0,_fH[2]));})];}},_fI=new T(function(){return B(_fD(6,_fC));}),_fJ=function(_fK,_fL){var _fM=E(_fK);if(!_fM[0]){return E(_fI);}else{var _fN=_fM[1];return _fL>1?[1,_fN,new T(function(){return B(_fJ(_fM[2],_fL-1|0));})]:[1,_fN,_fI];}},_fO=new T(function(){return B(_fz(25,40));}),_fP=new T(function(){return B(_fJ(_fO,6));}),_fQ=function(_fR){while(1){var _fS=(function(_fT){var _fU=E(_fT);if(!_fU[0]){return [0];}else{var _fV=_fU[2],_fW=E(_fU[1]);if(!E(_fW[2])[0]){return [1,_fW[1],new T(function(){return B(_fQ(_fV));})];}else{_fR=_fV;return null;}}})(_fR);if(_fS!=null){return _fS;}}},_fX=function(_fY,_fZ){var _g0=E(_fZ);if(!_g0[0]){return [0,_0,_0];}else{var _g1=_g0[1];if(!B(A(_fY,[_g1]))){var _g2=new T(function(){var _g3=B(_fX(_fY,_g0[2]));return [0,_g3[1],_g3[2]];});return [0,[1,_g1,new T(function(){return E(E(_g2)[1]);})],new T(function(){return E(E(_g2)[2]);})];}else{return [0,_0,_g0];}}},_g4=function(_g5,_g6){while(1){var _g7=E(_g6);if(!_g7[0]){return [0];}else{if(!B(A(_g5,[_g7[1]]))){return E(_g7);}else{_g6=_g7[2];continue;}}}},_g8=function(_g9){var _ga=E(_g9);switch(_ga){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _gb=u_iswspace(_ga),_gc=_gb;return E(_gc)==0?false:true;}},_gd=function(_ge){return new F(function(){return _g8(E(_ge)[1]);});},_gf=function(_gg){var _gh=B(_g4(_gd,_gg));if(!_gh[0]){return [0];}else{var _gi=new T(function(){var _gj=B(_fX(_gd,_gh));return [0,_gj[1],_gj[2]];});return [1,new T(function(){return E(E(_gi)[1]);}),new T(function(){return B(_gf(E(_gi)[2]));})];}},_gk=function(_gl,_){var _gm=setDropCheckerCallback_ffi(function(_gn,_go,_gp){var _gq=E(_gl),_gr=_gq[1],_gs=_gq[6],_gt=new T(function(){return B(_gf(B(_3T(_gn))));}),_gu=new T(function(){var _gv=B(_fQ(B(_41(_fg,new T(function(){return B(_3p(2,B(_2p(_gt,2))));})))));return _gv[0]==0?E(_fk):E(_gv[2])[0]==0?E(_gv[1]):E(_fi);}),_gw=new T(function(){var _gx=B(_fQ(B(_41(_fg,new T(function(){return B(_3p(2,B(_2p(_gt,3))));})))));return _gx[0]==0?E(_fk):E(_gx[2])[0]==0?E(_gx[1]):E(_fi);}),_gy=B(_3A(function(_gz){var _gA=E(_gz)[1]-E(_go)[1];return _gA<0? -_gA<7:_gA<7;},_fP));if(!_gy[0]){return function(_5M){return new F(function(){return _3e(_gu,_gw,_gu,_gw,_gs,_5M);});};}else{var _gB=_gy[1],_gC=function(_gD,_gE,_){var _gF=E(_gu),_gG=_gF[1];if(_gD<=_gG){return new F(function(){return _3e(_gF,_gw,_gF,_gw,_gs,_);});}else{if(_gD>=0){var _gH=B(_2p(_gr,_gD)),_gI=new T(function(){return _gG<0;}),_gJ=function(_){var _gK=B(_3e(_gF,_gw,_gE,new T(function(){if(_gD>=0){var _gL=E(B(_2p(_gr,_gD))[2]);}else{var _gL=E(_2m);}return _gL;}),_gs,_)),_gM=_gK;if(!E(_gI)){var _gN=new T(function(){return B(_3M(function(_gO,_gP,_gQ){return [1,new T(function(){var _gR=E(_gO)[1];return _gR!=_gG?_gR!=_gD?E(_gP):[0,new T(function(){if(_gG>=0){var _gS=E(B(_2p(_gr,_gG))[1]);}else{var _gS=E(_2m);}return _gS;}),new T(function(){return [0,E(E(_gP)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_gP)[1]);}),new T(function(){return [0,E(E(_gP)[2])[1]-1|0];})];}),_gQ];},_0,_3Z,_gr));}),_gT=B((function(_gU,_){while(1){var _gV=(function(_gW,_){var _gX=E(_gW);if(!_gX[0]){return _2u;}else{var _gY=_gX[1],_gZ=B(_3e(_gF,_gY,_gF,new T(function(){return [0,E(_gY)[1]-1|0];}),_gs,_)),_h0=_gZ;_gU=_gX[2];return null;}})(_gU,_);if(_gV!=null){return _gV;}}})(B(_3p(1,B(_3u(E(_gw)[1],E(B(_2p(_gN,_gG))[2])[1])))),_)),_h1=_gT;return new F(function(){return _gk([0,_gN,_gq[2],_gq[3],_gq[4],_gq[5],_gs,_gq[7]],_);});}else{return E(_2m);}},_h2=function(_){return E(_gH[2])[1]>=2?B(_3e(_gF,_gw,_gF,_gw,_gs,_)):B(_gJ(_));};return E(_gH[1])==0?!E(_gI)?E(B(_2p(_gr,_gG))[1])==0?B(_gJ(_)):B(_h2(_)):E(_2m):!E(_gI)?E(B(_2p(_gr,_gG))[1])==0?B(_h2(_)):B(_gJ(_)):E(_2m);}else{return E(_2m);}}};if(E(_gp)[1]<=E(_3Y)[1]){var _h3=E(_gB);return function(_5M){return new F(function(){return _gC(_h3[1],_h3,_5M);});};}else{var _h4=23-E(_gB)[1]|0;return function(_5M){return new F(function(){return _gC(_h4,[0,_h4],_5M);});};}}});return _2u;},_h5=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:136:5-10"));}),_h6=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_h7=new T(function(){return B(unCStr("base"));}),_h8=new T(function(){return B(unCStr("IOException"));}),_h9=new T(function(){var _ha=hs_wordToWord64(4053623282),_hb=_ha,_hc=hs_wordToWord64(3693590983),_hd=_hc;return [0,_hb,_hd,[0,_hb,_hd,_h7,_h6,_h8],_0];}),_he=function(_hf){return E(_h9);},_hg=function(_hh){var _hi=E(_hh);return new F(function(){return _T(B(_P(_hi[1])),_he,_hi[2]);});},_hj=new T(function(){return B(unCStr(": "));}),_hk=[0,41],_hl=new T(function(){return B(unCStr(" ("));}),_hm=new T(function(){return B(unCStr("already exists"));}),_hn=new T(function(){return B(unCStr("does not exist"));}),_ho=new T(function(){return B(unCStr("protocol error"));}),_hp=new T(function(){return B(unCStr("failed"));}),_hq=new T(function(){return B(unCStr("invalid argument"));}),_hr=new T(function(){return B(unCStr("inappropriate type"));}),_hs=new T(function(){return B(unCStr("hardware fault"));}),_ht=new T(function(){return B(unCStr("unsupported operation"));}),_hu=new T(function(){return B(unCStr("timeout"));}),_hv=new T(function(){return B(unCStr("resource vanished"));}),_hw=new T(function(){return B(unCStr("interrupted"));}),_hx=new T(function(){return B(unCStr("resource busy"));}),_hy=new T(function(){return B(unCStr("resource exhausted"));}),_hz=new T(function(){return B(unCStr("end of file"));}),_hA=new T(function(){return B(unCStr("illegal operation"));}),_hB=new T(function(){return B(unCStr("permission denied"));}),_hC=new T(function(){return B(unCStr("user error"));}),_hD=new T(function(){return B(unCStr("unsatisified constraints"));}),_hE=new T(function(){return B(unCStr("system error"));}),_hF=function(_hG,_hH){switch(E(_hG)){case 0:return new F(function(){return _1d(_hm,_hH);});break;case 1:return new F(function(){return _1d(_hn,_hH);});break;case 2:return new F(function(){return _1d(_hx,_hH);});break;case 3:return new F(function(){return _1d(_hy,_hH);});break;case 4:return new F(function(){return _1d(_hz,_hH);});break;case 5:return new F(function(){return _1d(_hA,_hH);});break;case 6:return new F(function(){return _1d(_hB,_hH);});break;case 7:return new F(function(){return _1d(_hC,_hH);});break;case 8:return new F(function(){return _1d(_hD,_hH);});break;case 9:return new F(function(){return _1d(_hE,_hH);});break;case 10:return new F(function(){return _1d(_ho,_hH);});break;case 11:return new F(function(){return _1d(_hp,_hH);});break;case 12:return new F(function(){return _1d(_hq,_hH);});break;case 13:return new F(function(){return _1d(_hr,_hH);});break;case 14:return new F(function(){return _1d(_hs,_hH);});break;case 15:return new F(function(){return _1d(_ht,_hH);});break;case 16:return new F(function(){return _1d(_hu,_hH);});break;case 17:return new F(function(){return _1d(_hv,_hH);});break;default:return new F(function(){return _1d(_hw,_hH);});}},_hI=[0,125],_hJ=new T(function(){return B(unCStr("{handle: "));}),_hK=function(_hL,_hM,_hN,_hO,_hP,_hQ){var _hR=new T(function(){var _hS=new T(function(){return B(_hF(_hM,new T(function(){var _hT=E(_hO);return _hT[0]==0?E(_hQ):B(_1d(_hl,new T(function(){return B(_1d(_hT,[1,_hk,_hQ]));})));})));}),_hU=E(_hN);return _hU[0]==0?E(_hS):B(_1d(_hU,new T(function(){return B(_1d(_hj,_hS));})));}),_hV=E(_hP);if(!_hV[0]){var _hW=E(_hL);if(!_hW[0]){return E(_hR);}else{var _hX=E(_hW[1]);return _hX[0]==0?B(_1d(_hJ,new T(function(){return B(_1d(_hX[1],[1,_hI,new T(function(){return B(_1d(_hj,_hR));})]));}))):B(_1d(_hJ,new T(function(){return B(_1d(_hX[1],[1,_hI,new T(function(){return B(_1d(_hj,_hR));})]));})));}}else{return new F(function(){return _1d(_hV[1],new T(function(){return B(_1d(_hj,_hR));}));});}},_hY=function(_hZ){var _i0=E(_hZ);return new F(function(){return _hK(_i0[1],_i0[2],_i0[3],_i0[4],_i0[6],_0);});},_i1=function(_i2,_i3){var _i4=E(_i2);return new F(function(){return _hK(_i4[1],_i4[2],_i4[3],_i4[4],_i4[6],_i3);});},_i5=function(_i6,_i7){return new F(function(){return _1n(_i1,_i6,_i7);});},_i8=function(_i9,_ia,_ib){var _ic=E(_ia);return new F(function(){return _hK(_ic[1],_ic[2],_ic[3],_ic[4],_ic[6],_ib);});},_id=[0,_i8,_hY,_i5],_ie=new T(function(){return [0,_he,_id,_if,_hg];}),_if=function(_ig){return [0,_ie,_ig];},_ih=7,_ii=function(_ij){return [0,_75,_ih,_0,_ij,_75,_75];},_ik=function(_il,_){return new F(function(){return die(new T(function(){return B(_if(new T(function(){return B(_ii(_il));})));}));});},_im=function(_in,_){return new F(function(){return _ik(_in,_);});},_io=[0,114],_ip=[1,_io,_0],_iq=new T(function(){return B(_2K(0,6,_0));}),_ir=new T(function(){return B(unCStr("cx"));}),_is=new T(function(){return B(unCStr("cy"));}),_it=new T(function(){return B(unCStr("circle"));}),_iu=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_iv=new T(function(){return B(unCStr("board"));}),_iw=function(_){return _2u;},_ix=function(_iy,_iz,_){while(1){var _iA=(function(_iB,_iC,_){var _iD=E(_iC);if(!_iD[0]){return _2u;}else{var _iE=E(_iD[1]),_iF=_iE[1],_iG=[0,_iB],_iH=B(A(_3M,[function(_iI,_iJ,_iK,_){var _iL=jsFind(toJSStr(E(_iv))),_iM=_iL,_iN=E(_iM);if(!_iN[0]){var _iO=B(_im(_h5,_)),_iP=_iO;return new F(function(){return A(_iK,[_]);});}else{var _iQ=jsCreateElemNS(toJSStr(E(_iu)),toJSStr(E(_it))),_iR=_iQ,_iS=[0,_iR],_iT=B(A(_2x,[_2Q,_iS,_ip,_iq,_])),_iU=_iT,_iV=new T(function(){var _iW=B(_32(_iG,_iI));return [0,_iW[1],_iW[2]];}),_iX=B(A(_2x,[_2Q,_iS,_ir,new T(function(){return B(_2K(0,E(E(_iV)[1])[1],_0));}),_])),_iY=_iX,_iZ=B(A(_2x,[_2Q,_iS,_is,new T(function(){return B(_2K(0,E(E(_iV)[2])[1],_0));}),_])),_j0=_iZ,_j1=B(A(_2U,[_iS,_y,_iG,_iI,_iJ,_])),_j2=_j1,_j3=jsAppendChild(_iR,E(_iN[1])[1]);return new F(function(){return A(_iK,[_]);});}},_iw,_3Z,new T(function(){var _j4=E(_iE[2])[1];if(_j4>0){var _j5=function(_j6){return _j6>1?[1,_iF,new T(function(){return B(_j5(_j6-1|0));})]:E([1,_iF,_0]);},_j7=B(_j5(_j4));}else{var _j7=[0];}var _j8=_j7;return _j8;}),_])),_j9=_iH,_ja=E(_iB);if(_ja==2147483647){return _2u;}else{_iy=_ja+1|0;_iz=_iD[2];return null;}}})(_iy,_iz,_);if(_iA!=null){return _iA;}}},_jb=function(_){var _jc=B(_ix(0,_2j,_)),_jd=_jc;return new F(function(){return _gk(_2k,_);});},_je=function(_){return new F(function(){return _jb(_);});};
var hasteMain = function() {B(A(_je, [0]));};window.onload = hasteMain;