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

var _0=[0],_1=function(_2,_3){while(1){var _4=E(_2);if(!_4[0]){return E(_3);}else{_2=_4[2];var _5=[1,_4[1],_3];_3=_5;continue;}}},_6=[0,2],_7=[0,0],_8=[1,_7,_0],_9=[1,_7,_8],_a=[1,_7,_9],_b=[1,_7,_a],_c=[1,_7,_b],_d=[0,5],_e=[1,_d,_c],_f=[1,_7,_e],_g=[0,3],_h=[1,_g,_f],_i=[1,_7,_h],_j=[1,_7,_i],_k=[1,_7,_j],_l=[1,_7,_k],_m=[1,_d,_l],_n=[1,_7,_m],_o=[1,_7,_n],_p=[1,_7,_o],_q=[1,_7,_p],_r=[1,_7,_q],_s=[1,_7,_r],_t=[1,_7,_s],_u=[1,_7,_t],_v=[1,_7,_u],_w=[1,_7,_v],_x=[1,_6,_w],_y=1,_z=function(_A){var _B=E(_A);return _B[0]==0?[0]:[1,[0,_y,_B[1]],new T(function(){return B(_z(_B[2]));})];},_C=new T(function(){return B(_z(_x));}),_D=new T(function(){return B(_1(_C,_0));}),_E=0,_F=new T(function(){return B(unCStr("Control.Exception.Base"));}),_G=new T(function(){return B(unCStr("base"));}),_H=new T(function(){return B(unCStr("PatternMatchFail"));}),_I=new T(function(){var _J=hs_wordToWord64(18445595),_K=_J,_L=hs_wordToWord64(52003073),_M=_L;return [0,_K,_M,[0,_K,_M,_G,_F,_H],_0];}),_N=function(_O){return E(_I);},_P=function(_Q){return E(E(_Q)[1]);},_R=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_S=new T(function(){return B(err(_R));}),_T=function(_U,_V,_W){var _X=new T(function(){var _Y=B(A(_U,[_W])),_Z=B(A(_V,[new T(function(){var _10=E(_X);return _10[0]==0?E(_S):E(_10[1]);})])),_11=hs_eqWord64(_Y[1],_Z[1]),_12=_11;if(!E(_12)){var _13=[0];}else{var _14=hs_eqWord64(_Y[2],_Z[2]),_15=_14,_13=E(_15)==0?[0]:[1,_W];}var _16=_13,_17=_16;return _17;});return E(_X);},_18=function(_19){var _1a=E(_19);return new F(function(){return _T(B(_P(_1a[1])),_N,_1a[2]);});},_1b=function(_1c){return E(E(_1c)[1]);},_1d=function(_1e,_1f){var _1g=E(_1e);return _1g[0]==0?E(_1f):[1,_1g[1],new T(function(){return B(_1d(_1g[2],_1f));})];},_1h=function(_1i,_1j){return new F(function(){return _1d(E(_1i)[1],_1j);});},_1k=[0,44],_1l=[0,93],_1m=[0,91],_1n=function(_1o,_1p,_1q){var _1r=E(_1p);return _1r[0]==0?B(unAppCStr("[]",_1q)):[1,_1m,new T(function(){return B(A(_1o,[_1r[1],new T(function(){var _1s=function(_1t){var _1u=E(_1t);return _1u[0]==0?E([1,_1l,_1q]):[1,_1k,new T(function(){return B(A(_1o,[_1u[1],new T(function(){return B(_1s(_1u[2]));})]));})];};return B(_1s(_1r[2]));})]));})];},_1v=function(_1w,_1x){return new F(function(){return _1n(_1h,_1w,_1x);});},_1y=function(_1z,_1A,_1B){return new F(function(){return _1d(E(_1A)[1],_1B);});},_1C=[0,_1y,_1b,_1v],_1D=new T(function(){return [0,_N,_1C,_1E,_18];}),_1E=function(_1F){return [0,_1D,_1F];},_1G=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_1H=function(_1I,_1J){return new F(function(){return die(new T(function(){return B(A(_1J,[_1I]));}));});},_1K=function(_1L,_1M){var _1N=E(_1M);if(!_1N[0]){return [0,_0,_0];}else{var _1O=_1N[1];if(!B(A(_1L,[_1O]))){return [0,_0,_1N];}else{var _1P=new T(function(){var _1Q=B(_1K(_1L,_1N[2]));return [0,_1Q[1],_1Q[2]];});return [0,[1,_1O,new T(function(){return E(E(_1P)[1]);})],new T(function(){return E(E(_1P)[2]);})];}}},_1R=[0,32],_1S=[0,10],_1T=[1,_1S,_0],_1U=function(_1V){return E(E(_1V)[1])==124?false:true;},_1W=function(_1X,_1Y){var _1Z=B(_1K(_1U,B(unCStr(_1X)))),_20=_1Z[1],_21=function(_22,_23){return new F(function(){return _1d(_22,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_1d(_1Y,new T(function(){return B(_1d(_23,_1T));})));})));}));});},_24=E(_1Z[2]);if(!_24[0]){return new F(function(){return _21(_20,_0);});}else{return E(E(_24[1])[1])==124?B(_21(_20,[1,_1R,_24[2]])):B(_21(_20,_0));}},_25=function(_26){return new F(function(){return _1H([0,new T(function(){return B(_1W(_26,_1G));})],_1E);});},_27=new T(function(){return B(_25("main.hs:(228,20)-(229,55)|function whiteOrBlack"));}),_28=function(_29,_2a){var _2b=E(_29);if(!_2b[0]){return [0];}else{var _2c=E(_2a);return _2c[0]==0?[0]:[1,new T(function(){var _2d=E(_2c[1]);if(!E(_2d[1])){var _2e=E(_27);}else{if(!E(E(_2d[2])[1])){var _2f=E(_2b[1]),_2g=E(_2f[1])==0?E(_2f):[0,_E,_2f[2]];}else{var _2g=E(_2d);}var _2h=_2g,_2e=_2h;}var _2i=_2e;return _2i;}),new T(function(){return B(_28(_2b[2],_2c[2]));})];}},_2j=new T(function(){return B(_28(_D,_C));}),_2k=[0,_2j,_7,_7,_7,_7,_y,_y],_2l=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_2m=new T(function(){return B(err(_2l));}),_2n=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_2o=new T(function(){return B(err(_2n));}),_2p=function(_2q,_2r){while(1){var _2s=E(_2q);if(!_2s[0]){return E(_2o);}else{var _2t=E(_2r);if(!_2t){return E(_2s[1]);}else{_2q=_2s[2];_2r=_2t-1|0;continue;}}}},_2u=0,_2v=new T(function(){return B(unCStr("Black"));}),_2w=new T(function(){return B(unCStr("White"));}),_2x=new T(function(){return B(unCStr("pointIndex = "));}),_2y=new T(function(){return B(unCStr("onSideIndex = "));}),_2z=new T(function(){return B(unCStr("SidePlacement {"));}),_2A=new T(function(){return B(unCStr("onBarIndex = "));}),_2B=new T(function(){return B(unCStr("BarPlacement {"));}),_2C=new T(function(){return B(unCStr("PointPlacement {"));}),_2D=[0,125],_2E=new T(function(){return B(unCStr("onPointIndex = "));}),_2F=new T(function(){return B(unCStr(", "));}),_2G=function(_2H,_2I){var _2J=jsShowI(_2H),_2K=_2J;return new F(function(){return _1d(fromJSStr(_2K),_2I);});},_2L=[0,41],_2M=[0,40],_2N=function(_2O,_2P,_2Q){return _2P>=0?B(_2G(_2P,_2Q)):_2O<=6?B(_2G(_2P,_2Q)):[1,_2M,new T(function(){var _2R=jsShowI(_2P),_2S=_2R;return B(_1d(fromJSStr(_2S),[1,_2L,_2Q]));})];},_2T=function(_2U,_2V,_2W){var _2X=E(_2V);switch(_2X[0]){case 0:var _2Y=function(_2Z){return new F(function(){return _1d(_2x,new T(function(){return B(_2N(0,E(_2X[1])[1],new T(function(){return B(_1d(_2F,new T(function(){return B(_1d(_2E,new T(function(){return B(_2N(0,E(_2X[2])[1],[1,_2D,_2Z]));})));})));})));}));});};return _2U<11?B(_1d(_2C,new T(function(){return B(_2Y(_2W));}))):[1,_2M,new T(function(){return B(_1d(_2C,new T(function(){return B(_2Y([1,_2L,_2W]));})));})];case 1:var _30=function(_31){return new F(function(){return _1d(_2B,new T(function(){return B(_1d(_2A,new T(function(){return B(_2N(0,E(_2X[1])[1],[1,_2D,_31]));})));}));});};return _2U<11?B(_30(_2W)):[1,_2M,new T(function(){return B(_30([1,_2L,_2W]));})];default:var _32=function(_33){return new F(function(){return _1d(_2z,new T(function(){return B(_1d(_2y,new T(function(){return B(_2N(0,E(_2X[1])[1],[1,_2D,_33]));})));}));});};return _2U<11?B(_32(_2W)):[1,_2M,new T(function(){return B(_32([1,_2L,_2W]));})];}},_34=function(_35,_36,_37,_38){return new F(function(){return A(_35,[new T(function(){return function(_){var _39=jsSetAttr(E(_36)[1],toJSStr(E(_37)),toJSStr(E(_38)));return _2u;};})]);});},_3a=function(_3b){return E(_3b);},_3c=[0,95],_3d=function(_3e){var _3f=E(_3e);return E(_3f[1])==32?E(_3c):E(_3f);},_3g=new T(function(){return B(unCStr("class"));}),_3h=new T(function(){return B(unCStr("draggable "));}),_3i=[0,32],_3j=function(_3k,_3l){var _3m=E(_3l);return _3m[0]==0?[0]:[1,new T(function(){return B(A(_3k,[_3m[1]]));}),new T(function(){return B(_3j(_3k,_3m[2]));})];},_3n=function(_3o,_3p,_3q,_3r){return new F(function(){return _34(_3a,_3o,_3g,new T(function(){var _3s=new T(function(){var _3t=new T(function(){return B(_3j(_3d,B(_2T(0,_3q,_0))));});return E(_3r)==0?B(_1d(_2v,[1,_3i,_3t])):B(_1d(_2w,[1,_3i,_3t]));});return E(_3p)==0?E(_3r)==0?B(_1d(_3h,_3s)):E(_3s):E(_3r)==0?E(_3s):B(_1d(_3h,_3s));}));});},_3u=new T(function(){return B(_25("main.hs:(81,1)-(102,14)|function checkerPosition"));}),_3v=function(_3w){var _3x=E(_3w);if(!_3x[0]){var _3y=_3x[1],_3z=_3x[2];return [0,new T(function(){var _3A=E(_3y)[1];if(_3A>=12){var _3B=23-_3A|0;if(_3B>=6){var _3C=[0,25+(20+(imul(_3B,15)|0)|0)|0];}else{var _3C=[0,25+(imul(_3B,15)|0)|0];}var _3D=_3C,_3E=_3D;}else{if(_3A>=6){var _3F=[0,25+(20+(imul(_3A,15)|0)|0)|0];}else{var _3F=[0,25+(imul(_3A,15)|0)|0];}var _3E=_3F;}var _3G=_3E;return _3G;}),new T(function(){if(E(_3y)[1]>=12){var _3H=[0,203+(imul(imul(imul(-1,E(_3z)[1])|0,2)|0,6)|0)|0];}else{var _3H=[0,7+(imul(imul(E(_3z)[1],2)|0,6)|0)|0];}var _3I=_3H;return _3I;})];}else{return E(_3u);}},_3J=function(_3K,_3L,_3M,_){var _3N=jsElemsByClassName(toJSStr(B(_3j(_3d,B(_2T(0,_3K,_0)))))),_3O=_3N,_3P=B(_2p(_3O,0)),_3Q=B(_3v(_3L)),_3R=animateCircle_ffi(_3P[1],E(_3Q[1])[1],E(_3Q[2])[1],300);return new F(function(){return A(_3n,[_3P,_3M,_3L,_3M,_]);});},_3S=function(_3T,_3U){while(1){var _3V=E(_3T);if(!_3V){return E(_3U);}else{var _3W=E(_3U);if(!_3W[0]){return [0];}else{_3T=_3V-1|0;_3U=_3W[2];continue;}}}},_3X=function(_3Y,_3Z){if(_3Y<=_3Z){var _40=function(_41){return [1,[0,_41],new T(function(){if(_41!=_3Z){var _42=B(_40(_41+1|0));}else{var _42=[0];}return _42;})];};return new F(function(){return _40(_3Y);});}else{return [0];}},_43=function(_44,_45){var _46=function(_47,_48){while(1){var _49=(function(_4a,_4b){var _4c=E(_4b);if(!_4c[0]){return [0];}else{var _4d=_4c[2];if(!B(A(_44,[_4c[1]]))){var _4e=_4a+1|0;_48=_4d;_47=_4e;return null;}else{return [1,[0,_4a],new T(function(){return B(_46(_4a+1|0,_4d));})];}}})(_47,_48);if(_49!=null){return _49;}}};return new F(function(){return _46(0,_45);});},_4f=function(_4g,_4h,_4i,_4j){var _4k=E(_4i);if(!_4k[0]){return E(_4h);}else{var _4l=E(_4j);if(!_4l[0]){return E(_4h);}else{return new F(function(){return A(_4g,[_4k[1],_4l[1],new T(function(){return B(_4f(_4g,_4h,_4k[2],_4l[2]));})]);});}}},_4m=function(_4n){return new F(function(){return fromJSStr(E(_4n)[1]);});},_4o=function(_4p){var _4q=E(_4p);return E(_4q[1])==95?E(_3i):E(_4q);},_4r=function(_4s,_4t){if(_4s<=0){if(_4s>=0){return new F(function(){return quot(_4s,_4t);});}else{if(_4t<=0){return new F(function(){return quot(_4s,_4t);});}else{return quot(_4s+1|0,_4t)-1|0;}}}else{if(_4t>=0){if(_4s>=0){return new F(function(){return quot(_4s,_4t);});}else{if(_4t<=0){return new F(function(){return quot(_4s,_4t);});}else{return quot(_4s+1|0,_4t)-1|0;}}}else{return quot(_4s-1|0,_4t)-1|0;}}},_4u=new T(function(){return [0,B(_4r(210,2))];}),_4v=new T(function(){return B(_3X(0,2147483647));}),_4w=new T(function(){return B(_25("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_4x=function(_4y,_4z){while(1){var _4A=(function(_4B,_4C){var _4D=E(_4B);switch(_4D[0]){case 0:var _4E=E(_4C);if(!_4E[0]){return [0];}else{_4y=B(A(_4D[1],[_4E[1]]));_4z=_4E[2];return null;}break;case 1:var _4F=B(A(_4D[1],[_4C])),_4G=_4C;_4y=_4F;_4z=_4G;return null;case 2:return [0];case 3:return [1,[0,_4D[1],_4C],new T(function(){return B(_4x(_4D[2],_4C));})];default:return E(_4D[1]);}})(_4y,_4z);if(_4A!=null){return _4A;}}},_4H=function(_4I,_4J){var _4K=new T(function(){var _4L=E(_4J);if(_4L[0]==3){var _4M=[3,_4L[1],new T(function(){return B(_4H(_4I,_4L[2]));})];}else{var _4N=E(_4I);if(_4N[0]==2){var _4O=E(_4L);}else{var _4P=E(_4L);if(_4P[0]==2){var _4Q=E(_4N);}else{var _4R=new T(function(){var _4S=E(_4P);if(_4S[0]==4){var _4T=[1,function(_4U){return [4,new T(function(){return B(_1d(B(_4x(_4N,_4U)),_4S[1]));})];}];}else{var _4V=E(_4N);if(_4V[0]==1){var _4W=_4V[1],_4X=E(_4S);if(!_4X[0]){var _4Y=[1,function(_4Z){return new F(function(){return _4H(B(A(_4W,[_4Z])),_4X);});}];}else{var _4Y=[1,function(_50){return new F(function(){return _4H(B(A(_4W,[_50])),new T(function(){return B(A(_4X[1],[_50]));}));});}];}var _51=_4Y;}else{var _52=E(_4S);if(!_52[0]){var _53=E(_4w);}else{var _53=[1,function(_54){return new F(function(){return _4H(_4V,new T(function(){return B(A(_52[1],[_54]));}));});}];}var _51=_53;}var _4T=_51;}return _4T;}),_55=E(_4N);switch(_55[0]){case 1:var _56=E(_4P);if(_56[0]==4){var _57=[1,function(_58){return [4,new T(function(){return B(_1d(B(_4x(B(A(_55[1],[_58])),_58)),_56[1]));})];}];}else{var _57=E(_4R);}var _59=_57;break;case 4:var _5a=_55[1],_5b=E(_4P);switch(_5b[0]){case 0:var _5c=[1,function(_5d){return [4,new T(function(){return B(_1d(_5a,new T(function(){return B(_4x(_5b,_5d));})));})];}];break;case 1:var _5c=[1,function(_5e){return [4,new T(function(){return B(_1d(_5a,new T(function(){return B(_4x(B(A(_5b[1],[_5e])),_5e));})));})];}];break;default:var _5c=[4,new T(function(){return B(_1d(_5a,_5b[1]));})];}var _59=_5c;break;default:var _59=E(_4R);}var _4Q=_59;}var _4O=_4Q;}var _4M=_4O;}return _4M;}),_5f=E(_4I);switch(_5f[0]){case 0:var _5g=E(_4J);return _5g[0]==0?[0,function(_5h){return new F(function(){return _4H(B(A(_5f[1],[_5h])),new T(function(){return B(A(_5g[1],[_5h]));}));});}]:E(_4K);case 3:return [3,_5f[1],new T(function(){return B(_4H(_5f[2],_4J));})];default:return E(_4K);}},_5i=function(_5j,_5k){return E(_5j)[1]!=E(_5k)[1];},_5l=function(_5m,_5n){return E(_5m)[1]==E(_5n)[1];},_5o=[0,_5l,_5i],_5p=function(_5q){return E(E(_5q)[1]);},_5r=function(_5s,_5t,_5u){while(1){var _5v=E(_5t);if(!_5v[0]){return E(_5u)[0]==0?true:false;}else{var _5w=E(_5u);if(!_5w[0]){return false;}else{if(!B(A(_5p,[_5s,_5v[1],_5w[1]]))){return false;}else{_5t=_5v[2];_5u=_5w[2];continue;}}}}},_5x=function(_5y,_5z,_5A){return !B(_5r(_5y,_5z,_5A))?true:false;},_5B=function(_5C){return [0,function(_5D,_5E){return new F(function(){return _5r(_5C,_5D,_5E);});},function(_5D,_5E){return new F(function(){return _5x(_5C,_5D,_5E);});}];},_5F=new T(function(){return B(_5B(_5o));}),_5G=function(_5H,_5I){var _5J=E(_5H);switch(_5J[0]){case 0:return [0,function(_5K){return new F(function(){return _5G(B(A(_5J[1],[_5K])),_5I);});}];case 1:return [1,function(_5L){return new F(function(){return _5G(B(A(_5J[1],[_5L])),_5I);});}];case 2:return [2];case 3:return new F(function(){return _4H(B(A(_5I,[_5J[1]])),new T(function(){return B(_5G(_5J[2],_5I));}));});break;default:var _5M=function(_5N){var _5O=E(_5N);if(!_5O[0]){return [0];}else{var _5P=E(_5O[1]);return new F(function(){return _1d(B(_4x(B(A(_5I,[_5P[1]])),_5P[2])),new T(function(){return B(_5M(_5O[2]));}));});}},_5Q=B(_5M(_5J[1]));return _5Q[0]==0?[2]:[4,_5Q];}},_5R=[2],_5S=function(_5T){return [3,_5T,_5R];},_5U=function(_5V,_5W){var _5X=E(_5V);if(!_5X){return new F(function(){return A(_5W,[_2u]);});}else{return [0,function(_5Y){return E(new T(function(){return B(_5U(_5X-1|0,_5W));}));}];}},_5Z=function(_60,_61,_62){return [1,function(_63){return new F(function(){return A(function(_64,_65,_66){while(1){var _67=(function(_68,_69,_6a){var _6b=E(_68);switch(_6b[0]){case 0:var _6c=E(_69);if(!_6c[0]){return E(_61);}else{_64=B(A(_6b[1],[_6c[1]]));_65=_6c[2];var _6d=_6a+1|0;_66=_6d;return null;}break;case 1:var _6e=B(A(_6b[1],[_69])),_6f=_69,_6d=_6a;_64=_6e;_65=_6f;_66=_6d;return null;case 2:return E(_61);case 3:return function(_6g){return new F(function(){return _5U(_6a,function(_6h){return E(new T(function(){return B(_5G(_6b,_6g));}));});});};default:return function(_6i){return new F(function(){return _5G(_6b,_6i);});};}})(_64,_65,_66);if(_67!=null){return _67;}}},[new T(function(){return B(A(_60,[_5S]));}),_63,0,_62]);});}];},_6j=[6],_6k=new T(function(){return B(unCStr("valDig: Bad base"));}),_6l=new T(function(){return B(err(_6k));}),_6m=function(_6n,_6o){var _6p=function(_6q,_6r){var _6s=E(_6q);if(!_6s[0]){return function(_6t){return new F(function(){return A(_6t,[new T(function(){return B(A(_6r,[_0]));})]);});};}else{var _6u=E(_6s[1])[1],_6v=function(_6w){return function(_6x){return [0,function(_6y){return E(new T(function(){return B(A(new T(function(){return B(_6p(_6s[2],function(_6z){return new F(function(){return A(_6r,[[1,_6w,_6z]]);});}));}),[_6x]));}));}];};};switch(E(E(_6n)[1])){case 8:if(48>_6u){return function(_6A){return new F(function(){return A(_6A,[new T(function(){return B(A(_6r,[_0]));})]);});};}else{if(_6u>55){return function(_6B){return new F(function(){return A(_6B,[new T(function(){return B(A(_6r,[_0]));})]);});};}else{return new F(function(){return _6v([0,_6u-48|0]);});}}break;case 10:if(48>_6u){return function(_6C){return new F(function(){return A(_6C,[new T(function(){return B(A(_6r,[_0]));})]);});};}else{if(_6u>57){return function(_6D){return new F(function(){return A(_6D,[new T(function(){return B(A(_6r,[_0]));})]);});};}else{return new F(function(){return _6v([0,_6u-48|0]);});}}break;case 16:var _6E=new T(function(){if(97>_6u){if(65>_6u){var _6F=[0];}else{if(_6u>70){var _6G=[0];}else{var _6G=[1,[0,(_6u-65|0)+10|0]];}var _6F=_6G;}var _6H=_6F;}else{if(_6u>102){if(65>_6u){var _6I=[0];}else{if(_6u>70){var _6J=[0];}else{var _6J=[1,[0,(_6u-65|0)+10|0]];}var _6I=_6J;}var _6K=_6I;}else{var _6K=[1,[0,(_6u-97|0)+10|0]];}var _6H=_6K;}return _6H;});if(48>_6u){var _6L=E(_6E);if(!_6L[0]){return function(_6M){return new F(function(){return A(_6M,[new T(function(){return B(A(_6r,[_0]));})]);});};}else{return new F(function(){return _6v(_6L[1]);});}}else{if(_6u>57){var _6N=E(_6E);if(!_6N[0]){return function(_6O){return new F(function(){return A(_6O,[new T(function(){return B(A(_6r,[_0]));})]);});};}else{return new F(function(){return _6v(_6N[1]);});}}else{return new F(function(){return _6v([0,_6u-48|0]);});}}break;default:return E(_6l);}}};return [1,function(_6P){return new F(function(){return A(_6p,[_6P,_3a,function(_6Q){var _6R=E(_6Q);return _6R[0]==0?[2]:B(A(_6o,[_6R]));}]);});}];},_6S=[0,10],_6T=[0,1],_6U=[0,2147483647],_6V=function(_6W,_6X){while(1){var _6Y=E(_6W);if(!_6Y[0]){var _6Z=_6Y[1],_70=E(_6X);if(!_70[0]){var _71=_70[1],_72=addC(_6Z,_71);if(!E(_72[2])){return [0,_72[1]];}else{_6W=[1,I_fromInt(_6Z)];_6X=[1,I_fromInt(_71)];continue;}}else{_6W=[1,I_fromInt(_6Z)];_6X=_70;continue;}}else{var _73=E(_6X);if(!_73[0]){_6W=_6Y;_6X=[1,I_fromInt(_73[1])];continue;}else{return [1,I_add(_6Y[1],_73[1])];}}}},_74=new T(function(){return B(_6V(_6U,_6T));}),_75=function(_76){var _77=E(_76);if(!_77[0]){var _78=E(_77[1]);return _78==(-2147483648)?E(_74):[0, -_78];}else{return [1,I_negate(_77[1])];}},_79=[0,10],_7a=[0,0],_7b=function(_7c){return [0,_7c];},_7d=function(_7e,_7f){while(1){var _7g=E(_7e);if(!_7g[0]){var _7h=_7g[1],_7i=E(_7f);if(!_7i[0]){var _7j=_7i[1];if(!(imul(_7h,_7j)|0)){return [0,imul(_7h,_7j)|0];}else{_7e=[1,I_fromInt(_7h)];_7f=[1,I_fromInt(_7j)];continue;}}else{_7e=[1,I_fromInt(_7h)];_7f=_7i;continue;}}else{var _7k=E(_7f);if(!_7k[0]){_7e=_7g;_7f=[1,I_fromInt(_7k[1])];continue;}else{return [1,I_mul(_7g[1],_7k[1])];}}}},_7l=function(_7m,_7n,_7o){while(1){var _7p=E(_7o);if(!_7p[0]){return E(_7n);}else{var _7q=B(_6V(B(_7d(_7n,_7m)),B(_7b(E(_7p[1])[1]))));_7o=_7p[2];_7n=_7q;continue;}}},_7r=function(_7s){var _7t=new T(function(){return B(_4H(B(_4H([0,function(_7u){if(E(E(_7u)[1])==45){return new F(function(){return _6m(_6S,function(_7v){return new F(function(){return A(_7s,[[1,new T(function(){return B(_75(B(_7l(_79,_7a,_7v))));})]]);});});});}else{return [2];}}],[0,function(_7w){if(E(E(_7w)[1])==43){return new F(function(){return _6m(_6S,function(_7x){return new F(function(){return A(_7s,[[1,new T(function(){return B(_7l(_79,_7a,_7x));})]]);});});});}else{return [2];}}])),new T(function(){return B(_6m(_6S,function(_7y){return new F(function(){return A(_7s,[[1,new T(function(){return B(_7l(_79,_7a,_7y));})]]);});}));})));});return new F(function(){return _4H([0,function(_7z){return E(E(_7z)[1])==101?E(_7t):[2];}],[0,function(_7A){return E(E(_7A)[1])==69?E(_7t):[2];}]);});},_7B=[0],_7C=function(_7D){return new F(function(){return A(_7D,[_7B]);});},_7E=function(_7F){return new F(function(){return A(_7F,[_7B]);});},_7G=function(_7H){return [0,function(_7I){return E(E(_7I)[1])==46?E(new T(function(){return B(_6m(_6S,function(_7J){return new F(function(){return A(_7H,[[1,_7J]]);});}));})):[2];}];},_7K=function(_7L){return new F(function(){return _6m(_6S,function(_7M){return new F(function(){return _5Z(_7G,_7C,function(_7N){return new F(function(){return _5Z(_7r,_7E,function(_7O){return new F(function(){return A(_7L,[[5,[1,_7M,_7N,_7O]]]);});});});});});});});},_7P=function(_7Q,_7R,_7S){while(1){var _7T=E(_7S);if(!_7T[0]){return false;}else{if(!B(A(_5p,[_7Q,_7R,_7T[1]]))){_7S=_7T[2];continue;}else{return true;}}}},_7U=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_7V=function(_7W){return new F(function(){return _7P(_5o,_7W,_7U);});},_7X=[0,8],_7Y=[0,16],_7Z=function(_80){return [0,function(_81){return E(E(_81)[1])==48?E([0,function(_82){switch(E(E(_82)[1])){case 79:return E(new T(function(){return B(_6m(_7X,function(_83){return new F(function(){return A(_80,[[5,[0,_7X,_83]]]);});}));}));case 88:return E(new T(function(){return B(_6m(_7Y,function(_84){return new F(function(){return A(_80,[[5,[0,_7Y,_84]]]);});}));}));case 111:return E(new T(function(){return B(_6m(_7X,function(_85){return new F(function(){return A(_80,[[5,[0,_7X,_85]]]);});}));}));case 120:return E(new T(function(){return B(_6m(_7Y,function(_86){return new F(function(){return A(_80,[[5,[0,_7Y,_86]]]);});}));}));default:return [2];}}]):[2];}];},_87=false,_88=true,_89=function(_8a){return [0,function(_8b){switch(E(E(_8b)[1])){case 79:return E(new T(function(){return B(A(_8a,[_7X]));}));case 88:return E(new T(function(){return B(A(_8a,[_7Y]));}));case 111:return E(new T(function(){return B(A(_8a,[_7X]));}));case 120:return E(new T(function(){return B(A(_8a,[_7Y]));}));default:return [2];}}];},_8c=function(_8d){return new F(function(){return A(_8d,[_6S]);});},_8e=function(_8f){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_2N(9,_8f,_0));}))));});},_8g=function(_8h){var _8i=E(_8h);return _8i[0]==0?E(_8i[1]):I_toInt(_8i[1]);},_8j=function(_8k,_8l){var _8m=E(_8k);if(!_8m[0]){var _8n=_8m[1],_8o=E(_8l);return _8o[0]==0?_8n<=_8o[1]:I_compareInt(_8o[1],_8n)>=0;}else{var _8p=_8m[1],_8q=E(_8l);return _8q[0]==0?I_compareInt(_8p,_8q[1])<=0:I_compare(_8p,_8q[1])<=0;}},_8r=function(_8s){return [2];},_8t=function(_8u){var _8v=E(_8u);if(!_8v[0]){return E(_8r);}else{var _8w=_8v[1],_8x=E(_8v[2]);return _8x[0]==0?E(_8w):function(_8y){return new F(function(){return _4H(B(A(_8w,[_8y])),new T(function(){return B(A(new T(function(){return B(_8t(_8x));}),[_8y]));}));});};}},_8z=new T(function(){return B(unCStr("NUL"));}),_8A=function(_8B){return [2];},_8C=function(_8D){return new F(function(){return _8A(_8D);});},_8E=function(_8F,_8G){var _8H=function(_8I,_8J){var _8K=E(_8I);if(!_8K[0]){return function(_8L){return new F(function(){return A(_8L,[_8F]);});};}else{var _8M=E(_8J);return _8M[0]==0?E(_8A):E(_8K[1])[1]!=E(_8M[1])[1]?E(_8C):function(_8N){return [0,function(_8O){return E(new T(function(){return B(A(new T(function(){return B(_8H(_8K[2],_8M[2]));}),[_8N]));}));}];};}};return [1,function(_8P){return new F(function(){return A(_8H,[_8F,_8P,_8G]);});}];},_8Q=[0,0],_8R=function(_8S){return new F(function(){return _8E(_8z,function(_8T){return E(new T(function(){return B(A(_8S,[_8Q]));}));});});},_8U=new T(function(){return B(unCStr("STX"));}),_8V=[0,2],_8W=function(_8X){return new F(function(){return _8E(_8U,function(_8Y){return E(new T(function(){return B(A(_8X,[_8V]));}));});});},_8Z=new T(function(){return B(unCStr("ETX"));}),_90=[0,3],_91=function(_92){return new F(function(){return _8E(_8Z,function(_93){return E(new T(function(){return B(A(_92,[_90]));}));});});},_94=new T(function(){return B(unCStr("EOT"));}),_95=[0,4],_96=function(_97){return new F(function(){return _8E(_94,function(_98){return E(new T(function(){return B(A(_97,[_95]));}));});});},_99=new T(function(){return B(unCStr("ENQ"));}),_9a=[0,5],_9b=function(_9c){return new F(function(){return _8E(_99,function(_9d){return E(new T(function(){return B(A(_9c,[_9a]));}));});});},_9e=new T(function(){return B(unCStr("ACK"));}),_9f=[0,6],_9g=function(_9h){return new F(function(){return _8E(_9e,function(_9i){return E(new T(function(){return B(A(_9h,[_9f]));}));});});},_9j=new T(function(){return B(unCStr("BEL"));}),_9k=[0,7],_9l=function(_9m){return new F(function(){return _8E(_9j,function(_9n){return E(new T(function(){return B(A(_9m,[_9k]));}));});});},_9o=new T(function(){return B(unCStr("BS"));}),_9p=[0,8],_9q=function(_9r){return new F(function(){return _8E(_9o,function(_9s){return E(new T(function(){return B(A(_9r,[_9p]));}));});});},_9t=new T(function(){return B(unCStr("HT"));}),_9u=[0,9],_9v=function(_9w){return new F(function(){return _8E(_9t,function(_9x){return E(new T(function(){return B(A(_9w,[_9u]));}));});});},_9y=new T(function(){return B(unCStr("LF"));}),_9z=[0,10],_9A=function(_9B){return new F(function(){return _8E(_9y,function(_9C){return E(new T(function(){return B(A(_9B,[_9z]));}));});});},_9D=new T(function(){return B(unCStr("VT"));}),_9E=[0,11],_9F=function(_9G){return new F(function(){return _8E(_9D,function(_9H){return E(new T(function(){return B(A(_9G,[_9E]));}));});});},_9I=new T(function(){return B(unCStr("FF"));}),_9J=[0,12],_9K=function(_9L){return new F(function(){return _8E(_9I,function(_9M){return E(new T(function(){return B(A(_9L,[_9J]));}));});});},_9N=new T(function(){return B(unCStr("CR"));}),_9O=[0,13],_9P=function(_9Q){return new F(function(){return _8E(_9N,function(_9R){return E(new T(function(){return B(A(_9Q,[_9O]));}));});});},_9S=new T(function(){return B(unCStr("SI"));}),_9T=[0,15],_9U=function(_9V){return new F(function(){return _8E(_9S,function(_9W){return E(new T(function(){return B(A(_9V,[_9T]));}));});});},_9X=new T(function(){return B(unCStr("DLE"));}),_9Y=[0,16],_9Z=function(_a0){return new F(function(){return _8E(_9X,function(_a1){return E(new T(function(){return B(A(_a0,[_9Y]));}));});});},_a2=new T(function(){return B(unCStr("DC1"));}),_a3=[0,17],_a4=function(_a5){return new F(function(){return _8E(_a2,function(_a6){return E(new T(function(){return B(A(_a5,[_a3]));}));});});},_a7=new T(function(){return B(unCStr("DC2"));}),_a8=[0,18],_a9=function(_aa){return new F(function(){return _8E(_a7,function(_ab){return E(new T(function(){return B(A(_aa,[_a8]));}));});});},_ac=new T(function(){return B(unCStr("DC3"));}),_ad=[0,19],_ae=function(_af){return new F(function(){return _8E(_ac,function(_ag){return E(new T(function(){return B(A(_af,[_ad]));}));});});},_ah=new T(function(){return B(unCStr("DC4"));}),_ai=[0,20],_aj=function(_ak){return new F(function(){return _8E(_ah,function(_al){return E(new T(function(){return B(A(_ak,[_ai]));}));});});},_am=new T(function(){return B(unCStr("NAK"));}),_an=[0,21],_ao=function(_ap){return new F(function(){return _8E(_am,function(_aq){return E(new T(function(){return B(A(_ap,[_an]));}));});});},_ar=new T(function(){return B(unCStr("SYN"));}),_as=[0,22],_at=function(_au){return new F(function(){return _8E(_ar,function(_av){return E(new T(function(){return B(A(_au,[_as]));}));});});},_aw=new T(function(){return B(unCStr("ETB"));}),_ax=[0,23],_ay=function(_az){return new F(function(){return _8E(_aw,function(_aA){return E(new T(function(){return B(A(_az,[_ax]));}));});});},_aB=new T(function(){return B(unCStr("CAN"));}),_aC=[0,24],_aD=function(_aE){return new F(function(){return _8E(_aB,function(_aF){return E(new T(function(){return B(A(_aE,[_aC]));}));});});},_aG=new T(function(){return B(unCStr("EM"));}),_aH=[0,25],_aI=function(_aJ){return new F(function(){return _8E(_aG,function(_aK){return E(new T(function(){return B(A(_aJ,[_aH]));}));});});},_aL=new T(function(){return B(unCStr("SUB"));}),_aM=[0,26],_aN=function(_aO){return new F(function(){return _8E(_aL,function(_aP){return E(new T(function(){return B(A(_aO,[_aM]));}));});});},_aQ=new T(function(){return B(unCStr("ESC"));}),_aR=[0,27],_aS=function(_aT){return new F(function(){return _8E(_aQ,function(_aU){return E(new T(function(){return B(A(_aT,[_aR]));}));});});},_aV=new T(function(){return B(unCStr("FS"));}),_aW=[0,28],_aX=function(_aY){return new F(function(){return _8E(_aV,function(_aZ){return E(new T(function(){return B(A(_aY,[_aW]));}));});});},_b0=new T(function(){return B(unCStr("GS"));}),_b1=[0,29],_b2=function(_b3){return new F(function(){return _8E(_b0,function(_b4){return E(new T(function(){return B(A(_b3,[_b1]));}));});});},_b5=new T(function(){return B(unCStr("RS"));}),_b6=[0,30],_b7=function(_b8){return new F(function(){return _8E(_b5,function(_b9){return E(new T(function(){return B(A(_b8,[_b6]));}));});});},_ba=new T(function(){return B(unCStr("US"));}),_bb=[0,31],_bc=function(_bd){return new F(function(){return _8E(_ba,function(_be){return E(new T(function(){return B(A(_bd,[_bb]));}));});});},_bf=new T(function(){return B(unCStr("SP"));}),_bg=[0,32],_bh=function(_bi){return new F(function(){return _8E(_bf,function(_bj){return E(new T(function(){return B(A(_bi,[_bg]));}));});});},_bk=new T(function(){return B(unCStr("DEL"));}),_bl=[0,127],_bm=function(_bn){return new F(function(){return _8E(_bk,function(_bo){return E(new T(function(){return B(A(_bn,[_bl]));}));});});},_bp=[1,_bm,_0],_bq=[1,_bh,_bp],_br=[1,_bc,_bq],_bs=[1,_b7,_br],_bt=[1,_b2,_bs],_bu=[1,_aX,_bt],_bv=[1,_aS,_bu],_bw=[1,_aN,_bv],_bx=[1,_aI,_bw],_by=[1,_aD,_bx],_bz=[1,_ay,_by],_bA=[1,_at,_bz],_bB=[1,_ao,_bA],_bC=[1,_aj,_bB],_bD=[1,_ae,_bC],_bE=[1,_a9,_bD],_bF=[1,_a4,_bE],_bG=[1,_9Z,_bF],_bH=[1,_9U,_bG],_bI=[1,_9P,_bH],_bJ=[1,_9K,_bI],_bK=[1,_9F,_bJ],_bL=[1,_9A,_bK],_bM=[1,_9v,_bL],_bN=[1,_9q,_bM],_bO=[1,_9l,_bN],_bP=[1,_9g,_bO],_bQ=[1,_9b,_bP],_bR=[1,_96,_bQ],_bS=[1,_91,_bR],_bT=[1,_8W,_bS],_bU=[1,_8R,_bT],_bV=new T(function(){return B(unCStr("SOH"));}),_bW=[0,1],_bX=function(_bY){return new F(function(){return _8E(_bV,function(_bZ){return E(new T(function(){return B(A(_bY,[_bW]));}));});});},_c0=new T(function(){return B(unCStr("SO"));}),_c1=[0,14],_c2=function(_c3){return new F(function(){return _8E(_c0,function(_c4){return E(new T(function(){return B(A(_c3,[_c1]));}));});});},_c5=function(_c6){return new F(function(){return _5Z(_bX,_c2,_c6);});},_c7=[1,_c5,_bU],_c8=new T(function(){return B(_8t(_c7));}),_c9=[0,1114111],_ca=[0,34],_cb=[0,_ca,_88],_cc=[0,39],_cd=[0,_cc,_88],_ce=[0,92],_cf=[0,_ce,_88],_cg=[0,_9k,_88],_ch=[0,_9p,_88],_ci=[0,_9J,_88],_cj=[0,_9z,_88],_ck=[0,_9O,_88],_cl=[0,_9u,_88],_cm=[0,_9E,_88],_cn=[0,_8Q,_88],_co=[0,_bW,_88],_cp=[0,_8V,_88],_cq=[0,_90,_88],_cr=[0,_95,_88],_cs=[0,_9a,_88],_ct=[0,_9f,_88],_cu=[0,_9k,_88],_cv=[0,_9p,_88],_cw=[0,_9u,_88],_cx=[0,_9z,_88],_cy=[0,_9E,_88],_cz=[0,_9J,_88],_cA=[0,_9O,_88],_cB=[0,_c1,_88],_cC=[0,_9T,_88],_cD=[0,_9Y,_88],_cE=[0,_a3,_88],_cF=[0,_a8,_88],_cG=[0,_ad,_88],_cH=[0,_ai,_88],_cI=[0,_an,_88],_cJ=[0,_as,_88],_cK=[0,_ax,_88],_cL=[0,_aC,_88],_cM=[0,_aH,_88],_cN=[0,_aM,_88],_cO=[0,_aR,_88],_cP=[0,_aW,_88],_cQ=[0,_b1,_88],_cR=[0,_b6,_88],_cS=[0,_bb,_88],_cT=function(_cU){return new F(function(){return _4H([0,function(_cV){switch(E(E(_cV)[1])){case 34:return E(new T(function(){return B(A(_cU,[_cb]));}));case 39:return E(new T(function(){return B(A(_cU,[_cd]));}));case 92:return E(new T(function(){return B(A(_cU,[_cf]));}));case 97:return E(new T(function(){return B(A(_cU,[_cg]));}));case 98:return E(new T(function(){return B(A(_cU,[_ch]));}));case 102:return E(new T(function(){return B(A(_cU,[_ci]));}));case 110:return E(new T(function(){return B(A(_cU,[_cj]));}));case 114:return E(new T(function(){return B(A(_cU,[_ck]));}));case 116:return E(new T(function(){return B(A(_cU,[_cl]));}));case 118:return E(new T(function(){return B(A(_cU,[_cm]));}));default:return [2];}}],new T(function(){return B(_4H(B(_5Z(_89,_8c,function(_cW){return new F(function(){return _6m(_cW,function(_cX){var _cY=B(_7l(new T(function(){return B(_7b(E(_cW)[1]));}),_7a,_cX));return !B(_8j(_cY,_c9))?[2]:B(A(_cU,[[0,new T(function(){var _cZ=B(_8g(_cY));if(_cZ>>>0>1114111){var _d0=B(_8e(_cZ));}else{var _d0=[0,_cZ];}var _d1=_d0,_d2=_d1;return _d2;}),_88]]));});});})),new T(function(){return B(_4H([0,function(_d3){return E(E(_d3)[1])==94?E([0,function(_d4){switch(E(E(_d4)[1])){case 64:return E(new T(function(){return B(A(_cU,[_cn]));}));case 65:return E(new T(function(){return B(A(_cU,[_co]));}));case 66:return E(new T(function(){return B(A(_cU,[_cp]));}));case 67:return E(new T(function(){return B(A(_cU,[_cq]));}));case 68:return E(new T(function(){return B(A(_cU,[_cr]));}));case 69:return E(new T(function(){return B(A(_cU,[_cs]));}));case 70:return E(new T(function(){return B(A(_cU,[_ct]));}));case 71:return E(new T(function(){return B(A(_cU,[_cu]));}));case 72:return E(new T(function(){return B(A(_cU,[_cv]));}));case 73:return E(new T(function(){return B(A(_cU,[_cw]));}));case 74:return E(new T(function(){return B(A(_cU,[_cx]));}));case 75:return E(new T(function(){return B(A(_cU,[_cy]));}));case 76:return E(new T(function(){return B(A(_cU,[_cz]));}));case 77:return E(new T(function(){return B(A(_cU,[_cA]));}));case 78:return E(new T(function(){return B(A(_cU,[_cB]));}));case 79:return E(new T(function(){return B(A(_cU,[_cC]));}));case 80:return E(new T(function(){return B(A(_cU,[_cD]));}));case 81:return E(new T(function(){return B(A(_cU,[_cE]));}));case 82:return E(new T(function(){return B(A(_cU,[_cF]));}));case 83:return E(new T(function(){return B(A(_cU,[_cG]));}));case 84:return E(new T(function(){return B(A(_cU,[_cH]));}));case 85:return E(new T(function(){return B(A(_cU,[_cI]));}));case 86:return E(new T(function(){return B(A(_cU,[_cJ]));}));case 87:return E(new T(function(){return B(A(_cU,[_cK]));}));case 88:return E(new T(function(){return B(A(_cU,[_cL]));}));case 89:return E(new T(function(){return B(A(_cU,[_cM]));}));case 90:return E(new T(function(){return B(A(_cU,[_cN]));}));case 91:return E(new T(function(){return B(A(_cU,[_cO]));}));case 92:return E(new T(function(){return B(A(_cU,[_cP]));}));case 93:return E(new T(function(){return B(A(_cU,[_cQ]));}));case 94:return E(new T(function(){return B(A(_cU,[_cR]));}));case 95:return E(new T(function(){return B(A(_cU,[_cS]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_c8,[function(_d5){return new F(function(){return A(_cU,[[0,_d5,_88]]);});}]));})));})));}));});},_d6=function(_d7){return new F(function(){return A(_d7,[_2u]);});},_d8=function(_d9){var _da=E(_d9);if(!_da[0]){return E(_d6);}else{var _db=_da[2],_dc=E(E(_da[1])[1]);switch(_dc){case 9:return function(_dd){return [0,function(_de){return E(new T(function(){return B(A(new T(function(){return B(_d8(_db));}),[_dd]));}));}];};case 10:return function(_df){return [0,function(_dg){return E(new T(function(){return B(A(new T(function(){return B(_d8(_db));}),[_df]));}));}];};case 11:return function(_dh){return [0,function(_di){return E(new T(function(){return B(A(new T(function(){return B(_d8(_db));}),[_dh]));}));}];};case 12:return function(_dj){return [0,function(_dk){return E(new T(function(){return B(A(new T(function(){return B(_d8(_db));}),[_dj]));}));}];};case 13:return function(_dl){return [0,function(_dm){return E(new T(function(){return B(A(new T(function(){return B(_d8(_db));}),[_dl]));}));}];};case 32:return function(_dn){return [0,function(_do){return E(new T(function(){return B(A(new T(function(){return B(_d8(_db));}),[_dn]));}));}];};case 160:return function(_dp){return [0,function(_dq){return E(new T(function(){return B(A(new T(function(){return B(_d8(_db));}),[_dp]));}));}];};default:var _dr=u_iswspace(_dc),_ds=_dr;return E(_ds)==0?E(_d6):function(_dt){return [0,function(_du){return E(new T(function(){return B(A(new T(function(){return B(_d8(_db));}),[_dt]));}));}];};}}},_dv=function(_dw){var _dx=new T(function(){return B(_dv(_dw));}),_dy=[1,function(_dz){return new F(function(){return A(_d8,[_dz,function(_dA){return E([0,function(_dB){return E(E(_dB)[1])==92?E(_dx):[2];}]);}]);});}];return new F(function(){return _4H([0,function(_dC){return E(E(_dC)[1])==92?E([0,function(_dD){var _dE=E(E(_dD)[1]);switch(_dE){case 9:return E(_dy);case 10:return E(_dy);case 11:return E(_dy);case 12:return E(_dy);case 13:return E(_dy);case 32:return E(_dy);case 38:return E(_dx);case 160:return E(_dy);default:var _dF=u_iswspace(_dE),_dG=_dF;return E(_dG)==0?[2]:E(_dy);}}]):[2];}],[0,function(_dH){var _dI=E(_dH);return E(_dI[1])==92?E(new T(function(){return B(_cT(_dw));})):B(A(_dw,[[0,_dI,_87]]));}]);});},_dJ=function(_dK,_dL){return new F(function(){return _dv(function(_dM){var _dN=E(_dM),_dO=E(_dN[1]);if(E(_dO[1])==34){if(!E(_dN[2])){return E(new T(function(){return B(A(_dL,[[1,new T(function(){return B(A(_dK,[_0]));})]]));}));}else{return new F(function(){return _dJ(function(_dP){return new F(function(){return A(_dK,[[1,_dO,_dP]]);});},_dL);});}}else{return new F(function(){return _dJ(function(_dQ){return new F(function(){return A(_dK,[[1,_dO,_dQ]]);});},_dL);});}});});},_dR=new T(function(){return B(unCStr("_\'"));}),_dS=function(_dT){var _dU=u_iswalnum(_dT),_dV=_dU;return E(_dV)==0?B(_7P(_5o,[0,_dT],_dR)):true;},_dW=function(_dX){return new F(function(){return _dS(E(_dX)[1]);});},_dY=new T(function(){return B(unCStr(",;()[]{}`"));}),_dZ=function(_e0){return new F(function(){return A(_e0,[_0]);});},_e1=function(_e2,_e3){var _e4=function(_e5){var _e6=E(_e5);if(!_e6[0]){return E(_dZ);}else{var _e7=_e6[1];return !B(A(_e2,[_e7]))?E(_dZ):function(_e8){return [0,function(_e9){return E(new T(function(){return B(A(new T(function(){return B(_e4(_e6[2]));}),[function(_ea){return new F(function(){return A(_e8,[[1,_e7,_ea]]);});}]));}));}];};}};return [1,function(_eb){return new F(function(){return A(_e4,[_eb,_e3]);});}];},_ec=new T(function(){return B(unCStr(".."));}),_ed=new T(function(){return B(unCStr("::"));}),_ee=new T(function(){return B(unCStr("->"));}),_ef=[0,64],_eg=[1,_ef,_0],_eh=[0,126],_ei=[1,_eh,_0],_ej=new T(function(){return B(unCStr("=>"));}),_ek=[1,_ej,_0],_el=[1,_ei,_ek],_em=[1,_eg,_el],_en=[1,_ee,_em],_eo=new T(function(){return B(unCStr("<-"));}),_ep=[1,_eo,_en],_eq=[0,124],_er=[1,_eq,_0],_es=[1,_er,_ep],_et=[1,_ce,_0],_eu=[1,_et,_es],_ev=[0,61],_ew=[1,_ev,_0],_ex=[1,_ew,_eu],_ey=[1,_ed,_ex],_ez=[1,_ec,_ey],_eA=function(_eB){return new F(function(){return _4H([1,function(_eC){return E(_eC)[0]==0?E(new T(function(){return B(A(_eB,[_6j]));})):[2];}],new T(function(){return B(_4H([0,function(_eD){return E(E(_eD)[1])==39?E([0,function(_eE){var _eF=E(_eE);switch(E(_eF[1])){case 39:return [2];case 92:return E(new T(function(){return B(_cT(function(_eG){var _eH=E(_eG);return new F(function(){return (function(_eI,_eJ){var _eK=new T(function(){return B(A(_eB,[[0,_eI]]));});return !E(_eJ)?E(E(_eI)[1])==39?[2]:[0,function(_eL){return E(E(_eL)[1])==39?E(_eK):[2];}]:[0,function(_eM){return E(E(_eM)[1])==39?E(_eK):[2];}];})(_eH[1],_eH[2]);});}));}));default:return [0,function(_eN){return E(E(_eN)[1])==39?E(new T(function(){return B(A(_eB,[[0,_eF]]));})):[2];}];}}]):[2];}],new T(function(){return B(_4H([0,function(_eO){return E(E(_eO)[1])==34?E(new T(function(){return B(_dJ(_3a,_eB));})):[2];}],new T(function(){return B(_4H([0,function(_eP){return !B(_7P(_5o,_eP,_dY))?[2]:B(A(_eB,[[2,[1,_eP,_0]]]));}],new T(function(){return B(_4H([0,function(_eQ){if(!B(_7P(_5o,_eQ,_7U))){return [2];}else{return new F(function(){return _e1(_7V,function(_eR){var _eS=[1,_eQ,_eR];return !B(_7P(_5F,_eS,_ez))?B(A(_eB,[[4,_eS]])):B(A(_eB,[[2,_eS]]));});});}}],new T(function(){return B(_4H([0,function(_eT){var _eU=E(_eT),_eV=_eU[1],_eW=u_iswalpha(_eV),_eX=_eW;if(!E(_eX)){if(E(_eV)==95){return new F(function(){return _e1(_dW,function(_eY){return new F(function(){return A(_eB,[[3,[1,_eU,_eY]]]);});});});}else{return [2];}}else{return new F(function(){return _e1(_dW,function(_eZ){return new F(function(){return A(_eB,[[3,[1,_eU,_eZ]]]);});});});}}],new T(function(){return B(_5Z(_7Z,_7K,_eB));})));})));})));})));})));}));});},_f0=function(_f1){return [1,function(_f2){return new F(function(){return A(_d8,[_f2,function(_f3){return E(new T(function(){return B(_eA(_f1));}));}]);});}];},_f4=[0,0],_f5=function(_f6,_f7){return new F(function(){return _f0(function(_f8){var _f9=E(_f8);if(_f9[0]==2){var _fa=E(_f9[1]);return _fa[0]==0?[2]:E(E(_fa[1])[1])==40?E(_fa[2])[0]==0?E(new T(function(){return B(A(_f6,[_f4,function(_fb){return new F(function(){return _f0(function(_fc){var _fd=E(_fc);if(_fd[0]==2){var _fe=E(_fd[1]);return _fe[0]==0?[2]:E(E(_fe[1])[1])==41?E(_fe[2])[0]==0?E(new T(function(){return B(A(_f7,[_fb]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_ff=function(_fg,_fh,_fi){var _fj=function(_fk,_fl){return new F(function(){return _4H(B(_f0(function(_fm){var _fn=E(_fm);if(_fn[0]==4){var _fo=E(_fn[1]);if(!_fo[0]){return new F(function(){return A(_fg,[_fn,_fk,_fl]);});}else{return E(E(_fo[1])[1])==45?E(_fo[2])[0]==0?E([1,function(_fp){return new F(function(){return A(_d8,[_fp,function(_fq){return E(new T(function(){return B(_eA(function(_fr){return new F(function(){return A(_fg,[_fr,_fk,function(_fs){return new F(function(){return A(_fl,[new T(function(){return [0, -E(_fs)[1]];})]);});}]);});}));}));}]);});}]):B(A(_fg,[_fn,_fk,_fl])):B(A(_fg,[_fn,_fk,_fl]));}}else{return new F(function(){return A(_fg,[_fn,_fk,_fl]);});}})),new T(function(){return B(_f5(_fj,_fl));}));});};return new F(function(){return _fj(_fh,_fi);});},_ft=function(_fu,_fv){return [2];},_fw=function(_fx,_fy){return new F(function(){return _ft(_fx,_fy);});},_fz=function(_fA){var _fB=E(_fA);return _fB[0]==0?[1,new T(function(){return B(_7l(new T(function(){return B(_7b(E(_fB[1])[1]));}),_7a,_fB[2]));})]:E(_fB[2])[0]==0?E(_fB[3])[0]==0?[1,new T(function(){return B(_7l(_79,_7a,_fB[1]));})]:[0]:[0];},_fC=function(_fD){var _fE=E(_fD);if(_fE[0]==5){var _fF=B(_fz(_fE[1]));return _fF[0]==0?E(_ft):function(_fG,_fH){return new F(function(){return A(_fH,[new T(function(){return [0,B(_8g(_fF[1]))];})]);});};}else{return E(_fw);}},_fI=function(_fJ,_fK){while(1){var _fL=E(_fJ);if(!_fL[0]){return E(_fK)[0]==0?true:false;}else{var _fM=E(_fK);if(!_fM[0]){return false;}else{if(E(_fL[1])[1]!=E(_fM[1])[1]){return false;}else{_fJ=_fL[2];_fK=_fM[2];continue;}}}}},_fN=new T(function(){return B(unCStr("onBarIndex"));}),_fO=new T(function(){return B(unCStr("BarPlacement"));}),_fP=new T(function(){return B(unCStr("onSideIndex"));}),_fQ=new T(function(){return B(unCStr("SidePlacement"));}),_fR=function(_fS,_fT){var _fU=new T(function(){if(_fS>11){var _fV=[2];}else{var _fV=[1,function(_fW){return new F(function(){return A(_d8,[_fW,function(_fX){return E(new T(function(){return B(_eA(function(_fY){var _fZ=E(_fY);return _fZ[0]==3?!B(_fI(_fZ[1],_fQ))?[2]:E([1,function(_g0){return new F(function(){return A(_d8,[_g0,function(_g1){return E(new T(function(){return B(_eA(function(_g2){var _g3=E(_g2);if(_g3[0]==2){var _g4=E(_g3[1]);return _g4[0]==0?[2]:E(E(_g4[1])[1])==123?E(_g4[2])[0]==0?E([1,function(_g5){return new F(function(){return A(_d8,[_g5,function(_g6){return E(new T(function(){return B(_eA(function(_g7){var _g8=E(_g7);return _g8[0]==3?!B(_fI(_g8[1],_fP))?[2]:E([1,function(_g9){return new F(function(){return A(_d8,[_g9,function(_ga){return E(new T(function(){return B(_eA(function(_gb){var _gc=E(_gb);if(_gc[0]==2){var _gd=E(_gc[1]);return _gd[0]==0?[2]:E(E(_gd[1])[1])==61?E(_gd[2])[0]==0?E(new T(function(){return B(_ff(_fC,_f4,function(_ge){return new F(function(){return _f0(function(_gf){var _gg=E(_gf);if(_gg[0]==2){var _gh=E(_gg[1]);return _gh[0]==0?[2]:E(E(_gh[1])[1])==125?E(_gh[2])[0]==0?E(new T(function(){return B(A(_fT,[[2,_ge]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}];}return _fV;});if(_fS>11){return new F(function(){return _4H(_5R,_fU);});}else{return new F(function(){return _4H(B(_f0(function(_gi){var _gj=E(_gi);return _gj[0]==3?!B(_fI(_gj[1],_fO))?[2]:E([1,function(_gk){return new F(function(){return A(_d8,[_gk,function(_gl){return E(new T(function(){return B(_eA(function(_gm){var _gn=E(_gm);if(_gn[0]==2){var _go=E(_gn[1]);return _go[0]==0?[2]:E(E(_go[1])[1])==123?E(_go[2])[0]==0?E([1,function(_gp){return new F(function(){return A(_d8,[_gp,function(_gq){return E(new T(function(){return B(_eA(function(_gr){var _gs=E(_gr);return _gs[0]==3?!B(_fI(_gs[1],_fN))?[2]:E([1,function(_gt){return new F(function(){return A(_d8,[_gt,function(_gu){return E(new T(function(){return B(_eA(function(_gv){var _gw=E(_gv);if(_gw[0]==2){var _gx=E(_gw[1]);return _gx[0]==0?[2]:E(E(_gx[1])[1])==61?E(_gx[2])[0]==0?E(new T(function(){return B(_ff(_fC,_f4,function(_gy){return new F(function(){return _f0(function(_gz){var _gA=E(_gz);if(_gA[0]==2){var _gB=E(_gA[1]);return _gB[0]==0?[2]:E(E(_gB[1])[1])==125?E(_gB[2])[0]==0?E(new T(function(){return B(A(_fT,[[1,_gy]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),_fU);});}},_gC=new T(function(){return B(unCStr("onPointIndex"));}),_gD=new T(function(){return B(unCStr("pointIndex"));}),_gE=new T(function(){return B(unCStr("PointPlacement"));}),_gF=function(_gG,_gH){if(_gG>11){return new F(function(){return _4H(_5R,new T(function(){return B(_fR(_gG,_gH));}));});}else{return new F(function(){return _4H(B(_f0(function(_gI){var _gJ=E(_gI);return _gJ[0]==3?!B(_fI(_gJ[1],_gE))?[2]:E([1,function(_gK){return new F(function(){return A(_d8,[_gK,function(_gL){return E(new T(function(){return B(_eA(function(_gM){var _gN=E(_gM);if(_gN[0]==2){var _gO=E(_gN[1]);return _gO[0]==0?[2]:E(E(_gO[1])[1])==123?E(_gO[2])[0]==0?E([1,function(_gP){return new F(function(){return A(_d8,[_gP,function(_gQ){return E(new T(function(){return B(_eA(function(_gR){var _gS=E(_gR);return _gS[0]==3?!B(_fI(_gS[1],_gD))?[2]:E([1,function(_gT){return new F(function(){return A(_d8,[_gT,function(_gU){return E(new T(function(){return B(_eA(function(_gV){var _gW=E(_gV);if(_gW[0]==2){var _gX=E(_gW[1]);return _gX[0]==0?[2]:E(E(_gX[1])[1])==61?E(_gX[2])[0]==0?E(new T(function(){return B(_ff(_fC,_f4,function(_gY){return new F(function(){return _f0(function(_gZ){var _h0=E(_gZ);if(_h0[0]==2){var _h1=E(_h0[1]);return _h1[0]==0?[2]:E(E(_h1[1])[1])==44?E(_h1[2])[0]==0?E([1,function(_h2){return new F(function(){return A(_d8,[_h2,function(_h3){return E(new T(function(){return B(_eA(function(_h4){var _h5=E(_h4);return _h5[0]==3?!B(_fI(_h5[1],_gC))?[2]:E([1,function(_h6){return new F(function(){return A(_d8,[_h6,function(_h7){return E(new T(function(){return B(_eA(function(_h8){var _h9=E(_h8);if(_h9[0]==2){var _ha=E(_h9[1]);return _ha[0]==0?[2]:E(E(_ha[1])[1])==61?E(_ha[2])[0]==0?E(new T(function(){return B(_ff(_fC,_f4,function(_hb){return new F(function(){return _f0(function(_hc){var _hd=E(_hc);if(_hd[0]==2){var _he=E(_hd[1]);return _he[0]==0?[2]:E(E(_he[1])[1])==125?E(_he[2])[0]==0?E(new T(function(){return B(A(_gH,[[0,_gY,_hb]]));})):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}});});}));})):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];}));}));}]);});}]):[2]:[2];}else{return [2];}}));}));}]);});}]):[2];})),new T(function(){return B(_fR(_gG,_gH));}));});}},_hf=function(_hg,_hh){return new F(function(){return _gF(E(_hg)[1],_hh);});},_hi=function(_hj,_hk){var _hl=function(_hm){return function(_hn){return new F(function(){return _4H(B(A(new T(function(){return B(A(_hj,[_hm]));}),[_hn])),new T(function(){return B(_f5(_hl,_hn));}));});};};return new F(function(){return _hl(_hk);});},_ho=function(_hp){return [1,function(_hq){return new F(function(){return A(_d8,[_hq,function(_hr){return E([3,_hp,_5R]);}]);});}];},_hs=new T(function(){return B(A(_hi,[_hf,_f4,_ho]));}),_ht=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_hu=new T(function(){return B(err(_ht));}),_hv=function(_hw,_hx){return new F(function(){return A(_hx,[_y]);});},_hy=[0,_2w,_hv],_hz=[1,_hy,_0],_hA=function(_hB,_hC){return new F(function(){return A(_hC,[_E]);});},_hD=[0,_2v,_hA],_hE=[1,_hD,_hz],_hF=function(_hG,_hH,_hI){var _hJ=E(_hG);if(!_hJ[0]){return [2];}else{var _hK=E(_hJ[1]),_hL=_hK[1],_hM=new T(function(){return B(A(_hK[2],[_hH,_hI]));});return new F(function(){return _4H(B(_f0(function(_hN){var _hO=E(_hN);switch(_hO[0]){case 3:return !B(_fI(_hL,_hO[1]))?[2]:E(_hM);case 4:return !B(_fI(_hL,_hO[1]))?[2]:E(_hM);default:return [2];}})),new T(function(){return B(_hF(_hJ[2],_hH,_hI));}));});}},_hP=function(_hQ,_hR){return new F(function(){return _hF(_hE,_hQ,_hR);});},_hS=new T(function(){return B(A(_hi,[_hP,_f4,_ho]));}),_hT=new T(function(){return B(err(_ht));}),_hU=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_hV=new T(function(){return B(err(_hU));}),_hW=new T(function(){return B(err(_hU));}),_hX=function(_hY,_hZ,_i0){return _i0<=_hZ?[1,[0,_hY],new T(function(){var _i1=_hZ-_hY|0,_i2=function(_i3){return _i3>=(_i0-_i1|0)?[1,[0,_i3],new T(function(){return B(_i2(_i3+_i1|0));})]:[1,[0,_i3],_0];};return B(_i2(_hZ));})]:_i0<=_hY?[1,[0,_hY],_0]:[0];},_i4=function(_i5,_i6,_i7){return _i7>=_i6?[1,[0,_i5],new T(function(){var _i8=_i6-_i5|0,_i9=function(_ia){return _ia<=(_i7-_i8|0)?[1,[0,_ia],new T(function(){return B(_i9(_ia+_i8|0));})]:[1,[0,_ia],_0];};return B(_i9(_i6));})]:_i7>=_i5?[1,[0,_i5],_0]:[0];},_ib=function(_ic,_id){return _id<_ic?B(_hX(_ic,_id,-2147483648)):B(_i4(_ic,_id,2147483647));},_ie=new T(function(){return B(_ib(135,150));}),_if=function(_ig,_ih){var _ii=E(_ig);if(!_ii){return [0];}else{var _ij=E(_ih);return _ij[0]==0?[0]:[1,_ij[1],new T(function(){return B(_if(_ii-1|0,_ij[2]));})];}},_ik=new T(function(){return B(_if(6,_ie));}),_il=function(_im,_in){var _io=E(_im);if(!_io[0]){return E(_ik);}else{var _ip=_io[1];return _in>1?[1,_ip,new T(function(){return B(_il(_io[2],_in-1|0));})]:[1,_ip,_ik];}},_iq=new T(function(){return B(_ib(25,40));}),_ir=new T(function(){return B(_il(_iq,6));}),_is=function(_it){while(1){var _iu=(function(_iv){var _iw=E(_iv);if(!_iw[0]){return [0];}else{var _ix=_iw[2],_iy=E(_iw[1]);if(!E(_iy[2])[0]){return [1,_iy[1],new T(function(){return B(_is(_ix));})];}else{_it=_ix;return null;}}})(_it);if(_iu!=null){return _iu;}}},_iz=function(_iA,_iB){var _iC=E(_iB);if(!_iC[0]){return [0,_0,_0];}else{var _iD=_iC[1];if(!B(A(_iA,[_iD]))){var _iE=new T(function(){var _iF=B(_iz(_iA,_iC[2]));return [0,_iF[1],_iF[2]];});return [0,[1,_iD,new T(function(){return E(E(_iE)[1]);})],new T(function(){return E(E(_iE)[2]);})];}else{return [0,_0,_iC];}}},_iG=function(_iH,_iI){while(1){var _iJ=E(_iI);if(!_iJ[0]){return [0];}else{if(!B(A(_iH,[_iJ[1]]))){return E(_iJ);}else{_iI=_iJ[2];continue;}}}},_iK=function(_iL){var _iM=E(_iL);switch(_iM){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _iN=u_iswspace(_iM),_iO=_iN;return E(_iO)==0?false:true;}},_iP=function(_iQ){return new F(function(){return _iK(E(_iQ)[1]);});},_iR=function(_iS){var _iT=B(_iG(_iP,_iS));if(!_iT[0]){return [0];}else{var _iU=new T(function(){var _iV=B(_iz(_iP,_iT));return [0,_iV[1],_iV[2]];});return [1,new T(function(){return E(E(_iU)[1]);}),new T(function(){return B(_iR(E(_iU)[2]));})];}},_iW=function(_iX,_){var _iY=setDropCheckerCallback_ffi(function(_iZ,_j0,_j1){var _j2=E(_iX),_j3=_j2[1],_j4=_j2[6],_j5=new T(function(){return B(_iR(B(_4m(_iZ))));}),_j6=B(_is(B(_4x(_hs,new T(function(){return B(_3j(_4o,B(_2p(_j5,2))));})))));if(!_j6[0]){return E(_hW);}else{if(!E(_j6[2])[0]){var _j7=E(_j6[1]);if(!_j7[0]){var _j8=B(_43(function(_j9){var _ja=E(_j9)[1]-E(_j0)[1];return _ja<0? -_ja<7:_ja<7;},_ir));if(!_j8[0]){return function(_6i){return new F(function(){return _3J(_j7,_j7,_j4,_6i);});};}else{var _jb=_j8[1],_jc=function(_jd,_je,_){var _jf=E(_j7[1]),_jg=_jf[1];if(_jd<=_jg){return new F(function(){return _3J(_j7,_j7,_j4,_);});}else{var _jh=B(_is(B(_4x(_hS,new T(function(){return B(_2p(_j5,1));})))));if(!_jh[0]){return E(_hV);}else{var _ji=_jh[1];if(!E(_jh[2])[0]){if(_jd>=0){var _jj=B(_2p(_j3,_jd)),_jk=function(_){var _jl=B(_3J(_j7,[0,_je,new T(function(){if(_jd>=0){var _jm=E(B(_2p(_j3,_jd))[2]);}else{var _jm=E(_2m);}return _jm;})],_j4,_)),_jn=_jl;if(_jg>=0){var _jo=new T(function(){return B(_4f(function(_jp,_jq,_jr){return [1,new T(function(){var _js=E(_jp)[1];return _js!=_jg?_js!=_jd?E(_jq):[0,new T(function(){if(_jg>=0){var _jt=E(B(_2p(_j3,_jg))[1]);}else{var _jt=E(_2m);}return _jt;}),new T(function(){return [0,E(E(_jq)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_jq)[1]);}),new T(function(){return [0,E(E(_jq)[2])[1]-1|0];})];}),_jr];},_0,_4v,_j3));}),_ju=B((function(_jv,_){while(1){var _jw=(function(_jx,_){var _jy=E(_jx);if(!_jy[0]){return _2u;}else{var _jz=_jy[1],_jA=B(_3J([0,_jf,_jz],[0,_jf,new T(function(){return [0,E(_jz)[1]-1|0];})],_j4,_)),_jB=_jA;_jv=_jy[2];return null;}})(_jv,_);if(_jw!=null){return _jw;}}})(B(_3S(1,B(_3X(E(_j7[2])[1],E(B(_2p(_jo,_jg))[2])[1])))),_)),_jC=_ju;return new F(function(){return _iW([0,_jo,_j2[2],_j2[3],_j2[4],_j2[5],_j4,_j2[7]],_);});}else{return E(_2m);}},_jD=function(_){return E(_jj[2])[1]>=2?B(_3J(_j7,_j7,_j4,_)):B(_jk(_));};return E(_jj[1])==0?E(_ji)==0?B(_jk(_)):B(_jD(_)):E(_ji)==0?B(_jD(_)):B(_jk(_));}else{return E(_2m);}}else{return E(_hT);}}}};if(E(_j1)[1]<=E(_4u)[1]){var _jE=E(_jb);return function(_6i){return new F(function(){return _jc(_jE[1],_jE,_6i);});};}else{var _jF=23-E(_jb)[1]|0;return function(_6i){return new F(function(){return _jc(_jF,[0,_jF],_6i);});};}}}else{return function(_6i){return new F(function(){return _3J(_j7,_j7,_j4,_6i);});};}}else{return E(_hu);}}});return _2u;},_jG=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:139:5-10"));}),_jH=function(_){return _2u;},_jI=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_jJ=new T(function(){return B(unCStr("base"));}),_jK=new T(function(){return B(unCStr("IOException"));}),_jL=new T(function(){var _jM=hs_wordToWord64(4053623282),_jN=_jM,_jO=hs_wordToWord64(3693590983),_jP=_jO;return [0,_jN,_jP,[0,_jN,_jP,_jJ,_jI,_jK],_0];}),_jQ=function(_jR){return E(_jL);},_jS=function(_jT){var _jU=E(_jT);return new F(function(){return _T(B(_P(_jU[1])),_jQ,_jU[2]);});},_jV=new T(function(){return B(unCStr(": "));}),_jW=[0,41],_jX=new T(function(){return B(unCStr(" ("));}),_jY=new T(function(){return B(unCStr("already exists"));}),_jZ=new T(function(){return B(unCStr("does not exist"));}),_k0=new T(function(){return B(unCStr("protocol error"));}),_k1=new T(function(){return B(unCStr("failed"));}),_k2=new T(function(){return B(unCStr("invalid argument"));}),_k3=new T(function(){return B(unCStr("inappropriate type"));}),_k4=new T(function(){return B(unCStr("hardware fault"));}),_k5=new T(function(){return B(unCStr("unsupported operation"));}),_k6=new T(function(){return B(unCStr("timeout"));}),_k7=new T(function(){return B(unCStr("resource vanished"));}),_k8=new T(function(){return B(unCStr("interrupted"));}),_k9=new T(function(){return B(unCStr("resource busy"));}),_ka=new T(function(){return B(unCStr("resource exhausted"));}),_kb=new T(function(){return B(unCStr("end of file"));}),_kc=new T(function(){return B(unCStr("illegal operation"));}),_kd=new T(function(){return B(unCStr("permission denied"));}),_ke=new T(function(){return B(unCStr("user error"));}),_kf=new T(function(){return B(unCStr("unsatisified constraints"));}),_kg=new T(function(){return B(unCStr("system error"));}),_kh=function(_ki,_kj){switch(E(_ki)){case 0:return new F(function(){return _1d(_jY,_kj);});break;case 1:return new F(function(){return _1d(_jZ,_kj);});break;case 2:return new F(function(){return _1d(_k9,_kj);});break;case 3:return new F(function(){return _1d(_ka,_kj);});break;case 4:return new F(function(){return _1d(_kb,_kj);});break;case 5:return new F(function(){return _1d(_kc,_kj);});break;case 6:return new F(function(){return _1d(_kd,_kj);});break;case 7:return new F(function(){return _1d(_ke,_kj);});break;case 8:return new F(function(){return _1d(_kf,_kj);});break;case 9:return new F(function(){return _1d(_kg,_kj);});break;case 10:return new F(function(){return _1d(_k0,_kj);});break;case 11:return new F(function(){return _1d(_k1,_kj);});break;case 12:return new F(function(){return _1d(_k2,_kj);});break;case 13:return new F(function(){return _1d(_k3,_kj);});break;case 14:return new F(function(){return _1d(_k4,_kj);});break;case 15:return new F(function(){return _1d(_k5,_kj);});break;case 16:return new F(function(){return _1d(_k6,_kj);});break;case 17:return new F(function(){return _1d(_k7,_kj);});break;default:return new F(function(){return _1d(_k8,_kj);});}},_kk=[0,125],_kl=new T(function(){return B(unCStr("{handle: "));}),_km=function(_kn,_ko,_kp,_kq,_kr,_ks){var _kt=new T(function(){var _ku=new T(function(){return B(_kh(_ko,new T(function(){var _kv=E(_kq);return _kv[0]==0?E(_ks):B(_1d(_jX,new T(function(){return B(_1d(_kv,[1,_jW,_ks]));})));})));}),_kw=E(_kp);return _kw[0]==0?E(_ku):B(_1d(_kw,new T(function(){return B(_1d(_jV,_ku));})));}),_kx=E(_kr);if(!_kx[0]){var _ky=E(_kn);if(!_ky[0]){return E(_kt);}else{var _kz=E(_ky[1]);return _kz[0]==0?B(_1d(_kl,new T(function(){return B(_1d(_kz[1],[1,_kk,new T(function(){return B(_1d(_jV,_kt));})]));}))):B(_1d(_kl,new T(function(){return B(_1d(_kz[1],[1,_kk,new T(function(){return B(_1d(_jV,_kt));})]));})));}}else{return new F(function(){return _1d(_kx[1],new T(function(){return B(_1d(_jV,_kt));}));});}},_kA=function(_kB){var _kC=E(_kB);return new F(function(){return _km(_kC[1],_kC[2],_kC[3],_kC[4],_kC[6],_0);});},_kD=function(_kE,_kF){var _kG=E(_kE);return new F(function(){return _km(_kG[1],_kG[2],_kG[3],_kG[4],_kG[6],_kF);});},_kH=function(_kI,_kJ){return new F(function(){return _1n(_kD,_kI,_kJ);});},_kK=function(_kL,_kM,_kN){var _kO=E(_kM);return new F(function(){return _km(_kO[1],_kO[2],_kO[3],_kO[4],_kO[6],_kN);});},_kP=[0,_kK,_kA,_kH],_kQ=new T(function(){return [0,_jQ,_kP,_kR,_jS];}),_kR=function(_kS){return [0,_kQ,_kS];},_kT=7,_kU=function(_kV){return [0,_7B,_kT,_0,_kV,_7B,_7B];},_kW=function(_kX,_){return new F(function(){return die(new T(function(){return B(_kR(new T(function(){return B(_kU(_kX));})));}));});},_kY=function(_kZ,_){return new F(function(){return _kW(_kZ,_);});},_l0=[0,114],_l1=[1,_l0,_0],_l2=new T(function(){return B(_2N(0,6,_0));}),_l3=new T(function(){return B(unCStr("cx"));}),_l4=new T(function(){return B(unCStr("cy"));}),_l5=new T(function(){return B(unCStr("circle"));}),_l6=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_l7=new T(function(){return B(unCStr("board"));}),_l8=function(_l9,_la,_){while(1){var _lb=(function(_lc,_ld,_){var _le=E(_ld);if(!_le[0]){return _2u;}else{var _lf=_le[2],_lg=E(_le[1]),_lh=E(_lg[2])[1];if(_lh>0){var _li=function(_lj,_lk,_){var _ll=jsFind(toJSStr(E(_l7))),_lm=_ll,_ln=E(_lm);if(!_ln[0]){var _lo=B(_kY(_jG,_)),_lp=_lo;return new F(function(){return A(_lk,[_]);});}else{var _lq=jsCreateElemNS(toJSStr(E(_l6)),toJSStr(E(_l5))),_lr=_lq,_ls=[0,_lr],_lt=B(A(_34,[_3a,_ls,_l1,_l2,_])),_lu=_lt,_lv=[0,[0,_lc],_lj],_lw=new T(function(){var _lx=B(_3v(_lv));return [0,_lx[1],_lx[2]];}),_ly=B(A(_34,[_3a,_ls,_l3,new T(function(){return B(_2N(0,E(E(_lw)[1])[1],_0));}),_])),_lz=_ly,_lA=B(A(_34,[_3a,_ls,_l4,new T(function(){return B(_2N(0,E(E(_lw)[2])[1],_0));}),_])),_lB=_lA,_lC=B(A(_3n,[_ls,_y,_lv,_lg[1],_])),_lD=_lC,_lE=jsAppendChild(_lr,E(_ln[1])[1]);return new F(function(){return A(_lk,[_]);});}},_lF=function(_lG,_lH,_){var _lI=E(_lG);if(!_lI[0]){return _2u;}else{var _lJ=_lI[1];if(_lH>1){return new F(function(){return _li(_lJ,function(_){return new F(function(){return _lF(_lI[2],_lH-1|0,_);});},_);});}else{return new F(function(){return _li(_lJ,_jH,_);});}}},_lK=B(_lF(_4v,_lh,_)),_lL=_lK,_lM=E(_lc);if(_lM==2147483647){return _2u;}else{_l9=_lM+1|0;_la=_lf;return null;}}else{var _lN=E(_lc);if(_lN==2147483647){return _2u;}else{_l9=_lN+1|0;_la=_lf;return null;}}}})(_l9,_la,_);if(_lb!=null){return _lb;}}},_lO=function(_){var _lP=B(_l8(0,_2j,_)),_lQ=_lP;return new F(function(){return _iW(_2k,_);});},_lR=function(_){return new F(function(){return _lO(_);});};
var hasteMain = function() {B(A(_lR, [0]));};window.onload = hasteMain;