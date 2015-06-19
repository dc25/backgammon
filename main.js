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

var _0=[0],_1=function(_2,_3){while(1){var _4=E(_2);if(!_4[0]){return E(_3);}else{_2=_4[2];var _5=[1,_4[1],_3];_3=_5;continue;}}},_6=2,_7=[0,0],_8=[0,_6,_7],_9=[0,_6,_7],_a=[0,_6,_7],_b=[0,_6,_7],_c=[0,_6,_7],_d=[1,_c,_0],_e=[0,_6,_7],_f=[1,_e,_d],_g=[0,_6,_7],_h=[1,_g,_f],_i=[0,_6,_7],_j=[1,_i,_h],_k=[0,_6,_7],_l=[1,_k,_j],_m=1,_n=[0,5],_o=[0,_m,_n],_p=[1,_o,_l],_q=[0,_6,_7],_r=[1,_q,_p],_s=[0,3],_t=[0,_m,_s],_u=[1,_t,_r],_v=[0,_6,_7],_w=[1,_v,_u],_x=[0,_6,_7],_y=[1,_x,_w],_z=[0,_6,_7],_A=[1,_z,_y],_B=[0,_6,_7],_C=[1,_B,_A],_D=[0,_m,_n],_E=[1,_D,_C],_F=[0,_6,_7],_G=[1,_F,_E],_H=[0,_6,_7],_I=[1,_H,_G],_J=[0,_6,_7],_K=[1,_J,_I],_L=[0,_6,_7],_M=[1,_L,_K],_N=[1,_b,_M],_O=[1,_a,_N],_P=[1,_9,_O],_Q=[1,_8,_P],_R=[0,_6,_7],_S=[1,_R,_Q],_T=[0,_6,_7],_U=[1,_T,_S],_V=[0,2],_W=[0,_m,_V],_X=[1,_W,_U],_Y=new T(function(){return B(_1(_X,_0));}),_Z=0,_10=function(_11,_12){var _13=E(_11);if(!_13[0]){return [0];}else{var _14=E(_12);return _14[0]==0?[0]:[1,new T(function(){var _15=E(_14[1]);if(E(_15[1])==1){var _16=E(_15);}else{var _17=E(_13[1]),_16=E(_17[1])==1?[0,_Z,_17[2]]:E(_17);}var _18=_16;return _18;}),new T(function(){return B(_10(_13[2],_14[2]));})];}},_19=new T(function(){return B(_10(_Y,_X));}),_1a=[0,_19,_m,_m],_1b=new T(function(){return B(unCStr("Prelude.(!!): negative index\n"));}),_1c=new T(function(){return B(err(_1b));}),_1d=new T(function(){return B(unCStr("Prelude.(!!): index too large\n"));}),_1e=new T(function(){return B(err(_1d));}),_1f=function(_1g,_1h){while(1){var _1i=E(_1g);if(!_1i[0]){return E(_1e);}else{var _1j=E(_1h);if(!_1j){return E(_1i[1]);}else{_1g=_1i[2];_1h=_1j-1|0;continue;}}}},_1k=0,_1l=new T(function(){return B(unCStr("None"));}),_1m=new T(function(){return B(unCStr("White"));}),_1n=new T(function(){return B(unCStr("Black"));}),_1o=function(_1p,_1q,_1r,_1s){return new F(function(){return A(_1p,[new T(function(){return function(_){var _1t=jsSetAttr(E(_1q)[1],toJSStr(E(_1r)),toJSStr(E(_1s)));return _1k;};})]);});},_1u=function(_1v,_1w){var _1x=E(_1v);return _1x[0]==0?E(_1w):[1,_1x[1],new T(function(){return B(_1u(_1x[2],_1w));})];},_1y=function(_1z,_1A){var _1B=jsShowI(_1z),_1C=_1B;return new F(function(){return _1u(fromJSStr(_1C),_1A);});},_1D=[0,41],_1E=[0,40],_1F=function(_1G,_1H,_1I){return _1H>=0?B(_1y(_1H,_1I)):_1G<=6?B(_1y(_1H,_1I)):[1,_1E,new T(function(){var _1J=jsShowI(_1H),_1K=_1J;return B(_1u(fromJSStr(_1K),[1,_1D,_1I]));})];},_1L=function(_1M){return E(_1M);},_1N=new T(function(){return B(unCStr("class"));}),_1O=new T(function(){return B(unCStr("draggable "));}),_1P=function(_1Q,_1R,_1S,_1T,_1U){return new F(function(){return _1o(_1L,_1Q,_1N,new T(function(){var _1V=new T(function(){var _1W=new T(function(){return B(unAppCStr(" pi",new T(function(){return B(_1u(B(_1F(0,E(_1S)[1],_0)),new T(function(){return B(unAppCStr(" ci",new T(function(){return B(_1F(0,E(_1T)[1],_0));})));})));})));});switch(E(_1U)){case 0:var _1X=B(_1u(_1n,_1W));break;case 1:var _1X=B(_1u(_1m,_1W));break;default:var _1X=B(_1u(_1l,_1W));}return _1X;});switch(E(_1R)){case 0:switch(E(_1U)){case 0:var _1Y=B(_1u(_1O,_1V));break;case 1:var _1Y=E(_1V);break;default:var _1Y=E(_1V);}var _1Z=_1Y;break;case 1:var _1Z=E(_1U)==1?B(_1u(_1O,_1V)):E(_1V);break;default:var _1Z=E(_1U)==2?B(_1u(_1O,_1V)):E(_1V);}return _1Z;}));});},_20=function(_21,_22){return [0,new T(function(){var _23=E(_21)[1];if(_23>=12){var _24=_23-12|0;if(_24>=6){var _25=[0,10+(5+(imul(_24,15)|0)|0)|0];}else{var _25=[0,10+(imul(_24,15)|0)|0];}var _26=_25,_27=_26;}else{var _28=11-_23|0;if(_28>=6){var _29=[0,10+(5+(imul(_28,15)|0)|0)|0];}else{var _29=[0,10+(imul(_28,15)|0)|0];}var _2a=_29,_27=_2a;}var _2b=_27;return _2b;}),new T(function(){if(E(_21)[1]>=12){var _2c=[0,7+(imul(imul(E(_22)[1],2)|0,6)|0)|0];}else{var _2c=[0,203+(imul(imul(imul(-1,E(_22)[1])|0,2)|0,6)|0)|0];}var _2d=_2c;return _2d;})];},_2e=function(_2f,_2g,_2h,_2i,_2j,_){var _2k=jsElemsByClassName(toJSStr(B(unAppCStr(" pi",new T(function(){return B(_1u(B(_1F(0,E(_2f)[1],_0)),new T(function(){return B(unAppCStr(" ci",new T(function(){return B(_1F(0,E(_2g)[1],_0));})));})));}))))),_2l=_2k,_2m=B(_1f(_2l,0)),_2n=B(_20(_2h,_2i)),_2o=animateCircle_ffi(_2m[1],E(_2n[1])[1],E(_2n[2])[1],300);return new F(function(){return A(_1P,[_2m,_2j,_2h,_2i,_2j,_]);});},_2p=function(_2q,_2r){while(1){var _2s=E(_2q);if(!_2s){return E(_2r);}else{var _2t=E(_2r);if(!_2t[0]){return [0];}else{_2q=_2s-1|0;_2r=_2t[2];continue;}}}},_2u=function(_2v,_2w){if(_2v<=_2w){var _2x=function(_2y){return [1,[0,_2y],new T(function(){if(_2y!=_2w){var _2z=B(_2x(_2y+1|0));}else{var _2z=[0];}return _2z;})];};return new F(function(){return _2x(_2v);});}else{return [0];}},_2A=function(_2B,_2C){var _2D=function(_2E,_2F){while(1){var _2G=(function(_2H,_2I){var _2J=E(_2I);if(!_2J[0]){return [0];}else{var _2K=_2J[2];if(!B(A(_2B,[_2J[1]]))){var _2L=_2H+1|0;_2F=_2K;_2E=_2L;return null;}else{return [1,[0,_2H],new T(function(){return B(_2D(_2H+1|0,_2K));})];}}})(_2E,_2F);if(_2G!=null){return _2G;}}};return new F(function(){return _2D(0,_2C);});},_2M=function(_2N,_2O,_2P,_2Q){var _2R=E(_2P);if(!_2R[0]){return E(_2O);}else{var _2S=E(_2Q);if(!_2S[0]){return E(_2O);}else{return new F(function(){return A(_2N,[_2R[1],_2S[1],new T(function(){return B(_2M(_2N,_2O,_2R[2],_2S[2]));})]);});}}},_2T=function(_2U){return new F(function(){return fromJSStr(E(_2U)[1]);});},_2V=new T(function(){return B(unCStr("Control.Exception.Base"));}),_2W=new T(function(){return B(unCStr("base"));}),_2X=new T(function(){return B(unCStr("PatternMatchFail"));}),_2Y=new T(function(){var _2Z=hs_wordToWord64(18445595),_30=_2Z,_31=hs_wordToWord64(52003073),_32=_31;return [0,_30,_32,[0,_30,_32,_2W,_2V,_2X],_0];}),_33=function(_34){return E(_2Y);},_35=function(_36){return E(E(_36)[1]);},_37=new T(function(){return B(unCStr("Maybe.fromJust: Nothing"));}),_38=new T(function(){return B(err(_37));}),_39=function(_3a,_3b,_3c){var _3d=new T(function(){var _3e=B(A(_3a,[_3c])),_3f=B(A(_3b,[new T(function(){var _3g=E(_3d);return _3g[0]==0?E(_38):E(_3g[1]);})])),_3h=hs_eqWord64(_3e[1],_3f[1]),_3i=_3h;if(!E(_3i)){var _3j=[0];}else{var _3k=hs_eqWord64(_3e[2],_3f[2]),_3l=_3k,_3j=E(_3l)==0?[0]:[1,_3c];}var _3m=_3j,_3n=_3m;return _3n;});return E(_3d);},_3o=function(_3p){var _3q=E(_3p);return new F(function(){return _39(B(_35(_3q[1])),_33,_3q[2]);});},_3r=function(_3s){return E(E(_3s)[1]);},_3t=function(_3u,_3v){return new F(function(){return _1u(E(_3u)[1],_3v);});},_3w=[0,44],_3x=[0,93],_3y=[0,91],_3z=function(_3A,_3B,_3C){var _3D=E(_3B);return _3D[0]==0?B(unAppCStr("[]",_3C)):[1,_3y,new T(function(){return B(A(_3A,[_3D[1],new T(function(){var _3E=function(_3F){var _3G=E(_3F);return _3G[0]==0?E([1,_3x,_3C]):[1,_3w,new T(function(){return B(A(_3A,[_3G[1],new T(function(){return B(_3E(_3G[2]));})]));})];};return B(_3E(_3D[2]));})]));})];},_3H=function(_3I,_3J){return new F(function(){return _3z(_3t,_3I,_3J);});},_3K=function(_3L,_3M,_3N){return new F(function(){return _1u(E(_3M)[1],_3N);});},_3O=[0,_3K,_3r,_3H],_3P=new T(function(){return [0,_33,_3O,_3Q,_3o];}),_3Q=function(_3R){return [0,_3P,_3R];},_3S=new T(function(){return B(unCStr("Non-exhaustive patterns in"));}),_3T=function(_3U,_3V){return new F(function(){return die(new T(function(){return B(A(_3V,[_3U]));}));});},_3W=function(_3X,_3Y){var _3Z=E(_3Y);if(!_3Z[0]){return [0,_0,_0];}else{var _40=_3Z[1];if(!B(A(_3X,[_40]))){return [0,_0,_3Z];}else{var _41=new T(function(){var _42=B(_3W(_3X,_3Z[2]));return [0,_42[1],_42[2]];});return [0,[1,_40,new T(function(){return E(E(_41)[1]);})],new T(function(){return E(E(_41)[2]);})];}}},_43=[0,32],_44=[0,10],_45=[1,_44,_0],_46=function(_47){return E(E(_47)[1])==124?false:true;},_48=function(_49,_4a){var _4b=B(_3W(_46,B(unCStr(_49)))),_4c=_4b[1],_4d=function(_4e,_4f){return new F(function(){return _1u(_4e,new T(function(){return B(unAppCStr(": ",new T(function(){return B(_1u(_4a,new T(function(){return B(_1u(_4f,_45));})));})));}));});},_4g=E(_4b[2]);if(!_4g[0]){return new F(function(){return _4d(_4c,_0);});}else{return E(E(_4g[1])[1])==124?B(_4d(_4c,[1,_43,_4g[2]])):B(_4d(_4c,_0));}},_4h=function(_4i){return new F(function(){return _3T([0,new T(function(){return B(_48(_4i,_3S));})],_3Q);});},_4j=new T(function(){return B(_4h("Text/ParserCombinators/ReadP.hs:(134,3)-(157,60)|function mplus"));}),_4k=function(_4l,_4m){while(1){var _4n=(function(_4o,_4p){var _4q=E(_4o);switch(_4q[0]){case 0:var _4r=E(_4p);if(!_4r[0]){return [0];}else{_4l=B(A(_4q[1],[_4r[1]]));_4m=_4r[2];return null;}break;case 1:var _4s=B(A(_4q[1],[_4p])),_4t=_4p;_4l=_4s;_4m=_4t;return null;case 2:return [0];case 3:return [1,[0,_4q[1],_4p],new T(function(){return B(_4k(_4q[2],_4p));})];default:return E(_4q[1]);}})(_4l,_4m);if(_4n!=null){return _4n;}}},_4u=function(_4v,_4w){var _4x=new T(function(){var _4y=E(_4w);if(_4y[0]==3){var _4z=[3,_4y[1],new T(function(){return B(_4u(_4v,_4y[2]));})];}else{var _4A=E(_4v);if(_4A[0]==2){var _4B=E(_4y);}else{var _4C=E(_4y);if(_4C[0]==2){var _4D=E(_4A);}else{var _4E=new T(function(){var _4F=E(_4C);if(_4F[0]==4){var _4G=[1,function(_4H){return [4,new T(function(){return B(_1u(B(_4k(_4A,_4H)),_4F[1]));})];}];}else{var _4I=E(_4A);if(_4I[0]==1){var _4J=_4I[1],_4K=E(_4F);if(!_4K[0]){var _4L=[1,function(_4M){return new F(function(){return _4u(B(A(_4J,[_4M])),_4K);});}];}else{var _4L=[1,function(_4N){return new F(function(){return _4u(B(A(_4J,[_4N])),new T(function(){return B(A(_4K[1],[_4N]));}));});}];}var _4O=_4L;}else{var _4P=E(_4F);if(!_4P[0]){var _4Q=E(_4j);}else{var _4Q=[1,function(_4R){return new F(function(){return _4u(_4I,new T(function(){return B(A(_4P[1],[_4R]));}));});}];}var _4O=_4Q;}var _4G=_4O;}return _4G;}),_4S=E(_4A);switch(_4S[0]){case 1:var _4T=E(_4C);if(_4T[0]==4){var _4U=[1,function(_4V){return [4,new T(function(){return B(_1u(B(_4k(B(A(_4S[1],[_4V])),_4V)),_4T[1]));})];}];}else{var _4U=E(_4E);}var _4W=_4U;break;case 4:var _4X=_4S[1],_4Y=E(_4C);switch(_4Y[0]){case 0:var _4Z=[1,function(_50){return [4,new T(function(){return B(_1u(_4X,new T(function(){return B(_4k(_4Y,_50));})));})];}];break;case 1:var _4Z=[1,function(_51){return [4,new T(function(){return B(_1u(_4X,new T(function(){return B(_4k(B(A(_4Y[1],[_51])),_51));})));})];}];break;default:var _4Z=[4,new T(function(){return B(_1u(_4X,_4Y[1]));})];}var _4W=_4Z;break;default:var _4W=E(_4E);}var _4D=_4W;}var _4B=_4D;}var _4z=_4B;}return _4z;}),_52=E(_4v);switch(_52[0]){case 0:var _53=E(_4w);return _53[0]==0?[0,function(_54){return new F(function(){return _4u(B(A(_52[1],[_54])),new T(function(){return B(A(_53[1],[_54]));}));});}]:E(_4x);case 3:return [3,_52[1],new T(function(){return B(_4u(_52[2],_4w));})];default:return E(_4x);}},_55=function(_56,_57){return E(_56)[1]!=E(_57)[1];},_58=function(_59,_5a){return E(_59)[1]==E(_5a)[1];},_5b=[0,_58,_55],_5c=function(_5d){return E(E(_5d)[1]);},_5e=function(_5f,_5g,_5h){while(1){var _5i=E(_5g);if(!_5i[0]){return E(_5h)[0]==0?true:false;}else{var _5j=E(_5h);if(!_5j[0]){return false;}else{if(!B(A(_5c,[_5f,_5i[1],_5j[1]]))){return false;}else{_5g=_5i[2];_5h=_5j[2];continue;}}}}},_5k=function(_5l,_5m,_5n){return !B(_5e(_5l,_5m,_5n))?true:false;},_5o=function(_5p){return [0,function(_5q,_5r){return new F(function(){return _5e(_5p,_5q,_5r);});},function(_5q,_5r){return new F(function(){return _5k(_5p,_5q,_5r);});}];},_5s=new T(function(){return B(_5o(_5b));}),_5t=function(_5u,_5v){var _5w=E(_5u);switch(_5w[0]){case 0:return [0,function(_5x){return new F(function(){return _5t(B(A(_5w[1],[_5x])),_5v);});}];case 1:return [1,function(_5y){return new F(function(){return _5t(B(A(_5w[1],[_5y])),_5v);});}];case 2:return [2];case 3:return new F(function(){return _4u(B(A(_5v,[_5w[1]])),new T(function(){return B(_5t(_5w[2],_5v));}));});break;default:var _5z=function(_5A){var _5B=E(_5A);if(!_5B[0]){return [0];}else{var _5C=E(_5B[1]);return new F(function(){return _1u(B(_4k(B(A(_5v,[_5C[1]])),_5C[2])),new T(function(){return B(_5z(_5B[2]));}));});}},_5D=B(_5z(_5w[1]));return _5D[0]==0?[2]:[4,_5D];}},_5E=[2],_5F=function(_5G){return [3,_5G,_5E];},_5H=function(_5I,_5J){var _5K=E(_5I);if(!_5K){return new F(function(){return A(_5J,[_1k]);});}else{return [0,function(_5L){return E(new T(function(){return B(_5H(_5K-1|0,_5J));}));}];}},_5M=function(_5N,_5O,_5P){return [1,function(_5Q){return new F(function(){return A(function(_5R,_5S,_5T){while(1){var _5U=(function(_5V,_5W,_5X){var _5Y=E(_5V);switch(_5Y[0]){case 0:var _5Z=E(_5W);if(!_5Z[0]){return E(_5O);}else{_5R=B(A(_5Y[1],[_5Z[1]]));_5S=_5Z[2];var _60=_5X+1|0;_5T=_60;return null;}break;case 1:var _61=B(A(_5Y[1],[_5W])),_62=_5W,_60=_5X;_5R=_61;_5S=_62;_5T=_60;return null;case 2:return E(_5O);case 3:return function(_63){return new F(function(){return _5H(_5X,function(_64){return E(new T(function(){return B(_5t(_5Y,_63));}));});});};default:return function(_65){return new F(function(){return _5t(_5Y,_65);});};}})(_5R,_5S,_5T);if(_5U!=null){return _5U;}}},[new T(function(){return B(A(_5N,[_5F]));}),_5Q,0,_5P]);});}];},_66=[6],_67=new T(function(){return B(unCStr("valDig: Bad base"));}),_68=new T(function(){return B(err(_67));}),_69=function(_6a,_6b){var _6c=function(_6d,_6e){var _6f=E(_6d);if(!_6f[0]){return function(_6g){return new F(function(){return A(_6g,[new T(function(){return B(A(_6e,[_0]));})]);});};}else{var _6h=E(_6f[1])[1],_6i=function(_6j){return function(_6k){return [0,function(_6l){return E(new T(function(){return B(A(new T(function(){return B(_6c(_6f[2],function(_6m){return new F(function(){return A(_6e,[[1,_6j,_6m]]);});}));}),[_6k]));}));}];};};switch(E(E(_6a)[1])){case 8:if(48>_6h){return function(_6n){return new F(function(){return A(_6n,[new T(function(){return B(A(_6e,[_0]));})]);});};}else{if(_6h>55){return function(_6o){return new F(function(){return A(_6o,[new T(function(){return B(A(_6e,[_0]));})]);});};}else{return new F(function(){return _6i([0,_6h-48|0]);});}}break;case 10:if(48>_6h){return function(_6p){return new F(function(){return A(_6p,[new T(function(){return B(A(_6e,[_0]));})]);});};}else{if(_6h>57){return function(_6q){return new F(function(){return A(_6q,[new T(function(){return B(A(_6e,[_0]));})]);});};}else{return new F(function(){return _6i([0,_6h-48|0]);});}}break;case 16:var _6r=new T(function(){if(97>_6h){if(65>_6h){var _6s=[0];}else{if(_6h>70){var _6t=[0];}else{var _6t=[1,[0,(_6h-65|0)+10|0]];}var _6s=_6t;}var _6u=_6s;}else{if(_6h>102){if(65>_6h){var _6v=[0];}else{if(_6h>70){var _6w=[0];}else{var _6w=[1,[0,(_6h-65|0)+10|0]];}var _6v=_6w;}var _6x=_6v;}else{var _6x=[1,[0,(_6h-97|0)+10|0]];}var _6u=_6x;}return _6u;});if(48>_6h){var _6y=E(_6r);if(!_6y[0]){return function(_6z){return new F(function(){return A(_6z,[new T(function(){return B(A(_6e,[_0]));})]);});};}else{return new F(function(){return _6i(_6y[1]);});}}else{if(_6h>57){var _6A=E(_6r);if(!_6A[0]){return function(_6B){return new F(function(){return A(_6B,[new T(function(){return B(A(_6e,[_0]));})]);});};}else{return new F(function(){return _6i(_6A[1]);});}}else{return new F(function(){return _6i([0,_6h-48|0]);});}}break;default:return E(_68);}}};return [1,function(_6C){return new F(function(){return A(_6c,[_6C,_1L,function(_6D){var _6E=E(_6D);return _6E[0]==0?[2]:B(A(_6b,[_6E]));}]);});}];},_6F=[0,10],_6G=[0,1],_6H=[0,2147483647],_6I=function(_6J,_6K){while(1){var _6L=E(_6J);if(!_6L[0]){var _6M=_6L[1],_6N=E(_6K);if(!_6N[0]){var _6O=_6N[1],_6P=addC(_6M,_6O);if(!E(_6P[2])){return [0,_6P[1]];}else{_6J=[1,I_fromInt(_6M)];_6K=[1,I_fromInt(_6O)];continue;}}else{_6J=[1,I_fromInt(_6M)];_6K=_6N;continue;}}else{var _6Q=E(_6K);if(!_6Q[0]){_6J=_6L;_6K=[1,I_fromInt(_6Q[1])];continue;}else{return [1,I_add(_6L[1],_6Q[1])];}}}},_6R=new T(function(){return B(_6I(_6H,_6G));}),_6S=function(_6T){var _6U=E(_6T);if(!_6U[0]){var _6V=E(_6U[1]);return _6V==(-2147483648)?E(_6R):[0, -_6V];}else{return [1,I_negate(_6U[1])];}},_6W=[0,10],_6X=[0,0],_6Y=function(_6Z){return [0,_6Z];},_70=function(_71,_72){while(1){var _73=E(_71);if(!_73[0]){var _74=_73[1],_75=E(_72);if(!_75[0]){var _76=_75[1];if(!(imul(_74,_76)|0)){return [0,imul(_74,_76)|0];}else{_71=[1,I_fromInt(_74)];_72=[1,I_fromInt(_76)];continue;}}else{_71=[1,I_fromInt(_74)];_72=_75;continue;}}else{var _77=E(_72);if(!_77[0]){_71=_73;_72=[1,I_fromInt(_77[1])];continue;}else{return [1,I_mul(_73[1],_77[1])];}}}},_78=function(_79,_7a,_7b){while(1){var _7c=E(_7b);if(!_7c[0]){return E(_7a);}else{var _7d=B(_6I(B(_70(_7a,_79)),B(_6Y(E(_7c[1])[1]))));_7b=_7c[2];_7a=_7d;continue;}}},_7e=function(_7f){var _7g=new T(function(){return B(_4u(B(_4u([0,function(_7h){if(E(E(_7h)[1])==45){return new F(function(){return _69(_6F,function(_7i){return new F(function(){return A(_7f,[[1,new T(function(){return B(_6S(B(_78(_6W,_6X,_7i))));})]]);});});});}else{return [2];}}],[0,function(_7j){if(E(E(_7j)[1])==43){return new F(function(){return _69(_6F,function(_7k){return new F(function(){return A(_7f,[[1,new T(function(){return B(_78(_6W,_6X,_7k));})]]);});});});}else{return [2];}}])),new T(function(){return B(_69(_6F,function(_7l){return new F(function(){return A(_7f,[[1,new T(function(){return B(_78(_6W,_6X,_7l));})]]);});}));})));});return new F(function(){return _4u([0,function(_7m){return E(E(_7m)[1])==101?E(_7g):[2];}],[0,function(_7n){return E(E(_7n)[1])==69?E(_7g):[2];}]);});},_7o=[0],_7p=function(_7q){return new F(function(){return A(_7q,[_7o]);});},_7r=function(_7s){return new F(function(){return A(_7s,[_7o]);});},_7t=function(_7u){return [0,function(_7v){return E(E(_7v)[1])==46?E(new T(function(){return B(_69(_6F,function(_7w){return new F(function(){return A(_7u,[[1,_7w]]);});}));})):[2];}];},_7x=function(_7y){return new F(function(){return _69(_6F,function(_7z){return new F(function(){return _5M(_7t,_7p,function(_7A){return new F(function(){return _5M(_7e,_7r,function(_7B){return new F(function(){return A(_7y,[[5,[1,_7z,_7A,_7B]]]);});});});});});});});},_7C=function(_7D,_7E,_7F){while(1){var _7G=E(_7F);if(!_7G[0]){return false;}else{if(!B(A(_5c,[_7D,_7E,_7G[1]]))){_7F=_7G[2];continue;}else{return true;}}}},_7H=new T(function(){return B(unCStr("!@#$%&*+./<=>?\\^|:-~"));}),_7I=function(_7J){return new F(function(){return _7C(_5b,_7J,_7H);});},_7K=[0,8],_7L=[0,16],_7M=function(_7N){return [0,function(_7O){return E(E(_7O)[1])==48?E([0,function(_7P){switch(E(E(_7P)[1])){case 79:return E(new T(function(){return B(_69(_7K,function(_7Q){return new F(function(){return A(_7N,[[5,[0,_7K,_7Q]]]);});}));}));case 88:return E(new T(function(){return B(_69(_7L,function(_7R){return new F(function(){return A(_7N,[[5,[0,_7L,_7R]]]);});}));}));case 111:return E(new T(function(){return B(_69(_7K,function(_7S){return new F(function(){return A(_7N,[[5,[0,_7K,_7S]]]);});}));}));case 120:return E(new T(function(){return B(_69(_7L,function(_7T){return new F(function(){return A(_7N,[[5,[0,_7L,_7T]]]);});}));}));default:return [2];}}]):[2];}];},_7U=false,_7V=true,_7W=function(_7X){return [0,function(_7Y){switch(E(E(_7Y)[1])){case 79:return E(new T(function(){return B(A(_7X,[_7K]));}));case 88:return E(new T(function(){return B(A(_7X,[_7L]));}));case 111:return E(new T(function(){return B(A(_7X,[_7K]));}));case 120:return E(new T(function(){return B(A(_7X,[_7L]));}));default:return [2];}}];},_7Z=function(_80){return new F(function(){return A(_80,[_6F]);});},_81=function(_82){return new F(function(){return err(B(unAppCStr("Prelude.chr: bad argument: ",new T(function(){return B(_1F(9,_82,_0));}))));});},_83=function(_84){var _85=E(_84);return _85[0]==0?E(_85[1]):I_toInt(_85[1]);},_86=function(_87,_88){var _89=E(_87);if(!_89[0]){var _8a=_89[1],_8b=E(_88);return _8b[0]==0?_8a<=_8b[1]:I_compareInt(_8b[1],_8a)>=0;}else{var _8c=_89[1],_8d=E(_88);return _8d[0]==0?I_compareInt(_8c,_8d[1])<=0:I_compare(_8c,_8d[1])<=0;}},_8e=function(_8f){return [2];},_8g=function(_8h){var _8i=E(_8h);if(!_8i[0]){return E(_8e);}else{var _8j=_8i[1],_8k=E(_8i[2]);return _8k[0]==0?E(_8j):function(_8l){return new F(function(){return _4u(B(A(_8j,[_8l])),new T(function(){return B(A(new T(function(){return B(_8g(_8k));}),[_8l]));}));});};}},_8m=new T(function(){return B(unCStr("NUL"));}),_8n=function(_8o){return [2];},_8p=function(_8q){return new F(function(){return _8n(_8q);});},_8r=function(_8s,_8t){var _8u=function(_8v,_8w){var _8x=E(_8v);if(!_8x[0]){return function(_8y){return new F(function(){return A(_8y,[_8s]);});};}else{var _8z=E(_8w);return _8z[0]==0?E(_8n):E(_8x[1])[1]!=E(_8z[1])[1]?E(_8p):function(_8A){return [0,function(_8B){return E(new T(function(){return B(A(new T(function(){return B(_8u(_8x[2],_8z[2]));}),[_8A]));}));}];};}};return [1,function(_8C){return new F(function(){return A(_8u,[_8s,_8C,_8t]);});}];},_8D=[0,0],_8E=function(_8F){return new F(function(){return _8r(_8m,function(_8G){return E(new T(function(){return B(A(_8F,[_8D]));}));});});},_8H=new T(function(){return B(unCStr("STX"));}),_8I=[0,2],_8J=function(_8K){return new F(function(){return _8r(_8H,function(_8L){return E(new T(function(){return B(A(_8K,[_8I]));}));});});},_8M=new T(function(){return B(unCStr("ETX"));}),_8N=[0,3],_8O=function(_8P){return new F(function(){return _8r(_8M,function(_8Q){return E(new T(function(){return B(A(_8P,[_8N]));}));});});},_8R=new T(function(){return B(unCStr("EOT"));}),_8S=[0,4],_8T=function(_8U){return new F(function(){return _8r(_8R,function(_8V){return E(new T(function(){return B(A(_8U,[_8S]));}));});});},_8W=new T(function(){return B(unCStr("ENQ"));}),_8X=[0,5],_8Y=function(_8Z){return new F(function(){return _8r(_8W,function(_90){return E(new T(function(){return B(A(_8Z,[_8X]));}));});});},_91=new T(function(){return B(unCStr("ACK"));}),_92=[0,6],_93=function(_94){return new F(function(){return _8r(_91,function(_95){return E(new T(function(){return B(A(_94,[_92]));}));});});},_96=new T(function(){return B(unCStr("BEL"));}),_97=[0,7],_98=function(_99){return new F(function(){return _8r(_96,function(_9a){return E(new T(function(){return B(A(_99,[_97]));}));});});},_9b=new T(function(){return B(unCStr("BS"));}),_9c=[0,8],_9d=function(_9e){return new F(function(){return _8r(_9b,function(_9f){return E(new T(function(){return B(A(_9e,[_9c]));}));});});},_9g=new T(function(){return B(unCStr("HT"));}),_9h=[0,9],_9i=function(_9j){return new F(function(){return _8r(_9g,function(_9k){return E(new T(function(){return B(A(_9j,[_9h]));}));});});},_9l=new T(function(){return B(unCStr("LF"));}),_9m=[0,10],_9n=function(_9o){return new F(function(){return _8r(_9l,function(_9p){return E(new T(function(){return B(A(_9o,[_9m]));}));});});},_9q=new T(function(){return B(unCStr("VT"));}),_9r=[0,11],_9s=function(_9t){return new F(function(){return _8r(_9q,function(_9u){return E(new T(function(){return B(A(_9t,[_9r]));}));});});},_9v=new T(function(){return B(unCStr("FF"));}),_9w=[0,12],_9x=function(_9y){return new F(function(){return _8r(_9v,function(_9z){return E(new T(function(){return B(A(_9y,[_9w]));}));});});},_9A=new T(function(){return B(unCStr("CR"));}),_9B=[0,13],_9C=function(_9D){return new F(function(){return _8r(_9A,function(_9E){return E(new T(function(){return B(A(_9D,[_9B]));}));});});},_9F=new T(function(){return B(unCStr("SI"));}),_9G=[0,15],_9H=function(_9I){return new F(function(){return _8r(_9F,function(_9J){return E(new T(function(){return B(A(_9I,[_9G]));}));});});},_9K=new T(function(){return B(unCStr("DLE"));}),_9L=[0,16],_9M=function(_9N){return new F(function(){return _8r(_9K,function(_9O){return E(new T(function(){return B(A(_9N,[_9L]));}));});});},_9P=new T(function(){return B(unCStr("DC1"));}),_9Q=[0,17],_9R=function(_9S){return new F(function(){return _8r(_9P,function(_9T){return E(new T(function(){return B(A(_9S,[_9Q]));}));});});},_9U=new T(function(){return B(unCStr("DC2"));}),_9V=[0,18],_9W=function(_9X){return new F(function(){return _8r(_9U,function(_9Y){return E(new T(function(){return B(A(_9X,[_9V]));}));});});},_9Z=new T(function(){return B(unCStr("DC3"));}),_a0=[0,19],_a1=function(_a2){return new F(function(){return _8r(_9Z,function(_a3){return E(new T(function(){return B(A(_a2,[_a0]));}));});});},_a4=new T(function(){return B(unCStr("DC4"));}),_a5=[0,20],_a6=function(_a7){return new F(function(){return _8r(_a4,function(_a8){return E(new T(function(){return B(A(_a7,[_a5]));}));});});},_a9=new T(function(){return B(unCStr("NAK"));}),_aa=[0,21],_ab=function(_ac){return new F(function(){return _8r(_a9,function(_ad){return E(new T(function(){return B(A(_ac,[_aa]));}));});});},_ae=new T(function(){return B(unCStr("SYN"));}),_af=[0,22],_ag=function(_ah){return new F(function(){return _8r(_ae,function(_ai){return E(new T(function(){return B(A(_ah,[_af]));}));});});},_aj=new T(function(){return B(unCStr("ETB"));}),_ak=[0,23],_al=function(_am){return new F(function(){return _8r(_aj,function(_an){return E(new T(function(){return B(A(_am,[_ak]));}));});});},_ao=new T(function(){return B(unCStr("CAN"));}),_ap=[0,24],_aq=function(_ar){return new F(function(){return _8r(_ao,function(_as){return E(new T(function(){return B(A(_ar,[_ap]));}));});});},_at=new T(function(){return B(unCStr("EM"));}),_au=[0,25],_av=function(_aw){return new F(function(){return _8r(_at,function(_ax){return E(new T(function(){return B(A(_aw,[_au]));}));});});},_ay=new T(function(){return B(unCStr("SUB"));}),_az=[0,26],_aA=function(_aB){return new F(function(){return _8r(_ay,function(_aC){return E(new T(function(){return B(A(_aB,[_az]));}));});});},_aD=new T(function(){return B(unCStr("ESC"));}),_aE=[0,27],_aF=function(_aG){return new F(function(){return _8r(_aD,function(_aH){return E(new T(function(){return B(A(_aG,[_aE]));}));});});},_aI=new T(function(){return B(unCStr("FS"));}),_aJ=[0,28],_aK=function(_aL){return new F(function(){return _8r(_aI,function(_aM){return E(new T(function(){return B(A(_aL,[_aJ]));}));});});},_aN=new T(function(){return B(unCStr("GS"));}),_aO=[0,29],_aP=function(_aQ){return new F(function(){return _8r(_aN,function(_aR){return E(new T(function(){return B(A(_aQ,[_aO]));}));});});},_aS=new T(function(){return B(unCStr("RS"));}),_aT=[0,30],_aU=function(_aV){return new F(function(){return _8r(_aS,function(_aW){return E(new T(function(){return B(A(_aV,[_aT]));}));});});},_aX=new T(function(){return B(unCStr("US"));}),_aY=[0,31],_aZ=function(_b0){return new F(function(){return _8r(_aX,function(_b1){return E(new T(function(){return B(A(_b0,[_aY]));}));});});},_b2=new T(function(){return B(unCStr("SP"));}),_b3=[0,32],_b4=function(_b5){return new F(function(){return _8r(_b2,function(_b6){return E(new T(function(){return B(A(_b5,[_b3]));}));});});},_b7=new T(function(){return B(unCStr("DEL"));}),_b8=[0,127],_b9=function(_ba){return new F(function(){return _8r(_b7,function(_bb){return E(new T(function(){return B(A(_ba,[_b8]));}));});});},_bc=[1,_b9,_0],_bd=[1,_b4,_bc],_be=[1,_aZ,_bd],_bf=[1,_aU,_be],_bg=[1,_aP,_bf],_bh=[1,_aK,_bg],_bi=[1,_aF,_bh],_bj=[1,_aA,_bi],_bk=[1,_av,_bj],_bl=[1,_aq,_bk],_bm=[1,_al,_bl],_bn=[1,_ag,_bm],_bo=[1,_ab,_bn],_bp=[1,_a6,_bo],_bq=[1,_a1,_bp],_br=[1,_9W,_bq],_bs=[1,_9R,_br],_bt=[1,_9M,_bs],_bu=[1,_9H,_bt],_bv=[1,_9C,_bu],_bw=[1,_9x,_bv],_bx=[1,_9s,_bw],_by=[1,_9n,_bx],_bz=[1,_9i,_by],_bA=[1,_9d,_bz],_bB=[1,_98,_bA],_bC=[1,_93,_bB],_bD=[1,_8Y,_bC],_bE=[1,_8T,_bD],_bF=[1,_8O,_bE],_bG=[1,_8J,_bF],_bH=[1,_8E,_bG],_bI=new T(function(){return B(unCStr("SOH"));}),_bJ=[0,1],_bK=function(_bL){return new F(function(){return _8r(_bI,function(_bM){return E(new T(function(){return B(A(_bL,[_bJ]));}));});});},_bN=new T(function(){return B(unCStr("SO"));}),_bO=[0,14],_bP=function(_bQ){return new F(function(){return _8r(_bN,function(_bR){return E(new T(function(){return B(A(_bQ,[_bO]));}));});});},_bS=function(_bT){return new F(function(){return _5M(_bK,_bP,_bT);});},_bU=[1,_bS,_bH],_bV=new T(function(){return B(_8g(_bU));}),_bW=[0,1114111],_bX=[0,34],_bY=[0,_bX,_7V],_bZ=[0,39],_c0=[0,_bZ,_7V],_c1=[0,92],_c2=[0,_c1,_7V],_c3=[0,_97,_7V],_c4=[0,_9c,_7V],_c5=[0,_9w,_7V],_c6=[0,_9m,_7V],_c7=[0,_9B,_7V],_c8=[0,_9h,_7V],_c9=[0,_9r,_7V],_ca=[0,_8D,_7V],_cb=[0,_bJ,_7V],_cc=[0,_8I,_7V],_cd=[0,_8N,_7V],_ce=[0,_8S,_7V],_cf=[0,_8X,_7V],_cg=[0,_92,_7V],_ch=[0,_97,_7V],_ci=[0,_9c,_7V],_cj=[0,_9h,_7V],_ck=[0,_9m,_7V],_cl=[0,_9r,_7V],_cm=[0,_9w,_7V],_cn=[0,_9B,_7V],_co=[0,_bO,_7V],_cp=[0,_9G,_7V],_cq=[0,_9L,_7V],_cr=[0,_9Q,_7V],_cs=[0,_9V,_7V],_ct=[0,_a0,_7V],_cu=[0,_a5,_7V],_cv=[0,_aa,_7V],_cw=[0,_af,_7V],_cx=[0,_ak,_7V],_cy=[0,_ap,_7V],_cz=[0,_au,_7V],_cA=[0,_az,_7V],_cB=[0,_aE,_7V],_cC=[0,_aJ,_7V],_cD=[0,_aO,_7V],_cE=[0,_aT,_7V],_cF=[0,_aY,_7V],_cG=function(_cH){return new F(function(){return _4u([0,function(_cI){switch(E(E(_cI)[1])){case 34:return E(new T(function(){return B(A(_cH,[_bY]));}));case 39:return E(new T(function(){return B(A(_cH,[_c0]));}));case 92:return E(new T(function(){return B(A(_cH,[_c2]));}));case 97:return E(new T(function(){return B(A(_cH,[_c3]));}));case 98:return E(new T(function(){return B(A(_cH,[_c4]));}));case 102:return E(new T(function(){return B(A(_cH,[_c5]));}));case 110:return E(new T(function(){return B(A(_cH,[_c6]));}));case 114:return E(new T(function(){return B(A(_cH,[_c7]));}));case 116:return E(new T(function(){return B(A(_cH,[_c8]));}));case 118:return E(new T(function(){return B(A(_cH,[_c9]));}));default:return [2];}}],new T(function(){return B(_4u(B(_5M(_7W,_7Z,function(_cJ){return new F(function(){return _69(_cJ,function(_cK){var _cL=B(_78(new T(function(){return B(_6Y(E(_cJ)[1]));}),_6X,_cK));return !B(_86(_cL,_bW))?[2]:B(A(_cH,[[0,new T(function(){var _cM=B(_83(_cL));if(_cM>>>0>1114111){var _cN=B(_81(_cM));}else{var _cN=[0,_cM];}var _cO=_cN,_cP=_cO;return _cP;}),_7V]]));});});})),new T(function(){return B(_4u([0,function(_cQ){return E(E(_cQ)[1])==94?E([0,function(_cR){switch(E(E(_cR)[1])){case 64:return E(new T(function(){return B(A(_cH,[_ca]));}));case 65:return E(new T(function(){return B(A(_cH,[_cb]));}));case 66:return E(new T(function(){return B(A(_cH,[_cc]));}));case 67:return E(new T(function(){return B(A(_cH,[_cd]));}));case 68:return E(new T(function(){return B(A(_cH,[_ce]));}));case 69:return E(new T(function(){return B(A(_cH,[_cf]));}));case 70:return E(new T(function(){return B(A(_cH,[_cg]));}));case 71:return E(new T(function(){return B(A(_cH,[_ch]));}));case 72:return E(new T(function(){return B(A(_cH,[_ci]));}));case 73:return E(new T(function(){return B(A(_cH,[_cj]));}));case 74:return E(new T(function(){return B(A(_cH,[_ck]));}));case 75:return E(new T(function(){return B(A(_cH,[_cl]));}));case 76:return E(new T(function(){return B(A(_cH,[_cm]));}));case 77:return E(new T(function(){return B(A(_cH,[_cn]));}));case 78:return E(new T(function(){return B(A(_cH,[_co]));}));case 79:return E(new T(function(){return B(A(_cH,[_cp]));}));case 80:return E(new T(function(){return B(A(_cH,[_cq]));}));case 81:return E(new T(function(){return B(A(_cH,[_cr]));}));case 82:return E(new T(function(){return B(A(_cH,[_cs]));}));case 83:return E(new T(function(){return B(A(_cH,[_ct]));}));case 84:return E(new T(function(){return B(A(_cH,[_cu]));}));case 85:return E(new T(function(){return B(A(_cH,[_cv]));}));case 86:return E(new T(function(){return B(A(_cH,[_cw]));}));case 87:return E(new T(function(){return B(A(_cH,[_cx]));}));case 88:return E(new T(function(){return B(A(_cH,[_cy]));}));case 89:return E(new T(function(){return B(A(_cH,[_cz]));}));case 90:return E(new T(function(){return B(A(_cH,[_cA]));}));case 91:return E(new T(function(){return B(A(_cH,[_cB]));}));case 92:return E(new T(function(){return B(A(_cH,[_cC]));}));case 93:return E(new T(function(){return B(A(_cH,[_cD]));}));case 94:return E(new T(function(){return B(A(_cH,[_cE]));}));case 95:return E(new T(function(){return B(A(_cH,[_cF]));}));default:return [2];}}]):[2];}],new T(function(){return B(A(_bV,[function(_cS){return new F(function(){return A(_cH,[[0,_cS,_7V]]);});}]));})));})));}));});},_cT=function(_cU){return new F(function(){return A(_cU,[_1k]);});},_cV=function(_cW){var _cX=E(_cW);if(!_cX[0]){return E(_cT);}else{var _cY=_cX[2],_cZ=E(E(_cX[1])[1]);switch(_cZ){case 9:return function(_d0){return [0,function(_d1){return E(new T(function(){return B(A(new T(function(){return B(_cV(_cY));}),[_d0]));}));}];};case 10:return function(_d2){return [0,function(_d3){return E(new T(function(){return B(A(new T(function(){return B(_cV(_cY));}),[_d2]));}));}];};case 11:return function(_d4){return [0,function(_d5){return E(new T(function(){return B(A(new T(function(){return B(_cV(_cY));}),[_d4]));}));}];};case 12:return function(_d6){return [0,function(_d7){return E(new T(function(){return B(A(new T(function(){return B(_cV(_cY));}),[_d6]));}));}];};case 13:return function(_d8){return [0,function(_d9){return E(new T(function(){return B(A(new T(function(){return B(_cV(_cY));}),[_d8]));}));}];};case 32:return function(_da){return [0,function(_db){return E(new T(function(){return B(A(new T(function(){return B(_cV(_cY));}),[_da]));}));}];};case 160:return function(_dc){return [0,function(_dd){return E(new T(function(){return B(A(new T(function(){return B(_cV(_cY));}),[_dc]));}));}];};default:var _de=u_iswspace(_cZ),_df=_de;return E(_df)==0?E(_cT):function(_dg){return [0,function(_dh){return E(new T(function(){return B(A(new T(function(){return B(_cV(_cY));}),[_dg]));}));}];};}}},_di=function(_dj){var _dk=new T(function(){return B(_di(_dj));}),_dl=[1,function(_dm){return new F(function(){return A(_cV,[_dm,function(_dn){return E([0,function(_do){return E(E(_do)[1])==92?E(_dk):[2];}]);}]);});}];return new F(function(){return _4u([0,function(_dp){return E(E(_dp)[1])==92?E([0,function(_dq){var _dr=E(E(_dq)[1]);switch(_dr){case 9:return E(_dl);case 10:return E(_dl);case 11:return E(_dl);case 12:return E(_dl);case 13:return E(_dl);case 32:return E(_dl);case 38:return E(_dk);case 160:return E(_dl);default:var _ds=u_iswspace(_dr),_dt=_ds;return E(_dt)==0?[2]:E(_dl);}}]):[2];}],[0,function(_du){var _dv=E(_du);return E(_dv[1])==92?E(new T(function(){return B(_cG(_dj));})):B(A(_dj,[[0,_dv,_7U]]));}]);});},_dw=function(_dx,_dy){return new F(function(){return _di(function(_dz){var _dA=E(_dz),_dB=E(_dA[1]);if(E(_dB[1])==34){if(!E(_dA[2])){return E(new T(function(){return B(A(_dy,[[1,new T(function(){return B(A(_dx,[_0]));})]]));}));}else{return new F(function(){return _dw(function(_dC){return new F(function(){return A(_dx,[[1,_dB,_dC]]);});},_dy);});}}else{return new F(function(){return _dw(function(_dD){return new F(function(){return A(_dx,[[1,_dB,_dD]]);});},_dy);});}});});},_dE=new T(function(){return B(unCStr("_\'"));}),_dF=function(_dG){var _dH=u_iswalnum(_dG),_dI=_dH;return E(_dI)==0?B(_7C(_5b,[0,_dG],_dE)):true;},_dJ=function(_dK){return new F(function(){return _dF(E(_dK)[1]);});},_dL=new T(function(){return B(unCStr(",;()[]{}`"));}),_dM=function(_dN){return new F(function(){return A(_dN,[_0]);});},_dO=function(_dP,_dQ){var _dR=function(_dS){var _dT=E(_dS);if(!_dT[0]){return E(_dM);}else{var _dU=_dT[1];return !B(A(_dP,[_dU]))?E(_dM):function(_dV){return [0,function(_dW){return E(new T(function(){return B(A(new T(function(){return B(_dR(_dT[2]));}),[function(_dX){return new F(function(){return A(_dV,[[1,_dU,_dX]]);});}]));}));}];};}};return [1,function(_dY){return new F(function(){return A(_dR,[_dY,_dQ]);});}];},_dZ=new T(function(){return B(unCStr(".."));}),_e0=new T(function(){return B(unCStr("::"));}),_e1=new T(function(){return B(unCStr("->"));}),_e2=[0,64],_e3=[1,_e2,_0],_e4=[0,126],_e5=[1,_e4,_0],_e6=new T(function(){return B(unCStr("=>"));}),_e7=[1,_e6,_0],_e8=[1,_e5,_e7],_e9=[1,_e3,_e8],_ea=[1,_e1,_e9],_eb=new T(function(){return B(unCStr("<-"));}),_ec=[1,_eb,_ea],_ed=[0,124],_ee=[1,_ed,_0],_ef=[1,_ee,_ec],_eg=[1,_c1,_0],_eh=[1,_eg,_ef],_ei=[0,61],_ej=[1,_ei,_0],_ek=[1,_ej,_eh],_el=[1,_e0,_ek],_em=[1,_dZ,_el],_en=function(_eo){return new F(function(){return _4u([1,function(_ep){return E(_ep)[0]==0?E(new T(function(){return B(A(_eo,[_66]));})):[2];}],new T(function(){return B(_4u([0,function(_eq){return E(E(_eq)[1])==39?E([0,function(_er){var _es=E(_er);switch(E(_es[1])){case 39:return [2];case 92:return E(new T(function(){return B(_cG(function(_et){var _eu=E(_et);return new F(function(){return (function(_ev,_ew){var _ex=new T(function(){return B(A(_eo,[[0,_ev]]));});return !E(_ew)?E(E(_ev)[1])==39?[2]:[0,function(_ey){return E(E(_ey)[1])==39?E(_ex):[2];}]:[0,function(_ez){return E(E(_ez)[1])==39?E(_ex):[2];}];})(_eu[1],_eu[2]);});}));}));default:return [0,function(_eA){return E(E(_eA)[1])==39?E(new T(function(){return B(A(_eo,[[0,_es]]));})):[2];}];}}]):[2];}],new T(function(){return B(_4u([0,function(_eB){return E(E(_eB)[1])==34?E(new T(function(){return B(_dw(_1L,_eo));})):[2];}],new T(function(){return B(_4u([0,function(_eC){return !B(_7C(_5b,_eC,_dL))?[2]:B(A(_eo,[[2,[1,_eC,_0]]]));}],new T(function(){return B(_4u([0,function(_eD){if(!B(_7C(_5b,_eD,_7H))){return [2];}else{return new F(function(){return _dO(_7I,function(_eE){var _eF=[1,_eD,_eE];return !B(_7C(_5s,_eF,_em))?B(A(_eo,[[4,_eF]])):B(A(_eo,[[2,_eF]]));});});}}],new T(function(){return B(_4u([0,function(_eG){var _eH=E(_eG),_eI=_eH[1],_eJ=u_iswalpha(_eI),_eK=_eJ;if(!E(_eK)){if(E(_eI)==95){return new F(function(){return _dO(_dJ,function(_eL){return new F(function(){return A(_eo,[[3,[1,_eH,_eL]]]);});});});}else{return [2];}}else{return new F(function(){return _dO(_dJ,function(_eM){return new F(function(){return A(_eo,[[3,[1,_eH,_eM]]]);});});});}}],new T(function(){return B(_5M(_7M,_7x,_eo));})));})));})));})));})));}));});},_eN=function(_eO){return [1,function(_eP){return new F(function(){return A(_cV,[_eP,function(_eQ){return E(new T(function(){return B(_en(_eO));}));}]);});}];},_eR=[0,0],_eS=function(_eT,_eU){return new F(function(){return _eN(function(_eV){var _eW=E(_eV);if(_eW[0]==2){var _eX=E(_eW[1]);return _eX[0]==0?[2]:E(E(_eX[1])[1])==40?E(_eX[2])[0]==0?E(new T(function(){return B(A(_eT,[_eR,function(_eY){return new F(function(){return _eN(function(_eZ){var _f0=E(_eZ);if(_f0[0]==2){var _f1=E(_f0[1]);return _f1[0]==0?[2]:E(E(_f1[1])[1])==41?E(_f1[2])[0]==0?E(new T(function(){return B(A(_eU,[_eY]));})):[2]:[2];}else{return [2];}});});}]));})):[2]:[2];}else{return [2];}});});},_f2=function(_f3,_f4,_f5){var _f6=function(_f7,_f8){return new F(function(){return _4u(B(_eN(function(_f9){var _fa=E(_f9);if(_fa[0]==4){var _fb=E(_fa[1]);if(!_fb[0]){return new F(function(){return A(_f3,[_fa,_f7,_f8]);});}else{return E(E(_fb[1])[1])==45?E(_fb[2])[0]==0?E([1,function(_fc){return new F(function(){return A(_cV,[_fc,function(_fd){return E(new T(function(){return B(_en(function(_fe){return new F(function(){return A(_f3,[_fe,_f7,function(_ff){return new F(function(){return A(_f8,[new T(function(){return [0, -E(_ff)[1]];})]);});}]);});}));}));}]);});}]):B(A(_f3,[_fa,_f7,_f8])):B(A(_f3,[_fa,_f7,_f8]));}}else{return new F(function(){return A(_f3,[_fa,_f7,_f8]);});}})),new T(function(){return B(_eS(_f6,_f8));}));});};return new F(function(){return _f6(_f4,_f5);});},_fg=function(_fh,_fi){return [2];},_fj=function(_fk,_fl){return new F(function(){return _fg(_fk,_fl);});},_fm=function(_fn){var _fo=E(_fn);return _fo[0]==0?[1,new T(function(){return B(_78(new T(function(){return B(_6Y(E(_fo[1])[1]));}),_6X,_fo[2]));})]:E(_fo[2])[0]==0?E(_fo[3])[0]==0?[1,new T(function(){return B(_78(_6W,_6X,_fo[1]));})]:[0]:[0];},_fp=function(_fq){var _fr=E(_fq);if(_fr[0]==5){var _fs=B(_fm(_fr[1]));return _fs[0]==0?E(_fg):function(_ft,_fu){return new F(function(){return A(_fu,[new T(function(){return [0,B(_83(_fs[1]))];})]);});};}else{return E(_fj);}},_fv=function(_fw){return [1,function(_fx){return new F(function(){return A(_cV,[_fx,function(_fy){return E([3,_fw,_5E]);}]);});}];},_fz=new T(function(){return B(_f2(_fp,_eR,_fv));}),_fA=new T(function(){return B(unCStr("Prelude.read: ambiguous parse"));}),_fB=new T(function(){return B(err(_fA));}),_fC=new T(function(){return B(unCStr("Prelude.read: no parse"));}),_fD=new T(function(){return B(err(_fC));}),_fE=function(_fF,_fG){if(_fF<=0){if(_fF>=0){return new F(function(){return quot(_fF,_fG);});}else{if(_fG<=0){return new F(function(){return quot(_fF,_fG);});}else{return quot(_fF+1|0,_fG)-1|0;}}}else{if(_fG>=0){if(_fF>=0){return new F(function(){return quot(_fF,_fG);});}else{if(_fG<=0){return new F(function(){return quot(_fF,_fG);});}else{return quot(_fF+1|0,_fG)-1|0;}}}else{return quot(_fF-1|0,_fG)-1|0;}}},_fH=new T(function(){return [0,B(_fE(210,2))];}),_fI=new T(function(){return B(_2u(0,2147483647));}),_fJ=function(_fK,_fL,_fM){return _fM<=_fL?[1,[0,_fK],new T(function(){var _fN=_fL-_fK|0,_fO=function(_fP){return _fP>=(_fM-_fN|0)?[1,[0,_fP],new T(function(){return B(_fO(_fP+_fN|0));})]:[1,[0,_fP],_0];};return B(_fO(_fL));})]:_fM<=_fK?[1,[0,_fK],_0]:[0];},_fQ=function(_fR,_fS,_fT){return _fT>=_fS?[1,[0,_fR],new T(function(){var _fU=_fS-_fR|0,_fV=function(_fW){return _fW<=(_fT-_fU|0)?[1,[0,_fW],new T(function(){return B(_fV(_fW+_fU|0));})]:[1,[0,_fW],_0];};return B(_fV(_fS));})]:_fT>=_fR?[1,[0,_fR],_0]:[0];},_fX=function(_fY,_fZ){return _fZ<_fY?B(_fJ(_fY,_fZ,-2147483648)):B(_fQ(_fY,_fZ,2147483647));},_g0=new T(function(){return B(_fX(105,120));}),_g1=function(_g2,_g3){var _g4=E(_g2);if(!_g4){return [0];}else{var _g5=E(_g3);return _g5[0]==0?[0]:[1,_g5[1],new T(function(){return B(_g1(_g4-1|0,_g5[2]));})];}},_g6=new T(function(){return B(_g1(6,_g0));}),_g7=function(_g8,_g9){var _ga=E(_g8);if(!_ga[0]){return E(_g6);}else{var _gb=_ga[1];return _g9>1?[1,_gb,new T(function(){return B(_g7(_ga[2],_g9-1|0));})]:[1,_gb,_g6];}},_gc=new T(function(){return B(_fX(10,25));}),_gd=new T(function(){return B(_g7(_gc,6));}),_ge=function(_gf){while(1){var _gg=(function(_gh){var _gi=E(_gh);if(!_gi[0]){return [0];}else{var _gj=_gi[2],_gk=E(_gi[1]);if(!E(_gk[2])[0]){return [1,_gk[1],new T(function(){return B(_ge(_gj));})];}else{_gf=_gj;return null;}}})(_gf);if(_gg!=null){return _gg;}}},_gl=function(_gm,_gn){var _go=E(_gn);if(!_go[0]){return [0,_0,_0];}else{var _gp=_go[1];if(!B(A(_gm,[_gp]))){var _gq=new T(function(){var _gr=B(_gl(_gm,_go[2]));return [0,_gr[1],_gr[2]];});return [0,[1,_gp,new T(function(){return E(E(_gq)[1]);})],new T(function(){return E(E(_gq)[2]);})];}else{return [0,_0,_go];}}},_gs=function(_gt,_gu){while(1){var _gv=E(_gu);if(!_gv[0]){return [0];}else{if(!B(A(_gt,[_gv[1]]))){return E(_gv);}else{_gu=_gv[2];continue;}}}},_gw=function(_gx){var _gy=E(_gx);switch(_gy){case 9:return true;case 10:return true;case 11:return true;case 12:return true;case 13:return true;case 32:return true;case 160:return true;default:var _gz=u_iswspace(_gy),_gA=_gz;return E(_gA)==0?false:true;}},_gB=function(_gC){return new F(function(){return _gw(E(_gC)[1]);});},_gD=function(_gE){var _gF=B(_gs(_gB,_gE));if(!_gF[0]){return [0];}else{var _gG=new T(function(){var _gH=B(_gl(_gB,_gF));return [0,_gH[1],_gH[2]];});return [1,new T(function(){return E(E(_gG)[1]);}),new T(function(){return B(_gD(E(_gG)[2]));})];}},_gI=function(_gJ,_){var _gK=setDropCheckerCallback_ffi(function(_gL,_gM,_gN){var _gO=E(_gJ),_gP=_gO[1],_gQ=_gO[2],_gR=new T(function(){return B(_gD(B(_2T(_gL))));}),_gS=new T(function(){var _gT=B(_ge(B(_4k(_fz,new T(function(){return B(_2p(2,B(_1f(_gR,2))));})))));return _gT[0]==0?E(_fD):E(_gT[2])[0]==0?E(_gT[1]):E(_fB);}),_gU=new T(function(){var _gV=B(_ge(B(_4k(_fz,new T(function(){return B(_2p(2,B(_1f(_gR,3))));})))));return _gV[0]==0?E(_fD):E(_gV[2])[0]==0?E(_gV[1]):E(_fB);}),_gW=B(_2A(function(_gX){var _gY=E(_gX)[1]-E(_gM)[1];return _gY<0? -_gY<7:_gY<7;},_gd));if(!_gW[0]){return function(_65){return new F(function(){return _2e(_gS,_gU,_gS,_gU,_gQ,_65);});};}else{var _gZ=_gW[1],_h0=function(_h1,_h2,_){var _h3=E(_gS),_h4=_h3[1];if(_h1<=_h4){return new F(function(){return _2e(_h3,_gU,_h3,_gU,_gQ,_);});}else{if(_h1>=0){var _h5=B(_1f(_gP,_h1)),_h6=new T(function(){return _h4<0;}),_h7=function(_){var _h8=B(_2e(_h3,_gU,_h2,new T(function(){if(_h1>=0){var _h9=E(B(_1f(_gP,_h1))[2]);}else{var _h9=E(_1c);}return _h9;}),_gQ,_)),_ha=_h8;if(!E(_h6)){var _hb=new T(function(){return B(_2M(function(_hc,_hd,_he){return [1,new T(function(){var _hf=E(_hc)[1];return _hf!=_h4?_hf!=_h1?E(_hd):[0,new T(function(){if(_h4>=0){var _hg=E(B(_1f(_gP,_h4))[1]);}else{var _hg=E(_1c);}return _hg;}),new T(function(){return [0,E(E(_hd)[2])[1]+1|0];})]:[0,new T(function(){return E(E(_hd)[1]);}),new T(function(){return [0,E(E(_hd)[2])[1]-1|0];})];}),_he];},_0,_fI,_gP));}),_hh=B((function(_hi,_){while(1){var _hj=(function(_hk,_){var _hl=E(_hk);if(!_hl[0]){return _1k;}else{var _hm=_hl[1],_hn=B(_2e(_h3,_hm,_h3,new T(function(){return [0,E(_hm)[1]-1|0];}),_gQ,_)),_ho=_hn;_hi=_hl[2];return null;}})(_hi,_);if(_hj!=null){return _hj;}}})(B(_2p(1,B(_2u(E(_gU)[1],E(B(_1f(_hb,_h4))[2])[1])))),_)),_hp=_hh;return new F(function(){return _gI([0,_hb,_gQ,_gO[3]],_);});}else{return E(_1c);}},_hq=function(_){return E(_h5[2])[1]>=2?B(_2e(_h3,_gU,_h3,_gU,_gQ,_)):B(_h7(_));};switch(E(_h5[1])){case 0:if(!E(_h6)){switch(E(B(_1f(_gP,_h4))[1])){case 0:return new F(function(){return _h7(_);});break;case 1:return new F(function(){return _hq(_);});break;default:return new F(function(){return _hq(_);});}}else{return E(_1c);}break;case 1:return !E(_h6)?E(B(_1f(_gP,_h4))[1])==1?B(_h7(_)):B(_hq(_)):E(_1c);default:return !E(_h6)?E(B(_1f(_gP,_h4))[1])==2?B(_h7(_)):B(_hq(_)):E(_1c);}}else{return E(_1c);}}};if(E(_gN)[1]<=E(_fH)[1]){var _hr=12+E(_gZ)[1]|0;return function(_65){return new F(function(){return _h0(_hr,[0,_hr],_65);});};}else{var _hs=11-E(_gZ)[1]|0;return function(_65){return new F(function(){return _h0(_hs,[0,_hs],_65);});};}}});return _1k;},_ht=new T(function(){return B(unCStr("Pattern match failure in do expression at main.hs:124:5-10"));}),_hu=new T(function(){return B(unCStr("GHC.IO.Exception"));}),_hv=new T(function(){return B(unCStr("base"));}),_hw=new T(function(){return B(unCStr("IOException"));}),_hx=new T(function(){var _hy=hs_wordToWord64(4053623282),_hz=_hy,_hA=hs_wordToWord64(3693590983),_hB=_hA;return [0,_hz,_hB,[0,_hz,_hB,_hv,_hu,_hw],_0];}),_hC=function(_hD){return E(_hx);},_hE=function(_hF){var _hG=E(_hF);return new F(function(){return _39(B(_35(_hG[1])),_hC,_hG[2]);});},_hH=new T(function(){return B(unCStr(": "));}),_hI=[0,41],_hJ=new T(function(){return B(unCStr(" ("));}),_hK=new T(function(){return B(unCStr("already exists"));}),_hL=new T(function(){return B(unCStr("does not exist"));}),_hM=new T(function(){return B(unCStr("protocol error"));}),_hN=new T(function(){return B(unCStr("failed"));}),_hO=new T(function(){return B(unCStr("invalid argument"));}),_hP=new T(function(){return B(unCStr("inappropriate type"));}),_hQ=new T(function(){return B(unCStr("hardware fault"));}),_hR=new T(function(){return B(unCStr("unsupported operation"));}),_hS=new T(function(){return B(unCStr("timeout"));}),_hT=new T(function(){return B(unCStr("resource vanished"));}),_hU=new T(function(){return B(unCStr("interrupted"));}),_hV=new T(function(){return B(unCStr("resource busy"));}),_hW=new T(function(){return B(unCStr("resource exhausted"));}),_hX=new T(function(){return B(unCStr("end of file"));}),_hY=new T(function(){return B(unCStr("illegal operation"));}),_hZ=new T(function(){return B(unCStr("permission denied"));}),_i0=new T(function(){return B(unCStr("user error"));}),_i1=new T(function(){return B(unCStr("unsatisified constraints"));}),_i2=new T(function(){return B(unCStr("system error"));}),_i3=function(_i4,_i5){switch(E(_i4)){case 0:return new F(function(){return _1u(_hK,_i5);});break;case 1:return new F(function(){return _1u(_hL,_i5);});break;case 2:return new F(function(){return _1u(_hV,_i5);});break;case 3:return new F(function(){return _1u(_hW,_i5);});break;case 4:return new F(function(){return _1u(_hX,_i5);});break;case 5:return new F(function(){return _1u(_hY,_i5);});break;case 6:return new F(function(){return _1u(_hZ,_i5);});break;case 7:return new F(function(){return _1u(_i0,_i5);});break;case 8:return new F(function(){return _1u(_i1,_i5);});break;case 9:return new F(function(){return _1u(_i2,_i5);});break;case 10:return new F(function(){return _1u(_hM,_i5);});break;case 11:return new F(function(){return _1u(_hN,_i5);});break;case 12:return new F(function(){return _1u(_hO,_i5);});break;case 13:return new F(function(){return _1u(_hP,_i5);});break;case 14:return new F(function(){return _1u(_hQ,_i5);});break;case 15:return new F(function(){return _1u(_hR,_i5);});break;case 16:return new F(function(){return _1u(_hS,_i5);});break;case 17:return new F(function(){return _1u(_hT,_i5);});break;default:return new F(function(){return _1u(_hU,_i5);});}},_i6=[0,125],_i7=new T(function(){return B(unCStr("{handle: "));}),_i8=function(_i9,_ia,_ib,_ic,_id,_ie){var _if=new T(function(){var _ig=new T(function(){return B(_i3(_ia,new T(function(){var _ih=E(_ic);return _ih[0]==0?E(_ie):B(_1u(_hJ,new T(function(){return B(_1u(_ih,[1,_hI,_ie]));})));})));}),_ii=E(_ib);return _ii[0]==0?E(_ig):B(_1u(_ii,new T(function(){return B(_1u(_hH,_ig));})));}),_ij=E(_id);if(!_ij[0]){var _ik=E(_i9);if(!_ik[0]){return E(_if);}else{var _il=E(_ik[1]);return _il[0]==0?B(_1u(_i7,new T(function(){return B(_1u(_il[1],[1,_i6,new T(function(){return B(_1u(_hH,_if));})]));}))):B(_1u(_i7,new T(function(){return B(_1u(_il[1],[1,_i6,new T(function(){return B(_1u(_hH,_if));})]));})));}}else{return new F(function(){return _1u(_ij[1],new T(function(){return B(_1u(_hH,_if));}));});}},_im=function(_in){var _io=E(_in);return new F(function(){return _i8(_io[1],_io[2],_io[3],_io[4],_io[6],_0);});},_ip=function(_iq,_ir){var _is=E(_iq);return new F(function(){return _i8(_is[1],_is[2],_is[3],_is[4],_is[6],_ir);});},_it=function(_iu,_iv){return new F(function(){return _3z(_ip,_iu,_iv);});},_iw=function(_ix,_iy,_iz){var _iA=E(_iy);return new F(function(){return _i8(_iA[1],_iA[2],_iA[3],_iA[4],_iA[6],_iz);});},_iB=[0,_iw,_im,_it],_iC=new T(function(){return [0,_hC,_iB,_iD,_hE];}),_iD=function(_iE){return [0,_iC,_iE];},_iF=7,_iG=function(_iH){return [0,_7o,_iF,_0,_iH,_7o,_7o];},_iI=function(_iJ,_){return new F(function(){return die(new T(function(){return B(_iD(new T(function(){return B(_iG(_iJ));})));}));});},_iK=function(_iL,_){return new F(function(){return _iI(_iL,_);});},_iM=[0,114],_iN=[1,_iM,_0],_iO=new T(function(){return B(_1F(0,6,_0));}),_iP=new T(function(){return B(unCStr("cx"));}),_iQ=new T(function(){return B(unCStr("cy"));}),_iR=new T(function(){return B(unCStr("circle"));}),_iS=new T(function(){return B(unCStr("http://www.w3.org/2000/svg"));}),_iT=new T(function(){return B(unCStr("board"));}),_iU=function(_){return _1k;},_iV=function(_iW,_iX,_){while(1){var _iY=(function(_iZ,_j0,_){var _j1=E(_j0);if(!_j1[0]){return _1k;}else{var _j2=E(_j1[1]),_j3=_j2[1],_j4=[0,_iZ],_j5=B(A(_2M,[function(_j6,_j7,_j8,_){var _j9=jsFind(toJSStr(E(_iT))),_ja=_j9,_jb=E(_ja);if(!_jb[0]){var _jc=B(_iK(_ht,_)),_jd=_jc;return new F(function(){return A(_j8,[_]);});}else{var _je=jsCreateElemNS(toJSStr(E(_iS)),toJSStr(E(_iR))),_jf=_je,_jg=[0,_jf],_jh=B(A(_1o,[_1L,_jg,_iN,_iO,_])),_ji=_jh,_jj=new T(function(){var _jk=B(_20(_j4,_j6));return [0,_jk[1],_jk[2]];}),_jl=B(A(_1o,[_1L,_jg,_iP,new T(function(){return B(_1F(0,E(E(_jj)[1])[1],_0));}),_])),_jm=_jl,_jn=B(A(_1o,[_1L,_jg,_iQ,new T(function(){return B(_1F(0,E(E(_jj)[2])[1],_0));}),_])),_jo=_jn,_jp=B(A(_1P,[_jg,_m,_j4,_j6,_j7,_])),_jq=_jp,_jr=jsAppendChild(_jf,E(_jb[1])[1]);return new F(function(){return A(_j8,[_]);});}},_iU,_fI,new T(function(){var _js=E(_j2[2])[1];if(_js>0){var _jt=function(_ju){return _ju>1?[1,_j3,new T(function(){return B(_jt(_ju-1|0));})]:E([1,_j3,_0]);},_jv=B(_jt(_js));}else{var _jv=[0];}var _jw=_jv;return _jw;}),_])),_jx=_j5,_jy=E(_iZ);if(_jy==2147483647){return _1k;}else{_iW=_jy+1|0;_iX=_j1[2];return null;}}})(_iW,_iX,_);if(_iY!=null){return _iY;}}},_jz=function(_){var _jA=B(_iV(0,_19,_)),_jB=_jA;return new F(function(){return _gI(_1a,_);});},_jC=function(_){return new F(function(){return _jz(_);});};
var hasteMain = function() {B(A(_jC, [0]));};window.onload = hasteMain;