/* ghcjs-base jsbits/jsstring.js, as GHC 9.12.2 links it into lib.js for a
   program that depends on ghcjs-base (miso does): after CPP, byte for byte
   from references/miso-lynx/oracle-jsexe/lib.js lines 91-1162. ghcjs-base is
   not vendored as a package here, so this file rides with the static RTS
   until it is; `Data.JSString.pack` reaches `h$jsstringPack` through it.
   It builds `h$jsstringEmpty` from the `JSVal` constructor at load time, which
   is why every program links GHC.JS.Prim. */
//#OPTIONS: CPP
/*
 * Support code for the Data.JSString module. This code presents a JSString
 * as a sequence of code points and hides the underlying encoding ugliness of
 * the JavaScript strings.
 *
 * Use Data.JSString.Raw for direct access to the JSThis makes the operations more expen
 */
/*
 * Some workarounds here for JS engines that do not support proper
 * code point access
 */
var h$jsstringEmpty = (h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, ('')));
var h$jsstringHead, h$jsstringTail, h$jsstringCons,
    h$jsstringSingleton, h$jsstringSnoc, h$jsstringUncons,
    h$jsstringIndex, h$jsstringUncheckedIndex;
var h$fromCodePoint;
if(String.prototype.fromCodePoint) {
    h$fromCodePoint = String.fromCodePoint;
} else {
    // polyfill from https://github.com/mathiasbynens/String.fromCodePoint (MIT-license)
    h$fromCodePoint =
      (function() {
          var stringFromCharCode = String.fromCharCode;
          var floor = Math.floor;
          return function(_) {
              var MAX_SIZE = 0x4000;
              var codeUnits = [];
              var highSurrogate;
              var lowSurrogate;
              var index = -1;
              var length = arguments.length;
              if (!length) {
                  return '';
              }
              var result = '';
              while (++index < length) {
                  var codePoint = Number(arguments[index]);
                  if (
                      !isFinite(codePoint) || // `NaN`, `+Infinity`, or `-Infinity`
                      codePoint < 0 || // not a valid Unicode code point
                      codePoint > 0x10FFFF || // not a valid Unicode code point
                      floor(codePoint) != codePoint // not an integer
                  ) {
                      throw RangeError('Invalid code point: ' + codePoint);
                  }
                  if (codePoint <= 0xFFFF) { // BMP code point
                      codeUnits.push(codePoint);
                  } else { // Astral code point; split in surrogate halves
                      // https://mathiasbynens.be/notes/javascript-encoding#surrogate-formulae
                      codePoint -= 0x10000;
                      highSurrogate = (codePoint >> 10) + 0xD800;
                      lowSurrogate = (codePoint % 0x400) + 0xDC00;
                      codeUnits.push(highSurrogate, lowSurrogate);
                  }
                  if (index + 1 == length || codeUnits.length > MAX_SIZE) {
                      result += stringFromCharCode.apply(null, codeUnits);
                      codeUnits.length = 0;
                  }
              }
              return result;
          }
      })();
}
if(String.prototype.codePointAt) {
    h$jsstringSingleton = function(ch) {
                                                        ;
 return String.fromCodePoint(ch);
    }
    h$jsstringHead = function(str) {
                                                    ;
 var cp = str.codePointAt(0);
 return (cp === undefined) ? -1 : (cp|0);
    }
    h$jsstringTail = function(str) {
                                                    ;
 var l = str.length;
 if(l===0) return null;
 var ch = str.codePointAt(0);
 if(ch === undefined) return null;
 // string length is at least two if ch comes from a surrogate pair
 return str.substr(((ch)>=0x10000)?2:1);
    }
    h$jsstringCons = function(ch, str) {
                                                                      ;
 return String.fromCodePoint(ch)+str;
    }
    h$jsstringSnoc = function(str, ch) {
                                                                 ;
 return str+String.fromCodePoint(ch);
    }
    h$jsstringUncons = function(str) {
                                                             ;
 var l = str.length;
 if(l===0) {
          { h$ret1 = (null); return (-1); };
        }
 var ch = str.codePointAt(0);
        if(ch === undefined) {
     { h$ret1 = (null); return (-1); };
        }
        { h$ret1 = (str.substr(((ch)>=0x10000)?2:1)); return (ch); };
    }
    // index is the first part of the character
    h$jsstringIndex = function(i, str) {
                                                                      ;
 var ch = str.codePointAt(i);
 if(ch === undefined) return -1;
 return ch;
    }
    h$jsstringUncheckedIndex = function(i, str) {
                                                                                      ;
 return str.codePointAt(i);
    }
} else {
    h$jsstringSingleton = function(ch) {
                                                           ;
 return (((ch)>=0x10000)) ? String.fromCharCode(((((ch)-0x10000)>>>10)+0xDC00), (((ch)&0x3FF)+0xD800))
                               : String.fromCharCode(ch);
    }
    h$jsstringHead = function(str) {
                                                       ;
 var l = str.length;
 if(l===0) return -1;
 var ch = str.charCodeAt(0);
 if(((ch|1023)===0xDBFF)) {
     return (l>1) ? ((((ch)-0xD800)<<10)+(str.charCodeAt(1))-0xDC00+0x10000) : -1;
 } else {
     return ch;
 }
    }
    h$jsstringTail = function(str) {
                                                       ;
 var l = str.length;
 if(l===0) return null;
 var ch = str.charCodeAt(0);
 if(((ch|1023)===0xDBFF)) {
     return (l>1)?str.substr(2):null;
 } else return str.substr(1);
    }
    h$jsstringCons = function(ch, str) {
                                                                         ;
 return ((((ch)>=0x10000)) ? String.fromCharCode(((((ch)-0x10000)>>>10)+0xDC00), (((ch)&0x3FF)+0xD800))
                                : String.fromCharCode(ch))
                                + str;
    }
    h$jsstringSnoc = function(str, ch) {
                                                                    ;
 return str + ((((ch)>=0x10000)) ? String.fromCharCode(((((ch)-0x10000)>>>10)+0xDC00), (((ch)&0x3FF)+0xD800))
                                      : String.fromCharCode(ch));
    }
    h$jsstringUncons = function(str) {
                                                                ;
 var l = str.length;
 if(l===0) {
          { h$ret1 = (null); return (-1); };
        }
 var ch = str.charCodeAt(0);
 if(((ch|1023)===0xDBFF)) {
   if(l > 1) {
        { h$ret1 = (str.substr(2)); return (((((ch)-0xD800)<<10)+(str.charCodeAt(1))-0xDC00+0x10000)); };
   } else {
       { h$ret1 = (null); return (-1); };
   }
 } else {
      { h$ret1 = (str.substr(1)); return (ch); };
 }
    }
    // index is the first part of the character
    h$jsstringIndex = function(i, str) {
        // TRACE_JSSTRING("(no codePointAt) index: " + i + " '" + str + "'");
 var ch = str.charCodeAt(i);
 if(ch != ch) return -1; // NaN test
 return (((ch|1023)===0xDBFF)) ? ((((ch)-0xD800)<<10)+(str.charCodeAt(i+1))-0xDC00+0x10000) : ch;
    }
    h$jsstringUncheckedIndex = function(i, str) {
                                                                                         ;
 var ch = str.charCodeAt(i);
 return (((ch|1023)===0xDBFF)) ? ((((ch)-0xD800)<<10)+(str.charCodeAt(i+1))-0xDC00+0x10000) : ch;
    }
}
function h$jsstringUnsnoc(str) {
                                         ;
  var l = str.length;
  if(l===0) {
    { h$ret1 = (null); return (-1); };
  }
  var ch = str.charCodeAt(l-1);
  if(((ch|1023)===0xDFFF)) {
    if(l !== 1) {
      { h$ret1 = (str.substr(0,l-2)); return (((((str.charCodeAt(l-2))-0xD800)<<10)+(ch)-0xDC00+0x10000)); };
    } else {
      { h$ret1 = (null); return (-1); };
    }
  } else {
    { h$ret1 = (str.substr(0,l-1)); return (ch); };
  }
}
function h$jsstringPack(xs) {
    var r = '', i = 0, a = [], c;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 c = ((xs).d1);
 a[i++] = ((typeof(c) === 'number')?(c):(c).d1);
 if(i >= 60000) {
     r += h$fromCodePoint.apply(null, a);
     a = [];
     i = 0;
 }
 xs = ((xs).d2);
    }
    if(i > 0) r += h$fromCodePoint.apply(null, a);
                                       ;
    return r;
}
function h$jsstringPackReverse(xs) {
    var a = [], i = 0, c;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 c = ((xs).d1);
 a[i++] = ((typeof(c) === 'number')?(c):(c).d1);
 xs = ((xs).d2);
    }
    if(i===0) return '';
    var r = h$jsstringConvertArray(a.reverse());
                                              ;
    return r;
}
function h$jsstringPackArray(arr) {
                                        ;
    return h$jsstringConvertArray(arr);
}
function h$jsstringPackArrayReverse(arr) {
                                                ;
    return h$jsstringConvertArray(arr.reverse());
}
function h$jsstringConvertArray(arr) {
    if(arr.length < 60000) {
 return h$fromCodePoint.apply(null, arr);
    } else {
 var r = '';
 for(var i=0; i<arr.length; i+=60000) {
     r += h$fromCodePoint.apply(null, arr.slice(i, i+60000));
 }
 return r;
    }
}
function h$jsstringInit(str) {
                                         ;
    var l = str.length;
    if(l===0) return null;
    var ch = str.charCodeAt(l-1);
    var o = ((ch|1023)===0xDFFF)?2:1;
    var r = str.substr(0, l-o);
    return r;
}
function h$jsstringLast(str) {
                                         ;
    var l = str.length;
    if(l===0) return -1;
    var ch = str.charCodeAt(l-1);
    if(((ch|1023)===0xDFFF)) {
 return (l>1) ? ((((str.charCodeAt(l-2))-0xD800)<<10)+(ch)-0xDC00+0x10000) : -1;
    } else return ch;
}
// index is the last part of the character
function h$jsstringIndexR(i, str) {
                                                     ;
    if(i < 0 || i > str.length) return -1;
    var ch = str.charCodeAt(i);
    return (((ch|1023)===0xDFFF)) ? ((((str.charCodeAt(i-1))-0xD800)<<10)+(ch)-0xDC00+0x10000) : ch;
}
function h$jsstringNextIndex(i, str) {
                                                        ;
    return i + (((str.charCodeAt(i)|1023)===0xDBFF)?2:1);
}
function h$jsstringTake(n, str) {
                                                   ;
    if(n <= 0) return '';
    var i = 0, l = str.length, ch;
    if(n >= l) return str;
    while(n--) {
 ch = str.charCodeAt(i++);
 if(((ch|1023)===0xDBFF)) i++;
 if(i >= l) return str;
    }
    return str.substr(0,i);
}
function h$jsstringDrop(n, str) {
                                                   ;
    if(n <= 0) return str;
    var i = 0, l = str.length, ch;
    if(n >= l) return '';
    while(n--) {
 ch = str.charCodeAt(i++);
 if(((ch|1023)===0xDBFF)) i++;
 if(i >= l) return '';
    }
    return str.substr(i);
}
function h$jsstringSplitAt(n, str) {
                                                    ;
  if(n <= 0) {
    { h$ret1 = (str); return (""); };
  } else if(n >= str.length) {
    { h$ret1 = (""); return (str); };
  }
  var i = 0, l = str.length, ch;
  while(n--) {
    ch = str.charCodeAt(i++);
    if(((ch|1023)===0xDBFF)) i++;
    if(i >= l) {
      { h$ret1 = (""); return (str); };
    }
  }
  { h$ret1 = (str.substr(i)); return (str.substr(0,i)); };
}
function h$jsstringTakeEnd(n, str) {
                                                      ;
    if(n <= 0) return '';
    var l = str.length, i = l-1, ch;
    if(n >= l) return str;
    while(n-- && i >= 0) {
 ch = str.charCodeAt(i--);
 if(((ch|1023)===0xDFFF)) i--;
    }
    return (i<0) ? str : str.substr(i+1);
}
function h$jsstringDropEnd(n, str) {
                                                      ;
    if(n <= 0) return str;
    var l = str.length, i = l-1, ch;
    if(n >= l) return '';
    while(n-- && i >= 0) {
 ch = str.charCodeAt(i--);
 if(((ch|1023)===0xDFFF)) i--;
    }
    return (i<0) ? '' : str.substr(0,i+1);
}
function h$jsstringIntercalate(x, ys) {
                                              ;
    var a = [], i = 0;
    while(((ys).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 if(i) a[i++] = x;
 a[i++] = ((((ys).d1)).d1);
 ys = ((ys).d2);
    }
    return a.join('');
}
function h$jsstringIntersperse(ch, ys) {
                                                          ;
    var i = 0, l = ys.length, j = 0, a = [], ych;
    if(((ch)>=0x10000)) {
 while(j < l) {
     if(i) a[i++] = ch;
     ych = ys.charCodeAt(j++);
     a[i++] = ych;
     if(((ych|1023)===0xDBFF)) a[i++] = ys.charCodeAt(j++);
 }
    } else {
 while(j < l) {
     if(i) a[i++] = ch;
     ych = ys.charCodeAt(j++);
     a[i++] = ych;
     if(((ych|1023)===0xDBFF)) a[i++] = ys.charCodeAt(j++);
 }
    }
    return h$jsstringConvertArray(a);
}
function h$jsstringConcat(xs) {
                            ;
    var a = [], i = 0;
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 a[i++] = ((((xs).d1)).d1);
 xs = ((xs).d2);
    }
    return a.join('');
}
var h$jsstringStripPrefix, h$jsstringStripSuffix,
    h$jsstringIsPrefixOf, h$jsstringIsSuffixOf,
    h$jsstringIsInfixOf;
if(String.prototype.startsWith) {
    h$jsstringStripPrefix = function(p, x) {
                                                                    ;
 if(x.startsWith(p)) {
     return (h$c1(h$ghczminternalZCGHCziInternalziMaybeziJust_con_e, ((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x.substr(p.length)))))));
 } else {
     return h$ghczminternalZCGHCziInternalziMaybeziNothing;
 }
    }
    h$jsstringIsPrefixOf = function(p, x) {
                                                                   ;
 return x.startsWith(p);
    }
} else {
    h$jsstringStripPrefix = function(p, x) {
                                                                       ;
 if(x.indexOf(p) === 0) { // this has worse complexity than it should
     return (h$c1(h$ghczminternalZCGHCziInternalziMaybeziJust_con_e, ((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x.substr(p.length)))))));
 } else {
   return h$ghczminternalZCGHCziInternalziMaybeziNothing;
 }
    }
    h$jsstringIsPrefixOf = function(p, x) {
                                                                      ;
 return x.indexOf(p) === 0; // this has worse complexity than it should
    }
}
if(String.prototype.endsWith) {
    h$jsstringStripSuffix = function(s, x) {
                                                                  ;
 if(x.endsWith(s)) {
     return (h$c1(h$ghczminternalZCGHCziInternalziMaybeziJust_con_e, ((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x.substr(0,x.length-s.length)))))));
 } else {
   return h$ghczminternalZCGHCziInternalziMaybeziNothing;
 }
    }
    h$jsstringIsSuffixOf = function(s, x) {
                                                                 ;
 return x.endsWith(s);
    }
} else {
    h$jsstringStripSuffix = function(s, x) {
                                                                     ;
 var i = x.lastIndexOf(s); // this has worse complexity than it should
 var l = x.length - s.length;
 if(i !== -1 && i === l) {
     return (h$c1(h$ghczminternalZCGHCziInternalziMaybeziJust_con_e, ((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x.substr(0,l)))))));
 } else {
   return h$ghczminternalZCGHCziInternalziMaybeziNothing;
 }
    }
      h$jsstringIsSuffixOf = function(s, x) {
                                                                    ;
        var i = x.lastIndexOf(s); // this has worse complexity than it should
 return i !== -1 && i === x.length - s.length;
    }
}
if(String.prototype.includes) {
    h$jsstringIsInfixOf = function(i, x) {
                                                                       ;
 return x.includes(i);
    }
} else {
    h$jsstringIsInfixOf = function(i, x) {
                                                                          ;
 return x.indexOf(i) !== -1; // this has worse complexity than it should
    }
}
function h$jsstringCommonPrefixes(x, y) {
                                                             ;
    var lx = x.length, ly = y.length, i = 0, cx;
    var l = lx <= ly ? lx : ly;
    if(lx === 0 || ly === 0 || x.charCodeAt(0) !== y.charCodeAt(0)) {
      return h$ghczminternalZCGHCziInternalziMaybeziNothing;
    }
    while(++i<l) {
 cx = x.charCodeAt(i);
 if(cx !== y.charCodeAt(i)) {
     if(((cx|1023)===0xDFFF)) i--;
     break;
 }
    }
  if(i===0) return h$ghczminternalZCGHCziInternalziMaybeziNothing;
    return (h$c1(h$ghczminternalZCGHCziInternalziMaybeziJust_con_e, ((h$c3(h$ghczmprimZCGHCziTupleziZ3T_con_e,((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, ((i===lx)?x:((i===ly)?y:x.substr(0,i)))))),((i===lx) ? h$jsstringEmpty : (h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x.substr(i))))),((i===ly) ? h$jsstringEmpty : (h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (y.substr(i))))))))));
}
function h$jsstringBreakOn(b, x) {
                                                      ;
    var i = x.indexOf(b);
    if(i===-1) {
        { h$ret1 = (""); return (x); };
    }
    if(i===0) {
        { h$ret1 = (x); return (""); };
    }
    { h$ret1 = (x.substr(i)); return (x.substr(0,i)); };
}
function h$jsstringBreakOnEnd(b, x) {
                                                         ;
    var i = x.lastIndexOf(b);
  if(i===-1) {
    { h$ret1 = (x); return (""); };
    }
  i += b.length;
    { h$ret1 = (x.substr(i)); return (x.substr(0,i)); };
}
function h$jsstringBreakOnAll1(n, b, x) {
                                                                    ;
    var i = x.indexOf(b, n);
    if(i===0) {
       { h$ret1 = (""); h$ret2 = (x); return (b.length); };
    }
    if(i===-1) {
       { h$ret1 = (null); h$ret2 = (null); return (-1); };
    }
    { h$ret1 = (x.substr(0,i)); h$ret2 = (x.substr(i)); return (i+b.length); };
}
function h$jsstringBreakOnAll(pat, src) {
                                ;
    var a = [], i = 0, n = 0, r = h$ghczmprimZCGHCziTypesziZMZN, pl = pat.length;
    while(true) {
 var x = src.indexOf(pat, n);
 if(x === -1) break;
 a[i++] = (h$c2(h$ghczmprimZCGHCziTupleziZ2T_con_e,((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (src.substr(0,x))))),((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (src.substr(x)))))));
 n = x + pl;
    }
    while(--i >= 0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (a[i]), (r)));
    return r;
}
function h$jsstringSplitOn1(n, p, x) {
                                                                 ;
    var i = x.indexOf(p, n);
    if(i === -1) {
        { h$ret1 = (null); return (-1); };
    }
    var r1 = (i==n) ? "" : x.substr(n, i-n);
    { h$ret1 = (r1); return (i + p.length); };
}
function h$jsstringSplitOn(p, x) {
                                                      ;
    var a = x.split(p);
    var r = h$ghczmprimZCGHCziTypesziZMZN, i = a.length;
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (a[i])))), (r)));
    return r;
}
// returns -1 for end of input, start of next token otherwise
// word in h$ret1
// this function assumes that there are no whitespace characters >= 0x10000
function h$jsstringWords1(n, x) {
                                                   ;
    var m = n, s = n, l = x.length;
    if(m >= l) return -1;
    // skip leading spaces
    do {
 if(m >= l) return -1;
    } while(h$isSpace(x.charCodeAt(m++)));
    // found start of word
    s = m - 1;
    while(m < l) {
 if(h$isSpace(x.charCodeAt(m++))) {
     // found end of word
            var r1 = (m-s<=1) ? "" : x.substr(s,m-s-1);
            { h$ret1 = (r1); return (m); };
 }
    }
    // end of string
    if(s < l) {
        var r1 = s === 0 ? x : x.substr(s);
        { h$ret1 = (r1); return (m); };
    }
    { h$ret1 = (null); return (-1); };
}
function h$jsstringWords(x) {
                                        ;
    var a = null, i = 0, n, s = -1, m = 0, w, l = x.length, r = h$ghczmprimZCGHCziTypesziZMZN;
    outer:
    while(m < l) {
 // skip leading spaces
 do {
     if(m >= l) { s = m; break outer; }
 } while(h$isSpace(x.charCodeAt(m++)));
 // found start of word
 s = m - 1;
 while(m < l) {
     if(h$isSpace(x.charCodeAt(m++))) {
  // found end of word
  w = (m-s<=1) ? h$jsstringEmpty
                             : (h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x.substr(s,m-s-1))));
  if(i) a[i++] = w; else { a = [w]; i = 1; }
  s = m;
  break;
     }
 }
    }
    // end of string
    if(s !== -1 && s < l) {
 w = (h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (s === 0 ? x : x.substr(s))));
 if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    // build resulting list
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (a[i]), (r)));
    return r;
}
// returns -1 for end of input, start of next token otherwise
// line in h$ret1
function h$jsstringLines1(n, x) {
                                                   ;
    var m = n, l = x.length;
    if(n >= l) return -1;
    while(m < l) {
 if(x.charCodeAt(m++) === 10) {
     // found newline
     if(n > 0 && n === l-1) return -1; // it was the last character
            var r1 = (m-n<=1) ? "" : x.substr(n,m-n-1);
            { h$ret1 = (r1); return (m); };
 }
    }
    // end of string
    { h$ret1 = (x.substr(n)); return (m); };
}
function h$jsstringLines(x) {
                                        ;
    var a = null, m = 0, i = 0, l = x.length, s = 0, r = h$ghczmprimZCGHCziTypesziZMZN, w;
    if(l === 0) return h$ghczmprimZCGHCziTypesziZMZN;
    outer:
    while(true) {
 s = m;
 do {
     if(m >= l) break outer;
 } while(x.charCodeAt(m++) !== 10);
 w = (m-s<=1) ? h$jsstringEmpty : (h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x.substr(s,m-s-1))));
 if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    if(s < l) {
 w = (h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x.substr(s))));
 if(i) a[i++] = w; else { a = [w]; i = 1; }
    }
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (a[i]), (r)));
    return r;
}
function h$jsstringGroup(x) {
                                        ;
    var xl = x.length;
    if(xl === 0) return h$ghczmprimZCGHCziTypesziZMZN;
    var i = xl-1, si, ch, s=xl, r=h$ghczmprimZCGHCziTypesziZMZN;
    var tch = x.charCodeAt(i--);
    if(((tch|1023)===0xDFFF)) tch = ((((x.charCodeAt(i--))-0xD800)<<10)+(tch)-0xDC00+0x10000);
    while(i >= 0) {
 si = i;
 ch = x.charCodeAt(i--);
 if(((ch|1023)===0xDFFF)) {
     ch = ((((x.charCodeAt(i--))-0xD800)<<10)+(ch)-0xDC00+0x10000);
 }
 if(ch != tch) {
     tch = ch;
     r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x.substr(si+1,s-si))))), (r)));
     s = si;
 }
    }
    return (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x.substr(0,s+1))))), (r)));
}
function h$jsstringChunksOf1(n, s, x) {
                                                                ;
    var m = s, c = 0, l = x.length, ch;
    if(n <= 0 || l === 0 || s >= l) return -1
    while(++m < l) {
        ch = x.charCodeAt(m - 1);
        if(((ch|1023)===0xDBFF)) ++m;
        if(++c >= n) break;
    }
    var r1 = (m >= l && s === c) ? x : x.substr(s,m-s);
    { h$ret1 = (r1); return (m); };
}
function h$jsstringChunksOf(n, x) {
                                                     ;
    var l = x.length;
    if(l===0 || n <= 0) return h$ghczmprimZCGHCziTypesziZMZN;
    if(l <= n) return (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (x)))), (h$ghczmprimZCGHCziTypesziZMZN)));
    var a = [], i = 0, s = 0, ch, m = 0, c, r = h$ghczmprimZCGHCziTypesziZMZN;
    while(m < l) {
 s = m;
 c = 0;
 while(m < l && ++c <= n) {
     ch = x.charCodeAt(m++);
     if(((ch|1023)===0xDBFF)) ++m;
 }
 if(c) a[i++] = x.substr(s, m-s);
    }
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (a[i])))), (r)));
    return r;
}
function h$jsstringCount(pat, src) {
                                                        ;
    var i = 0, n = 0, pl = pat.length, sl = src.length;
    while(i<sl) {
 i = src.indexOf(pat, i);
 if(i===-1) break;
 n++;
 i += pl;
    }
    return n;
}
function h$jsstringReplicate(n, str) {
                                                        ;
    if(n === 0 || str == '') return '';
    if(n === 1) return str;
    var r = '';
    do {
 if(n&1) r+=str;
        str+=str;
        n >>= 1;
    } while(n > 1);
    return r+str;
}
// this does not deal with combining diacritics, Data.Text does not either
var h$jsstringReverse;
if(Array.from) {
    h$jsstringReverse = function(str) {
                                                      ;
 return Array.from(str).reverse().join('');
    }
} else {
    h$jsstringReverse = function(str) {
                                                         ;
 var l = str.length, a = [], o = 0, i = 0, c, c1, s = '';
 while(i < l) {
     c = str.charCodeAt(i);
     if(((c|1023)===0xDBFF)) {
  a[i] = str.charCodeAt(i+1);
  a[i+1] = c;
  i += 2;
     } else a[i++] = c;
     if(i-o > 60000) {
  s = String.fromCharCode.apply(null, a.reverse()) + s;
  o = -i;
  a = [];
     }
 }
 return (i===0) ? s : String.fromCharCode.apply(null,a.reverse()) + s;
    }
}
function h$jsstringUnpack(str) {
                                           ;
    var r = h$ghczmprimZCGHCziTypesziZMZN, i = str.length-1, c;
    while(i >= 0) {
 c = str.charCodeAt(i--);
 if(((c|1023)===0xDFFF)) c = ((((str.charCodeAt(i--))-0xD800)<<10)+(c)-0xDC00+0x10000)
 r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, (c), (r)));
    }
    return r;
}
function h$jsstringDecBigNat(positive,x) {
                             ;
  const y = BigInt("0x" + h$jsstringHexBigNat(positive,x)).toString();
  return positive ? y : "-"+y;
}
function h$jsstringDecI64(hi,lo) {
                                              ;
    var lo0 = (lo < 0) ? lo+4294967296:lo;
    if(hi < 0) {
 if(hi === -1) return ''+(lo0-4294967296);
 lo0 = 4294967296 - lo0;
 var hi0 = -1 - hi;
 var x0 = hi0 * 967296;
 var x1 = (lo0 + x0) % 1000000;
 var x2 = hi0*4294+Math.floor((x0+lo0-x1)/1000000);
 return '-' + x2 + h$jsstringDecIPadded6(x1);
    } else {
 if(hi === 0) return ''+lo0;
 var x0 = hi * 967296;
 var x1 = (lo0 + x0) % 1000000;
 var x2 = hi*4294+Math.floor((x0+lo0-x1)/1000000);
 return '' + x2 + h$jsstringDecIPadded6(x1);
    }
}
function h$jsstringDecW64(hi,lo) {
                                              ;
    var lo0 = (lo < 0) ? lo+4294967296 : lo;
    if(hi === 0) return ''+lo0;
    var hi0 = (hi < 0) ? hi+4294967296 : hi;
    var x0 = hi0 * 967296;
    var x1 = (lo0 + x0) % 1000000;
    var x2 = hi0*4294+Math.floor((x0+lo0-x1)/1000000);
    return '' + x2 + h$jsstringDecIPadded6(x1);
}
function h$jsstringHexBigNat(positive,x) {
                             ;
  var v = "";
  var i = x.u1.length - 1;
  while (i >= 0) {
    if (x.u1[i] !== 0) {
      break;
    } else {
      i--;
    }
  }
  if (i >= 0) {
    v += x.u1[i].toString(16);
    i--;
  }
  for (; i >= 0; i--) {
    v += x.u1[i].toString(16).padStart(4, '0');
  }
  return positive ? v : "-"+v;
}
function h$jsstringHexI64(hi,lo) {
                                              ;
    var sign = (hi >>> 31) ? '-' : '';
    // unsigned right bitshift by zero to convert to UInt32
    var lo0 = sign ? ~(lo - 1) >>> 0 : lo;
    if(hi === 0 || hi === -1) return sign + lo0.toString(16);
    var hi0 = sign ? ~hi >>> 0 : hi;
    return sign + hi0.toString(16) + lo0.toString(16).padStart(8, '0');
}
function h$jsstringHexW64(hi,lo) {
    if (hi === 0) return lo.toString(16);
    return hi.toString(16) + lo.toString(16).padStart(8, '0');
}
// n in [0, 1000000000)
function h$jsstringDecIPadded9(n) {
                                       ;
    if(n === 0) return '000000000';
    var pad = (n>=100000000)?'':
              (n>=10000000)?'0':
              (n>=1000000)?'00':
              (n>=100000)?'000':
              (n>=10000)?'0000':
              (n>=1000)?'00000':
              (n>=100)?'000000':
              (n>=10)?'0000000':
                     '00000000';
    return pad+n;
}
// n in [0, 1000000)
function h$jsstringDecIPadded6(n) {
                                       ;
    if(n === 0) return '000000';
    var pad = (n>=100000)?'':
              (n>=10000)?'0':
              (n>=1000)?'00':
              (n>=100)?'000':
              (n>=10)?'0000':
                     '00000';
    return pad+n;
}
// n in [0, 2147483648)
function h$jsstringHexIPadded8(n) {
                                       ;
   if(n === 0) return '00000000';
   var pad = (n>=0x10000000)?'':
             (n>=0x1000000)?'0':
             (n>=0x100000)?'00':
             (n>=0x10000)?'000':
             (n>=0x1000)?'0000':
             (n>=0x100)?'00000':
             (n>=0x10)?'000000':
                      '0000000';
    return pad+n.toString(16);
}
function h$jsstringZeroes(n) {
    var r;
    switch(n&7) {
 case 0: r = ''; break;
 case 1: r = '0'; break;
 case 2: r = '00'; break;
 case 3: r = '000'; break;
 case 4: r = '0000'; break;
 case 5: r = '00000'; break;
 case 6: r = '000000'; break;
 case 7: r = '0000000';
    }
    for(var i=n>>3;i>0;i--) r = r + '00000000';
    return r;
}
function h$jsstringDoubleToFixed(decs, d) {
    if(decs >= 0) {
 if(Math.abs(d) < 1e21) {
     var r = d.toFixed(Math.min(20,decs));
     if(decs > 20) r = r + h$jsstringZeroes(decs-20);
     return r;
 } else {
     var r = d.toExponential();
     var ei = r.indexOf('e');
     var di = r.indexOf('.');
     var e = parseInt(r.substr(ei+1));
     return r.substring(0,di) + r.substring(di,ei) + h$jsstringZeroes(di-ei+e) +
                   ((decs > 0) ? ('.' + h$jsstringZeroes(decs)) : '');
 }
    }
    var r = Math.abs(d).toExponential();
    var ei = r.indexOf('e');
    var e = parseInt(r.substr(ei+1));
    var m = d < 0 ? '-' : '';
    r = r.substr(0,1) + r.substring(2,ei);
    if(e >= 0) {
 return (e > r.length) ? m + r + h$jsstringZeroes(r.length-e-1) + '.0'
                       : m + r.substr(0,e+1) + '.' + r.substr(e+1);
    } else {
 return m + '0.' + h$jsstringZeroes(-e-1) + r;
    }
}
function h$jsstringDoubleToExponent(decs, d) {
    var r;
    if(decs ===-1) {
 r = d.toExponential().replace('+','');
    } else {
 r = d.toExponential(Math.max(1, Math.min(20,decs))).replace('+','');
    }
    if(r.indexOf('.') === -1) {
 r = r.replace('e', '.0e');
    }
    if(decs > 20) r = r.replace('e', h$jsstringZeroes(decs-20)+'e');
    return r;
}
function h$jsstringDoubleGeneric(decs, d) {
    var r;
    if(decs === -1) {
 r = d.toString(10).replace('+','');
    } else {
 r = d.toPrecision(Math.max(decs+1,1)).replace('+','');
    }
    if(decs !== 0 && r.indexOf('.') === -1) {
 if(r.indexOf('e') !== -1) {
     r = r.replace('e', '.0e');
 } else {
     r = r + '.0';
 }
    }
    return r;
}
function h$jsstringAppend(x, y) {
                                                     ;
    return x+y;
}
function h$jsstringCompare(x, y) {
                                                      ;
    return (x<y)?-1:((x>y)?1:0);
}
function h$jsstringUnlines(xs) {
    var r = '';
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 r = r + ((((xs).d1)).d1) + '\n';
 xs = ((xs).d2);
    }
    return r;
}
function h$jsstringUnwords(xs) {
    if(((xs).f === h$ghczmprimZCGHCziTypesziZMZN_con_e)) return '';
    var r = ((((xs).d1)).d1);
    xs = ((xs).d2);
    while(((xs).f === h$ghczmprimZCGHCziTypesziZC_con_e)) {
 r = r + ' ' + ((((xs).d1)).d1);
 xs = ((xs).d2);
    }
    return r;
}
function h$jsstringReplace(pat, rep, src) {
                                                                        ;
    var r = src.replace(pat, rep, 'g');
    // the 'g' flag is not supported everywhere, check and fall back if necessary
    if(r.indexOf(pat) !== -1) {
 r = src.split(pat).join(rep);
    }
    return r;
}
function h$jsstringReplicateChar(n, ch) {
                                                    ;
    return h$jsstringReplicate(n, h$jsstringSingleton(ch));
}
function h$jsstringIsInteger(str) {
    return /^-?\d+$/.test(str);
}
function h$jsstringIsNatural(str) {
    return /^\d+$/.test(str);
}
function h$jsstringReadInt(str) {
    if(!/^-?\d+/.test(str)) return null;
    var x = parseInt(str, 10);
    var x0 = x|0;
    return (x===x0) ? x0 : null;
}
function h$jsstringLenientReadInt(str) {
    var x = parseInt(str, 10);
    var x0 = x|0;
    return (x===x0) ? x0 : null;
}
function h$jsstringReadWord(str) {
  if(!/^\d+/.test(str)) return null;
  var x = parseInt(str, 10);
  var x0 = x|0;
  if(x0<0) return (x===x0+2147483648) ? x0 : null;
  else return (x===x0) ? x0 : null;
}
function h$jsstringReadDouble(str) {
    return parseFloat(str, 10);
}
function h$jsstringLenientReadDouble(str) {
    return parseFloat(str, 10);
}
function h$jsstringReadInteger(str) {
                                       ;
  if(!/^(-)?\d+$/.test(str)) {
    return null;
  } else if(str.length <= 9) {
    return MK_INTEGER_S(parseInt(str, 10));
  } else {
    return h$ghcjsbn_readInteger(str);
  }
}
function h$jsstringReadInt64(str) {
  if(!/^(-)?\d+$/.test(str)) {
      { h$ret1 = (0); h$ret2 = (0); return (0); };
  }
  if(str.charCodeAt(0) === 45) { // '-'
    return h$jsstringReadValue64(str, 1, true);
  } else {
    return h$jsstringReadValue64(str, 0, false);
  }
}
function h$jsstringReadWord64(str) {
  if(!/^\d+$/.test(str)) {
    { h$ret1 = (0); h$ret2 = (0); return (0); };
  }
  return h$jsstringReadValue64(str, 0, false);
}
var h$jsstringLongs = null;
function h$jsstringReadValue64(str, start, negate) {
  var l = str.length, i = start;
  while(i < l) {
    if(str.charCodeAt(i) !== 48) break;
    i++;
  }
  if(i >= l) { h$ret1 = (0); h$ret2 = (0); return (1); }; // only zeroes
  if(h$jsstringLongs === null) {
    h$jsstringLongs = [];
    for(var t=10; t<=1000000000; t*=10) {
      h$jsstringLongs.push(goog.math.Long.fromInt(t));
    }
  }
  var li = l-i;
  if(li < 10 && !negate) {
    { h$ret1 = (0); h$ret2 = (parseInt(str.substr(i), 10)); return (1); };
  }
  var r = goog.math.Long.fromInt(parseInt(str.substr(li,9),10));
  li += 9;
  while(li < l) {
    r = r.multiply(h$jsstringLongs[Math.min(l-li-1,8)])
         .add(goog.math.Long.fromInt(parseInt(str.substr(li,9), 10)));
    li += 9;
  }
  if(negate) {
    r = r.negate();
  }
  { h$ret1 = (r.getHighBits()); h$ret2 = (r.getLowBits()); return (1); };
}
function h$jsstringExecRE(i, str, re) {
    re.lastIndex = i;
    var m = re.exec(str);
    if(m === null) return -1;
    var a = [], x, j = 1, r = h$ghczmprimZCGHCziTypesziZMZN;
    while(true) {
 x = m[j];
 if(typeof x === 'undefined') break;
 a[j-1] = x;
 j++;
    }
    j-=1;
    while(--j>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (a[j])))), (r)));
    { h$ret1 = (m[0]); h$ret2 = (r); return (m.index); };
}
function h$jsstringReplaceRE(pat, replacement, str) {
    return str.replace(pat, replacement);
}
function h$jsstringSplitRE(limit, re, str) {
    re.lastIndex = i;
    var s = (limit < 0) ? str.split(re) : str.split(re, limit);
    var i = s.length, r = h$ghczmprimZCGHCziTypesziZMZN;
    while(--i>=0) r = (h$c2(h$ghczmprimZCGHCziTypesziZC_con_e, ((h$c1(h$ghczminternalZCGHCziInternalziJSziPrimziJSVal_con_e, (a[i])))), (r)));
    return r;
}
function h$jsstringIndices(needle, startN, startI, haystack) {
    var endI = haystack.indexOf(needle, startI);
    if (endI === -1) {
        { h$ret1 = (-1); return (-1); };
    }
    var n = startN;
    for (var i = startI; i < endI; i++) {
        if (!((haystack.charCodeAt(i)|1023)===0xDFFF)) {
     n++;
 }
    }
    { h$ret1 = (endI); return (n); };
}

