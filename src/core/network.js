/* Copyright 2012 Mozilla Foundation
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

// NOTE: Be careful what goes in this file, as it is also used from the context
// of the addon. So using warn/error in here will break the addon.

'use strict';

//#if (FIREFOX || MOZCENTRAL)
//
//Components.utils.import('resource://gre/modules/Services.jsm');
//
//var EXPORTED_SYMBOLS = ['NetworkManager'];
//
//var console = {
//  log: function console_log(aMsg) {
//    var msg = 'network.js: ' + (aMsg.join ? aMsg.join('') : aMsg);
//    Services.console.logStringMessage(msg);
//    // TODO(mack): dump() doesn't seem to work here...
//    dump(msg + '\n');
//  }
//}
//#endif

/*
 * JavaScript MD5
 * https://github.com/blueimp/JavaScript-MD5
 *
 * Copyright 2011, Sebastian Tschan
 * https://blueimp.net
 *
 * Licensed under the MIT license:
 * http://www.opensource.org/licenses/MIT
 *
 * Based on
 * A JavaScript implementation of the RSA Data Security, Inc. MD5 Message
 * Digest Algorithm, as defined in RFC 1321.
 * Version 2.2 Copyright (C) Paul Johnston 1999 - 2009
 * Other contributors: Greg Holt, Andrew Kepert, Ydnar, Lostinet
 * Distributed under the BSD License
 * See http://pajhome.org.uk/crypt/md5 for more info.
 */

/*global unescape, define, module */

var md5 = (function () {
  /*
   * Add integers, wrapping at 2^32. This uses 16-bit operations internally
   * to work around bugs in some JS interpreters.
   */
  function safe_add (x, y) {
    var lsw = (x & 0xFFFF) + (y & 0xFFFF)
    var msw = (x >> 16) + (y >> 16) + (lsw >> 16)
    return (msw << 16) | (lsw & 0xFFFF)
  }

  /*
   * Bitwise rotate a 32-bit number to the left.
   */
  function bit_rol (num, cnt) {
    return (num << cnt) | (num >>> (32 - cnt))
  }

  /*
   * These functions implement the four basic operations the algorithm uses.
   */
  function md5_cmn (q, a, b, x, s, t) {
    return safe_add(bit_rol(safe_add(safe_add(a, q), safe_add(x, t)), s), b)
  }
  function md5_ff (a, b, c, d, x, s, t) {
    return md5_cmn((b & c) | ((~b) & d), a, b, x, s, t)
  }
  function md5_gg (a, b, c, d, x, s, t) {
    return md5_cmn((b & d) | (c & (~d)), a, b, x, s, t)
  }
  function md5_hh (a, b, c, d, x, s, t) {
    return md5_cmn(b ^ c ^ d, a, b, x, s, t)
  }
  function md5_ii (a, b, c, d, x, s, t) {
    return md5_cmn(c ^ (b | (~d)), a, b, x, s, t)
  }

  /*
   * Calculate the MD5 of an array of little-endian words, and a bit length.
   */
  function binl_md5 (x, len) {
    /* append padding */
    x[len >> 5] |= 0x80 << (len % 32)
    x[(((len + 64) >>> 9) << 4) + 14] = len

    var i
    var olda
    var oldb
    var oldc
    var oldd
    var a = 1732584193
    var b = -271733879
    var c = -1732584194
    var d = 271733878

    for (i = 0; i < x.length; i += 16) {
      olda = a
      oldb = b
      oldc = c
      oldd = d

      a = md5_ff(a, b, c, d, x[i], 7, -680876936)
      d = md5_ff(d, a, b, c, x[i + 1], 12, -389564586)
      c = md5_ff(c, d, a, b, x[i + 2], 17, 606105819)
      b = md5_ff(b, c, d, a, x[i + 3], 22, -1044525330)
      a = md5_ff(a, b, c, d, x[i + 4], 7, -176418897)
      d = md5_ff(d, a, b, c, x[i + 5], 12, 1200080426)
      c = md5_ff(c, d, a, b, x[i + 6], 17, -1473231341)
      b = md5_ff(b, c, d, a, x[i + 7], 22, -45705983)
      a = md5_ff(a, b, c, d, x[i + 8], 7, 1770035416)
      d = md5_ff(d, a, b, c, x[i + 9], 12, -1958414417)
      c = md5_ff(c, d, a, b, x[i + 10], 17, -42063)
      b = md5_ff(b, c, d, a, x[i + 11], 22, -1990404162)
      a = md5_ff(a, b, c, d, x[i + 12], 7, 1804603682)
      d = md5_ff(d, a, b, c, x[i + 13], 12, -40341101)
      c = md5_ff(c, d, a, b, x[i + 14], 17, -1502002290)
      b = md5_ff(b, c, d, a, x[i + 15], 22, 1236535329)

      a = md5_gg(a, b, c, d, x[i + 1], 5, -165796510)
      d = md5_gg(d, a, b, c, x[i + 6], 9, -1069501632)
      c = md5_gg(c, d, a, b, x[i + 11], 14, 643717713)
      b = md5_gg(b, c, d, a, x[i], 20, -373897302)
      a = md5_gg(a, b, c, d, x[i + 5], 5, -701558691)
      d = md5_gg(d, a, b, c, x[i + 10], 9, 38016083)
      c = md5_gg(c, d, a, b, x[i + 15], 14, -660478335)
      b = md5_gg(b, c, d, a, x[i + 4], 20, -405537848)
      a = md5_gg(a, b, c, d, x[i + 9], 5, 568446438)
      d = md5_gg(d, a, b, c, x[i + 14], 9, -1019803690)
      c = md5_gg(c, d, a, b, x[i + 3], 14, -187363961)
      b = md5_gg(b, c, d, a, x[i + 8], 20, 1163531501)
      a = md5_gg(a, b, c, d, x[i + 13], 5, -1444681467)
      d = md5_gg(d, a, b, c, x[i + 2], 9, -51403784)
      c = md5_gg(c, d, a, b, x[i + 7], 14, 1735328473)
      b = md5_gg(b, c, d, a, x[i + 12], 20, -1926607734)

      a = md5_hh(a, b, c, d, x[i + 5], 4, -378558)
      d = md5_hh(d, a, b, c, x[i + 8], 11, -2022574463)
      c = md5_hh(c, d, a, b, x[i + 11], 16, 1839030562)
      b = md5_hh(b, c, d, a, x[i + 14], 23, -35309556)
      a = md5_hh(a, b, c, d, x[i + 1], 4, -1530992060)
      d = md5_hh(d, a, b, c, x[i + 4], 11, 1272893353)
      c = md5_hh(c, d, a, b, x[i + 7], 16, -155497632)
      b = md5_hh(b, c, d, a, x[i + 10], 23, -1094730640)
      a = md5_hh(a, b, c, d, x[i + 13], 4, 681279174)
      d = md5_hh(d, a, b, c, x[i], 11, -358537222)
      c = md5_hh(c, d, a, b, x[i + 3], 16, -722521979)
      b = md5_hh(b, c, d, a, x[i + 6], 23, 76029189)
      a = md5_hh(a, b, c, d, x[i + 9], 4, -640364487)
      d = md5_hh(d, a, b, c, x[i + 12], 11, -421815835)
      c = md5_hh(c, d, a, b, x[i + 15], 16, 530742520)
      b = md5_hh(b, c, d, a, x[i + 2], 23, -995338651)

      a = md5_ii(a, b, c, d, x[i], 6, -198630844)
      d = md5_ii(d, a, b, c, x[i + 7], 10, 1126891415)
      c = md5_ii(c, d, a, b, x[i + 14], 15, -1416354905)
      b = md5_ii(b, c, d, a, x[i + 5], 21, -57434055)
      a = md5_ii(a, b, c, d, x[i + 12], 6, 1700485571)
      d = md5_ii(d, a, b, c, x[i + 3], 10, -1894986606)
      c = md5_ii(c, d, a, b, x[i + 10], 15, -1051523)
      b = md5_ii(b, c, d, a, x[i + 1], 21, -2054922799)
      a = md5_ii(a, b, c, d, x[i + 8], 6, 1873313359)
      d = md5_ii(d, a, b, c, x[i + 15], 10, -30611744)
      c = md5_ii(c, d, a, b, x[i + 6], 15, -1560198380)
      b = md5_ii(b, c, d, a, x[i + 13], 21, 1309151649)
      a = md5_ii(a, b, c, d, x[i + 4], 6, -145523070)
      d = md5_ii(d, a, b, c, x[i + 11], 10, -1120210379)
      c = md5_ii(c, d, a, b, x[i + 2], 15, 718787259)
      b = md5_ii(b, c, d, a, x[i + 9], 21, -343485551)

      a = safe_add(a, olda)
      b = safe_add(b, oldb)
      c = safe_add(c, oldc)
      d = safe_add(d, oldd)
    }
    return [a, b, c, d]
  }

  /*
   * Convert an array of little-endian words to a string
   */
  function binl2rstr (input) {
    var i
    var output = ''
    for (i = 0; i < input.length * 32; i += 8) {
      output += String.fromCharCode((input[i >> 5] >>> (i % 32)) & 0xFF)
    }
    return output
  }

  /*
   * Convert a raw string to an array of little-endian words
   * Characters >255 have their high-byte silently ignored.
   */
  function rstr2binl (input) {
    var i
    var output = []
    output[(input.length >> 2) - 1] = undefined
    for (i = 0; i < output.length; i += 1) {
      output[i] = 0
    }
    for (i = 0; i < input.length * 8; i += 8) {
      output[i >> 5] |= (input.charCodeAt(i / 8) & 0xFF) << (i % 32)
    }
    return output
  }

  /*
   * Calculate the MD5 of a raw string
   */
  function rstr_md5 (s) {
    return binl2rstr(binl_md5(rstr2binl(s), s.length * 8))
  }

  /*
   * Calculate the HMAC-MD5, of a key and some data (raw strings)
   */
  function rstr_hmac_md5 (key, data) {
    var i
    var bkey = rstr2binl(key)
    var ipad = []
    var opad = []
    var hash
    ipad[15] = opad[15] = undefined
    if (bkey.length > 16) {
      bkey = binl_md5(bkey, key.length * 8)
    }
    for (i = 0; i < 16; i += 1) {
      ipad[i] = bkey[i] ^ 0x36363636
      opad[i] = bkey[i] ^ 0x5C5C5C5C
    }
    hash = binl_md5(ipad.concat(rstr2binl(data)), 512 + data.length * 8)
    return binl2rstr(binl_md5(opad.concat(hash), 512 + 128))
  }

  /*
   * Convert a raw string to a hex string
   */
  function rstr2hex (input) {
    var hex_tab = '0123456789abcdef'
    var output = ''
    var x
    var i
    for (i = 0; i < input.length; i += 1) {
      x = input.charCodeAt(i)
      output += hex_tab.charAt((x >>> 4) & 0x0F) +
        hex_tab.charAt(x & 0x0F)
    }
    return output
  }

  /*
   * Encode a string as utf-8
   */
  function str2rstr_utf8 (input) {
    return unescape(encodeURIComponent(input))
  }

  /*
   * Take string arguments and return either raw or hex encoded strings
   */
  function raw_md5 (s) {
    return rstr_md5(str2rstr_utf8(s))
  }
  function hex_md5 (s) {
    return rstr2hex(raw_md5(s))
  }
  function raw_hmac_md5 (k, d) {
    return rstr_hmac_md5(str2rstr_utf8(k), str2rstr_utf8(d))
  }
  function hex_hmac_md5 (k, d) {
    return rstr2hex(raw_hmac_md5(k, d))
  }

  return function md5 (string, key, raw) {
    if (!key) {
      if (!raw) {
        return hex_md5(string)
      }
      return raw_md5(string)
    }
    if (!raw) {
      return hex_hmac_md5(key, string)
    }
    return raw_hmac_md5(key, string)
  };
}());

var NetworkManager = (function NetworkManagerClosure() {

  var OK_RESPONSE = 200;
  var PARTIAL_CONTENT_RESPONSE = 206;

  function NetworkManager(url, args) {
    this.url = url;
    args = args || {};
    this.isHttp = /^https?:/i.test(url);
    this.httpHeaders = (this.isHttp && args.httpHeaders) || {};
    this.withCredentials = args.withCredentials || false;
    this.getXhr = args.getXhr ||
      function NetworkManager_getXhr() {
        return new XMLHttpRequest();
      };

    this.currXhrId = 0;
    this.pendingRequests = Object.create(null);
    this.loadedRequests = Object.create(null);
  }

  function getArrayBuffer(xhr) {
    var data = xhr.response;
    if (typeof data !== 'string') {
      return data;
    }
    var length = data.length;
    var array = new Uint8Array(length);
    for (var i = 0; i < length; i++) {
      array[i] = data.charCodeAt(i) & 0xFF;
    }
    return array.buffer;
  }

//#if !(CHROME || FIREFOX || MOZCENTRAL)
  var supportsMozChunked = (function supportsMozChunkedClosure() {
    try {
      var x = new XMLHttpRequest();
      // Firefox 37- required .open() to be called before setting responseType.
      // https://bugzilla.mozilla.org/show_bug.cgi?id=707484
      // Even though the URL is not visited, .open() could fail if the URL is
      // blocked, e.g. via the connect-src CSP directive or the NoScript addon.
      // When this error occurs, this feature detection method will mistakenly
      // report that moz-chunked-arraybuffer is not supported in Firefox 37-.
      x.open('GET', 'https://example.com');
      x.responseType = 'moz-chunked-arraybuffer';
      return x.responseType === 'moz-chunked-arraybuffer';
    } catch (e) {
      return false;
    }
  })();
//#endif

  NetworkManager.prototype = {
    requestRange: function NetworkManager_requestRange(begin, end, listeners) {
      var args = {
        begin: begin,
        end: end
      };
      for (var prop in listeners) {
        args[prop] = listeners[prop];
      }
      return this.request(args);
    },

    requestFull: function NetworkManager_requestFull(listeners) {
      return this.request(listeners);
    },

    setNonceHeaders: function () {
      if (!this.xNonce) return;

      this.httpHeaders['X-Nonce'] = this.xNonce;
      this.httpHeaders['X-Signature'] = this.getNonceSignature();
    },

    getNonceSignature: function () {
      var key = 'FwwgsVn6rYKe7yyZgNPHqxHKtuddgQRjjFWqckOr6ksK9asp15';
      return md5(key + this.xNonce);
    },

    request: function NetworkManager_request(args) {
      var xhr = this.getXhr();
      var xhrId = this.currXhrId++;
      var pendingRequest = this.pendingRequests[xhrId] = {xhr: xhr};

      xhr.open('GET', this.url);
      xhr.withCredentials = this.withCredentials;

      this.setNonceHeaders();

      for (var property in this.httpHeaders) {
        if (!this.httpHeaders.hasOwnProperty(property)) continue;
        var value = this.httpHeaders[property];
        if (typeof value !== 'undefined') xhr.setRequestHeader(property, value);
      }
      if (this.isHttp && 'begin' in args && 'end' in args) {
        var rangeStr = args.begin + '-' + (args.end - 1);
        xhr.setRequestHeader('Range', 'bytes=' + rangeStr);
        pendingRequest.expectedStatus = 206;
      } else {
        pendingRequest.expectedStatus = 200;
      }

//#if CHROME
//    var useMozChunkedLoading = false;
//#endif
//#if (FIREFOX || MOZCENTRAL)
//    var useMozChunkedLoading = !!args.onProgressiveData;
//#endif
//#if !(CHROME || FIREFOX || MOZCENTRAL)
      var useMozChunkedLoading = supportsMozChunked && !!args.onProgressiveData;
//#endif
      if (useMozChunkedLoading) {
        xhr.responseType = 'moz-chunked-arraybuffer';
        pendingRequest.onProgressiveData = args.onProgressiveData;
        pendingRequest.mozChunked = true;
      } else {
        xhr.responseType = 'arraybuffer';
      }

      if (args.onError) {
        xhr.onerror = function (evt) {
          args.onError(xhr.status);
        };
      }
      xhr.onreadystatechange = this.onStateChange.bind(this, xhrId);
      xhr.onprogress = this.onProgress.bind(this, xhrId);

      pendingRequest.onHeadersReceived = args.onHeadersReceived;
      pendingRequest.onDone = args.onDone;
      pendingRequest.onError = args.onError;
      pendingRequest.onProgress = args.onProgress;

      xhr.send(null);

      return xhrId;
    },

    onProgress: function NetworkManager_onProgress(xhrId, evt) {
      var pendingRequest = this.pendingRequests[xhrId];
      if (!pendingRequest) {
        // Maybe abortRequest was called...
        return;
      }

      if (pendingRequest.mozChunked) {
        var chunk = getArrayBuffer(pendingRequest.xhr);
        pendingRequest.onProgressiveData(chunk);
      }

      var onProgress = pendingRequest.onProgress;
      if (onProgress) {
        onProgress(evt);
      }
    },

    onStateChange: function NetworkManager_onStateChange(xhrId, evt) {
      var pendingRequest = this.pendingRequests[xhrId];
      if (!pendingRequest) {
        // Maybe abortRequest was called...
        return;
      }

      var xhr = pendingRequest.xhr;

      if (!this.xNonce) this.xNonce = xhr.getResponseHeader('X-Nonce');
      this.xNonce = '123';

      if (xhr.readyState >= 2 && pendingRequest.onHeadersReceived) {
        pendingRequest.onHeadersReceived();
        delete pendingRequest.onHeadersReceived;
      }

      if (xhr.readyState !== 4) {
        return;
      }

      if (!(xhrId in this.pendingRequests)) {
        // The XHR request might have been aborted in onHeadersReceived()
        // callback, in which case we should abort request
        return;
      }

      delete this.pendingRequests[xhrId];

      // success status == 0 can be on ftp, file and other protocols
      if (xhr.status === 0 && this.isHttp) {
        if (pendingRequest.onError) {
          pendingRequest.onError(xhr.status);
        }
        return;
      }
      var xhrStatus = xhr.status || OK_RESPONSE;

      // From http://www.w3.org/Protocols/rfc2616/rfc2616-sec14.html#sec14.35.2:
      // "A server MAY ignore the Range header". This means it's possible to
      // get a 200 rather than a 206 response from a range request.
      var ok_response_on_range_request =
        xhrStatus === OK_RESPONSE &&
        pendingRequest.expectedStatus === PARTIAL_CONTENT_RESPONSE;

      if (!ok_response_on_range_request &&
        xhrStatus !== pendingRequest.expectedStatus) {
        if (pendingRequest.onError) {
          pendingRequest.onError(xhr.status);
        }
        return;
      }

      this.loadedRequests[xhrId] = true;

      var chunk = getArrayBuffer(xhr);
      if (xhrStatus === PARTIAL_CONTENT_RESPONSE) {
        var rangeHeader = xhr.getResponseHeader('Content-Range');
        var matches = /bytes (\d+)-(\d+)\/(\d+)/.exec(rangeHeader);
        var begin = parseInt(matches[1], 10);
        pendingRequest.onDone({
          begin: begin,
          chunk: chunk
        });
      } else if (pendingRequest.onProgressiveData) {
        pendingRequest.onDone(null);
      } else if (chunk) {
        pendingRequest.onDone({
          begin: 0,
          chunk: chunk
        });
      } else if (pendingRequest.onError) {
        pendingRequest.onError(xhr.status);
      }
    },

    hasPendingRequests: function NetworkManager_hasPendingRequests() {
      for (var xhrId in this.pendingRequests) {
        return true;
      }
      return false;
    },

    getRequestXhr: function NetworkManager_getXhr(xhrId) {
      return this.pendingRequests[xhrId].xhr;
    },

    isStreamingRequest: function NetworkManager_isStreamingRequest(xhrId) {
      return !!(this.pendingRequests[xhrId].onProgressiveData);
    },

    isPendingRequest: function NetworkManager_isPendingRequest(xhrId) {
      return xhrId in this.pendingRequests;
    },

    isLoadedRequest: function NetworkManager_isLoadedRequest(xhrId) {
      return xhrId in this.loadedRequests;
    },

    abortAllRequests: function NetworkManager_abortAllRequests() {
      for (var xhrId in this.pendingRequests) {
        this.abortRequest(xhrId | 0);
      }
    },

    abortRequest: function NetworkManager_abortRequest(xhrId) {
      var xhr = this.pendingRequests[xhrId].xhr;
      delete this.pendingRequests[xhrId];
      xhr.abort();
    }
  };

  return NetworkManager;
})();

//#if !(FIREFOX || MOZCENTRAL)
(function (root, factory) {
  if (typeof define === 'function' && define.amd) {
    define('pdfjs/core/network', ['exports', 'pdfjs/shared/util',
      'pdfjs/core/worker'], factory);
  } else if (typeof exports !== 'undefined') {
    factory(exports, require('../shared/util.js'), require('./worker.js'));
  } else {
    factory((root.pdfjsCoreNetwork = {}), root.pdfjsSharedUtil,
      root.pdfjsCoreWorker);
  }
}(this, function (exports, sharedUtil, coreWorker) {

  var assert = sharedUtil.assert;
  var createPromiseCapability = sharedUtil.createPromiseCapability;
  var isInt = sharedUtil.isInt;
  var MissingPDFException = sharedUtil.MissingPDFException;
  var UnexpectedResponseException = sharedUtil.UnexpectedResponseException;

  /** @implements {IPDFStream} */
  function PDFNetworkStream(options) {
    this._options = options;
    var source = options.source;
    this._manager = new NetworkManager(source.url, {
      httpHeaders: source.httpHeaders,
      withCredentials: source.withCredentials
    });
    this._rangeChunkSize = source.rangeChunkSize;
    this._fullRequestReader = null;
    this._rangeRequestReaders = [];
  }

  PDFNetworkStream.prototype = {
    _onRangeRequestReaderClosed: function PDFNetworkStream_onRangeRequestReaderClosed(reader) {
      var i = this._rangeRequestReaders.indexOf(reader);
      if (i >= 0) {
        this._rangeRequestReaders.splice(i, 1);
      }
    },

    getFullReader: function PDFNetworkStream_getFullReader() {
      assert(!this._fullRequestReader);
      this._fullRequestReader =
        new PDFNetworkStreamFullRequestReader(this._manager, this._options);
      return this._fullRequestReader;
    },

    getRangeReader: function PDFNetworkStream_getRangeReader(begin, end) {
      var reader = new PDFNetworkStreamRangeRequestReader(this._manager,
        begin, end);
      reader.onClosed = this._onRangeRequestReaderClosed.bind(this);
      this._rangeRequestReaders.push(reader);
      return reader;
    },

    cancelAllRequests: function PDFNetworkStream_cancelAllRequests(reason) {
      if (this._fullRequestReader) {
        this._fullRequestReader.cancel(reason);
      }
      var readers = this._rangeRequestReaders.slice(0);
      readers.forEach(function (reader) {
        reader.cancel(reason);
      });
    }
  };

  /** @implements {IPDFStreamReader} */
  function PDFNetworkStreamFullRequestReader(manager, options) {
    this._manager = manager;

    var source = options.source;
    var args = {
      onHeadersReceived: this._onHeadersReceived.bind(this),
      onProgressiveData: source.disableStream ? null :
        this._onProgressiveData.bind(this),
      onDone: this._onDone.bind(this),
      onError: this._onError.bind(this),
      onProgress: this._onProgress.bind(this)
    };
    this._url = source.url;
    this._fullRequestId = manager.requestFull(args);
    this._headersReceivedCapability = createPromiseCapability();
    this._disableRange = options.disableRange || false;
    this._contentLength = source.length; // optional
    this._rangeChunkSize = source.rangeChunkSize;
    if (!this._rangeChunkSize && !this._disableRange) {
      this._disableRange = true;
    }

    this._isStreamingSupported = false;
    this._isRangeSupported = false;

    this._cachedChunks = [];
    this._requests = [];
    this._done = false;
    this._storedError = undefined;

    this.onProgress = null;
  }

  PDFNetworkStreamFullRequestReader.prototype = {
    _validateRangeRequestCapabilities: function
      PDFNetworkStreamFullRequestReader_validateRangeRequestCapabilities() {

      if (this._disableRange) {
        return false;
      }

      var networkManager = this._manager;
      var fullRequestXhrId = this._fullRequestId;
      var fullRequestXhr = networkManager.getRequestXhr(fullRequestXhrId);
      if (fullRequestXhr.getResponseHeader('Accept-Ranges') !== 'bytes') {
        return false;
      }

      var contentEncoding =
        fullRequestXhr.getResponseHeader('Content-Encoding') || 'identity';
      if (contentEncoding !== 'identity') {
        return false;
      }

      var length = fullRequestXhr.getResponseHeader('Content-Length');
      length = parseInt(length, 10);
      if (!isInt(length)) {
        return false;
      }

      this._contentLength = length; // setting right content length

      if (length <= 2 * this._rangeChunkSize) {
        // The file size is smaller than the size of two chunks, so it does
        // not make any sense to abort the request and retry with a range
        // request.
        return false;
      }

      return true;
    },

    _onHeadersReceived: function PDFNetworkStreamFullRequestReader_onHeadersReceived() {

      if (this._validateRangeRequestCapabilities()) {
        this._isRangeSupported = true;
      }

      var networkManager = this._manager;
      var fullRequestXhrId = this._fullRequestId;
      if (networkManager.isStreamingRequest(fullRequestXhrId)) {
        // We can continue fetching when progressive loading is enabled,
        // and we don't need the autoFetch feature.
        this._isStreamingSupported = true;
      } else if (this._isRangeSupported) {
        // NOTE: by cancelling the full request, and then issuing range
        // requests, there will be an issue for sites where you can only
        // request the pdf once. However, if this is the case, then the
        // server should not be returning that it can support range
        // requests.
        networkManager.abortRequest(fullRequestXhrId);
      }

      this._headersReceivedCapability.resolve();
    },

    _onProgressiveData: function PDFNetworkStreamFullRequestReader_onProgressiveData(chunk) {
      if (this._requests.length > 0) {
        var requestCapability = this._requests.shift();
        requestCapability.resolve({value: chunk, done: false});
      } else {
        this._cachedChunks.push(chunk);
      }
    },

    _onDone: function PDFNetworkStreamFullRequestReader_onDone(args) {
      if (args) {
        this._onProgressiveData(args.chunk);
      }
      this._done = true;
      if (this._cachedChunks.length > 0) {
        return;
      }
      this._requests.forEach(function (requestCapability) {
        requestCapability.resolve({value: undefined, done: true});
      });
      this._requests = [];
    },

    _onError: function PDFNetworkStreamFullRequestReader_onError(status) {
      var url = this._url;
      var exception;
      if (status === 404 || status === 0 && /^file:/.test(url)) {
        exception = new MissingPDFException('Missing PDF "' + url + '".');
      } else {
        exception = new UnexpectedResponseException(
          'Unexpected server response (' + status +
          ') while retrieving PDF "' + url + '".', status);
      }
      this._storedError = exception;
      this._headersReceivedCapability.reject(exception);
      this._requests.forEach(function (requestCapability) {
        requestCapability.reject(exception);
      });
      this._requests = [];
      this._cachedChunks = [];
    },

    _onProgress: function PDFNetworkStreamFullRequestReader_onProgress(data) {
      if (this.onProgress) {
        this.onProgress({
          loaded: data.loaded,
          total: data.lengthComputable ? data.total : this._contentLength
        });
      }
    },

    get isRangeSupported() {
      return this._isRangeSupported;
    },

    get isStreamingSupported() {
      return this._isStreamingSupported;
    },

    get contentLength() {
      return this._contentLength;
    },

    get headersReady() {
      return this._headersReceivedCapability.promise;
    },

    read: function PDFNetworkStreamFullRequestReader_read() {
      if (this._storedError) {
        return Promise.reject(this._storedError);
      }
      if (this._cachedChunks.length > 0) {
        var chunk = this._cachedChunks.shift();
        return Promise.resolve(chunk);
      }
      if (this._done) {
        return Promise.resolve({value: undefined, done: true});
      }
      var requestCapability = createPromiseCapability();
      this._requests.push(requestCapability);
      return requestCapability.promise;
    },

    cancel: function PDFNetworkStreamFullRequestReader_cancel(reason) {
      this._done = true;
      this._headersReceivedCapability.reject(reason);
      this._requests.forEach(function (requestCapability) {
        requestCapability.resolve({value: undefined, done: true});
      });
      this._requests = [];
      if (this._manager.isPendingRequest(this._fullRequestId)) {
        this._manager.abortRequest(this._fullRequestId);
      }
      this._fullRequestReader = null;
    }
  };

  /** @implements {IPDFStreamRangeReader} */
  function PDFNetworkStreamRangeRequestReader(manager, begin, end) {
    this._manager = manager;
    var args = {
      onDone: this._onDone.bind(this),
      onProgress: this._onProgress.bind(this)
    };
    this._requestId = manager.requestRange(begin, end, args);
    this._requests = [];
    this._queuedChunk = null;
    this._done = false;

    this.onProgress = null;
    this.onClosed = null;
  }

  PDFNetworkStreamRangeRequestReader.prototype = {
    _close: function PDFNetworkStreamRangeRequestReader_close() {
      if (this.onClosed) {
        this.onClosed(this);
      }
    },

    _onDone: function PDFNetworkStreamRangeRequestReader_onDone(data) {
      var chunk = data.chunk;
      if (this._requests.length > 0) {
        var requestCapability = this._requests.shift();
        requestCapability.resolve({value: chunk, done: false});
      } else {
        this._queuedChunk = chunk;
      }
      this._done = true;
      this._requests.forEach(function (requestCapability) {
        requestCapability.resolve({value: undefined, done: true});
      });
      this._requests = [];
      this._close();
    },

    _onProgress: function PDFNetworkStreamRangeRequestReader_onProgress(evt) {
      if (!this.isStreamingSupported && this.onProgress) {
        this.onProgress({
          loaded: evt.loaded
        });
      }
    },

    get isStreamingSupported() {
      return false; // TODO allow progressive range bytes loading
    },

    read: function PDFNetworkStreamRangeRequestReader_read() {
      if (this._queuedChunk !== null) {
        var chunk = this._queuedChunk;
        this._queuedChunk = null;
        return Promise.resolve({value: chunk, done: false});
      }
      if (this._done) {
        return Promise.resolve({value: undefined, done: true});
      }
      var requestCapability = createPromiseCapability();
      this._requests.push(requestCapability);
      return requestCapability.promise;
    },

    cancel: function PDFNetworkStreamRangeRequestReader_cancel(reason) {
      this._done = true;
      this._requests.forEach(function (requestCapability) {
        requestCapability.resolve({value: undefined, done: true});
      });
      this._requests = [];
      if (this._manager.isPendingRequest(this._requestId)) {
        this._manager.abortRequest(this._requestId);
      }
      this._close();
    }
  };

  coreWorker.setPDFNetworkStreamClass(PDFNetworkStream);

  exports.PDFNetworkStream = PDFNetworkStream;
  exports.NetworkManager = NetworkManager;
}));
//#endif
