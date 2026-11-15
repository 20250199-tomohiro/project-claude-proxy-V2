'use strict';
/**
 * Service Worker 方式 Web プロキシ (Render 用 / 単一ファイル)
 *
 *  - トップページ・Service Worker・クライアントフックは全て本ファイルに埋め込み済み
 *    (ファイルの置き場所に依存しません)
 *  - 依存: ws のみ
 *
 * 環境変数
 *  PORT          Render が自動設定
 *  BASIC_AUTH    "user:pass" を入れると全体に Basic 認証をかける (任意・公開時は推奨)
 *  ALLOW_PRIVATE "1" でプライベート IP / localhost への接続を許可 (テスト専用)
 *
 * 対応:
 *  ① Cookie            : サーバー側 Cookie jar (セッション毎) + document.cookie フック
 *  ② Range / 大容量    : Range / If-Range をそのまま転送し、ストリームで中継 (バッファしない)
 *  ③ JS が後から作る   : fetch / XHR / 要素の src,href 等 / Worker / EventSource / history などをフック
 *  ④ WebSocket         : /~/ws でブリッジ (サブプロトコル・Cookie・Origin 対応)
 *  ⑤ 取りこぼし救済    : Service Worker + MutationObserver + サーバー側 Referer/最終サイトでのリダイレクト
 *  ⑥ Referer / Origin  : プロキシURLを元のURLに戻して転送
 */

const http = require('http');
const https = require('https');
const zlib = require('zlib');
const dns = require('dns');
const net = require('net');
const crypto = require('crypto');
const { WebSocketServer, WebSocket } = require('ws');
const fs = require('fs');
const pathMod = require('path');
const vm = require('vm');
const os = require('os');
const { execFile } = require('child_process');

const PORT = parseInt(process.env.PORT, 10) || 3000;
const BASIC_AUTH = process.env.BASIC_AUTH || '';
const ALLOW_PRIVATE = process.env.ALLOW_PRIVATE === '1';
const PREFIX = '/go/';
const SID_NAME = '__pxsid';
const MAX_REWRITE = 30 * 1024 * 1024; // HTML/CSS を書き換える際の上限
const UPSTREAM_TIMEOUT = 30000; // 応答ヘッダが来るまでの待ち時間

/* ---- reCAPTCHA 互換モジュール / デバッグオーバーレイ (同じフォルダの .js を読み込む) ----
 *  RC_DEBUG=0 でデバッグオーバーレイとログを無効化 (既定は有効) */
const RC_DEBUG = process.env.RC_DEBUG !== '0';
function loadLocal(name) {
  try {
    return fs.readFileSync(pathMod.join(__dirname, name), 'utf8');
  } catch (e) {
    console.warn('[rc] ' + name + ' を読み込めませんでした: ' + e.message);
    return null;
  }
}
const RC_OVERLAY_SRC = loadLocal('recaptcha-debug-overlay.js');
let RC_COMPAT_OK = false;
try {
  const src = loadLocal('recaptcha-compat.js');
  if (src) {
    vm.runInThisContext(src, { filename: 'recaptcha-compat.js' });
    RC_COMPAT_OK = typeof globalThis.createRecaptchaCompat === 'function';
  }
} catch (e) {
  console.warn('[rc] recaptcha-compat.js の初期化に失敗: ' + e.message);
}
// オリジン (ホスト名) ごとにインスタンスを持つ: proxyOrigin / ログが別々になるため
const GOOGLE_RE = /(^|\.)(google\.[a-z.]+|gstatic\.com|googleusercontent\.com|googleapis\.com|youtube\.com)$/i;
const pxLogs = [];
function pxLog(line) {
  pxLogs.push(new Date().toISOString().slice(11, 23) + ' ' + line);
  if (pxLogs.length > 300) pxLogs.shift();
}
const rcCompats = new Map();
function getRc(req) {
  if (!RC_COMPAT_OK) return null;
  const host = String(req.headers.host || '');
  const origin = (isSecure(req) ? 'https' : 'http') + '://' + host;
  let c = rcCompats.get(origin);
  if (!c) {
    try {
      c = globalThis.createRecaptchaCompat({
        proxyOrigin: origin,
        decodeUrl: (u) => decodeProxyUrl(u, host),
        debug: RC_DEBUG
      });
    } catch (e) {
      return null;
    }
    rcCompats.set(origin, c);
  }
  return c;
}

/* ========================================================================
 *  ブラウザ側コード (関数として書いて toString() で埋め込む)
 * ====================================================================== */

/* ---------- Service Worker ---------- */
function swMain() {
  var RX = /^\/go\/(https?)\/([^\/?#]+)(\/[^?#]*)?/;

  function targetFromProxyHref(href) {
    try {
      var u = new URL(href);
      if (u.origin !== self.location.origin) return null;
      var m = RX.exec(u.pathname);
      if (!m) return null;
      return m[1] + '://' + m[2] + (m[3] || '/') + u.search;
    } catch (e) {
      return null;
    }
  }

  function toProxyPath(t) {
    var u = new URL(t);
    return '/go/' + u.protocol.slice(0, -1) + '/' + u.host + u.pathname + u.search;
  }

  self.addEventListener('install', function () {
    self.skipWaiting();
  });
  self.addEventListener('activate', function (e) {
    e.waitUntil(self.clients.claim());
  });

  self.addEventListener('fetch', function (e) {
    var req = e.request;
    var url = new URL(req.url);
    if (url.origin === self.location.origin) {
      var p = url.pathname;
      // プロキシ済み / サーバー自身のパスはそのままネットワークへ
      if (p.indexOf('/go/') === 0 || p.indexOf('/~/') === 0 || p === '/' || p === '/sw.js' || p === '/healthz' || p === '/__rc-debug') return;
    }
    e.respondWith(rescue(e, req, url));
  });

  // ⑤ 取りこぼし救済: プロキシを経由していない要求を、元ページを手がかりにプロキシへ付け替える
  async function rescue(e, req, url) {
    var pageHref = null;
    try {
      if (e.clientId) {
        var c = await self.clients.get(e.clientId);
        if (c) pageHref = c.url;
      }
    } catch (err) {}
    if (!pageHref && req.referrer) pageHref = req.referrer;
    var pageTarget = pageHref ? targetFromProxyHref(pageHref) : null;
    if (!pageTarget) return fetch(req); // プロキシ越しのページではない

    var target;
    if (url.origin === self.location.origin) {
      // /foo.js のような絶対パスが取りこぼされたケース
      target = new URL(url.pathname + url.search, pageTarget).href;
    } else {
      // https://cdn.example.com/x.js のような直接の外部アクセス
      target = url.href;
    }
    if (!/^https?:/i.test(target)) return fetch(req);

    var prox = self.location.origin + toProxyPath(target);
    if (req.mode === 'navigate') return Response.redirect(prox, 307);

    var init = {
      method: req.method,
      headers: req.headers,
      credentials: 'same-origin',
      redirect: req.redirect,
      referrerPolicy: req.referrerPolicy
    };
    try {
      init.referrer = new URL(req.referrer).origin === self.location.origin ? req.referrer : '';
    } catch (err) {
      init.referrer = '';
    }
    if (req.cache && req.cache !== 'only-if-cached') init.cache = req.cache;
    if (req.method !== 'GET' && req.method !== 'HEAD') {
      init.body = await req.clone().arrayBuffer();
    }
    return fetch(prox, init);
  }
}

/* ---------- ページ内に注入するフック ---------- */
function clientMain() {
  if (window.__PX_ON) return;
  window.__PX_ON = true;

  var loc = window.location;
  var ORIGIN = loc.origin;
  var RX = /^\/go\/(https?)\/([^\/?#]+)(\/[^?#]*)?/;
  if (!RX.test(loc.pathname)) return;
  var NOPROXY = /^(data|blob|javascript|mailto|tel|about|sms|file|chrome|ws|wss):/i;

  function curT() {
    var m = RX.exec(loc.pathname);
    return new URL(m[1] + '://' + m[2] + (m[3] || '/') + loc.search);
  }

  // 任意のURL文字列をプロキシ経由のパスに変換
  function toProxy(raw) {
    try {
      if (raw === null || raw === undefined) return raw;
      var s = String(raw);
      var t = s.trim();
      if (!t || t.charAt(0) === '#' || NOPROXY.test(t)) return raw;
      var u = new URL(t, loc.href);
      if (u.protocol !== 'http:' && u.protocol !== 'https:') return raw;
      if (u.origin === ORIGIN) {
        if (RX.test(u.pathname) || u.pathname.indexOf('/~/') === 0) return u.pathname + u.search + u.hash;
        // プロキシ自身のオリジンに解決されてしまった絶対パス → 元サイトのパスとして扱う
        u = new URL(u.pathname + u.search + u.hash, curT().origin);
      }
      return '/go/' + u.protocol.slice(0, -1) + '/' + u.host + u.pathname + u.search + u.hash;
    } catch (e) {
      return raw;
    }
  }

  function fixSrcset(v) {
    try {
      return String(v)
        .split(',')
        .map(function (c) {
          var p = c.trim().split(/\s+/);
          p[0] = toProxy(p[0]);
          return p.join(' ');
        })
        .join(', ');
    } catch (e) {
      return v;
    }
  }

  var nativeFetch = window.fetch;

  // フック前のネイティブ関数を控えておく (末尾で toString() を native code に見せるために使う)
  var NAT = {
    fetch: window.fetch,
    xopen: XMLHttpRequest.prototype.open,
    xsend: XMLHttpRequest.prototype.send,
    beacon: navigator.sendBeacon,
    wopen: window.open,
    push: history.pushState,
    replace: history.replaceState,
    setAttr: Element.prototype.setAttribute,
    WS: window.WebSocket,
    Worker: window.Worker,
    SharedWorker: window.SharedWorker,
    ES: window.EventSource,
    dopen: Document.prototype.open,
    cerr: console.error
  };
  var nativeToStr = Function.prototype.toString;
  // Google ログインは Google のドメインかどうか (WebRTC 無効化など、挙動を変える判断に使う)
  var IS_GOOGLE = /(^|\.)(google\.[a-z.]+|gstatic\.com|googleusercontent\.com|googleapis\.com|youtube\.com)$/i.test(curT().hostname);
  // YouTube: SPA (location.pathname でページを判定する) はプロキシ URL (/go/https/...) では誤動作するため、
  // サイト内移動はすべて「通常のページ遷移」に置き換える。
  var YT_RE = /(^|\.)(youtube\.com|youtu\.be|youtube-nocookie\.com)$/i;
  var IS_YT = YT_RE.test(curT().hostname);
  var T0 = Date.now();

  /* --- fetch --- */
  if (nativeFetch) {
    window.fetch = function (input, init) {
      try {
        if (typeof input === 'string' || (window.URL && input instanceof URL)) {
          input = toProxy(String(input));
        } else if (input && typeof input.url === 'string') {
          var nu = toProxy(input.url);
          if (nu !== input.url) input = new Request(nu, input);
        }
      } catch (e) {}
      return nativeFetch.call(this, input, init);
    };
  }

  /* --- XHR --- */
  var xo = XMLHttpRequest.prototype.open;
  XMLHttpRequest.prototype.open = function (method, url) {
    var a = Array.prototype.slice.call(arguments);
    a[1] = toProxy(url);
    return xo.apply(this, a);
  };

  /* --- sendBeacon / window.open / history --- */
  if (navigator.sendBeacon) {
    var nb = navigator.sendBeacon;
    navigator.sendBeacon = function (url, data) {
      return nb.call(navigator, toProxy(url), data);
    };
  }
  // ナビバー付きページ (タブ) の中かどうか
  function hasShell() {
    try {
      var w = window;
      while (w !== w.parent) {
        w = w.parent;
        if (w.__PX_SHELL) return true;
      }
    } catch (e) {}
    return false;
  }
  function postOpen(path) {
    try {
      var w = window;
      while (w !== w.parent) {
        w = w.parent;
        w.postMessage({ pxopen: path }, '*');
      }
    } catch (e) {}
  }
  var nopen = window.open;
  window.open = function (url) {
    var a = Array.prototype.slice.call(arguments);
    if (url) a[0] = toProxy(url);
    // プロキシ内のタブとして開く
    if (typeof a[0] === 'string' && a[0].indexOf('/go/') === 0 && hasShell()) {
      postOpen(a[0]);
      return null;
    }
    return nopen.apply(window, a);
  };
  // target="_blank" のリンクも新しいタブで開く
  document.addEventListener(
    'click',
    function (ev) {
      try {
        var an = ev.target && ev.target.closest ? ev.target.closest('a[href]') : null;
        if (!an || ev.defaultPrevented) return;
        var tg = (an.getAttribute('target') || '').toLowerCase();
        if ((tg !== '_blank' && tg !== '_new') || !hasShell()) return;
        var pp = toProxy(an.getAttribute('href'));
        if (typeof pp === 'string' && pp.indexOf('/go/') === 0) {
          ev.preventDefault();
          postOpen(pp);
        }
      } catch (e) {}
    },
    false
  );
  ['pushState', 'replaceState'].forEach(function (k) {
    var o = history[k];
    history[k] = function (s, t, u) {
      var nu = u === undefined || u === null ? u : toProxy(u);
      // YouTube の SPA 遷移 (pushState) は、ページ全体の読み込みに置き換える
      // (起動直後 1.5 秒は素通し: 起動処理が pushState を呼んでも無限ループにならないように)
      if (IS_YT && k === 'pushState' && typeof nu === 'string' && nu.indexOf('/go/') === 0 &&
          nu !== loc.pathname + loc.search + loc.hash && Date.now() - T0 > 1500) {
        loc.assign(nu);
        return;
      }
      return o.call(this, s, t, nu);
    };
  });
  // YouTube 内のリンクは SPA を通さず、そのままページ遷移させる
  if (IS_YT) {
    window.addEventListener(
      'click',
      function (ev) {
        try {
          if (ev.defaultPrevented || ev.button !== 0 || ev.metaKey || ev.ctrlKey || ev.shiftKey || ev.altKey) return;
          var path = ev.composedPath ? ev.composedPath() : [];
          var an = null;
          for (var i = 0; i < path.length; i++) {
            if (path[i] && path[i].tagName === 'A' && path[i].getAttribute('href')) {
              an = path[i];
              break;
            }
          }
          if (!an) return;
          var tg = (an.getAttribute('target') || '').toLowerCase();
          if (tg === '_blank' || tg === '_new') return; // 新しいタブ側の既存処理に任せる
          var np = toProxy(an.getAttribute('href'));
          if (typeof np !== 'string' || np.indexOf('/go/') !== 0) return;
          var m = RX.exec(np);
          if (!m || !YT_RE.test(m[2].split(':')[0])) return; // YouTube 外へのリンクは対象外
          ev.preventDefault();
          ev.stopImmediatePropagation();
          loc.assign(np);
        } catch (e) {}
      },
      true
    );
  }

  /* --- Worker / EventSource --- */
  ['Worker', 'SharedWorker'].forEach(function (n) {
    var N = window[n];
    if (!N) return;
    var W = function (url, opts) {
      return new N(toProxy(url), opts);
    };
    W.prototype = N.prototype;
    window[n] = W;
  });
  if (window.EventSource) {
    var NES = window.EventSource;
    var ES = function (url, opts) {
      return new NES(toProxy(url), opts);
    };
    ES.prototype = NES.prototype;
    ES.CONNECTING = 0;
    ES.OPEN = 1;
    ES.CLOSED = 2;
    window.EventSource = ES;
  }

  /* --- ③ 要素の URL 属性 (setAttribute / プロパティ) --- */
  var URL_ATTRS = { src: 1, href: 1, action: 1, poster: 1, data: 1, formaction: 1 };
  var setAttr = Element.prototype.setAttribute;
  Element.prototype.setAttribute = function (n, v) {
    try {
      var ln = String(n).toLowerCase();
      if (URL_ATTRS[ln]) {
        if (!(ln === 'data' && this.tagName !== 'OBJECT')) v = toProxy(v);
      } else if (ln === 'srcset') {
        v = fixSrcset(v);
      }
    } catch (e) {}
    return setAttr.call(this, n, v);
  };

  function patchProp(ctor, prop, fn) {
    try {
      var C = window[ctor];
      if (!C) return;
      var d = Object.getOwnPropertyDescriptor(C.prototype, prop);
      if (!d || !d.set) return;
      Object.defineProperty(C.prototype, prop, {
        configurable: true,
        enumerable: d.enumerable,
        get: d.get,
        set: function (v) {
          d.set.call(this, fn(v));
        }
      });
    } catch (e) {}
  }
  [
    ['HTMLImageElement', 'src'],
    ['HTMLScriptElement', 'src'],
    ['HTMLLinkElement', 'href'],
    ['HTMLIFrameElement', 'src'],
    ['HTMLFrameElement', 'src'],
    ['HTMLAnchorElement', 'href'],
    ['HTMLAreaElement', 'href'],
    ['HTMLSourceElement', 'src'],
    ['HTMLMediaElement', 'src'],
    ['HTMLTrackElement', 'src'],
    ['HTMLEmbedElement', 'src'],
    ['HTMLObjectElement', 'data'],
    ['HTMLFormElement', 'action'],
    ['HTMLInputElement', 'src'],
    ['HTMLVideoElement', 'poster']
  ].forEach(function (x) {
    patchProp(x[0], x[1], toProxy);
  });
  patchProp('HTMLImageElement', 'srcset', fixSrcset);
  patchProp('HTMLSourceElement', 'srcset', fixSrcset);

  /* --- ⑤ MutationObserver: innerHTML 等で後から入った要素を救済 --- */
  function fixEl(el) {
    if (!el || el.nodeType !== 1) return;
    for (var a in URL_ATTRS) {
      if (a === 'data' && el.tagName !== 'OBJECT') continue;
      if (el.hasAttribute(a)) {
        var v = el.getAttribute(a);
        var nv = toProxy(v);
        if (nv !== v) setAttr.call(el, a, nv);
      }
    }
  }
  try {
    new MutationObserver(function (list) {
      for (var i = 0; i < list.length; i++) {
        var r = list[i];
        if (r.type === 'attributes') {
          fixEl(r.target);
        } else {
          for (var j = 0; j < r.addedNodes.length; j++) {
            var n = r.addedNodes[j];
            if (n.nodeType !== 1) continue;
            fixEl(n);
            if (n.querySelectorAll) {
              var all = n.querySelectorAll('[src],[href],[action],[poster]');
              for (var k = 0; k < all.length; k++) fixEl(all[k]);
            }
          }
        }
      }
    }).observe(document.documentElement, {
      subtree: true,
      childList: true,
      attributes: true,
      attributeFilter: ['src', 'href', 'action', 'poster']
    });
  } catch (e) {}

  /* --- ① document.cookie --- */
  var jar = {};
  String(window.__PX_COOKIE || '')
    .split(';')
    .forEach(function (p) {
      var i = p.indexOf('=');
      if (i < 0) return;
      var k = p.slice(0, i).trim();
      if (k) jar[k] = p.slice(i + 1).trim();
    });
  try {
    Object.defineProperty(Document.prototype, 'cookie', {
      configurable: true,
      get: function () {
        return Object.keys(jar)
          .map(function (k) {
            return k + '=' + jar[k];
          })
          .join('; ');
      },
      set: function (str) {
        str = String(str);
        var parts = str.split(';');
        var i = parts[0].indexOf('=');
        if (i > 0) {
          var k = parts[0].slice(0, i).trim();
          var v = parts[0].slice(i + 1).trim();
          var del = false;
          for (var n = 1; n < parts.length; n++) {
            var kv = parts[n].split('=');
            var an = kv[0].trim().toLowerCase();
            var av = (kv[1] || '').trim();
            if (an === 'max-age' && parseInt(av, 10) <= 0) del = true;
            if (an === 'expires') {
              var t = Date.parse(parts[n].slice(parts[n].indexOf('=') + 1));
              if (!isNaN(t) && t <= Date.now()) del = true;
            }
          }
          if (del) delete jar[k];
          else jar[k] = v;
        }
        try {
          nativeFetch.call(window, '/~/cookie', {
            method: 'POST',
            headers: { 'content-type': 'application/json' },
            body: JSON.stringify({ url: curT().href, cookie: str }),
            keepalive: true,
            credentials: 'same-origin'
          });
        } catch (e) {}
      }
    });
  } catch (e) {}

  /* --- ページ側からの Service Worker 操作を封じる (プロキシ用 SW を消されないように) --- */
  try {
    if (navigator.serviceWorker) {
      var sw = navigator.serviceWorker;
      sw.register = function () {
        return Promise.reject(new DOMException('Service Worker registration is disabled in proxy', 'SecurityError'));
      };
      sw.getRegistrations = function () {
        return Promise.resolve([]);
      };
      sw.getRegistration = function () {
        return Promise.resolve(undefined);
      };
    }
  } catch (e) {}

  /* --- ④ WebSocket --- */
  var NativeWS = window.WebSocket;
  if (NativeWS) {
    var PXWS = function (url, protocols) {
      var abs;
      try {
        abs = new URL(String(url), curT().href);
        if (abs.protocol === 'http:') abs.protocol = 'ws:';
        else if (abs.protocol === 'https:') abs.protocol = 'wss:';
      } catch (e) {
        return protocols === undefined ? new NativeWS(url) : new NativeWS(url, protocols);
      }
      var purl =
        (loc.protocol === 'https:' ? 'wss:' : 'ws:') +
        '//' +
        loc.host +
        '/~/ws?url=' +
        encodeURIComponent(abs.href) +
        '&o=' +
        encodeURIComponent(curT().origin);
      var ws = protocols === undefined ? new NativeWS(purl) : new NativeWS(purl, protocols);
      try {
        Object.defineProperty(ws, 'url', {
          get: function () {
            return abs.href;
          }
        });
      } catch (e) {}
      return ws;
    };
    PXWS.prototype = NativeWS.prototype;
    PXWS.CONNECTING = 0;
    PXWS.OPEN = 1;
    PXWS.CLOSING = 2;
    PXWS.CLOSED = 3;
    window.WebSocket = PXWS;
  }

  /* --- 外部への直接通信を作らせない: WebRTC / WebTransport を無効化 --- */
  // (Google 系ドメインでは無効化しない: これらが undefined だと不自然な環境として判定され、ログインが弾かれる原因になる)
  ['RTCPeerConnection', 'webkitRTCPeerConnection', 'RTCDataChannel', 'WebTransport'].forEach(function (n) {
    if (IS_GOOGLE) return;
    try {
      Object.defineProperty(window, n, { configurable: true, writable: true, value: undefined });
    } catch (e) {}
  });

  /* --- フォーム送信先が外部のままなら、送信直前にプロキシ経由へ書き換える --- */
  document.addEventListener(
    'submit',
    function (ev) {
      try {
        var f = ev.target;
        if (f && f.getAttribute) {
          var act = f.getAttribute('action');
          if (act) {
            var np = toProxy(act);
            if (np !== act) setAttr.call(f, 'action', np);
          }
        }
        var sb = ev.submitter;
        if (sb && sb.getAttribute) {
          var fa = sb.getAttribute('formaction');
          if (fa) {
            var nf = toProxy(fa);
            if (nf !== fa) setAttr.call(sb, 'formaction', nf);
          }
        }
      } catch (e) {}
    },
    true
  );

  /* --- 取りこぼしの外部 iframe 遷移 (CSP で遮断されたもの) をプロキシ内へ付け替え --- */
  var leakNote = function () {};
  document.addEventListener('securitypolicyviolation', function (ev) {
    try {
      var b = ev.blockedURI;
      var d = ev.violatedDirective || '';
      if (!/^https?:/i.test(b) || (d.indexOf('frame-src') !== 0 && d.indexOf('child-src') !== 0)) return;
      var fs = document.querySelectorAll('iframe,frame');
      var pick = null;
      for (var i = 0; i < fs.length; i++) {
        if (fs[i].src === b) {
          pick = fs[i];
          break;
        }
      }
      if (!pick && fs.length === 1) pick = fs[0];
      leakNote('LEAK遮断', '外部への iframe 移動を止めてプロキシ内で開きます ' + b);
      if (pick) pick.src = toProxy(b);
    } catch (e) {}
  });

  /* --- ページ自身が外部サイトへ移動しようとしたら、止めてプロキシ経由で開き直す (パスも保持) --- */
  try {
    if (window.navigation && navigation.addEventListener) {
      navigation.addEventListener('navigate', function (ev) {
        try {
          if (!ev.cancelable || ev.formData) return;
          var nu = new URL(ev.destination.url);
          if (nu.origin === ORIGIN || !/^https?:$/.test(nu.protocol)) return;
          ev.preventDefault();
          var np = toProxy(nu.href);
          leakNote('LEAK遮断', 'ページの外部移動を止めてプロキシ内で開きます ' + nu.href);
          setTimeout(function () {
            location.href = np;
          }, 0);
        } catch (e) {}
      });
    }
  } catch (e) {}

  /* --- 簡易デバッグ表示: JS エラー / 読み込み失敗 / 通信失敗を画面右下に出す --- */
  (function () {
    var logs = [];
    var badge = null;
    var panel = null;
    var list = null;
    var open = false;

    function el(tag, css, text) {
      var e = document.createElement(tag);
      if (css) e.style.cssText = css;
      if (text !== undefined) e.textContent = text;
      return e;
    }
    function short(s, n) {
      s = String(s);
      return s.length > n ? s.slice(0, n) + '…' : s;
    }
    function logColor(t) {
      if (/\] NAV /.test(t)) return '#6cb6ff';
      if (/\] document\.open/.test(t)) return '#ffa726';
      if (/\] LEAK遮断/.test(t)) return '#c792ea';
      if (/\] (JSエラー|LOAD失敗|HTTP \d|通信失敗|Promise拒否|console\.error|WebSocket失敗)/.test(t)) return '#ff6b6b';
      return '#eee';
    }
    function fillList(box) {
      box.textContent = '';
      for (var i = 0; i < logs.length; i++) {
        var d = document.createElement('div');
        d.style.cssText = 'margin-bottom:8px;color:' + logColor(logs[i]);
        d.textContent = logs[i];
        box.appendChild(d);
      }
    }
    function render() {
      if (!badge) return;
      badge.textContent = '⚠ ' + logs.length;
      badge.style.display = logs.length ? 'block' : 'none';
      if (open && list) fillList(list);
      if (open && list) list.scrollTop = list.scrollHeight;
    }
    function build() {
      if (badge || !document.documentElement) return;
      var base = 'position:fixed;z-index:2147483647;font:12px/1.5 monospace;';
      badge = el(
        'div',
        base + 'right:8px;bottom:8px;padding:6px 10px;border-radius:14px;background:#c62828;color:#fff;cursor:pointer;display:none;box-shadow:0 2px 8px rgba(0,0,0,.4)'
      );
      badge.addEventListener('click', function () {
        open = !open;
        panel.style.display = open ? 'flex' : 'none';
        render();
      });
      panel = el(
        'div',
        base + 'right:8px;bottom:44px;width:min(560px,92vw);height:min(360px,60vh);display:none;flex-direction:column;background:#111;color:#eee;border:1px solid #555;border-radius:8px;overflow:hidden'
      );
      var bar = el('div', 'display:flex;gap:6px;padding:6px;background:#222;align-items:center');
      bar.appendChild(el('span', 'flex:1;color:#ffb86b', 'Debug (' + location.pathname.slice(0, 60) + ')'));
      function btn(label, fn) {
        var b = el('button', 'font:12px monospace;padding:3px 8px;border:0;border-radius:4px;background:#444;color:#fff;cursor:pointer', label);
        b.addEventListener('click', fn);
        bar.appendChild(b);
      }
      btn('コピー', function () {
        var t = logs.join('\n\n');
        try {
          navigator.clipboard.writeText(t);
        } catch (e) {
          var ta = el('textarea', 'position:fixed;left:-999px');
          ta.value = t;
          document.documentElement.appendChild(ta);
          ta.select();
          try {
            document.execCommand('copy');
          } catch (e2) {}
          ta.remove();
        }
      });
      btn('クリア', function () {
        logs = [];
        render();
      });
      btn('閉じる', function () {
        open = false;
        panel.style.display = 'none';
      });
      list = el('div', 'flex:1;overflow:auto;padding:8px;white-space:pre-wrap;word-break:break-all');
      panel.appendChild(bar);
      panel.appendChild(list);
      document.documentElement.appendChild(panel);
      document.documentElement.appendChild(badge);
    }
    function add(kind, msg) {
      try {
        if (/ResizeObserver loop/.test(msg)) return;
        if (logs.length >= 200) logs.shift();
        var line = '[' + new Date().toTimeString().slice(0, 8) + '] ' + kind + ' ' + short(msg, 600);
        logs.push(line);
        // ナビバー付きページ (外側) にも送る: ゲームがページを書き換えても消えない
        try {
          var w = window;
          while (w !== w.parent) {
            w = w.parent;
            w.postMessage({ pxlog: location.pathname.slice(0, 80) + ' ' + line }, '*');
          }
        } catch (e) {}
        if (!badge) build();
        render();
      } catch (e) {}
    }
    leakNote = add;

    // JS 実行時エラー / 未処理の Promise 拒否 / 読み込み失敗した要素
    window.addEventListener(
      'error',
      function (ev) {
        var t = ev.target;
        if (t && t !== window && t.nodeType === 1) {
          add('LOAD失敗', '<' + t.tagName.toLowerCase() + '> ' + (t.currentSrc || t.src || t.href || ''));
        } else {
          add('JSエラー', (ev.message || 'error') + ' @ ' + short(ev.filename || '', 120) + ':' + (ev.lineno || 0) + ':' + (ev.colno || 0));
        }
      },
      true
    );
    window.addEventListener('unhandledrejection', function (ev) {
      var r = ev.reason;
      add('Promise拒否', r && r.stack ? r.stack : String(r));
    });
    var ce = console.error;
    console.error = function () {
      try {
        add('console.error', Array.prototype.slice
          .call(arguments)
          .map(function (a) {
            return a && a.stack ? a.stack : typeof a === 'object' ? JSON.stringify(a) : String(a);
          })
          .join(' '));
      } catch (e) {}
      return ce.apply(console, arguments);
    };

    // ページ全体の書き換え (document.open / write) と離脱の記録
    try {
      var dopen = Document.prototype.open;
      Document.prototype.open = function () {
        if (arguments.length < 3) add('document.open', 'ページ全体が書き換えられます (document.write)');
        return dopen.apply(this, arguments);
      };
    } catch (e) {}
    window.addEventListener('beforeunload', function () {
      add('ページ離脱', '別のページへ移動 / 再読み込みが始まりました');
    });
    // ゲームが DOM を作り直してもバッジが消えないよう、定期的に付け直す
    setInterval(function () {
      try {
        if (badge && document.documentElement && !badge.isConnected) {
          document.documentElement.appendChild(panel);
          document.documentElement.appendChild(badge);
        }
      } catch (e) {}
    }, 500);

    // fetch の失敗 (ネットワークエラー / HTTP 4xx,5xx)
    var f2 = window.fetch;
    if (f2) {
      window.fetch = function (input) {
        var u = typeof input === 'string' ? input : input && input.url ? input.url : String(input);
        return f2.apply(this, arguments).then(
          function (r) {
            if (r && r.status >= 400 && u.indexOf('/~/') < 0) add('HTTP ' + r.status, 'fetch ' + u);
            return r;
          },
          function (e) {
            if (u.indexOf('/~/') < 0) add('通信失敗', 'fetch ' + u + ' (' + (e && e.message) + ')');
            throw e;
          }
        );
      };
    }
    // XHR の失敗
    var xs = XMLHttpRequest.prototype.send;
    XMLHttpRequest.prototype.send = function () {
      var x = this;
      x.addEventListener('loadend', function () {
        var u = x.responseURL || '';
        if (x.status === 0) add('通信失敗', 'XHR ' + u);
        else if (x.status >= 400) add('HTTP ' + x.status, 'XHR ' + u);
      });
      return xs.apply(this, arguments);
    };
    // WebSocket の失敗
    var W2 = window.WebSocket;
    if (W2) {
      var W3 = function (url, protocols) {
        var ws = protocols === undefined ? new W2(url) : new W2(url, protocols);
        ws.addEventListener('error', function () {
          add('WebSocket失敗', String(url));
        });
        return ws;
      };
      W3.prototype = W2.prototype;
      W3.CONNECTING = 0;
      W3.OPEN = 1;
      W3.CLOSING = 2;
      W3.CLOSED = 3;
      window.WebSocket = W3;
    }
  })();

  /* --- フックした関数の toString() を native code に見せる ---
   *  Google ログインの BotGuard は fetch / XHR などが書き換えられていないかを
   *  Function.prototype.toString で確認するため、素のままだと「エラーが発生しました」で弾かれる */
  try {
    var fakes = new WeakMap();
    var pair = function (f, o) {
      if (typeof f === 'function' && typeof o === 'function' && f !== o) fakes.set(f, o);
    };
    pair(window.fetch, NAT.fetch);
    pair(XMLHttpRequest.prototype.open, NAT.xopen);
    pair(XMLHttpRequest.prototype.send, NAT.xsend);
    pair(navigator.sendBeacon, NAT.beacon);
    pair(window.open, NAT.wopen);
    pair(history.pushState, NAT.push);
    pair(history.replaceState, NAT.replace);
    pair(Element.prototype.setAttribute, NAT.setAttr);
    pair(window.WebSocket, NAT.WS);
    pair(window.Worker, NAT.Worker);
    pair(window.SharedWorker, NAT.SharedWorker);
    pair(window.EventSource, NAT.ES);
    pair(Document.prototype.open, NAT.dopen);
    pair(console.error, NAT.cerr);
    var fakeToString = function toString() {
      var o = fakes.get(this);
      return nativeToStr.call(o || this);
    };
    fakes.set(fakeToString, nativeToStr);
    Function.prototype.toString = fakeToString;
  } catch (e) {}
}

/* ---------- トップページのスクリプト ---------- */
function indexMain() {
  var f = document.getElementById('f');
  var inp = document.getElementById('u');
  var chk = document.getElementById('c');
  var st = document.getElementById('s');
  // ナビバー内 (iframe) で開かれたトップページでは、履歴なしチェックを隠してそのまま遷移する
  var framed = window.top !== window;
  if (framed) chk.parentNode.style.display = 'none';

  try {
    chk.checked = localStorage.getItem('px_cloak') === '1';
  } catch (e) {}
  chk.addEventListener('change', function () {
    try {
      localStorage.setItem('px_cloak', chk.checked ? '1' : '0');
    } catch (e) {}
  });

  function normalize(v) {
    v = v.trim();
    if (!v) return null;
    if (/^https?:\/\//i.test(v)) return v;
    if (
      !/\s/.test(v) &&
      (/^[^\s\/?#:.]+(\.[^\s\/?#:.]+)+(:\d+)?([\/?#]\S*)?$/.test(v) || /^localhost(:\d+)?([\/?#]\S*)?$/i.test(v))
    ) {
      return 'https://' + v;
    }
    return 'https://duckduckgo.com/?q=' + encodeURIComponent(v);
  }

  function toPath(u) {
    var x = new URL(u);
    return '/go/' + x.protocol.slice(0, -1) + '/' + x.host + x.pathname + x.search + x.hash;
  }

  function ensureSW() {
    if (!('serviceWorker' in navigator)) {
      return Promise.reject(new Error('このブラウザ/接続では Service Worker が使えません (HTTPS が必要です)'));
    }
    return navigator.serviceWorker
      .register('/sw.js', { scope: '/' })
      .then(function () {
        return navigator.serviceWorker.ready;
      })
      .then(function () {
        if (navigator.serviceWorker.controller) return;
        return new Promise(function (resolve) {
          var done = false;
          function fin() {
            if (!done) {
              done = true;
              resolve();
            }
          }
          navigator.serviceWorker.addEventListener('controllerchange', fin);
          setTimeout(fin, 2000);
        });
      });
  }

  f.addEventListener('submit', function (ev) {
    ev.preventDefault();
    var url = normalize(inp.value);
    if (!url) return;
    var path;
    try {
      path = toPath(url);
    } catch (e) {
      st.textContent = 'URL が正しくありません';
      return;
    }
    var w = null;
    if (chk.checked && !framed) {
      // ユーザー操作の直後に同期的に開く (ポップアップブロック回避)
      w = window.open('about:blank', '_blank');
      if (!w) {
        st.textContent = 'ポップアップがブロックされました。許可してからもう一度お試しください。';
        return;
      }
    }
    st.textContent = '準備中...';
    ensureSW()
      .then(function () {
        var shell = '/~/shell?u=' + encodeURIComponent(path);
        var full = location.origin + shell;
        if (w) {
          var d = w.document;
          d.open();
          d.write(
            '<!doctype html><html><head><meta charset="utf-8"><title>about:blank</title>' +
              '<style>html,body{margin:0;height:100%;overflow:hidden;background:#fff}' +
              'iframe{border:0;width:100%;height:100%}</style></head><body>' +
              '<iframe src="' + full + '" allow="fullscreen; autoplay; clipboard-read; clipboard-write" allowfullscreen></iframe>' +
              '</body></html>'
          );
          d.close();
          st.textContent = '別タブ (about:blank) で開きました';
        } else {
          location.href = framed ? path : shell;
        }
      })
      .catch(function (e) {
        if (w) w.close();
        st.textContent = 'エラー: ' + e.message;
      });
  });
}

/* ========================================================================
 *  埋め込みリソース
 * ====================================================================== */

const SW_JS = '(' + swMain.toString() + ')();';
const CLIENT_JS = '(' + clientMain.toString() + ')();';

/* ---------- ナビゲーションバー付きの表示ページ (/~/shell) ---------- */
function shellMain() {
  window.__PX_SHELL = true;
  var a = document.getElementById('a');
  var tabsEl = document.getElementById('tabs');
  var holder = document.getElementById('holder');
  var plus = document.getElementById('np');
  var RX = /^\/go\/(https?)\/([^\/?#]+)(\/[^?#]*)?/;
  var MAX_TABS = 30;
  var tabs = [];
  var cur = null;
  var seq = 0;

  function normalize(v) {
    v = v.trim();
    if (!v) return null;
    if (/^https?:\/\//i.test(v)) return v;
    if (
      !/\s/.test(v) &&
      (/^[^\s\/?#:.]+(\.[^\s\/?#:.]+)+(:\d+)?([\/?#]\S*)?$/.test(v) || /^localhost(:\d+)?([\/?#]\S*)?$/i.test(v))
    ) {
      return 'https://' + v;
    }
    return 'https://duckduckgo.com/?q=' + encodeURIComponent(v);
  }
  function toPath(u) {
    var x = new URL(u);
    return '/go/' + x.protocol.slice(0, -1) + '/' + x.host + x.pathname + x.search + x.hash;
  }
  function ensureSW() {
    if (!('serviceWorker' in navigator)) return Promise.resolve();
    return navigator.serviceWorker
      .register('/sw.js', { scope: '/' })
      .then(function () {
        return navigator.serviceWorker.ready;
      })
      .then(function () {
        if (navigator.serviceWorker.controller) return;
        return new Promise(function (resolve) {
          var done = false;
          function fin() {
            if (!done) {
              done = true;
              resolve();
            }
          }
          navigator.serviceWorker.addEventListener('controllerchange', fin);
          setTimeout(fin, 2000);
        });
      });
  }

  /* ---------- タブ ---------- */
  function tabTitle(t) {
    try {
      var d = t.fr.contentDocument;
      if (d && d.title) return d.title;
      var m = RX.exec(t.fr.contentWindow.location.pathname);
      if (m) return m[2];
    } catch (e) {}
    return '新しいタブ';
  }
  function newTab(src, activate) {
    if (tabs.length >= MAX_TABS) return null;
    var t = { id: ++seq, last: null, title: '' };
    t.fr = document.createElement('iframe');
    t.fr.className = 'fr';
    t.fr.setAttribute('allow', 'fullscreen; autoplay; clipboard-read; clipboard-write');
    t.fr.setAttribute('allowfullscreen', '');
    t.fr.style.display = 'none';
    t.fr.src = src || '/';
    holder.appendChild(t.fr);

    t.el = document.createElement('div');
    t.el.className = 'tab';
    t.tt = document.createElement('span');
    t.tt.className = 't';
    t.tt.textContent = '新しいタブ';
    t.x = document.createElement('button');
    t.x.className = 'x';
    t.x.textContent = '×';
    t.x.title = '閉じる';
    t.el.appendChild(t.tt);
    t.el.appendChild(t.x);
    t.el.addEventListener('click', function () {
      setActive(t);
    });
    t.x.addEventListener('click', function (ev) {
      ev.stopPropagation();
      closeTab(t);
    });
    // 中ボタンで閉じる
    t.el.addEventListener('auxclick', function (ev) {
      if (ev.button === 1) closeTab(t);
    });
    tabsEl.insertBefore(t.el, plus);
    tabs.push(t);
    if (activate || !cur) setActive(t);
    return t;
  }
  function setActive(t) {
    cur = t;
    for (var i = 0; i < tabs.length; i++) {
      var on = tabs[i] === t;
      tabs[i].fr.style.display = on ? 'block' : 'none';
      tabs[i].el.className = 'tab' + (on ? ' on' : '');
    }
    a.value = '';
    show(true);
    try {
      t.el.scrollIntoView({ inline: 'nearest', block: 'nearest' });
    } catch (e) {}
  }
  function closeTab(t) {
    var i = tabs.indexOf(t);
    if (i < 0) return;
    tabs.splice(i, 1);
    try {
      t.fr.src = 'about:blank';
    } catch (e) {}
    t.fr.remove();
    t.el.remove();
    if (!tabs.length) {
      cur = null;
      newTab('/', true);
    } else if (cur === t) {
      setActive(tabs[Math.min(i, tabs.length - 1)]);
    }
  }
  plus.addEventListener('click', function () {
    var t = newTab('/', true);
    if (t) a.focus();
  });

  // 現在のタブのURLを入力欄に表示 / 全タブのタイトルを更新
  function show(force) {
    for (var i = 0; i < tabs.length; i++) {
      var t = tabs[i];
      var ti = tabTitle(t);
      if (ti !== t.title) {
        t.title = ti;
        t.tt.textContent = ti;
        t.el.title = ti;
      }
    }
    if (!cur) return;
    try {
      if (!force && document.activeElement === a) return;
      var l = cur.fr.contentWindow.location;
      var m = RX.exec(l.pathname);
      var u = m ? m[1] + '://' + m[2] + (m[3] || '/') + l.search + l.hash : '';
      if (a.value !== u) a.value = u;
    } catch (e) {}
  }
  setInterval(show, 500);

  function hist(fn) {
    try {
      fn(cur.fr.contentWindow);
    } catch (e) {}
  }
  document.getElementById('b').addEventListener('click', function () {
    hist(function (w) {
      w.history.back();
    });
  });
  document.getElementById('n').addEventListener('click', function () {
    hist(function (w) {
      w.history.forward();
    });
  });
  document.getElementById('r').addEventListener('click', function () {
    hist(function (w) {
      w.location.reload();
    });
  });
  document.getElementById('h').addEventListener('click', function () {
    if (cur) cur.fr.src = '/';
  });
  a.addEventListener('keydown', function (ev) {
    if (ev.key !== 'Enter' || !cur) return;
    var url = normalize(a.value);
    if (!url) return;
    try {
      cur.fr.src = toPath(url);
      a.blur();
    } catch (e) {}
  });

  /* ---------- デバッグ: iframe 内のログ受信 + 移動先URLの記録 ---------- */
  var logs = [];
  var dBtn = document.getElementById('d');
  var dPanel = document.getElementById('p');
  var dList = document.getElementById('l');
  function logColor(t) {
    if (/\] NAV /.test(t)) return '#6cb6ff';
    if (/\] document\.open/.test(t)) return '#ffa726';
    if (/\] LEAK遮断/.test(t)) return '#c792ea';
    if (/\] (JSエラー|LOAD失敗|HTTP \d|通信失敗|Promise拒否|console\.error|WebSocket失敗)/.test(t)) return '#ff6b6b';
    return '#eee';
  }
  function fill() {
    dList.textContent = '';
    for (var i = 0; i < logs.length; i++) {
      var d = document.createElement('div');
      d.style.cssText = 'margin-bottom:8px;color:' + logColor(logs[i]);
      d.textContent = logs[i];
      dList.appendChild(d);
    }
    dList.scrollTop = dList.scrollHeight;
  }
  function addLog(t) {
    if (logs.length >= 300) logs.shift();
    logs.push(t);
    dBtn.style.display = 'block';
    dBtn.textContent = '🐞 ' + logs.length;
    if (dPanel.style.display === 'flex') fill();
  }
  function stamp() {
    return '[' + new Date().toTimeString().slice(0, 8) + '] ';
  }
  window.addEventListener('message', function (ev) {
    var d = ev.data;
    if (!d) return;
    if (typeof d.pxlog === 'string') addLog(d.pxlog);
    else if (typeof d.pxopen === 'string' && /^\/go\/https?\/[^\/]/.test(d.pxopen)) newTab(d.pxopen, true);
  });
  setInterval(function () {
    for (var i = 0; i < tabs.length; i++) {
      var t = tabs[i];
      var h;
      try {
        h = t.fr.contentWindow.location.href;
      } catch (e) {
        h = '(アクセス不可)';
      }
      if (h !== t.last) {
        addLog(stamp() + 'NAV (タブ' + t.id + ') ' + h);
        t.last = h;
      }
    }
  }, 150);
  dBtn.addEventListener('click', function () {
    var open = dPanel.style.display === 'flex';
    dPanel.style.display = open ? 'none' : 'flex';
    if (!open) fill();
  });
  document.getElementById('pc').addEventListener('click', function () {
    var t = logs.join('\n\n');
    try {
      navigator.clipboard.writeText(t);
    } catch (e) {
      var ta = document.createElement('textarea');
      ta.value = t;
      document.body.appendChild(ta);
      ta.select();
      try {
        document.execCommand('copy');
      } catch (e2) {}
      ta.remove();
    }
  });
  document.getElementById('px').addEventListener('click', function () {
    logs = [];
    dList.textContent = '';
    dBtn.style.display = 'none';
    dPanel.style.display = 'none';
  });

  /* ---------- 外部への通信・画面移動をプロキシ内に閉じ込める ---------- */
  // (1) タブ (iframe) が外部サイトへ移動しようとした → CSP (frame-src 'self') が遮断 → プロキシ経由で開き直す
  document.addEventListener('securitypolicyviolation', function (ev) {
    try {
      var b = ev.blockedURI;
      var d = ev.violatedDirective || '';
      if (!/^https?:/i.test(b) || (d.indexOf('frame-src') !== 0 && d.indexOf('child-src') !== 0)) return;
      var target = null;
      for (var i = 0; i < tabs.length; i++) {
        try {
          void tabs[i].fr.contentWindow.location.href;
        } catch (e) {
          target = tabs[i];
          break;
        }
      }
      target = target || cur;
      addLog(stamp() + 'LEAK遮断 タブの外部移動を止めてプロキシ内で開きます ' + b);
      if (target) target.fr.src = toPath(b);
    } catch (e) {}
  });
  // (2) 外側ページ自体 (top) を外部へ移動させようとした → 止めて、現在のタブでプロキシ経由で開く
  try {
    if (window.navigation && navigation.addEventListener) {
      navigation.addEventListener('navigate', function (ev) {
        try {
          var u = new URL(ev.destination.url);
          if (u.origin === location.origin || !/^https?:$/.test(u.protocol)) return;
          if (ev.cancelable) ev.preventDefault();
          addLog(stamp() + 'LEAK遮断 外部への画面移動を止めてプロキシ内で開きます ' + u.href);
          if (cur) cur.fr.src = toPath(u.href);
        } catch (e) {}
      });
    }
  } catch (e) {}

  var q = new URLSearchParams(location.search).get('u');
  var start = q && /^\/go\/https?\/[^\/]/.test(q) ? q : '/';
  // 外側ページのURLは常に「/」に固定 (開いているサイトによって変わらない)
  try {
    history.replaceState(null, '', '/');
  } catch (e) {}
  ensureSW().then(function () {
    newTab(start, true);
  });
}

const SHELL_HTML = `<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Data Center</title>
<link rel="icon" type="image/svg+xml" href="/favicon.svg">
<style>
  *{box-sizing:border-box}
  html,body{margin:0;height:100%;background:#0f1117}
  #tabs{position:fixed;top:0;left:0;right:0;height:34px;display:flex;gap:4px;align-items:flex-end;padding:4px 8px 0;
        background:#0f1117;overflow-x:auto;overflow-y:hidden;font-family:system-ui,sans-serif}
  .tab{display:flex;align-items:center;gap:6px;width:180px;flex:none;height:30px;padding:0 6px 0 12px;border-radius:8px 8px 0 0;
       background:#1d2130;color:#aab0c0;font-size:12px;cursor:pointer;user-select:none}
  .tab:hover{background:#242938}
  .tab.on{background:#171a23;color:#fff}
  .tab .t{flex:1;min-width:0;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
  .tab .x{width:20px;height:20px;border:0;border-radius:10px;background:transparent;color:inherit;cursor:pointer;font-size:14px;line-height:1;padding:0;flex:none}
  .tab .x:hover{background:#3a4160}
  #np{width:28px;height:28px;margin-bottom:2px;border:0;border-radius:8px;background:transparent;color:#aab0c0;font-size:18px;cursor:pointer;flex:none}
  #np:hover{background:#242938;color:#fff}
  #bar{position:fixed;top:34px;left:0;right:0;height:44px;display:flex;gap:6px;align-items:center;padding:6px 8px;
       background:#171a23;border-bottom:1px solid #2b3040;font-family:system-ui,sans-serif}
  #bar button{width:34px;height:32px;border:0;border-radius:8px;background:#242938;color:#e8eaf0;font-size:16px;cursor:pointer;flex:none}
  #bar button:hover{background:#2f3550}
  #a{flex:1;min-width:0;height:32px;padding:0 14px;border-radius:16px;border:1px solid #2b3040;background:#0f1117;
     color:#e8eaf0;font-size:14px;outline:none}
  #a:focus{border-color:#5b8cff}
  #d{display:none;width:auto!important;padding:0 10px;background:#c62828!important;font-size:13px!important}
  #p{position:fixed;z-index:10;top:84px;right:8px;width:min(620px,94vw);height:min(420px,70vh);display:none;flex-direction:column;
     background:#111;color:#eee;border:1px solid #555;border-radius:8px;overflow:hidden;font:12px/1.5 monospace}
  #p .hd{display:flex;gap:6px;padding:6px;background:#222;align-items:center}
  #p .hd span{flex:1;color:#ffb86b}
  #p .hd button{width:auto;height:auto;padding:3px 8px;font:12px monospace}
  #l{flex:1;overflow:auto;padding:8px;white-space:pre-wrap;word-break:break-all}
  .fr{position:fixed;top:78px;left:0;right:0;bottom:0;width:100%;height:calc(100% - 78px);border:0;background:#fff}
</style>
</head>
<body>
<div id="tabs"><button id="np" title="新しいタブ">+</button></div>
<div id="bar">
  <button id="b" title="戻る">&#8592;</button>
  <button id="n" title="進む">&#8594;</button>
  <button id="r" title="再読み込み">&#10227;</button>
  <button id="h" title="ホーム">&#8962;</button>
  <input id="a" type="text" placeholder="URL または検索ワードを入力" autocomplete="off" spellcheck="false">
  <button id="d" title="デバッグログ">&#128030;</button>
</div>
<div id="p"><div class="hd"><span>Debug ログ (NAV = 移動先URLの記録)</span><button id="pc">コピー</button><button id="px">クリア</button></div><div id="l"></div></div>
<div id="holder"></div>
<script>(${shellMain.toString()})();</script>
</body>
</html>`;

/* ---------- ファビコン (黒背景 / 蛍光グリーンの ≫ / 白の _) ---------- */
const FAVICON_SVG =
  '<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 64 64">' +
  '<rect width="64" height="64" rx="12" fill="#000"/>' +
  '<g fill="none" stroke="#39ff14" stroke-width="6" stroke-linecap="round" stroke-linejoin="round">' +
  '<polyline points="10,18 24,32 10,46"/><polyline points="24,18 38,32 24,46"/></g>' +
  '<line x1="42" y1="48" x2="56" y2="48" stroke="#fff" stroke-width="6" stroke-linecap="round"/>' +
  '</svg>';

/* ---------- プロキシ経由のHTMLに付ける CSP: 外部への iframe 移動 / フォーム送信を遮断 ---------- */
const LEAK_CSP = "frame-src 'self' blob: data:; form-action 'self'";
const SHELL_CSP = "frame-src 'self'";

const INDEX_HTML = `<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Data Center</title>
<link rel="icon" type="image/svg+xml" href="/favicon.svg">
<style>
  :root{color-scheme:dark}
  *{box-sizing:border-box}
  html,body{height:100%;margin:0}
  body{display:flex;align-items:center;justify-content:center;background:#0f1117;color:#e8eaf0;
       font-family:system-ui,-apple-system,"Segoe UI","Hiragino Sans","Noto Sans JP",sans-serif}
  main{width:min(640px,92vw);text-align:center}
  h1{font-size:28px;font-weight:600;margin:0 0 24px;letter-spacing:.02em}
  form{display:flex;gap:8px}
  input[type=text]{flex:1;min-width:0;padding:14px 16px;font-size:16px;border-radius:12px;border:1px solid #2b3040;
       background:#171a23;color:inherit;outline:none}
  input[type=text]:focus{border-color:#5b8cff;box-shadow:0 0 0 3px rgba(91,140,255,.25)}
  button{padding:0 22px;font-size:16px;border:0;border-radius:12px;background:#5b8cff;color:#fff;cursor:pointer}
  button:hover{background:#4a7bf0}
  .chk{display:inline-flex;align-items:center;gap:8px;margin-top:16px;font-size:14px;color:#aab0c0;cursor:pointer;user-select:none}
  .st{min-height:1.4em;margin:14px 0 0;font-size:13px;color:#ffb86b}
  footer{position:fixed;left:0;right:0;bottom:0;padding:14px 16px;text-align:center;font-size:12px;line-height:1.7;color:#8a90a2}
  footer a{color:#8fb0ff;text-decoration:none}
  footer a:hover{text-decoration:underline}
</style>
</head>
<body>
<main>
  <h1>Data Center</h1>
  <form id="f" autocomplete="off">
    <input id="u" type="text" placeholder="コマンドを待機中…" autofocus required>
    <button type="submit">開く</button>
  </form>
  <label class="chk"><input type="checkbox" id="c"> 履歴を残さない (about:blank で表示)</label>
  <p id="s" class="st"></p>
  <p style="margin:18px 0 0;font-size:14px"><a href="/~/yt" style="color:#8fb0ff;text-decoration:none">&#9654; YouTube 検索モード (yt-dlp)</a></p>
  <noscript>JavaScript を有効にしてください。</noscript>
</main>
<footer>
  &copy;2026 <a href="https://github.com/20250199-tomohiro" target="_blank" rel="noopener">20250199-tomohiro</a>&amp;<a href="http://www.claude.ai" target="_blank" rel="noopener">Claude</a><br>
  このプロキシは<a href="https://github.com/20250199-tomohiro/project-claude-proxy-v2" target="_blank" rel="noopener">Github</a>でオープンソースとして公開されており、誰でもインストール、開発に参加することができます。
</footer>
<script>(${indexMain.toString()})();</script>
</body>
</html>`;

/* ========================================================================
 *  ユーティリティ
 * ====================================================================== */

function isPrivateIp(ip) {
  if (net.isIPv4(ip)) {
    const [a, b] = ip.split('.').map(Number);
    return (
      a === 0 || a === 10 || a === 127 || (a === 169 && b === 254) || (a === 172 && b >= 16 && b <= 31) ||
      (a === 192 && b === 168) || (a === 100 && b >= 64 && b <= 127) || a >= 224
    );
  }
  if (net.isIPv6(ip)) {
    const l = ip.toLowerCase();
    if (l === '::1' || l === '::' || l.startsWith('fc') || l.startsWith('fd') || l.startsWith('fe80')) return true;
    const m = l.match(/^::ffff:(\d+\.\d+\.\d+\.\d+)$/);
    if (m) return isPrivateIp(m[1]);
    return false;
  }
  return true;
}

// SSRF 対策: 名前解決の結果がプライベートアドレスなら拒否
function safeLookup(hostname, options, cb) {
  dns.lookup(hostname, options, (err, address, family) => {
    if (err) return cb(err);
    if (!ALLOW_PRIVATE) {
      const list = Array.isArray(address) ? address : [{ address, family }];
      for (const a of list) if (isPrivateIp(a.address)) return cb(new Error('blocked address'));
    }
    cb(null, address, family);
  });
}

function hostBlocked(hostname) {
  if (ALLOW_PRIVATE) return false;
  const h = hostname.replace(/^\[|\]$/g, '');
  if (net.isIP(h)) return isPrivateIp(h);
  return /^localhost$|\.localhost$|\.internal$/i.test(h);
}

const agentOpts = { keepAlive: true, lookup: safeLookup, maxSockets: 256 };
const httpAgent = new http.Agent(agentOpts);
const httpsAgent = new https.Agent(agentOpts);

// Basic 認証に成功したら Cookie も発行する。
// Google などのページは fetch に独自の Authorization ヘッダ (SAPISIDHASH 等) を付けるため、
// ブラウザ自動の Basic 認証ヘッダが上書きされて 401 になる。Cookie なら上書きされない。
const AUTH_COOKIE = '__pxauth';
const AUTH_TOKEN = BASIC_AUTH ? crypto.createHash('sha256').update('pxauth:' + BASIC_AUTH).digest('hex') : '';

function authOk(req, res) {
  if (!BASIC_AUTH) return true;
  const ck = parseCookieHeader(req.headers.cookie)[AUTH_COOKIE];
  if (ck && ck.length === AUTH_TOKEN.length && crypto.timingSafeEqual(Buffer.from(ck), Buffer.from(AUTH_TOKEN))) return true;
  const h = req.headers.authorization || '';
  if (!h.startsWith('Basic ')) return false;
  const a = Buffer.from(Buffer.from(h.slice(6), 'base64').toString());
  const b = Buffer.from(BASIC_AUTH);
  const ok = a.length === b.length && crypto.timingSafeEqual(a, b);
  if (ok && res) {
    addSetCookie(res, `${AUTH_COOKIE}=${AUTH_TOKEN}; Path=/; HttpOnly; SameSite=Lax; Max-Age=2592000${isSecure(req) ? '; Secure' : ''}`);
  }
  return ok;
}

function addSetCookie(res, c) {
  const prev = res.getHeader('Set-Cookie');
  res.setHeader('Set-Cookie', prev ? [].concat(prev, c) : c);
}

function isSecure(req) {
  return req.headers['x-forwarded-proto'] === 'https' || !!(req.socket && req.socket.encrypted);
}

/* ---- プロキシURL <-> 元URL ---- */

// "/go/https/example.com/a?b=1" -> URL("https://example.com/a?b=1")
function parseProxyPath(raw) {
  const m = /^\/go\/(https?)\/([^\/?#]+)([^]*)$/.exec(raw);
  if (!m) return null;
  let rest = m[3] || '/';
  if (rest[0] === '?') rest = '/' + rest;
  try {
    return new URL(m[1] + '://' + m[2] + rest);
  } catch (e) {
    return null;
  }
}

// Referer など (絶対URL or パス) がプロキシURLなら元のURL文字列を返す
function decodeProxyUrl(str, selfHost) {
  try {
    const u = new URL(str, 'http://' + selfHost);
    if (u.host.toLowerCase() !== String(selfHost).toLowerCase()) return null;
    const t = parseProxyPath(u.pathname + u.search);
    return t ? t.href : null;
  } catch (e) {
    return null;
  }
}

const SKIP_URL = /^(data|blob|javascript|mailto|tel|about|sms|file|ws|wss):/i;
function proxify(val, base, isHtml) {
  let v = String(val);
  if (isHtml) v = v.replace(/&amp;/gi, '&');
  v = v.trim();
  if (!v || v[0] === '#' || SKIP_URL.test(v) || /^\/go\/https?\/[^/]/.test(v)) return null;
  let u;
  try {
    u = new URL(v, base);
  } catch (e) {
    return null;
  }
  if (u.protocol !== 'http:' && u.protocol !== 'https:') return null;
  return PREFIX + u.protocol.slice(0, -1) + '/' + u.host + u.pathname + u.search + u.hash;
}
function px(val, base) {
  const r = proxify(val, base, true);
  return r === null ? val : r.replace(/&/g, '&amp;');
}

/* ========================================================================
 *  ① Cookie jar
 * ====================================================================== */

const sessions = new Map(); // sid -> { jar:[], last:string|null, t:number }

function parseCookieHeader(h) {
  const o = {};
  String(h || '').split(';').forEach((p) => {
    const i = p.indexOf('=');
    if (i < 0) return;
    o[p.slice(0, i).trim()] = p.slice(i + 1).trim();
  });
  return o;
}

function getSession(req, res, create) {
  const sid = parseCookieHeader(req.headers.cookie)[SID_NAME];
  let s = sid && sessions.get(sid);
  if (!s && create) {
    const nsid = crypto.randomBytes(18).toString('hex');
    s = { jar: [], last: null, t: Date.now() };
    sessions.set(nsid, s);
    if (res) {
      addSetCookie(
        res,
        `${SID_NAME}=${nsid}; Path=/; HttpOnly; SameSite=Lax; Max-Age=2592000${isSecure(req) ? '; Secure' : ''}`
      );
    }
  }
  if (s) s.t = Date.now();
  return s || null;
}

setInterval(() => {
  const limit = Date.now() - 3 * 24 * 3600 * 1000;
  for (const [k, s] of sessions) if (s.t < limit) sessions.delete(k);
}, 10 * 60 * 1000).unref();

function defaultPath(p) {
  if (!p || p[0] !== '/') return '/';
  const i = p.lastIndexOf('/');
  return i <= 0 ? '/' : p.slice(0, i);
}
function pathMatch(reqPath, cp) {
  if (reqPath === cp) return true;
  if (reqPath.startsWith(cp)) return cp.endsWith('/') || reqPath[cp.length] === '/';
  return false;
}

function storeSetCookie(sess, str, url) {
  const parts = String(str).split(';');
  const nv = parts.shift();
  const i = nv.indexOf('=');
  const name = i < 0 ? '' : nv.slice(0, i).trim();
  const value = i < 0 ? nv.trim() : nv.slice(i + 1).trim();
  const host = url.hostname.toLowerCase();
  const c = { name, value, domain: host, hostOnly: true, path: defaultPath(url.pathname), secure: false, httpOnly: false, exp: 0 };
  let hasMaxAge = false;
  for (const p of parts) {
    const j = p.indexOf('=');
    const k = (j < 0 ? p : p.slice(0, j)).trim().toLowerCase();
    const v = j < 0 ? '' : p.slice(j + 1).trim();
    if (k === 'domain' && v) {
      const d = v.replace(/^\./, '').toLowerCase();
      if (host === d || host.endsWith('.' + d)) {
        c.domain = d;
        c.hostOnly = false;
      }
    } else if (k === 'path' && v[0] === '/') c.path = v;
    else if (k === 'secure') c.secure = true;
    else if (k === 'httponly') c.httpOnly = true;
    else if (k === 'max-age') {
      const n = parseInt(v, 10);
      if (!isNaN(n)) {
        hasMaxAge = true;
        c.exp = n <= 0 ? 1 : Date.now() + n * 1000;
      }
    } else if (k === 'expires' && !hasMaxAge) {
      const t = Date.parse(v);
      if (!isNaN(t)) c.exp = t || 1;
    }
  }
  sess.jar = sess.jar.filter((x) => !(x.name === c.name && x.domain === c.domain && x.path === c.path && x.hostOnly === c.hostOnly));
  if (c.exp && c.exp <= Date.now()) return; // 削除指示
  sess.jar.push(c);
  if (sess.jar.length > 3000) sess.jar.shift();
}

function cookieHeader(sess, url, forJs) {
  if (!sess) return '';
  const now = Date.now();
  const host = url.hostname.toLowerCase();
  const secure = url.protocol === 'https:' || url.protocol === 'wss:';
  sess.jar = sess.jar.filter((c) => !c.exp || c.exp > now);
  const out = sess.jar.filter((c) => {
    if (c.secure && !secure) return false;
    if (forJs && c.httpOnly) return false;
    if (c.hostOnly ? host !== c.domain : !(host === c.domain || host.endsWith('.' + c.domain))) return false;
    return pathMatch(url.pathname, c.path);
  });
  out.sort((a, b) => b.path.length - a.path.length);
  return out.map((c) => (c.name ? c.name + '=' + c.value : c.value)).join('; ');
}

/* ========================================================================
 *  HTML / CSS 書き換え
 * ====================================================================== */

function decodeText(buf, ct, isHtml) {
  let cs = (/charset\s*=\s*["']?([\w-]+)/i.exec(ct) || [])[1];
  if (!cs && isHtml) {
    const m = /<meta[^>]+charset\s*=\s*["']?([\w-]+)/i.exec(buf.slice(0, 4096).toString('latin1'));
    if (m) cs = m[1];
  }
  try {
    return new TextDecoder((cs || 'utf-8').toLowerCase()).decode(buf);
  } catch (e) {
    return buf.toString('utf8');
  }
}

function rewriteCss(css, base) {
  css = css.replace(/url\(\s*(['"]?)([^'")]+?)\1\s*\)/gi, (m, q, u) => {
    const r = proxify(u, base, false);
    return r === null ? m : 'url(' + q + r + q + ')';
  });
  css = css.replace(/@import\s+(['"])([^'"]+)\1/gi, (m, q, u) => {
    const r = proxify(u, base, false);
    return r === null ? m : '@import ' + q + r + q;
  });
  return css;
}

const ATTR_RE = /(\s)(src|href|action|poster|formaction|data|background)(\s*=\s*)("[^"]*"|'[^']*'|[^\s"'>`=<]+)/gi;
const SRCSET_RE = /(\s)((?:img)?srcset)(\s*=\s*)("[^"]*"|'[^']*')/gi;
const STYLE_RE = /(\s)(style)(\s*=\s*)("[^"]*"|'[^']*')/gi;

function rewriteAttrs(str, base) {
  return str
    .replace(/\sintegrity\s*=\s*("[^"]*"|'[^']*'|[^\s>]+)/gi, '')
    .replace(/<meta\b[^>]*http-equiv\s*=\s*["']?refresh[^>]*>/gi, (tag) =>
      tag.replace(/(url\s*=\s*)([^"';>]+)/i, (m, a, b) => a + px(b, base))
    )
    .replace(ATTR_RE, (m, pre, name, eq, val) => {
      let q = '';
      let v = val;
      if (v[0] === '"' || v[0] === "'") {
        q = v[0];
        v = v.slice(1, -1);
      }
      return pre + name + eq + q + px(v, base) + q;
    })
    .replace(SRCSET_RE, (m, pre, name, eq, val) => {
      const q = val[0];
      const inner = val
        .slice(1, -1)
        .split(',')
        .map((c) => {
          const p = c.trim().split(/\s+/);
          if (p[0]) p[0] = px(p[0], base);
          return p.join(' ');
        })
        .join(', ');
      return pre + name + eq + q + inner + q;
    })
    .replace(STYLE_RE, (m, pre, name, eq, val) => {
      const q = val[0];
      return pre + name + eq + q + rewriteCss(val.slice(1, -1), base) + q;
    });
}

function rewriteHtml(html, baseHref, cookieStr) {
  let base = baseHref;
  const bm = /<base\b[^>]*?\shref\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s>]+))/i.exec(html);
  if (bm) {
    try {
      base = new URL(bm[1] || bm[2] || bm[3] || '', baseHref).href;
    } catch (e) {}
  }
  html = html.replace(/<meta\b[^>]*http-equiv\s*=\s*["']?content-security-policy[^>]*>/gi, '');

  let out = '';
  let last = 0;
  let m;
  const blockRe = /<script\b[\s\S]*?<\/script\s*>|<style\b[\s\S]*?<\/style\s*>/gi;
  while ((m = blockRe.exec(html))) {
    out += rewriteAttrs(html.slice(last, m.index), base);
    const blk = m[0];
    const open = /^<[^>]*>/.exec(blk)[0];
    const rest = blk.slice(open.length);
    if (/^<style/i.test(blk)) {
      const ci = rest.search(/<\/style\s*>/i);
      out += rewriteAttrs(open, base) + rewriteCss(rest.slice(0, ci), base) + rest.slice(ci);
    } else {
      out += rewriteAttrs(open, base) + rest; // <script> の中身は触らない (クライアントフックが処理)
    }
    last = m.index + blk.length;
  }
  out += rewriteAttrs(html.slice(last), base);

  // デバッグオーバーレイ (recaptcha-debug-overlay.js) は client.js より先に読み込む
  const inj =
    '<script>window.__PX_COOKIE=' + JSON.stringify(cookieStr || '').replace(/</g, '\\u003c') + ';</script>' +
    (RC_DEBUG && RC_OVERLAY_SRC ? '<script src="/~/rc-overlay.js"></script>' : '') +
    '<script src="/~/client.js"></script>';
  let mm = /<head(\s[^>]*)?>/i.exec(out) || /<html(\s[^>]*)?>/i.exec(out);
  if (mm) {
    const at = mm.index + mm[0].length;
    return out.slice(0, at) + inj + out.slice(at);
  }
  mm = /^\s*<!doctype[^>]*>/i.exec(out);
  if (mm) return out.slice(0, mm[0].length) + inj + out.slice(mm[0].length);
  return inj + out;
}

function decompressor(enc) {
  enc = String(enc).split(',')[0].trim().toLowerCase();
  if (enc === 'gzip' || enc === 'x-gzip') return zlib.createGunzip();
  if (enc === 'deflate') return zlib.createInflate();
  if (enc === 'br') return zlib.createBrotliDecompress();
  return null;
}

/* ========================================================================
 *  プロキシ本体 (HTTP)
 * ====================================================================== */

const SKIP_REQ = /^(render-|host|connection|keep-alive|proxy-|te$|trailer|upgrade$|transfer-encoding|sec-fetch-|x-forwarded-|x-render|x-request|rndr|cf-|cdn-loop|true-client-ip|forwarded|via|x-real-ip|accept-encoding|cookie|referer|origin|content-length$)/i;
const SKIP_RES = /^(set-cookie|content-security-policy|content-security-policy-report-only|x-frame-options|strict-transport-security|public-key-pins|public-key-pins-report-only|cross-origin-opener-policy|cross-origin-embedder-policy|cross-origin-resource-policy|connection|keep-alive|transfer-encoding|upgrade|proxy-authenticate|proxy-authorization|te|trailer|alt-svc|link|report-to|nel|expect-ct|clear-site-data|access-control-.*)$/i;

function buildUpstreamHeaders(req, target, sess) {
  const h = {};
  for (const [k, v] of Object.entries(req.headers)) {
    if (SKIP_REQ.test(k)) continue;
    // プロキシ自身の Basic 認証だけ除外。Google の SAPISIDHASH など他の Authorization は転送する
    if (k === 'authorization' && BASIC_AUTH && /^basic\s/i.test(String(v))) continue;
    h[k] = v;
  }
  if (req.headers['content-length'] !== undefined) h['content-length'] = req.headers['content-length'];
  h.host = target.host;
  h['accept-encoding'] = 'gzip, deflate, br';

  const ck = cookieHeader(sess, target, false);
  if (ck) h.cookie = ck;

  // ⑥ Referer / Origin の転送 (プロキシURL -> 元URL)
  const self = req.headers.host;
  const ref = req.headers.referer ? decodeProxyUrl(req.headers.referer, self) : null;
  if (ref) h.referer = ref;
  if (req.headers.origin !== undefined) {
    let o = target.origin;
    if (ref) {
      try {
        o = new URL(ref).origin;
      } catch (e) {}
    }
    h.origin = o;
  }

  // Sec-Fetch-*: ブラウザが付けた値は「プロキシ ↔ プロキシ」の関係なので、元サイトから見た関係に直して送る
  //  (Google は Sec-Fetch-* の欠落・不整合も不審な環境の判定材料にする)
  const sfm = req.headers['sec-fetch-mode'];
  const sfd = req.headers['sec-fetch-dest'];
  if (sfm) {
    h['sec-fetch-mode'] = sfm;
    if (sfd) h['sec-fetch-dest'] = sfd;
    if (req.headers['sec-fetch-user']) h['sec-fetch-user'] = req.headers['sec-fetch-user'];
    let site = 'same-origin';
    if (!ref) {
      if (sfm === 'navigate') {
        // 本物のブラウザでは iframe / frame の移動で none になることはない (埋め込み元は別サイト扱い)
        site = sfd === 'iframe' || sfd === 'frame' || sfd === 'embed' || sfd === 'object' ? 'cross-site' : 'none';
      } else {
        site = 'same-origin';
      }
    } else {
      try {
        const ro = new URL(ref);
        if (ro.origin === target.origin) site = 'same-origin';
        else {
          const reg = (x) => x.hostname.split('.').slice(-2).join('.');
          site = reg(ro) === reg(target) ? 'same-site' : 'cross-site';
        }
      } catch (e) {}
    }
    h['sec-fetch-site'] = site;
  }

  // Chrome のヘッダ順に並べ替える (Google は順序もブラウザかどうかの判定材料にする)
  const ORDER = [
    'host', 'connection', 'content-length', 'pragma', 'cache-control',
    'sec-ch-ua', 'sec-ch-ua-mobile', 'sec-ch-ua-platform', 'upgrade-insecure-requests',
    'user-agent', 'content-type', 'accept',
    'sec-fetch-site', 'sec-fetch-mode', 'sec-fetch-user', 'sec-fetch-dest',
    'origin', 'referer', 'accept-encoding', 'accept-language', 'cookie'
  ];
  const sorted = {};
  for (const k of ORDER) if (h[k] !== undefined) sorted[k] = h[k];
  for (const k of Object.keys(h)) if (sorted[k] === undefined) sorted[k] = h[k];
  return sorted;
}

function errorPage(res, code, msg) {
  if (res.headersSent) {
    res.destroy();
    return;
  }
  const esc = String(msg).replace(/[&<>]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;' }[c]));
  res.writeHead(code, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-store' });
  res.end(`<!doctype html><meta charset="utf-8"><title>Proxy error</title>
<body style="font-family:system-ui;background:#0f1117;color:#e8eaf0;padding:40px"><h2>プロキシエラー (${code})</h2><p>${esc}</p><p><a style="color:#8fb0ff" href="/">トップへ戻る</a></p></body>`);
}

function handleProxy(req, res, target) {
  const sess = getSession(req, res, true);
  if (YT_HOST_RE.test(target.hostname)) seedYtCookies(sess);

  // reCAPTCHA 互換: anchor/bframe の co (埋め込み元オリジン) をプロキシ → 実ページのオリジンへ書き換える
  const rc = getRc(req);
  const rcIs = !!(rc && rc.isRecaptchaUrl(target));
  let rcCtx = null;
  let rcReferer = null;
  if (rcIs) {
    let pageUrl = null;
    try {
      const ps = req.headers.referer ? decodeProxyUrl(req.headers.referer, req.headers.host) : null;
      pageUrl = ps ? new URL(ps) : null;
    } catch (e) {}
    // 親が reCAPTCHA 自身 (anchor → bframe 等) のときは、直近に開いた通常ページを埋め込み元とみなす
    if ((!pageUrl || rc.isRecaptchaUrl(pageUrl)) && sess && sess.lastPage) {
      try {
        pageUrl = new URL(sess.lastPage);
      } catch (e) {}
    }
    if (pageUrl && rc.isRecaptchaUrl(pageUrl)) pageUrl = null;
    rcCtx = { realUrl: target, pageUrl, isRecaptcha: true };
    try {
      const r = rc.rewriteRequest(rcCtx, new Headers());
      target = r.url;
      rcReferer = r.headers.get('referer');
    } catch (e) {}
  }

  const isHttps = target.protocol === 'https:';
  const upHeaders = buildUpstreamHeaders(req, target, sess);
  if (rcReferer) upHeaders.referer = rcReferer;

  const up = (isHttps ? https : http).request(
    {
      hostname: target.hostname.replace(/^\[|\]$/g, ''),
      port: target.port || (isHttps ? 443 : 80),
      path: target.pathname + target.search,
      method: req.method,
      headers: upHeaders,
      agent: isHttps ? httpsAgent : httpAgent
    },
    (ur) => {
      clearTimeout(timer);
      const status = ur.statusCode;
      // Google 宛ての通信をサーバー側で記録 (Cookie は名前だけ。値は残さない)
      if (RC_DEBUG && GOOGLE_RE.test(target.hostname)) {
        const sn = [].concat(ur.headers['set-cookie'] || []).map((s) => String(s).split('=')[0]).join(',');
        const cn = upHeaders.cookie ? upHeaders.cookie.split(';').map((s) => s.trim().split('=')[0]).join(',') : '';
        const loc = ur.headers.location ? ' -> ' + String(ur.headers.location).split('?')[0].slice(0, 100) : '';
        const sf = [upHeaders['sec-fetch-site'], upHeaders['sec-fetch-mode'], upHeaders['sec-fetch-dest']].join('/');
        const wa = ur.headers['www-authenticate'] ? ' www-auth=' + String(ur.headers['www-authenticate']).slice(0, 80) : '';
        pxLog(
          `[google] ${req.method} ${status} ${target.hostname}${target.pathname.slice(0, 70)}${loc} | sent=[${cn}] set=[${sn}] sf=${sf} ref=${upHeaders.referer ? 'y' : 'n'} origin=${upHeaders.origin ? 'y' : 'n'}${wa}`
        );
        if (status >= 400) {
          // 失敗したときだけ、送ったヘッダ名・返ってきたヘッダ名・本文の見出し部分を記録する (値は記録しない)
          pxLog(`[google-hdr] ${status} req-h=[${Object.keys(upHeaders).join(',')}] res-h=[${Object.keys(ur.headers).join(',')}] ct=${ur.headers['content-type'] || ''}`);
          const bufs = [];
          let got = 0;
          ur.on('data', (c) => {
            if (got < 65536) {
              bufs.push(c);
              got += c.length;
            }
          });
          ur.on('end', () => {
            try {
              let b = Buffer.concat(bufs);
              const e = String(ur.headers['content-encoding'] || '').toLowerCase();
              if (e === 'gzip' || e === 'x-gzip') b = zlib.gunzipSync(b);
              else if (e === 'br') b = zlib.brotliDecompressSync(b);
              else if (e === 'deflate') b = zlib.inflateSync(b);
              const txt = b
                .toString('utf8')
                .replace(/<script[\s\S]*?<\/script>|<style[\s\S]*?<\/style>/gi, '')
                .replace(/<[^>]+>/g, ' ')
                .replace(/\s+/g, ' ')
                .trim()
                .slice(0, 300);
              pxLog(`[google-body] ${status} ${target.pathname.slice(0, 50)} ${txt}`);
            } catch (err) {
              pxLog('[google-body] 本文を読めませんでした: ' + err.message);
            }
          });
        }
      }
      if (rcIs) {
        try {
          rc.rewriteResponse(rcCtx, new Response(null, { status })); // ログ記録のみ (ヘッダ除去はこの後の処理で実施済み)
        } catch (e) {}
      }

      // ① Set-Cookie は jar に保存 (ブラウザへは渡さない)
      const sc = ur.headers['set-cookie'];
      if (sc && sess) for (const s of sc) storeSetCookie(sess, s, target);

      const h = {};
      for (const [k, v] of Object.entries(ur.headers)) {
        if (!SKIP_RES.test(k)) h[k] = v;
      }
      if (ur.headers.location) {
        const r = proxify(ur.headers.location, target.href, false);
        if (r) h.location = r;
      }
      if (h.refresh) {
        h.refresh = String(h.refresh).replace(/(url\s*=\s*)(.+)$/i, (m, a, b) => a + (proxify(b.trim(), target.href, false) || b));
      }

      const ct = String(ur.headers['content-type'] || '').toLowerCase();
      const enc = String(ur.headers['content-encoding'] || '').toLowerCase();
      const isHtml = /text\/html|application\/xhtml\+xml/.test(ct);
      const isCss = /text\/css/.test(ct);
      // 外部への iframe 移動・フォーム送信をブラウザ側で遮断 (プロキシ内への付け替えはクライアントが行う)
      if (isHtml) h['content-security-policy'] = LEAK_CSP;
      const len = parseInt(ur.headers['content-length'], 10);
      const dec = enc && enc !== 'identity' ? decompressor(enc) : null;
      const canRewrite =
        (isHtml || isCss) &&
        req.method !== 'HEAD' &&
        ![204, 206, 304].includes(status) &&
        !(len > MAX_REWRITE) &&
        (!enc || enc === 'identity' || dec);

      if (!canRewrite) {
        // ② 動画・大容量: 一切バッファせずストリーム中継 (Range / 206 もそのまま)
        res.writeHead(status, h);
        ur.pipe(res);
        ur.on('error', () => res.destroy());
        return;
      }

      if (isHtml && sess) {
        sess.last = target.origin;
        if (!rcIs) sess.lastPage = target.origin; // reCAPTCHA の埋め込み元ページ候補
      }

      let stream = ur;
      if (dec) {
        stream = ur.pipe(dec);
        delete h['content-encoding'];
        ur.on('error', (e) => stream.destroy(e));
      }
      delete h['content-length'];

      const chunks = [];
      let size = 0;
      let failed = false;
      const fail = (e) => {
        if (failed) return;
        failed = true;
        ur.destroy();
        errorPage(res, 502, '応答の処理に失敗しました: ' + e.message);
      };
      stream.on('data', (c) => {
        size += c.length;
        if (size > MAX_REWRITE) return fail(new Error('too large'));
        chunks.push(c);
      });
      stream.on('error', fail);
      stream.on('end', () => {
        if (failed) return;
        let body;
        try {
          const text = decodeText(Buffer.concat(chunks), ct, isHtml);
          body = isHtml
            ? rewriteHtml(text, target.href, cookieHeader(sess, target, true))
            : rewriteCss(text, target.href);
        } catch (e) {
          return fail(e);
        }
        const buf = Buffer.from(body, 'utf8');
        h['content-type'] = (ur.headers['content-type'] || (isHtml ? 'text/html' : 'text/css')).replace(/;\s*charset=[^;]*/i, '') + '; charset=utf-8';
        h['content-length'] = buf.length;
        if (isHtml) {
          delete h.etag;
          delete h['last-modified'];
          h['cache-control'] = 'no-cache';
        }
        res.writeHead(status, h);
        res.end(buf);
      });
    }
  );

  const timer = setTimeout(() => up.destroy(new Error('接続先が応答しません (タイムアウト)')), UPSTREAM_TIMEOUT);
  up.on('error', (e) => {
    clearTimeout(timer);
    errorPage(res, 502, e.message);
  });
  res.on('close', () => {
    if (!res.writableEnded) up.destroy();
  });
  req.pipe(up);
}

/* ---- ⑤ サーバー側の取りこぼし救済 ---- */
function rescue(req, res) {
  let base = null;
  if (req.headers.referer) {
    const t = decodeProxyUrl(req.headers.referer, req.headers.host);
    if (t) base = new URL(t).origin;
  }
  if (!base) {
    const s = getSession(req, null, false);
    if (s && s.last) base = s.last;
  }
  if (!base) {
    res.writeHead(404, { 'content-type': 'text/plain; charset=utf-8' });
    res.end('Not found');
    return;
  }
  const u = new URL(base);
  res.writeHead(307, { location: PREFIX + u.protocol.slice(0, -1) + '/' + u.host + req.url, 'cache-control': 'no-store' });
  res.end();
}

/* ========================================================================
 *  HTTP サーバー
 * ====================================================================== */

function readBody(req, limit) {
  return new Promise((resolve, reject) => {
    const chunks = [];
    let n = 0;
    req.on('data', (c) => {
      n += c.length;
      if (n > limit) {
        reject(new Error('too large'));
        req.destroy();
        return;
      }
      chunks.push(c);
    });
    req.on('end', () => resolve(Buffer.concat(chunks).toString('utf8')));
    req.on('error', reject);
  });
}

/* ========================================================================
 *  YouTube 対応
 *
 *  YouTube 本体のページはプロキシ URL (/go/https/www.youtube.com/...) の下では SPA が
 *  location.pathname からページを判定できず壊れやすい。そのため
 *    ・トップ / 検索 / チャンネル等 : 通常どおりプロキシ (リンクはクライアント側で通常遷移に変換)
 *    ・動画 (/watch /shorts /live youtu.be) : 専用プレーヤーに差し替え
 *  専用プレーヤーは yt-dlp (render.yaml のビルドで bin/yt-dlp に取得) で動画の直リンクを解決し、
 *  このサーバーが中継する (googlevideo の URL は取得元 IP に紐づくため、必ずサーバー経由にする)。
 *
 *  環境変数
 *   YT_DLP           yt-dlp のパス (既定: ./bin/yt-dlp)
 *   YT_COOKIES_FILE  Netscape 形式の cookies.txt (「ボットではないことを確認」と出る場合の対策・任意)
 *   YT_MAX_JOBS      yt-dlp の同時実行数 (既定 2)
 * ====================================================================== */

const YT_HOST_RE = /(^|\.)(youtube\.com|youtu\.be|youtube-nocookie\.com)$/i;
const YT_DLP = process.env.YT_DLP || pathMod.join(__dirname, 'bin', 'yt-dlp');
const YT_MAX = Math.max(1, parseInt(process.env.YT_MAX_JOBS, 10) || 2);
const YT_TTL = 90 * 60 * 1000; // 解決した直リンクを使い回す時間 (リンク自体は数時間有効)
const YT_UA = 'Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/131.0.0.0 Safari/537.36';
// 新しい yt-dlp は YouTube の n 署名の解読に JS ランタイムが必要 (Node はこのサーバー自身のものを使う)
const YT_RT_ARGS = ['--js-runtimes', 'node:' + process.execPath, '--remote-components', 'ejs:github'];

// cookies.txt は yt-dlp が書き戻すことがあるため、書き込み可能な場所へコピーして使う
let YT_COOKIES = '';
if (process.env.YT_COOKIES_FILE) {
  try {
    YT_COOKIES = pathMod.join(os.tmpdir(), 'yt-cookies.txt');
    fs.copyFileSync(process.env.YT_COOKIES_FILE, YT_COOKIES);
  } catch (e) {
    console.warn('[yt] YT_COOKIES_FILE を読み込めませんでした: ' + e.message);
    YT_COOKIES = '';
  }
}

const ytCache = new Map(); // id -> { t, info, fmts }
const ytJobs = new Map(); // id -> Promise (同じ動画の同時解決をまとめる)
const ytQueue = [];
let ytRunning = 0;

function ytAcquire() {
  return new Promise((resolve) => {
    if (ytRunning < YT_MAX) {
      ytRunning++;
      resolve();
    } else ytQueue.push(resolve);
  });
}
function ytRelease() {
  const next = ytQueue.shift();
  if (next) next();
  else ytRunning--;
}

function ytJson(res, code, obj) {
  if (res.headersSent) return res.destroy();
  res.writeHead(code, { 'content-type': 'application/json; charset=utf-8', 'cache-control': 'no-store' });
  res.end(JSON.stringify(obj));
}

function ytCleanErr(s) {
  const lines = String(s || '')
    .replace(/\x1b\[[0-9;]*m/g, '')
    .split('\n')
    .map((l) => l.trim())
    .filter(Boolean);
  const err = lines.filter((l) => /^ERROR/i.test(l));
  return (err.length ? err.slice(-2) : lines.slice(-2)).join(' ').slice(0, 500) || 'yt-dlp が失敗しました';
}

// yt-dlp に実行権限が無い (EACCES) とき: chmod し、それも駄目なら書き込み可能な場所へコピーして使う
let ytBin = YT_DLP;
let ytFixTried = false;
function ytFixBin() {
  try {
    fs.chmodSync(ytBin, 0o755);
    return true;
  } catch (e) {}
  try {
    const t = pathMod.join(os.tmpdir(), 'yt-dlp');
    fs.copyFileSync(ytBin, t);
    fs.chmodSync(t, 0o755);
    ytBin = t;
    return true;
  } catch (e) {}
  return false;
}
if (fs.existsSync(YT_DLP)) {
  try {
    fs.accessSync(YT_DLP, fs.constants.X_OK);
  } catch (e) {
    ytFixTried = true;
    console.warn('[yt] yt-dlp に実行権限がありません。付与します: ' + (ytFixBin() ? 'OK' : '失敗'));
  }
}

function ytExec(target, extra) {
  return new Promise((resolve, reject) => {
    const args = ['-J', '--no-warnings', '--socket-timeout', '20', '--cache-dir', pathMod.join(os.tmpdir(), 'yt-dlp-cache')].concat(extra);
    if (YT_COOKIES) args.push('--cookies', YT_COOKIES);
    args.push(target);
    execFile(ytBin, args, { timeout: 120000, maxBuffer: 64 * 1024 * 1024, env: process.env }, (err, stdout, stderr) => {
      if (err && err.code === 'EACCES' && !ytFixTried) {
        ytFixTried = true;
        if (ytFixBin()) return ytExec(target, extra).then(resolve, reject);
      }
      if (err) {
        const e = new Error(
          err.code === 'ENOENT'
            ? 'yt-dlp が見つかりません (render.yaml のビルドコマンドで bin/yt-dlp を取得してください)'
            : err.killed
              ? 'yt-dlp がタイムアウトしました'
              : ytCleanErr(stderr || err.message)
        );
        e.stderr = String(stderr || '');
        return reject(e);
      }
      try {
        resolve(JSON.parse(stdout));
      } catch (e2) {
        reject(new Error('yt-dlp の出力を解釈できませんでした'));
      }
    });
  });
}

// yt-dlp の JSON から、ブラウザが直接再生できる (単一ファイルの https) 形式だけを取り出す
function ytBuild(j) {
  const fmts = []; // サーバー内部用 (URL を含む)
  const list = []; // ブラウザへ返す (URL は含めない)
  for (const f of j.formats || []) {
    if (!f.url || (f.protocol !== 'https' && f.protocol !== 'http')) continue;
    if (!/^(mp4|m4a|webm)$/.test(f.ext)) continue;
    const hasV = !!f.vcodec && f.vcodec !== 'none';
    const hasA = !!f.acodec && f.acodec !== 'none';
    if (!hasV && !hasA) continue;
    fmts.push({ url: f.url, ua: (f.http_headers && f.http_headers['User-Agent']) || YT_UA });
    list.push({
      i: fmts.length - 1,
      k: hasV && hasA ? 'm' : hasV ? 'v' : 'a', // m=音声込み / v=映像のみ / a=音声のみ
      h: f.height || 0,
      fps: f.fps || 0,
      ext: f.ext,
      vc: hasV ? f.vcodec : '',
      ac: hasA ? f.acodec : '',
      abr: f.abr || 0,
      lp: f.language_preference || 0 // 吹き替え音声より元の音声を優先するため
    });
  }
  return {
    fmts,
    info: {
      id: j.id,
      title: j.title || '',
      uploader: j.uploader || j.channel || '',
      duration: j.duration || 0,
      live: !!j.is_live,
      formats: list
    }
  };
}

// yt-dlp を同時実行数の上限内で実行する (動画の解決・検索で共用)
async function ytRun(target, extra) {
  await ytAcquire();
  try {
    try {
      return await ytExec(target, extra.concat(YT_RT_ARGS));
    } catch (e) {
      // 古い yt-dlp は JS ランタイム用のオプションを知らない → 付けずにやり直す
      if (/no such option|unrecognized arguments/i.test(e.stderr || '')) return await ytExec(target, extra);
      throw e;
    }
  } finally {
    ytRelease();
  }
}

// 検索: yt-dlp の ytsearchN: を使う (--flat-playlist で一覧だけ高速に取得)
const ytSearchCache = new Map(); // "n:query" -> { t, items }
async function ytSearch(q, n) {
  const key = n + ':' + q.toLowerCase();
  const c = ytSearchCache.get(key);
  if (c && Date.now() - c.t < 10 * 60 * 1000) return c.items;
  const j = await ytRun('ytsearch' + n + ':' + q, ['--flat-playlist']);
  const items = (j.entries || [])
    .filter((e) => e && /^[\w-]{11}$/.test(e.id || ''))
    .map((e) => ({
      id: e.id,
      title: e.title || '',
      by: e.channel || e.uploader || '',
      dur: e.duration || 0,
      views: e.view_count || 0,
      live: e.live_status === 'is_live'
    }));
  ytSearchCache.set(key, { t: Date.now(), items });
  if (ytSearchCache.size > 60) ytSearchCache.delete(ytSearchCache.keys().next().value);
  return items;
}

function ytGet(id) {
  const c = ytCache.get(id);
  if (c && Date.now() - c.t < YT_TTL) return Promise.resolve(c);
  let p = ytJobs.get(id);
  if (p) return p;
  p = (async () => {
    const j = await ytRun('https://www.youtube.com/watch?v=' + id, ['--no-playlist']);
    if (j.is_live) throw new Error('ライブ配信には未対応です');
    const r = ytBuild(j);
    if (!r.info.formats.length) throw new Error('再生できる形式が見つかりませんでした');
    r.t = Date.now();
    ytCache.set(id, r);
    if (ytCache.size > 60) ytCache.delete(ytCache.keys().next().value);
    return r;
  })();
  ytJobs.set(id, p);
  const done = () => ytJobs.delete(id);
  p.then(done, done);
  return p;
}

// googlevideo の直リンクを、Range ごとそのままブラウザへ中継する
function ytPipe(req, res, id, f, depth, u) {
  const fail = (code, msg) => ytJson(res, code, { error: msg });
  if (depth > 4 || !/^https?:$/.test(u.protocol) || hostBlocked(u.hostname)) return fail(502, '接続先を開けません');
  const h = {
    'user-agent': f.ua || YT_UA,
    accept: '*/*',
    'accept-encoding': 'identity',
    'accept-language': req.headers['accept-language'] || 'en-US,en;q=0.9',
    origin: 'https://www.youtube.com',
    referer: 'https://www.youtube.com/'
  };
  if (req.headers.range) h.range = req.headers.range;
  const isHttps = u.protocol === 'https:';
  const up = (isHttps ? https : http).request(
    {
      hostname: u.hostname,
      port: u.port || (isHttps ? 443 : 80),
      path: u.pathname + u.search,
      method: 'GET',
      headers: h,
      agent: isHttps ? httpsAgent : httpAgent
    },
    (ur) => {
      const st = ur.statusCode;
      if ([301, 302, 303, 307, 308].includes(st) && ur.headers.location) {
        ur.resume();
        let nu;
        try {
          nu = new URL(ur.headers.location, u);
        } catch (e) {
          return fail(502, 'リダイレクト先が不正です');
        }
        return ytPipe(req, res, id, f, depth + 1, nu);
      }
      if (st === 403 || st === 410) ytCache.delete(id); // 期限切れ / IP 不一致 → 次回は解決し直す
      const oh = { 'cache-control': 'no-store', 'accept-ranges': 'bytes' };
      for (const k of ['content-type', 'content-length', 'content-range', 'accept-ranges']) if (ur.headers[k]) oh[k] = ur.headers[k];
      res.writeHead(st, oh);
      ur.pipe(res);
      ur.on('error', () => res.destroy());
    }
  );
  up.setTimeout(30000, () => up.destroy(new Error('timeout')));
  up.on('error', () => fail(502, '動画の取得に失敗しました'));
  res.on('close', () => up.destroy());
  up.end();
}

// EU 圏のサーバーから接続すると consent.youtube.com へ飛ばされるため、同意済みの Cookie を先に入れておく
function seedYtCookies(sess) {
  if (!sess || sess.ytSeeded) return;
  sess.ytSeeded = true;
  storeSetCookie(sess, 'SOCS=CAI; Domain=youtube.com; Path=/; Secure; Max-Age=31536000', new URL('https://www.youtube.com/'));
}

function ytParseT(s) {
  if (!s) return 0;
  if (/^\d+$/.test(s)) return parseInt(s, 10);
  const m = /^(?:(\d+)h)?(?:(\d+)m)?(?:(\d+)s?)?$/.exec(s);
  return m ? (+(m[1] || 0)) * 3600 + (+(m[2] || 0)) * 60 + +(m[3] || 0) : 0;
}

// ページ移動としての「動画ページ」要求なら { id, t } を返す。?pxraw=1 を付けると本来のページを開く
function ytWatchTarget(req, target) {
  if (req.method !== 'GET' || target.searchParams.has('pxraw')) return null;
  const host = target.hostname.toLowerCase();
  let id = null;
  if (/^(www\.|m\.)?youtube\.com$/.test(host)) {
    if (target.pathname === '/watch') id = target.searchParams.get('v');
    else {
      const m = /^\/(?:shorts|live)\/([\w-]{11})/.exec(target.pathname);
      if (m) id = m[1];
    }
  } else if (host === 'youtu.be') {
    const m = /^\/([\w-]{11})/.exec(target.pathname);
    if (m) id = m[1];
  }
  if (!id || !/^[\w-]{11}$/.test(id)) return null;
  const dest = req.headers['sec-fetch-dest'];
  const isNav = dest ? dest === 'document' || dest === 'iframe' : /text\/html/.test(req.headers.accept || '');
  if (!isNav) return null; // SPA の裏側の fetch などは素通し
  return { id, t: ytParseT(target.searchParams.get('t') || target.searchParams.get('start')) };
}

/* ---------- 専用プレーヤーのブラウザ側スクリプト ----------
 *  yt-dlp の動画は「映像のみ」「音声のみ」に分かれていることが多いため、<video> と <audio> を同期させて再生する。
 *  音声込みの形式 (360p など) がある場合は、画質の選択肢としてそれも出す。 */
function ytViewerMain() {
  var Y = window.__YT;
  var $ = function (id) {
    return document.getElementById(id);
  };
  var V = $('v'), A = $('a'), box = $('box'), msg = $('msg'), seek = $('seek');
  var info = null, opts = [], split = false, dragging = false, hideTimer = null;
  var noop = function () {};
  var startAt = Y.t || 0;

  V.poster = '/go/https/i.ytimg.com/vi/' + Y.id + '/hqdefault.jpg';
  $('raw').href = '/go/https/www.youtube.com/watch?v=' + Y.id + '&pxraw=1';
  $('home').href = '/~/yt';

  function fmtT(s) {
    s = Math.max(0, Math.floor(s || 0));
    var h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60), x = s % 60;
    return (h ? h + ':' + (m < 10 ? '0' : '') + m : m) + ':' + (x < 10 ? '0' : '') + x;
  }
  function showMsg(t, isErr) {
    msg.textContent = t || '';
    msg.className = isErr ? 'err' : '';
    msg.style.display = t ? 'block' : 'none';
  }
  function src(i) {
    return '/~/yt/s?v=' + Y.id + '&i=' + i;
  }
  function sup(el, type, codec) {
    try {
      return el.canPlayType(type + (codec ? '; codecs="' + codec + '"' : '')) !== '';
    } catch (e) {
      return false;
    }
  }
  function vtype(f) {
    return f.ext === 'webm' ? 'video/webm' : 'video/mp4';
  }
  function atype(f) {
    return f.ext === 'webm' ? 'audio/webm' : 'audio/mp4';
  }
  function codecName(c) {
    return /^avc1/.test(c) ? 'H.264' : /^vp0?9/.test(c) ? 'VP9' : /^av01/.test(c) ? 'AV1' : c;
  }
  function codecRank(c) {
    return /^avc1/.test(c) ? 0 : /^vp0?9/.test(c) ? 1 : 2; // 互換性と軽さの順
  }

  /* ----- 画質の選択肢を作る ----- */
  function build(fs) {
    var vids = [], auds = [], mux = [];
    fs.forEach(function (f) {
      if (f.k === 'v' && sup(V, vtype(f), f.vc)) vids.push(f);
      else if (f.k === 'a' && sup(A, atype(f), f.ac)) auds.push(f);
      else if (f.k === 'm' && sup(V, vtype(f), f.vc + ', ' + f.ac)) mux.push(f);
    });
    auds.sort(function (x, y) {
      return y.lp - x.lp || y.abr - x.abr;
    });
    vids.sort(function (x, y) {
      return y.h - x.h || y.fps - x.fps || codecRank(x.vc) - codecRank(y.vc);
    });
    function audioFor(vf) {
      var want = vf.ext === 'webm' ? 'webm' : 'm4a';
      for (var i = 0; i < auds.length; i++) if (auds[i].ext === want) return auds[i];
      return auds[0] || null;
    }
    var seen = {}, out = [];
    vids.forEach(function (f) {
      var key = f.h + 'p' + (f.fps > 30 ? f.fps : '');
      if (seen[key]) return;
      var a = audioFor(f);
      if (!a) return;
      seen[key] = 1;
      out.push({ label: key + ' (' + codecName(f.vc) + ')', h: f.h, v: f.i, a: a.i });
    });
    mux.sort(function (x, y) {
      return y.h - x.h;
    });
    mux.forEach(function (f) {
      out.push({ label: f.h + 'p 音声込み (' + codecName(f.vc) + ')', h: f.h, v: f.i, a: null });
    });
    return out;
  }

  /* ----- 読み込み / 画質切り替え ----- */
  function load(opt, keep) {
    var t = keep ? V.currentTime : startAt;
    var wasPlaying = keep && !V.paused;
    split = opt.a !== null;
    showMsg('読み込み中…');
    V.src = src(opt.v);
    if (split) {
      A.src = src(opt.a);
    } else {
      A.removeAttribute('src');
      try {
        A.load();
      } catch (e) {}
    }
    V.onloadedmetadata = function () {
      try {
        if (t > 0) V.currentTime = t;
      } catch (e) {}
      showMsg('');
      if (wasPlaying) play();
      ui();
    };
    A.onloadedmetadata = function () {
      try {
        A.currentTime = V.currentTime || t;
      } catch (e) {}
    };
  }

  /* ----- 再生制御 (映像を主、音声を従として同期) ----- */
  function play() {
    var p = V.play();
    if (p && p.catch)
      p.catch(function (e) {
        showMsg('再生できません: ' + e.message, true);
      });
  }
  function toggle() {
    if (V.paused) play();
    else V.pause();
  }
  function seekBy(s) {
    var d = V.duration || (info && info.duration) || 0;
    V.currentTime = Math.max(0, Math.min(d || 1e9, V.currentTime + s));
  }
  V.addEventListener('play', function () {
    if (split) {
      try {
        A.currentTime = V.currentTime;
      } catch (e) {}
      var p = A.play();
      if (p && p.catch) p.catch(noop);
    }
    ui();
  });
  V.addEventListener('pause', function () {
    if (split) A.pause();
    ui();
  });
  V.addEventListener('waiting', function () {
    if (split) A.pause();
    showMsg('バッファ中…');
  });
  V.addEventListener('playing', function () {
    showMsg('');
    if (split && A.paused) {
      try {
        A.currentTime = V.currentTime;
      } catch (e) {}
      var p = A.play();
      if (p && p.catch) p.catch(noop);
    }
  });
  V.addEventListener('seeking', function () {
    if (split) {
      try {
        A.currentTime = V.currentTime;
      } catch (e) {}
    }
  });
  V.addEventListener('ratechange', function () {
    A.playbackRate = V.playbackRate;
  });
  V.addEventListener('timeupdate', ui);
  V.addEventListener('ended', ui);
  V.addEventListener('error', function () {
    showMsg('動画を読み込めませんでした (code ' + (V.error ? V.error.code : '?') + ')。別の画質を試すか、時間をおいて再読み込みしてください。', true);
  });
  A.addEventListener('error', function () {
    if (split) showMsg('音声を読み込めませんでした。別の画質を試してください。', true);
  });
  // 音声と映像のずれを補正
  setInterval(function () {
    if (split && !V.paused && !V.seeking && !A.seeking && A.readyState >= 2 && Math.abs(A.currentTime - V.currentTime) > 0.3) {
      try {
        A.currentTime = V.currentTime;
      } catch (e) {}
    }
  }, 500);

  /* ----- コントロール ----- */
  function ui() {
    var d = V.duration || (info && info.duration) || 0;
    $('t').textContent = fmtT(V.currentTime) + ' / ' + fmtT(d);
    if (!dragging && d) seek.value = Math.round((V.currentTime / d) * 1000);
    $('pp').textContent = V.paused ? '▶' : '❚❚';
    box.classList.toggle('paused', V.paused);
    $('mute').textContent = V.muted || V.volume === 0 ? '🔇' : '🔊';
  }
  function setVol(v, m) {
    V.volume = A.volume = v;
    V.muted = A.muted = m;
    $('vol').value = v;
    try {
      localStorage.setItem('yt_vol', JSON.stringify([v, m]));
    } catch (e) {}
    ui();
  }
  function fullscreen() {
    var d = document;
    if (d.fullscreenElement || d.webkitFullscreenElement) {
      (d.exitFullscreen || d.webkitExitFullscreen).call(d);
    } else {
      var r = box.requestFullscreen || box.webkitRequestFullscreen;
      if (r) r.call(box);
    }
  }
  function poke() {
    box.classList.add('show');
    clearTimeout(hideTimer);
    hideTimer = setTimeout(function () {
      if (!V.paused) box.classList.remove('show');
    }, 2500);
  }
  seek.addEventListener('input', function () {
    dragging = true;
    var d = V.duration || (info && info.duration) || 0;
    $('t').textContent = fmtT((seek.value / 1000) * d) + ' / ' + fmtT(d);
  });
  seek.addEventListener('change', function () {
    var d = V.duration || (info && info.duration) || 0;
    if (d) V.currentTime = (seek.value / 1000) * d;
    dragging = false;
  });
  $('pp').addEventListener('click', toggle);
  $('big').addEventListener('click', toggle);
  V.addEventListener('click', toggle);
  V.addEventListener('dblclick', fullscreen);
  $('fs').addEventListener('click', fullscreen);
  $('mute').addEventListener('click', function () {
    setVol(V.volume || 1, !V.muted);
  });
  $('vol').addEventListener('input', function () {
    setVol(parseFloat($('vol').value), false);
  });
  $('rate').addEventListener('change', function () {
    V.playbackRate = parseFloat($('rate').value);
  });
  $('q').addEventListener('change', function () {
    load(opts[parseInt($('q').value, 10)], true);
  });
  box.addEventListener('mousemove', poke);
  box.addEventListener('touchstart', poke, { passive: true });
  document.addEventListener('keydown', function (ev) {
    var tg = ev.target && ev.target.tagName;
    if (tg === 'SELECT' || tg === 'TEXTAREA' || (tg === 'INPUT' && ev.target.type === 'text') || ev.ctrlKey || ev.metaKey || ev.altKey) return;
    var k = ev.key, used = true;
    if (k === ' ' || k === 'k') toggle();
    else if (k === 'ArrowLeft') seekBy(-5);
    else if (k === 'ArrowRight') seekBy(5);
    else if (k === 'ArrowUp') setVol(Math.min(1, V.volume + 0.05), false);
    else if (k === 'ArrowDown') setVol(Math.max(0, V.volume - 0.05), false);
    else if (k === 'f') fullscreen();
    else if (k === 'm') setVol(V.volume || 1, !V.muted);
    else used = false;
    if (used) {
      ev.preventDefault();
      poke();
    }
  });
  try {
    var sv = JSON.parse(localStorage.getItem('yt_vol') || 'null');
    if (sv) setVol(sv[0], !!sv[1]);
  } catch (e) {}

  /* ----- 動画情報の取得 ----- */
  showMsg('動画情報を取得中… (初回は 10〜30 秒ほどかかります)');
  fetch('/~/yt/info?v=' + encodeURIComponent(Y.id), { credentials: 'same-origin' })
    .then(function (r) {
      return r.json().then(function (j) {
        if (!r.ok || j.error) throw new Error(j.error || 'HTTP ' + r.status);
        return j;
      });
    })
    .then(function (j) {
      info = j;
      $('title').textContent = j.title;
      $('up').textContent = j.uploader + (j.duration ? ' ・ ' + fmtT(j.duration) : '');
      document.title = j.title + ' - YouTube';
      opts = build(j.formats);
      if (!opts.length) throw new Error('このブラウザで再生できる形式がありませんでした');
      var q = $('q'), def = 0;
      opts.forEach(function (o, i) {
        var e = document.createElement('option');
        e.value = i;
        e.textContent = o.label;
        q.appendChild(e);
      });
      for (var i = 0; i < opts.length; i++) {
        if (opts[i].a !== null && opts[i].h <= 1080) {
          def = i;
          break;
        }
      }
      q.value = def;
      load(opts[def], false);
      showMsg('');
      ui();
      poke();
    })
    .catch(function (e) {
      $('title').textContent = '動画を再生できません';
      showMsg(e.message, true);
      $('hint').style.display = 'block';
    });
  ui();
}

const YT_VIEWER_HTML = `<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>YouTube</title>
<link rel="icon" type="image/svg+xml" href="/favicon.svg">
<style>
  :root{color-scheme:dark}
  *{box-sizing:border-box}
  html,body{margin:0;min-height:100%;background:#0f1117;color:#e8eaf0;
    font-family:system-ui,-apple-system,"Segoe UI","Hiragino Sans","Noto Sans JP",sans-serif}
  #wrap{max-width:1200px;margin:0 auto;padding:12px}
  #sf{display:flex;gap:8px;margin:0 0 10px}
  #sf input{flex:1;min-width:0;padding:9px 14px;font-size:14px;border-radius:20px;border:1px solid #2b3040;background:#171a23;color:inherit;outline:none}
  #sf input:focus{border-color:#5b8cff}
  #sf button{padding:0 16px;border:0;border-radius:20px;background:#5b8cff;color:#fff;cursor:pointer}
  #box{position:relative;width:100%;aspect-ratio:16/9;max-height:calc(100vh - 150px);background:#000;border-radius:10px;overflow:hidden;margin:0 auto}
  #box:fullscreen{max-height:none;border-radius:0}
  #v{width:100%;height:100%;object-fit:contain;display:block;background:#000}
  #big{position:absolute;left:50%;top:50%;transform:translate(-50%,-50%);width:72px;height:72px;border-radius:50%;
    background:rgba(0,0,0,.6);display:none;align-items:center;justify-content:center;font-size:30px;cursor:pointer}
  #box.paused #big{display:flex}
  #msg{position:absolute;left:12px;right:12px;top:12px;padding:8px 12px;border-radius:8px;background:rgba(0,0,0,.7);font-size:13px;line-height:1.5}
  #msg.err{background:rgba(198,40,40,.9)}
  .ctl{position:absolute;left:0;right:0;bottom:0;padding:18px 10px 8px;background:linear-gradient(transparent,rgba(0,0,0,.85));
    opacity:0;transition:opacity .2s}
  #box.show .ctl,#box.paused .ctl,.ctl:hover{opacity:1}
  .row{display:flex;align-items:center;gap:8px;font-size:13px}
  .row .sp{flex:1}
  .row button{width:34px;height:30px;border:0;border-radius:6px;background:transparent;color:#fff;font-size:16px;cursor:pointer}
  .row button:hover{background:rgba(255,255,255,.18)}
  .row select{background:#222;color:#fff;border:1px solid #444;border-radius:6px;padding:3px 4px;font-size:12px}
  input[type=range]{accent-color:#ff3b3b}
  #seek{width:100%;margin:0 0 4px}
  #vol{width:70px}
  h1{font-size:18px;font-weight:600;margin:14px 2px 4px}
  #up{color:#aab0c0;font-size:13px;margin:0 2px 10px}
  .links{font-size:13px;margin:0 2px;color:#8a90a2}
  .links a{color:#8fb0ff;text-decoration:none}
  .links a:hover{text-decoration:underline}
  #hint{display:none;margin:14px 2px;font-size:12px;line-height:1.7;color:#aab0c0}
</style>
</head>
<body>
<div id="wrap">
  <form id="sf" action="/~/yt" method="get"><input name="q" placeholder="YouTube を検索" autocomplete="off"><button type="submit">検索</button></form>
  <div id="box" class="paused show">
    <video id="v" playsinline preload="metadata"></video>
    <audio id="a" preload="auto"></audio>
    <div id="big">&#9654;</div>
    <div id="msg" style="display:none"></div>
    <div class="ctl">
      <input id="seek" type="range" min="0" max="1000" value="0">
      <div class="row">
        <button id="pp" title="再生 / 一時停止 (Space)">&#9654;</button>
        <span id="t">0:00 / 0:00</span>
        <span class="sp"></span>
        <button id="mute" title="ミュート (M)">&#128266;</button>
        <input id="vol" type="range" min="0" max="1" step="0.05" value="1">
        <select id="rate" title="再生速度">
          <option value="0.5">0.5x</option><option value="0.75">0.75x</option><option value="1" selected>1x</option>
          <option value="1.25">1.25x</option><option value="1.5">1.5x</option><option value="2">2x</option>
        </select>
        <select id="q" title="画質"></select>
        <button id="fs" title="全画面 (F)">&#9974;</button>
      </div>
    </div>
  </div>
  <h1 id="title">読み込み中…</h1>
  <div id="up"></div>
  <div class="links"><a id="home">検索に戻る</a> ・ <a id="raw">通常ページで開く</a></div>
  <div id="hint">
    「ボットではないことを確認」などと出る場合は、サーバー (Render) の IP が YouTube に制限されています。
    環境変数 YT_COOKIES_FILE に cookies.txt を設定すると改善することがあります。
  </div>
</div>
<script>window.__YT=__CFG__;</script>
<script>(${ytViewerMain.toString()})();</script>
</body>
</html>`;

/* ---------- YouTube 検索モードのページ (/~/yt) ---------- */
function ytHomeMain() {
  var $ = function (id) {
    return document.getElementById(id);
  };
  var form = $('f'), inp = $('q'), list = $('list'), more = $('more'), st = $('st'), hist = $('hist');
  var cur = { q: '', n: 20 };

  function fmtT(s) {
    s = Math.max(0, Math.floor(s || 0));
    var h = Math.floor(s / 3600), m = Math.floor((s % 3600) / 60), x = s % 60;
    return (h ? h + ':' + (m < 10 ? '0' : '') + m : m) + ':' + (x < 10 ? '0' : '') + x;
  }
  function fmtV(n) {
    if (!n) return '';
    if (n >= 1e8) return (n / 1e8).toFixed(1) + '億回視聴';
    if (n >= 1e4) return (n / 1e4).toFixed(n >= 1e5 ? 0 : 1) + '万回視聴';
    return n + '回視聴';
  }
  // YouTube の URL が貼られたら、検索せずそのまま再生ページへ
  function idFromUrl(s) {
    var m = /(?:youtu\.be\/|[?&]v=|\/shorts\/|\/live\/|\/embed\/)([\w-]{11})/.exec(s);
    return /youtu/i.test(s) && m ? m[1] : null;
  }
  function getHist() {
    try {
      return JSON.parse(localStorage.getItem('yt_hist') || '[]');
    } catch (e) {
      return [];
    }
  }
  function addHist(q) {
    try {
      var h = getHist().filter(function (x) {
        return x !== q;
      });
      h.unshift(q);
      localStorage.setItem('yt_hist', JSON.stringify(h.slice(0, 10)));
    } catch (e) {}
  }
  function showHist() {
    hist.textContent = '';
    getHist().forEach(function (q) {
      var a = document.createElement('a');
      a.href = '/~/yt?q=' + encodeURIComponent(q);
      a.textContent = q;
      a.className = 'chip';
      a.addEventListener('click', function (ev) {
        ev.preventDefault();
        go(q);
      });
      hist.appendChild(a);
    });
  }
  function card(it) {
    var a = document.createElement('a');
    a.className = 'card';
    a.href = '/go/https/www.youtube.com/watch?v=' + it.id;
    var th = document.createElement('div');
    th.className = 'th';
    var im = document.createElement('img');
    im.loading = 'lazy';
    im.alt = '';
    im.src = '/go/https/i.ytimg.com/vi/' + it.id + '/mqdefault.jpg';
    th.appendChild(im);
    var d = document.createElement('span');
    d.className = 'dur';
    d.textContent = it.live ? 'LIVE' : it.dur ? fmtT(it.dur) : '';
    if (d.textContent) th.appendChild(d);
    var t = document.createElement('div');
    t.className = 'ti';
    t.textContent = it.title;
    var s = document.createElement('div');
    s.className = 'sub';
    s.textContent = [it.by, fmtV(it.views)].filter(Boolean).join(' ・ ');
    a.appendChild(th);
    a.appendChild(t);
    a.appendChild(s);
    return a;
  }
  function search(q, n) {
    cur = { q: q, n: n };
    inp.value = q;
    st.className = 'st';
    st.textContent = '検索中… (初回は 10〜20 秒ほどかかることがあります)';
    more.style.display = 'none';
    if (n === 20) list.textContent = '';
    hist.style.display = 'none';
    document.title = q + ' - YouTube 検索';
    fetch('/~/yt/search?q=' + encodeURIComponent(q) + '&n=' + n, { credentials: 'same-origin' })
      .then(function (r) {
        return r.json().then(function (j) {
          if (!r.ok || j.error) throw new Error(j.error || 'HTTP ' + r.status);
          return j;
        });
      })
      .then(function (j) {
        if (cur.q !== q || cur.n !== n) return; // 古い応答は捨てる
        list.textContent = '';
        j.items.forEach(function (it) {
          list.appendChild(card(it));
        });
        st.textContent = j.items.length ? '' : '見つかりませんでした';
        more.style.display = j.items.length >= n && n < 60 ? 'block' : 'none';
      })
      .catch(function (e) {
        if (cur.q !== q || cur.n !== n) return;
        st.className = 'st err';
        st.textContent = '検索に失敗しました: ' + e.message;
      });
  }
  function go(q) {
    var id = idFromUrl(q);
    if (id) {
      location.href = '/go/https/www.youtube.com/watch?v=' + id;
      return;
    }
    addHist(q);
    try {
      history.pushState(null, '', '/~/yt?q=' + encodeURIComponent(q));
    } catch (e) {}
    search(q, 20);
  }
  form.addEventListener('submit', function (ev) {
    ev.preventDefault();
    var q = inp.value.trim();
    if (q) go(q);
  });
  more.addEventListener('click', function () {
    search(cur.q, Math.min(60, cur.n + 20));
  });
  function fromUrl() {
    var q = (new URLSearchParams(location.search).get('q') || '').trim();
    if (q) search(q, 20);
    else {
      cur = { q: '', n: 20 };
      list.textContent = '';
      st.textContent = '';
      more.style.display = 'none';
      inp.value = '';
      document.title = 'YouTube 検索';
      hist.style.display = 'flex';
      showHist();
    }
  }
  window.addEventListener('popstate', fromUrl);
  fromUrl();
}

const YT_HOME_HTML = `<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>YouTube 検索</title>
<link rel="icon" type="image/svg+xml" href="/favicon.svg">
<style>
  :root{color-scheme:dark}
  *{box-sizing:border-box}
  html,body{margin:0;min-height:100%;background:#0f1117;color:#e8eaf0;
    font-family:system-ui,-apple-system,"Segoe UI","Hiragino Sans","Noto Sans JP",sans-serif}
  #wrap{max-width:1200px;margin:0 auto;padding:14px}
  form{display:flex;gap:8px;max-width:720px;margin:0 auto 14px}
  input{flex:1;min-width:0;padding:11px 16px;font-size:16px;border-radius:24px;border:1px solid #2b3040;background:#171a23;color:inherit;outline:none}
  input:focus{border-color:#5b8cff;box-shadow:0 0 0 3px rgba(91,140,255,.25)}
  button.go{padding:0 22px;font-size:15px;border:0;border-radius:24px;background:#5b8cff;color:#fff;cursor:pointer}
  .st{min-height:1.4em;text-align:center;font-size:13px;color:#aab0c0;margin:6px 0 12px}
  .st.err{color:#ff8a80}
  #hist{display:none;flex-wrap:wrap;gap:8px;justify-content:center;max-width:720px;margin:0 auto}
  .chip{padding:6px 12px;border-radius:16px;background:#1d2130;color:#cfd5e6;font-size:13px;text-decoration:none}
  .chip:hover{background:#2a3050}
  #list{display:grid;grid-template-columns:repeat(auto-fill,minmax(240px,1fr));gap:18px 14px}
  .card{display:block;color:inherit;text-decoration:none}
  .th{position:relative;aspect-ratio:16/9;background:#1d2130;border-radius:10px;overflow:hidden}
  .th img{width:100%;height:100%;object-fit:cover;display:block}
  .dur{position:absolute;right:6px;bottom:6px;padding:1px 6px;border-radius:4px;background:rgba(0,0,0,.8);font-size:12px}
  .ti{margin:8px 2px 2px;font-size:14px;line-height:1.4;display:-webkit-box;-webkit-line-clamp:2;-webkit-box-orient:vertical;overflow:hidden}
  .card:hover .ti{color:#8fb0ff}
  .sub{margin:0 2px;font-size:12px;color:#8a90a2}
  #more{display:none;margin:22px auto;padding:10px 28px;border:0;border-radius:20px;background:#242938;color:#e8eaf0;font-size:14px;cursor:pointer}
  #more:hover{background:#2f3550}
  footer{text-align:center;font-size:12px;color:#8a90a2;margin:26px 0 8px}
  footer a{color:#8fb0ff;text-decoration:none}
</style>
</head>
<body>
<div id="wrap">
  <form id="f" autocomplete="off">
    <input id="q" type="text" placeholder="YouTube を検索 / 動画の URL を貼り付け" autofocus>
    <button class="go" type="submit">検索</button>
  </form>
  <div id="hist"></div>
  <p id="st" class="st"></p>
  <div id="list"></div>
  <button id="more">もっと見る</button>
  <footer><a href="/">トップへ戻る</a></footer>
</div>
<script>(${ytHomeMain.toString()})();</script>
</body>
</html>`;

function serveYtViewer(res, id, t) {
  const cfg = JSON.stringify({ id, t }).replace(/</g, '\\u003c');
  res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-store' });
  res.end(YT_VIEWER_HTML.replace('__CFG__', () => cfg));
}

const server = http.createServer(async (req, res) => {
  try {
    const path = req.url.split('?')[0];

    if (path === '/healthz') {
      res.writeHead(200, { 'content-type': 'text/plain' });
      return res.end('ok');
    }
    if (!authOk(req, res)) {
      res.writeHead(401, { 'www-authenticate': 'Basic realm="proxy", charset="UTF-8"' });
      return res.end('Unauthorized');
    }

    if (path === '/') {
      res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-cache' });
      return res.end(INDEX_HTML);
    }
    if (path === '/favicon.svg' || path === '/favicon.ico') {
      res.writeHead(200, { 'content-type': 'image/svg+xml', 'cache-control': 'public, max-age=86400' });
      return res.end(FAVICON_SVG);
    }
    if (path === '/sw.js') {
      res.writeHead(200, {
        'content-type': 'application/javascript; charset=utf-8',
        'service-worker-allowed': '/',
        'cache-control': 'no-cache'
      });
      return res.end(SW_JS);
    }
    if (path === '/~/rc-overlay.js' && RC_OVERLAY_SRC) {
      res.writeHead(200, { 'content-type': 'application/javascript; charset=utf-8', 'cache-control': 'no-cache' });
      return res.end(RC_OVERLAY_SRC);
    }
    // サーバー側 (reCAPTCHA 互換モジュール) のログ。/__rc-debug を直接開いても見られる (?clear で消去)
    if (path === '/~/rc-debug' || path === '/__rc-debug') {
      const rc = getRc(req);
      const qs = req.url.includes('?') ? '?' + req.url.split('?')[1] : '';
      if (/[?&]clear\b/.test(qs)) pxLogs.length = 0;
      let rcText = '';
      if (rc) {
        const origin = (isSecure(req) ? 'https' : 'http') + '://' + req.headers.host;
        const r = rc.handleDebug(new Request(origin + '/__rc-debug' + qs));
        if (r) rcText = await r.text();
      }
      const body = pxLogs.concat(rcText && rcText.charAt(0) !== '(' ? [rcText] : []).join('\n');
      res.writeHead(200, { 'content-type': 'text/plain; charset=utf-8', 'cache-control': 'no-store' });
      return res.end(body || '(ログなし: Google / reCAPTCHA 宛ての通信がまだありません)');
    }
    if (path === '/~/client.js') {
      res.writeHead(200, { 'content-type': 'application/javascript; charset=utf-8', 'cache-control': 'no-cache' });
      return res.end(CLIENT_JS);
    }
    if (path === '/~/shell') {
      res.writeHead(200, {
        'content-type': 'text/html; charset=utf-8',
        'cache-control': 'no-cache',
        'content-security-policy': SHELL_CSP
      });
      return res.end(SHELL_HTML);
    }
    if (path === '/~/yt') {
      res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-store' });
      return res.end(YT_HOME_HTML);
    }
    if (path === '/~/yt/search') {
      const qs = new URL(req.url, 'http://x').searchParams;
      const q = (qs.get('q') || '').trim().slice(0, 200);
      const n = Math.min(60, Math.max(10, parseInt(qs.get('n'), 10) || 20));
      if (!q) return ytJson(res, 400, { error: '検索ワードを入力してください' });
      ytSearch(q, n).then(
        (items) => ytJson(res, 200, { items }),
        (e) => ytJson(res, 502, { error: e.message })
      );
      return;
    }
    if (path === '/~/yt/info' || path === '/~/yt/s') {
      const qs = new URL(req.url, 'http://x').searchParams;
      const id = qs.get('v') || '';
      if (!/^[\w-]{11}$/.test(id)) return ytJson(res, 400, { error: '動画 ID が正しくありません' });
      if (path === '/~/yt/info') {
        ytGet(id).then(
          (r) => ytJson(res, 200, r.info),
          (e) => ytJson(res, 502, { error: e.message })
        );
        return;
      }
      const idx = parseInt(qs.get('i'), 10);
      ytGet(id).then(
        (r) => {
          const f = r.fmts[idx];
          if (!f) return ytJson(res, 404, { error: '形式が見つかりません' });
          ytPipe(req, res, id, f, 0, new URL(f.url));
        },
        (e) => ytJson(res, 502, { error: e.message })
      );
      return;
    }
    if (path === '/~/cookie' && req.method === 'POST') {
      const body = JSON.parse((await readBody(req, 16384)) || '{}');
      const u = new URL(String(body.url));
      if (/^https?:$/.test(u.protocol) && typeof body.cookie === 'string') {
        const sess = getSession(req, res, true);
        storeSetCookie(sess, body.cookie, u);
      }
      res.writeHead(204);
      return res.end();
    }

    if (req.url.startsWith(PREFIX)) {
      const m = /^\/go\/(https?)\/([^\/?#]+)([^]*)$/.exec(req.url);
      if (m && (!m[3] || m[3][0] === '?' || m[3][0] === '#')) {
        // /go/https/example.com  ->  /go/https/example.com/  (相対パス解決のため)
        res.writeHead(308, { location: PREFIX + m[1] + '/' + m[2] + '/' + m[3] });
        return res.end();
      }
      const target = parseProxyPath(req.url);
      if (!target) return errorPage(res, 400, 'URL が正しくありません');
      if (target.host.toLowerCase() === String(req.headers.host).toLowerCase()) return errorPage(res, 400, '自分自身へのアクセスはできません');
      if (hostBlocked(target.hostname)) return errorPage(res, 403, 'このアドレスへは接続できません');
      // YouTube の動画ページは、専用プレーヤー (yt-dlp 経由) に差し替える
      const yt = ytWatchTarget(req, target);
      if (yt) return serveYtViewer(res, yt.id, yt.t);
      return handleProxy(req, res, target);
    }

    return rescue(req, res);
  } catch (e) {
    errorPage(res, 500, e.message);
  }
});

server.requestTimeout = 0; // 大きなアップロード・長い転送を途中で切らない
server.keepAliveTimeout = 65000;
server.headersTimeout = 66000;

/* ========================================================================
 *  ④ WebSocket ブリッジ  (/~/ws?url=wss://...&o=https://page-origin)
 * ====================================================================== */

function closeSafe(ws, code, reason) {
  try {
    const ok = code >= 1000 && code <= 4999 && ![1004, 1005, 1006, 1015].includes(code);
    const r = Buffer.isBuffer(reason) ? reason.toString().slice(0, 100) : String(reason || '').slice(0, 100);
    ws.close(ok ? code : 1000, r);
  } catch (e) {
    try {
      ws.terminate();
    } catch (e2) {}
  }
}

server.on('upgrade', (req, socket, head) => {
  socket.on('error', () => {});
  const reject = (line) => {
    try {
      socket.write(`HTTP/1.1 ${line}\r\nConnection: close\r\n\r\n`);
    } catch (e) {}
    socket.destroy();
  };
  if (!authOk(req)) return reject('401 Unauthorized');

  let u;
  let target;
  try {
    u = new URL(req.url, 'http://x');
    if (u.pathname !== '/~/ws') return reject('404 Not Found');
    target = new URL(u.searchParams.get('url'));
  } catch (e) {
    return reject('400 Bad Request');
  }
  if (!/^wss?:$/.test(target.protocol)) return reject('400 Bad Request');
  if (hostBlocked(target.hostname)) return reject('403 Forbidden');

  const httpUrl = new URL(target.href.replace(/^ws/, 'http'));
  const sess = getSession(req, null, false);
  const headers = {};
  if (req.headers['user-agent']) headers['user-agent'] = req.headers['user-agent'];
  if (req.headers['accept-language']) headers['accept-language'] = req.headers['accept-language'];
  const o = u.searchParams.get('o');
  headers.origin = o && /^https?:\/\/[^/]+$/.test(o) ? o : httpUrl.origin; // ⑥ Origin
  const ck = cookieHeader(sess, httpUrl, false);
  if (ck) headers.cookie = ck; // ① Cookie
  const protocols = String(req.headers['sec-websocket-protocol'] || '').split(',').map((s) => s.trim()).filter(Boolean);

  let up;
  try {
    up = new WebSocket(target.href, protocols, { headers, lookup: safeLookup, followRedirects: true, handshakeTimeout: 20000 });
  } catch (e) {
    return reject('502 Bad Gateway');
  }

  let clientGone = false;
  socket.on('close', () => {
    clientGone = true;
    if (up.readyState === WebSocket.CONNECTING) up.terminate();
  });

  up.on('upgrade', (r) => {
    const sc = r.headers['set-cookie'];
    if (sc && sess) for (const s of sc) storeSetCookie(sess, s, httpUrl);
  });
  up.on('unexpected-response', (rq, rs) => {
    reject(`${rs.statusCode || 502} Upstream Rejected`);
    rs.resume();
  });
  up.on('error', () => {
    if (up.readyState !== WebSocket.OPEN) reject('502 Bad Gateway');
  });

  up.on('open', () => {
    if (clientGone) return up.terminate();
    // 接続先が選んだサブプロトコルをそのままブラウザへ返す
    const wss = new WebSocketServer({ noServer: true, perMessageDeflate: false, handleProtocols: () => up.protocol || false });
    wss.handleUpgrade(req, socket, head, (client) => {
      const iv = setInterval(() => {
        if (client.readyState === WebSocket.OPEN) client.ping();
      }, 25000);
      client.on('message', (d, bin) => {
        if (up.readyState === WebSocket.OPEN) up.send(d, { binary: bin });
      });
      up.on('message', (d, bin) => {
        if (client.readyState === WebSocket.OPEN) client.send(d, { binary: bin });
      });
      client.on('close', (c, r) => {
        clearInterval(iv);
        closeSafe(up, c, r);
      });
      up.on('close', (c, r) => {
        clearInterval(iv);
        closeSafe(client, c, r);
      });
      client.on('error', () => up.terminate());
      up.on('error', () => client.terminate());
    });
  });
});

server.listen(PORT, '0.0.0.0', () => {
  console.log(`web proxy listening on :${PORT}` + (BASIC_AUTH ? ' (basic auth on)' : ''));
});

process.on('unhandledRejection', (e) => console.error('unhandledRejection', e));
process.on('uncaughtException', (e) => console.error('uncaughtException', e));
