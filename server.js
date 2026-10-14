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
 *  YTDLP_PATH    yt-dlp 実行ファイルのパス (既定: ./bin/yt-dlp)
 *  YTDLP_HOSTS   動画モードで許可するドメインをカンマ区切りで指定 ("*" で全て許可)
 *  YTDLP_COOKIES yt-dlp 用 cookies.txt のパス (任意。Render の Secret Files 等。YouTube の bot 判定対策)
 *  YTDLP_MAX     yt-dlp の同時実行数 (既定 2)
 *
 *  動画モード (yt-dlp):
 *   /~/player?u=URL  プレイヤーページ / /~/yt/info  情報取得 / /~/yt/play  Range 対応ストリーム中継
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
const fs = require('fs');
const path_ = require('path');
const os = require('os');
const { execFile } = require('child_process');
const { WebSocketServer, WebSocket } = require('ws');

const PORT = parseInt(process.env.PORT, 10) || 3000;
const BASIC_AUTH = process.env.BASIC_AUTH || '';
const ALLOW_PRIVATE = process.env.ALLOW_PRIVATE === '1';
const PREFIX = '/go/';
const SID_NAME = '__pxsid';
const MAX_REWRITE = 30 * 1024 * 1024; // HTML/CSS を書き換える際の上限
const UPSTREAM_TIMEOUT = 30000; // 応答ヘッダが来るまでの待ち時間

let YTDLP_BIN = process.env.YTDLP_PATH || path_.join(__dirname, 'bin', 'yt-dlp');
const YTDLP_URL = process.env.YTDLP_URL || 'https://github.com/yt-dlp/yt-dlp/releases/latest/download/yt-dlp_linux';
const YTDLP_MAX = parseInt(process.env.YTDLP_MAX, 10) || 2;
const YTDLP_TIMEOUT = 60000;
const YT_CACHE_TTL = 30 * 60 * 1000;
const YTDLP_HOSTS = (process.env.YTDLP_HOSTS ||
  'youtube.com,youtu.be,youtube-nocookie.com,nicovideo.jp,nico.ms,vimeo.com,twitter.com,x.com,tiktok.com,dailymotion.com,twitch.tv,bilibili.com,instagram.com,facebook.com,reddit.com,soundcloud.com')
  .split(',').map((s) => s.trim().toLowerCase()).filter(Boolean);

// Secret Files は読み取り専用のことがあるので、yt-dlp が書き戻せるよう /tmp にコピー
let YT_COOKIE_FILE = '';
if (process.env.YTDLP_COOKIES) {
  try {
    YT_COOKIE_FILE = '/tmp/yt-cookies.txt';
    fs.copyFileSync(process.env.YTDLP_COOKIES, YT_COOKIE_FILE);
  } catch (e) {
    console.error('cookies copy failed:', e.message);
    YT_COOKIE_FILE = '';
  }
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
      if (p.indexOf('/go/') === 0 || p.indexOf('/~/') === 0 || p === '/' || p === '/sw.js' || p === '/healthz') return;
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
  var nopen = window.open;
  window.open = function (url) {
    var a = Array.prototype.slice.call(arguments);
    if (url) a[0] = toProxy(url);
    return nopen.apply(window, a);
  };
  ['pushState', 'replaceState'].forEach(function (k) {
    var o = history[k];
    history[k] = function (s, t, u) {
      return o.call(this, s, t, u === undefined || u === null ? u : toProxy(u));
    };
  });

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
}

/* ---------- トップページのスクリプト ---------- */
function indexMain() {
  var f = document.getElementById('f');
  var inp = document.getElementById('u');
  var chk = document.getElementById('c');
  var st = document.getElementById('s');
  var yt = document.getElementById('y');
  // ナビバー内 (iframe) で開かれたトップページでは、履歴なしチェックを隠してそのまま遷移する
  var framed = window.top !== window;
  if (framed) chk.parentNode.style.display = 'none';

  try {
    chk.checked = localStorage.getItem('px_cloak') === '1';
    yt.checked = localStorage.getItem('px_yt') === '1';
  } catch (e) {}
  chk.addEventListener('change', function () {
    try {
      localStorage.setItem('px_cloak', chk.checked ? '1' : '0');
    } catch (e) {}
  });
  yt.addEventListener('change', function () {
    try {
      localStorage.setItem('px_yt', yt.checked ? '1' : '0');
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
    var ytMode = yt.checked && /^https?:\/\//i.test(url);
    (ytMode ? Promise.resolve() : ensureSW())
      .then(function () {
        var shell = ytMode ? '/~/player?u=' + encodeURIComponent(url) : '/~/shell?u=' + encodeURIComponent(path);
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
          location.href = ytMode ? shell : framed ? path : shell;
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
  var fr = document.getElementById('fr');
  var a = document.getElementById('a');
  var RX = /^\/go\/(https?)\/([^\/?#]+)(\/[^?#]*)?/;

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

  // iframe 内の現在のページを、元のURLとして入力欄に表示
  function show() {
    try {
      if (document.activeElement === a) return;
      var l = fr.contentWindow.location;
      var m = RX.exec(l.pathname);
      var t = m ? m[1] + '://' + m[2] + (m[3] || '/') + l.search + l.hash : '';
      if (a.value !== t) a.value = t;
    } catch (e) {}
  }
  setInterval(show, 500);
  fr.addEventListener('load', show);

  function hist(fn) {
    try {
      fn(fr.contentWindow);
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
    fr.src = '/';
  });
  a.addEventListener('keydown', function (ev) {
    if (ev.key !== 'Enter') return;
    var url = normalize(a.value);
    if (!url) return;
    try {
      fr.src = toPath(url);
      a.blur();
    } catch (e) {}
  });

  var q = new URLSearchParams(location.search).get('u');
  var start = q && /^\/go\/https?\/[^\/]/.test(q) ? q : '/';
  // 外側ページのURLは常に「/」に固定 (開いているサイトによって変わらない)
  try {
    history.replaceState(null, '', '/');
  } catch (e) {}
  ensureSW().then(function () {
    fr.src = start;
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
  #bar{position:fixed;top:0;left:0;right:0;height:44px;display:flex;gap:6px;align-items:center;padding:6px 8px;
       background:#171a23;border-bottom:1px solid #2b3040;font-family:system-ui,sans-serif}
  #bar button{width:34px;height:32px;border:0;border-radius:8px;background:#242938;color:#e8eaf0;font-size:16px;cursor:pointer;flex:none}
  #bar button:hover{background:#2f3550}
  #a{flex:1;min-width:0;height:32px;padding:0 14px;border-radius:16px;border:1px solid #2b3040;background:#0f1117;
     color:#e8eaf0;font-size:14px;outline:none}
  #a:focus{border-color:#5b8cff}
  #fr{position:fixed;top:44px;left:0;right:0;bottom:0;width:100%;height:calc(100% - 44px);border:0;background:#fff}
</style>
</head>
<body>
<div id="bar">
  <button id="b" title="戻る">&#8592;</button>
  <button id="n" title="進む">&#8594;</button>
  <button id="r" title="再読み込み">&#10227;</button>
  <button id="h" title="ホーム">&#8962;</button>
  <input id="a" type="text" placeholder="URL または検索ワードを入力" autocomplete="off" spellcheck="false">
</div>
<iframe id="fr" allow="fullscreen; autoplay; clipboard-read; clipboard-write" allowfullscreen></iframe>
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
  <br>
  <label class="chk"><input type="checkbox" id="y"> 動画モード (yt-dlp で YouTube 等の動画を再生)</label>
  <p id="s" class="st"></p>
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

function authOk(req) {
  if (!BASIC_AUTH) return true;
  const h = req.headers.authorization || '';
  if (!h.startsWith('Basic ')) return false;
  const a = Buffer.from(Buffer.from(h.slice(6), 'base64').toString());
  const b = Buffer.from(BASIC_AUTH);
  return a.length === b.length && crypto.timingSafeEqual(a, b);
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
      res.setHeader(
        'Set-Cookie',
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

  const inj =
    '<script>window.__PX_COOKIE=' + JSON.stringify(cookieStr || '').replace(/</g, '\\u003c') + ';</script>' +
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

const SKIP_REQ = /^(host|connection|keep-alive|proxy-|te$|trailer|upgrade$|transfer-encoding|sec-fetch-|x-forwarded-|x-render|x-request|rndr|cf-|cdn-loop|true-client-ip|forwarded|via|x-real-ip|accept-encoding|cookie|referer|origin|content-length$)/i;
const SKIP_RES = /^(set-cookie|content-security-policy|content-security-policy-report-only|x-frame-options|strict-transport-security|public-key-pins|public-key-pins-report-only|cross-origin-opener-policy|cross-origin-embedder-policy|cross-origin-resource-policy|connection|keep-alive|transfer-encoding|upgrade|proxy-authenticate|proxy-authorization|te|trailer|alt-svc|link|report-to|nel|expect-ct|clear-site-data|access-control-.*)$/i;

function buildUpstreamHeaders(req, target, sess) {
  const h = {};
  for (const [k, v] of Object.entries(req.headers)) {
    if (SKIP_REQ.test(k)) continue;
    if (k === 'authorization' && BASIC_AUTH) continue;
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
  return h;
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
  const isHttps = target.protocol === 'https:';
  const upHeaders = buildUpstreamHeaders(req, target, sess);

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

      if (isHtml && sess) sess.last = target.origin;

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
 *  動画モード (yt-dlp)
 *    /~/player        プレイヤーページ
 *    /~/yt/info       yt-dlp で情報取得 -> 再生可能な形式一覧 (JSON)
 *    /~/yt/play       形式の直URLを Range 対応でストリーム中継 (&dl=1 でダウンロード)
 *  ffmpeg 不要: 映像+音声が一体になった progressive 形式 (mp4/webm) と音声のみ形式を使う
 * ====================================================================== */

function playerMain() {
  var qs = new URLSearchParams(location.search);
  var cur = qs.get('u') || '';
  var v = document.getElementById('v');
  var sel = document.getElementById('sel');
  var ttl = document.getElementById('ttl');
  var msg = document.getElementById('msg');
  var inp = document.getElementById('inp');
  var dl = document.getElementById('dl');
  var info = null;

  function srcFor(id) {
    return '/~/yt/play?url=' + encodeURIComponent(cur) + '&f=' + encodeURIComponent(id);
  }
  function play(keep) {
    if (!info) return;
    var id = sel.value;
    var tm = keep ? v.currentTime : 0;
    var was = !v.paused;
    v.src = srcFor(id);
    dl.href = srcFor(id) + '&dl=1';
    v.addEventListener(
      'loadedmetadata',
      function once() {
        v.removeEventListener('loadedmetadata', once);
        if (tm) v.currentTime = tm;
      }
    );
    var p = v.play();
    if (p && p.catch) p.catch(function () {});
    if (keep && !was) v.pause();
  }
  function load(u) {
    cur = u;
    info = null;
    sel.innerHTML = '';
    ttl.textContent = '';
    dl.style.display = 'none';
    v.removeAttribute('src');
    v.load();
    msg.textContent = 'yt-dlp で取得中... (数秒〜数十秒かかります)';
    fetch('/~/yt/info?url=' + encodeURIComponent(u), { credentials: 'same-origin' })
      .then(function (r) {
        return r.json();
      })
      .then(function (d) {
        if (d.error) throw new Error(d.error);
        info = d;
        ttl.textContent = d.title || '';
        document.title = (d.title || 'Data Center').slice(0, 60);
        d.formats.forEach(function (f) {
          var o = document.createElement('option');
          o.value = f.id;
          o.textContent = f.label;
          sel.appendChild(o);
        });
        msg.textContent = '';
        dl.style.display = '';
        play(false);
      })
      .catch(function (e) {
        msg.textContent = 'エラー: ' + e.message;
      });
  }
  sel.addEventListener('change', function () {
    play(true);
  });
  v.addEventListener('error', function () {
    if (info) msg.textContent = '再生に失敗しました。別の画質を選ぶか、時間をおいて再読み込みしてください。';
  });
  v.addEventListener('playing', function () {
    msg.textContent = '';
  });
  document.getElementById('f').addEventListener('submit', function (ev) {
    ev.preventDefault();
    var s = inp.value.trim();
    if (!/^https?:\/\//i.test(s)) {
      msg.textContent = 'http(s):// で始まる URL を入力してください';
      return;
    }
    try {
      history.replaceState(null, '', '/~/player?u=' + encodeURIComponent(s));
    } catch (e) {}
    load(s);
  });
  document.getElementById('h').addEventListener('click', function () {
    location.href = '/';
  });
  inp.value = cur;
  if (cur) load(cur);
  else msg.textContent = '動画の URL を入力してください';
}

const PLAYER_HTML = `<!doctype html>
<html lang="ja">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1">
<title>Data Center</title>
<link rel="icon" type="image/svg+xml" href="/favicon.svg">
<style>
  :root{color-scheme:dark}
  *{box-sizing:border-box}
  html,body{margin:0;min-height:100%;background:#0f1117;color:#e8eaf0;
       font-family:system-ui,-apple-system,"Segoe UI","Hiragino Sans","Noto Sans JP",sans-serif}
  #bar{display:flex;gap:6px;align-items:center;padding:6px 8px;background:#171a23;border-bottom:1px solid #2b3040}
  #bar button{height:32px;padding:0 12px;border:0;border-radius:8px;background:#242938;color:#e8eaf0;font-size:14px;cursor:pointer;flex:none}
  #bar button:hover{background:#2f3550}
  #inp{flex:1;min-width:0;height:32px;padding:0 14px;border-radius:16px;border:1px solid #2b3040;background:#0f1117;color:#e8eaf0;font-size:14px;outline:none}
  #inp:focus{border-color:#5b8cff}
  #f{display:flex;gap:6px;flex:1;min-width:0}
  main{max-width:1100px;margin:0 auto;padding:14px}
  video{width:100%;max-height:76vh;background:#000;border-radius:10px}
  #ttl{font-size:18px;font-weight:600;margin:12px 0 8px;word-break:break-word}
  .row{display:flex;gap:10px;align-items:center;flex-wrap:wrap}
  select{height:32px;border-radius:8px;border:1px solid #2b3040;background:#171a23;color:inherit;padding:0 8px;font-size:14px}
  #dl{color:#8fb0ff;font-size:14px;text-decoration:none}
  #dl:hover{text-decoration:underline}
  #msg{min-height:1.4em;margin:10px 0 0;font-size:13px;color:#ffb86b;white-space:pre-wrap}
</style>
</head>
<body>
<div id="bar">
  <button id="h" title="ホーム">&#8962;</button>
  <form id="f" autocomplete="off">
    <input id="inp" type="text" placeholder="動画の URL (YouTube など)" spellcheck="false">
    <button type="submit">再生</button>
  </form>
</div>
<main>
  <video id="v" controls playsinline preload="metadata"></video>
  <div id="ttl"></div>
  <div class="row"><select id="sel"></select><a id="dl" style="display:none" download>ダウンロード</a></div>
  <p id="msg"></p>
</main>
<script>(${playerMain.toString()})();</script>
</body>
</html>`;

let ytActive = 0;
const ytCache = new Map(); // url -> { t, title, duration, formats:{id:{url,headers,ext,list}}, list:[] }

function ytAllowed(raw) {
  let u;
  try {
    u = new URL(raw);
  } catch (e) {
    return false;
  }
  if (u.protocol !== 'http:' && u.protocol !== 'https:') return false;
  if (hostBlocked(u.hostname)) return false;
  if (YTDLP_HOSTS.includes('*')) return true;
  const h = u.hostname.toLowerCase();
  return YTDLP_HOSTS.some((d) => h === d || h.endsWith('.' + d));
}

const YT_EXT = new Set(['mp4', 'webm', 'm4a', 'mp3', 'ogg', 'opus', 'aac']);

function summarizeInfo(info) {
  if (info && Array.isArray(info.entries) && info.entries.length) info = info.entries[0];
  const all = (info && info.formats) || [];
  const ok = all.filter(
    (f) => f && f.url && (f.protocol === 'https' || f.protocol === 'http') && YT_EXT.has(f.ext) && f.format_note !== 'storyboard'
  );
  const video = ok
    .filter((f) => f.vcodec && f.vcodec !== 'none' && f.acodec && f.acodec !== 'none')
    .sort((a, b) => (b.height || 0) - (a.height || 0) || (b.tbr || 0) - (a.tbr || 0));
  const audio = ok
    .filter((f) => (!f.vcodec || f.vcodec === 'none') && f.acodec && f.acodec !== 'none')
    .sort((a, b) => (b.abr || b.tbr || 0) - (a.abr || a.tbr || 0));
  const picked = [];
  const seen = new Set();
  for (const f of video) {
    const k = (f.height || 0) + f.ext;
    if (seen.has(k)) continue;
    seen.add(k);
    picked.push({ f, kind: 'video', label: (f.height ? f.height + 'p' : f.format_note || '動画') + ' ' + f.ext });
    if (picked.length >= 8) break;
  }
  for (const f of audio.slice(0, 2)) {
    picked.push({ f, kind: 'audio', label: '音声のみ ' + (f.abr ? Math.round(f.abr) + 'kbps ' : '') + f.ext });
  }
  const formats = {};
  const list = [];
  for (const p of picked) {
    const id = String(p.f.format_id);
    if (formats[id]) continue;
    const headers = Object.assign({}, p.f.http_headers || {});
    if (p.f.cookies) headers.Cookie = p.f.cookies;
    formats[id] = { url: p.f.url, headers, ext: p.f.ext };
    list.push({ id, label: p.label, kind: p.kind, ext: p.f.ext });
  }
  return { title: String((info && info.title) || 'video'), duration: info && info.duration, formats, list };
}

/* ---- yt-dlp 本体の自動取得 (ビルドコマンドに依存しない) ---- */
let ytdlpPromise = null;

function downloadTo(url, dest, redirects) {
  return new Promise((resolve, reject) => {
    https
      .get(url, { headers: { 'user-agent': 'sw-web-proxy' } }, (r) => {
        if ([301, 302, 303, 307, 308].includes(r.statusCode) && r.headers.location) {
          r.resume();
          if (redirects >= 6) return reject(new Error('too many redirects'));
          return downloadTo(new URL(r.headers.location, url).href, dest, redirects + 1).then(resolve, reject);
        }
        if (r.statusCode !== 200) {
          r.resume();
          return reject(new Error('HTTP ' + r.statusCode));
        }
        const f = fs.createWriteStream(dest);
        r.pipe(f);
        f.on('finish', () => f.close(() => resolve()));
        f.on('error', reject);
        r.on('error', reject);
      })
      .on('error', reject);
  });
}

function ensureYtdlp() {
  if (fs.existsSync(YTDLP_BIN)) return Promise.resolve();
  if (!ytdlpPromise) {
    ytdlpPromise = (async () => {
      let lastErr = new Error('unknown');
      for (const dest of [YTDLP_BIN, path_.join(os.tmpdir(), 'yt-dlp')]) {
        const part = dest + '.part';
        try {
          fs.mkdirSync(path_.dirname(dest), { recursive: true });
          console.log('downloading yt-dlp ->', dest);
          await downloadTo(YTDLP_URL, part, 0);
          fs.chmodSync(part, 0o755);
          fs.renameSync(part, dest);
          YTDLP_BIN = dest;
          console.log('yt-dlp ready');
          return;
        } catch (e) {
          lastErr = e;
          try {
            fs.unlinkSync(part);
          } catch (e2) {}
        }
      }
      throw lastErr;
    })().finally(() => {
      ytdlpPromise = null;
    });
  }
  return ytdlpPromise;
}

function ytResolve(url, cb) {
  const c = ytCache.get(url);
  if (c && Date.now() - c.t < YT_CACHE_TTL) return cb(null, c);
  if (ytActive >= YTDLP_MAX) return cb(new Error('サーバーが混み合っています。少し待ってからもう一度お試しください。'));
  const args = ['--ignore-config', '-J', '--no-playlist', '--no-warnings', '--socket-timeout', '15', '--js-runtimes', 'node'];
  if (YT_COOKIE_FILE) args.push('--cookies', YT_COOKIE_FILE);
  args.push('--', url);
  ytActive++;
  ensureYtdlp().then(
    () => runYtdlp(args, url, cb),
    (e) => {
      ytActive--;
      cb(new Error('yt-dlp を用意できませんでした: ' + e.message));
    }
  );
}

function runYtdlp(args, url, cb) {
  execFile(YTDLP_BIN, args, { timeout: YTDLP_TIMEOUT, maxBuffer: 64 * 1024 * 1024 }, (err, stdout, stderr) => {
    ytActive--;
    if (err) {
      if (err.code === 'ENOENT' || err.code === 'EACCES') {
        try {
          fs.unlinkSync(YTDLP_BIN);
        } catch (e) {}
        return cb(new Error('yt-dlp を実行できませんでした (' + err.code + ')。もう一度お試しください。'));
      }
      const last = String(stderr || err.message).trim().split('\n').filter((l) => /ERROR/.test(l)).pop() || err.message;
      return cb(new Error(last.replace(/^ERROR:\s*/, '').slice(0, 400)));
    }
    let entry;
    try {
      entry = summarizeInfo(JSON.parse(stdout));
    } catch (e) {
      return cb(new Error('yt-dlp の出力を解釈できませんでした'));
    }
    if (!entry.list.length) return cb(new Error('再生可能な形式が見つかりませんでした (映像+音声が一体の mp4/webm がありません)'));
    entry.t = Date.now();
    if (ytCache.size > 200) ytCache.delete(ytCache.keys().next().value);
    ytCache.set(url, entry);
    cb(null, entry);
  });
}

function sendJson(res, code, obj) {
  res.writeHead(code, { 'content-type': 'application/json; charset=utf-8', 'cache-control': 'no-store' });
  res.end(JSON.stringify(obj));
}

function ytPipe(req, res, fmtUrl, hdrs, dlName, redirects) {
  let u;
  try {
    u = new URL(fmtUrl);
  } catch (e) {
    return errorPage(res, 502, '動画URLが不正です');
  }
  if (!/^https?:$/.test(u.protocol)) return errorPage(res, 502, '動画URLが不正です');
  if (hostBlocked(u.hostname)) return errorPage(res, 403, 'このアドレスへは接続できません');
  const isHttps = u.protocol === 'https:';
  const h = {};
  for (const [k, v] of Object.entries(hdrs || {})) {
    if (!/^(host|accept-encoding|content-length|range|if-range|connection)$/i.test(k)) h[k] = v;
  }
  h['accept-encoding'] = 'identity';
  if (req.headers.range) h.range = req.headers.range;
  if (req.headers['if-range']) h['if-range'] = req.headers['if-range'];

  const up = (isHttps ? https : http).request(
    {
      hostname: u.hostname.replace(/^\[|\]$/g, ''),
      port: u.port || (isHttps ? 443 : 80),
      path: u.pathname + u.search,
      method: 'GET',
      headers: h,
      agent: isHttps ? httpsAgent : httpAgent
    },
    (ur) => {
      clearTimeout(timer);
      const st = ur.statusCode;
      if ([301, 302, 303, 307, 308].includes(st) && ur.headers.location && redirects < 5) {
        ur.resume();
        let next;
        try {
          next = new URL(ur.headers.location, u).href;
        } catch (e) {
          return errorPage(res, 502, 'リダイレクト先が不正です');
        }
        return ytPipe(req, res, next, hdrs, dlName, redirects + 1);
      }
      const oh = {};
      for (const k of ['content-length', 'content-range', 'accept-ranges', 'last-modified', 'etag']) {
        if (ur.headers[k] !== undefined) oh[k] = ur.headers[k];
      }
      const ct = String(ur.headers['content-type'] || '');
      oh['content-type'] = /^(video|audio)\//i.test(ct) ? ct : 'application/octet-stream';
      oh['x-content-type-options'] = 'nosniff';
      oh['content-security-policy'] = 'sandbox';
      oh['cache-control'] = 'private, max-age=0';
      if (dlName) oh['content-disposition'] = "attachment; filename*=UTF-8''" + encodeURIComponent(dlName);
      res.writeHead(st, oh);
      ur.pipe(res);
      ur.on('error', () => res.destroy());
    }
  );
  const timer = setTimeout(() => up.destroy(new Error('動画サーバーが応答しません (タイムアウト)')), UPSTREAM_TIMEOUT);
  up.on('error', (e) => {
    clearTimeout(timer);
    errorPage(res, 502, e.message);
  });
  res.on('close', () => {
    if (!res.writableEnded) up.destroy();
  });
  up.end();
}

function handleYt(req, res, path) {
  const qs = new URL(req.url, 'http://x').searchParams;
  const url = qs.get('url') || '';
  if (!ytAllowed(url)) {
    return sendJson(res, 400, { error: 'このURLは動画モードでは利用できません (許可されたサイトのみ対応)' });
  }
  if (path === '/~/yt/info') {
    return ytResolve(url, (err, e) => {
      if (err) return sendJson(res, 502, { error: err.message });
      sendJson(res, 200, { title: e.title, duration: e.duration, formats: e.list });
    });
  }
  // /~/yt/play
  const fid = qs.get('f') || '';
  ytResolve(url, (err, e) => {
    if (err) return errorPage(res, 502, err.message);
    const fm = e.formats[fid];
    if (!fm) return errorPage(res, 404, '指定された形式がありません');
    const name = qs.get('dl') ? e.title.replace(/[\\/:*?"<>|\r\n]+/g, '_').slice(0, 120) + '.' + fm.ext : '';
    ytPipe(req, res, fm.url, fm.headers, name, 0);
  });
}

const server = http.createServer(async (req, res) => {
  try {
    const path = req.url.split('?')[0];

    if (path === '/healthz') {
      res.writeHead(200, { 'content-type': 'text/plain' });
      return res.end('ok');
    }
    if (!authOk(req)) {
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
    if (path === '/~/client.js') {
      res.writeHead(200, { 'content-type': 'application/javascript; charset=utf-8', 'cache-control': 'no-cache' });
      return res.end(CLIENT_JS);
    }
    if (path === '/~/shell') {
      res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-cache' });
      return res.end(SHELL_HTML);
    }
    if (path === '/~/player') {
      res.writeHead(200, { 'content-type': 'text/html; charset=utf-8', 'cache-control': 'no-cache' });
      return res.end(PLAYER_HTML);
    }
    if ((path === '/~/yt/info' || path === '/~/yt/play') && (req.method === 'GET' || req.method === 'HEAD')) {
      return handleYt(req, res, path);
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
  ensureYtdlp().catch((e) => console.error('yt-dlp download failed:', e.message)); // 起動時に先読み
});

process.on('unhandledRejection', (e) => console.error('unhandledRejection', e));
process.on('uncaughtException', (e) => console.error('uncaughtException', e));
