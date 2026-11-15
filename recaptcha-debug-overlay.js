/**
 * recaptcha-debug-overlay.js
 * ページ右下に「RC」ボタンを出し、押すと Service Worker のログとページ内エラーを表示する。
 * DevTools が使えない環境向け。
 *
 * 読み込み方（どちらか）:
 *   A) recaptcha-compat.js の injectOverlay() で HTML に自動挿入（debug: true のとき）
 *   B) プロキシのトップページ(index.html)に <script src="/recaptcha-debug-overlay.js"></script>
 */
(function () {
  'use strict';
  if (window.__rcOverlay) return;
  window.__rcOverlay = true;
  // 広告などの小さい iframe には出さない
  if (window.innerWidth < 300 || window.innerHeight < 200) return;

  var lines = [];
  var MAX = 400;
  var panel, listEl, countEl;

  function add(line) {
    lines.push(line);
    if (lines.length > MAX) lines.shift();
    if (listEl) render();
    updateBadge();
  }

  function ts() {
    return new Date().toISOString().slice(11, 23);
  }

  // ---- Service Worker からのログ受信 ----
  var channel = null;
  try {
    channel = new BroadcastChannel('rc-debug');
    channel.onmessage = function (e) {
      var d = e.data || {};
      if (d.type === 'log') add(d.line);
      if (d.type === 'history') {
        lines = d.lines.concat(lines.filter(function (l) { return l.indexOf('[page') === 0; }));
        render();
        updateBadge();
      }
    };
    channel.postMessage({ type: 'hello' }); // 過去ログを要求
  } catch (_) {
    add('[page] BroadcastChannel が使えません。/__rc-debug を別タブで開いてください。');
  }

  // ---- ページ内エラーの収集 ----
  window.addEventListener('error', function (e) {
    add('[page-error] ' + ts() + ' ' + (e.message || 'error') + (e.filename ? ' @ ' + e.filename + ':' + e.lineno : ''));
  });
  window.addEventListener('unhandledrejection', function (e) {
    var r = e.reason;
    add('[page-rejection] ' + ts() + ' ' + (r && r.message ? r.message : String(r)));
  });
  var origErr = console.error;
  console.error = function () {
    try {
      add('[console.error] ' + ts() + ' ' + Array.prototype.map.call(arguments, function (a) {
        return typeof a === 'string' ? a : (a && a.message) || JSON.stringify(a);
      }).join(' '));
    } catch (_) { /* noop */ }
    return origErr.apply(console, arguments);
  };

  // ---- プロキシサーバー側 (recaptcha-compat) のログ取得 ----
  // サーバー側のログは BroadcastChannel では届かないため HTTP で定期取得する。
  // /~/ 配下はプロキシのフックを素通りするパス。
  var seen = {};
  function pollServer() {
    if (document.visibilityState === 'hidden' || !window.fetch) return;
    fetch('/~/rc-debug', { cache: 'no-store', credentials: 'same-origin' })
      .then(function (r) { return r.ok ? r.text() : ''; })
      .then(function (t) {
        t.split('\n').forEach(function (l) {
          if (!l || l.charAt(0) === '(' || seen[l]) return;
          seen[l] = 1;
          add('[server] ' + l);
        });
      })
      .catch(function () { /* noop */ });
  }
  setInterval(pollServer, 3000);
  pollServer();

  // ---- UI ----
  var host = document.createElement('div');
  host.style.cssText = 'all:initial;position:fixed;right:12px;bottom:12px;z-index:2147483647;';
  var root = host.attachShadow ? host.attachShadow({ mode: 'open' }) : host;
  root.innerHTML =
    '<style>' +
    '.btn{font:600 12px system-ui,sans-serif;background:#1a73e8;color:#fff;border:0;border-radius:16px;padding:8px 12px;cursor:pointer;box-shadow:0 2px 8px rgba(0,0,0,.35)}' +
    '.btn .n{background:#d93025;border-radius:8px;padding:0 6px;margin-left:6px;display:none}' +
    '.panel{display:none;position:fixed;left:8px;right:8px;bottom:56px;max-height:55vh;background:#111;color:#ddd;border-radius:8px;box-shadow:0 4px 18px rgba(0,0,0,.5);flex-direction:column;font:11px/1.45 ui-monospace,Menlo,Consolas,monospace}' +
    '.bar{display:flex;gap:6px;padding:6px;border-bottom:1px solid #333}' +
    '.bar button{font:11px system-ui,sans-serif;background:#333;color:#fff;border:0;border-radius:4px;padding:4px 8px;cursor:pointer}' +
    '.list{overflow:auto;padding:6px;white-space:pre-wrap;word-break:break-all;flex:1}' +
    '.err{color:#ff8a80}.warn{color:#ffd180}.ok{color:#a5d6a7}' +
    '</style>' +
    '<button class="btn" id="t">RC<span class="n" id="n"></span></button>' +
    '<div class="panel" id="p"><div class="bar">' +
    '<button id="copy">コピー</button><button id="clear">クリア</button><button id="close">閉じる</button>' +
    '</div><div class="list" id="l"></div></div>';

  function $(id) { return root.getElementById ? root.getElementById(id) : root.querySelector('#' + id); }

  function esc(s) {
    return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;');
  }
  function cls(l) {
    if (/WARN|error|rejection|\b[45]\d\d\b/i.test(l)) return 'err';
    if (/rewritten/.test(l)) return 'ok';
    return '';
  }
  function render() {
    listEl.innerHTML = lines.map(function (l) {
      return '<div class="' + cls(l) + '">' + esc(l) + '</div>';
    }).join('');
    listEl.scrollTop = listEl.scrollHeight;
  }
  function updateBadge() {
    if (!countEl) return;
    var errs = lines.filter(function (l) { return cls(l) === 'err'; }).length;
    countEl.style.display = errs ? 'inline' : 'none';
    countEl.textContent = errs;
  }

  function mount() {
    document.documentElement.appendChild(host);
    panel = $('p'); listEl = $('l'); countEl = $('n');
    $('t').onclick = function () {
      panel.style.display = panel.style.display === 'flex' ? 'none' : 'flex';
      render();
    };
    $('close').onclick = function () { panel.style.display = 'none'; };
    $('clear').onclick = function () { lines = []; render(); updateBadge(); };
    $('copy').onclick = function () {
      var text = lines.join('\n');
      try {
        navigator.clipboard.writeText(text);
      } catch (_) {
        var ta = document.createElement('textarea');
        ta.value = text; document.body.appendChild(ta); ta.select();
        try { document.execCommand('copy'); } catch (__) { /* noop */ }
        ta.remove();
      }
    };
    render(); updateBadge();
  }

  if (document.documentElement) mount();
  else document.addEventListener('DOMContentLoaded', mount);
})();
