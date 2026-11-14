/**
 * recaptcha-compat.js
 * Service Worker 型 Web プロキシ用 reCAPTCHA 互換モジュール
 *
 * 目的:
 *   プロキシ経由でも reCAPTCHA ウィジェットが「Invalid domain for site key」や
 *   ロード失敗などのエラーを出さず、人間が普通に操作できるようにする。
 *   ※ CAPTCHA の自動解答やスコアの偽装は行わない（人間の操作が前提）。
 *
 * 主な原因と対処:
 *   1. anchor/bframe の `co` パラメータ（埋め込み元オリジン）にプロキシのオリジンが入り、
 *      サイトキーのドメイン検証で弾かれる → 実際のページのオリジンに書き換える
 *   2. Origin/Referer 等にプロキシのホスト名が漏れる → 除去/補正する
 *   3. X-Frame-Options / CSP frame-ancestors 等で iframe 表示がブロックされる → ヘッダ除去
 *
 * 読み込み (classic SW):
 *   importScripts('/recaptcha-compat.js');   // self.createRecaptchaCompat が生える
 *
 * 組み込み例 (Ultraviolet / 自作プロキシ共通のイメージ):
 *
 *   const recaptcha = createRecaptchaCompat({
 *     proxyOrigin: self.location.origin,
 *     decodeUrl: (u) => __uv$config.decodeUrl(u.slice(location.origin.length + __uv$config.prefix.length)),
 *     // ↑ 「プロキシURL → 本来のURL文字列」に変換する関数をあなたのプロキシに合わせて渡す
 *     encodeUrl: (realUrl) => location.origin + __uv$config.prefix + __uv$config.encodeUrl(realUrl),
 *     // ↑ 「本来のURL → プロキシURL」に変換する関数
 *   });
 *
 *   self.addEventListener('fetch', (event) => {
 *     event.respondWith((async () => {
 *       const ctx = await recaptcha.createContext(event);   // 本来のURLと埋め込み元ページURLを解決
 *       if (ctx.isRecaptcha) {
 *         const { url, headers } = recaptcha.rewriteRequest(ctx, event.request.headers);
 *         // ↓ 既存のプロキシの「実際にサーバーへ fetch する処理」に url / headers を渡す
 *         const res = await yourProxyFetch(url.href, { method: event.request.method, headers,
 *                                                       body: event.request.body });
 *         return recaptcha.rewriteResponse(ctx, res);
 *       }
 *       return yourExistingHandler(event);                   // それ以外は既存処理
 *     })());
 *   });
 */
(function (global) {
  'use strict';

  const RECAPTCHA_HOSTS = new Set([
    'www.google.com',
    'www.recaptcha.net',
    'recaptcha.net',
    'www.gstatic.com',
    'www.gstatic.cn',
  ]);

  // iframe 表示を妨げるレスポンスヘッダ
  const STRIP_RESPONSE_HEADERS = [
    'x-frame-options',
    'content-security-policy',
    'content-security-policy-report-only',
    'cross-origin-opener-policy',
    'cross-origin-embedder-policy',
    'cross-origin-resource-policy',
  ];

  // プロキシ自身を示し得る（漏れると弾かれる）リクエストヘッダ
  const LEAKY_REQUEST_HEADERS = ['x-forwarded-for', 'x-forwarded-host', 'x-forwarded-proto', 'x-real-ip', 'via', 'forwarded'];

  // `co` パラメータを持つエンドポイント
  const CO_PATH_RE = /\/recaptcha\/(?:api2|enterprise)\/(?:anchor|bframe)$/;

  /** reCAPTCHA の URL か */
  function isRecaptchaUrl(url) {
    return RECAPTCHA_HOSTS.has(url.hostname) && url.pathname.startsWith('/recaptcha/');
  }

  /** `co` パラメータのエンコード/デコード（base64 の '=' を '.' に置換した形式） */
  function encodeCo(origin) {
    const u = new URL(origin);
    const port = u.port || (u.protocol === 'https:' ? '443' : '80');
    const raw = u.protocol + '//' + u.hostname + ':' + port;
    return btoa(raw).replace(/\+/g, '-').replace(/\//g, '_').replace(/=/g, '.');
  }

  function decodeCo(co) {
    try {
      const b64 = co.replace(/\./g, '=').replace(/-/g, '+').replace(/_/g, '/');
      return atob(b64); // 例: https://example.com:443
    } catch (_) {
      return null;
    }
  }

  function createRecaptchaCompat(opts) {
    const proxyOrigin = opts.proxyOrigin;
    const proxyHost = new URL(proxyOrigin).hostname;
    const decodeUrl = opts.decodeUrl; // proxyUrl(string) -> realUrl(string)
    const debug = !!opts.debug;       // true で診断ログを記録する（DevTools なしでも /__rc-debug で閲覧可）

    // 診断ログ（直近200件をメモリに保持）
    const logs = [];
    function log() {
      if (!debug) return;
      const line = new Date().toISOString() + ' ' +
        Array.prototype.map.call(arguments, (x) => (typeof x === 'string' ? x : JSON.stringify(x))).join(' ');
      logs.push(line);
      if (logs.length > 200) logs.shift();
      try { console.log(line); } catch (_) { /* noop */ }
    }

    /**
     * `<プロキシのオリジン>/__rc-debug` を開くとログがテキストで見られる。
     * fetch ハンドラの先頭で呼ぶ: const d = recaptcha.handleDebug(event.request); if (d) return d;
     */
    function handleDebug(request) {
      const u = new URL(request.url);
      if (u.origin !== proxyOrigin || u.pathname !== '/__rc-debug') return null;
      if (u.searchParams.has('clear')) logs.length = 0;
      const body = logs.length ? logs.join('\n') : '(ログなし: reCAPTCHA関連のリクエストがまだ処理されていません)';
      return new Response(body, { headers: { 'content-type': 'text/plain; charset=utf-8', 'cache-control': 'no-store' } });
    }

    function safeDecode(u) {
      try {
        return new URL(decodeUrl(u));
      } catch (_) {
        return null;
      }
    }

    /**
     * fetch イベントから「本来のURL」と「埋め込み元ページの本来のURL」を解決する。
     * ページURLは clientId → referrer の順で探す。
     */
    async function createContext(event) {
      const realUrl = safeDecode(event.request.url);
      const ctx = { realUrl, pageUrl: null, isRecaptcha: !!realUrl && isRecaptchaUrl(realUrl) };
      if (!ctx.isRecaptcha) return ctx;

      // 1) 要求元クライアント（iframe の場合は親ドキュメント）
      const id = event.clientId || event.resultingClientId;
      if (id && global.clients) {
        try {
          const client = await global.clients.get(event.clientId);
          if (client) ctx.pageUrl = safeDecode(client.url);
        } catch (_) { /* noop */ }
      }
      // 2) Referrer からのフォールバック
      if (!ctx.pageUrl && event.request.referrer) {
        ctx.pageUrl = safeDecode(event.request.referrer);
      }
      // 3) 親が reCAPTCHA 自身（anchor→bframe 等）なら埋め込み元は `co` から復元できるので null のまま
      if (ctx.pageUrl && isRecaptchaUrl(ctx.pageUrl)) ctx.pageUrl = null;

      // 4) まだ不明なら、開いているウィンドウのうち reCAPTCHA 以外の本来のページを探す
      if (!ctx.pageUrl && global.clients) {
        try {
          const wins = await global.clients.matchAll({ type: 'window', includeUncontrolled: true });
          for (const w of wins) {
            const u = safeDecode(w.url);
            if (u && !isRecaptchaUrl(u) && u.hostname !== proxyHost) {
              // 可視中・フォーカス中のウィンドウを優先
              if (!ctx.pageUrl || w.focused) ctx.pageUrl = u;
            }
          }
        } catch (_) { /* noop */ }
      }
      log('[ctx]', ctx.realUrl.href, '<- page:', ctx.pageUrl ? ctx.pageUrl.href : null);
      return ctx;
    }

    /** リクエストの書き換え。戻り値: { url: URL, headers: Headers } */
    function rewriteRequest(ctx, srcHeaders) {
      const url = new URL(ctx.realUrl.href);
      const headers = new Headers(srcHeaders);

      // (1) `co` をプロキシのオリジン → 実ページのオリジンへ
      if (CO_PATH_RE.test(url.pathname) && url.searchParams.has('co')) {
        const current = decodeCo(url.searchParams.get('co'));
        let currentHost = null;
        try { currentHost = current && new URL(current).hostname; } catch (_) { /* noop */ }

        log('[co] co =', current, '| proxyHost =', proxyHost, '| page =', ctx.pageUrl ? ctx.pageUrl.origin : null);

        if (ctx.pageUrl && (currentHost === proxyHost || !currentHost || opts.forceCo)) {
          url.searchParams.set('co', encodeCo(ctx.pageUrl.origin));
          log('[co] rewritten ->', ctx.pageUrl.origin);
        } else if (!ctx.pageUrl) {
          log('[co] WARN: 埋め込み元ページを特定できず co を書き換えられません');
        }
      }

      // (2) プロキシのホスト名が漏れるヘッダを除去・補正
      for (const h of LEAKY_REQUEST_HEADERS) headers.delete(h);
      for (const name of ['origin', 'referer']) {
        const v = headers.get(name);
        if (v && v.includes(proxyHost)) {
          const real = safeDecode(v);
          if (real) headers.set(name, name === 'origin' ? real.origin : real.href);
          else headers.delete(name);
        }
      }
      // iframe ナビゲーション時の Referer は埋め込み元ページ（オリジンのみ）
      if (ctx.pageUrl && CO_PATH_RE.test(url.pathname)) {
        headers.set('referer', ctx.pageUrl.origin + '/');
      }
      return { url, headers };
    }

    /** レスポンスのヘッダを iframe 表示可能にして返す */
    function rewriteResponse(ctx, response) {
      log('[res]', response.status, ctx.realUrl.hostname + ctx.realUrl.pathname);
      const headers = new Headers(response.headers);
      for (const h of STRIP_RESPONSE_HEADERS) headers.delete(h);
      return new Response(response.body, {
        status: response.status,
        statusText: response.statusText,
        headers,
      });
    }

    return { createContext, rewriteRequest, rewriteResponse, handleDebug, isRecaptchaUrl, encodeCo, decodeCo };
  }

  global.createRecaptchaCompat = createRecaptchaCompat;
})(typeof self !== 'undefined' ? self : globalThis);
