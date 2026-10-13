# Web Proxy (Service Worker 方式)

## Render へのデプロイ
1. この3ファイル (server.js / package.json / render.yaml) を GitHub のリポジトリのルートに置く
2. Render で New + > Web Service > リポジトリを選択
   - Build Command: `npm install`
   - Start Command: `node server.js`
3. 公開用途なら Environment に `BASIC_AUTH` = `user:pass` を設定 (推奨)

## ローカルで試す
    npm install
    npm start   # http://localhost:3000
