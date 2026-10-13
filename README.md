# Web Proxy (Service Worker 方式)

## Render へのデプロイ
1. この3ファイル (server.js / package.json / render.yaml) を GitHub のリポジトリのルートに置く
2. Render で New + > Web Service > リポジトリを選択
   - Build Command: `npm install`
   - Start Command: `node server.js`
3. デプロイを押してしばらく待ち、https://(サーバー名).onrender.comが出たら成功!

[![Deploy to Render](https://render.com/images/deploy-to-render-button.svg)](https://render.com/deploy)

## ローカルで試す
    npm install
    npm start   # http://localhost:3000

## 本家サイト
https://project-claude-proxy-v2.onrender.com/
(パスワードがかかっているので、使いたい人は直接言うか自分でデプロイしてね☆)
