# Web Proxy (Service Worker 方式)(Render専用)
みんな大好きClaudeニキに作ってもらいました。

## 注意点
①YouTubeは現在動きません。正確には、開くけど動画が再生できません。  
　フィルタリングソフトでYouTubeがブロックされている場合、ログインがブロックされて詰みます。
②reCAPCHAやCloudflareなどのBot対策がされているサイトだとアクセスがブロックされて詰みます。  
③制作者は、このプロキシを使って発生したいかなる損害も負わず、すべて使用者の責任にあるものとします。  

# ※ここから先の内容を閲覧することは①から③の内容に同意したことと同義です。注意してください。  
  
  
  
  
  
  
## Render へのデプロイ
1. このリポジトリをフォークする。
2. Renderにログインし、 New + > Web Service > リポジトリを選択
   - Build Command: `npm install`
   - Start Command: `node server.js`
3. デプロイを押してしばらく待ち、https://(サーバー名).onrender.comが出たら成功!

[![Deploy to Render](https://render.com/images/deploy-to-render-button.svg)](https://render.com/deploy)

##Cloudflare版もどうぞ
https://github.com/20250199-tomohiro/project-claude-proxy-v2-cloudflare-port  
で、Cloudflare版が上がってます。
