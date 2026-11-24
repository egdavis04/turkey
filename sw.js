'use strict';
const BUILD = '4e19dabd';

// Own names only. The deer soundboard keeps its saved things at this same site (audio-v1 and
// shell-<build>), and a site's saved things are pooled. This worker clears nothing but its own.
const SHELL = 'turkey-shell-' + BUILD;
const AUDIO = 'turkey-audio-v1';
const IMPORTS = 'turkey-import-v1';
const FILES = ['./', 'style.css', 'app.js', 'manifest.json', 'app.webmanifest',
  'icons/icon-180.png', 'icons/icon-192.png', 'icons/icon-512.png'];

self.addEventListener('install', e => e.waitUntil((async () => {
  const cache = await caches.open(SHELL);
  await cache.addAll(FILES.map(url => new Request(url, { cache: 'reload' })));
  await self.skipWaiting();
})()));

self.addEventListener('activate', e => e.waitUntil((async () => {
  for (const name of await caches.keys()) {
    if (name.startsWith('turkey-shell-') && name !== SHELL) await caches.delete(name);
  }
  await self.clients.claim();
})()));

self.addEventListener('fetch', e => {
  const url = new URL(e.request.url);
  if (e.request.method === 'GET' && url.origin === location.origin) e.respondWith(answer(e.request, url));
});

async function answer(req, url) {
  // A sound that was put on the phone through the import button. It was never on the web.
  if (url.pathname.includes('/imported/')) {
    const hit = await (await caches.open(IMPORTS)).match(url.href);
    if (!hit) return new Response('This sound is not on this phone yet.', { status: 404 });
    return req.headers.has('range') ? slice(hit, req.headers.get('range')) : hit;
  }
  if (/\.(m4a|mp3)$/.test(url.pathname)) {
    const hit = await (await caches.open(AUDIO)).match(url.href);
    if (!hit) return fetch(req);
    return req.headers.has('range') ? slice(hit, req.headers.get('range')) : hit;
  }
  const cache = await caches.open(SHELL);
  const hit = await cache.match(req.mode === 'navigate' ? './' : req, { ignoreSearch: true });
  return hit || fetch(req);
}

// Safari asks for audio in byte ranges and plays nothing if it is handed the whole file back.
async function slice(resp, header) {
  const blob = await resp.blob(), size = blob.size;
  const m = /^bytes=(\d*)-(\d*)$/.exec(header.trim());
  let start = 0, end = size - 1;
  if (m && m[1]) {
    start = +m[1];
    if (m[2]) end = Math.min(+m[2], end);
  } else if (m && m[2]) {
    start = Math.max(0, size - m[2]);
  }
  if (!m || start > end) {
    return new Response(null, { status: 416, headers: { 'Content-Range': 'bytes */' + size } });
  }
  return new Response(blob.slice(start, end + 1), {
    status: 206,
    statusText: 'Partial Content',
    headers: {
      'Content-Type': resp.headers.get('Content-Type') || 'audio/mp4',
      'Content-Length': String(end - start + 1),
      'Content-Range': `bytes ${start}-${end}/${size}`,
      'Accept-Ranges': 'bytes',
    },
  });
}
