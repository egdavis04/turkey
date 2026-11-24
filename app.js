'use strict';
const BUILD = '4e19dabd';

const $ = id => document.getElementById(id);
const audio = $('player');
const seq = $('seq');
const bed = $('bed');
const now = () => Date.now();

// Everything this page saves on the phone goes under a name of its own. The deer soundboard
// lives at the same site, and a site's saved things are pooled, not kept by folder. Its names
// are audio-v1, shell-<build>, sb-settings and sb-session, and nothing here touches them.
const AUDIO_CACHE = 'turkey-audio-v1';
const IMPORT_CACHE = 'turkey-import-v1';
const SHELL_CACHE = 'turkey-shell-' + BUILD;
const KEY = { settings: 'tk-settings', session: 'tk-session', last: 'tk-lastcall', reloaded: 'tk-reloaded' };

const AC = window.AudioContext || window.webkitAudioContext;
const GAP_FLOOR = 1;         // seconds: the shortest silence an answer loop leaves, however short the call
const REC_FLOOR = 1.5;       // the same, when the silence is being recorded
const ART = [{ src: new URL('icons/icon-512.png', location.href).href, sizes: '512x512', type: 'image/png' }];
const HOLDS = [[0, 'Tap'], [1000, '1 s'], [2000, '2 s'], [3000, '3 s']];
const CHOICES = {
  hold: HOLDS,
  holdCall: HOLDS,
  startOn: [['fill', 'When the bar fills'], ['release', 'When I let go']],
  red: [[false, 'Normal'], [true, 'Dim red']],
  src: [['memory', 'From memory'], ['direct', 'Direct']],
  gap: [[1, 'As long as the call'], [1.5, '1½ times'], [2, 'Twice']],
  bed: [['auto', 'Automatic'], ['on', 'Always'], ['off', 'Never']],
  via: [['player', 'Second player'], ['ctx', 'Call player']],
  lgEndMode: [['sun', 'After sunset'], ['clock', 'At a set time']],
};

const store = {
  get(key) { try { return JSON.parse(localStorage.getItem(key)); } catch (e) { return null; } },
  set(key, v) { try { v == null ? localStorage.removeItem(key) : localStorage.setItem(key, JSON.stringify(v)); } catch (e) {} },
};

// The first time, the place for legal light is borrowed from the deer soundboard if it has one.
// It is only read. From then on this page keeps its own copy.
function borrowed() {
  const d = store.get('sb-settings');
  return d && d.geo ? { geo: d.geo, lgBefore: d.lgBefore, lgAfter: d.lgAfter } : null;
}
const cfg = Object.assign({ hold: 3000, holdCall: 1000, startOn: 'fill', red: false, src: 'memory',
  geo: null, lgBefore: 30, lgAfter: 30, lgEnd: null, tab: 'spring', mode: 'hunt', gap: 1, record: false, bed: 'auto', via: 'player' },
  borrowed(), store.get(KEY.settings));
const saveCfg = () => store.set(KEY.settings, cfg);
// A setting that is worked out from another one rather than kept under its own name.
const VIRTUAL = {
  lgEndMode: { get: () => cfg.lgEnd == null ? 'sun' : 'clock', set: v => { cfg.lgEnd = v === 'sun' ? null : cfg.lgEnd == null ? 13 * 60 : cfg.lgEnd; } },
};
const getSetting = key => VIRTUAL[key] ? VIRTUAL[key].get() : cfg[key];
const setSetting = (key, v) => { VIRTUAL[key] ? VIRTUAL[key].set(v) : cfg[key] = v; };

const subs = new Map();       // button -> what its small line says when nothing else claims it
const holdResets = [];
const notes = [];
let M = null, longs = [], calls = [], files = [], cache = null, icache = null;
let armed = false, priming = false, shellSaved = false, updateWaiting = false, storageNote = '';
let pending = null, pendingTimer = 0, lastRun = null, lastSave = 0, provisioning = false, retries = 0;
let importing = false, importNote = '', forgetArmed = 0, pressedAt = 0, touchedAt = now();

// The long sound in play: a background, or one of the real recordings. While it is heard, the
// <audio> element is the clock. While it is muted the element is paused, and its place is
// worked out from when it went quiet (pos, wall).
const S = { mode: 'idle', sound: null, len: 0, pos: 0, wall: 0, since: 0, mutedBy: '', seq: 0, target: null, tries: 0,
  heardAt: 0, resuming: false, url: '', msg: '', msgUntil: 0 };

// The calls. Each take is decoded ahead of time and played through Web Audio, so a call starts
// the moment it is asked for and plays over the background without touching it.
const V = { ctx: null, voice: null, decoding: false, lastEnd: store.get(KEY.last) || 0, lag: [], bedSet: false, bedTry: 0, lock: null, locking: false };

// A long call: a sequence of about two minutes. In Hunt it plays on a player of its own, the same
// kind the background uses, so it runs over the background and keeps going with the phone locked.
// loading is a long call that is still being read for the call player (the other way to play one).
const Q = { call: null, url: '', gen: 0, since: 0, priming: false, loading: null };
const seqKept = [];           // the long calls read for the call player, the one used last at the end

// Practice: the answer loop, and the recording of an answer.
const P = { call: null, gen: 0, phase: '', until: 0, timer: 0, guard: 0, stream: null, src: null, node: null, sink: null, chunks: null };

const fmt = s => {
  s = Math.max(0, Math.floor(s));
  const h = Math.floor(s / 3600), m = Math.floor(s % 3600 / 60);
  return (h ? h + ':' + String(m).padStart(2, '0') : m) + ':' + String(s % 60).padStart(2, '0');
};
const holdWords = ms => ms ? 'hold ' + ms / 1000 + ' s' : 'tap';
const setText = (el, t) => { if (el.textContent !== t) el.textContent = t; };
const el = (tag, cls) => { const e = document.createElement(tag); if (cls) e.className = cls; return e; };
const closeSetup = () => { $('setup').hidden = true; };
const hunting = () => cfg.mode === 'hunt';
const holdMs = () => hunting() ? cfg.holdCall : 0;
const takesOf = () => calls.reduce((all, c) => all.concat(c.takes), []);
const seqsOf = () => calls.filter(c => c.seq).map(c => c.seq);
const callReady = c => c.seq ? c.seq.f.state === 'ready' && !c.seq.bad : c.takes.some(t => t.buf);
const anyCall = () => !!V.voice || !!P.call || !!Q.call || !!Q.loading;
const sounding = () => S.mode === 'playing' || anyCall();

function note(msg) {
  notes.push(new Date().toTimeString().slice(0, 8) + ' ' + msg);
  if (notes.length > 40) notes.shift();
  if (!$('setup').hidden) drawDiag();
}

function say(msg) {
  S.msg = msg;
  S.msgUntil = now() + 4000;
  render();
}

// A stretch of digital silence as a sound file: n samples, 8 bits, mono.
function wav(n, rate) {
  const b = new Uint8Array(44 + n).fill(128), v = new DataView(b.buffer);
  const put = (at, s) => { for (let i = 0; i < s.length; i++) b[at + i] = s.charCodeAt(i); };
  put(0, 'RIFF'); v.setUint32(4, 36 + n, true); put(8, 'WAVEfmt '); v.setUint32(16, 16, true);
  v.setUint16(20, 1, true); v.setUint16(22, 1, true); v.setUint32(24, rate, true); v.setUint32(28, rate, true);
  v.setUint16(32, 1, true); v.setUint16(34, 8, true); put(36, 'data'); v.setUint32(40, n, true);
  return b;
}
const SILENCE = (() => {
  const b = wav(2205, 44100);
  let s = '';
  for (let i = 0; i < b.length; i++) s += String.fromCharCode(b[i]);
  return 'data:audio/wav;base64,' + btoa(s);
})();

const mime = name => /\.mp3$/i.test(name) ? 'audio/mpeg' : /\.wav$/i.test(name) ? 'audio/wav' : 'audio/mp4';

// The phone's audio type. "playback" is what lets sound through with the phone set to silent.
function setSession(type) {
  try { if (navigator.audioSession && navigator.audioSession.type !== type) navigator.audioSession.type = type; } catch (e) {}
}

// ---------------------------------------------------------------- the files

// A sound file is either published with the page (fetched, then saved on the phone) or part of
// the import pack (never on the web; put on the phone by its owner through the import button).
function fileOf(ref, long) {
  return ref.path
    ? { name: ref.path.split('/').pop(), url: ref.path + '?v=' + ref.v, bytes: ref.bytes, where: 'published', long, state: 'wait', got: 0, saved: false, blob: null, blobUrl: '', odd: false }
    : { name: ref.name, url: 'imported/' + encodeURIComponent(ref.name), bytes: ref.bytes || 0, where: 'import', long, state: 'none', got: 0, saved: false, blob: null, blobUrl: '', odd: false };
}

async function loadManifest() {
  const r = await fetch('manifest.json', { cache: 'no-cache' });
  if (!r.ok) throw new Error('manifest.json ' + r.status);
  M = await r.json();
  longs = M.backgrounds.map(b => ({ id: b.id, label: b.label, tabs: b.tabs, kind: 'bg', hunt: true, len: b.seconds || 0, f: fileOf(b.file, true), credit: b.credit }))
    .concat(M.listen.map(l => ({ id: l.id, label: l.label, tabs: l.tabs || M.tabs, kind: 'listen', group: l.group, hunt: !!l.hunt,
      len: l.seconds || 0, f: fileOf(l.file, true), credit: l.credit, check: l.check })));
  // A call is either one whole event with a few takes (an owl hoot, a cackle) or a sequence: one
  // long file of the call given over and over, with the times of its phrases.
  calls = M.calls.map(c => ({ id: c.id, label: c.label, tabs: c.tabs, group: c.group, hunt: c.hunt !== false, last: -1,
    takes: (c.takes || []).map(t => ({ f: fileOf(t, false), seconds: t.seconds, buf: null, bad: false })),
    seq: c.seq ? { f: fileOf(c.seq.file, true), seconds: c.seq.seconds || 0, phrases: c.seq.phrases || [], buf: null, bad: false, job: null } : null }));
  files = longs.map(b => b.f).concat(takesOf().map(t => t.f), seqsOf().map(q => q.f));
}

function fileReady(f, blob) {
  f.blob = blob.type === mime(f.name) ? blob : blob.slice(0, blob.size, mime(f.name));
  if (f.long) {
    if (f.blobUrl) URL.revokeObjectURL(f.blobUrl);
    f.blobUrl = URL.createObjectURL(f.blob);
  }
  f.odd = !!f.bytes && f.blob.size !== f.bytes;
  f.state = 'ready';
  decodeSoon();
}

async function provisionAll() {
  if (provisioning) return;
  provisioning = true;
  if (!cache && window.caches) {
    try { cache = await caches.open(AUDIO_CACHE); } catch (e) { note('cannot open the saved-files store: ' + e.message); }
  }
  const mine = files.filter(f => f.where === 'published');
  for (const f of mine) if (f.state !== 'ready') await provision(f);
  provisioning = false;
  drawSaved();
  if (mine.some(f => f.state === 'error')) {
    if (retries++ < 6) setTimeout(provisionAll, 15000);
  } else {
    retries = 0;
    if (cache && mine.every(f => f.saved)) prune(mine);
  }
}

// Each file is fetched whole and played from memory: Safari will not play audio that a service
// worker hands back complete, and a sound that is all in memory needs no signal.
async function provision(f) {
  f.state = 'loading';
  f.got = 0;
  drawButtons(); drawSaved();
  try {
    const hit = cache && await cache.match(f.url);
    let blob = hit ? await hit.blob() : null;
    if (blob && blob.size === f.bytes) {
      f.saved = true;
    } else {
      const r = await fetch(f.url, { cache: 'no-store' });
      if (!r.ok) throw new Error('HTTP ' + r.status);
      blob = await pull(r, f);
      if (blob.size !== f.bytes) throw new Error('download cut short');
      if (cache) {
        try {
          await cache.put(f.url, new Response(blob, { headers: { 'Content-Type': mime(f.name), 'Content-Length': String(blob.size) } }));
          f.saved = true;
        } catch (e) { note('could not save ' + f.name + ': ' + e.message); }
      }
    }
    fileReady(f, blob);
  } catch (e) {
    f.state = 'error';
    note('could not get ' + f.name + ': ' + (e.message || e));
  }
  drawButtons(); drawSaved();
}

async function pull(r, f) {
  if (!r.body || !r.body.getReader) return r.blob();
  const reader = r.body.getReader(), parts = [];
  let drawn = 0;
  for (;;) {
    const { done, value } = await reader.read();
    if (done) break;
    parts.push(value);
    f.got += value.length;
    if (now() - drawn > 200) { drawn = now(); drawButtons(); }
  }
  return new Blob(parts);
}

// Only this page's own store of published sounds is ever cleaned. The imported sounds are in a
// store of their own and are never cleared by anything but the Remove button.
async function prune(mine) {
  const keep = new Set(mine.map(f => new URL(f.url, location.href).href));
  for (const req of await cache.keys()) if (!keep.has(req.url)) cache.delete(req);
}

async function redownload() {
  if (sounding() || S.mode !== 'idle' || provisioning) return;
  for (const f of files.filter(f => f.where === 'published')) {
    if (f.blobUrl) URL.revokeObjectURL(f.blobUrl);
    Object.assign(f, { state: 'wait', got: 0, saved: false, blob: null, blobUrl: '' });
  }
  cache = null;
  try { if (window.caches) await caches.delete(AUDIO_CACHE); } catch (e) {}
  provisionAll();
}

async function askStorage() {
  const st = navigator.storage;
  if (!st || !st.persist) return;
  try {
    storageNote = (await st.persisted()) || (await st.persist())
      ? 'The phone will keep them.'
      : 'The phone can clear them after about a week without a visit. Open this page now and then, and keep the import pack on your drive.';
  } catch (e) {}
  drawSaved();
}

function worker() {
  const sw = navigator.serviceWorker;
  if (!sw) return;
  const had = !!sw.controller;
  const checkShell = async () => {
    try { shellSaved = await caches.has(SHELL_CACHE); } catch (e) { shellSaved = false; }
    drawSaved();
  };
  sw.register('sw.js', { updateViaCache: 'none' }).catch(e => note('offline worker: ' + e.message));
  sw.ready.then(checkShell);
  sw.addEventListener('controllerchange', () => {
    checkShell();
    if (!had) return;
    let last = 0;
    try { last = +sessionStorage.getItem(KEY.reloaded) || 0; } catch (e) {}
    if (S.mode === 'idle' && !sounding() && $('setup').hidden && now() - last > 30000) {
      try { sessionStorage.setItem(KEY.reloaded, String(now())); } catch (e) {}
      location.reload();
    } else {
      updateWaiting = true;
      drawSaved();
    }
  });
}

// ---------------------------------------------------------------- the import pack

// The sounds that are not on the web page. They are read from the phone's own store when the
// page opens, and put there by the import button.
async function loadImports() {
  if (!window.caches) return;
  try { icache = await caches.open(IMPORT_CACHE); } catch (e) { return note('cannot open the import store: ' + e.message); }
  for (const f of files) {
    if (f.where !== 'import' || f.state === 'ready') continue;
    try {
      const hit = await icache.match(f.url);
      if (hit) { f.saved = true; fileReady(f, await hit.blob()); }
    } catch (e) { note('could not read ' + f.name + ': ' + e.message); }
  }
  drawButtons(); drawSaved();
}

// A zip is read by its table of contents at the end of the file. Stored entries are sliced
// straight out; compressed ones go through the browser's own inflater.
async function unzip(file) {
  const size = file.size, tailLen = Math.min(size, 65557);
  const tail = new DataView(await file.slice(size - tailLen).arrayBuffer());
  let at = -1;
  for (let i = tailLen - 22; i >= 0; i--) if (tail.getUint32(i, true) === 0x06054b50) { at = i; break; }
  if (at < 0) throw new Error('that zip could not be read');
  const count = tail.getUint16(at + 10, true), dirSize = tail.getUint32(at + 12, true), dirAt = tail.getUint32(at + 16, true);
  const dir = new DataView(await file.slice(dirAt, dirAt + dirSize).arrayBuffer());
  const out = [], dec = new TextDecoder();
  let p = 0;
  for (let i = 0; i < count && p + 46 <= dir.byteLength; i++) {
    if (dir.getUint32(p, true) !== 0x02014b50) break;
    const method = dir.getUint16(p + 10, true), packed = dir.getUint32(p + 20, true);
    const nameLen = dir.getUint16(p + 28, true), extraLen = dir.getUint16(p + 30, true), noteLen = dir.getUint16(p + 32, true);
    const headAt = dir.getUint32(p + 42, true);
    const name = dec.decode(new Uint8Array(dir.buffer, dir.byteOffset + p + 46, nameLen));
    p += 46 + nameLen + extraLen + noteLen;
    if (name.endsWith('/') || name.startsWith('__MACOSX/') || name.split('/').pop().startsWith('.')) continue;
    const head = new DataView(await file.slice(headAt, headAt + 30).arrayBuffer());
    const start = headAt + 30 + head.getUint16(26, true) + head.getUint16(28, true);
    let blob = file.slice(start, start + packed);
    if (method === 8) {
      if (typeof DecompressionStream !== 'function') throw new Error('this phone cannot open a compressed zip; pick the files themselves');
      blob = await new Response(blob.stream().pipeThrough(new DecompressionStream('deflate-raw'))).blob();
    } else if (method !== 0) {
      throw new Error('that zip is packed in a way this page cannot read; pick the files themselves');
    }
    out.push({ name, blob });
  }
  return out;
}

async function importFiles(list) {
  const picked = Array.from(list || []);
  if (!picked.length || importing) return;
  importing = true;
  importNote = 'Reading ' + picked.length + (picked.length === 1 ? ' file…' : ' files…');
  drawSetup();
  const wanted = new Map(files.filter(f => f.where === 'import').map(f => [f.name, f]));
  if (sounding()) stopAll();                             // a file may be replaced under a player
  const takeFor = new Map(takesOf().map(t => [t.f, t]).concat(seqsOf().map(q => [q.f, q])));
  let items = [], added = 0, again = 0, odd = 0, bad = '', packList = null;
  const strange = [];
  try {
    for (const f of picked) {
      if (/\.zip$/i.test(f.name)) items = items.concat(await unzip(f));
      else items.push({ name: f.name, blob: f });
    }
    if (!icache && window.caches) icache = await caches.open(IMPORT_CACHE);
    for (const it of items) {
      const name = it.name.split('/').pop();
      if (/^pack\.json$/i.test(name)) {
        try { packList = JSON.parse(await it.blob.text()); } catch (e) { note('pack.json could not be read'); }
        continue;
      }
      const f = wanted.get(name);
      if (!f) { strange.push(name); continue; }
      if (f.state === 'ready') again++;
      if (icache) {
        await icache.put(f.url, new Response(it.blob, { headers: { 'Content-Type': mime(name), 'Content-Length': String(it.blob.size) } }));
        f.saved = true;
      }
      const take = takeFor.get(f);
      if (take) { take.buf = null; take.bad = false; }      // a fresh copy is decoded afresh
      fileReady(f, it.blob);
      if (f.odd) odd++;
      added++;
      importNote = 'Added ' + added + '…';
      drawSetup();
    }
  } catch (e) {
    bad = (e && e.message) || String(e);
    note('import: ' + bad);
  }
  decodeSoon();
  const missing = [...wanted.values()].filter(f => f.state !== 'ready');
  const parts = [];
  parts.push(added ? `Added ${added} ${added === 1 ? 'sound' : 'sounds'}${again ? ` (${again} replaced)` : ''}.` : 'Nothing was added.');
  if (bad) parts.push('Stopped early: ' + bad + '.');
  parts.push(missing.length ? `Still missing ${missing.length}: ${missing.slice(0, 4).map(f => f.name).join(', ')}${missing.length > 4 ? ', …' : ''}.` : 'Every sound is on this phone.');
  if (strange.length) parts.push(`Left out, not on the list: ${strange.slice(0, 3).join(', ')}${strange.length > 3 ? ' and ' + (strange.length - 3) + ' more' : ''}.`);
  if (odd) parts.push(`Not the size this version of the page expects: ${odd}. If the pack was rebuilt, reload the page and add the sounds again.`);
  if (packList && M.built && packList.built && packList.built > M.built) parts.push('The pack is newer than the page. Reload the page with signal.');
  if (!window.caches) parts.push('This address cannot save them: they last until the page is closed.');
  importNote = parts.join(' ');
  importing = false;
  note('import: ' + added + ' added, ' + missing.length + ' missing, ' + strange.length + ' left out');
  askStorage();
  drawSetup(); drawSaved(); render();
}

async function forgetImports() {
  if (sounding() || S.mode !== 'idle' || importing) return;
  if (now() - forgetArmed > 4000) {                  // the second tap does it
    forgetArmed = now();
    setTimeout(drawSetup, 4100);
    return drawSetup();
  }
  forgetArmed = 0;
  try { if (window.caches) await caches.delete(IMPORT_CACHE); } catch (e) {}
  icache = null;
  for (const f of files.filter(f => f.where === 'import')) {
    if (f.blobUrl) URL.revokeObjectURL(f.blobUrl);
    Object.assign(f, { state: 'none', saved: false, blob: null, blobUrl: '', odd: false });
  }
  for (const t of takesOf().concat(seqsOf())) if (t.f.where === 'import') { t.buf = null; t.bad = false; }
  seqKept.length = 0;
  importNote = 'The added sounds were removed from this phone.';
  note('imports removed');
  drawSetup(); drawSaved(); render();
}

// ---------------------------------------------------------------- the calls

function ctx() {
  if (!V.ctx && AC) {
    try { V.ctx = new AC({ latencyHint: 'interactive' }); } catch (e) {
      try { V.ctx = new AC(); } catch (e2) { note('no call player: ' + e2.message); }
    }
    if (V.ctx) V.ctx.addEventListener('statechange', () => note('call player ' + V.ctx.state));
  }
  return V.ctx;
}

// Bring the call player up if the phone has put it to sleep. Inside a touch this always works.
function wake() {
  const k = ctx();
  if (k && k.state !== 'running' && k.state !== 'closed') {
    try { const p = k.resume(); if (p && p.catch) p.catch(() => {}); } catch (e) {}
  }
  return k;
}

// Every take is decoded as soon as its file is on hand, one at a time, so a press never waits.
async function decodeSoon() {
  if (V.decoding) return;
  const k = ctx();
  if (!k) return;
  V.decoding = true;
  for (;;) {
    const t = takesOf().find(t => t.f.state === 'ready' && t.f.blob && !t.buf && !t.bad);
    if (!t) break;
    try {
      const data = await t.f.blob.arrayBuffer();
      t.buf = await new Promise((ok, no) => { const p = k.decodeAudioData(data, ok, no); if (p && p.catch) p.catch(no); });
    } catch (e) {
      t.bad = true;
      note('could not read ' + t.f.name + ': ' + ((e && e.message) || e || 'not a sound this phone knows'));
    }
    drawButtons();
  }
  V.decoding = false;
  drawButtons(); drawSaved();
}

// One sound through the call player, starting at a time on its clock. Nothing is leveled: the
// files carry their own soft and loud. With off and dur it is a piece out of a long sound, and
// gets soft edges so it does not begin or end on a click.
function tone(buf, when, gain, off, dur) {
  const k = V.ctx, src = k.createBufferSource(), g = k.createGain(), level = gain == null ? 1 : gain;
  const len = dur == null ? buf.duration : dur;
  src.buffer = buf;
  src.connect(g);
  g.connect(k.destination);
  const p = { src, g, at: when, end: when + len, done: false, then: null };
  src.onended = () => { p.done = true; if (p.then) p.then(); };
  if (dur == null) {
    g.gain.value = level;
    src.start(when);
  } else {
    g.gain.setValueAtTime(0, when);
    g.gain.linearRampToValueAtTime(level, when + 0.012);
    g.gain.setValueAtTime(level, when + Math.max(0.02, len - 0.04));
    g.gain.linearRampToValueAtTime(0, when + len);
    src.start(when, off, len);
  }
  return p;
}

// What pick() hands back: a whole take, or one phrase of a long call.
const sound = (take, when, gain) => take.whole ? tone(take.buf, when, gain) : tone(take.buf, when, gain, take.off, take.dur);

// End one, with a 15 ms fade so a cut-off call does not click.
function hush(p) {
  if (!p || p.done) return;
  p.then = null;
  p.done = true;
  const k = V.ctx, t = k.currentTime;
  try {
    if (p.at > t) {
      p.src.stop();
    } else {
      try { p.g.gain.cancelScheduledValues(t); } catch (e) {}
      p.g.gain.setValueAtTime(p.g.gain.value, t);
      p.g.gain.linearRampToValueAtTime(0, t + 0.015);
      p.src.stop(t + 0.02);
    }
  } catch (e) {}
}

function markCall() {
  V.lastEnd = now();
  store.set(KEY.last, V.lastEnd);
}

// A different take each press, never the same one twice running. A long call hands out its
// phrases in the order the hen gave them, and carries on from where it left off.
function pick(c) {
  if (c.seq) {
    const q = c.seq;
    if (!q.buf || !q.phrases.length) return null;
    c.last = (c.last + 1) % q.phrases.length;
    const off = Math.max(0, Math.min(q.phrases[c.last][0], q.buf.duration - 0.2));
    return { buf: q.buf, off, dur: Math.max(0.1, Math.min(q.phrases[c.last][1], q.buf.duration) - off), whole: false };
  }
  const ready = c.takes.map((t, i) => t.buf ? i : -1).filter(i => i >= 0);
  if (!ready.length) return null;
  const pool = ready.length > 1 ? ready.filter(i => i !== c.last) : ready;
  c.last = pool[Math.floor(Math.random() * pool.length)];
  const buf = c.takes[c.last].buf;
  return { buf, off: 0, dur: buf.duration, whole: true };
}

function voice(c, parts) {
  const k = V.ctx, last = parts[parts.length - 1];
  V.voice = { call: c, parts, wallEnd: now() + Math.max(0, last.end - k.currentTime) * 1000 + 600, asleep: k.state !== 'running' };
  return V.voice;
}

// The call that is sounding, on either player, and how much of it is left.
function calling() {
  if (Q.call) return { call: Q.call, left: Math.max(0, (isFinite(seq.duration) && seq.duration ? seq.duration : Q.call.seq.seconds) - seq.currentTime) };
  const v = V.voice;
  if (!v || P.call) return null;
  return { call: v.call, left: Math.max(0, v.parts[v.parts.length - 1].end - V.ctx.currentTime) };
}

// Ends whatever call is sounding, and any answer loop. The background is left alone.
function quiet() {
  stopPractice();
  Q.gen++;                              // also drops a long call that is still being read
  Q.loading = null;
  if (Q.call) {
    const heard = seq.currentTime > 0.05;
    Q.call = null;
    try { seq.pause(); } catch (e) {}
    if (heard) markCall();
    media();
  }
  const v = V.voice;
  if (!v) return;
  V.voice = null;
  const t = V.ctx.currentTime;
  let heard = false;
  for (const p of v.parts) {
    if (!p.done && p.at <= t) heard = true;
    hush(p);
  }
  if (heard) markCall();
}

// Hunt: the call plays once, over the background. A call pressed over another replaces it.
function playCall(c) {
  if (c.seq) return playSeq(c);
  const k = wake();
  if (!k) return say('This browser cannot play the calls');
  const take = pick(c);
  if (!take) return;
  quiet();
  const p = sound(take, k.currentTime);
  const v = voice(c, [p]);
  p.then = () => {
    if (V.voice !== v) return;
    V.voice = null;
    markCall();
    render();
  };
  V.lag.push(Math.round(performance.now() - pressedAt));
  if (V.lag.length > 10) V.lag.shift();
  note('call ' + c.id + ' take ' + (c.last + 1));
  render();
}

// ---------------------------------------------------------------- the long calls

// Hunt: a long call plays through once, from its start, over the background. The same button
// again ends it; so do Mute, Stop and any other call.
function playSeq(c) {
  const on = Q.call === c || Q.loading === c || !!(V.voice && V.voice.call === c);
  quiet();
  if (on) return render();
  if (cfg.via === 'ctx') return playSeqCtx(c);
  const f = c.seq.f, url = cfg.src === 'direct' ? f.url : f.blobUrl, my = Q.gen;
  Q.call = c;
  Q.since = now();
  if (Q.url !== url) {
    Q.url = url;
    seq.src = url;
  } else if (seq.readyState > 0 && seq.currentTime > 0.05) {
    try { seq.currentTime = 0; } catch (e) {}
  }
  seq.muted = false;
  let p;
  try { p = seq.play(); } catch (e) { p = Promise.reject(e); }
  Promise.resolve(p).catch(e => seqFailed(my, e));
  V.lag.push(Math.round(performance.now() - pressedAt));
  if (V.lag.length > 10) V.lag.shift();
  note('long call ' + c.id);
  media(); render();
}

// The other way to play one, for a phone where the two players will not run together: read the
// whole call and send it through the call player. That player can stop when the phone locks, so
// the screen is kept on while it runs.
function playSeqCtx(c) {
  const k = wake(), my = Q.gen;
  if (!k) return say('This browser cannot play the calls');
  Q.loading = c;
  render();
  seqDecode(c).then(buf => {
    if (my !== Q.gen || Q.loading !== c) return;
    Q.loading = null;
    const p = tone(buf, V.ctx.currentTime);
    const v = voice(c, [p]);
    p.then = () => {
      if (V.voice !== v) return;
      V.voice = null;
      markCall();
      render();
    };
    note('long call ' + c.id + ' on the call player');
    render();
  }, () => {
    if (my !== Q.gen) return;
    Q.loading = null;
    say('Could not read that sound');
  });
}

function seqDone(why) {
  const c = Q.call;
  if (!c) return;
  Q.call = null;
  Q.gen++;
  if (why !== 'ended') { try { seq.pause(); } catch (e) {} }
  markCall();
  note('long call ' + c.id + ' ' + why);
  media(); render();
}

function seqFailed(my, e) {
  const name = (e && e.name) || 'Error';
  if (my !== Q.gen || !Q.call || name === 'AbortError') return;
  note('the phone refused to play the call: ' + name);
  Q.call = null;
  Q.gen++;
  try { seq.pause(); } catch (err) {}
  media();
  if (name === 'NotAllowedError') blocked(); else say('Could not play that sound');
  render();
}

// A long call is too much to keep read for every button at once. The call player reads one when
// it is first wanted (the press starts the reading, so it is mostly done before the thumb is up)
// and keeps the two used last.
function seqDecode(c) {
  const q = c.seq, k = ctx();
  const keep = () => {
    const i = seqKept.indexOf(c);
    if (i >= 0) seqKept.splice(i, 1);
    seqKept.push(c);
    while (seqKept.length > 2) {
      const old = seqKept.find(x => x !== c && x !== P.call && !(V.voice && V.voice.call === x));
      if (!old) break;
      seqKept.splice(seqKept.indexOf(old), 1);
      old.seq.buf = null;
    }
  };
  if (q.buf) { keep(); return Promise.resolve(q.buf); }
  if (!k || !q.f.blob) return Promise.reject(new Error('not ready'));
  if (!q.job) {
    q.job = q.f.blob.arrayBuffer()
      .then(data => new Promise((ok, no) => { const p = k.decodeAudioData(data, ok, no); if (p && p.catch) p.catch(no); }))
      .then(buf => { q.job = null; q.buf = buf; keep(); drawButtons(); return buf; },
        e => {
          q.job = null;
          q.bad = true;
          note('could not read ' + q.f.name + ': ' + ((e && e.message) || e || 'not a sound this phone knows'));
          drawButtons();
          throw e;
        });
  }
  return q.job;
}

// ---------------------------------------------------------------- practice

// Tap a call and its answer loop starts: the call, a silence to answer in, the call again.
// Tap it again and it stops. A long call is practised a phrase at a time.
function practice(c) {
  if (P.call === c) { quiet(); return render(); }
  const k = wake();
  if (!k) return say('This browser cannot play the calls');
  quiet();
  P.call = c;
  P.gen++;
  if (cfg.record && S.mode === 'playing') mute('recording');     // a recording should hear only the answer
  const gen = P.gen, go = () => { if (gen === P.gen) round(gen, V.ctx.currentTime + 0.02); };
  if (c.seq && !c.seq.buf) {
    P.phase = 'load';
    seqDecode(c).then(go, () => {
      if (gen !== P.gen) return;
      quiet();
      say('Could not read that sound');
    });
  } else {
    go();
  }
  note('answer loop ' + c.id + (cfg.record ? ', recording' : ''));
  render();
}

function stopPractice() {
  if (!P.call) return;
  P.call = null;
  P.gen++;
  P.phase = '';
  clearTimeout(P.timer);
  clearTimeout(P.guard);
  if (P.stream) closeMic();
}

// An answer loop moves on when the call player says a sound has ended. If the phone stops the
// player part-way (a phone call, the microphone changing how sound is routed), that word never
// comes. So each sound is given until two seconds past its end, and then the loop is ended and
// says so, rather than sitting there looking as if it were running.
function guard(gen, v) {
  const k = V.ctx, last = v.parts[v.parts.length - 1];
  clearTimeout(P.guard);
  P.guard = setTimeout(() => {
    if (gen !== P.gen || V.voice !== v || last.done) return;
    note('answer loop: the call player stalled (' + k.state + ')');
    quiet();
    say('The phone cut the sound off. Tap the call again.');
  }, Math.max(0, last.end - k.currentTime) * 1000 + 2000);
}

function round(gen, when) {
  const c = P.call, k = V.ctx;
  if (gen !== P.gen || !c) return;
  const take = pick(c);
  if (!take) return quiet();
  const p = sound(take, Math.max(when, k.currentTime));
  const v = voice(c, [p]);
  const gap = Math.max(take.dur * cfg.gap, cfg.record ? REC_FLOOR : GAP_FLOOR);
  P.phase = 'loop';
  guard(gen, v);
  p.then = () => {
    if (gen !== P.gen || V.voice !== v) return;
    markCall();
    if (cfg.record) return answer(gen, take, gap);
    // The next pass is lined up now, on the player's own clock, so the silence is exact and
    // does not hang on a timer.
    round(gen, p.end + gap);
    render();
  };
}

// The silence is recorded, then the real call and the answer are played back to back. The
// microphone is open only for the take itself.
async function answer(gen, take, gap) {
  P.phase = 'ready';
  render();
  try {
    await openMic();
  } catch (e) {
    closeMic();
    if (gen !== P.gen) return;
    cfg.record = false;
    saveCfg();
    note('microphone: ' + ((e && e.name) || e));
    say(micHelp(e));
    return round(gen, V.ctx.currentTime + gap);
  }
  if (gen !== P.gen) return closeMic();
  P.phase = 'rec';
  P.until = now() + gap * 1000;
  render();
  P.timer = setTimeout(() => {
    const mine = closeMic();
    if (gen !== P.gen) return;
    P.phase = 'back';
    render();
    // A moment for the phone to hand the speaker back at its full level.
    P.timer = setTimeout(() => {
      if (gen !== P.gen) return;
      const k = wake(), a = sound(take, k.currentTime + 0.05);
      const parts = [a];
      if (mine) parts.push(tone(mine, a.end + 0.35, matched(mine, take)));
      const v = voice(P.call, parts);
      guard(gen, v);
      parts[parts.length - 1].then = () => {
        if (gen !== P.gen || V.voice !== v) return;
        P.phase = 'rest';
        P.timer = setTimeout(() => round(gen, V.ctx.currentTime + 0.02), 900);
        render();
      };
    }, 400);
  }, gap * 1000);
}

// The answer is played at about the loudness of the call it answers, so the two can be compared
// however far the phone was from the caller's mouth. Only the answer is touched, never a call.
function matched(mine, take) {
  const peak = (b, from, to) => { const d = b.getChannelData(0); let m = 0; for (let i = from; i < to; i += 4) { const a = Math.abs(d[i]); if (a > m) m = a; } return m; };
  const rate = take.buf.sampleRate, from = Math.floor(take.off * rate);
  const a = peak(mine, 0, mine.length), r = peak(take.buf, from, Math.min(take.buf.length, from + Math.floor(take.dur * rate)));
  return a < 0.003 ? 1 : Math.max(0.25, Math.min(12, r / a));
}

function micHelp(e) {
  const name = (e && e.name) || '';
  return name === 'NotAllowedError' || name === 'SecurityError' ? 'The phone did not allow the microphone. Record is off.'
    : name === 'NotFoundError' ? 'No microphone found. Record is off.'
    : 'This browser cannot record. Record is off.';
}

// Recording needs the phone's audio type set to play-and-record, and only then. The phone's own
// voice clean-up is switched off: it mangles a turkey call and drops the speaker's volume.
async function openMic() {
  const md = navigator.mediaDevices, k = wake();
  if (!md || !md.getUserMedia || !k || !k.createScriptProcessor) throw new Error('unsupported');
  setSession('play-and-record');
  const stream = await md.getUserMedia({ audio: { echoCancellation: false, noiseSuppression: false, autoGainControl: false } });
  P.stream = stream;
  P.chunks = [];
  P.src = k.createMediaStreamSource(stream);
  P.node = k.createScriptProcessor(4096, 1, 1);
  P.sink = k.createGain();
  P.sink.gain.value = 0;
  P.node.onaudioprocess = e => { if (P.chunks) P.chunks.push(new Float32Array(e.inputBuffer.getChannelData(0))); };
  P.src.connect(P.node);
  P.node.connect(P.sink);
  P.sink.connect(k.destination);
}

// Lets go of the microphone and hands back what was heard. Nothing is kept anywhere else.
function closeMic() {
  let buf = null;
  try {
    if (P.node) { P.node.onaudioprocess = null; P.src.disconnect(); P.node.disconnect(); P.sink.disconnect(); }
    if (P.stream) for (const t of P.stream.getTracks()) t.stop();
    const n = P.chunks ? P.chunks.reduce((sum, c) => sum + c.length, 0) : 0;
    if (n) {
      buf = V.ctx.createBuffer(1, n, V.ctx.sampleRate);
      const d = buf.getChannelData(0);
      let at = 0;
      for (const c of P.chunks) { d.set(c, at); at += c.length; }
    }
  } catch (e) { note('microphone: ' + e.message); }
  P.stream = P.src = P.node = P.sink = P.chunks = null;
  setSession('playback');
  return buf;
}

// The switch asks for the microphone once, at the tap, so the phone's question comes then and
// not in the middle of a call.
async function toggleRecord() {
  if (hunting()) return;
  quiet();
  if (cfg.record) {
    cfg.record = false;
  } else {
    try {
      await openMic();
      closeMic();
      cfg.record = true;
    } catch (e) {
      closeMic();
      note('microphone: ' + ((e && e.name) || e));
      say(micHelp(e));
    }
  }
  saveCfg();
  render();
}

// ---------------------------------------------------------------- the clock

function where() {
  if (S.mode !== 'muted') return S.target != null ? S.target : audio.currentTime;
  return (S.pos + (now() - S.wall) / 1000) % (S.len || 1e9);
}

// ---------------------------------------------------------------- the background player

function setSrc(f) {
  const url = cfg.src === 'direct' ? f.url : f.blobUrl;
  if (S.url !== url) { S.url = url; audio.src = url; }
}

function dropSrc() {
  if (!S.url) return;
  S.url = '';
  audio.removeAttribute('src');
  audio.load();
}

// play() is called at once, so it lands inside the touch when there is one. A file that is already
// loaded is moved in place and played as is. A fresh file that has to begin somewhere other than
// 0:00 plays muted until the playhead gets there, so nothing from the wrong spot is heard.
function playAt(at) {
  const my = S.seq;
  at = Math.max(0, at);
  S.tries = 0;
  S.target = null;
  if (audio.readyState < 1) S.target = at || null;
  else if (Math.abs(audio.currentTime - at) > 0.05) audio.currentTime = at;
  audio.muted = S.target != null;
  let p;
  try { p = audio.play(); } catch (e) { return playFailed(my, e); }
  if (p && p.catch) p.catch(e => playFailed(my, e));
}

function land() {
  if (S.mode !== 'playing' || audio.readyState < 1) return;
  if (isFinite(audio.duration) && audio.duration > 0) S.len = S.sound.len = audio.duration;
  if (S.target == null || audio.seeking) return;
  const off = audio.currentTime - S.target;
  if ((off < -0.3 || off > 2.5) && S.tries < 3) {
    S.tries++;
    audio.currentTime = S.target;
    return;
  }
  S.target = null;
  S.heardAt = now();
  audio.muted = false;
}

// The phone would not let the page make sound: play() was turned down, or the player was paused
// the moment it was unmuted. A fresh start is dropped; an unmute goes back to muted.
function refused(name) {
  note('the phone refused to play: ' + name);
  if (S.resuming) {
    Object.assign(S, { mode: 'muted', target: null, resuming: false });
    audio.muted = true;
    audio.pause();
    media(); saveSession();
  } else {
    stopLong();
  }
  if (name === 'NotAllowedError') blocked(); else say('Could not play that sound');
  render();
}

function playFailed(my, e) {
  const name = (e && e.name) || 'Error';
  if (my === S.seq && name !== 'AbortError') refused(name);
}

function startLong(b) {
  if (b.f.state !== 'ready') return;
  dropPending();
  S.seq++;
  Object.assign(S, { mode: 'playing', sound: b, len: b.len, pos: 0, wall: now(), since: now(), mutedBy: '', resuming: false, msg: '' });
  audio.loop = true;
  setSrc(b.f);
  playAt(0);
  media(); saveSession(); render();
  note('start ' + b.id);
}

// The same press on a background that is on turns it off, and only it: a call playing over it
// keeps going (roost talk off at the fly-down cackle, the feeding hens off once the cutting
// starts). A hold in Hunt, a tap in Practice. Stop is the button that ends everything.
function pressLong(b) {
  if (S.sound === b && S.mode !== 'idle') return stopLong('background turned off');
  startLong(b);
}

// The background goes quiet and keeps its place in time: unmuted later, it is further along.
function mute(by) {
  if (S.mode !== 'playing') return;
  S.pos = S.target != null ? S.target : audio.currentTime;
  S.wall = now();
  Object.assign(S, { mode: 'muted', mutedBy: by, target: null, resuming: false });
  audio.muted = true;
  audio.pause();
  media(); saveSession(); render();
  note('muted' + (by === 'user' ? '' : ' by the ' + by) + ' at ' + fmt(S.pos));
}

// Mute covers both players: the background, and any call or answer loop.
function muteAll(by) {
  quiet();
  mute(by);
  render();
}

function unmute() {
  if (S.mode !== 'muted') return;
  if (S.sound.f.state !== 'ready') return say('That sound is not ready yet');
  const at = where();
  S.seq++;
  Object.assign(S, { mode: 'playing', pos: at, wall: now(), resuming: true });
  audio.loop = true;
  setSrc(S.sound.f);
  playAt(at);
  media(); saveSession(); render();
  note('unmuted at ' + fmt(at));
}

function stopLong(why) {
  const was = S.mode;
  S.seq++;
  Object.assign(S, { mode: 'idle', sound: null, target: null, mutedBy: '', resuming: false });
  audio.muted = true;
  audio.pause();
  audio.loop = false;
  dropSrc();
  media(); saveSession(); render();
  if (was !== 'idle') note(typeof why === 'string' ? why : 'background stopped');
}

function stopAll() {
  quiet();
  stopLong();
}

// iPhone only lets a page start sound from inside a touch, and a hold that finishes on a timer is
// not one. A plain tap on the players first lifts that rule for them for as long as the page is
// open. The same tap chooses Hunt or Practice, so the page never opens by surprise in the mode
// where a tap makes sound.
function arm(mode) {
  armed = true;
  cfg.mode = mode;
  saveCfg();
  $('arm').hidden = true;
  wake();
  primeBed();
  if (S.mode !== 'playing') {
    priming = true;
    audio.muted = true;
    audio.loop = false;
    S.url = SILENCE;
    audio.src = SILENCE;
    const done = e => {
      priming = false;
      if (e && e.name === 'NotAllowedError') {
        note('the arming tap was refused');
        cfg.startOn = 'release';
        saveCfg();
      }
      if (S.mode !== 'playing') {
        audio.pause();
        if (S.url === SILENCE) dropSrc();
      }
    };
    let p;
    try { p = audio.play(); } catch (e) { p = Promise.reject(e); }
    Promise.resolve(p).then(() => done(), done);
  }
  // The second player, the one the long calls use, is unlocked by the same tap.
  if (!Q.call) {
    Q.priming = true;
    seq.muted = true;
    Q.url = SILENCE;
    seq.src = SILENCE;
    const primed = e => {
      Q.priming = false;
      if (e && e.name === 'NotAllowedError') note('the arming tap was refused for the second player');
      if (!Q.call) { try { seq.pause(); } catch (err) {} seq.muted = false; }
    };
    let p2;
    try { p2 = seq.play(); } catch (e) { p2 = Promise.reject(e); }
    Promise.resolve(p2).then(() => primed(), primed);
  }
  askStorage();
  decodeSoon();
  layout();
  render();
  note('armed, ' + mode);
}

function tick() {
  if (S.mode !== 'playing') return;
  land();
  if (S.target == null) {
    S.pos = audio.currentTime;
    S.wall = now();
    if (S.resuming && S.wall - S.heardAt > 1000) S.resuming = false;
    if (S.wall - lastSave > 10000) saveSession();
  }
  render();
}

function listen() {
  for (const ev of ['loadedmetadata', 'seeked', 'canplay', 'playing']) audio.addEventListener(ev, land);
  audio.addEventListener('timeupdate', tick);
  audio.addEventListener('ended', () => { if (S.mode === 'playing') stopLong('played to the end'); });
  // A pause this page did not ask for: a phone call, the speaker dropping out, another app's sound.
  audio.addEventListener('pause', () => {
    if (S.mode !== 'playing' || !audio.paused || audio.ended) return;
    // iPhone pauses a player on the spot if it is unmuted without the right to make sound.
    if (now() - S.heardAt < 1000) return refused('NotAllowedError');
    mute('phone');
  });
  // The phone resumes on its own after an interruption. Sound only comes back when it is asked for.
  audio.addEventListener('play', () => {
    if (S.mode !== 'playing' && !priming) { audio.muted = true; audio.pause(); }
  });
  audio.addEventListener('error', () => {
    if (S.mode !== 'playing' || !audio.error) return;
    note('audio error ' + audio.error.code);
    stopLong();
    say('Could not play that sound');
  });

  // The second player. A long call that reaches its end, or that the phone stops, is over.
  seq.addEventListener('ended', () => seqDone('ended'));
  seq.addEventListener('pause', () => {
    if (!Q.call || !seq.paused || seq.ended) return;
    // paused the moment it began: the phone would not let it make sound
    if (now() - Q.since < 1000) return seqFailed(Q.gen, { name: 'NotAllowedError' });
    seqDone('stopped by the phone');
  });
  seq.addEventListener('play', () => { if (!Q.call && !Q.priming) { try { seq.pause(); } catch (e) {} } });
  seq.addEventListener('error', () => {
    if (!Q.call || !seq.error) return;
    note('second player error ' + seq.error.code);
    seqDone('could not be played');
    say('Could not play that sound');
  });

  const ms = navigator.mediaSession;
  if (!ms) return;
  const on = (name, fn) => { try { ms.setActionHandler(name, fn); } catch (e) {} };
  on('play', () => { lastRun = null; unmute(); });
  on('pause', () => muteAll('user'));
  on('stop', stopAll);
  // Without these the lock screen's skip and scrub controls would move the background on their own.
  for (const name of ['seekto', 'seekbackward', 'seekforward']) on(name, () => {});
}

function media() {
  const ms = navigator.mediaSession;
  if (!ms) return;
  try {
    const title = S.sound ? S.sound.label : Q.call ? Q.call.label : '';
    ms.metadata = title && window.MediaMetadata
      ? new MediaMetadata({ title, artist: 'Turkey soundboard', artwork: ART })
      : null;
    ms.playbackState = S.mode === 'playing' || Q.call ? 'playing' : S.mode === 'muted' ? 'paused' : 'none';
  } catch (e) {}
}

// A running background is written down so that a reload (the phone clearing the tab while another
// app is open) does not lose its place. It always comes back muted.
function saveSession() {
  lastSave = now();
  store.set(KEY.session, S.mode !== 'idle' && S.sound
    ? { id: S.sound.id, pos: S.pos, wall: S.wall, len: S.len, since: S.since } : null);
}

function restoreSession() {
  const s = store.get(KEY.session), sound = s && longs.find(x => x.id === s.id);
  const age = s ? now() - s.wall : -1;
  if (!sound || age < 0 || age > 6 * 3600e3) return store.set(KEY.session, null);
  Object.assign(S, { mode: 'muted', sound, len: s.len || sound.len, pos: s.pos, wall: s.wall, since: s.since || s.wall, mutedBy: 'reload' });
  if (!sound.tabs.includes(cfg.tab)) cfg.tab = sound.tabs[0];
  note('picked up ' + sound.id + ' after a reload, muted');
}

// ---------------------------------------------------------------- the phone's own behavior

// With the phone set to silent, an iPhone mutes the call player unless a media player is running
// beside it. The audio type set at the start should cover that. Where it is missing, or if it is
// not enough, a silent track is kept running while the page is on screen.
function bedWanted() {
  return armed && !document.hidden && S.mode !== 'playing' && !P.stream
    && (cfg.bed === 'on' || (cfg.bed === 'auto' && !navigator.audioSession));
}

function primeBed() {
  if (cfg.bed === 'off' || (cfg.bed === 'auto' && navigator.audioSession)) return;
  if (!V.bedSet) {
    V.bedSet = true;
    bed.src = URL.createObjectURL(new Blob([wav(8000 * 30, 8000)], { type: 'audio/wav' }));
  }
  try { const p = bed.play(); if (p && p.catch) p.catch(() => {}); } catch (e) {}
}

function tend() {
  // the silent track
  const want = bedWanted();
  if (want && bed.paused && now() - V.bedTry > 2000) { V.bedTry = now(); primeBed(); }
  if (!want && !bed.paused) bed.pause();

  // the screen stays awake in Practice while it is being used, and while a long call is running
  // on the call player, which a locked phone may stop
  const longOnCtx = !!(V.voice && V.voice.call.seq && !P.call) || !!Q.loading;
  const awake = armed && !document.hidden && (longOnCtx || (!hunting() && (P.call || now() - touchedAt < 10 * 60e3)));
  if (awake && !V.lock && !V.locking && navigator.wakeLock) {
    V.locking = true;
    navigator.wakeLock.request('screen').then(l => {
      V.lock = l;
      l.addEventListener('release', () => { if (V.lock === l) V.lock = null; });
    }, () => {}).then(() => { V.locking = false; });
  }
  if (!awake && V.lock) { const l = V.lock; V.lock = null; try { l.release().catch(() => {}); } catch (e) {} }

  // a call whose end the phone never reported
  const v = V.voice;
  if (v && now() > v.wallEnd && !P.call) {
    V.voice = null;
    if (V.ctx.state !== 'running') {
      // The phone has the call player asleep, so the call was cut short or never heard. It is
      // dropped, not left to go off later by itself.
      for (const p of v.parts) hush(p);
      note('call player ' + V.ctx.state + (v.asleep ? ' at the press' : ' during the call'));
      if (v.asleep) { S.msg = 'Touch the screen once, then call again'; S.msgUntil = now() + 4000; }
    } else {
      markCall();
    }
  }
}

// ---------------------------------------------------------------- holding a button

function holdable(btn, o) {
  let id = null, timer = 0, full = false;
  const inside = e => {
    const r = btn.getBoundingClientRect(), slop = 14;
    return e.clientX > r.left - slop && e.clientX < r.right + slop && e.clientY > r.top - slop && e.clientY < r.bottom + slop;
  };
  const reset = () => {
    clearTimeout(timer);
    id = null;
    full = false;
    btn.classList.remove('holding', 'full');
    drawButtons();
  };
  const fire = () => { lastRun = { run: o.run, btn }; pressedAt = performance.now(); o.run(); };
  holdResets.push(() => { if (id !== null) reset(); });

  btn.addEventListener('pointerdown', e => {
    if (id !== null || (e.pointerType === 'mouse' && e.button !== 0)) return;
    if (pending && pending.btn === btn) return;
    if (o.down && o.down()) return;
    if (!o.can()) return;
    id = e.pointerId;
    try { btn.setPointerCapture(id); } catch (err) {}
    const ms = o.ms();
    if (!ms) return;
    btn.style.setProperty('--hold', ms + 'ms');
    btn.classList.add('holding');
    timer = setTimeout(() => {
      full = true;
      btn.classList.add('full');
      if (cfg.startOn === 'release') drawButtons(); else fire();
    }, ms);
  });
  btn.addEventListener('pointerup', e => {
    if (e.pointerId !== id) return;
    const ms = o.ms(), wasFull = full, ok = inside(e);
    const waiting = pending && pending.btn === btn && pending.stage === 'release';
    reset();
    if (waiting) return ok ? runPending() : dropPending();
    if (!ok) return;
    if (!ms || (wasFull && cfg.startOn === 'release')) fire();
    else if (!wasFull && o.tap) o.tap();
  });
  const cancel = e => {
    if (e.pointerId !== id) return;
    reset();
    if (pending && pending.btn === btn) dropPending();
  };
  btn.addEventListener('pointercancel', cancel);
  btn.addEventListener('pointermove', e => { if (!inside(e)) cancel(e); });
  btn.addEventListener('click', () => { if (pending && pending.btn === btn && pending.stage === 'tap') runPending(); });
}

// The phone would not start the sound from the timer. From now on a hold starts when the thumb
// lifts, which is a touch; if even that is refused, one more tap on the same button does it.
function blocked() {
  if (cfg.startOn !== 'release') {
    cfg.startOn = 'release';
    saveCfg();
    drawSetup();
    note('switched to starting when you let go');
  }
  if (!lastRun) return;
  const btn = lastRun.btn;
  pending = { run: lastRun.run, btn, stage: btn.classList.contains('full') ? 'release' : 'tap' };
  btn.classList.add('armed');
  clearTimeout(pendingTimer);
  pendingTimer = setTimeout(dropPending, 10000);
  drawButtons();
}

function runPending() {
  const p = pending;
  dropPending();
  if (!p) return;
  lastRun = p;
  p.run();
}

function dropPending() {
  if (!pending) return;
  clearTimeout(pendingTimer);
  pending.btn.classList.remove('armed');
  pending = null;
  drawButtons();
}

function flash(btn, text) {
  btn.dataset.flash = text;
  btn.classList.add('flash');
  clearTimeout(btn.flashTimer);
  btn.flashTimer = setTimeout(() => {
    delete btn.dataset.flash;
    btn.classList.remove('flash');
    drawButtons();
  }, 1800);
  drawButtons();
}

// ---------------------------------------------------------------- legal light

// The two times are worked out on the phone from the date and a saved location, with the standard
// sunrise and sunset formulas (NOAA's, good to about a minute). Nothing is fetched, and the
// location is kept in this phone's settings and nowhere else.
const RAD = Math.PI / 180;
const clock = new Intl.DateTimeFormat(undefined, { hour: 'numeric', minute: '2-digit' });
const dayName = new Intl.DateTimeFormat(undefined, { month: 'short', day: 'numeric' });
const zone = () => { try { return Intl.DateTimeFormat().resolvedOptions().timeZone || ''; } catch (e) { return ''; } };
let locating = false, locateNote = '', locateRun = 0, locateWatch = 0;

// Where the sun is at a moment: its declination in radians and the equation of time in minutes.
function sunAt(ms) {
  const T = (ms / 864e5 + 2440587.5 - 2451545) / 36525;
  const L0 = (280.46646 + T * (36000.76983 + T * 0.0003032)) % 360 * RAD;
  const M0 = (357.52911 + T * (35999.05029 - 0.0001537 * T)) * RAD;
  const e = 0.016708634 - T * (0.000042037 + 0.0000001267 * T);
  const C = Math.sin(M0) * (1.914602 - T * (0.004817 + 0.000014 * T))
    + Math.sin(2 * M0) * (0.019993 - 0.000101 * T) + Math.sin(3 * M0) * 0.000289;
  const om = (125.04 - 1934.136 * T) * RAD;
  const lam = L0 + (C - 0.00569 - 0.00478 * Math.sin(om)) * RAD;
  const eps = (23 + (26 + (21.448 - T * (46.815 + T * (0.00059 - T * 0.001813))) / 60) / 60 + 0.00256 * Math.cos(om)) * RAD;
  const y = Math.tan(eps / 2) ** 2;
  const eot = 4 / RAD * (y * Math.sin(2 * L0) - 2 * e * Math.sin(M0) + 4 * e * y * Math.sin(M0) * Math.cos(2 * L0)
    - 0.5 * y * y * Math.sin(4 * L0) - 1.25 * e * e * Math.sin(2 * M0));
  return { decl: Math.asin(Math.sin(eps) * Math.sin(lam)), eot };
}

// Sunrise and sunset, in milliseconds, for a calendar day at a place. Null where the sun does neither.
function sunTimes(y, m, d, lat, lon) {
  const base = Date.UTC(y, m, d), out = [];
  for (const side of [-1, 1]) {
    let t = base + (720 - 4 * lon) * 6e4;
    for (let i = 0; i < 3; i++) {
      const s = sunAt(t);
      const c = Math.cos(90.833 * RAD) / (Math.cos(lat * RAD) * Math.cos(s.decl)) - Math.tan(lat * RAD) * Math.tan(s.decl);
      if (!(c >= -1 && c <= 1)) return null;
      t = base + (720 - 4 * lon - s.eot + side * 4 * Math.acos(c) / RAD) * 6e4;
    }
    out.push(t);
  }
  return out;
}

// Half a minute of slack and then rounded to the minute, so the start never shows early and the
// end never shows late. Where a closing time is set, the day ends then instead of at sunset.
function legalTimes(g, when) {
  const d = new Date(when), s = sunTimes(d.getFullYear(), d.getMonth(), d.getDate(), g.lat, g.lon);
  if (!s) return null;
  const end = cfg.lgEnd == null ? Math.floor((s[1] + cfg.lgAfter * 6e4 - 3e4) / 6e4) * 6e4
    : new Date(d.getFullYear(), d.getMonth(), d.getDate(), 0, cfg.lgEnd).getTime();
  return [Math.ceil((s[0] - cfg.lgBefore * 6e4 + 3e4) / 6e4) * 6e4, end];
}

const spanText = t => clock.format(t[0]) + ' – ' + clock.format(t[1]);

function drawLegal() {
  const g = cfg.geo;
  let label = 'Legal light', line;
  if (!g) {
    line = 'Set location in Setup';
  } else if (g.zone !== zone()) {
    // The phone has changed time zones since the location was saved, so the saved spot is not here.
    line = 'Set location again in Setup';
  } else {
    const t = legalTimes(g, now());
    line = t ? spanText(t) : 'No sunrise or sunset today';
    if (now() - g.at > 2 * 864e5) label += ' · from ' + dayName.format(g.at);
  }
  setText($('lg-l'), label);
  setText($('lg-t'), line);
}

// Kept to a tenth of a degree, a few miles: plenty for sunrise, and not a pin on a stand.
function setPlace(lat, lon, how) {
  cfg.geo = { lat: Math.round(lat * 10) / 10, lon: Math.round(lon * 10) / 10, at: now(), zone: zone() };
  saveCfg();
  note('location saved for legal light, ' + how);
  applyCfg();
}

// Which browser this is on an iPhone, for pointing at the right switch in the phone's Settings.
function browserName() {
  const ua = navigator.userAgent;
  if (!/iPhone|iPad|iPod/.test(ua)) return '';
  return /FxiOS/.test(ua) ? 'Firefox' : /CriOS/.test(ua) ? 'Chrome' : /EdgiOS/.test(ua) ? 'Edge' : 'Safari Websites';
}

function refusedHelp() {
  const b = browserName();
  return 'The phone would not share its location with this page. '
    + (b ? `In the phone's Settings, open Privacy & Security, then Location Services, then ${b}, and choose While Using the App. ` : '')
    + 'Then close this page, open it again, press the button once more and tap Allow when the phone asks. Or set the place by hand below.';
}

function locate() {
  if (locating) return;
  if (!navigator.geolocation || !window.isSecureContext) {
    locateNote = 'This address cannot ask the phone where it is. Set the place by hand below.';
    return drawSetup();
  }
  const run = ++locateRun;
  locating = true;
  locateNote = '';
  drawSetup();
  const stop = text => { clearTimeout(locateWatch); locating = false; locateNote = text; drawSetup(); };
  // The phone's own time limit only starts once permission has been given. A request the phone
  // never asks about would wait for ever, so after a while the button is freed and says so.
  const wait = ms => {
    clearTimeout(locateWatch);
    locateWatch = setTimeout(() => {
      note('location: no answer from the phone');
      stop('The phone has not answered. If it is asking for permission, tap Allow. If it is not, close this page, open it again and press the button once more. Or set the place by hand below.');
    }, ms);
  };
  const got = p => {
    if (run !== locateRun) return;
    clearTimeout(locateWatch);
    locating = false;
    locateNote = '';
    setPlace(p.coords.latitude, p.coords.longitude, 'from the phone');
  };
  const failed = (e, precise) => {
    if (run !== locateRun) return;
    note(`location: code ${e.code}${precise ? ' on the second try' : ''}`);
    if (e.code === 1) return stop(refusedHelp());
    if (!precise) return ask(true);
    stop('The phone could not find itself. Step into the open and press again, or set the place by hand below.');
  };
  // A quick, rough answer first: a few miles is close enough. If that fails, one slower try that
  // lets the phone use its GPS. Always a fresh answer, never one the phone has kept, because the
  // button is pressed when the phone has moved.
  const ask = precise => {
    wait(precise ? 60000 : 30000);
    navigator.geolocation.getCurrentPosition(got, e => failed(e, precise),
      { enableHighAccuracy: precise, timeout: precise ? 45000 : 12000, maximumAge: 0 });
  };
  ask(false);
}

// For when the phone will not give a location: the place typed in, to a tenth of a degree.
function placeByHand() {
  const read = id => parseFloat($(id).value.replace(',', '.'));
  const lat = read('lg-lat'), lon = Math.abs(read('lg-lon'));
  if (!(lat >= 15 && lat <= 72) || !(lon >= 50 && lon <= 170)) {
    locateNote = 'Those do not look right. For North America the latitude is between 15 and 72 and the longitude between 50 and 170. Example: 41.9 and 87.6.';
    return drawSetup();
  }
  locateRun++;                 // anything the phone says about an earlier request no longer counts
  clearTimeout(locateWatch);
  locating = false;
  locateNote = '';
  for (const id of ['lg-lat', 'lg-lon']) { $(id).blur(); $(id).dataset.shown = ''; }   // so the boxes go to what was saved
  setPlace(lat, -lon, 'typed in');
}

// ---------------------------------------------------------------- the screen

function button(cls, label) {
  const b = el('button', 'btn hold ' + cls);
  b.type = 'button';
  b.innerHTML = '<span class="fill"></span><span class="lbl"></span><span class="sub"></span>';
  b.querySelector('.lbl').textContent = label;
  return b;
}

// "Putt (alarm)" is drawn as PUTT with "alarm" on the small line under it.
function split(x) {
  const paren = /\s*\(([^)]*)\)\s*$/.exec(x.label);
  x.short = paren ? x.label.slice(0, paren.index) : x.label;
  x.hint = paren ? paren[1] : '';
}

// Every button is made once. Which ones show, and where, is decided by layout().
function buildBoard() {
  for (const b of longs) {
    const f = b.f;
    split(b);
    b.btn = button('long', b.short);
    holdable(b.btn, {
      ms: holdMs,
      down: () => {
        if (f.state !== 'none' && f.state !== 'error') return false;
        flash(b.btn, f.state === 'none' ? 'add it in setup' : 'needs signal');
        return true;
      },
      can: () => f.state === 'ready',
      run: () => pressLong(b),
      tap: () => flash(b.btn, holdWords(cfg.holdCall) + (S.sound === b && S.mode !== 'idle' ? ' to turn it off' : ' to start')),
    });
    subs.set(b.btn, () => f.state === 'none' ? 'import'
      : f.state === 'loading' ? 'saving ' + Math.floor(100 * f.got / (f.bytes || 1)) + '%'
      : f.state === 'wait' ? 'waiting'
      : f.state === 'error' ? 'not saved'
      : S.sound === b && S.mode === 'muted' ? 'muted'
      : S.sound === b && S.mode === 'playing' ? 'running'
      : b.hint || (b.len ? Math.round(b.len / 60) + ' min' : ''));
  }
  for (const c of calls) {
    split(c);
    c.btn = button('call', c.short);
    holdable(c.btn, {
      ms: holdMs,
      down: () => {
        if (c.seq) {
          if (callReady(c)) {
            // the call player will want it read: start now, while the thumb is still down
            if (!hunting() || cfg.via === 'ctx') seqDecode(c).catch(() => {});
            return false;
          }
          if (c.seq.f.state === 'loading' || c.seq.f.state === 'wait') return false;
          flash(c.btn, c.seq.bad ? 'could not be read' : c.seq.f.state === 'error' ? 'needs signal' : 'add it in setup');
          return true;
        }
        if (callReady(c) || c.takes.some(t => t.f.state !== 'none' && !t.bad)) return false;
        flash(c.btn, c.takes.some(t => t.bad) ? 'could not be read' : 'add it in setup');
        return true;
      },
      can: () => callReady(c),
      run: () => hunting() ? playCall(c) : practice(c),
      tap: () => { const x = calling(); flash(c.btn, holdWords(cfg.holdCall) + (x && x.call === c && c.seq ? ' to end it' : ' to call')); },
    });
    subs.set(c.btn, () => {
      if (!callReady(c)) {
        return c.seq ? (c.seq.bad ? 'unreadable' : c.seq.f.state === 'none' ? 'import' : 'getting ready')
          : c.takes.every(t => t.f.state === 'none') ? 'import' : c.takes.some(t => !t.bad) ? 'getting ready' : 'unreadable';
      }
      if (P.call === c) return P.phase === 'load' ? 'getting ready' : 'loop on';
      if (Q.loading === c) return 'getting ready';
      const x = calling();
      if (x && x.call === c) return c.seq ? fmt(x.left) + ' left' : 'playing';
      return c.hint || (c.seq ? Math.max(1, Math.round(c.seq.seconds / 60)) + ' min' : '');
    });
  }
}

// The buttons for this tab and this mode, in rows. A row holds up to four; a group stays whole.
function layout() {
  const practiceMode = !hunting();
  const shown = x => x.tabs.includes(cfg.tab) && (practiceMode || x.hunt);
  const bg = $('bg-btns'), pad = $('pad');
  bg.textContent = '';
  for (const b of longs) if (b.kind === 'bg' && shown(b)) bg.appendChild(b.btn);
  pad.textContent = '';
  let row = null, n = 0;
  for (const name of M.groups) {
    const items = calls.filter(c => c.group === name && shown(c)).concat(longs.filter(b => b.kind === 'listen' && b.group === name && shown(b)));
    if (!items.length) continue;
    if (!row || n + items.length > 4) { row = el('div', 'pad-row'); pad.appendChild(row); n = 0; }
    const g = el('div', 'grp'), l = el('div', 'grp-l'), bs = el('div', 'grp-b');
    g.style.flexGrow = items.length;
    l.textContent = name;
    for (const it of items) bs.appendChild(it.btn);
    g.append(l, bs);
    row.appendChild(g);
    n += items.length;
    row.className = 'pad-row n' + Math.min(n, 5);      // the more buttons across, the smaller their type
  }
  $('b-spring').classList.toggle('on', cfg.tab === 'spring');
  $('b-fall').classList.toggle('on', cfg.tab === 'fall');
  $('b-hunt').classList.toggle('on', !practiceMode);
  $('b-practice').classList.toggle('on', practiceMode);
  $('b-called').hidden = practiceMode;
  $('b-gap').hidden = $('b-rec').hidden = !practiceMode;
  $('app').classList.toggle('practice', practiceMode);
}

function setTab(tab) {
  if (cfg.tab === tab) return;
  cfg.tab = tab;
  saveCfg();
  layout();
  render();
}

function setMode(mode) {
  if (cfg.mode === mode) return;
  quiet();
  if (mode === 'hunt' && S.sound && S.sound.kind === 'listen') stopLong();    // the real recordings are for Practice
  cfg.mode = mode;
  saveCfg();
  layout();
  render();
  note('mode ' + mode);
}

// Everything on screen is read from the clock and the players each time. Nothing here counts time.
function render() {
  if (!M) return;
  tend();
  const told = S.msg && now() < S.msgUntil ? S.msg : '';

  // the background: which one, and for how long
  const bg = $('bg');
  let l = 'Background', t = 'off', cls = 'idle';
  if (S.mode !== 'idle') {
    const run = fmt((now() - S.since) / 1000);
    cls = S.mode;
    l = S.sound.label + (S.mode !== 'muted' ? ''
      : S.mutedBy === 'phone' ? ' · paused by the phone'
      : S.mutedBy === 'reload' ? ' · the page was reloaded'
      : S.mutedBy === 'recording' ? ' · muted to record'
      : ' · muted');
    t = S.mode === 'muted' ? run : '▶ ' + run;
  } else if (longs.some(b => b.kind === 'bg') && longs.filter(b => b.kind === 'bg').every(b => b.f.state === 'none')) {
    t = 'add sounds in Setup';
  }
  if (bg.className !== 'bg ' + cls) bg.className = 'bg ' + cls;
  setText($('bg-l'), l);
  setText($('bg-t'), t);

  // Hunt: the clock since the last call. Practice: where the answer loop is.
  let a, b = '', live = '';
  if (told) {
    a = told;
  } else if (P.call) {
    const p = V.voice && V.voice.parts.find(x => !x.done), k = V.ctx;
    const left = s => (Math.max(0, s)).toFixed(1) + ' s';
    a = P.call.label;
    live = 'live';
    if (P.phase === 'load') b = 'getting ready';
    else if (P.phase === 'ready') b = 'get ready';
    else if (P.phase === 'rec') { b = 'your answer · ' + left((P.until - now()) / 1000); live = 'rec'; }
    else if (P.phase === 'back') b = 'the call, then you';
    else if (P.phase === 'rest') b = '';
    else if (p && p.at > k.currentTime + 0.05) b = 'your turn · ' + left(p.at - k.currentTime);
    else b = 'listen';
  } else if (calling()) {
    const x = calling();
    a = 'Calling';
    b = x.call.label + (x.call.seq ? ' · ' + fmt(x.left) : '');
    live = 'live';
  } else if (Q.loading) {
    a = 'Calling';
    b = Q.loading.label + ' · getting ready';
  } else if (!hunting()) {
    a = cfg.record ? 'Tap a call: it plays, then records you' : 'Tap a call for its answer loop';
  } else {
    const age = now() - V.lastEnd;
    a = 'Last call';
    b = V.lastEnd && age >= 0 && age < 12 * 3600e3 ? fmt(age / 1000) + ' ago' : 'none yet';
  }
  const last = $('last'), lastCls = 'last ' + live + (told ? ' say' : '');
  if (last.className !== lastCls) last.className = lastCls;
  setText($('last-a'), a);
  setText($('last-b'), b);

  drawLegal();
  drawButtons();
}

function drawButtons() {
  if (!M) return;
  for (const [btn, base] of subs) {
    const mine = pending && pending.btn === btn;
    setText(btn.querySelector('.sub'), btn.dataset.flash
      || (mine ? (pending.stage === 'tap' ? 'tap again' : 'let go now')
        : btn.classList.contains('full') && cfg.startOn === 'release' ? 'let go'
        : base()));
  }
  for (const b of longs) {
    b.btn.classList.toggle('off', b.f.state !== 'ready');
    b.btn.classList.toggle('active', S.sound === b && S.mode !== 'idle');
  }
  for (const c of calls) {
    c.btn.classList.toggle('off', !callReady(c));
    c.btn.classList.toggle('active', P.call === c || Q.call === c || Q.loading === c || !!(V.voice && V.voice.call === c));
  }
  const any = S.mode !== 'idle' || anyCall();
  $('b-stop').classList.toggle('off', !any);
  $('b-mute').classList.toggle('off', !any);
  setText($('b-mute').querySelector('.lbl'), S.mode === 'muted' && !anyCall() ? 'Unmute' : 'Mute');
  setText($('b-gap'), 'Gap ' + (cfg.gap === 1 ? '1×' : cfg.gap === 1.5 ? '1½×' : '2×'));
  $('b-rec').classList.toggle('on', !!cfg.record);
  setText($('b-rec'), cfg.record ? 'Record on' : 'Record');
}

function drawSaved() {
  if (!M) return;
  const pub = files.filter(f => f.where === 'published'), imp = files.filter(f => f.where === 'import');
  const pubHave = pub.filter(f => f.state === 'ready').length, impHave = imp.filter(f => f.state === 'ready').length;
  const canSave = !!(window.caches && navigator.serviceWorker);
  // An added sound that is not the size this version of the page lists is an older cut of it:
  // it still plays (a page update must never silence a working sound), but the screen says so.
  const old = imp.filter(f => f.state === 'ready' && f.odd);
  const t = pub.some(f => f.state === 'loading' || f.state === 'wait') ? `Saving the page's sounds ${pubHave} of ${pub.length}…`
    : pub.some(f => f.state === 'error') ? `The page's sounds: ${pubHave} of ${pub.length} · needs signal`
    : impHave < imp.length ? `Sounds on this phone: ${pubHave + impHave} of ${files.length} · add the rest in Setup`
    : old.length ? `Sounds: ${files.length} of ${files.length} · ${old.length} out of date · add ${old.length === 1 ? 'it' : 'them'} in Setup`
    : !canSave ? `Sounds loaded: ${files.length} of ${files.length} · not saved (address is not https)`
    : !shellSaved ? `Sounds: ${files.length} of ${files.length} · saving the page…`
    : `Sounds on this phone: ${files.length} of ${files.length}`;
  setText($('arm-saved'), t);
  setText($('saved'), updateWaiting ? 'Update ready · tap here to load it' : t);
  const mb = files.filter(f => f.state === 'ready' && f.blob).reduce((sum, f) => sum + f.blob.size, 0) / 1e6;
  const unread = takesOf().concat(seqsOf()).filter(x => x.bad).length;
  setText($('snd-count'), `imported ${impHave} of ${imp.length} · published ${pubHave} of ${pub.length}, ${mb.toFixed(1)} MB.`
    + (unread ? ` Could not be read: ${unread}. Add ${unread === 1 ? 'it' : 'them'} again.` : '')
    + (old.length ? ` An older cut than this page lists: ${old.slice(0, 3).map(f => f.name).join(', ')}${old.length > 3 ? ' and ' + (old.length - 3) + ' more' : ''}.`
      + ` ${old.length === 1 ? 'It still plays' : 'They still play'}; add the new ${old.length === 1 ? 'file' : 'files'} or the new pack to replace ${old.length === 1 ? 'it' : 'them'}.` : '')
    + (canSave ? ' ' + storageNote : ' This address cannot save anything on the phone. Saving needs an https address.'));
}

function drawSetup() {
  if (!M) return;
  for (const seg of document.querySelectorAll('.seg')) {
    const key = seg.dataset.key;
    if (!seg.firstChild) {
      for (const [value, text] of CHOICES[key]) {
        const b = el('button');
        b.type = 'button';
        b.textContent = text;
        b.addEventListener('click', () => { setSetting(key, value); saveCfg(); applyCfg(); });
        seg.appendChild(b);
      }
    }
    [...seg.children].forEach((b, i) => b.classList.toggle('on', CHOICES[key][i][0] === getSetting(key)));
  }
  for (const step of document.querySelectorAll('.step')) {
    const key = step.dataset.key;
    if (!step.firstChild) {
      for (const by of [-5, -1, 0, 1, 5]) {
        const e = el(by ? 'button' : 'span');
        if (by) {
          e.type = 'button';
          e.textContent = (by > 0 ? '+' : '−') + Math.abs(by);
          e.addEventListener('click', () => { cfg[key] = Math.max(0, Math.min(90, cfg[key] + by)); saveCfg(); applyCfg(); });
        } else {
          e.className = 'val';
        }
        step.appendChild(e);
      }
    }
    setText(step.querySelector('.val'), cfg[key] + ' min');
  }
  const g = cfg.geo, t = g && g.zone === zone() && legalTimes(g, now());
  // The boxes show what is saved, but are left alone while someone is typing in them.
  const hhmm = cfg.lgEnd == null ? '' : String(Math.floor(cfg.lgEnd / 60)).padStart(2, '0') + ':' + String(cfg.lgEnd % 60).padStart(2, '0');
  for (const [id, v] of [['lg-lat', g ? g.lat : ''], ['lg-lon', g ? Math.abs(g.lon) : ''], ['lg-end', hhmm]]) {
    const box = $(id);
    if (document.activeElement !== box && box.dataset.shown !== String(v)) { box.value = v; box.dataset.shown = String(v); }
  }
  $('lg-sun').hidden = cfg.lgEnd != null;
  $('lg-clock').hidden = cfg.lgEnd == null;
  setText($('lg-status'), locating ? 'Asking the phone where it is…'
    : locateNote ? locateNote
    : !g ? 'No location saved yet.'
    : `Location saved ${dayName.format(g.at)}${t ? ' · today ' + spanText(t) : ''}. Press again when you move camp.`);
  setText($('pick-l'), importing ? 'Adding…' : 'Add sounds from this phone');
  $('pick-l').parentNode.classList.toggle('busy', importing);
  setText($('snd-note'), importNote);
  setText($('b-forget'), now() - forgetArmed < 4000 ? 'Tap again to remove them' : 'Remove the added sounds');
  drawDiag();
}

// Who made the three recordings that are published with the page, and on what terms.
function drawCredits() {
  const box = $('credits');
  box.textContent = '';
  const short = u => (u || '').replace(/^https?:\/\//, '').replace(/\/$/, '');
  for (const b of longs) {
    if (!b.credit) continue;
    const c = b.credit, p = el('p'), name = el('b');
    name.textContent = b.label;
    p.append(name, ` — recorded by ${c.recordist}, xeno-canto ${c.catalogue} (${short(c.url)}). License: ${c.license}`
      + (c.license_url ? ` (${short(c.license_url)})` : '') + `. Changed from the original: ${c.changes}. This edited version is shared under the same license.`
      + (b.check ? ' ' + b.check : ''));
    box.appendChild(p);
  }
  const p = el('p');
  p.textContent = 'The other backgrounds and the push-button calls are not part of this web page. Each phone gets them from its owner through Add sounds, and they stay on that phone.';
  box.appendChild(p);
}

function drawDiag() {
  const home = navigator.standalone || matchMedia('(display-mode: standalone)').matches;
  const edge = name => parseFloat(getComputedStyle(document.documentElement).getPropertyValue(name)) || 0;
  const k = V.ctx;
  $('diag').textContent = [
    `build ${BUILD} · opened ${home ? 'from the Home Screen' : 'in a browser tab'}`,
    `screen ${screen.width} x ${screen.height} · page ${innerWidth} x ${innerHeight} · kept clear: top ${edge('--edge-top')}, bottom ${edge('--edge-bottom')}`,
    `page saved for offline: ${shellSaved ? 'yes' : 'no'}`,
    `armed: ${armed ? 'yes, ' + cfg.mode : 'no'} · background: ${S.mode}${S.sound ? ' ' + S.sound.id : ''}`,
    `call player: ${k ? k.state + ' @ ' + k.sampleRate : 'none'} · decoded ${takesOf().filter(t => t.buf).length} of ${takesOf().length} takes`
      + (k && k.outputLatency ? ` · output delay ${Math.round((k.outputLatency + (k.baseLatency || 0)) * 1000)} ms` : ''),
    `second player: ${Q.call ? Q.call.id + ' at ' + fmt(seq.currentTime) : 'idle'} · long calls go to ${cfg.via === 'ctx' ? 'the call player' : 'the second player'} · read for the call player: ${seqKept.map(c => c.id).join(', ') || 'none'}`,
    `audio type: ${navigator.audioSession ? navigator.audioSession.type : 'not offered by this browser'} · silent track: ${bed.paused ? 'off' : 'on'} · screen kept awake: ${V.lock ? 'yes' : 'no'}`,
    `last presses, ms from the press to the call starting: ${V.lag.length ? V.lag.join(' ') : 'none yet'}`,
    ...notes.slice(-14),
  ].join('\n');
}

function applyCfg() {
  document.documentElement.classList.toggle('red', !!cfg.red);
  setText($('b-arm-hunt').querySelector('.sub'), cfg.holdCall ? holdWords(cfg.holdCall) + ' on a button plays it' : 'a tap plays a call');
  drawSetup();
  render();
}

function wire() {
  $('b-arm-hunt').addEventListener('click', () => arm('hunt'));
  $('b-arm-practice').addEventListener('click', () => arm('practice'));
  $('b-setup').addEventListener('click', () => { locateNote = ''; $('setup').hidden = false; drawSetup(); drawSaved(); });
  $('b-done').addEventListener('click', closeSetup);
  $('b-locate').addEventListener('click', locate);
  $('b-byhand').addEventListener('click', placeByHand);
  for (const id of ['lg-lat', 'lg-lon']) $(id).addEventListener('keydown', e => { if (e.key === 'Enter') placeByHand(); });
  $('lg-end').addEventListener('change', () => {
    const m = /^(\d{1,2}):(\d{2})/.exec($('lg-end').value);
    if (!m) return;
    cfg.lgEnd = Math.min(23, +m[1]) * 60 + Math.min(59, +m[2]);
    saveCfg();
    applyCfg();
  });
  $('b-redo').addEventListener('click', redownload);
  $('b-forget').addEventListener('click', forgetImports);
  $('pick').addEventListener('change', e => { const list = Array.from(e.target.files || []); e.target.value = ''; importFiles(list); });
  $('saved').addEventListener('click', () => { if (updateWaiting && !sounding() && S.mode === 'idle') location.reload(); });

  $('b-spring').addEventListener('click', () => setTab('spring'));
  $('b-fall').addEventListener('click', () => setTab('fall'));
  $('b-called').addEventListener('click', () => { markCall(); render(); });
  $('b-gap').addEventListener('click', () => { cfg.gap = cfg.gap === 1 ? 1.5 : cfg.gap === 1.5 ? 2 : 1; saveCfg(); applyCfg(); });
  $('b-rec').addEventListener('click', toggleRecord);

  // Hunt is always one tap away. Practice, where a tap makes sound, takes the hold to get into.
  holdable($('b-hunt'), { ms: () => 0, can: () => true, run: () => setMode('hunt') });
  holdable($('b-practice'), { ms: () => hunting() ? cfg.holdCall : 0, can: () => true, run: () => setMode('practice'),
    tap: () => flash($('b-practice'), holdWords(cfg.holdCall)) });
  subs.set($('b-hunt'), () => holdWords(cfg.holdCall));
  subs.set($('b-practice'), () => 'tap');

  holdable($('b-stop'), { ms: () => cfg.hold, can: () => S.mode !== 'idle' || anyCall(), run: stopAll,
    tap: () => flash($('b-stop'), holdWords(cfg.hold)) });
  subs.set($('b-stop'), () => holdWords(cfg.hold));

  // Mute acts the moment the thumb lands, on the background and on any call. Unmuting takes a
  // hold so a brush cannot do it.
  holdable($('b-mute'), {
    ms: () => cfg.holdCall,
    down: () => { if (S.mode !== 'playing' && !anyCall()) return false; muteAll('user'); return true; },
    can: () => S.mode === 'muted',
    run: unmute,
    tap: () => flash($('b-mute'), holdWords(cfg.holdCall) + ' to unmute'),
  });
  subs.set($('b-mute'), () => S.mode === 'muted' && !anyCall() ? holdWords(cfg.holdCall) + ' · the clock kept running'
    : S.mode === 'playing' ? (anyCall() ? 'ends the call · the background keeps its place' : 'the background keeps its place')
    : anyCall() ? 'ends the call' : '');

  document.addEventListener('pointerdown', e => {
    touchedAt = now();
    if (armed) wake();
    if (pending && !pending.btn.contains(e.target)) dropPending();
  }, true);
  document.addEventListener('pointerup', () => { if (armed) wake(); }, true);
  for (const ev of ['contextmenu', 'gesturestart', 'dblclick']) document.addEventListener(ev, e => e.preventDefault());
  document.addEventListener('touchmove', e => { if (!e.target.closest('.setup-body')) e.preventDefault(); }, { passive: false });
  document.addEventListener('visibilitychange', () => {
    if (document.hidden) {
      holdResets.forEach(reset => reset());
      if (P.call) { quiet(); note('answer loop ended: the screen went away'); }
      return;
    }
    if (armed) wake();
    render();
    if (files.some(f => f.state === 'error')) provisionAll();
  });
  window.addEventListener('online', provisionAll);
}

async function boot() {
  wire();
  listen();
  applyCfg();
  setSession('playback');
  try {
    await loadManifest();
  } catch (e) {
    note('manifest: ' + e.message);
    $('b-arm-hunt').hidden = $('b-arm-practice').hidden = true;
    return setText($('arm-note'), 'Could not load the sounds list. Check the signal and reload the page.');
  }
  buildBoard();
  restoreSession();
  if (S.mode === 'muted') setText($('arm-note'), S.sound.label + ' was running. It comes back muted, still in its place. Tap one to arm.');
  $(cfg.mode === 'practice' ? 'b-arm-practice' : 'b-arm-hunt').classList.add('last-used');
  layout();
  drawCredits();
  applyCfg();
  drawSaved();
  worker();
  provisionAll();
  loadImports();
  setInterval(render, 250);
}

window.turkeyboard = { S, V, P, Q, cfg, notes, audio, seq, bed, sunTimes, legalTimes, importFiles, unzip, seqKept,
  get files() { return files; }, get calls() { return calls; }, get longs() { return longs; } };
boot();
