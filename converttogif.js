// ==UserScript==
// @name         GIF Maker – video / GIF / images → GIF (trim, resize, slideshow)
// @namespace    https://violentmonkey.github.io/
// @version      1.0.0
// @description  Hover any video or image and click "GIF" to convert it to a GIF. Trim, resize, change FPS/speed/colors. Also builds GIF slideshows from images.
// @match        *://*/*
// @run-at       document-idle
// @grant        GM_xmlhttpRequest
// @grant        GM_registerMenuCommand
// @grant        GM_getValue
// @grant        GM_setValue
// @connect      *
// ==/UserScript==

(() => {
  'use strict';
  if (window.__gifMakerLoaded) return;
  window.__gifMakerLoaded = true;
  if (window !== window.top && (innerWidth < 200 || innerHeight < 120)) return;

  /* ───────────────────────── helpers ───────────────────────── */
  const sleep = ms => new Promise(r => setTimeout(r, ms));
  const sameOrigin = u => { try { return new URL(u, location.href).origin === location.origin; } catch { return false; } };
  const absUrl = u => new URL(u, location.href).href;
  const fileBase = u => { try { return decodeURIComponent(new URL(u, location.href).pathname.split('/').pop() || '').replace(/\.[a-z0-9]{2,5}$/i, '') || 'media'; } catch { return 'media'; } };
  const fmtSize = b => b > 1048576 ? (b / 1048576).toFixed(1) + ' MB' : Math.max(1, Math.round(b / 1024)) + ' KB';
  const dimW = d => d.videoWidth || d.naturalWidth || d.width;
  const dimH = d => d.videoHeight || d.naturalHeight || d.height;

  function generateRandomString(length = 8) {
  const chars = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789';
  let result = '';
  for (let i = 0; i < length; i++) {
    result += chars.charAt(Math.floor(Math.random() * chars.length));
  }
  return result;
  }

  function gmGet(url, onProg) {
    return new Promise((resolve, reject) => {
      GM_xmlhttpRequest({
        method: 'GET', url, responseType: 'blob', headers: { Referer: location.href },
        onprogress: e => onProg && e.total > 0 && onProg(e.loaded / e.total),
        onload: r => (r.status >= 200 && r.status < 300 ? resolve(r.response) : reject(new Error('HTTP ' + r.status))),
        onerror: () => reject(new Error('Network error while downloading')),
        ontimeout: () => reject(new Error('Download timed out')),
      });
    });
  }
  async function getBlob(url, onProg) {
    const local = /^(blob:|data:)/.test(url);
    if (local || sameOrigin(url)) {
      try { const r = await fetch(url, { credentials: 'include' }); if (r.ok) return await r.blob(); } catch { /* fall through */ }
      if (local) throw new Error('Could not read this media');
    }
    return gmGet(url, onProg);
  }
  async function sniff(blob) {
    const b = new Uint8Array(await blob.slice(0, 16).arrayBuffer());
    const s = String.fromCharCode(...b);
    if (s.startsWith('GIF8')) return 'image/gif';
    if (b[0] === 0x89 && s.slice(1, 4) === 'PNG') return 'image/png';
    if (s.startsWith('RIFF') && s.slice(8, 12) === 'WEBP') return 'image/webp';
    return blob.type || '';
  }
  async function bitmapFromBlob(blob) {
    try { return await createImageBitmap(blob); } catch {
      const im = new Image(); im.src = URL.createObjectURL(blob); await im.decode();
      try { return await createImageBitmap(im); } catch { return im; }
    }
  }
  function waitEvent(el, ev, ms = 20000) {
    return new Promise((res, rej) => {
      const h = () => { clearTimeout(t); res(); };
      const t = setTimeout(() => { el.removeEventListener(ev, h); rej(new Error('Timed out waiting for ' + ev)); }, ms);
      el.addEventListener(ev, h, { once: true });
    });
  }
  function seek(v, t) {
    return new Promise(res => {
      t = Math.min(Math.max(0, t), Math.max(0, v.duration - 0.001));
      if (Math.abs(v.currentTime - t) < 0.0005 && v.readyState >= 2) return res();
      const done = () => { v.removeEventListener('seeked', done); clearTimeout(to); res(); };
      const to = setTimeout(done, 4000);
      v.addEventListener('seeked', done);
      v.currentTime = t;
    });
  }

  /* ───────────────────────── GIF encoder ───────────────────────── */
  function lzw(minCode, px) {
    const clear = 1 << minCode, eoi = clear + 1;
    let size = minCode + 1, next = eoi + 1, cur = 0, bits = 0, dict = new Map();
    const out = [];
    const emit = c => { cur |= c << bits; bits += size; while (bits >= 8) { out.push(cur & 255); cur >>= 8; bits -= 8; } };
    emit(clear);
    let pre = px[0];
    for (let i = 1; i < px.length; i++) {
      const k = px[i], key = (pre << 8) | k, v = dict.get(key);
      if (v !== undefined) { pre = v; continue; }
      emit(pre);
      if (next < 4096) { dict.set(key, next); if (next >= (1 << size) && size < 12) size++; next++; }
      else { emit(clear); dict = new Map(); size = minCode + 1; next = eoi + 1; }
      pre = k;
    }
    emit(pre);
    if (next >= (1 << size) && size < 12) size++;
    emit(eoi);
    if (bits > 0) out.push(cur & 255);
    return Uint8Array.from(out);
  }

  class GifEncoder {
    constructor(w, h, loop) {
      this.w = w; this.h = h; this.parts = [];
      const hdr = [71, 73, 70, 56, 57, 97, w & 255, w >> 8, h & 255, h >> 8, 0, 0, 0];
      if (loop != null) hdr.push(0x21, 0xFF, 0x0B, ...[...'NETSCAPE2.0'].map(c => c.charCodeAt(0)), 3, 1, loop & 255, loop >> 8, 0);
      this.parts.push(new Uint8Array(hdr));
    }
    addFrame(idx, pal, count, delay, transp) {
      const bits = Math.max(1, Math.ceil(Math.log2(count))), size = 1 << bits;
      const lct = new Uint8Array(size * 3); lct.set(pal.subarray(0, count * 3));
      const head = new Uint8Array([0x21, 0xF9, 4, transp ? 9 : 4, delay & 255, delay >> 8, 0, 0,
        0x2C, 0, 0, 0, 0, this.w & 255, this.w >> 8, this.h & 255, this.h >> 8, 0x80 | (bits - 1)]);
      const minCode = Math.max(2, bits), data = lzw(minCode, idx);
      const blocks = new Uint8Array(1 + data.length + Math.ceil(data.length / 255) + 1);
      let p = 0; blocks[p++] = minCode;
      for (let i = 0; i < data.length; i += 255) {
        const n = Math.min(255, data.length - i); blocks[p++] = n; blocks.set(data.subarray(i, i + n), p); p += n;
      }
      blocks[p++] = 0;
      this.parts.push(head, lct, blocks.subarray(0, p));
    }
    finish() { this.parts.push(new Uint8Array([0x3B])); return new Blob(this.parts, { type: 'image/gif' }); }
  }

  // Median-cut quantizer (5 bits/channel histogram)
  function quantize(px, n, maxC, transp) {
    const hist = new Uint32Array(32768), off = transp ? 1 : 0;
    for (let i = 0, p = 0; i < n; i++, p += 4) {
      if (transp && px[p + 3] < 128) continue;
      hist[((px[p] >> 3) << 10) | ((px[p + 1] >> 3) << 5) | (px[p + 2] >> 3)]++;
    }
    const keys = [];
    for (let k = 0; k < 32768; k++) if (hist[k]) keys.push(k);
    const idx = new Uint8Array(n);
    if (!keys.length) return { indices: idx, palette: new Uint8Array(6), count: 1 };
    const mk = ks => {
      let mn = [31, 31, 31], mx = [0, 0, 0], pop = 0;
      for (const k of ks) {
        pop += hist[k];
        const c = [k >> 10, (k >> 5) & 31, k & 31];
        for (let j = 0; j < 3; j++) { if (c[j] < mn[j]) mn[j] = c[j]; if (c[j] > mx[j]) mx[j] = c[j]; }
      }
      const rg = [mx[0] - mn[0], mx[1] - mn[1], mx[2] - mn[2]];
      const ch = rg[0] >= rg[1] && rg[0] >= rg[2] ? 0 : rg[1] >= rg[2] ? 1 : 2;
      return { ks, pop, ch, rng: rg[ch] };
    };
    const limit = maxC - off, boxes = [mk(keys)];
    while (boxes.length < limit) {
      let bi = -1, bs = 0;
      for (let i = 0; i < boxes.length; i++) {
        const b = boxes[i]; if (b.ks.length < 2) continue;
        const s = (b.rng + 1) * Math.sqrt(b.pop);
        if (s > bs) { bs = s; bi = i; }
      }
      if (bi < 0) break;
      const b = boxes[bi], sh = [10, 5, 0][b.ch];
      b.ks.sort((x, y) => ((x >> sh) & 31) - ((y >> sh) & 31));
      let acc = 0, cut = 1;
      for (let i = 0; i < b.ks.length - 1; i++) { acc += hist[b.ks[i]]; cut = i + 1; if (acc >= b.pop / 2) break; }
      boxes.splice(bi, 1, mk(b.ks.slice(0, cut)), mk(b.ks.slice(cut)));
    }
    const count = boxes.length + off, pal = new Uint8Array(Math.max(count, 2) * 3);
    boxes.forEach((b, i) => {
      let r = 0, g = 0, bl = 0;
      for (const k of b.ks) { const w = hist[k]; r += (k >> 10) * w; g += ((k >> 5) & 31) * w; bl += (k & 31) * w; }
      pal[(i + off) * 3] = Math.round(r / b.pop * 255 / 31);
      pal[(i + off) * 3 + 1] = Math.round(g / b.pop * 255 / 31);
      pal[(i + off) * 3 + 2] = Math.round(bl / b.pop * 255 / 31);
    });
    const lut = new Int16Array(32768).fill(-1), nb = boxes.length;
    for (let i = 0, p = 0; i < n; i++, p += 4) {
      if (transp && px[p + 3] < 128) { idx[i] = 0; continue; }
      const k = ((px[p] >> 3) << 10) | ((px[p + 1] >> 3) << 5) | (px[p + 2] >> 3);
      let j = lut[k];
      if (j < 0) {
        const r = px[p], g = px[p + 1], b = px[p + 2]; let best = 1e9; j = 0;
        for (let q = 0; q < nb; q++) {
          const dr = pal[(q + off) * 3] - r, dg = pal[(q + off) * 3 + 1] - g, db = pal[(q + off) * 3 + 2] - b;
          const dd = dr * dr + dg * dg + db * db;
          if (dd < best) { best = dd; j = q; }
        }
        lut[k] = j;
      }
      idx[i] = j + off;
    }
    return { indices: idx, palette: pal, count };
  }

  function drawFit(ctx, d, w, h, fit, bg) {
    ctx.clearRect(0, 0, w, h);
    if (bg) { ctx.fillStyle = bg; ctx.fillRect(0, 0, w, h); }
    const sw = dimW(d), sh = dimH(d);
    let dw = w, dh = h, dx = 0, dy = 0;
    if (fit !== 'stretch') {
      const s = fit === 'cover' ? Math.max(w / sw, h / sh) : Math.min(w / sw, h / sh);
      dw = sw * s; dh = sh * s; dx = (w - dw) / 2; dy = (h - dh) / 2;
    }
    ctx.imageSmoothingQuality = 'high';
    ctx.drawImage(d, dx, dy, dw, dh);
  }

  function makeEncoder({ w, h, maxColors, loop, transparent, bg, fit }) {
    const c = document.createElement('canvas'); c.width = w; c.height = h;
    const ctx = c.getContext('2d', { willReadFrequently: true });
    const gif = new GifEncoder(w, h, loop ? 0 : null);
    return {
      add(d, cs) {
        drawFit(ctx, d, w, h, fit, transparent ? null : bg);
        const { data } = ctx.getImageData(0, 0, w, h);
        const q = quantize(data, w * h, maxColors, transparent);
        gif.addFrame(q.indices, q.palette, q.count, Math.max(2, cs), transparent);
      },
      finish: () => gif.finish(),
    };
  }

  /* ───────────────────────── media sources ───────────────────────── */
  async function videoSource(el, status) {
    const s = el.currentSrc || el.src || '';
    let v, cleanup = () => {};
    if (!s || s.startsWith('blob:')) {            // MediaSource / streamed video: use the live element
      v = el;
      const t0 = el.currentTime, wasPlaying = !el.paused, wasMuted = el.muted;
      el.pause(); el.muted = true;
      cleanup = () => { el.muted = wasMuted; try { el.currentTime = t0; } catch {} if (wasPlaying) el.play().catch(() => {}); };
    } else {
      let url = s, revoke = () => {};
      if (!sameOrigin(s)) {
        status('Downloading video…');
        const blob = await getBlob(s, p => status(`Downloading video ${Math.round(p * 100)}%`));
        url = URL.createObjectURL(blob); revoke = () => URL.revokeObjectURL(url);
      }
      v = document.createElement('video'); v.muted = true; v.preload = 'auto'; v.playsInline = true; v.src = url;
      cleanup = () => { revoke(); v.removeAttribute('src'); v.load(); };
      status('Reading video…');
    }
    try {
      if (v.readyState < 1) {
        await Promise.race([waitEvent(v, 'loadedmetadata'),
          new Promise((_, rej) => v.addEventListener('error', () => rej(new Error('Video failed to load (unsupported codec or blocked).')), { once: true }))]);
      }
      if (!isFinite(v.duration) || !v.duration) throw new Error('Live / endless streams have no fixed length and are not supported.');
      if (!v.videoWidth) throw new Error('Could not read video dimensions.');
      await seek(v, 0);
    } catch (e) { cleanup(); throw e; }
    return { kind: 'video', el: v, w: v.videoWidth, h: v.videoHeight, duration: v.duration, fps: 15,
      getFrame: async t => { await seek(v, t); return v; }, cleanup };
  }

  function framesSource(frames, total) {
    return {
      kind: 'frames', w: frames[0].bmp.width, h: frames[0].bmp.height, duration: total,
      fps: Math.min(30, Math.max(5, Math.round(frames.length / total))),
      async getFrame(t) {
        let lo = 0, hi = frames.length - 1;
        while (lo < hi) { const m = (lo + hi + 1) >> 1; if (frames[m].t <= t) lo = m; else hi = m - 1; }
        return frames[lo].bmp;
      },
      cleanup() { frames.forEach(f => f.bmp.close && f.bmp.close()); },
    };
  }

  async function imageSource(url, status) {
    status('Loading image…');
    const blob = await getBlob(url, p => status(`Downloading ${Math.round(p * 100)}%`));
    const type = await sniff(blob);
    if (typeof ImageDecoder !== 'undefined' && /^image\/(gif|webp|png)$/.test(type)) {
      try {
        if (await ImageDecoder.isTypeSupported(type)) {
          const dec = new ImageDecoder({ data: await blob.arrayBuffer(), type });
          await dec.tracks.ready;
          const n = dec.tracks.selectedTrack.frameCount;
          if (n > 1) {
            const frames = []; let t = 0;
            for (let i = 0; i < n; i++) {
              const { image } = await dec.decode({ frameIndex: i });
              const d = Math.max((image.duration || 100000) / 1e6, 0.02);
              const bmp = await createImageBitmap(image); image.close();
              frames.push({ bmp, t, d }); t += d;
              if (i % 8 === 0) { status(`Decoding frames ${i + 1}/${n}`); await sleep(0); }
            }
            dec.close();
            return framesSource(frames, t);
          }
          dec.close();
        }
      } catch (e) { console.warn('[GIF Maker] ImageDecoder failed, using first frame only', e); }
    }
    const bmp = await bitmapFromBlob(blob);
    return { kind: 'image', w: dimW(bmp), h: dimH(bmp), duration: 0, fps: 10, getFrame: async () => bmp, cleanup() { bmp.close && bmp.close(); } };
  }

  function resolveMedia(el, allowBg) {
    if (!(el instanceof Element)) return null;
    const r = el.getBoundingClientRect();
    if (el.tagName === 'VIDEO') return r.width >= 80 && r.height >= 50 ? { type: 'video', el } : null;
    if (el.tagName === 'IMG') {
      const u = el.currentSrc || el.src;
      return u && r.width >= 48 && r.height >= 48 ? { type: 'image', el, url: u } : null;
    }
    if (allowBg) {
      const m = /url\(["']?(.*?)["']?\)/.exec(getComputedStyle(el).backgroundImage || '');
      if (m && m[1] && !/gradient/.test(m[1])) return { type: 'image', el, url: absUrl(m[1]) };
    }
    return null;
  }

  /* ───────────────────────── UI: host, styles ───────────────────────── */
  const CSS = `
*{box-sizing:border-box;font:13px/1.4 system-ui,"Segoe UI",Roboto,sans-serif}
.hb{position:fixed;display:none;gap:4px;z-index:2}
.hb button{all:unset;cursor:pointer;background:#111d;color:#fff;font:600 12px system-ui;padding:5px 9px;border-radius:999px;border:1px solid #fff5;box-shadow:0 2px 8px #0007}
.hb button:hover{background:#7c3aed}
.ov{position:fixed;inset:0;background:#000b;display:flex;align-items:center;justify-content:center;z-index:5}
.dlg{background:#16161a;color:#eee;width:min(980px,96vw);max-height:94vh;display:flex;flex-direction:column;border-radius:12px;box-shadow:0 10px 50px #000}
.hd{display:flex;align-items:center;gap:10px;padding:10px 14px;border-bottom:1px solid #333}
.hd b{font-size:15px}.hd .sub{opacity:.6;flex:1;overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.bd{display:flex;gap:16px;padding:14px;overflow:auto;flex-wrap:wrap}
.pv{flex:1 1 380px;min-width:0;display:flex;flex-direction:column;gap:10px;align-items:center}
.pv canvas,.pv img.out{max-width:100%;max-height:44vh;border-radius:6px;background:repeating-conic-gradient(#3a3a3a 0 25%,#2c2c2c 0 50%) 0 0/16px 16px}
.ctl{flex:1 1 330px;display:grid;gap:8px;align-content:start}
.row{display:grid;grid-template-columns:62px 1fr 78px;gap:8px;align-items:center}
.row.opts{grid-template-columns:62px 1fr}.row.opts div{display:flex;gap:12px;flex-wrap:wrap}
label{opacity:.85}
input,select{background:#25252b;color:#eee;border:1px solid #444;border-radius:6px;padding:4px 6px;min-width:0}
input[type=range]{padding:0;width:100%}input[type=checkbox]{margin-right:4px}input[type=color]{padding:0;height:24px;width:40px}
.btn{all:unset;cursor:pointer;background:#2e2e36;color:#eee;padding:6px 12px;border-radius:7px;border:1px solid #484852;text-align:center;font-size:13px}
.btn:hover{background:#3b3b46}.btn.pri{background:#7c3aed;border-color:#8b5cf6;font-weight:600}.btn.pri:hover{background:#6d28d9}.btn.warn{background:#b91c1c;border-color:#dc2626}
.x{margin-left:auto}.info{opacity:.7;font-size:12px}.info.bad{color:#f87171;opacity:1}
progress{width:100%;height:8px}.res{display:flex;flex-direction:column;gap:8px;align-items:center;max-width:100%;text-align:center}
.note{background:#25252b;padding:8px;border-radius:6px;display:grid;gap:8px}
.drop{border:2px dashed #555;border-radius:8px;padding:12px;display:flex;gap:8px;align-items:center;flex-wrap:wrap;width:100%}
.list{display:grid;gap:6px;width:100%;max-height:40vh;overflow:auto}
.item{display:grid;grid-template-columns:44px 1fr 70px auto auto auto;gap:6px;align-items:center;background:#202026;padding:4px;border-radius:6px}
.item img{width:44px;height:44px;object-fit:cover;border-radius:4px}.item .nm{overflow:hidden;text-overflow:ellipsis;white-space:nowrap}
.item .btn{padding:4px 8px}
.toast{position:fixed;left:50%;bottom:24px;transform:translateX(-50%);background:#16161a;color:#eee;padding:10px 14px;border-radius:10px;box-shadow:0 4px 24px #000a;display:flex;gap:10px;align-items:center;z-index:6;border:1px solid #444}
.pkhl{position:fixed;border:2px solid #a78bfa;background:#7c3aed33;pointer-events:none;z-index:3;display:none}
.pkb{position:fixed;top:12px;left:50%;transform:translateX(-50%);background:#7c3aed;color:#fff;padding:8px 16px;border-radius:999px;z-index:4;font-weight:600;pointer-events:none}
`;

  let host, root, current = null, picking = false, hoverOn = true;
  try { hoverOn = GM_getValue('hover', true); } catch {}
  function ensureHost() {
    if (host && host.isConnected) return;
    host = document.createElement('div'); host.id = 'gifmaker-host';
    host.style.cssText = 'all:initial;position:fixed;z-index:2147483647;top:0;left:0;width:0;height:0';
    root = host.attachShadow({ mode: 'open' });
    root.innerHTML = `<style>${CSS}</style>`;
    document.documentElement.appendChild(host);
    hb = null;
  }
  function toast(msg, label, action) {
    ensureHost();
    const t = document.createElement('div'); t.className = 'toast'; t.textContent = msg;
    if (label) { const b = document.createElement('button'); b.className = 'btn'; b.textContent = label; b.onclick = () => { action(); t.remove(); }; t.append(b); }
    root.appendChild(t); setTimeout(() => t.remove(), 5000);
  }

  function dialog(title, sub) {
    ensureHost(); if (current) current.close();
    const ov = document.createElement('div'); ov.className = 'ov';
    ov.innerHTML = `<div class="dlg"><div class="hd"><b>${title}</b><span class="sub"></span><button class="btn x">✕</button></div><div class="bd"></div></div>`;
    ov.querySelector('.sub').textContent = sub || '';
    root.appendChild(ov);
    const d = { ov, bd: ov.querySelector('.bd'), cleanups: [], render: null,
      close() { this.cleanups.forEach(f => { try { f(); } catch {} }); ov.remove(); if (current === d) current = null; } };
    ['keydown', 'keyup', 'keypress'].forEach(ev => ov.addEventListener(ev, e => { e.stopPropagation(); if (ev === 'keydown' && e.key === 'Escape') d.close(); }));
    ov.querySelector('.x').onclick = () => d.close();
    current = d; return d;
  }

  function wireGo(d, name, producer) {
    const $ = s => d.bd.querySelector(s), go = $('.go'), pg = $('progress'), res = $('.res');
    let job = null, url = null;
    go.onclick = async () => {
      if (job) { job.cancel = true; return; }
      job = { cancel: false }; go.textContent = 'Cancel'; go.classList.add('warn'); pg.hidden = false; pg.value = 0; res.textContent = '';
      try {
        const blob = await producer(job, p => { pg.value = p; });
        if (url) URL.revokeObjectURL(url);
        url = URL.createObjectURL(blob);
        res.innerHTML = '';
        const img = new Image(); img.src = url; img.className = 'out';
        const a = document.createElement('a'); a.href = url; a.download = generateRandomString() + '.gif'; a.className = 'btn pri';
        a.textContent = `⬇ Download GIF (${fmtSize(blob.size)})`;
        res.append(img, a); a.click();
      } catch (e) {
        res.textContent = e.message === 'Cancelled' ? 'Cancelled.'
          : '⚠ ' + (e.name === 'SecurityError' ? 'The browser blocked reading this media (cross-origin or DRM-protected).' : e.message);
      } finally { job = null; pg.hidden = true; go.textContent = 'Create GIF'; go.classList.remove('warn'); }
    };
    d.cleanups.push(() => { if (job) job.cancel = true; if (url) URL.revokeObjectURL(url); });
  }

  /* ───────────────────────── media editor (video / gif / image → GIF) ───────────────────────── */
  async function openMedia(m) {
    const d = dialog('GIF Maker', m.type === 'video' ? 'Video → GIF' : fileBase(m.url));
    const msg = document.createElement('div'); msg.style.padding = '30px'; msg.textContent = 'Loading…'; d.bd.append(msg);
    let src;
    try { src = m.type === 'video' ? await videoSource(m.el, t => { msg.textContent = t; }) : await imageSource(m.url, t => { msg.textContent = t; }); }
    catch (e) { msg.textContent = '⚠ ' + e.message; return; }
    if (current !== d) { src.cleanup(); return; }
    d.cleanups.push(() => src.cleanup());
    msg.remove();
    buildMediaUI(d, src, m);
  }

  function buildMediaUI(d, src, m) {
    const still = src.kind === 'image', dur = src.duration || 0, $ = s => d.bd.querySelector(s);
    const maxW = Math.min(src.w, 1920);
    d.bd.innerHTML = `
<div class="pv"><canvas></canvas>${still ? '' : '<button class="btn play">▶ Play selected range</button>'}<div class="res"></div></div>
<div class="ctl">
${still ? `<div class="note">This is a still image, so the GIF will have one frame. To combine several images into an animation, use the slideshow maker.<button class="btn add">＋ Add to slideshow</button></div>` : `
<div class="row"><label>Start (s)</label><input type="range" class="s" min="0" max="${dur}" step="0.01"><input type="number" class="sn" step="0.1" min="0" max="${dur}"></div>
<div class="row"><label>End (s)</label><input type="range" class="e" min="0" max="${dur}" step="0.01"><input type="number" class="en" step="0.1" min="0" max="${dur}"></div>`}
<div class="row"><label>Width</label><input type="range" class="w" min="40" max="${maxW}" step="1"><input type="number" class="wn" min="40" max="${maxW}"></div>
<div class="row"><label>FPS</label><input type="range" class="f" min="1" max="50" step="1"><input type="number" class="fn" min="1" max="50"></div>
${still ? '' : `<div class="row"><label>Speed</label><select class="sp"><option value="0.25">0.25×</option><option value="0.5">0.5×</option><option value="1" selected>1×</option><option value="1.5">1.5×</option><option value="2">2×</option><option value="4">4×</option></select><span></span></div>`}
<div class="row"><label>Colors</label><select class="col"><option>256</option><option>128</option><option>64</option><option>32</option><option>16</option></select><span></span></div>
<div class="row opts"><label>Options</label><div><label><input type="checkbox" class="lp" checked>Loop</label><label><input type="checkbox" class="tr">Transparent</label><label>BG <input type="color" class="bg" value="#ffffff"></label></div></div>
<div class="info"></div>
<button class="btn pri go">Create GIF</button><progress hidden max="1"></progress>
</div>`;

    const st = { start: 0, end: still ? 0 : (src.kind === 'frames' ? dur : Math.min(dur, 5)) };
    const link = (rs, ns, val, fn) => {
      const r = $(rs), n = $(ns); r.value = n.value = val;
      r.oninput = () => { n.value = r.value; fn(+r.value); };
      n.onchange = () => { r.value = n.value; n.value = r.value; fn(+r.value); };
    };
    const canvas = $('canvas'), cx = canvas.getContext('2d');
    let width = Math.min(src.w, 480), fps = src.fps, last = null, tok = 0, playing = false, raf = 0;
    const height = () => Math.max(2, Math.round(width * src.h / src.w));
    const draw = dd => { last = dd; canvas.width = width; canvas.height = height(); cx.drawImage(dd, 0, 0, canvas.width, canvas.height); };
    const previewAt = async t => { const k = ++tok; const dd = await src.getFrame(t); if (k === tok && !playing) draw(dd); };
    const nFrames = () => still ? 1 : Math.max(1, Math.floor((st.end - st.start) * fps / +$('.sp').value));
    const upd = () => {
      const n = nFrames(), est = width * height() * n * 0.12, info = $('.info');
      info.textContent = `${n} frames · ${width}×${height()} · ${(n / fps).toFixed(1)}s · est. ≈${fmtSize(est)}`;
      info.classList.toggle('bad', est > 25e6 || n > 600);
    };

    if (!still) {
      link('.s', '.sn', 0, v => { st.start = Math.min(v, st.end - 0.05); if (st.start !== v) $('.s').value = $('.sn').value = st.start; stopPlay(); previewAt(st.start); upd(); });
      link('.e', '.en', st.end, v => { st.end = Math.max(v, st.start + 0.05); if (st.end !== v) $('.e').value = $('.en').value = st.end; stopPlay(); previewAt(Math.max(0, st.end - 0.02)); upd(); });
      $('.sp').onchange = upd;
    }
    link('.w', '.wn', width, v => { width = Math.max(40, v | 0); if (last) draw(last); upd(); });
    link('.f', '.fn', fps, v => { fps = Math.min(50, Math.max(1, v | 0)); upd(); });
    $('.tr').checked = false;

    function stopPlay() {
      if (!playing) return; playing = false; cancelAnimationFrame(raf);
      if (src.kind === 'video') src.el.pause();
      $('.play') && ($('.play').textContent = '▶ Play selected range');
    }
    d.cleanups.push(() => { playing = false; cancelAnimationFrame(raf); if (src.kind === 'video') src.el.pause(); });
    if ($('.play')) $('.play').onclick = async () => {
      if (playing) return stopPlay();
      playing = true; $('.play').textContent = '■ Stop'; const speed = +$('.sp').value;
      if (src.kind === 'video') {
        const v = src.el; await seek(v, st.start); v.playbackRate = speed; v.play().catch(() => {});
        const loop = () => { if (!playing) return; if (v.currentTime >= st.end || v.ended) { v.currentTime = st.start; v.play().catch(() => {}); } draw(v); raf = requestAnimationFrame(loop); };
        loop();
      } else {
        const t0 = performance.now();
        const loop = async () => { if (!playing) return; const t = st.start + (((performance.now() - t0) / 1000 * speed) % (st.end - st.start)); draw(await src.getFrame(t)); raf = requestAnimationFrame(loop); };
        loop();
      }
    };
    if ($('.add')) $('.add').onclick = () => { addSlideUrl(m.url).then(() => { d.close(); openSlides(); }).catch(e => toast('⚠ ' + e.message)); };

    wireGo(d, () => fileBase(m.url || location.pathname) || 'video', async (job, prog) => {
      stopPlay();
      const speed = still ? 1 : +$('.sp').value, n = nFrames(), step = speed / fps;
      const enc = makeEncoder({ w: width, h: height(), maxColors: +$('.col').value, loop: $('.lp').checked,
        transparent: $('.tr').checked, bg: $('.bg').value, fit: 'stretch' });
      for (let i = 0; i < n; i++) {
        if (job.cancel) throw new Error('Cancelled');
        const t = Math.min(st.start + i * step, Math.max(0, dur - 0.001));
        const dd = await src.getFrame(t);
        enc.add(dd, Math.round((i + 1) * 100 / fps) - Math.round(i * 100 / fps));
        prog((i + 1) / n); await sleep(0);
      }
      return enc.finish();
    });
    upd(); previewAt(st.start);
  }

  /* ───────────────────────── slideshow editor (images → GIF) ───────────────────────── */
  const slides = []; let slideUid = 0, slideDelay = 500;
  async function addSlideBlob(blob, name) {
    const bmp = await bitmapFromBlob(blob), w = dimW(bmp), h = dimH(bmp);
    const c = document.createElement('canvas'), s = Math.min(1, 96 / Math.max(w, h));
    c.width = Math.max(1, Math.round(w * s)); c.height = Math.max(1, Math.round(h * s));
    c.getContext('2d').drawImage(bmp, 0, 0, c.width, c.height);
    slides.push({ id: ++slideUid, name, bmp, w, h, delay: slideDelay, thumb: c.toDataURL() });
  }
  async function addSlideUrl(url) { await addSlideBlob(await getBlob(url), fileBase(url)); }

  function openSlides() {
    const d = dialog('GIF Maker', 'Images → GIF slideshow'), $ = s => d.bd.querySelector(s);
    d.bd.innerHTML = `
<div class="pv" style="align-items:stretch;flex:1 1 420px">
 <div class="drop"><span>Drop images here</span><button class="btn" data-a="file">Choose files</button><button class="btn" data-a="page">Pick from page</button><button class="btn" data-a="url">Add URL</button><input type="file" multiple accept="image/*" hidden></div>
 <div class="list"></div><div class="res"></div>
</div>
<div class="ctl">
 <div class="row"><label>Delay ms</label><input type="number" class="gd" min="20" step="10" value="${slideDelay}"><button class="btn apply">Apply all</button></div>
 <div class="row"><label>Size</label><input type="number" class="wn" min="16" max="1920" placeholder="width"><input type="number" class="hn" min="16" max="1920" placeholder="height"></div>
 <div class="row"><label>Fit</label><select class="fit"><option value="contain">Contain (letterbox)</option><option value="cover">Cover (crop)</option><option value="stretch">Stretch</option></select><span></span></div>
 <div class="row"><label>Colors</label><select class="col"><option>256</option><option>128</option><option>64</option><option>32</option></select><span></span></div>
 <div class="row opts"><label>Options</label><div><label><input type="checkbox" class="lp" checked>Loop</label><label><input type="checkbox" class="pp">Ping-pong</label><label><input type="checkbox" class="tr">Transparent</label><label>BG <input type="color" class="bg" value="#ffffff"></label></div></div>
 <button class="btn rev">⇅ Reverse order</button>
 <div class="info"></div>
 <button class="btn pri go">Create GIF</button><progress hidden max="1"></progress>
</div>`;
    const list = $('.list'), fileIn = $('input[type=file]');
    let touched = false;
    d.render = () => {
      list.innerHTML = '';
      slides.forEach((s, i) => {
        const r = document.createElement('div'); r.className = 'item'; r.dataset.i = i;
        r.innerHTML = `<img src="${s.thumb}"><span class="nm"></span><input type="number" class="dl" min="20" step="10" value="${s.delay}"><button class="btn" data-a="up">↑</button><button class="btn" data-a="dn">↓</button><button class="btn" data-a="rm">✕</button>`;
        r.querySelector('.nm').textContent = `${i + 1}. ${s.name}`; list.append(r);
      });
      if (!slides.length) list.textContent = 'No images yet.';
      if (slides.length && !touched) { const w = Math.min(slides[0].w, 480); $('.wn').value = w; $('.hn').value = Math.round(w * slides[0].h / slides[0].w); }
      $('.info').textContent = `${slides.length} image${slides.length === 1 ? '' : 's'}`;
    };
    $('.wn').oninput = $('.hn').oninput = () => { touched = true; };
    $('.gd').onchange = () => { slideDelay = Math.max(20, +$('.gd').value || 500); };
    $('.apply').onclick = () => { slideDelay = Math.max(20, +$('.gd').value || 500); slides.forEach(s => { s.delay = slideDelay; }); d.render(); };
    $('.rev').onclick = () => { slides.reverse(); d.render(); };
    list.onclick = e => {
      const b = e.target.closest('button'); if (!b) return;
      const i = +b.closest('.item').dataset.i, a = b.dataset.a;
      if (a === 'rm') slides.splice(i, 1);
      else if (a === 'up' && i > 0) [slides[i - 1], slides[i]] = [slides[i], slides[i - 1]];
      else if (a === 'dn' && i < slides.length - 1) [slides[i + 1], slides[i]] = [slides[i], slides[i + 1]];
      d.render();
    };
    list.onchange = e => { if (e.target.classList.contains('dl')) slides[+e.target.closest('.item').dataset.i].delay = Math.max(20, +e.target.value || 100); };
    const addFiles = async files => {
      for (const f of files) { if (!f.type.startsWith('image/')) continue; try { await addSlideBlob(f, f.name.replace(/\.[^.]+$/, '')); } catch (e) { toast('⚠ ' + f.name + ': ' + e.message); } }
      d.render();
    };
    fileIn.onchange = () => { addFiles([...fileIn.files]); fileIn.value = ''; };
    d.ov.addEventListener('dragover', e => e.preventDefault());
    d.ov.addEventListener('drop', e => { e.preventDefault(); addFiles([...e.dataTransfer.files]); });
    $('.drop').onclick = async e => {
      const a = e.target.closest('button')?.dataset.a;
      if (a === 'file') fileIn.click();
      else if (a === 'url') { const u = prompt('Image URL:'); if (u) { try { await addSlideUrl(absUrl(u.trim())); d.render(); } catch (err) { toast('⚠ ' + err.message); } } }
      else if (a === 'page') {
        d.ov.style.display = 'none';
        startPicker(async mm => {
          d.ov.style.display = '';
          if (mm.type !== 'image') return toast('Pick an image (videos can be converted directly).');
          try { await addSlideUrl(mm.url); d.render(); } catch (err) { toast('⚠ ' + err.message); }
        }, () => { d.ov.style.display = ''; });
      }
    };
    wireGo(d, () => 'slideshow', async (job, prog) => {
      if (!slides.length) throw new Error('Add at least one image.');
      const w = Math.max(16, +$('.wn').value || Math.min(slides[0].w, 480));
      const h = Math.max(16, +$('.hn').value || Math.round(w * slides[0].h / slides[0].w));
      const enc = makeEncoder({ w, h, maxColors: +$('.col').value, loop: $('.lp').checked, transparent: $('.tr').checked, bg: $('.bg').value, fit: $('.fit').value });
      let seq = slides.slice();
      if ($('.pp').checked && seq.length > 2) seq = seq.concat(seq.slice(1, -1).reverse());
      for (let i = 0; i < seq.length; i++) {
        if (job.cancel) throw new Error('Cancelled');
        enc.add(seq[i].bmp, Math.round(seq[i].delay / 10));
        prog((i + 1) / seq.length); await sleep(0);
      }
      return enc.finish();
    });
    d.render();
  }

  /* ───────────────────────── hover button ───────────────────────── */
  let hb = null, hbTarget = null, hideT = 0, raf = 0, mx = 0, my = 0;
  function buildHB() {
    hb = document.createElement('div'); hb.className = 'hb';
    hb.innerHTML = '<button class="g" title="Convert to GIF">GIF</button><button class="p" title="Add to slideshow">＋</button>';
    hb.addEventListener('mouseenter', () => clearTimeout(hideT));
    hb.addEventListener('mouseleave', schedHide);
    hb.querySelector('.g').onclick = e => { e.preventDefault(); e.stopPropagation(); const t = hbTarget; hideHB(); if (t) openMedia(t); };
    hb.querySelector('.p').onclick = async e => {
      e.preventDefault(); e.stopPropagation(); const t = hbTarget; hideHB(); if (!t) return;
      try { await addSlideUrl(t.url); toast(`Added to slideshow (${slides.length})`, 'Open', openSlides); } catch (err) { toast('⚠ ' + err.message); }
    };
    root.appendChild(hb);
  }
  const hideHB = () => { if (hb) hb.style.display = 'none'; hbTarget = null; };
  const schedHide = () => { clearTimeout(hideT); hideT = setTimeout(hideHB, 350); };
  function showHB(m) {
    if (!hb || !hb.isConnected) buildHB();
    hbTarget = m; const r = m.el.getBoundingClientRect();
    hb.style.left = Math.min(Math.max(r.left, 0) + 6, innerWidth - 90) + 'px';
    hb.style.top = Math.min(Math.max(r.top, 0) + 6, innerHeight - 40) + 'px';
    hb.style.display = 'flex'; hb.querySelector('.p').style.display = m.type === 'image' ? '' : 'none';
  }
  function scan() {
    let m = null;
    for (const el of document.elementsFromPoint(mx, my)) { if (el === host) continue; m = resolveMedia(el, false); if (m) break; }
    if (m) { clearTimeout(hideT); showHB(m); } else schedHide();
  }
  document.addEventListener('mousemove', e => {
    if (!hoverOn || picking || current || (host && e.composedPath().includes(host))) return;
    mx = e.clientX; my = e.clientY;
    if (!raf) raf = requestAnimationFrame(() => { raf = 0; scan(); });
  }, { passive: true });
  document.addEventListener('scroll', () => { if (hb && !current) hideHB(); }, { passive: true, capture: true });

  /* ───────────────────────── element picker ───────────────────────── */
  function startPicker(cb, onCancel) {
    ensureHost(); hideHB(); picking = true;
    const hl = document.createElement('div'); hl.className = 'pkhl';
    const bn = document.createElement('div'); bn.className = 'pkb'; bn.textContent = 'Click a video or image · Esc to cancel';
    root.append(hl, bn);
    const pickAt = (x, y) => { for (const el of document.elementsFromPoint(x, y)) { if (el === host) continue; const m = resolveMedia(el, true); if (m) return m; } return null; };
    const stop = () => {
      picking = false; hl.remove(); bn.remove();
      ['mousemove', 'click', 'mousedown', 'mouseup', 'pointerdown', 'pointerup', 'keydown'].forEach(ev => window.removeEventListener(ev, handlers[ev], true));
    };
    const block = e => { e.preventDefault(); e.stopPropagation(); e.stopImmediatePropagation(); };
    const handlers = {
      mousemove(e) {
        const m = pickAt(e.clientX, e.clientY);
        if (!m) { hl.style.display = 'none'; return; }
        const r = m.el.getBoundingClientRect();
        Object.assign(hl.style, { display: 'block', left: r.left + 'px', top: r.top + 'px', width: r.width + 'px', height: r.height + 'px' });
      },
      click(e) { block(e); const m = pickAt(e.clientX, e.clientY); stop(); if (m) cb(m); else { toast('No video or image found there.'); onCancel && onCancel(); } },
      mousedown: block, mouseup: block, pointerdown: block, pointerup: block,
      keydown(e) { if (e.key === 'Escape') { block(e); stop(); onCancel && onCancel(); } },
    };
    Object.keys(handlers).forEach(ev => window.addEventListener(ev, handlers[ev], true));
  }

  /* ───────────────────────── init ───────────────────────── */
  ensureHost();
  if (window === window.top && typeof GM_registerMenuCommand === 'function') {
    GM_registerMenuCommand('Pick video / image → GIF  (Alt+Shift+G)', () => startPicker(openMedia));
    GM_registerMenuCommand('Images → GIF slideshow  (Alt+Shift+I)', openSlides);
    GM_registerMenuCommand('Toggle hover GIF button', () => {
      hoverOn = !hoverOn; try { GM_setValue('hover', hoverOn); } catch {}
      hideHB(); toast('Hover GIF button: ' + (hoverOn ? 'ON' : 'OFF'));
    });
  }
  window.addEventListener('keydown', e => {
    if (!e.altKey || !e.shiftKey || e.ctrlKey || e.metaKey) return;
    if (e.code === 'KeyG') { e.preventDefault(); startPicker(openMedia); }
    else if (e.code === 'KeyI') { e.preventDefault(); openSlides(); }
  }, true);
})();
