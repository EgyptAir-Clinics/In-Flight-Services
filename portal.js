(function () {
  'use strict';

  const LANGUAGE_KEY = 'egyptairPortal:language';
  const THEME_KEY = 'egyptairPortal:theme';

  /* ── Safe storage ────────────────────────────────────────────────────────
     Some phones (iOS Safari private mode, locked-down WebViews) throw when
     localStorage is touched. Fall back to memory so the page still works. */
  const mem = {};
  const store = {
    get(key) {
      if (key in mem) return mem[key];
      try { return window.localStorage.getItem(key); } catch (e) { return null; }
    },
    set(key, value) {
      mem[key] = value;
      try { window.localStorage.setItem(key, value); } catch (e) { /* memory only */ }
    }
  };

  /* ── Device detection ────────────────────────────────────────────────────
     Layout is driven by CSS media queries; these classes only switch on
     touch-specific niceties (no custom cursor, no hover lifts, bigger taps). */
  const MOBILE_UA = /Android|webOS|iPhone|iPad|iPod|BlackBerry|IEMobile|Opera Mini/i;
  const ua = navigator.userAgent || '';
  // iPadOS 13+ reports itself as a Mac; touch points give it away.
  const isIpadOs = navigator.platform === 'MacIntel' && navigator.maxTouchPoints > 1;
  const isMobile = MOBILE_UA.test(ua) || isIpadOs;
  const isTouch = isMobile || (window.matchMedia && window.matchMedia('(pointer: coarse)').matches);
  const root = document.documentElement;
  root.classList.add(isMobile ? 'is-mobile' : 'is-desktop');
  if (isTouch) root.classList.add('is-touch');

  /* ── Hashing + sealing ───────────────────────────────────────────────────
     sha256Hex: pure JS (works on plain http:// where crypto.subtle does not)
     and UTF-8 safe, so Arabic text hashes correctly.

     seal / unseal: SHA-256 used as a stream cipher (counter mode). Links and
     contact details are stored sealed in the HTML and only decoded in memory
     when needed, so they never appear as readable text in View Source or the
     Elements panel. This stops casual snooping; it is obfuscation, not a
     vault: the browser must be able to decode it, so a developer still can. */
  const K = new Uint32Array(64);
  const H0 = new Uint32Array(8);
  (function initConstants() {
    let n = 2, count = 0;
    while (count < 64) {
      let prime = true;
      for (let d = 2; d * d <= n; d++) { if (n % d === 0) { prime = false; break; } }
      if (prime) {
        if (count < 8) H0[count] = Math.floor((Math.pow(n, 0.5) % 1) * 4294967296);
        K[count] = Math.floor((Math.pow(n, 1 / 3) % 1) * 4294967296);
        count++;
      }
      n++;
    }
  }());

  function utf8Encode(str) {
    const s = unescape(encodeURIComponent(String(str)));
    const out = new Uint8Array(s.length);
    for (let i = 0; i < s.length; i++) out[i] = s.charCodeAt(i);
    return out;
  }

  function utf8Decode(bytes) {
    let s = '';
    for (let i = 0; i < bytes.length; i++) s += String.fromCharCode(bytes[i]);
    try { return decodeURIComponent(escape(s)); } catch (e) { return ''; }
  }

  function ror(x, n) { return (x >>> n) | (x << (32 - n)); }

  function sha256Bytes(input) {
    const data = typeof input === 'string' ? utf8Encode(input) : input;
    const len = data.length;
    const total = ((len + 9 + 63) >> 6) << 6;
    const buf = new Uint8Array(total);
    buf.set(data);
    buf[len] = 0x80;
    const bitsHi = Math.floor(len / 536870912);
    const bitsLo = (len << 3) >>> 0;
    buf[total - 8] = bitsHi >>> 24; buf[total - 7] = bitsHi >>> 16; buf[total - 6] = bitsHi >>> 8; buf[total - 5] = bitsHi;
    buf[total - 4] = bitsLo >>> 24; buf[total - 3] = bitsLo >>> 16; buf[total - 2] = bitsLo >>> 8; buf[total - 1] = bitsLo;

    const h = new Uint32Array(H0);
    const w = new Uint32Array(64);
    for (let off = 0; off < total; off += 64) {
      for (let i = 0; i < 16; i++) {
        const p = off + i * 4;
        w[i] = (buf[p] << 24) | (buf[p + 1] << 16) | (buf[p + 2] << 8) | buf[p + 3];
      }
      for (let i = 16; i < 64; i++) {
        const s0 = ror(w[i - 15], 7) ^ ror(w[i - 15], 18) ^ (w[i - 15] >>> 3);
        const s1 = ror(w[i - 2], 17) ^ ror(w[i - 2], 19) ^ (w[i - 2] >>> 10);
        w[i] = (w[i - 16] + s0 + w[i - 7] + s1) | 0;
      }
      let a = h[0], b = h[1], c = h[2], d = h[3], e = h[4], f = h[5], g = h[6], hh = h[7];
      for (let i = 0; i < 64; i++) {
        const t1 = (hh + (ror(e, 6) ^ ror(e, 11) ^ ror(e, 25)) + ((e & f) ^ (~e & g)) + K[i] + w[i]) | 0;
        const t2 = ((ror(a, 2) ^ ror(a, 13) ^ ror(a, 22)) + ((a & b) ^ (a & c) ^ (b & c))) | 0;
        hh = g; g = f; f = e; e = (d + t1) | 0; d = c; c = b; b = a; a = (t1 + t2) | 0;
      }
      h[0] += a; h[1] += b; h[2] += c; h[3] += d; h[4] += e; h[5] += f; h[6] += g; h[7] += hh;
    }
    const out = new Uint8Array(32);
    for (let i = 0; i < 8; i++) {
      out[i * 4] = h[i] >>> 24; out[i * 4 + 1] = h[i] >>> 16; out[i * 4 + 2] = h[i] >>> 8; out[i * 4 + 3] = h[i];
    }
    return out;
  }

  function toHex(bytes) {
    let s = '';
    for (let i = 0; i < bytes.length; i++) s += (bytes[i] < 16 ? '0' : '') + bytes[i].toString(16);
    return s;
  }

  function sha256Hex(value) { return toHex(sha256Bytes(String(value == null ? '' : value))); }

  // The salt lives here, the sealed blobs live in the page: neither alone is enough.
  const SALT = ['ea', 'clinics', '\u2708', 'v1'].join('\u00b7');

  function keystream(ctx, nonceHex, length) {
    const out = new Uint8Array(length);
    for (let i = 0, block = 0; i < length; block++) {
      const chunk = sha256Bytes(SALT + '|' + ctx + '|' + nonceHex + '|' + block);
      for (let j = 0; j < 32 && i < length; j++, i++) out[i] = chunk[j];
    }
    return out;
  }

  function tagFor(ctx, plain) { return sha256Bytes(SALT + '|' + ctx + '|tag|' + plain).slice(0, 4); }

  function seal(plain, ctx) {
    const nonce = new Uint8Array(8);
    if (window.crypto && window.crypto.getRandomValues) window.crypto.getRandomValues(nonce);
    else for (let i = 0; i < 8; i++) nonce[i] = Math.floor(Math.random() * 256);
    const body = utf8Encode(plain);
    const ks = keystream(ctx, toHex(nonce), body.length);
    const packed = new Uint8Array(12 + body.length);
    packed.set(nonce, 0);
    packed.set(tagFor(ctx, plain), 8);
    for (let i = 0; i < body.length; i++) packed[12 + i] = body[i] ^ ks[i];
    let bin = '';
    for (let i = 0; i < packed.length; i++) bin += String.fromCharCode(packed[i]);
    return btoa(bin);
  }

  function unseal(blob, ctx) {
    try {
      const bin = atob(String(blob));
      const bytes = new Uint8Array(bin.length);
      for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
      const nonce = bytes.slice(0, 8);
      const tag = bytes.slice(8, 12);
      const cipher = bytes.slice(12);
      const ks = keystream(ctx, toHex(nonce), cipher.length);
      const plainBytes = new Uint8Array(cipher.length);
      for (let i = 0; i < cipher.length; i++) plainBytes[i] = cipher[i] ^ ks[i];
      const plain = utf8Decode(plainBytes);
      return toHex(tagFor(ctx, plain)) === toHex(tag) ? plain : '';
    } catch (e) {
      return '';
    }
  }

  /* ── Language + theme ───────────────────────────────────────────────── */
  const prefersDark = window.matchMedia && window.matchMedia('(prefers-color-scheme: dark)').matches;
  const savedLanguage = store.get(LANGUAGE_KEY) || store.get('holidayPlanner:language') || 'en';
  const savedTheme = store.get(THEME_KEY) || (prefersDark ? 'dark' : 'light');

  function currentLanguage() { return store.get(LANGUAGE_KEY) === 'ar' ? 'ar' : 'en'; }

  function setLanguage(language) {
    const lang = language === 'ar' ? 'ar' : 'en';
    store.set(LANGUAGE_KEY, lang);
    store.set('holidayPlanner:language', lang);
    document.documentElement.lang = lang;
    document.documentElement.dir = lang === 'ar' ? 'rtl' : 'ltr';

    document.querySelectorAll('[data-en][data-ar]').forEach((element) => {
      const value = element.getAttribute(`data-${lang}`);
      if (element.matches('input, textarea')) {
        element.placeholder = value;
      } else {
        element.textContent = value;
      }
    });

    document.querySelectorAll('[data-en-placeholder][data-ar-placeholder]').forEach((element) => {
      element.placeholder = element.getAttribute(`data-${lang}-placeholder`) || '';
    });

    document.querySelectorAll('[data-en-label][data-ar-label]').forEach((element) => {
      element.setAttribute('aria-label', element.getAttribute(`data-${lang}-label`) || '');
    });

    document.querySelectorAll('[data-lang-option]').forEach((button) => {
      const active = button.dataset.langOption === lang;
      button.classList.toggle('active', active);
      button.setAttribute('aria-pressed', String(active));
    });

    window.dispatchEvent(new CustomEvent('portal-language-change', { detail: { language: lang } }));
  }

  function setTheme(theme) {
    const nextTheme = theme === 'dark' ? 'dark' : 'light';
    store.set(THEME_KEY, nextTheme);
    document.documentElement.dataset.theme = nextTheme;

    const meta = document.querySelector('meta[name="theme-color"]');
    if (meta) meta.setAttribute('content', nextTheme === 'dark' ? '#172234' : '#ffffff');

    const lang = currentLanguage();
    document.querySelectorAll('[data-theme-toggle]').forEach((button) => {
      const lightLabel = lang === 'ar' ? 'فاتح' : 'Light';
      const darkLabel = lang === 'ar' ? 'داكن' : 'Dark';
      button.textContent = nextTheme === 'dark' ? lightLabel : darkLabel;
    });
  }

  document.addEventListener('DOMContentLoaded', () => {
    document.querySelectorAll('[data-lang-option]').forEach((button) => {
      button.addEventListener('click', () => {
        setLanguage(button.dataset.langOption);
        setTheme(store.get(THEME_KEY) || 'light');
      });
    });

    document.querySelectorAll('[data-theme-toggle]').forEach((button) => {
      button.addEventListener('click', () => {
        setTheme((store.get(THEME_KEY) || 'light') === 'dark' ? 'light' : 'dark');
      });
    });

    setTheme(savedTheme);
    setLanguage(savedLanguage);
  });

  window.EgyptAirPortal = {
    get language() { return currentLanguage(); },
    get isMobile() { return isMobile; },
    get isTouch() { return isTouch; },
    setLanguage,
    setTheme,
    secure: Object.freeze({ sha256Hex, seal, unseal })
  };

  /* ── Toast helper ── */
  function ensureToastContainer() {
    let container = document.getElementById('portal-toast-container');
    if (!container) {
      container = document.createElement('div');
      container.id = 'portal-toast-container';
      container.className = 'toast-container';
      container.setAttribute('role', 'status');
      container.setAttribute('aria-live', 'polite');
      document.body.appendChild(container);
    }
    return container;
  }

  window.showToast = function (message, type = 'info') {
    const container = ensureToastContainer();
    const toast = document.createElement('div');
    toast.className = `toast toast--${type}`;
    toast.textContent = message;
    container.appendChild(toast);
    setTimeout(() => toast.remove(), 4000);
  };
}());
