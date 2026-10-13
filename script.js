(() => {
'use strict';
/* =========================================================================
   THE LOST CITY: PORT HARCOURT — third-person survival horror
   Self-contained WebGL engine. No libraries, no external assets: every
   model, light, sound and piece of music is generated at runtime.
   ========================================================================= */

/* ---------- utilities ---------- */
const $ = s => document.querySelector(s);
const $$ = s => Array.from(document.querySelectorAll(s));
const TAU = Math.PI * 2;
const clamp = (v, a, b) => v < a ? a : v > b ? b : v;
const lerp = (a, b, t) => a + (b - a) * t;
const rand = (a, b) => a + Math.random() * (b - a);
const randi = (a, b) => Math.floor(rand(a, b + 1));
const pick = arr => arr[(Math.random() * arr.length) | 0];
const hyp = Math.hypot;
const smooth = t => t * t * (3 - 2 * t);
const angDiff = (a, b) => { let d = (b - a) % TAU; if (d > Math.PI) d -= TAU; if (d < -Math.PI) d += TAU; return d; };
const esc = s => String(s).replace(/[&<>"']/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
const fmtTime = s => `${Math.floor(s / 60)}:${String(Math.floor(s % 60)).padStart(2, '0')}`;
function makeRng(seed) {
  let s = (seed >>> 0) || 1;
  const f = () => (s = (s * 16807) % 2147483647) / 2147483647;
  f.r = (a, b) => a + f() * (b - a);
  f.i = (a, b) => Math.floor(a + f() * (b - a + 1));
  f.pick = arr => arr[(f() * arr.length) | 0];
  return f;
}
function hex(h, k = 1) {
  const n = parseInt(h.slice(1), 16);
  return [((n >> 16) & 255) / 255 * k, ((n >> 8) & 255) / 255 * k, (n & 255) / 255 * k];
}
const mix3 = (a, b, t) => [lerp(a[0], b[0], t), lerp(a[1], b[1], t), lerp(a[2], b[2], t)];
const scale3 = (a, k) => [a[0] * k, a[1] * k, a[2] * k];

const store = {
  get(k, d) { try { const v = localStorage.getItem('lc3d.' + k); return v ? JSON.parse(v) : d; } catch (e) { return d; } },
  set(k, v) { try { localStorage.setItem('lc3d.' + k, JSON.stringify(v)); } catch (e) { /* storage blocked: progress lasts this session only */ } }
};

/* ---------- 4x4 matrices (column-major, WebGL order) ---------- */
const M4 = {
  create() { const m = new Float32Array(16); m[0] = m[5] = m[10] = m[15] = 1; return m; },
  persp(o, fovy, asp, n, f) {
    const t = 1 / Math.tan(fovy / 2); o.fill(0);
    o[0] = t / asp; o[5] = t; o[10] = (f + n) / (n - f); o[11] = -1; o[14] = 2 * f * n / (n - f); return o;
  },
  lookAt(o, ex, ey, ez, cx, cy, cz) {
    let zx = ex - cx, zy = ey - cy, zz = ez - cz; let l = Math.hypot(zx, zy, zz) || 1; zx /= l; zy /= l; zz /= l;
    let xx = zz, xy = 0, xz = -zx; l = Math.hypot(xx, xz) || 1; xx /= l; xz /= l; // up = (0,1,0)
    const yx = zy * xz - zz * xy, yy = zz * xx - zx * xz, yz = zx * xy - zy * xx;
    o[0] = xx; o[1] = yx; o[2] = zx; o[3] = 0;
    o[4] = xy; o[5] = yy; o[6] = zy; o[7] = 0;
    o[8] = xz; o[9] = yz; o[10] = zz; o[11] = 0;
    o[12] = -(xx * ex + xy * ey + xz * ez); o[13] = -(yx * ex + yy * ey + yz * ez); o[14] = -(zx * ex + zy * ey + zz * ez); o[15] = 1;
    return o;
  },
  mul(o, a, b) {
    const r = new Float32Array(16);
    for (let c = 0; c < 4; c++) for (let rr = 0; rr < 4; rr++) {
      r[c * 4 + rr] = a[rr] * b[c * 4] + a[4 + rr] * b[c * 4 + 1] + a[8 + rr] * b[c * 4 + 2] + a[12 + rr] * b[c * 4 + 3];
    }
    o.set(r); return o;
  },
  // translation * Ry * Rx * Rz * uniform scale
  trs(o, x, y, z, ry = 0, rx = 0, rz = 0, s = 1) {
    const cy = Math.cos(ry), sy = Math.sin(ry), cx = Math.cos(rx), sx = Math.sin(rx), cz = Math.cos(rz), sz = Math.sin(rz);
    // R = Ry*Rx*Rz (row-major math)
    const a00 = cy * cz + sy * sx * sz, a01 = -cy * sz + sy * sx * cz, a02 = sy * cx;
    const a10 = cx * sz, a11 = cx * cz, a12 = -sx;
    const a20 = -sy * cz + cy * sx * sz, a21 = sy * sz + cy * sx * cz, a22 = cy * cx;
    o[0] = a00 * s; o[1] = a10 * s; o[2] = a20 * s; o[3] = 0;
    o[4] = a01 * s; o[5] = a11 * s; o[6] = a21 * s; o[7] = 0;
    o[8] = a02 * s; o[9] = a12 * s; o[10] = a22 * s; o[11] = 0;
    o[12] = x; o[13] = y; o[14] = z; o[15] = 1;
    return o;
  },
  apply(m, x, y, z) { return [m[0] * x + m[4] * y + m[8] * z + m[12], m[1] * x + m[5] * y + m[9] * z + m[13], m[2] * x + m[6] * y + m[10] * z + m[14]]; },
  applyDir(m, x, y, z) { return [m[0] * x + m[4] * y + m[8] * z, m[1] * x + m[5] * y + m[9] * z, m[2] * x + m[6] * y + m[10] * z]; },
  project(pv, x, y, z) {
    const X = pv[0] * x + pv[4] * y + pv[8] * z + pv[12], Y = pv[1] * x + pv[5] * y + pv[9] * z + pv[13];
    const Wc = pv[3] * x + pv[7] * y + pv[11] * z + pv[15];
    return { x: X / Wc, y: Y / Wc, w: Wc };
  }
};

/* =========================================================================
   Renderer — forward WebGL with hemisphere ambient, moonlight, lightning,
   12 point lights, 2 spotlights (torch + headlights), wet specular, fog.
   ========================================================================= */
const MAXPL = 12;
const VS = `
attribute vec3 aP; attribute vec3 aN; attribute vec3 aC; attribute vec2 aE;
uniform mat4 uPV; uniform mat4 uM; uniform float uWarp; uniform float uTime; uniform float uWave;
varying vec3 vP; varying vec3 vN; varying vec3 vC; varying vec2 vE;
void main(){
  vec4 wp = uM * vec4(aP, 1.0);
  wp.y += uWave * (sin(wp.x*0.7 + uTime*1.3) + sin(wp.z*0.9 - uTime*1.1)) * 0.06;
  wp.x += uWarp * sin(wp.z*0.31 + uTime*1.7) * 0.35;
  wp.y += uWarp * sin(wp.x*0.27 + uTime*1.2) * 0.15;
  vP = wp.xyz; vN = (uM * vec4(aN, 0.0)).xyz; vC = aC; vE = aE;
  gl_Position = uPV * wp;
}`;
const FS = `
#ifdef GL_FRAGMENT_PRECISION_HIGH
precision highp float;
#else
precision mediump float;
#endif
varying vec3 vP; varying vec3 vN; varying vec3 vC; varying vec2 vE;
uniform vec3 uCam; uniform vec3 uSky; uniform vec3 uGnd; uniform vec3 uMoonD; uniform vec3 uMoonC;
uniform vec3 uPLp[${MAXPL}]; uniform vec3 uPLc[${MAXPL}]; uniform float uPLr[${MAXPL}]; uniform int uNPL;
uniform vec3 uSPp[2]; uniform vec3 uSPd[2]; uniform vec3 uSPc[2]; uniform vec2 uSPk[2];
uniform vec3 uFogC; uniform float uFogD; uniform vec3 uTint; uniform float uEmis; uniform float uAlpha; uniform float uFlash;
void main(){
  vec3 N = normalize(vN);
  vec3 V = uCam - vP; float dist = length(V); V /= max(dist, 0.001);
  if (dot(N, V) < 0.0) N = -N;
  vec3 base = vC * uTint;
  float shine = vE.y;
  vec3 lit = mix(uGnd, uSky, N.y * 0.5 + 0.5);
  lit += uMoonC * max(dot(N, uMoonD), 0.0);
  lit += uFlash * vec3(0.62, 0.7, 0.95) * (0.35 + 0.65 * max(N.y, 0.0));
  vec3 spec = vec3(0.0);
  for (int i = 0