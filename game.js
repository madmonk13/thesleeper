(() => {
'use strict';

// ---------- Config ----------
const ROWS = 10, COLS = 8, TAU = Math.PI * 2, PAD = 8;
// Carved stones. Each has its own silhouette and glyph so colour is never the only cue.
const STONES = [
  { shape: 'circle',   glyph: 'ring',     light: '#a9ecd6', fill: '#3e9c86', dark: '#103b33' }, // verdigris
  { shape: 'square',   glyph: 'spiral',   light: '#fff6e0', fill: '#cdbf9c', dark: '#5f5440' }, // bone
  { shape: 'star',     glyph: 'dots',     light: '#ffb8a6', fill: '#c4543f', dark: '#521810' }, // coral
  { shape: 'diamond',  glyph: 'crescent', light: '#c4aef0', fill: '#5d3f8f', dark: '#1c0f31' }, // obsidian
  { shape: 'hex',      glyph: 'eye',      light: '#d4f7a4', fill: '#7aa83e', dark: '#243f12' }, // jade
  { shape: 'triangle', glyph: 'tentacle', light: '#ffe6a8', fill: '#c9932f', dark: '#563809' }, // ichor
];
const NC = STONES.length;
const GLYPH_OFFSET = { triangle: .16, star: .06 };
const GLOW = { ley: '#3dffb0', elder: '#ffb84d', wisp: '#aaffd8', taint: '#b44dff', void: '#ff2a2a' };
const POINTS_PER_PIECE = 40;
const CLEANSE_BONUS = 100;
const SHOG_BONUS = 100;
const WITCH_STRIKE = 110; // ms from a witch-light firing to its bolt landing
const TAINT_PATIENCE = 2;
const STAR_THRESHOLDS = [1, 1.5, 2];
const DIRS = [[0, 1], [1, 0], [0, -1], [-1, 0]];

function levelConfig(n) {
  const goals = [{ type: 'score', target: 1500 + n * 1000 }];
  let taint = 0, shoggoth = 0;
  if (n % 3 === 0) {
    taint = Math.min(18, 4 + n);
  } else if (n >= 5 && n % 3 === 2) {
    // every third level from 5 (5, 8, 11…) a shoggoth engulfs part of the board
    shoggoth = Math.min(24, 6 + n);
  } else if (n >= 2) {
    const count = Math.min(25, 8 + Math.floor(n * 1.5));
    const first = (n * 2) % NC;
    goals.push({ type: 'collect', color: first, count });
    if (n >= 5) goals.push({ type: 'collect', color: (first + 3) % NC, count });
    if (n >= 7) taint = 4;
  }
  if (taint) goals.push({ type: 'cleanse' });
  if (shoggoth) goals.push({ type: 'free' });
  return { moves: Math.max(16, 22 - Math.floor(n / 2)), goals, taint, shoggoth };
}

// ---------- DOM ----------
const $ = id => document.getElementById(id);
const canvas = $('board'), ctx = canvas.getContext('2d'), wrap = $('boardWrap');
const bg = $('bg'), bctx = bg.getContext('2d');
const fg = $('fg'), fctx = fg.getContext('2d'); // eye layer, drawn over the board
const overlay = $('overlay');

// ---------- State ----------
let grid = [], taint = [], taintFill = [], shog = [], shogFill = [], level = 1, score = 0, movesLeft = 0, cfg = null, collected = [];
let state = 'menu', busy = false, selected = null, drag = null, hint = null;
let lastInput = 0, muted = false, cleansedThisMove = 0, idleTurns = 0;
let particles = [], fx = [], floats = [], banner = null, shake = null;
let dpr = 1, bgDpr = 1, boardW = 0, boardH = 0, cell = 0, bgW = 0, bgH = 0;
let fxDelay = 0; // delay (ms) applied to effects/sounds spawned while resolving a delayed hit
const dread = { shown: 0, target: 0.08 }; // 0 = sleeping, 1 = awake
let previewDread = false; // hold D to preview the fully-awake scene

try { level = Math.max(1, parseInt(localStorage.getItem('sleeper.level'), 10) || 1); } catch (e) {}

const key = (r, c) => r * COLS + c;
const inBounds = (r, c) => r >= 0 && r < ROWS && c >= 0 && c < COLS;
const randInt = n => Math.floor(Math.random() * n);
const randColor = () => randInt(NC);
const makePiece = (color, special, c, r) => ({ color, special: special || null, x: c, y: r, scale: 1 });
const hash = n => { const x = Math.sin(n * 127.1 + 311.7) * 43758.5453; return x - Math.floor(x); };

// ---------- Tweens ----------
const tweens = [];
const ease = {
  inQuad: t => t * t,
  inOut: t => t < .5 ? 2 * t * t : 1 - Math.pow(-2 * t + 2, 2) / 2,
  outBack: t => { const c = 1.70158; return 1 + (c + 1) * Math.pow(t - 1, 3) + c * Math.pow(t - 1, 2); },
  inBack: t => { const c = 1.70158; return (c + 1) * t * t * t - c * t * t; },
};
function tween(obj, to, dur, e = ease.inOut) {
  return new Promise(res => {
    const from = {};
    for (const k in to) from[k] = obj[k];
    tweens.push({ obj, from, to, dur, t: 0, e, res });
  });
}
function updateTweens(dt) {
  for (let i = tweens.length - 1; i >= 0; i--) {
    const tw = tweens[i];
    tw.t += dt;
    const p = Math.min(1, tw.t / tw.dur), v = tw.e(p);
    for (const k in tw.to) tw.obj[k] = tw.from[k] + (tw.to[k] - tw.from[k]) * v;
    if (p >= 1) { tweens.splice(i, 1); tw.res(); }
  }
}
const wait = ms => new Promise(r => setTimeout(r, ms));

// ---------- Audio ----------
let actx = null, master = null, noiseBuf = null, drone = null;
function audio() {
  if (!actx) {
    actx = new (window.AudioContext || window.webkitAudioContext)();
    // limiter on the master bus so stacked effects (thunder over matches) don't clip
    master = actx.createDynamicsCompressor();
    master.threshold.value = -14; master.knee.value = 10; master.ratio.value = 8;
    master.attack.value = 0.003; master.release.value = 0.25;
    master.connect(actx.destination);
  }
  return actx;
}
function beep(freq, dur = 0.12, type = 'sine', vol = 0.12, delay = 0) {
  if (muted) return;
  try {
    const a = audio(), t0 = a.currentTime + delay + fxDelay / 1000;
    const o = a.createOscillator(), g = a.createGain();
    o.type = type;
    o.frequency.setValueAtTime(freq, t0);
    g.gain.setValueAtTime(0.0001, t0);
    g.gain.exponentialRampToValueAtTime(vol, t0 + 0.01);
    g.gain.exponentialRampToValueAtTime(0.0001, t0 + dur);
    o.connect(g).connect(master);
    o.start(t0);
    o.stop(t0 + dur + 0.02);
  } catch (e) {}
}
// Sawtooth gliding from f0 to f1 through a lowpass: a "boom" whose harmonics survive small speakers.
function sweep(f0, f1, dur, vol, delay = 0, cutoff = 420) {
  if (muted) return;
  try {
    const a = audio(), t0 = a.currentTime + delay;
    const o = a.createOscillator(), f = a.createBiquadFilter(), g = a.createGain();
    o.type = 'sawtooth';
    o.frequency.setValueAtTime(f0, t0);
    o.frequency.exponentialRampToValueAtTime(f1, t0 + dur);
    f.type = 'lowpass'; f.frequency.value = cutoff;
    g.gain.setValueAtTime(0.0001, t0);
    g.gain.exponentialRampToValueAtTime(vol, t0 + 0.02);
    g.gain.exponentialRampToValueAtTime(0.0001, t0 + dur);
    o.connect(f).connect(g).connect(master);
    o.start(t0);
    o.stop(t0 + dur + 0.05);
  } catch (e) {}
}
function noise(dur = 0.2, freq = 800, vol = 0.08, q = 1, delay = 0, type = 'bandpass', attack = 0.005) {
  if (muted) return;
  try {
    const a = audio(), t0 = a.currentTime + delay + fxDelay / 1000;
    if (!noiseBuf) {
      noiseBuf = a.createBuffer(1, a.sampleRate, a.sampleRate);
      const d = noiseBuf.getChannelData(0);
      for (let i = 0; i < d.length; i++) d[i] = Math.random() * 2 - 1;
    }
    const s = a.createBufferSource(), f = a.createBiquadFilter(), g = a.createGain();
    s.buffer = noiseBuf;
    s.loop = true; // the buffer is 1s; long sounds (thunder rumble) would otherwise cut off
    f.type = type; f.frequency.value = freq; f.Q.value = q;
    g.gain.setValueAtTime(0.0001, t0);
    g.gain.exponentialRampToValueAtTime(vol, t0 + attack);
    g.gain.exponentialRampToValueAtTime(0.0001, t0 + dur);
    s.connect(f).connect(g).connect(master);
    s.start(t0, Math.random() * 0.9);
    s.stop(t0 + dur + 0.05);
  } catch (e) {}
}
// Low, beating drone that swells and opens up as dread rises.
function startDrone() {
  if (drone) return;
  try {
    const a = audio();
    const gain = a.createGain(), filter = a.createBiquadFilter();
    gain.gain.value = 0;
    filter.type = 'lowpass'; filter.frequency.value = 160;
    filter.connect(gain).connect(master);
    [[55, 'sawtooth'], [55.7, 'sawtooth'], [41.2, 'sine']].forEach(([f, type]) => {
      const o = a.createOscillator();
      o.type = type; o.frequency.value = f;
      o.connect(filter);
      o.start();
    });
    drone = { gain, filter };
  } catch (e) {}
}
let droneTick = 0;
function updateDrone(now) {
  if (!drone || now - droneTick < 250) return;
  droneTick = now;
  const t = actx.currentTime, d = dread.shown;
  drone.gain.gain.setTargetAtTime(muted ? 0 : 0.025 + 0.07 * d, t, 0.6);
  drone.filter.frequency.setTargetAtTime(140 + 600 * d * d, t, 0.6);
}
const SCALE = [0, 3, 5, 7, 10, 12, 15, 17];
function matchSound(cascade) {
  const base = 196 * Math.pow(2, SCALE[Math.min(cascade - 1, SCALE.length - 1)] / 12);
  beep(base, 0.7, 'sine', 0.1);
  beep(base * 1.003, 0.7, 'sine', 0.06);
  beep(base * 1.5, 0.6, 'triangle', 0.035, 0.05);
  noise(0.15, 650, 0.05, 0.9);
}

// ---------- Board logic ----------
function findRuns() {
  // stones engulfed by a shoggoth never match
  const at = (r, c) => shogAt(r, c) ? null : grid[r][c];
  const runs = [];
  for (let r = 0; r < ROWS; r++) {
    let c = 0;
    while (c < COLS) {
      const p = at(r, c);
      if (!p || p.color < 0) { c++; continue; }
      let e = c + 1;
      while (e < COLS && at(r, e) && at(r, e).color === p.color) e++;
      if (e - c >= 3) {
        const cells = [];
        for (let k = c; k < e; k++) cells.push([r, k]);
        runs.push({ dir: 'h', cells, color: p.color });
      }
      c = e;
    }
  }
  for (let c = 0; c < COLS; c++) {
    let r = 0;
    while (r < ROWS) {
      const p = at(r, c);
      if (!p || p.color < 0) { r++; continue; }
      let e = r + 1;
      while (e < ROWS && at(e, c) && at(e, c).color === p.color) e++;
      if (e - r >= 3) {
        const cells = [];
        for (let k = r; k < e; k++) cells.push([k, c]);
        runs.push({ dir: 'v', cells, color: p.color });
      }
      r = e;
    }
  }
  for (let r = 0; r < ROWS - 1; r++) {
    for (let c = 0; c < COLS - 1; c++) {
      const p = at(r, c);
      if (!p || p.color < 0) continue;
      const same = (rr, cc) => at(rr, cc) && at(rr, cc).color === p.color;
      if (same(r, c + 1) && same(r + 1, c) && same(r + 1, c + 1)) {
        runs.push({ dir: 'sq', cells: [[r, c], [r, c + 1], [r + 1, c], [r + 1, c + 1]], color: p.color });
      }
    }
  }
  return runs;
}

function groupRuns(runs) {
  const sets = runs.map(run => new Set(run.cells.map(([r, c]) => key(r, c))));
  const used = new Array(runs.length).fill(false), groups = [];
  for (let i = 0; i < runs.length; i++) {
    if (used[i]) continue;
    used[i] = true;
    const members = [i], cells = new Set(sets[i]);
    let changed = true;
    while (changed) {
      changed = false;
      for (let j = 0; j < runs.length; j++) {
        if (used[j] || runs[j].color !== runs[i].color) continue;
        if ([...sets[j]].some(k => cells.has(k))) {
          used[j] = true; members.push(j); changed = true;
          sets[j].forEach(k => cells.add(k));
        }
      }
    }
    groups.push({ runs: members.map(m => runs[m]), cells, color: runs[i].color });
  }
  return groups;
}

function analyzeGroup(g, swapCells) {
  const lines = g.runs.filter(r => r.dir !== 'sq');
  const maxLen = lines.length ? Math.max(...lines.map(r => r.cells.length)) : 0;
  const hasH = lines.some(r => r.dir === 'h'), hasV = lines.some(r => r.dir === 'v');
  let special = null;
  if (maxLen >= 5) special = 'rainbow';
  else if (hasH && hasV) special = 'bomb';
  else if (maxLen === 4) special = lines[0].dir === 'h' ? 'v' : 'h';
  else if (lines.length < g.runs.length) special = 'dart';
  if (!special) return null;

  let spot = null;
  if (swapCells) spot = swapCells.find(s => g.cells.has(key(s.r, s.c))) || null;
  if (!spot && special === 'bomb') {
    const hk = new Set(), vk = new Set();
    g.runs.forEach(run => run.cells.forEach(([r, c]) => (run.dir === 'h' ? hk : vk).add(key(r, c))));
    const k = [...hk].find(x => vk.has(x));
    if (k !== undefined) spot = { r: Math.floor(k / COLS), c: k % COLS };
  }
  if (!spot) {
    const longest = (lines.length ? lines : g.runs).reduce((a, b) => (b.cells.length > a.cells.length ? b : a));
    const [r, c] = longest.cells[Math.floor(longest.cells.length / 2)];
    spot = { r, c };
  }
  return { r: spot.r, c: spot.c, special, color: special === 'rainbow' ? -1 : g.color };
}

function mostCommonColor() {
  const counts = new Array(NC).fill(0);
  forEachPiece(p => { if (p.color >= 0) counts[p.color]++; });
  return counts.indexOf(Math.max(...counts));
}

function forEachPiece(fn) {
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      if (grid[r][c]) fn(grid[r][c], r, c);
}

// ---------- Taint ----------
const hasCleanseGoal = () => cfg.goals.some(g => g.type === 'cleanse');
const taintCount = () => taint.reduce((s, row) => s + row.filter(Boolean).length, 0);

function seedTaint(n) {
  taint = Array.from({ length: ROWS }, () => new Array(COLS).fill(false));
  taintFill = Array.from({ length: ROWS }, () => new Array(COLS).fill(0)); // rises to 1: cells flood in
  if (!n) return;
  const cells = [];
  const add = (r, c) => { if (inBounds(r, c) && !taint[r][c]) { taint[r][c] = true; cells.push([r, c]); } };
  for (let i = 0; i < Math.max(1, Math.round(n / 5)); i++) add(randInt(ROWS), randInt(COLS));
  for (let guard = 0; cells.length < n && guard < 1000; guard++) {
    const [r, c] = cells[randInt(cells.length)], [dr, dc] = DIRS[randInt(4)];
    add(r + dr, c + dc);
  }
  // stagger the level-start swell: negative fill = still waiting to appear
  cells.forEach(([r, c]) => { taintFill[r][c] = -.3 - Math.random() * .8; });
}

// ---------- Shoggoth ----------
// A shoggoth engulfs stones: they can't be swapped or matched, and stones fall past
// behind it. Clearing any stone beside it (or hitting it with a relic) drives it off that cell.
const shogAt = (r, c) => !!(shog[r] && shog[r][c]);
const shogCount = () => shog.reduce((s, row) => s + row.filter(Boolean).length, 0);

function seedShoggoth(n) {
  shog = Array.from({ length: ROWS }, () => new Array(COLS).fill(false));
  shogFill = Array.from({ length: ROWS }, () => new Array(COLS).fill(0));
  if (!n) return;
  const cells = [];
  const add = (r, c) => {
    if (inBounds(r, c) && !shog[r][c] && !(taint[r] && taint[r][c])) { shog[r][c] = true; cells.push([r, c]); }
  };
  // one or two masses, grown outward so it reads as a single creature
  for (let i = 0; i < (n > 12 ? 2 : 1); i++) add(2 + randInt(ROWS - 4), 1 + randInt(COLS - 2));
  for (let guard = 0; cells.length < n && guard < 2000; guard++) {
    const [r, c] = cells[randInt(cells.length)], [dr, dc] = DIRS[randInt(4)];
    add(r + dr, c + dc);
  }
  cells.forEach(([r, c]) => { shogFill[r][c] = -.3 - Math.random() * .8; });
}

let freedThisMove = 0;
function freeShoggoth(r, c) {
  if (!shog[r][c]) return;
  shog[r][c] = false;
  freedThisMove++;
  score += SHOG_BONUS;
  for (let i = 0; i < 10; i++) {
    const a = Math.random() * TAU, sp = .06 + Math.random() * .12;
    particles.push({
      x: c + .5, y: r + .5, vx: Math.cos(a) * sp, vy: Math.sin(a) * sp - .06,
      life: 0, max: 600, color: i % 3 ? '#3b3d40' : '#6d7a6a', size: .04 + Math.random() * .05, rot: 0, spin: 0, drop: true,
    });
  }
  // a wet recoil
  noise(.22, 320, .12, 2.2, 0, 'lowpass');
  sweep(240, 90, .22, .05, 0);
  updateHUD();
}

// A tendril reaches from an existing blob into a neighbouring cell, then a new blob
// swells there with a wet splat.
const TENDRIL_REACH = 520;
async function spreadTaint() {
  const options = [];
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++)
      if (taint[r][c])
        for (const [dr, dc] of DIRS)
          if (inBounds(r + dr, c + dc) && !taint[r + dr][c + dc] && !shogAt(r + dr, c + dc)) options.push([r, c, r + dr, c + dc]);
  if (!options.length) return;
  const [r0, c0, r, c] = options[randInt(options.length)];
  addFx({ type: 'tendril', r0, c0, r1: r, c1: c, dur: TENDRIL_REACH + 250 });
  noise(TENDRIL_REACH / 1000, 260, .06, 3);
  beep(80, TENDRIL_REACH / 1000, 'sawtooth', .03);
  await wait(TENDRIL_REACH);
  taint[r][c] = true;
  taintFill[r][c] = 0;
  addFx({ type: 'ring', r, c, size: .7, color: GLOW.taint, dur: 550 });
  for (let i = 0; i < 12; i++) {
    const a = Math.random() * TAU, s = .08 + Math.random() * .14;
    particles.push({
      x: c + .5, y: r + .5, vx: Math.cos(a) * s, vy: Math.sin(a) * s - .05,
      life: 0, max: 550, color: '#8f2fc4', size: .03 + Math.random() * .04, rot: 0, spin: 0, drop: true,
    });
  }
  addFloat('the taint spreads', c, r, '#d9a6ff', .3);
  startShake(220, 3);
  beep(150, .3, 'sine', .1);
  beep(70, .5, 'sawtooth', .05);
  noise(.3, 380, .12, 1.4, 0, 'lowpass');
  await wait(250);
}

// ---------- Effects of special pieces ----------
// Witch-lights seek taint first, then a shoggoth, then stones still needed for a goal, then anything.
// `prefer` keeps the choice stable between the preview and the real strike while it's still valid.
function pickDartTarget(taken, prefer) {
  const want = new Set(cfg.goals
    .filter(g => g.type === 'collect' && collected[g.color] < g.count)
    .map(g => g.color));
  const pool = [], goalPool = [], taintPool = [], shogPool = [];
  forEachPiece((q, r, c) => {
    const k = key(r, c);
    if (taken.has(k)) return;
    pool.push(k);
    if (taint[r][c]) taintPool.push(k);
    if (shogAt(r, c)) shogPool.push(k);
    else if (want.has(q.color)) goalPool.push(k);
  });
  const from = taintPool.length ? taintPool : shogPool.length ? shogPool : goalPool.length ? goalPool : pool;
  if (prefer != null && from.includes(prefer)) return prefer;
  return from.length ? from[randInt(from.length)] : null;
}

// The cells a witch-light at (r, c) would strike right now; remembered on the piece.
function dartAims(p, r, c, n = p.count || 1) {
  const taken = new Set([key(r, c)]), out = [], prev = p.aims || [];
  for (let i = 0; i < n; i++) {
    const t = pickDartTarget(taken, prev[i]);
    if (t == null) break;
    taken.add(t); out.push(t);
  }
  p.aims = out;
  return out;
}

// A bolt from the sky onto one cell, after `delay` ms.
function witchBolt(r, c, delay) {
  wait(delay).then(() => {
    const rect = canvas.getBoundingClientRect();
    const tx = rect.left + PAD + (c + .5) * cell, ty = rect.top + PAD + (r + .5) * cell;
    const main = boltPath(tx + (Math.random() - .5) * cell * 3, rect.top - cell * 2, tx, ty, cell * .35, 10);
    const [bx, by] = main[4];
    bolts.push({ main, branches: [boltPath(bx, by, bx + (Math.random() - .5) * cell * 2, by + cell, cell * .2, 4)], t: 0, dur: 360, width: .9 });
  });
}

function effectCells(r, c, p, cleared, queued, hitDelay) {
  const out = [];
  if (p.special === 'dart') {
    const taken = new Set([...cleared, ...queued, key(r, c)]);
    for (let i = 0; i < (p.count || 1); i++) {
      const t = pickDartTarget(taken, p.aims && p.aims[i]);
      if (t == null) break;
      taken.add(t);
      out.push(t);
      const tr = Math.floor(t / COLS), tc = t % COLS, target = grid[tr][tc];
      if (p.carry && target.special !== 'rainbow' && !shogAt(tr, tc)) target.special = p.carry;
      hitDelay.set(t, fxDelay + WITCH_STRIKE + i * 70);
      witchBolt(tr, tc, fxDelay + i * 70);
    }
    // a lighter flash and roll than a chain reaction's storm
    wait(fxDelay).then(() => {
      flash = { t: 0, dur: 300, strength: .35 };
      startShake(180, 3);
      thunder(.3);
      beep(1400, 0.2, 'sine', 0.03);
    });
  } else if (p.special === 'h') {
    for (let cc = 0; cc < COLS; cc++) out.push(key(r, cc));
    addFx({ type: 'beam', dir: 'h', r, c, dur: 420 });
    noise(0.4, 900, 0.06, 0.8);
    beep(98, 0.5, 'sine', 0.08);
  } else if (p.special === 'v') {
    for (let rr = 0; rr < ROWS; rr++) out.push(key(rr, c));
    addFx({ type: 'beam', dir: 'v', r, c, dur: 420 });
    noise(0.4, 900, 0.06, 0.8);
    beep(98, 0.5, 'sine', 0.08);
  } else if (p.special === 'bomb') {
    for (let dr = -1; dr <= 1; dr++)
      for (let dc = -1; dc <= 1; dc++)
        if (inBounds(r + dr, c + dc)) out.push(key(r + dr, c + dc));
    addFx({ type: 'ring', r, c, size: 1.6, dur: 480 });
    addFx({ type: 'sign', r, c, dur: 600 });
    beep(55, 0.7, 'sine', 0.15);
    noise(0.5, 160, 0.12, 0.6);
  } else if (p.special === 'rainbow') {
    const col = p.targetColor != null ? p.targetColor : mostCommonColor();
    forEachPiece((q, rr, cc) => {
      if (q.color === col) {
        out.push(key(rr, cc));
        addFx({ type: 'zap', r0: r, c0: c, r1: rr, c1: cc, dur: 460 });
      }
    });
    addFx({ type: 'ring', r, c, size: 1.2, color: GLOW.void, dur: 450 });
    beep(233, 0.9, 'sawtooth', 0.035);
    beep(247, 0.9, 'sawtooth', 0.035);
    beep(349, 0.9, 'sine', 0.05);
  }
  return out;
}

async function clearCells(keys, cascade = 1, creates = []) {
  // hitDelay: ms before a cell clears, so pieces hit by a witch-light wait for it to land.
  // freed: shoggoth cells driven off (key -> delay). The stone beneath stays.
  const queue = [...keys], cleared = new Set(), hitDelay = new Map(), freed = new Map();
  while (queue.length) {
    const k = queue.shift();
    if (cleared.has(k)) continue;
    const r = Math.floor(k / COLS), c = k % COLS, p = grid[r][c];
    if (!p) continue;
    if (shogAt(r, c)) { if (!freed.has(k)) freed.set(k, hitDelay.get(k) || 0); continue; }
    cleared.add(k);
    if (p.special) {
      fxDelay = hitDelay.get(k) || 0;
      for (const e of effectCells(r, c, p, cleared, queue, hitDelay)) {
        if (cleared.has(e)) continue;
        queue.push(e);
        if (!hitDelay.has(e)) hitDelay.set(e, fxDelay);
      }
      fxDelay = 0;
    }
  }
  // a shoggoth recoils from any stone cleared beside it
  for (const k of cleared) {
    const r = Math.floor(k / COLS), c = k % COLS, d = hitDelay.get(k) || 0;
    for (const [dr, dc] of DIRS) {
      if (!shogAt(r + dr, c + dc)) continue;
      const k2 = key(r + dr, c + dc);
      if (!freed.has(k2) || freed.get(k2) > d) freed.set(k2, d);
    }
  }
  if (!cleared.size && !freed.size) return;

  const pts = cleared.size * POINTS_PER_PIECE * cascade;
  score += pts;
  let sx = 0, sy = 0;
  const anims = [];
  for (const k of cleared) {
    const r = Math.floor(k / COLS), c = k % COLS, p = grid[r][c];
    sx += c; sy += r;
    if (p.color >= 0) collected[p.color]++;
    const pop = () => {
      spawnParticles(p);
      if (taint[r][c]) {
        taint[r][c] = false;
        cleansedThisMove++;
        score += CLEANSE_BONUS;
        addFx({ type: 'ring', r, c, size: .5, color: '#e8c8ff', dur: 450 });
        for (let i = 0; i < 8; i++) {
          particles.push({
            x: c + .2 + Math.random() * .6, y: r + .7, vx: (Math.random() - .5) * .12, vy: -.12 - Math.random() * .12,
            life: 0, max: 600, color: '#9b3fd0', size: .035 + Math.random() * .03, rot: 0, spin: 0, drop: true,
          });
        }
        beep(660, 0.4, 'sine', 0.04);
        updateHUD();
      }
      return tween(p, { scale: 0 }, 200, ease.inBack);
    };
    const d = hitDelay.get(k) || 0;
    anims.push(d ? wait(d).then(pop) : pop());
  }
  for (const [k, d] of freed) {
    const free = () => freeShoggoth(Math.floor(k / COLS), k % COLS);
    if (d) anims.push(wait(d).then(free)); else free();
  }
  if (cleared.size) {
    addFloat('+' + pts, sx / cleared.size, sy / cleared.size);
    matchSound(cascade);
  }
  updateHUD();
  await Promise.all(anims);
  for (const k of cleared) grid[Math.floor(k / COLS)][k % COLS] = null;

  const pops = [];
  for (const cr of creates) {
    if (grid[cr.r][cr.c]) continue;
    const np = makePiece(cr.color, cr.special, cr.c, cr.r);
    np.scale = 0;
    grid[cr.r][cr.c] = np;
    noteFormed(cr.special);
    pops.push(tween(np, { scale: 1 }, 260, ease.outBack));
  }
  if (pops.length) { beep(392, 0.6, 'sine', 0.06); beep(587, 0.6, 'sine', 0.04, 0.06); }
  await Promise.all(pops);
}

async function applyGravity() {
  const anims = [];
  for (let c = 0; c < COLS; c++) {
    // engulfed stones hold their place; the rest fall past behind the shoggoth
    const free = [];
    for (let r = ROWS - 1; r >= 0; r--) if (!shogAt(r, c)) free.push(r);
    let w = 0;
    for (const r of free) {
      if (!grid[r][c]) continue;
      const p = grid[r][c];
      grid[r][c] = null;
      grid[free[w++]][c] = p;
    }
    let spawn = 0;
    for (; w < free.length; w++) grid[free[w]][c] = makePiece(randColor(), null, c, -1 - spawn++);
    for (let r = 0; r < ROWS; r++) {
      const p = grid[r][c], dist = r - p.y;
      if (dist > 0) anims.push(tween(p, { y: r }, 140 + Math.sqrt(dist) * 90, ease.inQuad));
    }
  }
  await Promise.all(anims);
}

async function resolveBoard(swapCells = null) {
  let cascade = 0;
  for (;;) {
    const runs = findRuns();
    if (!runs.length) break;
    cascade++;
    const toClear = new Set(), creates = [];
    for (const g of groupRuns(runs)) {
      g.cells.forEach(k => toClear.add(k));
      const cr = analyzeGroup(g, swapCells);
      if (cr) creates.push(cr);
    }
    if (cascade >= 2) await strikeLightning(cascade, toClear);
    await clearCells(toClear, cascade, creates);
    await applyGravity();
    swapCells = null;
  }
}

function swapGrid(a, b) {
  const t = grid[a.r][a.c];
  grid[a.r][a.c] = grid[b.r][b.c];
  grid[b.r][b.c] = t;
}

const isCombo = (p, q) => p.special === 'rainbow' || q.special === 'rainbow' || (p.special && q.special);

function findMove() {
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      for (const [dr, dc] of [[0, 1], [1, 0]]) {
        const r2 = r + dr, c2 = c + dc;
        if (!inBounds(r2, c2)) continue;
        const a = grid[r][c], b = grid[r2][c2];
        if (!a || !b || shogAt(r, c) || shogAt(r2, c2)) continue;
        if (isCombo(a, b)) return [{ r, c }, { r: r2, c: c2 }];
        swapGrid({ r, c }, { r: r2, c: c2 });
        const ok = findRuns().length > 0;
        swapGrid({ r, c }, { r: r2, c: c2 });
        if (ok) return [{ r, c }, { r: r2, c: c2 }];
      }
    }
  }
  return null;
}

async function doCombo(p1, c1, p2, c2) {
  const s1 = p1.special, s2 = p2.special;
  const k1 = key(c1.r, c1.c), k2 = key(c2.r, c2.c);
  const R1 = s1 === 'rainbow', R2 = s2 === 'rainbow';

  if (R1 && R2) {
    p1.special = p2.special = null;
    showBanner('The Void opens!');
    startShake(900, 9);
    addFx({ type: 'ring', r: c1.r, c: c1.c, size: 9, color: GLOW.void, dur: 800 });
    beep(40, 1.4, 'sawtooth', 0.12);
    const all = [];
    forEachPiece((p, r, c) => all.push(key(r, c)));
    await clearCells(all, 2);
  } else if (R1 || R2) {
    const R = R1 ? p1 : p2, O = R1 ? p2 : p1, kR = R1 ? k1 : k2;
    const rc = R1 ? c1 : c2;
    if (O.special) {
      const pops = [];
      forEachPiece((p, r, c) => {
        if (p.color !== O.color) return;
        p.special = O.special === 'bomb' || O.special === 'dart' ? O.special : (Math.random() < .5 ? 'h' : 'v');
        p.scale = 1.4;
        pops.push(tween(p, { scale: 1 }, 300, ease.outBack));
        addFx({ type: 'zap', r0: rc.r, c0: rc.c, r1: r, c1: c, dur: 420 });
      });
      showBanner('The Trapezohedron shines!');
      beep(233, 0.8, 'sawtooth', 0.05);
      await Promise.all(pops);
      await wait(150);
    }
    R.targetColor = O.color;
    await clearCells([kR], 1);
  } else if (s1 === 'dart' || s2 === 'dart') {
    // Witch-light + witch-light launches three; witch-light + relic carries the relic to its target.
    const D = s1 === 'dart' ? p1 : p2, O = D === p1 ? p2 : p1;
    const kD = D === p1 ? k1 : k2, kO = D === p1 ? k2 : k1;
    if (O.special === 'dart') { D.count = 3; showBanner('A swarm of lights!'); }
    else D.carry = O.special;
    O.special = null;
    await clearCells([kD, kO], 1);
  } else {
    const striped = s => s === 'h' || s === 'v';
    p1.special = p2.special = null;
    const keys = new Set([k1, k2]);
    const { r, c } = c1;
    let rows = [], cols = [];
    if (striped(s1) && striped(s2)) {
      rows = [r]; cols = [c];
    } else if (s1 === 'bomb' && s2 === 'bomb') {
      for (let dr = -2; dr <= 2; dr++)
        for (let dc = -2; dc <= 2; dc++)
          if (inBounds(r + dr, c + dc)) keys.add(key(r + dr, c + dc));
      addFx({ type: 'ring', r, c, size: 3, dur: 600 });
      addFx({ type: 'sign', r, c, size: 2.2, dur: 800 });
      startShake(500, 6);
      beep(45, 0.9, 'sine', 0.16);
      noise(0.7, 120, 0.14, 0.6);
    } else {
      rows = [r - 1, r, r + 1].filter(x => x >= 0 && x < ROWS);
      cols = [c - 1, c, c + 1].filter(x => x >= 0 && x < COLS);
    }
    rows.forEach(rr => {
      for (let cc = 0; cc < COLS; cc++) keys.add(key(rr, cc));
      addFx({ type: 'beam', dir: 'h', r: rr, c, dur: 500 });
    });
    cols.forEach(cc => {
      for (let rr = 0; rr < ROWS; rr++) keys.add(key(rr, cc));
      addFx({ type: 'beam', dir: 'v', r, c: cc, dur: 500 });
    });
    if (rows.length || cols.length) { noise(0.6, 700, 0.08, 0.7); beep(73, 0.7, 'sine', 0.1); }
    await clearCells([...keys], 1);
  }
  await applyGravity();
}

async function trySwap(a, b) {
  if (busy || state !== 'playing') return;
  if (!inBounds(b.r, b.c) || Math.abs(a.r - b.r) + Math.abs(a.c - b.c) !== 1) return;
  if (shogAt(a.r, a.c) || shogAt(b.r, b.c)) return;
  busy = true; selected = null; hint = null; cleansedThisMove = 0; freedThisMove = 0;
  const pA = grid[a.r][a.c], pB = grid[b.r][b.c];
  swapGrid(a, b);
  noise(0.1, 500, 0.05, 1.2);
  beep(150, 0.08, 'triangle', 0.04);
  // A drag may have already carried the pieces most of the way; only animate what's left.
  const remaining = Math.abs(pA.x - b.c) + Math.abs(pA.y - b.r);
  const dur = Math.max(40, 160 * remaining);
  await Promise.all([
    tween(pA, { x: b.c, y: b.r }, dur),
    tween(pB, { x: a.c, y: a.r }, dur),
  ]);

  if (isCombo(pA, pB)) {
    movesLeft--; updateHUD();
    await doCombo(pA, b, pB, a);
    await resolveBoard();
  } else if (findRuns().length) {
    movesLeft--; updateHUD();
    await resolveBoard([b, a]);
  } else {
    beep(110, 0.18, 'triangle', 0.06);
    swapGrid(a, b);
    await Promise.all([
      tween(pA, { x: a.c, y: a.r }, 160),
      tween(pB, { x: b.c, y: b.r }, 160),
    ]);
    busy = false;
    lastInput = performance.now();
    return;
  }
  await showPendingIntros();
  await afterMove();
  busy = false;
  lastInput = performance.now();
}

function goalsMet() {
  return cfg.goals.every(g =>
    g.type === 'score' ? score >= g.target :
    g.type === 'collect' ? collected[g.color] >= g.count :
    g.type === 'free' ? shogCount() === 0 :
    taintCount() === 0);
}

async function afterMove() {
  updateHUD();
  if (goalsMet()) {
    state = 'finale';
    dread.target = 0;
    await finale();
    state = 'over';
    const stars = starCount();
    try { localStorage.setItem('sleeper.level', String(level + 1)); } catch (e) {}
    showOverlay('The seal holds', `Warding ${score.toLocaleString()}. In his house at R'lyeh, the Sleeper dreams on.`,
      stars, 'Descend deeper', () => startLevel(level + 1));
    [220, 262, 330, 440].forEach((f, i) => beep(f, 1.1, 'sine', 0.08, i * 0.16));
  } else if (movesLeft <= 0) {
    state = 'over';
    dread.target = 1;
    startShake(1400, 12);
    beep(41, 2.2, 'sawtooth', 0.12);
    beep(43.6, 2.2, 'sawtooth', 0.1);
    noise(1.8, 110, 0.16, 0.6);
    await breakBoard();
    const missing = cfg.goals.filter(g =>
      g.type === 'score' ? score < g.target :
      g.type === 'collect' ? collected[g.color] < g.count :
      g.type === 'free' ? shogCount() > 0 : taintCount() > 0);
    const text = missing.map(g =>
      g.type === 'score' ? `${(g.target - score).toLocaleString()} warding short` :
      g.type === 'collect' ? `${g.count - collected[g.color]} more stones needed` :
      g.type === 'free' ? `${shogCount()} stones still engulfed` :
      `${taintCount()} tainted tiles remain`).join(' · ');
    showOverlay('The Sleeper wakes', text, null, 'Try the rite again', () => startLevel(level), true);
  } else {
    // Taint creeps after TAINT_PATIENCE turns in a row without cleansing any of it.
    idleTurns = cleansedThisMove ? 0 : idleTurns + 1;
    if (hasCleanseGoal() && idleTurns >= TAINT_PATIENCE && taintCount() > 0) {
      idleTurns = 0;
      await spreadTaint();
      updateHUD();
    }
    if (!findMove()) await shuffleBoard();
  }
}

async function finale() {
  showBanner('The rite completes!');
  await wait(600);
  while (movesLeft > 0) {
    const cands = [];
    forEachPiece(p => { if (!p.special) cands.push(p); });
    if (!cands.length) break;
    const p = cands[randInt(cands.length)];
    p.special = Math.random() < .5 ? 'h' : 'v';
    p.scale = 1.5;
    tween(p, { scale: 1 }, 250, ease.outBack);
    movesLeft--;
    score += 100;
    updateHUD();
    beep(500 + Math.random() * 300, 0.2, 'sine', 0.04);
    await wait(110);
  }
  for (let guard = 0; guard < 25; guard++) {
    const keys = [];
    forEachPiece((p, r, c) => { if (p.special) keys.push(key(r, c)); });
    if (!keys.length) break;
    await clearCells(keys, 1);
    await applyGravity();
    await resolveBoard();
  }
  await wait(400);
}

async function shuffleBoard() {
  showBanner('The ruins shift…');
  noise(0.8, 300, 0.1, 0.6);
  // engulfed stones stay put; only the free cells are shuffled
  const pieces = [], spots = [];
  forEachPiece((p, r, c) => { if (!shogAt(r, c)) { pieces.push(p); spots.push([r, c]); } });
  for (let tries = 0; tries < 200; tries++) {
    for (let i = pieces.length - 1; i > 0; i--) {
      const j = randInt(i + 1);
      [pieces[i], pieces[j]] = [pieces[j], pieces[i]];
    }
    pieces.forEach((p, i) => { grid[spots[i][0]][spots[i][1]] = p; });
    if (!findRuns().length && findMove()) break;
    if (tries === 199) { generateBoard(); return; }
  }
  const anims = [];
  forEachPiece((p, r, c) => anims.push(tween(p, { x: c, y: r }, 500)));
  await Promise.all(anims);
}

function generateBoard() {
  for (let attempt = 0; attempt < 100; attempt++) {
    grid = [];
    for (let r = 0; r < ROWS; r++) {
      grid.push([]);
      for (let c = 0; c < COLS; c++) {
        let col;
        do {
          col = randColor();
        } while (
          (c >= 2 && grid[r][c - 1].color === col && grid[r][c - 2].color === col) ||
          (r >= 2 && grid[r - 1][c].color === col && grid[r - 2][c].color === col) ||
          (r >= 1 && c >= 1 && grid[r - 1][c - 1].color === col && grid[r - 1][c].color === col && grid[r][c - 1].color === col)
        );
        grid[r].push(makePiece(col, null, c, r));
      }
    }
    if (findMove()) return;
  }
}

// ---------- First-time introductions ----------
// Each relic is explained the first time the player forms one (after that move settles),
// and taint on the first level that has it. Seen intros persist across sessions.
const INTROS = {
  ley: {
    piece: [4, 'h'], title: 'Ley Line', iconSize: .34,
    text: 'Four stones in a row awaken a Ley Line. Match it or swap it, and it seals its whole row or column, the way its lines run.',
  },
  bomb: {
    piece: [0, 'bomb'], title: 'Elder Sign', iconSize: .3,
    text: 'An L or T shape forms an Elder Sign. Set it off and it banishes everything in the 3×3 around it.',
  },
  dart: {
    piece: [2, 'dart'], title: 'Witch-light',
    text: 'A 2×2 square kindles a Witch-light. Set it off and it calls lightning down on a tainted stone, or one you still need. Its flicker shows where.',
  },
  rainbow: {
    piece: [-1, 'rainbow'], title: 'Shining Trapezohedron',
    text: 'Five in a row calls forth the Shining Trapezohedron. Swap it with any stone to unmake every stone of that kind.',
  },
  shog: {
    piece: [3, null], title: 'The Shoggoth', shog: true,
    text: 'A shoggoth has engulfed these stones. They can\'t be moved or matched while it holds them. Clear a stone beside it, or strike it with a relic, to drive it off.',
  },
  taint: {
    piece: [1, null], title: 'The Taint', blob: true,
    text: 'A living taint clings to some stones. Clear a stone resting on it to purge it. Go two turns without purging any, and it spreads.',
  },
};
const COMBO_TIP = 'Swap two relics together for a stronger rite.';
const introKey = special => (special === 'h' || special === 'v' ? 'ley' : special);
let seenIntros = new Set(), pendingIntros = [], introOpen = null, introResolve = null;
try {
  const v = JSON.parse(localStorage.getItem('sleeper.seen'));
  if (Array.isArray(v)) seenIntros = new Set(v);
} catch (e) {}
function markSeen(k) {
  seenIntros.add(k);
  try { localStorage.setItem('sleeper.seen', JSON.stringify([...seenIntros])); } catch (e) {}
}

function noteFormed(special) {
  const k = introKey(special);
  if (state === 'playing' && !seenIntros.has(k) && !pendingIntros.includes(k)) pendingIntros.push(k);
}

async function showIntro(k) {
  const it = INTROS[k];
  markSeen(k);
  const tip = k !== 'taint' && !seenIntros.has('tip');
  if (tip) markSeen('tip');
  $('introTitle').textContent = it.title;
  $('introTitle').classList.toggle('taint', !!it.blob);
  $('introTitle').classList.toggle('shog', !!it.shog);
  $('introText').textContent = it.text;
  $('introTip').textContent = tip ? COMBO_TIP : '';
  introOpen = { blob: it.blob, shog: it.shog, iconSize: it.iconSize || .62, piece: makePiece(it.piece[0], it.piece[1], 0, 0) };
  $('intro').classList.remove('hidden');
  beep(330, 1, 'sine', .06); beep(494, 1, 'sine', .04, .12); beep(659, 1.2, 'sine', .03, .24);
  await new Promise(res => { introResolve = res; });
  $('intro').classList.add('hidden');
  introOpen = null;
  lastInput = performance.now();
}
$('introBtn').addEventListener('click', () => {
  if (!introResolve) return;
  const r = introResolve;
  introResolve = null;
  r();
});

async function showPendingIntros() {
  while (pendingIntros.length) await showIntro(pendingIntros.shift());
}

function drawIntroIcon(now) {
  if (!introOpen) return;
  const ic = $('introIcon'), s = ic.width, c = ic.getContext('2d');
  c.setTransform(1, 0, 0, 1, 0, 0);
  c.clearRect(0, 0, s, s);
  if (introOpen.blob) drawBlob(c, s / 2, s / 2, s * .36, now, 3);
  drawPiece(c, introOpen.piece, s / 2, s / 2, s * introOpen.iconSize, now, 1);
  if (introOpen.shog) drawShoggothIcon(c, s / 2, s / 2, s * .72, now);
}

// ---------- Level flow ----------
async function startLevel(n) {
  startDrone();
  level = n;
  cfg = levelConfig(n);
  score = 0;
  movesLeft = cfg.moves;
  collected = new Array(NC).fill(0);
  particles = []; fx = []; floats = []; banner = null; wreck = null; resetBoardSink();
  selected = null; hint = null; drag = null; idleTurns = 0; pendingIntros = [];
  seedTaint(cfg.taint);
  seedShoggoth(cfg.shoggoth);
  generateBoard();
  buildGoals();
  state = 'playing';
  updateHUD();
  hideOverlay();
  busy = true;
  const anims = [];
  forEachPiece((p, r, c) => {
    p.y = r - ROWS - 1;
    anims.push(wait((ROWS - r) * 30 + c * 15).then(() => tween(p, { y: r }, 450, ease.outBack)));
  });
  await Promise.all(anims);
  if (cfg.taint && !seenIntros.has('taint')) { await wait(700); await showIntro('taint'); }
  if (cfg.shoggoth && !seenIntros.has('shog')) { await wait(700); await showIntro('shog'); }
  busy = false;
  lastInput = performance.now();
}

function starCount() {
  const t = cfg.goals[0].target;
  return STAR_THRESHOLDS.filter(m => score >= t * m).length;
}

// ---------- HUD ----------
function iconCanvas(drawFn) {
  const ic = document.createElement('canvas');
  const s = 26 * (window.devicePixelRatio || 1);
  ic.width = ic.height = s;
  drawFn(ic.getContext('2d'), s);
  return ic;
}

function buildGoals() {
  const box = $('goals');
  box.innerHTML = '';
  cfg.goals.forEach((g, i) => {
    const el = document.createElement('div');
    el.className = 'goal';
    el.id = 'goal' + i;
    if (g.type === 'score') {
      el.innerHTML = `<span class="icon">✦</span><span>${g.target.toLocaleString()}</span>`;
    } else {
      el.appendChild(iconCanvas((ic, s) => g.type === 'collect'
        ? drawPiece(ic, makePiece(g.color, null, 0, 0), s / 2, s / 2, s * 1.15, 0, 1)
        : g.type === 'free' ? drawShoggothIcon(ic, s / 2, s / 2, s * .9, 0)
        : drawBlob(ic, s / 2, s / 2, s * .36, 0, 7)));
      const sp = document.createElement('span');
      sp.className = 'count';
      el.appendChild(sp);
    }
    box.appendChild(el);
  });
}

function updateHUD() {
  $('level').textContent = level;
  $('score').textContent = score.toLocaleString();
  $('moves').textContent = movesLeft;
  $('moves').classList.toggle('low', state === 'playing' && movesLeft <= 5);
  if (state === 'playing') dread.target = 1 - movesLeft / cfg.moves;
  const t = cfg.goals[0].target;
  $('barFill').style.width = Math.min(100, score / (t * 2) * 100) + '%';
  STAR_THRESHOLDS.forEach((m, i) => $('star' + (i + 1)).classList.toggle('on', score >= t * m));
  cfg.goals.forEach((g, i) => {
    const el = $('goal' + i);
    if (!el) return;
    if (g.type === 'score') {
      el.classList.toggle('done', score >= g.target);
    } else if (g.type === 'collect') {
      el.querySelector('.count').textContent = `${Math.min(collected[g.color], g.count)}/${g.count}`;
      el.classList.toggle('done', collected[g.color] >= g.count);
    } else {
      const n = g.type === 'free' ? shogCount() : taintCount();
      el.querySelector('.count').textContent = n ? `${n} left` : '';
      el.classList.toggle('done', n === 0);
    }
  });
}

let ovAction = null;
function showOverlay(title, text, stars, btn, action, doom = false) {
  $('ovTitle').textContent = title;
  $('ovTitle').classList.toggle('doom', doom);
  $('ovText').textContent = text;
  $('ovStars').innerHTML = stars == null ? '' :
    [0, 1, 2].map(i => `<span class="${i < stars ? 'on' : 'off'}">✦</span>`).join('');
  $('ovBtn').textContent = btn;
  ovAction = action;
  overlay.classList.remove('hidden');
}
function hideOverlay() { overlay.classList.add('hidden'); }
$('ovBtn').addEventListener('click', () => { if (ovAction) ovAction(); });

$('restartBtn').addEventListener('click', () => {
  if (state === 'playing' && !busy) startLevel(level);
});
$('muteBtn').addEventListener('click', () => {
  muted = !muted;
  $('muteBtn').textContent = muted ? '🔇 Muted' : '🔊 Sound';
  droneTick = 0;
});

// ---------- Debug menu ----------
// Toggle with the ` key, or open the page with ?debug for a button in the footer (for phones).
// Each entry becomes one row; add more here as testing needs grow.
const DEBUG_ITEMS = [
  { label: 'Go to seal', input: { type: 'number', min: 1, value: () => level },
    run: v => { const n = Math.max(1, Math.floor(+v) || 1); setDebug(false); startLevel(n); } },
  { label: 'Lose now', when: () => state === 'playing' && !busy,
    run: async () => { setDebug(false); busy = true; movesLeft = 0; await afterMove(); busy = false; } },
  // forgets which first-time relic and taint cards have been shown, so they all appear again
  { label: 'Reset alerts',
    run: (v, btn) => {
      seenIntros.clear(); try { localStorage.removeItem('sleeper.seen'); } catch (e) {}
      btn.textContent = 'Alerts reset ✓';
    } },
];
const debugEl = $('debug');
function buildDebug() {
  const list = $('debugItems');
  list.innerHTML = '';
  for (const it of DEBUG_ITEMS) {
    const row = document.createElement('div');
    row.className = 'row';
    let input = null;
    if (it.input) {
      input = document.createElement('input');
      input.type = it.input.type; if (it.input.min != null) input.min = it.input.min;
      input.value = it.input.value();
      input.addEventListener('keydown', e => { if (e.key === 'Enter') btn.click(); e.stopPropagation(); });
      row.appendChild(input);
    }
    const btn = document.createElement('button');
    btn.className = 'ghost';
    btn.textContent = it.label;
    btn.disabled = it.when ? !it.when() : false;
    btn.addEventListener('click', () => it.run(input && input.value, btn));
    row.appendChild(btn);
    list.appendChild(row);
  }
}
function setDebug(open) {
  if (open) buildDebug();
  debugEl.classList.toggle('hidden', !open);
}
window.addEventListener('keydown', e => { if (e.key === '`') setDebug(debugEl.classList.contains('hidden')); });
$('debugClose').addEventListener('click', () => setDebug(false));
if (window.location && /[?&]debug\b/.test(window.location.search)) {
  $('debugBtn').classList.remove('hidden');
  $('debugBtn').addEventListener('click', () => setDebug(true));
}

// ---------- Effects ----------
function addFx(f) { f.t = -fxDelay; fx.push(f); }
function addFloat(text, cx, cy, color = '#e4f5ee', size = .42) {
  floats.push({ text, x: cx, y: cy, t: 0, dur: 1000, color, size });
}
function showBanner(text) { banner = { text, t: 0, dur: 1300 }; }
function startShake(dur, mag) { shake = { t: 0, dur, mag }; }
function spawnParticles(p) {
  const color = p.color >= 0 ? STONES[p.color].fill : '#ff4040';
  for (let i = 0; i < 7; i++) {
    const a = Math.random() * TAU, s = 0.05 + Math.random() * 0.18;
    particles.push({
      x: p.x + .5, y: p.y + .5, vx: Math.cos(a) * s, vy: Math.sin(a) * s - 0.08,
      life: 0, max: 500 + Math.random() * 300, color, size: 0.04 + Math.random() * 0.06,
      rot: Math.random() * TAU, spin: (Math.random() - .5) * .02,
    });
  }
  for (let i = 0; i < 2; i++) {
    particles.push({
      x: p.x + .5, y: p.y + .5, vx: (Math.random() - .5) * .05, vy: -0.05 - Math.random() * .05,
      life: 0, max: 900, color: GLOW.wisp, size: 0.035, rot: 0, spin: 0, mote: true,
    });
  }
}

// ---------- The Sleeper breaks through (on a loss) ----------
// Three arms burst up from the deep, one after another, smash into the board and fling the
// nearby stones off screen, then drag the board down into the dark. Arms and flying stones
// live on the fg layer; the board itself sinks via a CSS transform.
const WRECK_ARMS = [
  { bx: .3, by: 1.05, hit: [.36, .64], at: 250, bend: .5, w: .075 },
  { bx: 1.05, by: .38, hit: [.74, .3], at: 470, bend: -.6, w: .06 },
  { bx: -.05, by: .72, hit: [.2, .4], at: 650, bend: .55, w: .06 },
];
const WRECK_REACH = 480, WRECK_SINK = [1050, 2300], WRECK_DUR = 2500;
let wreck = null;

function breakBoard() {
  const br = canvas.getBoundingClientRect();
  // flung stones keep to where the board started, not where it sinks to
  wreck = { t: 0, struck: WRECK_ARMS.map(() => false), ox: br.left, oy: br.top };
  return wait(WRECK_DUR);
}

function strikeArm(i) {
  const [hx, hy] = WRECK_ARMS[i].hit;
  startShake(600, 18 - i * 3);
  noise(.5, 600, .3, .7, 0, 'bandpass', .002);
  noise(.9, 180, .25, .5, .03, 'lowpass', .002);
  beep(55 - i * 6, .7, 'sawtooth', .1);
  // stones near this impact are flung away from it
  const hc = (hx * boardW - PAD) / cell - .5, hr = (hy * boardH - PAD) / cell - .5;
  forEachPiece(p => {
    if (p.fly || shogAt(Math.round(p.y), Math.round(p.x))) return; // engulfed stones sink with the board
    const dx = p.x - hc, dy = p.y - hr, d = Math.hypot(dx, dy);
    if (d > 3.2) return; // the rest go down with the board
    const k = .012 + Math.random() * .012 + .02 / (d + 1);
    p.fly = { vx: dx / (d || 1) * k, vy: dy / (d || 1) * k - .018, spin: (Math.random() - .5) * .02, rot: 0 };
  });
}

function updateWreck(dt) {
  if (!wreck) return;
  wreck.t += dt;
  WRECK_ARMS.forEach((A, i) => {
    if (!wreck.struck[i] && wreck.t >= A.at + WRECK_REACH * .8) { wreck.struck[i] = true; strikeArm(i); }
  });
  forEachPiece(p => {
    if (!p.fly) return;
    const f = p.fly;
    f.vy += .00006 * dt;
    p.x += f.vx * dt; p.y += f.vy * dt; f.rot += f.spin * dt;
  });
  const k = Math.max(0, Math.min(1, (wreck.t - WRECK_SINK[0]) / (WRECK_SINK[1] - WRECK_SINK[0])));
  if (k > 0) {
    const e = ease.inQuad(k);
    canvas.style.transform = `translateY(${e * boardH * .35}px) scale(${1 - e * .88}) rotate(${e * 9}deg)`;
    canvas.style.filter = `drop-shadow(0 12px 30px rgba(0,0,0,.7)) brightness(${1 - e * .8})`;
    canvas.style.opacity = String(1 - ease.inQuad(Math.max(0, k - .3) / .7));
  }
}

function resetBoardSink() {
  canvas.style.transform = canvas.style.filter = canvas.style.opacity = '';
}

function drawWreckFg(now) {
  if (!wreck) return;
  const br = canvas.getBoundingClientRect(), W = bgW, H = bgH;
  forEachPiece(p => {
    if (!p.fly) return;
    const x = wreck.ox + PAD + (p.x + .5) * cell, y = wreck.oy + PAD + (p.y + .5) * cell;
    if (y > H + cell || x < -cell || x > W + cell) return;
    fctx.save();
    fctx.translate(x, y); fctx.rotate(p.fly.rot);
    drawPiece(fctx, p, 0, 0, cell, now, 1);
    fctx.restore();
  });
  WRECK_ARMS.forEach(A => {
    const k = (wreck.t - A.at) / WRECK_REACH;
    if (k <= 0) return;
    const sx = A.bx * W, sy = A.by * H;
    const hx = br.left + A.hit[0] * br.width, hy = br.top + A.hit[1] * br.height;
    const dist = Math.hypot(hx - sx, hy - sy);
    const T = { bx: A.bx, by: A.by, ang: Math.atan2(hy - sy, hx - sx) - A.bend / 3, bend: A.bend,
      len: dist * 1.12 / (Math.hypot(W, H) * .5), w: A.w, at: 0, phase: A.at };
    drawTentacle(fctx, W, H, T, Math.min(1, k) * TENTACLE_GROW, now);
  });
}

// ---------- Chain reactions: lightning & thunder ----------
// Bolts are stored in screen coordinates so they can run from the top of the screen
// (background canvas) down into the board (board canvas).
let bolts = [], flash = null;

function boltPath(x0, y0, x1, y1, jitter, segments) {
  const pts = [[x0, y0]];
  const nx = -(y1 - y0), ny = x1 - x0, len = Math.hypot(nx, ny) || 1;
  for (let i = 1; i < segments; i++) {
    const t = i / segments, off = (Math.random() - .5) * 2 * jitter * (1 - t * .6);
    pts.push([x0 + (x1 - x0) * t + nx / len * off, y0 + (y1 - y0) * t + ny / len * off]);
  }
  pts.push([x1, y1]);
  return pts;
}

async function strikeLightning(cascade, cells) {
  const power = Math.min(1, .45 + .15 * (cascade - 2));
  const rect = canvas.getBoundingClientRect();
  const targets = [...cells].sort(() => Math.random() - .5).slice(0, Math.min(cascade - 1, 4));
  for (const k of targets) {
    const r = Math.floor(k / COLS), c = k % COLS;
    const tx = rect.left + PAD + (c + .5) * cell, ty = rect.top + PAD + (r + .5) * cell;
    const sx = tx + (Math.random() - .5) * bgW * .3;
    const main = boltPath(sx, -10, tx, ty, cell * .45, 14 + Math.floor(ty / 60));
    const branches = [];
    for (let i = 0; i < 2 + Math.floor(power * 2); i++) {
      const [bx, by] = main[2 + randInt(main.length - 5)];
      const ex = bx + (Math.random() - .5) * cell * 3, ey = by + cell * (1 + Math.random() * 1.5);
      branches.push(boltPath(bx, by, ex, ey, cell * .25, 5));
    }
    bolts.push({ main, branches, t: 0, dur: 420 + power * 200, width: 1 + power });
  }
  flash = { t: 0, dur: 380 + power * 250, strength: .5 + .5 * power };
  startShake(220 + cascade * 90, 3 + cascade * 2);
  thunder(power);
  await wait(90);
}

// Built mostly from 150 Hz–5 kHz content so it's audible on laptop and phone speakers;
// the sub-bass layer is a bonus for headphones.
function thunder(power) {
  // crack: bright broadband snap
  noise(0.09, 2400, 0.5 * power, 0.35);
  noise(0.2, 5000, 0.25 * power, 0.5, 0.01, 'highpass');
  // crackle: a scatter of irregular snaps right after the strike
  for (let i = 0; i < 6 + power * 8; i++) {
    noise(0.03 + Math.random() * .07, 500 + Math.random() * 1600, (.15 + Math.random() * .15) * power, 1.2, .04 + Math.random() * .55);
  }
  // rumble: overlapping waves that swell in and roll away
  for (let i = 0; i < 3; i++) {
    noise(1.3 + power * .9, 260 + i * 110, (.45 - i * .08) * power, .9, .08 + i * .4, 'lowpass', .12 + i * .05);
  }
  // boom: falling sawtooth whose harmonics carry the low end on small speakers
  sweep(120, 40, 1.2 + power * .6, .3 * power, .02);
  beep(42, 1.6 + power, 'sine', .15 * power, .03);
}

function drawBolts(g, ox, oy) {
  for (const b of bolts) {
    const p = b.t / b.dur;
    // flicker: on, off, on, then fade
    const a = p < .14 ? 1 : p < .24 ? .15 : p < .4 ? .9 : Math.max(0, 1 - (p - .4) / .6);
    if (a <= 0) continue;
    const stroke = (pts, w) => {
      g.beginPath();
      pts.forEach(([x, y], i) => i ? g.lineTo(x - ox, y - oy) : g.moveTo(x - ox, y - oy));
      g.lineWidth = w; g.stroke();
    };
    g.save();
    g.lineJoin = 'round'; g.lineCap = 'round';
    g.globalAlpha = a * .5;
    g.strokeStyle = '#a99cff'; g.shadowColor = '#b9a8ff'; g.shadowBlur = 28;
    stroke(b.main, 7 * b.width);
    b.branches.forEach(br => stroke(br, 3.5 * b.width));
    g.globalAlpha = a;
    g.shadowBlur = 10; g.strokeStyle = '#f4f0ff';
    stroke(b.main, 2.2 * b.width);
    b.branches.forEach(br => stroke(br, 1.2 * b.width));
    g.restore();
  }
}

function flashAlpha() {
  if (!flash) return 0;
  const p = flash.t / flash.dur;
  const k = p < .1 ? 1 : p < .2 ? .35 : p < .3 ? .85 : 1 - (p - .3) / .7;
  return Math.max(0, k) * flash.strength;
}

// ---------- Rendering: shoggoth ----------
// One dark, oily mass over the stones it engulfs. Eyes surface, look about, blink and sink;
// mouths open and gnash; the whole body heaves.
const SHOG_BODY = '#2b2d30', SHOG_EDGE = '#111214';
const shogLevel = (r, c) => inBounds(r, c) && shogFill[r] ? Math.max(0, Math.min(1, shogFill[r][c])) : 0;

function shogLumpPath(c, cx, cy, R, now, seed) {
  const N = 20;
  for (let i = 0; i <= N; i++) {
    const a = i / N * TAU;
    const k = 1 + .08 * Math.sin(4 * a + seed + now / 520) + .05 * Math.sin(7 * a - seed * 2 + now / 330);
    const x = cx + Math.cos(a) * R * k, y = cy + Math.sin(a) * R * k;
    i ? c.lineTo(x, y) : c.moveTo(x, y);
  }
  c.closePath();
}

function drawShoggothFeatures(c, cx, cy, size, l, now, seed) {
  if (l < .4) return;
  const a0 = Math.min(1, (l - .4) / .4);
  c.save();
  // eyes: each surfaces somewhere new every cycle
  for (let i = 0; i < 3; i++) {
    const P = 2400 + hash(seed * 3 + i) * 2200, t = now + hash(seed + i * 17) * P;
    const n = Math.floor(t / P), ph = (t % P) / P;
    let open = Math.min(1, Math.sin(ph * Math.PI) * 2.4);
    if (ph > .42 && ph < .48) open *= .1; // blink
    if (open <= .05) continue;
    const h = hash(seed * 7 + i * 31 + n * 13), h2 = hash(seed * 11 + i * 7 + n * 29);
    const x = cx + (h - .5) * size * .62, y = cy + (h2 - .5) * size * .62;
    const e = size * (.07 + .07 * hash(seed + i + n * 3));
    const look = now / 700 + seed + i, lx = Math.cos(look) * e * .3, ly = Math.sin(look * 1.3) * e * .2;
    c.globalAlpha = a0;
    c.beginPath(); c.ellipse(x, y, e, e * open, 0, 0, TAU);
    c.fillStyle = '#cdc8b0'; c.fill();
    c.beginPath(); c.ellipse(x + lx, y + ly * open, e * .55, e * .55 * open, 0, 0, TAU);
    c.fillStyle = '#9dbb34'; c.fill();
    c.beginPath(); c.ellipse(x + lx, y + ly * open, e * .22, e * .5 * open, 0, 0, TAU);
    c.fillStyle = '#050505'; c.fill();
  }
  // mouths: open and close, teeth along the upper lip
  for (let i = 0; i < 2; i++) {
    const P = 3000 + hash(seed * 5 + i) * 2500, t = now + hash(seed * 2 + i * 23) * P;
    const n = Math.floor(t / P), ph = (t % P) / P, life = Math.min(1, Math.sin(ph * Math.PI) * 2);
    if (life <= .05) continue;
    const h = hash(seed * 13 + i * 41 + n * 7), h2 = hash(seed * 17 + i * 3 + n * 19);
    const x = cx + (h - .5) * size * .55, y = cy + (h2 - .5) * size * .55;
    const w = size * (.11 + .06 * hash(seed + i * 5 + n)), gape = w * .55 * life * (.35 + .65 * Math.abs(Math.sin(now / 170 + seed + i * 2)));
    c.globalAlpha = a0;
    c.beginPath(); c.ellipse(x, y, w, gape, 0, 0, TAU);
    c.fillStyle = '#060607'; c.fill();
    c.strokeStyle = '#4a4d51'; c.lineWidth = Math.max(1, size * .02); c.stroke();
    if (gape > w * .15) {
      c.beginPath();
      for (let k = -2; k <= 2; k++) {
        const tx = x + k * w * .34, ty = y - gape * Math.sqrt(Math.max(0, 1 - (k * .34) ** 2)) * .9;
        c.moveTo(tx - w * .08, ty); c.lineTo(tx, ty + gape * .45); c.lineTo(tx + w * .08, ty);
      }
      c.fillStyle = '#d6d0bd'; c.fill();
    }
  }
  c.restore();
}

function drawShoggothLayer(now) {
  const centre = (r, c) => [PAD + (c + .5) * cell, PAD + (r + .5) * cell];
  const cells = [];
  ctx.save();
  // bridges and lumps share one path so the mass has no seams
  ctx.beginPath();
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      const l = shogLevel(r, c);
      if (l <= .03) continue;
      const [x, y] = centre(r, c), k = key(r, c);
      cells.push([x, y, l, k]);
      for (const [dr, dc] of [[0, 1], [1, 0]]) {
        const l2 = Math.min(l, shogLevel(r + dr, c + dc));
        if (l2 <= .03) continue;
        const w = cell * .88 * l2 * (1 + .05 * Math.sin(now / 400 + k));
        if (dc) ctx.rect(x, y - w / 2, cell, w); else ctx.rect(x - w / 2, y, w, cell);
      }
      shogLumpPath(ctx, x, y, cell * .6 * ease.outBack(l), now, k * 1.7);
    }
  }
  if (!cells.length) { ctx.restore(); return; }
  ctx.lineJoin = 'round';
  ctx.strokeStyle = SHOG_EDGE; ctx.lineWidth = Math.max(2, cell * .06); ctx.stroke();
  ctx.globalAlpha = .95; ctx.fillStyle = SHOG_BODY; ctx.fill();
  // an oily sheen that slides over each lump
  for (const [x, y, l, k] of cells) {
    const sx = x + Math.sin(now / 1100 + k) * cell * .15 - cell * .12, sy = y - cell * .16;
    const g = ctx.createRadialGradient(sx, sy, 0, sx, sy, cell * .35);
    g.addColorStop(0, 'rgba(150,160,165,.22)'); g.addColorStop(1, 'rgba(150,160,165,0)');
    ctx.globalAlpha = l; ctx.fillStyle = g;
    ctx.fillRect(sx - cell * .35, sy - cell * .35, cell * .7, cell * .7);
  }
  ctx.globalAlpha = 1;
  for (const [x, y, l, k] of cells) drawShoggothFeatures(ctx, x, y, cell, l, now, k + 1);
  ctx.restore();
}

// A single lump, for the goal counter and the intro card.
function drawShoggothIcon(c, cx, cy, size, now) {
  c.save();
  c.beginPath(); shogLumpPath(c, cx, cy, size * .5, now, 2);
  c.strokeStyle = SHOG_EDGE; c.lineWidth = Math.max(1.5, size * .05); c.stroke();
  c.fillStyle = SHOG_BODY; c.fill();
  drawShoggothFeatures(c, cx, cy, size * .9, 1, now || 1800, 5);
  c.restore();
}

// ---------- Rendering: stones ----------
function roundRectPath(c, x, y, w, h, r) {
  c.moveTo(x + r, y);
  c.arcTo(x + w, y, x + w, y + h, r);
  c.arcTo(x + w, y + h, x, y + h, r);
  c.arcTo(x, y + h, x, y, r);
  c.arcTo(x, y, x + w, y, r);
  c.closePath();
}

function shapePath(c, shape, cx, cy, r) {
  c.beginPath();
  switch (shape) {
    case 'circle': c.arc(cx, cy, r * 0.9, 0, TAU); break;
    case 'square': roundRectPath(c, cx - r * .8, cy - r * .8, r * 1.6, r * 1.6, r * .22); break;
    case 'star':
      for (let i = 0; i < 10; i++) {
        const a = -Math.PI / 2 + i * Math.PI / 5, rad = i % 2 ? r * .52 : r * 1.02;
        const px = cx + Math.cos(a) * rad, py = cy + Math.sin(a) * rad + r * .06;
        i ? c.lineTo(px, py) : c.moveTo(px, py);
      }
      c.closePath();
      break;
    case 'diamond':
      c.moveTo(cx, cy - r); c.lineTo(cx + r * .78, cy); c.lineTo(cx, cy + r); c.lineTo(cx - r * .78, cy);
      c.closePath();
      break;
    case 'hex':
      for (let i = 0; i < 6; i++) {
        const a = i * Math.PI / 3, px = cx + Math.cos(a) * r * .92, py = cy + Math.sin(a) * r * .92;
        i ? c.lineTo(px, py) : c.moveTo(px, py);
      }
      c.closePath();
      break;
    case 'triangle':
      c.moveTo(cx, cy - r * .92); c.lineTo(cx + r * .95, cy + r * .72); c.lineTo(cx - r * .95, cy + r * .72);
      c.closePath();
      break;
  }
}

function glyphPath(c, glyph, cx, cy, r) {
  c.beginPath();
  switch (glyph) {
    case 'ring':
      c.arc(cx, cy, r * .38, 0, TAU);
      c.moveTo(cx + r * .1, cy); c.arc(cx, cy, r * .1, 0, TAU);
      for (let i = 0; i < 4; i++) {
        const a = i * Math.PI / 2 + Math.PI / 4;
        c.moveTo(cx + Math.cos(a) * r * .38, cy + Math.sin(a) * r * .38);
        c.lineTo(cx + Math.cos(a) * r * .56, cy + Math.sin(a) * r * .56);
      }
      break;
    case 'spiral':
      for (let i = 0; i <= 40; i++) {
        const a = i * .42, rad = r * .04 + i * r * .011;
        const x = cx + Math.cos(a) * rad, y = cy + Math.sin(a) * rad;
        i ? c.lineTo(x, y) : c.moveTo(x, y);
      }
      break;
    case 'dots':
      c.arc(cx, cy, r * .14, 0, TAU);
      for (let i = 0; i < 5; i++) {
        const a = -Math.PI / 2 + i * TAU / 5, x = cx + Math.cos(a) * r * .5, y = cy + Math.sin(a) * r * .5;
        c.moveTo(x + r * .05, y); c.arc(x, y, r * .05, 0, TAU);
      }
      break;
    case 'crescent':
      c.arc(cx, cy, r * .36, Math.PI * .3, Math.PI * 1.7);
      c.arc(cx + r * .16, cy, r * .27, Math.PI * 1.62, Math.PI * .38, true);
      c.closePath();
      break;
    case 'eye':
      c.moveTo(cx - r * .48, cy);
      c.quadraticCurveTo(cx, cy - r * .42, cx + r * .48, cy);
      c.quadraticCurveTo(cx, cy + r * .42, cx - r * .48, cy);
      c.moveTo(cx + r * .06, cy - r * .14); c.lineTo(cx + r * .06, cy + r * .14);
      c.moveTo(cx - r * .06, cy - r * .14); c.lineTo(cx - r * .06, cy + r * .14);
      break;
    case 'tentacle':
      c.moveTo(cx - r * .12, cy + r * .34);
      c.bezierCurveTo(cx + r * .38, cy + r * .12, cx - r * .38, cy - r * .1, cx + r * .04, cy - r * .3);
      c.arc(cx + r * .12, cy - r * .26, r * .08, Math.PI * 1.1, Math.PI * 2.7);
      break;
  }
}

// Carved look: a faint light edge below, then the dark (or glowing) cut.
function drawGlyph(c, glyph, cx, cy, r, color, glow) {
  c.save();
  c.lineCap = 'round'; c.lineJoin = 'round'; c.lineWidth = Math.max(1, r * .09);
  glyphPath(c, glyph, cx, cy + r * .045, r);
  c.strokeStyle = 'rgba(255,255,255,.22)'; c.stroke();
  glyphPath(c, glyph, cx, cy, r);
  c.strokeStyle = color;
  if (glow) { c.shadowColor = glow; c.shadowBlur = r * .6; }
  c.stroke();
  c.restore();
}

function drawWisp(c, x, y, s, time, color = GLOW.wisp) {
  const f = 1 + 0.15 * Math.sin(time / 55 + x);
  c.save();
  c.beginPath();
  c.moveTo(x, y - s * 1.3 * f);
  c.quadraticCurveTo(x + s * .95, y + s * .1, x, y + s * .6);
  c.quadraticCurveTo(x - s * .95, y + s * .1, x, y - s * 1.3 * f);
  const g = c.createRadialGradient(x, y + s * .15, s * .05, x, y, s * 1.2);
  g.addColorStop(0, '#ffffff'); g.addColorStop(.4, color); g.addColorStop(1, 'rgba(60,255,180,0)');
  c.fillStyle = g; c.shadowColor = color; c.shadowBlur = s * 1.6;
  c.fill();
  c.restore();
}

function drawTrapezohedron(c, cx, cy, r, time) {
  const pulse = .6 + .4 * Math.sin(time / 300);
  c.save();
  c.translate(cx, cy);
  c.rotate(Math.sin(time / 1300) * .15);
  const pts = [[0, -1], [.78, -.36], [.64, .6], [0, 1], [-.64, .6], [-.78, -.36]].map(([x, y]) => [x * r * .95, y * r * .95]);
  const poly = () => { c.beginPath(); pts.forEach(([x, y], i) => i ? c.lineTo(x, y) : c.moveTo(x, y)); c.closePath(); };
  poly();
  c.shadowColor = `rgba(255,40,40,${.7 * pulse})`; c.shadowBlur = r * .9;
  const g = c.createLinearGradient(0, -r, 0, r);
  g.addColorStop(0, '#2a2733'); g.addColorStop(1, '#030305');
  c.fillStyle = g; c.fill();
  c.shadowBlur = 0;
  const core = [r * .08, -r * .06];
  // every facet catches a different stone's colour as it turns: it holds every kind
  const turn = Math.floor(time / 450);
  pts.forEach(([x, y], i) => {
    c.beginPath(); c.moveTo(...core); c.lineTo(x, y); c.lineTo(...pts[(i + 1) % pts.length]); c.closePath();
    c.globalAlpha = .3; c.fillStyle = STONES[(i + turn) % STONES.length].fill; c.fill();
  });
  c.globalAlpha = 1;
  c.lineWidth = Math.max(1, r * .04);
  c.strokeStyle = 'rgba(255,255,255,.14)';
  pts.forEach(([x, y]) => { c.beginPath(); c.moveTo(...core); c.lineTo(x, y); c.stroke(); });
  c.strokeStyle = `rgba(255,60,60,${.45 + .5 * pulse})`;
  c.shadowColor = GLOW.void; c.shadowBlur = r * .4;
  [[0, 2], [2, 4], [4, 0]].forEach(([a, b]) => {
    c.beginPath(); c.moveTo(...core);
    c.quadraticCurveTo(pts[a][0] * .4, pts[a][1] * .6, (pts[a][0] + pts[b][0]) * .35, (pts[a][1] + pts[b][1]) * .35);
    c.stroke();
  });
  const cg = c.createRadialGradient(...core, 0, ...core, r * .3);
  cg.addColorStop(0, '#fff0f0'); cg.addColorStop(.35, `rgba(255,40,40,${pulse})`); cg.addColorStop(1, 'rgba(255,0,0,0)');
  c.beginPath(); c.arc(...core, r * .3, 0, TAU); c.fillStyle = cg; c.fill();
  poly(); c.shadowBlur = 0; c.strokeStyle = 'rgba(0,0,0,.8)'; c.lineWidth = Math.max(1, r * .06); c.stroke();
  for (let k = 0; k < STONES.length; k++) {
    const a = time / 1400 + k * TAU / STONES.length;
    c.beginPath(); c.arc(Math.cos(a) * r * 1.1, Math.sin(a) * r * .42, r * .075, 0, TAU);
    c.fillStyle = STONES[k].fill; c.fill();
  }
  c.restore();
}

function drawElderRing(c, cx, cy, r, time, scale = 1) {
  c.save();
  c.translate(cx, cy);
  c.rotate(time / 1800);
  const R = r * 1.04 * scale;
  c.strokeStyle = 'rgba(255,220,150,.9)';
  c.shadowColor = GLOW.elder; c.shadowBlur = r * (.5 + .2 * Math.sin(time / 220));
  c.lineWidth = Math.max(1, r * .06); c.lineCap = 'round';
  c.beginPath(); c.arc(0, 0, R, 0, TAU); c.stroke();
  // five branching ticks, a nod to the Elder Sign
  for (let i = 0; i < 5; i++) {
    const a = i * TAU / 5;
    const x0 = Math.cos(a) * R * .86, y0 = Math.sin(a) * R * .86;
    const x1 = Math.cos(a) * R * 1.16, y1 = Math.sin(a) * R * 1.16;
    c.beginPath(); c.moveTo(x0, y0); c.lineTo(x1, y1);
    c.moveTo(Math.cos(a) * R * 1.06, Math.sin(a) * R * 1.06);
    c.lineTo(Math.cos(a + .12) * R * 1.18, Math.sin(a + .12) * R * 1.18);
    c.stroke();
  }
  c.restore();
}

// Ley Line: sparks pour out of both ends and run on past the stone, along the line it seals.
function drawLeyStreaks(c, dir, cx, cy, size, r, time) {
  const ux = dir === 'h' ? 1 : 0, uy = 1 - ux;
  c.save();
  c.lineCap = 'round';
  for (let i = 0; i < 5; i++) {
    const ph = (time / 900 + i / 5) % 1;
    const d = r * .7 + ph * size * 2.4, len = size * .3 * (1 - ph * .5), a = (1 - ph) * .85;
    for (const sg of [-1, 1]) {
      const x0 = cx + ux * sg * d, y0 = cy + uy * sg * d;
      const seg = () => { c.beginPath(); c.moveTo(x0, y0); c.lineTo(x0 + ux * sg * len, y0 + uy * sg * len); c.stroke(); };
      c.globalAlpha = a * .35; c.strokeStyle = GLOW.ley; c.lineWidth = size * .13; seg();
      c.globalAlpha = a; c.strokeStyle = '#d8fff0'; c.lineWidth = Math.max(1, size * .045); seg();
    }
  }
  c.restore();
}

// Elder Sign: a square seal around the eight neighbouring cells, the exact area it banishes.
function drawElderFrame(c, cx, cy, size, time) {
  const h = size * 1.47, L = size * .4, br = .5 + .5 * Math.sin(time / 500);
  c.save();
  c.strokeStyle = GLOW.elder; c.lineCap = 'round'; c.lineJoin = 'round';
  c.globalAlpha = .14 + .12 * br; c.lineWidth = Math.max(1, size * .03);
  c.setLineDash([size * .12, size * .1]);
  c.strokeRect(cx - h, cy - h, h * 2, h * 2);
  c.setLineDash([]);
  c.globalAlpha = .5 + .35 * br; c.lineWidth = Math.max(1.5, size * .055);
  c.beginPath();
  for (const sx of [-1, 1]) for (const sy of [-1, 1]) {
    c.moveTo(cx + sx * h, cy + sy * (h - L)); c.lineTo(cx + sx * h, cy + sy * h); c.lineTo(cx + sx * (h - L), cy + sy * h);
  }
  // a branching rune at the middle of each side
  for (let i = 0; i < 4; i++) {
    const a = i * Math.PI / 2, ox = Math.cos(a), oy = Math.sin(a), px = -oy, py = ox;
    const mx = cx + ox * h, my = cy + oy * h, t = size * .13;
    c.moveTo(mx - ox * t * 1.4, my - oy * t * 1.4); c.lineTo(mx, my);
    c.moveTo(mx - ox * t * .7, my - oy * t * .7); c.lineTo(mx - ox * t * .7 + px * t, my - oy * t * .7 + py * t);
  }
  c.stroke();
  c.restore();
}

function drawPiece(c, p, cx, cy, size, time, mult) {
  const r = size * 0.42 * p.scale * mult;
  if (r <= 0.5) return;
  if (p.special === 'rainbow') { drawTrapezohedron(c, cx, cy, r, time); return; }
  const st = STONES[p.color], rr = r, ley = p.special === 'h' || p.special === 'v';
  c.save();
  if (ley) drawLeyStreaks(c, p.special, cx, cy, size, r, time);
  else if (p.special === 'bomb') drawElderFrame(c, cx, cy, size, time);
  // a Ley Line stone is drawn out along the way it seals
  if (ley) { c.translate(cx, cy); if (p.special === 'h') c.scale(1.12, .94); else c.scale(.94, 1.12); c.translate(-cx, -cy); }

  // drop shadow, body, rim
  shapePath(c, st.shape, cx, cy + rr * .1, rr);
  c.fillStyle = 'rgba(0,0,0,.45)'; c.fill();
  shapePath(c, st.shape, cx, cy, rr);
  const g = c.createLinearGradient(cx - rr * .4, cy - rr, cx + rr * .4, cy + rr);
  g.addColorStop(0, st.light); g.addColorStop(.38, st.fill); g.addColorStop(1, st.dark);
  c.fillStyle = g; c.fill();
  c.lineJoin = 'round'; c.lineWidth = Math.max(1, rr * .07); c.strokeStyle = st.dark; c.stroke();

  c.save();
  shapePath(c, st.shape, cx, cy, rr);
  c.clip();
  // bevel: dark lower inner edge, light upper inner edge
  c.lineWidth = rr * .14;
  shapePath(c, st.shape, cx, cy + rr * .07, rr); c.strokeStyle = 'rgba(0,0,0,.28)'; c.stroke();
  shapePath(c, st.shape, cx, cy - rr * .07, rr); c.strokeStyle = 'rgba(255,255,255,.14)'; c.stroke();
  // weathering pits
  for (let i = 0; i < 4; i++) {
    const s = p.color * 13 + i * 7;
    c.beginPath();
    c.arc(cx + (hash(s) - .5) * rr * 1.2, cy + (hash(s + 1) - .5) * rr * 1.2, rr * (.03 + hash(s + 2) * .04), 0, TAU);
    c.fillStyle = 'rgba(0,0,0,.18)'; c.fill();
  }
  const gy = cy + rr * (GLYPH_OFFSET[st.shape] || 0);
  if (p.special === 'h' || p.special === 'v') drawGlyph(c, st.glyph, cx, gy, rr, '#d8fff0', GLOW.ley);
  else if (p.special === 'bomb') drawGlyph(c, st.glyph, cx, gy, rr, '#ffe7b8', GLOW.elder);
  else if (p.special === 'dart') drawGlyph(c, st.glyph, cx, gy, rr, '#e9fff4', GLOW.wisp);
  else drawGlyph(c, st.glyph, cx, gy, rr, 'rgba(0,0,0,.55)', null);
  c.restore();

  if (ley) {
    // chevrons carved at each end, pointing the way it seals
    c.save();
    c.strokeStyle = `rgba(216,255,240,${.75 + .25 * Math.sin(time / 170)})`;
    c.shadowColor = GLOW.ley; c.shadowBlur = r * .5;
    c.lineWidth = Math.max(1.2, r * .1); c.lineCap = 'round'; c.lineJoin = 'round';
    c.beginPath();
    for (const sg of [-1, 1]) {
      const pt = (a, b) => p.special === 'h' ? [cx + sg * a * r, cy + b * r] : [cx + b * r, cy + sg * a * r];
      c.moveTo(...pt(.58, -.2)); c.lineTo(...pt(.8, 0)); c.lineTo(...pt(.58, .2));
    }
    c.stroke();
    c.restore();
  } else if (p.special === 'bomb') {
    shapePath(c, st.shape, cx, cy, rr);
    c.strokeStyle = `rgba(255,200,110,${.55 + .3 * Math.sin(time / 260)})`; c.lineWidth = Math.max(1, rr * .07); c.stroke();
  } else if (p.special === 'dart') {
    drawWisp(c, cx + rr * .5, cy - rr * .55, rr * .3, time);
  }
  c.restore();
}

// Taint is a living blob that sits behind the stone: a lumpy, slowly writhing mass a
// little larger than the stone so it shows around its edges.
const BLOB_RADIUS = .54;           // in cells
const TAINT_FLESH = '#55147a';     // flat midtone shared by bridges and tendrils
function drawBlob(c, cx, cy, R, now, seed) {
  if (R <= .5) return;
  const N = 32;
  c.save();
  c.beginPath();
  for (let i = 0; i <= N; i++) {
    const a = i / N * TAU;
    const k = 1 + .09 * Math.sin(3 * a + seed + now / 700)
                + .06 * Math.sin(5 * a - seed * 2 + now / 430)
                + .04 * Math.sin(7 * a + seed * 3 - now / 900);
    const x = cx + Math.cos(a) * R * k, y = cy + Math.sin(a) * R * k;
    i ? c.lineTo(x, y) : c.moveTo(x, y);
  }
  c.closePath();
  const g = c.createRadialGradient(cx - R * .25, cy - R * .3, R * .1, cx, cy, R * 1.15);
  g.addColorStop(0, '#c25cf0'); g.addColorStop(.45, '#6a1a8f'); g.addColorStop(1, '#2a0538');
  c.fillStyle = g;
  c.shadowColor = GLOW.taint; c.shadowBlur = R * (.4 + .15 * Math.sin(now / 500 + seed));
  c.fill();
  c.shadowBlur = 0;
  // glistening pustules around the rim
  for (let i = 0; i < 4; i++) {
    const a = hash(seed * 5 + i) * TAU + now / 4000, d = R * (.78 + .1 * hash(seed + i));
    const pr = R * (.07 + .05 * hash(seed * 2 + i)) * (1 + .15 * Math.sin(now / 300 + i * 2));
    c.beginPath(); c.arc(cx + Math.cos(a) * d, cy + Math.sin(a) * d, pr, 0, TAU);
    c.fillStyle = 'rgba(214,130,255,.75)'; c.fill();
    c.beginPath(); c.arc(cx + Math.cos(a) * d - pr * .3, cy + Math.sin(a) * d - pr * .3, pr * .35, 0, TAU);
    c.fillStyle = 'rgba(255,235,255,.7)'; c.fill();
  }
  c.beginPath(); c.ellipse(cx - R * .35, cy - R * .45, R * .28, R * .12, -.5, 0, TAU);
  c.fillStyle = 'rgba(255,220,255,.28)'; c.fill();
  c.restore();
}

function fleshStroke(c, pts, w0, w1, glow) {
  c.save();
  c.lineCap = 'round'; c.strokeStyle = TAINT_FLESH;
  c.shadowColor = GLOW.taint; c.shadowBlur = glow;
  for (let i = 0; i < pts.length - 1; i++) {
    c.beginPath(); c.moveTo(...pts[i]); c.lineTo(...pts[i + 1]);
    c.lineWidth = w0 + (w1 - w0) * (i / (pts.length - 1)); c.stroke();
  }
  c.restore();
}

// Displayed blob size: pops in with an overshoot when tainted, shrinks away when cleansed.
function taintLevel(r, c) {
  const f = Math.max(0, taintFill[r][c]);
  return taint[r][c] ? ease.outBack(f) : f;
}

function drawTaintLayer(now) {
  const centre = (r, c) => [PAD + (c + .5) * cell, PAD + (r + .5) * cell];
  // fleshy bridges between neighbouring blobs
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      const l0 = taintLevel(r, c);
      if (l0 <= .05) continue;
      for (const [dr, dc] of [[0, 1], [1, 0]]) {
        if (!inBounds(r + dr, c + dc)) continue;
        const l = Math.min(l0, taintLevel(r + dr, c + dc));
        if (l <= .05) continue;
        const [x0, y0] = centre(r, c), [x1, y1] = centre(r + dr, c + dc);
        const w = cell * .5 * l * (1 + .12 * Math.sin(now / 520 + key(r, c)));
        const mid = [(x0 + x1) / 2 + dr * Math.sin(now / 800 + c) * cell * .05, (y0 + y1) / 2 + dc * Math.sin(now / 800 + r) * cell * .05];
        fleshStroke(ctx, [[x0, y0], mid, [x1, y1]], w, w, cell * .2);
      }
    }
  }
  // tendrils reaching toward newly tainted cells
  for (const f of fx) {
    if (f.type !== 'tendril' || f.t < 0) continue;
    const p = ease.inOut(Math.min(1, f.t / f.dur));
    const [x0, y0] = centre(f.r0, f.c0), [x1, y1] = centre(f.r1, f.c1);
    const nx = -(y1 - y0) / cell, ny = (x1 - x0) / cell, pts = [];
    for (let i = 0; i <= 12; i++) {
      const s = i / 12 * p, wig = Math.sin(s * 9 - now / 70) * cell * .09 * s;
      pts.push([x0 + (x1 - x0) * s + nx * wig, y0 + (y1 - y0) * s + ny * wig]);
    }
    fleshStroke(ctx, pts, cell * .26, cell * .06, cell * .3);
  }
  for (let r = 0; r < ROWS; r++)
    for (let c = 0; c < COLS; c++) {
      const l = taintLevel(r, c);
      if (l > .01) drawBlob(ctx, ...centre(r, c), cell * BLOB_RADIUS * l, now, key(r, c) + 1);
    }
}

// ---------- Rendering: background (eye, tentacles, deep water) ----------
// Each tentacle grows from a root at (bx, by) (fractions of the screen) along heading `ang`,
// curving by `bend`. `at` is the dread level where it starts to emerge; it reaches full
// length TENTACLE_GROW later. Thresholds sit in the first ~60% of a level so most
// appear in normal play, and the last few turns are the most crowded.
const UP = -Math.PI / 2;
const TENTACLE_GROW = .35;
const TENTACLES = [
  // bottom corners: present from the start
  { bx: -.04, by: 1, ang: UP + .38, bend: .8, len: .62, w: .075, at: 0 },
  { bx: 1.04, by: 1, ang: UP - .38, bend: -.8, len: .64, w: .08, at: 0 },
  // low on the sides
  { bx: -.03, by: .85, ang: -.6, bend: -.7, len: .3, w: .045, at: .05 },
  { bx: 1.03, by: .8, ang: Math.PI + .6, bend: .7, len: .3, w: .045, at: .05 },
  // rising from the depths
  { bx: .1, by: 1, ang: UP + .15, bend: .5, len: .4, w: .045, at: .12 },
  { bx: .9, by: 1, ang: UP - .15, bend: -.5, len: .4, w: .045, at: .12 },
  // curling in from the sides
  { bx: -.03, by: .62, ang: -.25, bend: -.9, len: .36, w: .05, at: .22 },
  { bx: 1.03, by: .5, ang: Math.PI + .25, bend: .9, len: .36, w: .05, at: .22 },
  { bx: .2, by: 1, ang: UP + .3, bend: -.6, len: .28, w: .032, at: .32 },
  { bx: .8, by: 1, ang: UP - .3, bend: .6, len: .28, w: .032, at: .32 },
  { bx: -.03, by: .3, ang: .1, bend: -.6, len: .26, w: .035, at: .42 },
  { bx: 1.03, by: .24, ang: Math.PI - .1, bend: .6, len: .26, w: .035, at: .42 },
  // reaching down from above
  { bx: -.02, by: -.02, ang: .9, bend: .7, len: .3, w: .04, at: .55 },
  { bx: 1.02, by: -.02, ang: Math.PI - .9, bend: -.7, len: .3, w: .04, at: .55 },
].map((t, i) => ({ ...t, phase: i * 1.37 }));
const SNOW = Array.from({ length: 80 }, () => ({
  x: Math.random(), y: Math.random(), s: Math.random() * 1.5 + .4, v: Math.random() * .000012 + .000004, ph: Math.random() * TAU,
}));

const EYE_OPACITY = .9;
const eyeSlot = $('eyeSlot');
function drawEyeLayer(now) {
  fctx.setTransform(bgDpr, 0, 0, bgDpr, 0, 0);
  fctx.clearRect(0, 0, bgW, bgH);
  // Sized so the fully open eye (height .75R) fills the slot; the glow spills a little past it.
  const sr = eyeSlot.getBoundingClientRect();
  drawEye(fctx, sr.left + sr.width / 2, sr.top + sr.height / 2,
    Math.min(sr.width * .4, sr.height / .75), dread.shown, now);
  drawWreckFg(now); // the arms and flung stones pass in front of everything
}

function drawEye(g, cx, cy, R, open, now) {
  g.save();
  if (open < 0.03) {
    g.beginPath(); g.moveTo(cx - R, cy); g.quadraticCurveTo(cx, cy + R * .15, cx + R, cy);
    g.strokeStyle = 'rgba(140,255,210,.08)'; g.lineWidth = 2; g.stroke();
    g.restore();
    return;
  }
  const h = R * .75 * open;
  const lid = () => {
    g.beginPath(); g.moveTo(cx - R, cy);
    g.quadraticCurveTo(cx, cy - h, cx + R, cy);
    g.quadraticCurveTo(cx, cy + h, cx - R, cy);
    g.closePath();
  };
  // Faint while barely open, more solid as it opens.
  g.globalAlpha = EYE_OPACITY * (.25 + .75 * open);
  lid();
  g.shadowColor = `rgba(190,255,60,${.5 * open})`; g.shadowBlur = 80 * open;
  g.fillStyle = '#141c08'; g.fill();
  g.shadowBlur = 0;
  g.save();
  lid(); g.clip();
  const ir = R * .4, ix = cx, iy = cy;
  const ig = g.createRadialGradient(ix, iy, ir * .1, ix, iy, ir);
  ig.addColorStop(0, '#f4ff9a'); ig.addColorStop(.45, '#a6c41c'); ig.addColorStop(.85, '#3a4a05'); ig.addColorStop(1, '#141c08');
  g.beginPath(); g.arc(ix, iy, ir, 0, TAU); g.fillStyle = ig; g.fill();
  g.strokeStyle = 'rgba(40,50,0,.35)'; g.lineWidth = 1;
  g.beginPath();
  for (let i = 0; i < 40; i++) {
    const a = i * TAU / 40;
    g.moveTo(ix + Math.cos(a) * ir * .3, iy + Math.sin(a) * ir * .3);
    g.lineTo(ix + Math.cos(a) * ir * .95, iy + Math.sin(a) * ir * .95);
  }
  g.stroke();
  g.beginPath(); g.ellipse(ix, iy, ir * (.2 - .12 * open), ir * .82, 0, 0, TAU);
  g.fillStyle = '#000'; g.fill();
  const lg = g.createLinearGradient(0, cy - h / 2, 0, cy + h / 2);
  lg.addColorStop(0, 'rgba(0,0,0,.75)'); lg.addColorStop(.3, 'rgba(0,0,0,0)');
  lg.addColorStop(.7, 'rgba(0,0,0,0)'); lg.addColorStop(1, 'rgba(0,0,0,.65)');
  g.fillStyle = lg; g.fillRect(cx - R, cy - h, R * 2, h * 2);
  g.restore();
  lid(); g.strokeStyle = 'rgba(10,20,6,.95)'; g.lineWidth = 5; g.stroke();
  g.restore();
}

function drawTentacle(g, W, H, T, d, now) {
  const grow = Math.min(1, Math.max(0, (d - T.at) / TENTACLE_GROW));
  const L = Math.hypot(W, H) * .5 * T.len * ease.inOut(grow);
  if (L < 6) return;
  const N = 40, base = Math.min(W, H) * T.w, step = (L + base) / N, pts = [];
  // start just off-screen so the root is hidden
  let x = T.bx * W - Math.cos(T.ang) * base, y = T.by * H - Math.sin(T.ang) * base;
  for (let i = 0; i <= N; i++) {
    const s = i / N;
    const h = T.ang + T.bend * s * s + Math.sin(now / 1100 + T.phase + s * 5) * .35 * s;
    pts.push([x, y, base * (1 - s * .9), h]);
    x += Math.cos(h) * step; y += Math.sin(h) * step;
  }
  g.save();
  g.lineCap = 'round'; g.lineJoin = 'round';
  // Drawn in a few bands of constant width (one path each) rather than per segment, and
  // the glow is a wider translucent pass: shadowBlur here is far too slow at this scale.
  const BAND = 5;
  const band = (from, widthOf) => {
    g.beginPath();
    for (let i = from; i <= Math.min(N, from + BAND); i++) i === from ? g.moveTo(pts[i][0], pts[i][1]) : g.lineTo(pts[i][0], pts[i][1]);
    g.lineWidth = widthOf(pts[Math.min(N, from + (BAND >> 1))][2]);
    g.stroke();
  };
  g.strokeStyle = 'rgba(110,200,170,.1)';
  for (let i = 0; i < N; i += BAND) band(i, w => w * 2 + 6);
  for (let i = 0; i < N; i += BAND) {
    const s = i / N; // slightly paler toward the tip
    g.strokeStyle = `rgb(${Math.round(38 + 22 * s)},${Math.round(84 + 26 * s)},${Math.round(72 + 20 * s)})`;
    band(i, w => w * 2);
  }
  // suckers and sheen on the inside of the curl
  const side = T.bend >= 0 ? 1 : -1;
  const perp = (h, w, k) => [-Math.sin(h) * w * k * side, Math.cos(h) * w * k * side];
  g.beginPath();
  pts.forEach(([px, py, w, h], i) => {
    const [ox, oy] = perp(h, w, -.45);
    i ? g.lineTo(px + ox, py + oy) : g.moveTo(px + ox, py + oy);
  });
  g.strokeStyle = 'rgba(160,230,200,.3)'; g.lineWidth = Math.max(1, base * .14); g.stroke();
  g.fillStyle = 'rgba(215,180,170,.5)';
  for (let i = 3; i < N - 3; i += 3) {
    const [px, py, w, h] = pts[i], [ox, oy] = perp(h, w, .55);
    g.beginPath(); g.arc(px + ox, py + oy, w * .26, 0, TAU); g.fill();
  }
  g.restore();
}

// Murky water: a soft cloud texture painted once per resize at low resolution, then two copies
// drift past each other at different speeds so the gloom slowly churns.
let murk = null;
function buildMurk() {
  const W = Math.max(1, Math.round(bgW / 4)), H = Math.max(1, Math.round(bgH / 4)), c = document.createElement('canvas');
  c.width = W; c.height = H;
  const g = c.getContext('2d');
  for (let i = 0; i < 46; i++) {
    const x = Math.random() * W, y = Math.random() * H, r = (Math.random() * .25 + .1) * Math.max(W, H);
    const tone = Math.random() < .55 ? '2,6,6' : Math.random() < .5 ? '22,40,30' : '14,30,34';
    const a = Math.random() * .35 + .15;
    // drawn three times across so the texture wraps seamlessly as it scrolls
    for (const ox of [-W, 0, W]) {
      const rg = g.createRadialGradient(x + ox, y, 0, x + ox, y, r);
      rg.addColorStop(0, `rgba(${tone},${a})`); rg.addColorStop(1, `rgba(${tone},0)`);
      g.fillStyle = rg; g.fillRect(x + ox - r, y - r, r * 2, r * 2);
    }
  }
  murk = c;
}

function drawMurk(g, W, H, now) {
  if (!murk) return;
  g.save();
  g.imageSmoothingEnabled = true;
  [[.0045, 0, .9], [-.0028, H * .37, .6]].forEach(([v, dy, a]) => {
    const off = ((now * v) % W + W) % W;
    g.globalAlpha = a;
    for (const x of [off - W, off]) {
      g.drawImage(murk, x, -dy, W, H);
      g.drawImage(murk, x, H - dy, W, H);
    }
  });
  g.restore();
}

// faint rippling light where the surface would be
function drawSurface(g, W, H, now) {
  g.save();
  g.globalCompositeOperation = 'lighter';
  g.lineWidth = 1.5;
  for (let k = 0; k < 5; k++) {
    const y0 = H * (.02 + k * .028);
    g.strokeStyle = `rgba(120,210,190,${.05 - k * .008})`;
    g.beginPath();
    for (let x = 0; x <= W; x += 24) {
      const y = y0 + Math.sin(x / 70 + now / 1300 + k * 1.9) * 5 + Math.sin(x / 31 - now / 900 + k) * 2;
      x ? g.lineTo(x, y) : g.moveTo(x, y);
    }
    g.stroke();
  }
  g.restore();
}

function drawBackground(now) {
  const W = bgW, H = bgH, g = bctx;
  g.setTransform(bgDpr, 0, 0, bgDpr, 0, 0);
  const sky = g.createLinearGradient(0, 0, 0, H);
  sky.addColorStop(0, '#08201e'); sky.addColorStop(.45, '#04100f'); sky.addColorStop(1, '#010403');
  g.fillStyle = sky; g.fillRect(0, 0, W, H);
  drawSurface(g, W, H, now);

  g.save();
  g.globalCompositeOperation = 'lighter';
  for (let i = 0; i < 4; i++) {
    const x = W * (.12 + i * .26) + Math.sin(now / 4000 + i * 1.7) * W * .05;
    const sg = g.createLinearGradient(0, 0, 0, H * .85);
    sg.addColorStop(0, 'rgba(120,220,200,.05)'); sg.addColorStop(1, 'rgba(120,220,200,0)');
    g.beginPath();
    g.moveTo(x - W * .03, 0); g.lineTo(x + W * .04, 0); g.lineTo(x + W * .2, H * .85); g.lineTo(x - W * .01, H * .85);
    g.closePath(); g.fillStyle = sg; g.fill();
  }
  g.restore();

  drawMurk(g, W, H, now);
  TENTACLES.forEach(T => drawTentacle(g, W, H, T, dread.shown, now));

  g.fillStyle = 'rgba(200,240,230,.22)';
  for (const s of SNOW) {
    const y = ((s.y + now * s.v) % 1) * H, x = (s.x + Math.sin(now / 3000 + s.ph) * .01) * W;
    g.beginPath(); g.arc(x, y, s.s, 0, TAU); g.fill();
  }

  const vg = g.createRadialGradient(W / 2, H / 2, Math.min(W, H) * .3, W / 2, H / 2, Math.max(W, H) * .75);
  vg.addColorStop(0, 'rgba(0,0,0,0)');
  vg.addColorStop(1, `rgba(${Math.round(60 * dread.shown)},0,0,${.6 + .25 * dread.shown})`);
  g.fillStyle = vg; g.fillRect(0, 0, W, H);

  const fa = flashAlpha();
  if (fa) { g.fillStyle = `rgba(200,205,255,${.4 * fa})`; g.fillRect(0, 0, W, H); }
  drawBolts(g, 0, 0);
}

// ---------- Rendering: board ----------
function cellCenter(r, c) { return [PAD + (c + .5) * cell, PAD + (r + .5) * cell]; }

// ---------- Relic preview ----------
// While a relic is pressed or dragged, the cells it would clear are lit, including the
// combined area when it's dragged onto another relic. Mirrors effectCells and doCombo.
function relicPreview() {
  if (state !== 'playing' || busy) return null;
  const at = drag ? drag.start : selected;
  if (!at) return null;
  const to = drag && drag.axis && drag.n && drag.offset > .2 ? drag.n : null;
  const A = grid[at.r][at.c], B = to && grid[to.r][to.c];
  if (!A) return null;
  const cells = new Set(), aims = [];
  let color = GLOW.ley;
  const add = (r, c) => { if (inBounds(r, c)) cells.add(key(r, c)); };
  const area = (sp, r, c) => {
    if (sp === 'h') for (let cc = 0; cc < COLS; cc++) add(r, cc);
    else if (sp === 'v') for (let rr = 0; rr < ROWS; rr++) add(rr, c);
    else if (sp === 'bomb') for (let dr = -1; dr <= 1; dr++) for (let dc = -1; dc <= 1; dc++) add(r + dr, c + dc);
  };
  const strike = (p, r, c, n, carry) => dartAims(p, r, c, n).forEach(t => {
    cells.add(t); aims.push([r, c, t]);
    if (carry) area(carry, Math.floor(t / COLS), t % COLS);
  });
  const solo = (p, pos) => {
    if (p.special === 'dart') { color = GLOW.wisp; strike(p, pos.r, pos.c); }
    else if (p.special !== 'rainbow') { area(p.special, pos.r, pos.c); color = p.special === 'bomb' ? GLOW.elder : GLOW.ley; }
  };
  if (B && isCombo(A, B)) {
    // after the swap A sits at `to` and B at `at`; combos centre on `to`
    const s1 = A.special, s2 = B.special, { r, c } = to;
    const striped = sp => sp === 'h' || sp === 'v';
    if (s1 === 'rainbow' && s2 === 'rainbow') { forEachPiece((q, rr, cc) => add(rr, cc)); color = GLOW.void; }
    else if (s1 === 'rainbow' || s2 === 'rainbow') {
      const O = s1 === 'rainbow' ? B : A;
      forEachPiece((q, rr, cc) => { if (q.color === O.color) add(rr, cc); });
      color = GLOW.void;
    } else if (s1 === 'dart' || s2 === 'dart') {
      const D = s1 === 'dart' ? A : B, O = D === A ? B : A, pos = D === A ? to : at;
      color = GLOW.wisp;
      strike(D, pos.r, pos.c, O.special === 'dart' ? 3 : 1, O.special === 'dart' ? null : O.special);
    } else if (striped(s1) && striped(s2)) { area('h', r, c); area('v', r, c); }
    else if (s1 === 'bomb' && s2 === 'bomb') {
      for (let dr = -2; dr <= 2; dr++) for (let dc = -2; dc <= 2; dc++) add(r + dr, c + dc);
      color = GLOW.elder;
    } else {
      for (let d = -1; d <= 1; d++) { area('h', r + d, c); area('v', r, c + d); }
      color = GLOW.elder;
    }
    add(to.r, to.c); add(at.r, at.c);
  } else if (A.special) solo(A, to || at);
  else if (B && B.special) solo(B, at); // dragging a plain stone onto a relic moves the relic here
  return cells.size ? { cells, aims, color } : null;
}

function drawPreview(pv, now) {
  const pulse = .5 + .5 * Math.sin(now / 180);
  ctx.save();
  ctx.fillStyle = ctx.strokeStyle = pv.color;
  ctx.lineWidth = 1.5;
  for (const k of pv.cells) {
    const r = Math.floor(k / COLS), c = k % COLS;
    ctx.beginPath(); roundRectPath(ctx, PAD + c * cell + 2, PAD + r * cell + 2, cell - 4, cell - 4, cell * .14);
    ctx.globalAlpha = .13 + .09 * pulse; ctx.fill();
    ctx.globalAlpha = .5; ctx.stroke();
  }
  ctx.restore();
}

// Lines from each witch-light to where its lightning will land.
function drawAims(aims, alpha) {
  ctx.save();
  ctx.lineJoin = 'round'; ctx.lineCap = 'round';
  for (const [r0, c0, t] of aims) {
    const [x0, y0] = cellCenter(r0, c0), [x1, y1] = cellCenter(Math.floor(t / COLS), t % COLS);
    const pts = boltPath(x0, y0, x1, y1, cell * .18, 6);
    const path = () => { ctx.beginPath(); pts.forEach(([x, y], i) => i ? ctx.lineTo(x, y) : ctx.moveTo(x, y)); };
    ctx.globalAlpha = alpha * .4; ctx.strokeStyle = '#b9a8ff'; ctx.lineWidth = cell * .12; path(); ctx.stroke();
    ctx.globalAlpha = alpha; ctx.strokeStyle = '#f4f0ff'; ctx.lineWidth = Math.max(1, cell * .035); path(); ctx.stroke();
    ctx.beginPath(); ctx.arc(x1, y1, cell * .4, 0, TAU); ctx.lineWidth = 1.5; ctx.stroke();
  }
  ctx.restore();
}

// Idle witch-lights flicker toward their target every few seconds.
const WITCH_FLICKER = 2600;
function drawWitchFlickers(now, skip) {
  if (state !== 'playing' || busy) return;
  const aims = [];
  forEachPiece((p, r, c) => {
    if (p.special !== 'dart' || p === skip || p.x !== c || p.y !== r) return;
    const ph = ((now + hash(key(r, c)) * WITCH_FLICKER) % WITCH_FLICKER) / WITCH_FLICKER;
    if (ph < .1) dartAims(p, r, c, 1).forEach(t => aims.push([r, c, t, 1 - ph / .1]));
  });
  for (const [r, c, t, a] of aims) drawAims([[r, c, t]], .55 * a);
}

function draw(now) {
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  ctx.clearRect(0, 0, boardW, boardH);
  if (shake) {
    const k = 1 - shake.t / shake.dur;
    ctx.translate((Math.random() - .5) * shake.mag * k, (Math.random() - .5) * shake.mag * k);
  }

  ctx.beginPath(); roundRectPath(ctx, 0, 0, boardW, boardH, 14);
  ctx.fillStyle = 'rgba(3,12,12,.3)'; ctx.fill(); // translucent so the eye and tentacles show through
  ctx.strokeStyle = 'rgba(125,255,200,.14)'; ctx.lineWidth = 1.5; ctx.stroke();
  for (let r = 0; r < ROWS; r++) {
    for (let c = 0; c < COLS; c++) {
      const x = PAD + c * cell + 2, y = PAD + r * cell + 2, w = cell - 4;
      ctx.beginPath(); roundRectPath(ctx, x, y, w, w, cell * .14);
      ctx.fillStyle = (r + c) % 2 ? 'rgba(140,190,175,.05)' : 'rgba(140,190,175,.1)';
      ctx.fill();
      ctx.strokeStyle = 'rgba(0,0,0,.35)'; ctx.lineWidth = 1; ctx.stroke();
    }
  }
  if (taintFill.length) drawTaintLayer(now);
  if (selected) {
    const x = PAD + selected.c * cell + 2, y = PAD + selected.r * cell + 2;
    ctx.beginPath(); roundRectPath(ctx, x, y, cell - 4, cell - 4, cell * .14);
    ctx.fillStyle = 'rgba(125,255,200,.2)'; ctx.fill();
    ctx.strokeStyle = 'rgba(125,255,200,.6)'; ctx.lineWidth = 1; ctx.stroke();
  }

  const pv = relicPreview();
  if (pv) drawPreview(pv, now);

  const hintPieces = hint ? hint.map(h => grid[h.r][h.c]) : [];
  const dragged = drag && drag.axis ? grid[drag.start.r][drag.start.c] : null;
  ctx.save();
  ctx.beginPath(); ctx.rect(PAD, PAD, cell * COLS, cell * ROWS); ctx.clip();
  forEachPiece((p, r, c) => {
    if (p === dragged || p.fly) return;
    let mult = 1, dy = 0;
    if (hintPieces.includes(p)) mult = 1 + 0.1 * Math.sin(now / 110);
    if (selected && selected.r === r && selected.c === c) dy = Math.sin(now / 140) * cell * .05;
    drawPiece(ctx, p, PAD + (p.x + .5) * cell, PAD + (p.y + .5) * cell + dy, cell, now, mult);
  });
  if (dragged) drawPiece(ctx, dragged, PAD + (dragged.x + .5) * cell, PAD + (dragged.y + .5) * cell, cell, now, 1.1);
  ctx.restore();
  drawShoggothLayer(now);
  if (pv && pv.aims.length) drawAims(pv.aims, .8);
  else drawWitchFlickers(now);

  for (const f of fx) {
    if (f.t < 0 || f.type === 'tendril') continue;
    const p = f.t / f.dur, a = 1 - p;
    ctx.save();
    ctx.globalAlpha = a;
    if (f.type === 'beam') {
      const w = cell * .9 * (1 - p * .7);
      ctx.shadowColor = GLOW.ley; ctx.shadowBlur = 28; ctx.fillStyle = '#d8fff0';
      if (f.dir === 'h') ctx.fillRect(PAD, PAD + (f.r + .5) * cell - w / 2, cell * COLS, w);
      else ctx.fillRect(PAD + (f.c + .5) * cell - w / 2, PAD, w, cell * ROWS);
    } else if (f.type === 'ring') {
      const [x, y] = cellCenter(f.r, f.c), col = f.color || GLOW.elder;
      ctx.beginPath(); ctx.arc(x, y, cell * (.4 + f.size * p), 0, TAU);
      ctx.lineWidth = cell * .25 * a + 1; ctx.strokeStyle = col;
      ctx.shadowColor = col; ctx.shadowBlur = 22; ctx.stroke();
    } else if (f.type === 'sign') {
      const [x, y] = cellCenter(f.r, f.c);
      drawElderRing(ctx, x, y, cell * .5, now, (f.size || 1.4) * (.6 + p * .8));
    } else if (f.type === 'zap') {
      const [x0, y0] = cellCenter(f.r0, f.c0), [x1, y1] = cellCenter(f.r1, f.c1);
      ctx.beginPath(); ctx.moveTo(x0, y0);
      const mx = (x0 + x1) / 2 + (Math.random() - .5) * cell * .5, my = (y0 + y1) / 2 + (Math.random() - .5) * cell * .5;
      ctx.lineTo(mx, my); ctx.lineTo(x1, y1);
      ctx.lineWidth = 2.5; ctx.strokeStyle = '#ff6a6a';
      ctx.shadowColor = GLOW.void; ctx.shadowBlur = 12; ctx.stroke();
    }
    ctx.restore();
  }

  for (const pt of particles) {
    const k = 1 - pt.life / pt.max, x = PAD + pt.x * cell, y = PAD + pt.y * cell, s = pt.size * cell;
    ctx.globalAlpha = k;
    ctx.fillStyle = pt.color;
    if (pt.mote || pt.drop) {
      ctx.save(); ctx.shadowColor = pt.color; ctx.shadowBlur = pt.mote ? 8 : 3;
      ctx.beginPath(); ctx.arc(x, y, s, 0, TAU); ctx.fill();
      ctx.restore();
    } else {
      ctx.save(); ctx.translate(x, y); ctx.rotate(pt.rot);
      ctx.fillRect(-s, -s * .7, s * 2, s * 1.4);
      ctx.restore();
    }
  }
  ctx.globalAlpha = 1;

  const fa = flashAlpha();
  if (fa) { ctx.fillStyle = `rgba(225,225,255,${.28 * fa})`; ctx.fillRect(0, 0, boardW, boardH); }
  const br = canvas.getBoundingClientRect();
  drawBolts(ctx, br.left, br.top);

  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  for (const f of floats) {
    const p = f.t / f.dur;
    ctx.globalAlpha = 1 - p * p;
    ctx.font = `700 ${Math.round(cell * f.size)}px Cinzel, Georgia, serif`;
    const x = PAD + (f.x + .5) * cell, y = PAD + (f.y + .5) * cell - p * cell * .9;
    ctx.lineWidth = 4; ctx.lineJoin = 'round'; ctx.strokeStyle = 'rgba(2,10,8,.85)'; ctx.strokeText(f.text, x, y);
    ctx.fillStyle = f.color; ctx.fillText(f.text, x, y);
  }
  ctx.globalAlpha = 1;

  if (banner) {
    const p = banner.t / banner.dur;
    const s = p < .2 ? ease.outBack(p / .2) : 1;
    ctx.save();
    ctx.globalAlpha = p > .7 ? 1 - (p - .7) / .3 : 1;
    ctx.translate(boardW / 2, boardH / 2 - p * cell * .5);
    ctx.scale(s, s);
    let fs = cell * .8;
    ctx.font = `900 ${Math.round(fs)}px Cinzel, Georgia, serif`;
    const tw = ctx.measureText(banner.text).width;
    if (tw > boardW * .92) { fs *= boardW * .92 / tw; ctx.font = `900 ${Math.round(fs)}px Cinzel, Georgia, serif`; }
    const grad = ctx.createLinearGradient(0, -fs / 2, 0, fs / 2);
    grad.addColorStop(0, '#f0fff8'); grad.addColorStop(1, '#5fe0b0');
    ctx.lineWidth = 7; ctx.strokeStyle = '#03120e'; ctx.lineJoin = 'round';
    ctx.shadowColor = GLOW.ley; ctx.shadowBlur = 20;
    ctx.strokeText(banner.text, 0, 0);
    ctx.shadowBlur = 0;
    ctx.fillStyle = grad; ctx.fillText(banner.text, 0, 0);
    ctx.restore();
  }
}

let lastT = performance.now();
function frame(now) {
  const dt = Math.min(50, now - lastT);
  lastT = now;
  updateTweens(dt);
  for (let i = particles.length - 1; i >= 0; i--) {
    const pt = particles[i];
    pt.life += dt;
    if (!pt.mote) pt.vy += 0.0006 * dt;
    pt.x += pt.vx * dt / 16; pt.y += pt.vy * dt / 16; pt.rot += pt.spin * dt;
    if (pt.life >= pt.max) particles.splice(i, 1);
  }
  fx = fx.filter(f => (f.t += dt) < f.dur);
  floats = floats.filter(f => (f.t += dt) < f.dur);
  if (banner && (banner.t += dt) >= banner.dur) banner = null;
  if (shake && (shake.t += dt) >= shake.dur) shake = null;
  if (flash && (flash.t += dt) >= flash.dur) flash = null;
  bolts = bolts.filter(b => (b.t += dt) < b.dur);
  updateWreck(dt);
  const dreadGoal = previewDread ? 1 : dread.target;
  dread.shown += (dreadGoal - dread.shown) * Math.min(1, dt / 500);
  // Blobs swell in when a cell is tainted and shrink away when cleansed.
  for (let r = 0; r < taintFill.length; r++)
    for (let c = 0; c < COLS; c++)
      taintFill[r][c] = taint[r][c] ? Math.min(1, taintFill[r][c] + dt / 450) : Math.max(0, taintFill[r][c] - dt / 280);
  for (let r = 0; r < shogFill.length; r++)
    for (let c = 0; c < COLS; c++)
      shogFill[r][c] = shog[r][c] ? Math.min(1, shogFill[r][c] + dt / 600) : Math.max(0, shogFill[r][c] - dt / 260);
  updateDrone(now);
  if (state === 'playing' && !busy && !hint && !selected && now - lastInput > 5000) hint = findMove();
  drawBackground(now);
  if (grid.length) draw(now);
  drawEyeLayer(now);
  drawIntroIcon(now);
  requestAnimationFrame(frame);
}

// ---------- Input ----------
function cellAt(e) {
  const rect = canvas.getBoundingClientRect();
  const c = Math.floor((e.clientX - rect.left - PAD) / cell);
  const r = Math.floor((e.clientY - rect.top - PAD) / cell);
  return inBounds(r, c) ? { r, c } : null;
}

canvas.addEventListener('pointerdown', e => {
  e.preventDefault();
  lastInput = performance.now();
  hint = null;
  if (busy || state !== 'playing') return;
  const at = cellAt(e);
  if (!at || shogAt(at.r, at.c)) return;
  if (selected && Math.abs(selected.r - at.r) + Math.abs(selected.c - at.c) === 1) {
    const s = selected;
    selected = null;
    trySwap(s, at);
    return;
  }
  if (selected && selected.r === at.r && selected.c === at.c) { selected = null; return; }
  selected = at;
  drag = { start: at, x: e.clientX, y: e.clientY, axis: null, n: null, offset: 0 };
  canvas.setPointerCapture(e.pointerId);
});

// While dragging, the piece tracks the pointer along one axis (up to one cell) and its
// neighbour slides the opposite way. The swap commits when it locks into the neighbouring
// cell, or on release past halfway; otherwise both spring back.
const LOCK_IN = 0.98, COMMIT_ON_RELEASE = 0.5, AXIS_DEADZONE = 6;

function resetNeighbor() {
  if (!drag.n) return;
  const B = grid[drag.n.r][drag.n.c];
  B.x = drag.n.c; B.y = drag.n.r;
  drag.n = null;
}

function dragTo(e) {
  const dx = e.clientX - drag.x, dy = e.clientY - drag.y;
  if (!drag.axis && Math.max(Math.abs(dx), Math.abs(dy)) < AXIS_DEADZONE) return;
  // Pick the dominant axis; allow switching only while the piece is still near home.
  if (!drag.axis || drag.offset < 0.15) {
    const axis = Math.abs(dx) > Math.abs(dy) ? 'h' : 'v';
    if (axis !== drag.axis) { resetNeighbor(); drag.axis = axis; }
  }
  selected = null; hint = null;
  const s = drag.start, A = grid[s.r][s.c];
  const raw = (drag.axis === 'h' ? dx : dy) / cell, sign = Math.sign(raw);
  const n = drag.axis === 'h' ? { r: s.r, c: s.c + sign } : { r: s.r + sign, c: s.c };
  if (!sign || !inBounds(n.r, n.c) || shogAt(n.r, n.c)) {
    resetNeighbor();
    A.x = s.c; A.y = s.r; drag.offset = 0;
    return;
  }
  if (drag.n && (drag.n.r !== n.r || drag.n.c !== n.c)) resetNeighbor();
  drag.n = n;
  const off = Math.min(1, Math.abs(raw)), B = grid[n.r][n.c];
  drag.offset = off;
  A.x = s.c + (n.c - s.c) * off; A.y = s.r + (n.r - s.r) * off;
  B.x = n.c + (s.c - n.c) * off; B.y = n.r + (s.r - n.r) * off;
  if (off >= LOCK_IN) commitDrag();
}

function commitDrag() {
  const { start, n } = drag;
  drag = null;
  trySwap(start, n);
}

async function releaseDrag() {
  if (!drag) return;
  if (drag.n && drag.offset >= COMMIT_ON_RELEASE) { commitDrag(); return; }
  const s = drag.start, n = drag.n, A = grid[s.r][s.c];
  drag = null;
  if (!n && A.x === s.c && A.y === s.r) return; // plain tap: keep the selection
  busy = true;
  const anims = [tween(A, { x: s.c, y: s.r }, 120, ease.outBack)];
  if (n) anims.push(tween(grid[n.r][n.c], { x: n.c, y: n.r }, 120, ease.outBack));
  await Promise.all(anims);
  busy = false;
}

canvas.addEventListener('pointermove', e => { if (drag && !busy) dragTo(e); });
canvas.addEventListener('pointerup', releaseDrag);
canvas.addEventListener('pointercancel', releaseDrag);
window.addEventListener('keydown', e => { if (e.key === 'd' || e.key === 'D') previewDread = true; });
window.addEventListener('keyup', e => { if (e.key === 'd' || e.key === 'D') previewDread = false; });
window.addEventListener('blur', () => { previewDread = false; });

// ---------- Layout & boot ----------
function resize() {
  const r = wrap.getBoundingClientRect();
  // the largest whole-pixel cell that fits both ways
  cell = Math.max(20, Math.floor(Math.min((r.width - PAD * 2) / COLS, (r.height - PAD * 2) / ROWS)));
  boardW = cell * COLS + PAD * 2;
  boardH = cell * ROWS + PAD * 2;
  dpr = window.devicePixelRatio || 1;
  canvas.style.width = boardW + 'px';
  canvas.style.height = boardH + 'px';
  canvas.width = Math.round(boardW * dpr);
  canvas.height = Math.round(boardH * dpr);
  bgW = window.innerWidth || 400;
  bgH = window.innerHeight || 700;
  // The background is soft and full-screen; rendering it at Retina resolution costs 4x for no visible gain.
  bgDpr = Math.min(dpr, 1);
  $('introIcon').width = $('introIcon').height = Math.round(96 * dpr);
  bg.width = fg.width = Math.round(bgW * bgDpr);
  bg.height = fg.height = Math.round(bgH * bgDpr);
  buildMurk();
}
window.addEventListener('resize', resize);
resize();

cfg = levelConfig(level);
collected = new Array(NC).fill(0);
seedShoggoth(0);
generateBoard();
seedTaint(0);
buildGoals();
updateHUD();
ovAction = () => startLevel(level);
if (level > 1) $('ovText').textContent = `The seals weaken once more. Return to seal ${level}.`;
if (document.fonts && document.fonts.ready) document.fonts.ready.then(buildGoals).then(updateHUD);
requestAnimationFrame(frame);

// Debug/testing hook
window.cascade = {
  get grid() { return grid; }, get taint() { return taint; }, trySwap, findMove,
  get state() { return state; }, get busy() { return busy; }, get bolts() { return bolts; },
  get introOpen() { return introOpen; }, get seenIntros() { return seenIntros; },
};
})();
