/* The Alnadi Dispatch — Mohammed Alnadi's portfolio. No dependencies. */
(() => {
  'use strict';

  const reduce = matchMedia('(prefers-reduced-motion: reduce)').matches;

  /* ── Fit display lines to the width of their container ── */
  const fits = [...document.querySelectorAll('.fit')];
  function fitAll() {
    for (const el of fits) {
      const box = el.parentElement;
      box.style.fontSize = '100px';
      const w = el.getBoundingClientRect().width;
      const max = +el.dataset.max || Infinity;
      if (w > 0) box.style.fontSize = Math.min(max, 100 * box.clientWidth / w).toFixed(2) + 'px';
      else box.style.fontSize = '';
    }
  }
  fitAll();
  if (document.fonts && document.fonts.ready) document.fonts.ready.then(fitAll);
  addEventListener('resize', fitAll);

  /* ── Today's date in the dateline ── */
  const date = document.getElementById('date');
  if (date) {
    try {
      date.textContent = 'Edison, N.J., ' + new Date().toLocaleDateString('en-US',
        { weekday: 'long', year: 'numeric', month: 'long', day: 'numeric' });
    } catch (e) { /* keep the static dateline */ }
  }

  const year = document.getElementById('year');
  if (year) year.textContent = new Date().getFullYear();

  /* ── Fig. 1: the decision tree ──
     A few thousand nodes, generated, laid out and painted on one canvas.
     The finished tree is cached to an offscreen canvas; each frame only
     blits that cache and strokes the handful of lit paths on top. */
  const canvas = document.getElementById('tree');
  if (!canvas || !canvas.getContext) return;

  const ctx = canvas.getContext('2d');
  const readout = document.getElementById('tree-readout');
  const RED = '#c4161c';
  const INK = '#151515';
  const PAPER = '#efede7';
  const MAX_DEPTH = 13;

  let W = 0, H = 0, dpr = 1;
  let T = null;                 // the tree
  let base = null, bctx = null; // cached full render
  let seed = 4;
  let growing = false, growStart = 0;
  let hover = -1;
  let pulses = [], lastPulse = 0;
  let onScreen = true, raf = 0;

  function rng(a) {
    return () => {
      a |= 0; a = a + 0x6D2B79F5 | 0;
      let t = Math.imul(a ^ a >>> 15, 1 | a);
      t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
      return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
  }

  function build(target, s) {
    const r = rng(s);
    const parent = new Int32Array(target).fill(-1);
    const depth = new Uint8Array(target);
    const kids = new Array(target);
    for (let i = 0; i < target; i++) kids[i] = [];

    // Grow from a random open node each step, leaning toward shallower ones
    // so the tree is bushy rather than stringy.
    const open = [0];
    let n = 1;
    while (n < target && open.length) {
      let i = (r() * open.length) | 0;
      const j = (r() * open.length) | 0;
      if (depth[open[j]] < depth[open[i]] && r() < 0.7) i = j;
      const p = open[i];
      open[i] = open[open.length - 1];
      open.pop();
      if (depth[p] >= MAX_DEPTH) continue;
      const k = Math.min(target - n, r() < 0.7 ? 2 : 3);
      for (let c = 0; c < k; c++) {
        const id = n++;
        parent[id] = p;
        depth[id] = depth[p] + 1;
        kids[p].push(id);
        open.push(id);
      }
    }

    // Tidy layout: leaves take consecutive slots, parents sit over their children.
    const x = new Float32Array(n);
    const size = new Int32Array(n).fill(1);
    let slots = 0, maxD = 0;
    (function walk(i) {
      if (depth[i] > maxD) maxD = depth[i];
      const k = kids[i];
      if (!k.length) { x[i] = slots++; return; }
      for (const c of k) { walk(c); size[i] += size[c]; }
      x[i] = (x[k[0]] + x[k[k.length - 1]]) / 2;
    })(0);

    const byDepth = Array.from({ length: maxD + 1 }, () => []);
    const leaves = [];
    for (let i = 0; i < n; i++) {
      byDepth[depth[i]].push(i);
      if (!kids[i].length) leaves.push(i);
    }
    return { target, n, parent, depth, kids, x, size, slots, maxD, byDepth, leaves,
             X: new Float32Array(n), Y: new Float32Array(n) };
  }

  function place() {
    const padX = Math.max(12, W * 0.025), top = 16, bottom = 12;
    const { n, x, depth, maxD, slots, X, Y } = T;
    for (let i = 0; i < n; i++) {
      X[i] = padX + (slots > 1 ? x[i] / (slots - 1) : 0.5) * (W - 2 * padX);
      Y[i] = top + Math.pow(depth[i] / maxD, 0.9) * (H - top - bottom);
    }
  }

  // Append the edge parent→i to the current path; t < 1 draws only the first part.
  function edge(c, i, t) {
    const p = T.parent[i];
    const x0 = T.X[p], y0 = T.Y[p], x3 = T.X[i], y3 = T.Y[i], my = (y0 + y3) / 2;
    c.moveTo(x0, y0);
    if (t >= 1) { c.bezierCurveTo(x0, my, x3, my, x3, y3); return; }
    const ay = y0 + (my - y0) * t;
    const bx = x0 + (x3 - x0) * t;
    const cy = my + (y3 - my) * t;
    const dx = x0 + (bx - x0) * t, dy = ay + (my - ay) * t;
    const ex = bx + (x3 - bx) * t, ey = my + (cy - my) * t;
    c.bezierCurveTo(x0, ay, dx, dy, dx + (ex - dx) * t, dy + (ey - dy) * t);
  }

  function paintTree(c, g) {
    const { byDepth, maxD, leaves, depth, X, Y } = T;
    c.clearRect(0, 0, W, H);
    c.lineCap = 'round';
    for (let d = 1; d <= maxD; d++) {
      const t = Math.min(1, g - (d - 1));
      if (t <= 0) break;
      c.beginPath();
      for (const i of byDepth[d]) edge(c, i, t);
      c.strokeStyle = 'rgba(21,21,21,' + (0.82 - 0.42 * d / maxD).toFixed(3) + ')';
      c.lineWidth = Math.max(0.6, 2.2 - d * 0.16);
      c.stroke();
    }
    c.fillStyle = INK;
    for (const i of leaves) if (g >= depth[i]) c.fillRect(X[i] - 1, Y[i] - 1, 2, 2);
    c.fillStyle = RED;
    c.fillRect(X[0] - 4.5, Y[0] - 4.5, 9, 9);
  }

  function blit() {
    ctx.save();
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.clearRect(0, 0, canvas.width, canvas.height);
    ctx.drawImage(base, 0, 0);
    ctx.restore();
  }

  function spawn(now) {
    const leaf = T.leaves[(Math.random() * T.leaves.length) | 0];
    const path = [];
    for (let i = leaf; i !== -1; i = T.parent[i]) path.push(i);
    path.reverse();
    pulses.push({ path, t0: now });
  }

  // One evaluation running root → leaf, then fading out.
  function drawPulse(p, now) {
    const pos = (now - p.t0) / 90;       // edges travelled
    const last = p.path.length - 1;
    const fade = pos > last ? 1 - (pos - last) / 8 : 1;
    if (fade <= 0) return false;
    const full = Math.min(last, Math.floor(pos));
    ctx.beginPath();
    for (let s = 1; s <= full; s++) edge(ctx, p.path[s], 1);
    if (full < last) edge(ctx, p.path[full + 1], pos - full);
    ctx.globalAlpha = 0.95 * fade;
    ctx.strokeStyle = RED;
    ctx.lineWidth = 1.8;
    ctx.stroke();
    if (pos >= last) {
      const i = p.path[last], s = 2.5 + 5 * fade;
      ctx.fillStyle = RED;
      ctx.fillRect(T.X[i] - s / 2, T.Y[i] - s / 2, s, s);
    }
    ctx.globalAlpha = 1;
    return true;
  }

  function drawHover() {
    const i = hover;
    if (i < 0) return;
    const { kids, parent, depth, size, X, Y } = T;

    ctx.beginPath();                         // everything below this node
    const stack = [i];
    while (stack.length) {
      const a = stack.pop();
      for (const c of kids[a]) { edge(ctx, c, 1); stack.push(c); }
    }
    ctx.strokeStyle = 'rgba(196,22,28,.45)';
    ctx.lineWidth = 1.1;
    ctx.stroke();

    ctx.beginPath();                         // the decision path back to the root
    for (let a = i; parent[a] !== -1; a = parent[a]) edge(ctx, a, 1);
    ctx.strokeStyle = RED;
    ctx.lineWidth = 2.6;
    ctx.stroke();

    ctx.fillStyle = RED;
    ctx.fillRect(X[i] - 4.5, Y[i] - 4.5, 9, 9);

    const below = size[i] - 1;
    const label = 'NODE ' + i + ' · DEPTH ' + depth[i] + ' · ' + (below ? below.toLocaleString() + ' BELOW' : 'LEAF');
    ctx.font = '600 12px "Barlow Condensed", "Arial Narrow", sans-serif';
    if ('letterSpacing' in ctx) ctx.letterSpacing = '0.8px';
    const tw = ctx.measureText(label).width + 14;
    let lx = X[i] + 12, ly = Y[i] - 26;
    if (lx + tw > W - 6) lx = X[i] - 12 - tw;
    if (lx < 6) lx = 6;
    if (ly < 4) ly = Y[i] + 10;
    ctx.fillStyle = INK;
    ctx.fillRect(lx, ly, tw, 20);
    ctx.fillStyle = PAPER;
    ctx.textBaseline = 'middle';
    ctx.fillText(label, lx + 7, ly + 10.5);
  }

  function frame(now) {
    raf = 0;
    if (!T) return;
    if (growing) {
      const k = Math.min(1, (now - growStart) / 1900);
      paintTree(ctx, (1 - Math.pow(1 - k, 2.4)) * T.maxD);
      if (k >= 1) growing = false;
    } else {
      blit();
      if (!reduce) {
        if (now - lastPulse > 620 && pulses.length < 5) { spawn(now); lastPulse = now; }
        pulses = pulses.filter((p) => drawPulse(p, now));
      }
      drawHover();
    }
    if (growing || (!reduce && onScreen)) kick();
  }
  function kick() { if (!raf) raf = requestAnimationFrame(frame); }

  function setup(regen) {
    const r = canvas.getBoundingClientRect();
    const w = Math.round(r.width), h = Math.round(r.height);
    if (!w || !h) return;
    if (!regen && w === W && h === H) return;
    W = w; H = h;
    dpr = Math.min(window.devicePixelRatio || 1, 2);
    canvas.width = W * dpr; canvas.height = H * dpr;
    if (!base) { base = document.createElement('canvas'); bctx = base.getContext('2d'); }
    base.width = canvas.width; base.height = canvas.height;
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    bctx.setTransform(dpr, 0, 0, dpr, 0, 0);

    const target = W < 520 ? 900 : 2400;
    const t0 = performance.now();
    if (regen || !T || T.target !== target) { T = build(target, seed); regen = true; }
    place();
    paintTree(bctx, T.maxD);
    const ms = performance.now() - t0;

    if (regen) {
      hover = -1; pulses = [];
      if (readout) {
        readout.textContent = 'A ' + T.n.toLocaleString() + '-node decision tree, built and painted in your browser in ' +
          (ms < 10 ? ms.toFixed(1) : Math.round(ms)) + ' ms.';
      }
      if (!reduce) { growing = true; growStart = performance.now(); }
    }
    kick();
  }

  canvas.addEventListener('pointermove', (e) => {
    if (!T || growing) return;
    const r = canvas.getBoundingClientRect();
    const mx = e.clientX - r.left, my = e.clientY - r.top;
    let best = -1, bd = 34 * 34;
    for (let i = 0; i < T.n; i++) {
      const dx = T.X[i] - mx, dy = T.Y[i] - my, d = dx * dx + dy * dy;
      if (d < bd) { bd = d; best = i; }
    }
    if (best !== hover) { hover = best; kick(); }
  });
  canvas.addEventListener('pointerleave', () => { if (hover !== -1) { hover = -1; kick(); } });

  const regrow = document.getElementById('regrow');
  if (regrow) regrow.addEventListener('click', () => { seed = (Math.random() * 1e9) | 0; setup(true); });

  if ('ResizeObserver' in window) {
    let ro = 0;
    new ResizeObserver(() => { cancelAnimationFrame(ro); ro = requestAnimationFrame(() => setup(false)); }).observe(canvas);
  } else {
    addEventListener('resize', () => setup(false));
  }
  if ('IntersectionObserver' in window) {
    new IntersectionObserver((entries) => {
      onScreen = entries[0].isIntersecting;
      if (onScreen) kick();
    }).observe(canvas);
  }

  setup(true);
})();
