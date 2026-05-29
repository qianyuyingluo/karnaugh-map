// ═══════════════════════════════════════════════════════
// 4×4 Karnaugh Map — Q₃Q₂Q₁Q₀
// Quine-McCluskey simplification, manual grouping, KaTeX rendering
// ═══════════════════════════════════════════════════════

// ── Constants ──────────────────────────────────────────
const GCOLORS = ['#f38ba8','#a6e3a1','#fab387','#cba6f7','#94e2d5','#89dceb','#f2cdcd','#b4befe'];
const ROW_GRAY = [0, 1, 3, 2]; // Q₃Q₂ Gray: 00,01,11,10
const COL_GRAY = [0, 1, 3, 2]; // Q₁Q₀ Gray

function rcToMinterm(r, c) { return ROW_GRAY[r] * 4 + COL_GRAY[c]; }
function mintermToRC(m) {
  const rv = (m >> 2) & 3, cv = m & 3;
  return [ROW_GRAY.indexOf(rv), COL_GRAY.indexOf(cv)];
}
function mintermToBin(m) { return m.toString(2).padStart(4, '0'); }

// ── State ──────────────────────────────────────────────
function createKMap(name) {
  return {
    name,
    cells: new Array(16).fill(0),
    groups: [],
    mode: 'edit',
    groupStart: null,
    hoverCells: new Set(),
    _autoExpr: null,
  };
}

const state = {
  kmaps: [createKMap('卡诺图 1')],
  activeIdx: 0,
};
function active() { return state.kmaps[state.activeIdx]; }

// ═══════════════════════════════════════════════════════
// Quine-McCluskey Algorithm
// ═══════════════════════════════════════════════════════
function countOnes(bin) { let n = 0; for (const ch of bin) if (ch === '1') n++; return n; }

function differByOne(a, b) {
  let diff = 0, pos = -1;
  for (let i = 0; i < a.length; i++) { if (a[i] !== b[i]) { diff++; pos = i; } }
  return diff === 1 ? pos : -1;
}
function combineTerms(a, b, pos) { return a.substring(0, pos) + '-' + a.substring(pos + 1); }

function piToMinterms(pi) {
  const dashes = [];
  for (let i = 0; i < pi.length; i++) if (pi[i] === '-') dashes.push(i);
  const res = [];
  for (let i = 0; i < (1 << dashes.length); i++) {
    const arr = pi.split('');
    for (let j = 0; j < dashes.length; j++) arr[dashes[j]] = (i >> j) & 1 ? '1' : '0';
    res.push(parseInt(arr.join(''), 2));
  }
  return res;
}

function findPrimeImplicants(minterms, dontcares) {
  const allBin = [
    ...minterms.map(m => mintermToBin(m)),
    ...dontcares.map(m => mintermToBin(m))
  ];
  const dcSet = new Set(dontcares.map(m => mintermToBin(m)));

  const groups = new Map();
  for (const t of allBin) {
    const c = countOnes(t);
    if (!groups.has(c)) groups.set(c, []);
    groups.get(c).push({ term: t, used: false });
  }

  let cur = groups;
  const primes = [];

  while (true) {
    const next = new Map();
    const keys = [...cur.keys()].sort((a, b) => a - b);
    for (let ki = 0; ki < keys.length - 1; ki++) {
      const g1 = cur.get(keys[ki]);
      const g2 = cur.get(keys[ki + 1]);
      if (!g1 || !g2) continue;
      for (const t1 of g1) {
        for (const t2 of g2) {
          const dp = differByOne(t1.term, t2.term);
          if (dp !== -1) {
            const cmb = combineTerms(t1.term, t2.term, dp);
            if (!next.has(cmb)) next.set(cmb, []);
            if (!next.get(cmb).some(x => x.term === cmb)) {
              next.get(cmb).push({ term: cmb, used: false });
            }
            t1.used = t2.used = true;
          }
        }
      }
    }
    for (const terms of cur.values())
      for (const t of terms)
        if (!t.used && !dcSet.has(t.term)) primes.push(t.term);
    if (next.size === 0) break;
    cur = next;
  }
  for (const terms of cur.values())
    for (const t of terms)
      if (!dcSet.has(t.term)) primes.push(t.term);
  return [...new Set(primes)];
}

function piCovers(pi, minterm) {
  const bin = mintermToBin(minterm);
  for (let i = 0; i < 4; i++) if (pi[i] !== '-' && pi[i] !== bin[i]) return false;
  return true;
}

function findMinimumCover(minterms, primeImplicants) {
  if (minterms.length === 0) return [];

  const cov = primeImplicants
    .map(pi => ({ pi, covers: minterms.filter(m => piCovers(pi, m)) }))
    .filter(c => c.covers.length > 0);
  if (cov.length === 0) return [];

  for (const m of minterms) {
    const covering = cov.filter(c => c.covers.includes(m));
    if (covering.length === 1) covering[0].essential = true;
  }

  const essential = [...new Set(cov.filter(c => c.essential).map(c => c.pi))];
  const covered = new Set();
  for (const c of cov.filter(c => c.essential))
    for (const m of c.covers) covered.add(m);

  const remaining = minterms.filter(m => !covered.has(m));
  if (remaining.length === 0) return essential;

  const remainCov = cov
    .filter(c => !c.essential)
    .map(c => ({ pi: c.pi, covers: c.covers.filter(m => remaining.includes(m)) }))
    .filter(c => c.covers.length > 0);

  let best = null;
  (function search(idx, selected, covSet) {
    if (best !== null && selected.length >= best.length) return;
    if (covSet.size === remaining.length) { best = [...selected]; return; }
    if (idx >= remainCov.length) return;
    const item = remainCov[idx];
    const newCov = new Set(covSet);
    for (const m of item.covers) newCov.add(m);
    if (newCov.size > covSet.size) search(idx + 1, [...selected, item.pi], newCov);
    search(idx + 1, selected, covSet);
  })(0, [], new Set());

  if (best) return [...new Set([...essential, ...best])];

  // Greedy fallback
  const res = [...essential];
  const covSet = new Set(covered);
  const pool = remainCov.map(c => ({ ...c }));
  while (remaining.some(m => !covSet.has(m))) {
    pool.sort((a, b) => b.covers.filter(m => !covSet.has(m)).length - a.covers.filter(m => !covSet.has(m)).length);
    const top = pool.shift();
    if (!top) break;
    res.push(top.pi);
    for (const m of top.covers) covSet.add(m);
  }
  return [...new Set(res)];
}

function piToExpr(pi) {
  const vars = ['Q3', 'Q2', 'Q1', 'Q0'];
  const parts = [];
  for (let i = 0; i < 4; i++) {
    if (pi[i] === '0') parts.push(vars[i] + "'");
    else if (pi[i] === '1') parts.push(vars[i]);
  }
  return parts.length === 0 ? '1' : parts.join('·');
}

function simplify(km) {
  const ones = [], dcs = [];
  km.cells.forEach((v, i) => {
    if (v === 1) ones.push(i);
    else if (v === 'x') dcs.push(i);
  });
  if (ones.length === 0) return '0';
  if (ones.length === 16 || ones.length + dcs.length === 16) return '1';

  const pis = findPrimeImplicants(ones, dcs);
  const cover = findMinimumCover(ones, pis);
  return cover.length === 0 ? '0' : cover.map(piToExpr).join(' + ');
}

// ═══════════════════════════════════════════════════════
// KaTeX Rendering
// ═══════════════════════════════════════════════════════
function toKatex(expr) {
  if (!expr || expr === '0') return '0';
  if (expr === '1') return '1';

  let latex = expr;

  // 1. Complemented variables → overline (must run before bare variables)
  latex = latex.replace(/Q3'/g, '\\overline{Q_3}');
  latex = latex.replace(/Q2'/g, '\\overline{Q_2}');
  latex = latex.replace(/Q1'/g, '\\overline{Q_1}');
  latex = latex.replace(/Q0'/g, '\\overline{Q_0}');

  // 2. Bare variables → subscript
  latex = latex.replace(/Q3/g, 'Q_3');
  latex = latex.replace(/Q2/g, 'Q_2');
  latex = latex.replace(/Q1/g, 'Q_1');
  latex = latex.replace(/Q0/g, 'Q_0');

  // 3. AND: dot → \cdot
  latex = latex.replace(/·/g, ' \\cdot ');

  // 4. Prevent merged overlines: add \, spacer between adjacent \overline{...} blocks
  latex = latex.replace(/(\\overline\{[^}]+\})\s*(\\overline\{)/g, '$1 \\, $2');

  // 5. Remove warning markers
  latex = latex.replace(/⚠️.*$/, '').trim();

  return latex;
}

function renderKatex() {
  const el = document.getElementById('katexDisplay');
  const expr = document.getElementById('exprText').textContent.trim();

  if (!expr) {
    el.innerHTML = '<span class="katex-placeholder">点击自动化简或在上方输入表达式</span>';
    return;
  }

  const latex = toKatex(expr);
  try {
    katex.render(latex, el, {
      displayMode: true,
      throwOnError: false,
      trust: true,
    });
  } catch (e) {
    el.innerHTML = '<span class="katex-error">渲染错误：' + e.message + '</span>';
  }
}

// ═══════════════════════════════════════════════════════
// Group Helpers
// ═══════════════════════════════════════════════════════
function groupCellsToExpr(cells) {
  const arr = [...cells];
  if (arr.length === 0) return '1';
  const vars = ['Q3', 'Q2', 'Q1', 'Q0'];
  const first = mintermToBin(arr[0]);
  const common = first.split('');
  for (const m of arr) {
    const bin = mintermToBin(m);
    for (let i = 0; i < 4; i++) if (common[i] !== bin[i]) common[i] = '-';
  }
  const parts = [];
  for (let i = 0; i < 4; i++) {
    if (common[i] === '0') parts.push(vars[i] + "'");
    else if (common[i] === '1') parts.push(vars[i]);
  }
  return parts.length === 0 ? '1' : parts.join('·');
}

function allGroupsToExpr(km) {
  if (km.groups.length === 0) return '';
  const ones = new Set();
  km.cells.forEach((v, i) => { if (v === 1) ones.add(i); });
  const covered = new Set();
  const terms = km.groups.map(g => {
    for (const c of g.cells) covered.add(c);
    return groupCellsToExpr(g.cells);
  });
  const allCovered = [...ones].every(o => covered.has(o));
  return terms.join(' + ') + (allCovered ? '' : '  ⚠️');
}

function isValidKMapGroup(cellSet) {
  const n = cellSet.size;
  if (n === 0 || (n & (n - 1)) !== 0) return false;
  const arr = [...cellSet];
  const first = mintermToBin(arr[0]);
  const varying = [false, false, false, false];
  for (const m of arr) {
    const bin = mintermToBin(m);
    for (let i = 0; i < 4; i++) if (bin[i] !== first[i]) varying[i] = true;
  }
  const vc = varying.filter(Boolean).length;
  if (n !== (1 << vc)) return false;
  const gen = new Set(arr);
  for (let i = 0; i < 16; i++) {
    const tb = mintermToBin(i);
    let ok = true;
    for (let j = 0; j < 4; j++) if (!varying[j] && tb[j] !== first[j]) ok = false;
    if (ok && !gen.has(i)) return false;
  }
  return true;
}

// ═══════════════════════════════════════════════════════
// Cell Selection for Manual Grouping
// ═══════════════════════════════════════════════════════
function getCellsInRect(r1, r2, c1, c2, rWrap, cWrap) {
  const cells = new Set();
  let rows, cols;

  if (!rWrap) {
    const a = Math.min(r1, r2), b = Math.max(r1, r2);
    rows = []; for (let r = a; r <= b; r++) rows.push(r);
  } else {
    rows = [];
    for (let r = r1; r < 4; r++) rows.push(r);
    for (let r = 0; r <= r2; r++) rows.push(r);
  }
  if (!cWrap) {
    const a = Math.min(c1, c2), b = Math.max(c1, c2);
    cols = []; for (let c = a; c <= b; c++) cols.push(c);
  } else {
    cols = [];
    for (let c = c1; c < 4; c++) cols.push(c);
    for (let c = 0; c <= c2; c++) cols.push(c);
  }
  for (const r of rows) for (const c of cols) cells.add(rcToMinterm(r, c));
  return cells;
}

function getBestGroup(startM, endM) {
  if (startM === endM) return new Set([startM]);

  const [sr, sc] = mintermToRC(startM);
  const [er, ec] = mintermToRC(endM);

  const tries = [
    [sr, er, sc, ec, false, false],
    [er, sr, sc, ec, true,  false],
    [sr, er, ec, sc, false, true ],
    [er, sr, ec, sc, true,  true ],
  ];

  let best = null;
  for (const [r1, r2, c1, c2, rw, cw] of tries) {
    const cells = getCellsInRect(r1, r2, c1, c2, rw, cw);
    if (isValidKMapGroup(cells)) {
      if (best === null || cells.size < best.size) best = cells;
    }
  }

  // Also try exact pair (for 2-cell edge-wrap groups)
  if (startM !== endM) {
    const pair = new Set([startM, endM]);
    if (isValidKMapGroup(pair)) {
      if (best === null || 2 < best.size) best = pair;
    }
  }

  return best;
}

// ═══════════════════════════════════════════════════════
// Visual Rectangles for Overlay Drawing
// ═══════════════════════════════════════════════════════
function getVisualRects(cellSet) {
  const arr = [...cellSet];
  const rcs = arr.map(m => mintermToRC(m));
  const rows = [...new Set(rcs.map(rc => rc[0]))].sort((a, b) => a - b);
  const cols = [...new Set(rcs.map(rc => rc[1]))].sort((a, b) => a - b);

  function contiguousGroups(sorted) {
    if (sorted.length === 0) return [];
    const groups = [];
    let cur = [sorted[0]];
    for (let i = 1; i < sorted.length; i++) {
      if (sorted[i] === sorted[i - 1] + 1) cur.push(sorted[i]);
      else { groups.push(cur); cur = [sorted[i]]; }
    }
    groups.push(cur);
    return groups;
  }

  const rowGrps = contiguousGroups(rows);
  const colGrps = contiguousGroups(cols);
  const rects = [];
  for (const rg of rowGrps)
    for (const cg of colGrps)
      rects.push({ r0: rg[0], r1: rg[rg.length - 1], c0: cg[0], c1: cg[cg.length - 1] });
  return rects;
}

// ═══════════════════════════════════════════════════════
// Render
// ═══════════════════════════════════════════════════════
function renderAll() {
  renderTabs();
  renderKMap();
  renderExpr();
  renderKatex();
  renderGroupList();
}

function renderTabs() {
  const bar = document.getElementById('tabBar');
  const addBtn = document.getElementById('tabAdd');
  bar.querySelectorAll('.tab').forEach(t => t.remove());
  state.kmaps.forEach((km, i) => {
    const tab = document.createElement('div');
    tab.className = 'tab' + (i === state.activeIdx ? ' active' : '');
    tab.dataset.idx = i;
    tab.innerHTML = `<span>${km.name}</span>`;
    if (state.kmaps.length > 1) {
      const cls = document.createElement('button');
      cls.className = 'tab-close'; cls.textContent = '×'; cls.title = '关闭';
      cls.onclick = e => { e.stopPropagation(); closeTab(i); };
      tab.appendChild(cls);
    }
    tab.onclick = () => { state.activeIdx = i; renderAll(); };
    bar.insertBefore(tab, addBtn);
  });
}

function renderKMap() {
  const km = active();
  const panel = document.getElementById('leftPanel');
  panel.innerHTML = '';

  const container = document.createElement('div');
  container.className = 'kmap-container';
  container.innerHTML = `<div class="kmap-title">${km.name} <span class="tag">Q₃Q₂ \\ Q₁Q₀</span></div>`;

  const wrapper = document.createElement('div');
  wrapper.className = 'grid-wrapper';
  wrapper.id = 'gridWrapper';

  const grid = document.createElement('div');
  grid.className = 'kmap-grid';

  // Corner label
  const corner = document.createElement('div');
  corner.className = 'corner';
  corner.innerHTML = 'Q₃Q₂↓<br>Q₁Q₀→';
  corner.style.fontSize = '10px';
  grid.appendChild(corner);

  // Column headers (Q₁Q₀ Gray)
  for (const cl of ['00', '01', '11', '10']) {
    const h = document.createElement('div');
    h.className = 'h-label'; h.textContent = cl;
    grid.appendChild(h);
  }

  // Rows (Q₃Q₂ Gray)
  const rowLabels = ['00', '01', '11', '10'];
  for (let r = 0; r < 4; r++) {
    const rl = document.createElement('div');
    rl.className = 'v-label'; rl.textContent = rowLabels[r];
    grid.appendChild(rl);

    for (let c = 0; c < 4; c++) {
      const m = rcToMinterm(r, c);
      const v = km.cells[m];
      const cell = document.createElement('div');
      cell.className = 'cell v' + (v === 'x' ? 'x' : v);
      cell.dataset.r = r;
      cell.dataset.c = c;
      cell.dataset.m = m;
      cell.innerHTML = `<span class="val">${v === 'x' ? 'X' : v}</span><span class="idx">m${m}</span>`;
      cell.addEventListener('mousedown', e => onCellDown(e, cell));
      cell.addEventListener('mouseenter', e => onCellEnter(e, cell));
      cell.addEventListener('mouseup', e => onCellUp(e, cell));
      cell.addEventListener('contextmenu', e => e.preventDefault());
      grid.appendChild(cell);
    }
  }

  wrapper.appendChild(grid);

  // Overlay container for group rectangles
  const ov = document.createElement('div');
  ov.className = 'group-overlays';
  ov.style.cssText = 'position:absolute;top:0;left:0;width:100%;height:100%;pointer-events:none;z-index:0';
  wrapper.appendChild(ov);

  container.appendChild(wrapper);

  const caption = document.createElement('div');
  caption.className = 'caption';
  caption.textContent = '行列 Gray 00→01→11→10 | 点击格子 0→1→X→0 | 圈选模式拖拽画圈';
  container.appendChild(caption);

  panel.appendChild(container);

  requestAnimationFrame(() => drawOverlays(wrapper, km));
}

function drawOverlays(wrapper, km) {
  const ov = wrapper.querySelector('.group-overlays');
  ov.innerHTML = '';

  const grid = wrapper.querySelector('.kmap-grid');
  const wr = wrapper.getBoundingClientRect();
  const cells = grid.querySelectorAll('.cell');

  const posMap = {};
  cells.forEach(cell => {
    const r = parseInt(cell.dataset.r);
    const c = parseInt(cell.dataset.c);
    const rect = cell.getBoundingClientRect();
    posMap[`${r},${c}`] = {
      left: rect.left - wr.left,
      top: rect.top - wr.top,
      w: rect.width,
      h: rect.height
    };
  });

  // Draw each group's rectangles
  km.groups.forEach(g => {
    const rects = getVisualRects(g.cells);
    rects.forEach(rect => {
      let ml = Infinity, mt = Infinity, mr = -Infinity, mb = -Infinity;
      for (let r = rect.r0; r <= rect.r1; r++) {
        for (let c = rect.c0; c <= rect.c1; c++) {
          const p = posMap[`${r},${c}`];
          if (p) {
            ml = Math.min(ml, p.left);
            mt = Math.min(mt, p.top);
            mr = Math.max(mr, p.left + p.w);
            mb = Math.max(mb, p.top + p.h);
          }
        }
      }
      if (ml === Infinity) return;
      const div = document.createElement('div');
      div.style.cssText = `
        position:absolute;
        left:${ml - 3}px; top:${mt - 3}px;
        width:${mr - ml + 6}px; height:${mb - mt + 6}px;
        border:3px solid ${g.color};
        background:${g.color}22;
        border-radius:8px;
        pointer-events:none; z-index:1;
      `;
      ov.appendChild(div);
    });
  });

  // Preview hover cells in group mode
  if (km.mode === 'group' && km.groupStart !== null) {
    for (const m of km.hoverCells) {
      const [r, c] = mintermToRC(m);
      const p = posMap[`${r},${c}`];
      if (p) {
        const div = document.createElement('div');
        div.style.cssText = `
          position:absolute;
          left:${p.left - 1}px; top:${p.top - 1}px;
          width:${p.w + 2}px; height:${p.h + 2}px;
          border:2px dashed #f5c2e7;
          background:#f5c2e733;
          border-radius:6px;
          pointer-events:none; z-index:2;
        `;
        ov.appendChild(div);
      }
    }
  }
}

function renderExpr() {
  const km = active();
  const el = document.getElementById('exprText');
  if (km.groups.length > 0) {
    el.textContent = allGroupsToExpr(km);
  } else if (km._autoExpr !== null) {
    el.textContent = km._autoExpr;
  } else {
    el.textContent = '';
  }
}

function renderGroupList() {
  const km = active();
  document.getElementById('groupCount').textContent = km.groups.length;
  const list = document.getElementById('groupList');
  if (km.groups.length === 0) {
    list.innerHTML = '<div style="color:#6c7086;font-size:13px;padding:4px 0">暂无圈选 — 请手动圈选或点击自动化简</div>';
    return;
  }
  const ones = new Set();
  km.cells.forEach((v, i) => { if (v === 1) ones.add(i); });
  const covered = new Set();
  km.groups.forEach(g => { for (const c of g.cells) covered.add(c); });

  list.innerHTML = km.groups.map((g, i) => {
    const hasZero = [...g.cells].some(c => km.cells[c] === 0);
    const onlyX = [...g.cells].every(c => km.cells[c] === 'x');
    return `
    <div class="group-item" style="${onlyX ? 'opacity:0.5' : ''}">
      <span class="color-dot" style="background:${g.color}"></span>
      <span>${g.cells.size}格: ${groupCellsToExpr(g.cells)}</span>
      ${hasZero ? '<span class="warn" title="圈选了0值格子">⚠️</span>' : ''}
      ${onlyX ? '<span style="color:#6c7086;font-size:11px">(仅X)</span>' : ''}
      <button class="del-btn" onclick="deleteGroup(${i})" title="删除">×</button>
    </div>`;
  }).join('');

  const allCovered = [...ones].every(o => covered.has(o));
  if (!allCovered && ones.size > 0) {
    list.innerHTML += '<div style="color:#f38ba8;font-size:12px;margin-top:4px">⚠️ 当前圈选未覆盖所有 1</div>';
  }
}

function deleteGroup(idx) {
  active().groups.splice(idx, 1);
  renderAll();
}

// ═══════════════════════════════════════════════════════
// Event Handlers
// ═══════════════════════════════════════════════════════
function onCellDown(e, cell) {
  const km = active();
  const m = parseInt(cell.dataset.m);

  if (km.mode === 'edit') {
    e.preventDefault();
    const cur = km.cells[m];
    km.cells[m] = cur === 0 ? 1 : cur === 1 ? 'x' : 0;
    km.groups = [];
    km._autoExpr = null;
    renderAll();
  } else if (km.mode === 'group') {
    e.preventDefault();
    km.groupStart = m;
    km.hoverCells = new Set([m]);
    renderKMap();
    renderGroupList();
    renderKatex();
  }
}

function onCellEnter(e, cell) {
  const km = active();
  if (km.mode !== 'group' || km.groupStart === null) return;
  const m = parseInt(cell.dataset.m);
  const best = getBestGroup(km.groupStart, m);
  km.hoverCells = best || new Set([km.groupStart, m]);
  const wrapper = document.getElementById('gridWrapper');
  if (wrapper) drawOverlays(wrapper, km);
}

function onCellUp(e, cell) {
  const km = active();
  if (km.mode !== 'group' || km.groupStart === null) return;
  const m = parseInt(cell.dataset.m);
  const best = getBestGroup(km.groupStart, m);
  if (best && isValidKMapGroup(best)) {
    const color = GCOLORS[km.groups.length % GCOLORS.length];
    km.groups.push({ cells: new Set(best), color });
  }
  km.groupStart = null;
  km.hoverCells = new Set();
  km._autoExpr = null;
  renderAll();
}

// Global mouseup fallback (in case released outside grid)
document.addEventListener('mouseup', () => {
  let changed = false;
  for (const km of state.kmaps) {
    if (km.groupStart !== null) {
      km.groupStart = null;
      km.hoverCells = new Set();
      changed = true;
    }
  }
  if (changed) renderAll();
});

// ═══════════════════════════════════════════════════════
// Tab Management
// ═══════════════════════════════════════════════════════
function closeTab(idx) {
  if (state.kmaps.length <= 1) return;
  state.kmaps.splice(idx, 1);
  if (state.activeIdx >= state.kmaps.length) state.activeIdx = state.kmaps.length - 1;
  renderAll();
}

document.getElementById('tabAdd').onclick = () => {
  state.kmaps.push(createKMap('卡诺图 ' + (state.kmaps.length + 1)));
  state.activeIdx = state.kmaps.length - 1;
  renderAll();
};

// ═══════════════════════════════════════════════════════
// Mode Switch
// ═══════════════════════════════════════════════════════
document.getElementById('modeSwitch').addEventListener('click', e => {
  if (!e.target.classList.contains('mode-btn')) return;
  const km = active();
  km.mode = e.target.dataset.mode;
  km.groupStart = null;
  km.hoverCells = new Set();
  document.querySelectorAll('#modeSwitch .mode-btn').forEach(b => b.classList.remove('active'));
  e.target.classList.add('active');
  document.getElementById('modeHint').textContent =
    km.mode === 'edit'
      ? '点击格子切换 0 → 1 → X → 0（修改取值时清空圈选）'
      : '在格子上按住拖拽来圈选卡诺圈（自动识别有效矩形，支持环绕）';
  renderAll();
});

// ═══════════════════════════════════════════════════════
// Auto Simplify
// ═══════════════════════════════════════════════════════
document.getElementById('btnAutoSimplify').onclick = () => {
  const km = active();
  const expr = simplify(km);
  km._autoExpr = expr;

  // Generate visual groups from prime implicants
  const ones = [], dcs = [];
  km.cells.forEach((v, i) => {
    if (v === 1) ones.push(i);
    else if (v === 'x') dcs.push(i);
  });

  km.groups = [];
  if (ones.length > 0 && ones.length < 16 && ones.length + dcs.length < 16) {
    const pis = findPrimeImplicants(ones, dcs);
    const cover = findMinimumCover(ones, pis);
    km.groups = cover.map((pi, i) => ({
      cells: new Set(piToMinterms(pi).filter(m => km.cells[m] === 1 || km.cells[m] === 'x')),
      color: GCOLORS[i % GCOLORS.length]
    }));
  }

  renderAll();
};

// ═══════════════════════════════════════════════════════
// Clear / Reset
// ═══════════════════════════════════════════════════════
document.getElementById('btnClearGroups').onclick = () => {
  active().groups = [];
  active()._autoExpr = null;
  renderAll();
};
document.getElementById('btnClearAll').onclick = () => {
  const km = active();
  km.cells.fill(0);
  km.groups = [];
  km._autoExpr = null;
  renderAll();
};

// ═══════════════════════════════════════════════════════
// Expression Input Buttons
// ═══════════════════════════════════════════════════════
function getTextNodes(node) {
  const walker = document.createTreeWalker(node, NodeFilter.SHOW_TEXT, null);
  const nodes = [];
  while (walker.nextNode()) nodes.push(walker.currentNode);
  return nodes;
}

function insertAtCursor(text) {
  const el = document.getElementById('exprText');
  el.focus();

  // Clear auto state
  const km = active();
  km._autoExpr = null;
  km.groups = [];

  const sel = window.getSelection();
  if (!sel.rangeCount) {
    el.textContent += text;
    renderKatex();
    return;
  }

  const rng = sel.getRangeAt(0);
  if (rng.startContainer === el || rng.startContainer.parentNode === el) {
    rng.deleteContents();
    const tn = document.createTextNode(text);
    rng.insertNode(tn);
    rng.setStartAfter(tn);
    rng.collapse(true);
    sel.removeAllRanges();
    sel.addRange(rng);
  } else {
    el.textContent += text;
    const nr = document.createRange();
    nr.selectNodeContents(el);
    nr.collapse(false);
    sel.removeAllRanges();
    sel.addRange(nr);
  }
  renderKatex();
}

document.querySelectorAll('.ins-btn').forEach(btn => {
  btn.onclick = () => insertAtCursor(btn.dataset.text);
});

document.getElementById('btnBackspace').onclick = () => {
  const el = document.getElementById('exprText');
  el.focus();
  const sel = window.getSelection();
  if (!sel.rangeCount) return;
  const rng = sel.getRangeAt(0);
  if (!rng.collapsed) {
    rng.deleteContents();
  } else if (rng.startOffset > 0 && rng.startContainer.nodeType === 3) {
    rng.setStart(rng.startContainer, rng.startOffset - 1);
    rng.deleteContents();
  }
  renderKatex();
};

document.getElementById('btnClearExpr').onclick = () => {
  document.getElementById('exprText').textContent = '';
  active()._autoExpr = null;
  active().groups = [];
  renderAll();
};

// Live KaTeX rendering while user types
document.getElementById('exprText').addEventListener('input', () => {
  const km = active();
  km._autoExpr = document.getElementById('exprText').textContent;
  renderKatex();
});

// ═══════════════════════════════════════════════════════
// Init
// ═══════════════════════════════════════════════════════
renderAll();
