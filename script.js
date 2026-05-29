// ═══════════════════════════════════════════════════════
// N×M Karnaugh Map — Quine-McCluskey + Manual Grouping + KaTeX
// Variable names customizable (default Q₃Q₂Q₁Q₀)
// ═══════════════════════════════════════════════════════

const GCOLORS = ['#f38ba8','#a6e3a1','#fab387','#cba6f7','#94e2d5','#89dceb','#f2cdcd','#b4befe'];

// Unicode subscript digits
const SUB = ['₀','₁','₂','₃','₄','₅','₆','₇','₈','₉'];

function defaultVarNames(varCount) {
  // MSB → LSB: Qₙ₋₁ ... Q₀
  const names = [];
  for (let i = varCount - 1; i >= 0; i--) {
    names.push('Q' + SUB[i]);
  }
  return names;
}

// ── Gray Code ──────────────────────────────────────────
function grayCode(bits) {
  if (bits === 0) return [0];
  const n = 1 << bits;
  const g = [];
  for (let i = 0; i < n; i++) g.push(i ^ (i >> 1));
  return g;
}
function grayIndex(bits, grayVal) {
  let v = grayVal;
  let mask = v >> 1;
  while (mask) { v ^= mask; mask >>= 1; }
  return v;
}

// ── K-Map layout for N variables ───────────────────────
function getLayout(varCount) {
  const rowVars = varCount <= 2 ? 1 : varCount <= 3 ? 1 : 2;
  const layerVars = varCount <= 4 ? 0 : varCount - 4;
  const colVars = varCount - rowVars - layerVars;
  return { rowVars, colVars, layerVars, rows: 1 << rowVars, cols: 1 << colVars, layers: 1 << layerVars };
}

function rcToMinterm(r, c, layer, layout) {
  const { rowVars, colVars, layerVars } = layout;
  const rowGray = grayCode(rowVars)[r];
  const colGray = grayCode(colVars)[c];
  const layerGray = layerVars > 0 ? grayCode(layerVars)[layer] : 0;
  return (layerGray << (rowVars + colVars)) | (rowGray << colVars) | colGray;
}

function mintermToRC(m, layout) {
  const { rowVars, colVars, layerVars } = layout;
  const colGray = m & ((1 << colVars) - 1);
  const rowGray = (m >> colVars) & ((1 << rowVars) - 1);
  const layerGray = layerVars > 0 ? (m >> (rowVars + colVars)) & ((1 << layerVars) - 1) : 0;
  return {
    r: grayIndex(rowVars, rowGray),
    c: grayIndex(colVars, colGray),
    layer: layerVars > 0 ? grayIndex(layerVars, layerGray) : 0
  };
}

function mintermToBin(m, totalVars) {
  return m.toString(2).padStart(totalVars, '0');
}

// ── Variable name helpers (per-KM) ─────────────────────
function rowVarNames(km) {
  const layout = getLayout(km.varCount);
  return km.varNames.slice(0, layout.rowVars);
}
function colVarNames(km) {
  const layout = getLayout(km.varCount);
  return km.varNames.slice(layout.rowVars, layout.rowVars + layout.colVars);
}
function layerVarNames(km) {
  const layout = getLayout(km.varCount);
  return km.varNames.slice(layout.rowVars + layout.colVars);
}

function rowLabels(km) {
  const layout = getLayout(km.varCount);
  return grayCode(layout.rowVars).map(g => g.toString(2).padStart(layout.rowVars, '0'));
}
function colLabels(km) {
  const layout = getLayout(km.varCount);
  return grayCode(layout.colVars).map(g => g.toString(2).padStart(layout.colVars, '0'));
}
function layerLabels(km) {
  const layout = getLayout(km.varCount);
  if (layout.layerVars === 0) return [''];
  const lv = layerVarNames(km);
  return grayCode(layout.layerVars).map(g => {
    const bits = g.toString(2).padStart(layout.layerVars, '0');
    return lv.map((name, i) => name + '=' + bits[i]).join('  ');
  });
}

// ── State ──────────────────────────────────────────────
function createKMap(name, varCount) {
  return {
    name,
    varCount,
    varNames: defaultVarNames(varCount),
    cells: new Array(1 << varCount).fill(0),
    groups: [],
    mode: 'edit',
    groupStart: null,
    hoverCells: new Set(),
    _autoExpr: null,
  };
}

const state = {
  kmaps: [createKMap('卡诺图 1', 4)],
  activeIdx: 0,
};
function active() { return state.kmaps[state.activeIdx]; }

// ═══════════════════════════════════════════════════════
// 0-1 IP Cover Algorithm (enumeration-based)
// See ALGORITHM.md for full specification
// ═══════════════════════════════════════════════════════
function countLiterals(pi) { let n = 0; for (const ch of pi) if (ch !== '-') n++; return n; }

// ── Step 1: Enumerate all valid groups ────────────────
// Convert integer to base-3 term string: 0→'0', 1→'1', 2→'-'
function patternToTerm(pattern, varCount) {
  let term = '';
  let p = pattern;
  for (let i = 0; i < varCount; i++) {
    const digit = p % 3;
    term = (digit === 0 ? '0' : digit === 1 ? '1' : '-') + term;
    p = Math.floor(p / 3);
  }
  return term;
}

// Get all minterms covered by a term string (e.g. "01-0" → [...])
function termToMinterms(term) {
  const dashes = [];
  for (let i = 0; i < term.length; i++) if (term[i] === '-') dashes.push(i);
  const res = [];
  for (let i = 0; i < (1 << dashes.length); i++) {
    const arr = term.split('');
    for (let j = 0; j < dashes.length; j++) arr[dashes[j]] = (i >> j) & 1 ? '1' : '0';
    res.push(parseInt(arr.join(''), 2));
  }
  return res;
}

function enumerateAllGroups(ones, dcs, varCount) {
  const totalCells = 1 << varCount;
  const cellVal = new Array(totalCells).fill(0);
  for (const m of ones) cellVal[m] = 1;
  for (const m of dcs) cellVal[m] = 'x';

  const allPatterns = Math.pow(3, varCount);
  const groups = [];

  // Enumerate all 3^varCount possible term patterns
  for (let pat = 0; pat < allPatterns - 1; pat++) {  // exclude "---...-" (all don't care)
    const term = patternToTerm(pat, varCount);
    const minterms = termToMinterms(term);

    // Validity: no 0 inside, at least one 1
    let hasZero = false, hasOne = false;
    const groupOnes = [];
    for (const m of minterms) {
      if (cellVal[m] === 0) { hasZero = true; break; }
      if (cellVal[m] === 1) { hasOne = true; groupOnes.push(m); }
    }

    if (!hasZero && hasOne) {
      groups.push({
        term,                           // bit pattern string e.g. "01-0"
        cells: minterms,                // all covered minterms (1 + X)
        ones: groupOnes,                // covered 1-minterms only
        size: minterms.length,          // 2^k
        literals: countLiterals(term),  // n - log₂(size)
      });
    }
  }
  return groups;
}

// ── Step 2–9: Solve min cover, then min literals ──────
function solveMinCover(ones, dcs, varCount) {
  const M = ones.length;
  if (M === 0) return [];
  if (M === (1 << varCount)) return [];  // all ones → constant 1

  const groups = enumerateAllGroups(ones, dcs, varCount);
  if (groups.length === 0) return [];

  // Map 1-minterm → index
  const oneIdxMap = new Map();
  ones.forEach((m, j) => oneIdxMap.set(m, j));

  // Build cover matrix: for each group, which 1-minterms it covers
  const coverMasks = groups.map(g => {
    let mask = 0n;
    for (const m of g.ones) {
      const j = oneIdxMap.get(m);
      mask |= (1n << BigInt(j));
    }
    return mask;
  });

  const allMask = (1n << BigInt(M)) - 1n;

  // Phase 1 + 2 combined: lexicographic objective
  // Primary: minimize term count
  // Secondary: minimize total literals
  let bestTerms = null;       // array of group indices
  let bestTermCount = Infinity;
  let bestLitCount = Infinity;

  function search(idx, selected, selectedLits, covMask) {
    // Prune
    if (selected.length > bestTermCount) return;
    if (selected.length === bestTermCount && selectedLits >= bestLitCount) return;

    // Full coverage
    if (covMask === allMask) {
      if (selected.length < bestTermCount ||
          (selected.length === bestTermCount && selectedLits < bestLitCount)) {
        bestTermCount = selected.length;
        bestLitCount = selectedLits;
        bestTerms = [...selected];
      }
      return;
    }

    if (idx >= groups.length) return;

    // Include this group
    const newMask = covMask | coverMasks[idx];
    if (newMask !== covMask) {
      search(idx + 1, [...selected, idx], selectedLits + groups[idx].literals, newMask);
    }

    // Skip this group
    search(idx + 1, selected, selectedLits, covMask);
  }

  // Sort groups: larger first for better pruning
  const order = groups.map((g, i) => ({ i, size: g.size }))
    .sort((a, b) => b.size - a.size);
  const sortedIdx = order.map(o => o.i);
  const sortedGroups = sortedIdx.map(i => groups[i]);
  const sortedMasks = sortedIdx.map(i => coverMasks[i]);

  // Re-search with sorted groups
  function searchSorted(idx, selected, selectedLits, covMask) {
    if (selected.length > bestTermCount) return;
    if (selected.length === bestTermCount && selectedLits >= bestLitCount) return;

    if (covMask === allMask) {
      if (selected.length < bestTermCount ||
          (selected.length === bestTermCount && selectedLits < bestLitCount)) {
        bestTermCount = selected.length;
        bestLitCount = selectedLits;
        bestTerms = [...selected];
      }
      return;
    }

    if (idx >= sortedGroups.length) return;

    const gi = sortedIdx[idx];
    const newMask = covMask | coverMasks[gi];
    if (newMask !== covMask) {
      searchSorted(idx + 1, [...selected, gi], selectedLits + groups[gi].literals, newMask);
    }
    searchSorted(idx + 1, selected, selectedLits, covMask);
  }

  searchSorted(0, [], 0, 0n);

  if (!bestTerms) return [];

  // Step 10: Remove redundant groups
  const selectedSet = new Set(bestTerms);
  const nonRedundant = [];

  for (const gi of bestTerms) {
    // Check if removing this group still covers all ones
    let maskWithout = 0n;
    for (const gj of bestTerms) {
      if (gj !== gi) maskWithout |= coverMasks[gj];
    }
    if (maskWithout !== allMask) {
      nonRedundant.push(gi);
    }
  }

  return nonRedundant.map(gi => groups[gi]);
}

// ── Step 11–12: Term to expression ───────────────────
function termToExpr(termString, varNames) {
  const parts = [];
  for (let i = 0; i < termString.length; i++) {
    if (termString[i] === '0') parts.push(varNames[i] + "'");
    else if (termString[i] === '1') parts.push(varNames[i]);
  }
  return parts.length === 0 ? '1' : parts.join('·');
}

function simplify(km) {
  const ones = [], dcs = [];
  km.cells.forEach((v, i) => {
    if (v === 1) ones.push(i);
    else if (v === 'x') dcs.push(i);
  });
  const total = 1 << km.varCount;
  if (ones.length === 0) return '0';
  if (ones.length === total || ones.length + dcs.length === total) return '1';

  const selected = solveMinCover(ones, dcs, km.varCount);
  if (selected.length === 0) return '0';

  return selected.map(g => termToExpr(g.term, km.varNames)).join(' + ');
}

// Also expose for auto-simplify button (to create visual groups)
function getSelectedGroups(km) {
  const ones = [], dcs = [];
  km.cells.forEach((v, i) => {
    if (v === 1) ones.push(i);
    else if (v === 'x') dcs.push(i);
  });
  const total = 1 << km.varCount;
  if (ones.length === 0 || ones.length === total || ones.length + dcs.length === total) return [];
  return solveMinCover(ones, dcs, km.varCount);
}

// ═══════════════════════════════════════════════════════
// KaTeX Rendering
// ═══════════════════════════════════════════════════════

// Escape special LaTeX chars in a user-provided name
function latexEscape(name) {
  return name.replace(/[\\{}#%&_$^~]/g, '\\$&');
}

// Convert a variable name to its LaTeX math-mode representation
function varToLatex(name) {
  // Check for default Qₙ pattern
  const m = name.match(/^Q([₀₁₂₃₄₅₆₇₈₉]+)$/);
  if (m) {
    // Q with Unicode subscript digits → Q_{...} in LaTeX
    let digits = '';
    for (const ch of m[1]) {
      const idx = SUB.indexOf(ch);
      if (idx >= 0) digits += idx;
    }
    return 'Q_{' + digits + '}';
  }
  // Plain ASCII letter(s) — use directly
  if (/^[A-Za-z][A-Za-z0-9]*$/.test(name)) return name;
  // Chinese or other Unicode — wrap in \text{}
  return '\\text{' + latexEscape(name) + '}';
}

function toKatex(exprText, varNames) {
  if (!exprText || exprText === '0') return '0';
  if (exprText === '1') return '1';

  let latex = exprText;

  // Sort varNames longest-first so "Q₁₂" matches before "Q₁"
  const sorted = [...varNames].sort((a, b) => b.length - a.length);

  // Replace complemented variables: name' → \overline{...}
  for (const name of sorted) {
    const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const latexName = varToLatex(name);
    latex = latex.replace(new RegExp(escaped + "'", 'g'), '\\overline{' + latexName + '}');
  }
  // Replace bare variables
  for (const name of sorted) {
    const escaped = name.replace(/[.*+?^${}()|[\]\\]/g, '\\$&');
    const latexName = varToLatex(name);
    latex = latex.replace(new RegExp(escaped + "(?!')", 'g'), latexName);
  }

  // AND
  latex = latex.replace(/·/g, ' \\cdot ');
  // Prevent merged overlines
  latex = latex.replace(/(\\overline\{[^}]+\})\s*(\\overline\{)/g, '$1 \\, $2');
  // Remove warnings
  latex = latex.replace(/⚠️.*$/, '').trim();

  return latex;
}

function renderKatex() {
  const km = active();
  const el = document.getElementById('katexDisplay');
  if (!el) return;
  const expr = document.getElementById('exprText').textContent.trim();
  if (!expr) {
    el.innerHTML = '<span class="katex-placeholder">点击自动化简或在上方输入表达式</span>';
    return;
  }
  if (typeof katex === 'undefined') {
    el.innerHTML = '<span class="katex-error">KaTeX 加载中...</span>';
    return;
  }
  const latex = toKatex(expr, km.varNames);
  try {
    katex.render(latex, el, { displayMode: true, throwOnError: false, trust: true });
  } catch (e) {
    el.innerHTML = '<span class="katex-error">渲染错误</span>';
  }
}

// ═══════════════════════════════════════════════════════
// Group Helpers
// ═══════════════════════════════════════════════════════
function groupCellsToExpr(cells, varCount, varNames) {
  const arr = [...cells];
  if (arr.length === 0) return '1';
  const first = mintermToBin(arr[0], varCount);
  const common = first.split('');
  for (const m of arr) {
    const bin = mintermToBin(m, varCount);
    for (let i = 0; i < varCount; i++) if (common[i] !== bin[i]) common[i] = '-';
  }
  const parts = [];
  for (let i = 0; i < varCount; i++) {
    if (common[i] === '0') parts.push(varNames[i] + "'");
    else if (common[i] === '1') parts.push(varNames[i]);
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
    return groupCellsToExpr(g.cells, km.varCount, km.varNames);
  });
  const allCovered = [...ones].every(o => covered.has(o));
  return terms.join(' + ') + (allCovered ? '' : '  ⚠️');
}

function isValidKMapGroup(cellSet, varCount) {
  const n = cellSet.size;
  if (n === 0 || (n & (n - 1)) !== 0) return false;
  const arr = [...cellSet];
  const first = mintermToBin(arr[0], varCount);
  const varying = new Array(varCount).fill(false);
  for (const m of arr) {
    const bin = mintermToBin(m, varCount);
    for (let i = 0; i < varCount; i++) if (bin[i] !== first[i]) varying[i] = true;
  }
  const vc = varying.filter(Boolean).length;
  if (n !== (1 << vc)) return false;
  const gen = new Set(arr);
  for (let i = 0; i < (1 << varCount); i++) {
    const tb = mintermToBin(i, varCount);
    let ok = true;
    for (let j = 0; j < varCount; j++) if (!varying[j] && tb[j] !== first[j]) ok = false;
    if (ok && !gen.has(i)) return false;
  }
  return true;
}

// ═══════════════════════════════════════════════════════
// Cell Selection for Manual Grouping
// ═══════════════════════════════════════════════════════
function getCellsInRect(r1, r2, c1, c2, layer, rWrap, cWrap, km) {
  const layout = getLayout(km.varCount);
  const cells = new Set();
  let rows, cols;

  if (!rWrap) {
    const a = Math.min(r1, r2), b = Math.max(r1, r2);
    rows = []; for (let r = a; r <= b; r++) rows.push(r);
  } else {
    rows = [];
    for (let r = r1; r < layout.rows; r++) rows.push(r);
    for (let r = 0; r <= r2; r++) rows.push(r);
  }
  if (!cWrap) {
    const a = Math.min(c1, c2), b = Math.max(c1, c2);
    cols = []; for (let c = a; c <= b; c++) cols.push(c);
  } else {
    cols = [];
    for (let c = c1; c < layout.cols; c++) cols.push(c);
    for (let c = 0; c <= c2; c++) cols.push(c);
  }
  for (const r of rows) for (const c of cols) cells.add(rcToMinterm(r, c, layer, layout));
  return cells;
}

function getBestGroup(startM, endM, km) {
  if (startM === endM) return new Set([startM]);

  const layout = getLayout(km.varCount);
  const s = mintermToRC(startM, layout);
  const e = mintermToRC(endM, layout);

  if (s.layer !== e.layer) return null;

  const tries = [
    [s.r, e.r, s.c, e.c, false, false],
    [e.r, s.r, s.c, e.c, true,  false],
    [s.r, e.r, e.c, s.c, false, true ],
    [e.r, s.r, e.c, s.c, true,  true ],
  ];

  let best = null;
  for (const [r1, r2, c1, c2, rw, cw] of tries) {
    const cells = getCellsInRect(r1, r2, c1, c2, s.layer, rw, cw, km);
    if (isValidKMapGroup(cells, km.varCount)) {
      if (best === null || cells.size < best.size) best = cells;
    }
  }

  if (startM !== endM) {
    const pair = new Set([startM, endM]);
    if (isValidKMapGroup(pair, km.varCount)) {
      if (best === null || 2 < best.size) best = pair;
    }
  }

  return best;
}

// ═══════════════════════════════════════════════════════
// Visual Rectangles for Overlay Drawing
// ═══════════════════════════════════════════════════════
function getVisualRects(cellSet, varCount) {
  const arr = [...cellSet];
  const layout = getLayout(varCount);
  const rcs = arr.map(m => mintermToRC(m, layout));
  const rows = [...new Set(rcs.map(rc => rc.r))].sort((a, b) => a - b);
  const cols = [...new Set(rcs.map(rc => rc.c))].sort((a, b) => a - b);

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
  renderVarSelector();
  renderVarNameInputs();
  renderKMap();
  renderExpr();
  renderKatex();
  renderGroupList();
  renderVarButtons();
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

function renderVarSelector() {
  const km = active();
  const sel = document.getElementById('varCountSelect');
  if (sel) sel.value = km.varCount;
}

function renderVarNameInputs() {
  const km = active();
  const container = document.getElementById('varNameInputs');
  if (!container) return;
  let html = '';
  for (let i = 0; i < km.varCount; i++) {
    html += `<input class="varname-inp" data-idx="${i}" value="${escapeHtml(km.varNames[i])}" maxlength="8" title="变量 ${i} 名称">`;
  }
  container.innerHTML = html;
  container.querySelectorAll('.varname-inp').forEach(inp => {
    inp.addEventListener('input', function () {
      const idx = parseInt(this.dataset.idx);
      const newName = this.value.trim() || defaultVarNames(km.varCount)[idx];
      km.varNames[idx] = newName;
      this.value = newName;
      renderKMap();
      renderVarButtons();
      renderKatex();
    });
  });
}

function escapeHtml(s) {
  const d = document.createElement('div');
  d.textContent = s;
  return d.innerHTML;
}

function renderKMap() {
  const km = active();
  const layout = getLayout(km.varCount);
  const panel = document.getElementById('leftPanel');
  panel.innerHTML = '';

  const container = document.createElement('div');
  container.className = 'kmap-container';

  const rv = rowVarNames(km).join('');
  const cv = colVarNames(km).join('');
  container.innerHTML = `<div class="kmap-title">${km.name}
    <span class="tag">${rv} \\ ${cv}</span>
  </div>`;

  const layers = layerLabels(km);
  const layersWrap = document.createElement('div');
  layersWrap.className = 'layers-wrap';

  for (let layerIdx = 0; layerIdx < layout.layers; layerIdx++) {
    const layerDiv = document.createElement('div');
    layerDiv.className = 'layer-panel';

    if (layout.layers > 1) {
      const layerHdr = document.createElement('div');
      layerHdr.className = 'layer-header';
      layerHdr.textContent = layers[layerIdx];
      layerDiv.appendChild(layerHdr);
    }

    const wrapper = document.createElement('div');
    wrapper.className = 'grid-wrapper';
    wrapper.dataset.layer = layerIdx;

    const grid = document.createElement('div');
    grid.className = 'kmap-grid';
    grid.style.gridTemplateColumns = `52px repeat(${layout.cols}, ${layout.cols <= 2 ? '82px' : layout.cols <= 4 ? '72px' : '56px'})`;
    grid.style.gridTemplateRows = `44px repeat(${layout.rows}, ${layout.rows <= 2 ? '66px' : layout.rows <= 4 ? '58px' : '44px'})`;

    // Corner
    const corner = document.createElement('div');
    corner.className = 'corner';
    corner.innerHTML = rv + '↓<br>' + cv + '→';
    corner.style.fontSize = '10px';
    grid.appendChild(corner);

    // Column headers
    for (const cl of colLabels(km)) {
      const h = document.createElement('div');
      h.className = 'h-label'; h.textContent = cl;
      grid.appendChild(h);
    }

    // Rows
    const rLabels = rowLabels(km);
    for (let r = 0; r < layout.rows; r++) {
      const rl = document.createElement('div');
      rl.className = 'v-label'; rl.textContent = rLabels[r];
      grid.appendChild(rl);

      for (let c = 0; c < layout.cols; c++) {
        const m = rcToMinterm(r, c, layerIdx, layout);
        const v = km.cells[m];
        const cell = document.createElement('div');
        cell.className = 'cell v' + (v === 'x' ? 'x' : v);
        cell.dataset.r = r;
        cell.dataset.c = c;
        cell.dataset.m = m;
        cell.dataset.layer = layerIdx;
        if (layout.cols > 4 || layout.rows > 4) {
          cell.innerHTML = `<span class="val" style="font-size:13px">${v === 'x' ? 'X' : v}</span>`;
        } else {
          cell.innerHTML = `<span class="val">${v === 'x' ? 'X' : v}</span><span class="idx">m${m}</span>`;
        }
        cell.addEventListener('mousedown', e => onCellDown(e, cell));
        cell.addEventListener('mouseenter', e => onCellEnter(e, cell));
        cell.addEventListener('mouseup', e => onCellUp(e, cell));
        cell.addEventListener('contextmenu', e => e.preventDefault());
        grid.appendChild(cell);
      }
    }

    wrapper.appendChild(grid);

    const ov = document.createElement('div');
    ov.className = 'group-overlays';
    ov.style.cssText = 'position:absolute;top:0;left:0;width:100%;height:100%;pointer-events:none;z-index:0';
    wrapper.appendChild(ov);

    layerDiv.appendChild(wrapper);
    layersWrap.appendChild(layerDiv);
  }

  container.appendChild(layersWrap);

  const caption = document.createElement('div');
  caption.className = 'caption';
  caption.textContent = layout.layers > 1
    ? '行列 Gray 码排列 | 点击 0→1→X→0 | 拖拽圈选（仅同层）'
    : '行列 Gray 码排列 | 点击 0→1→X→0 | 拖拽圈选';
  container.appendChild(caption);

  // Action buttons below the K-map
  const actions = document.createElement('div');
  actions.className = 'kmap-actions';
  const btnClearAll = document.createElement('button');
  btnClearAll.className = 'btn btn-secondary';
  btnClearAll.textContent = '🗑 清空全部';
  btnClearAll.onclick = () => {
    km.cells.fill(0);
    km.groups = [];
    km._autoExpr = null;
    renderAll();
  };
  const btnAlgo = document.createElement('button');
  btnAlgo.className = 'btn btn-secondary';
  btnAlgo.textContent = '📖 算法说明';
  btnAlgo.onclick = openAlgoModal;
  actions.appendChild(btnClearAll);
  actions.appendChild(btnAlgo);
  container.appendChild(actions);

  panel.appendChild(container);

  requestAnimationFrame(() => {
    document.querySelectorAll('.grid-wrapper').forEach(w => {
      drawOverlays(w, km);
    });
  });
}

function drawOverlays(wrapper, km) {
  const ov = wrapper.querySelector('.group-overlays');
  ov.innerHTML = '';

  const layout = getLayout(km.varCount);
  const layerIdx = parseInt(wrapper.dataset.layer || 0);
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

  km.groups.forEach(g => {
    const layerCells = new Set();
    for (const m of g.cells) {
      const rc = mintermToRC(m, layout);
      if (rc.layer === layerIdx) layerCells.add(m);
    }
    if (layerCells.size === 0) return;

    const rects = getVisualRects(layerCells, km.varCount);
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

  if (km.mode === 'group' && km.groupStart !== null) {
    for (const m of km.hoverCells) {
      const rc = mintermToRC(m, layout);
      if (rc.layer !== layerIdx) continue;
      const p = posMap[`${rc.r},${rc.c}`];
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
    list.innerHTML = '<div style="color:#bcc3d0;font-size:13px;padding:4px 0">暂无圈选 — 请手动圈选或点击自动化简</div>';
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
      <span>${g.cells.size}格: ${groupCellsToExpr(g.cells, km.varCount, km.varNames)}</span>
      ${hasZero ? '<span class="warn" title="圈选了0值格子">⚠️</span>' : ''}
      ${onlyX ? '<span style="color:#bcc3d0;font-size:11px">(仅X)</span>' : ''}
      <button class="del-btn" onclick="deleteGroup(${i})" title="删除">×</button>
    </div>`;
  }).join('');

  const allCovered = [...ones].every(o => covered.has(o));
  if (!allCovered && ones.size > 0) {
    list.innerHTML += '<div style="color:#e74c3c;font-size:12px;margin-top:4px">⚠️ 当前圈选未覆盖所有 1</div>';
  }
}

function deleteGroup(idx) {
  active().groups.splice(idx, 1);
  renderAll();
}

function renderVarButtons() {
  const km = active();
  const container = document.getElementById('varButtons');
  if (!container) return;
  let html = '';
  for (let i = 0; i < km.varCount; i++) {
    html += `<button class="btn btn-var ins-btn" data-text="${escapeHtml(km.varNames[i])}">${escapeHtml(km.varNames[i])}</button>`;
  }
  container.innerHTML = html;
  container.querySelectorAll('.ins-btn').forEach(btn => {
    btn.onclick = () => insertAtCursor(btn.dataset.text);
  });
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
  const best = getBestGroup(km.groupStart, m, km);
  km.hoverCells = best || new Set([km.groupStart, m]);
  document.querySelectorAll('.grid-wrapper').forEach(w => drawOverlays(w, km));
}

function onCellUp(e, cell) {
  const km = active();
  if (km.mode !== 'group' || km.groupStart === null) return;
  const m = parseInt(cell.dataset.m);
  const best = getBestGroup(km.groupStart, m, km);
  if (best && isValidKMapGroup(best, km.varCount)) {
    const color = GCOLORS[km.groups.length % GCOLORS.length];
    km.groups.push({ cells: new Set(best), color });
  }
  km.groupStart = null;
  km.hoverCells = new Set();
  km._autoExpr = null;
  renderAll();
}

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
  const km = active();
  state.kmaps.push(createKMap('卡诺图 ' + (state.kmaps.length + 1), km.varCount));
  state.activeIdx = state.kmaps.length - 1;
  renderAll();
};

// ═══════════════════════════════════════════════════════
// Variable Count Selector
// ═══════════════════════════════════════════════════════
document.getElementById('varCountSelect').addEventListener('change', function () {
  const km = active();
  const newCount = parseInt(this.value);
  if (newCount === km.varCount) return;
  km.varCount = newCount;
  km.varNames = defaultVarNames(newCount);
  km.cells = new Array(1 << newCount).fill(0);
  km.groups = [];
  km._autoExpr = null;
  km.groupStart = null;
  km.hoverCells = new Set();
  renderAll();
});

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
      : '在格子上按住拖拽来圈选卡诺圈（仅同层，自动识别有效矩形）';
  renderAll();
});

// ═══════════════════════════════════════════════════════
// Auto Simplify
// ═══════════════════════════════════════════════════════
document.getElementById('btnAutoSimplify').onclick = () => {
  const km = active();
  const expr = simplify(km);
  km._autoExpr = expr;

  const ones = [], dcs = [];
  km.cells.forEach((v, i) => {
    if (v === 1) ones.push(i);
    else if (v === 'x') dcs.push(i);
  });

  km.groups = [];
  const total = 1 << km.varCount;
  if (ones.length > 0 && ones.length < total && ones.length + dcs.length < total) {
    const selected = getSelectedGroups(km);
    km.groups = selected.map((g, i) => ({
      cells: new Set(g.cells.filter(m => km.cells[m] === 1 || km.cells[m] === 'x')),
      color: GCOLORS[i % GCOLORS.length]
    }));
  }

  renderAll();
};

// ═══════════════════════════════════════════════════════
// Clear / Reset
// ═══════════════════════════════════════════════════════
document.getElementById('btnClearGroups').onclick = () => {
  const km = active();
  km.groups = [];
  km._autoExpr = null;
  renderAll();
};

// ═══════════════════════════════════════════════════════
// Expression Input Buttons
// ═══════════════════════════════════════════════════════
function insertAtCursor(text) {
  const el = document.getElementById('exprText');
  el.focus();
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

// Bind static ins-btn (NOT, AND, OR, parens, backspace, clear)
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
  const km = active();
  km._autoExpr = null;
  km.groups = [];
  renderAll();
};

document.getElementById('exprText').addEventListener('input', () => {
  const km = active();
  km._autoExpr = document.getElementById('exprText').textContent;
  renderKatex();
});

// ═══════════════════════════════════════════════════════
// Algorithm Modal
// ═══════════════════════════════════════════════════════
function openAlgoModal() {
  document.getElementById('algoOverlay').classList.add('show');
  document.body.style.overflow = 'hidden';
  // Render KaTeX formulas in the modal
  setTimeout(() => {
    const modal = document.getElementById('algoModal');
    if (modal && typeof renderMathInElement !== 'undefined') {
      renderMathInElement(modal, {
        delimiters: [
          { left: '\\[', right: '\\]', display: true },
          { left: '\\(', right: '\\)', display: false }
        ],
        throwOnError: false
      });
    }
  }, 100);
}

function closeAlgoModal(e) {
  if (e && e.target !== document.getElementById('algoOverlay')) return;
  document.getElementById('algoOverlay').classList.remove('show');
  document.body.style.overflow = '';
}

document.addEventListener('keydown', e => {
  if (e.key === 'Escape') {
    const overlay = document.getElementById('algoOverlay');
    if (overlay.classList.contains('show')) {
      overlay.classList.remove('show');
      document.body.style.overflow = '';
    }
  }
});

// ═══════════════════════════════════════════════════════
// Init
// ═══════════════════════════════════════════════════════
renderAll();
