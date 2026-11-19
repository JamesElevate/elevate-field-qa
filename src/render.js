/* Elevate Surveying - Field QA drawings: A3 SVG sheets (check plot, setout check, client sketch) and DXF. */
(function (root) {
"use strict";
const QA = (typeof module !== "undefined" && module.exports) ? require("./engine.js") : root.FieldQA;
const { COL, SECTIONS, DESIGN_LAYER_KEYS, SETOUT_CODES, MARKS, section, mm, f0, fx, last, d2 } = QA;
const W = 1587, H = 1123;                         // A3 landscape at 96 dpi (SVG px)
const SANS = "helvetica", MONO = "courier";
const INK = "#2d3436", MUTED = "#636e72", FAINT = "#b2bec3";

function esc(s) { return String(s).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;"); }
function n2(v) { return Math.round(v * 100) / 100; }
function text(x, y, s, o = {}) {
  const a = [`x="${n2(x)}"`, `y="${n2(y)}"`, `font-family="${o.mono ? MONO : SANS}"`, `font-size="${o.size || 10}"`, `fill="${o.fill || INK}"`];
  if (o.weight) a.push(`font-weight="${o.weight}"`);
  if (o.italic) a.push(`font-style="italic"`);
  if (o.anchor) a.push(`text-anchor="${o.anchor}"`);
  if (o.op) a.push(`fill-opacity="${o.op}"`);
  if (o.rot) a.push(`transform="rotate(${o.rot} ${n2(x)} ${n2(y)})"`);
  return `<text ${a.join(" ")}>${esc(s)}</text>`;
}
function line(x1, y1, x2, y2, o = {}) {
  return `<line x1="${n2(x1)}" y1="${n2(y1)}" x2="${n2(x2)}" y2="${n2(y2)}" stroke="${o.stroke || INK}" stroke-width="${o.w || 1}"${o.dash ? ` stroke-dasharray="${o.dash}"` : ""}${o.op ? ` stroke-opacity="${o.op}"` : ""}/>`;
}
function poly(pts, o = {}) {
  return `<polyline points="${pts.map((p) => n2(p[0]) + "," + n2(p[1])).join(" ")}" fill="none" stroke="${o.stroke || INK}" stroke-width="${o.w || 1}"${o.dash ? ` stroke-dasharray="${o.dash}"` : ""}/>`;
}
function marker(kind, x, y, s, fill, stroke, sw = 1) {
  const st = `fill="${fill}" stroke="${stroke}" stroke-width="${sw}"`;
  if (kind === "s") return `<rect x="${n2(x - s)}" y="${n2(y - s)}" width="${n2(2 * s)}" height="${n2(2 * s)}" ${st}/>`;
  if (kind === "^") return `<polygon points="${n2(x)},${n2(y - s * 1.2)} ${n2(x - s * 1.1)},${n2(y + s * 0.8)} ${n2(x + s * 1.1)},${n2(y + s * 0.8)}" ${st}/>`;
  return `<circle cx="${n2(x)}" cy="${n2(y)}" r="${n2(s)}" ${st}/>`;
}
function wrap(s, n) { const out = []; let cur = ""; for (const w of String(s).split(/\s+/)) { if ((cur + " " + w).trim().length > n && cur) { out.push(cur); cur = w; } else cur = (cur + " " + w).trim(); } if (cur) out.push(cur); return out; }

// world -> sheet transform with equal scale, centred in a panel
function frame(x0, x1, y0, y1, px, py, pw, ph) {
  const s = Math.min(pw / (x1 - x0), ph / (y1 - y0));
  const cx = (x0 + x1) / 2, cy = (y0 + y1) / 2;
  const T = (E, N) => [px + pw / 2 + (E - cx) * s, py + ph / 2 - (N - cy) * s];
  return { T, s, px, py, pw, ph, wx0: cx - pw / 2 / s, wx1: cx + pw / 2 / s, wy0: cy - ph / 2 / s, wy1: cy + ph / 2 / s };
}

// greedy label placement: try positions around each anchor, avoid earlier labels and markers
function placeLabels(items, fr, obstacles) {
  const boxes = obstacles ? obstacles.slice() : [];
  for (const it of items) if (it.mark) boxes.push([it.x - it.mark, it.y - it.mark, 2 * it.mark, 2 * it.mark]);
  const out = [];
  const R = [[6, -6], [6, 10], [-6, -6], [-6, 10], [0, -12], [0, 18], [14, 3], [-14, 3], [16, -16], [16, 22], [-16, -16], [-16, 22], [26, 3], [-26, 3], [0, -26], [0, 32], [30, -24], [-30, -24], [30, 30], [-30, 30]];
  for (const it of items) {
    const w = it.s.length * it.size * 0.56, h = it.size * 1.05;
    let best = null;
    for (let i = 0; i < R.length; i++) {
      const [dx, dy] = R[i], left = dx < 0, cxp = dx === 0;
      const x = it.x + dx - (left ? w : cxp ? w / 2 : 0), y = it.y + dy - h * 0.8;
      if (x < fr.px + 2 || x + w > fr.px + fr.pw - 2 || y < fr.py + 2 || y + h > fr.py + fr.ph - 2) continue;
      let ov = 0;
      for (const b of boxes) { const ix = Math.max(0, Math.min(x + w, b[0] + b[2]) - Math.max(x, b[0])), iy = Math.max(0, Math.min(y + h, b[1] + b[3]) - Math.max(y, b[1])); ov += ix * iy; }
      const score = ov * 10 + i;
      if (!best || score < best.score) best = { score, x, y, w, h, dx, dy, anchor: left ? "end" : cxp ? "middle" : "start" };
      if (ov === 0) break;
    }
    if (!best) best = { x: it.x + 6, y: it.y - 6 - h * 0.8, w, h, dx: 6, dy: -6, anchor: "start" };
    boxes.push([best.x, best.y, best.w, best.h]);
    out.push({ ...it, lx: it.x + best.dx, ly: it.y + best.dy, anchor: best.anchor, far: Math.hypot(best.dx, best.dy) > 20, bx: best.x, by: best.y, bw: best.w, bh: best.h });
  }
  return out;
}
function drawLabels(placed) {
  let s = "";
  for (const p of placed) {
    if (p.far) s += line(p.x, p.y, p.anchor === "end" ? p.bx + p.bw : p.anchor === "middle" ? p.bx + p.bw / 2 : p.bx, p.by + p.bh / 2, { stroke: "#999", w: 0.4 });
    s += text(p.lx, p.ly, p.s, { size: p.size, fill: p.fill || INK, weight: p.weight, italic: p.italic, anchor: p.anchor });
  }
  return s;
}
function clipStart(id, fr) { return `<defs><clipPath id="${id}"><rect x="${fr.px}" y="${fr.py}" width="${fr.pw}" height="${fr.ph}"/></clipPath></defs><g clip-path="url(#${id})">`; }
function axes(fr) {
  // light coordinate grid with labels on the frame
  const span = fr.wx1 - fr.wx0, step = [5, 10, 20, 25, 50, 100, 200].find((v) => span / v <= 10) || 500;
  let s = "";
  for (let e = Math.ceil(fr.wx0 / step) * step; e <= fr.wx1; e += step) { const [x] = fr.T(e, 0); s += line(x, fr.py, x, fr.py + fr.ph, { stroke: "#eef0f2", w: 0.5 }) + text(x, fr.py + fr.ph + 12, String(Math.round(e)), { size: 7, fill: MUTED, anchor: "middle" }); }
  for (let n = Math.ceil(fr.wy0 / step) * step; n <= fr.wy1; n += step) { const [, y] = fr.T(0, n); s += line(fr.px, y, fr.px + fr.pw, y, { stroke: "#eef0f2", w: 0.5 }) + text(fr.px - 4, y + 2.5, String(Math.round(n)), { size: 7, fill: MUTED, anchor: "end" }); }
  return s;
}
function banner(x, y, s, color, size = 12) {
  const w = s.length * size * 0.55 + 20;
  return `<rect x="${n2(x - w / 2)}" y="${n2(y)}" width="${n2(w)}" height="${size + 10}" rx="5" fill="${color}"/>` + text(x, y + size + 2, s, { size, fill: "#ffffff", weight: "bold", anchor: "middle" });
}
const LOGO_AR = 967 / 659;   // width / height of the Elevate logo artwork
function logoImg(logo, x, y, w, h) {   // fit inside the box keeping the logo's aspect (PDF export ignores preserveAspectRatio)
  if (!logo) return "";
  let lw = w, lh = w / LOGO_AR; if (lh > h) { lh = h; lw = h * LOGO_AR; }
  const lx = x + (w - lw), ly = y + (h - lh) / 2;
  return `<image x="${n2(lx)}" y="${n2(ly)}" width="${n2(lw)}" height="${n2(lh)}" href="${logo}" xlink:href="${logo}"/>`;
}
function svgWrap(body) { return `<svg xmlns="http://www.w3.org/2000/svg" xmlns:xlink="http://www.w3.org/1999/xlink" viewBox="0 0 ${W} ${H}" width="${W}" height="${H}"><rect x="0" y="0" width="${W}" height="${H}" fill="#ffffff"/>${body}</svg>`; }

function titleLines(R) {
  const t = R.tol, prof = R.prof;
  const mode = prof.label + (prof.heights ? " - heights included" : " - horizontal only") + (prof.heightsOverride ? " (set by user)" : "") + ", " + (R.hasCalc ? "survey + calc file" : "single file") + (R.raw ? ", raw obs" : ", NO RAW OBS - no traverse/radiations");
  return [`Field QA - ${R.fileName || R.info.job}  (${mode})`,
    `1 Calc to survey: GREEN <=${f0(t.BDY_GREEN * 1000)} ORANGE <=${f0(t.BDY_ORANGE * 1000)} RED >${f0(t.BDY_ORANGE * 1000)} mm   2 Survey to survey: GREEN <=${f0(t.GREEN * 1000)} ORANGE <=${f0(t.ORANGE * 1000)} RED >${f0(t.ORANGE * 1000)} mm` + (prof.setout ? `   3 Setout: pass <=${f0(t.SETOUT_TOL * 1000)} mm` : "")];
}
function pointStatus(rows) {
  const ORD = ["INFO", "GREEN", "ORANGE", "RED"], st = new Map();
  for (const r of rows) if (/^(L1|L2|DAT|SO )/.test(r.level)) { const cur = st.get(r.pt) || "INFO"; if (ORD.indexOf(r.status) > ORD.indexOf(cur)) st.set(r.pt, r.status); }
  return st;
}

// ---------------------------------------------------------------- sheet 1: check plot + report
function checkPlot(R, logo) {
  const { survey, calc, lines, rows, raw, pts } = R;
  const status = pointStatus(rows);
  const setoutMode = R.prof.setout;
  const isLabelled = (p) => MARKS.has(p.code) || ["STN", "CHK", "BM", "RL"].includes(p.code) || (setoutMode && SETOUT_CODES.has(p.code));
  const E = survey.map((p) => p.E), N = survey.map((p) => p.N), pad = 8;
  const fr = frame(Math.min(...E) - pad, Math.max(...E) + pad, Math.min(...N) - pad, Math.max(...N) + pad, 62, 70, 1010, 1020);
  const T = fr.T;
  let g = "";
  const vis = (p) => p.E > fr.wx0 && p.E < fr.wx1 && p.N > fr.wy0 && p.N < fr.wy1;
  for (const l of lines) {
    const U = l.layer.toUpperCase(), cad = U.includes("CADASTRAL") || U.includes("BDY");
    g += poly(l.xy.map((v) => T(v[0], v[1])), { stroke: cad ? "#c0392b" : "#d5d5d5", w: cad ? 0.9 : 0.4 });
  }
  const labels = [];
  for (const c of calc) if (c.code.startsWith("O") && vis(c)) { const [x, y] = T(c.E, c.N); g += marker("s", x, y, 3.2, "none", "#444", 0.8); labels.push({ x, y, s: `${c.name} ${c.code}`, size: 6.5, fill: "#666", italic: true, pri: 3 }); }
  const allbn = new Map(pts.map((p) => [p.name, p])), cbn = new Map(calc.map((c) => [c.name, c]));
  if (raw) for (const s of raw.setups) {
    if (!s.shots.length) continue;
    const [sx, sy] = T(s.E, s.N);
    for (const sh of s.shots) { const p = allbn.get(sh.name); if (!p) continue; const [x, y] = T(p.E, p.N); const st = p.code === "STN"; g += line(sx, sy, x, y, { stroke: st ? "#1e3799" : "#82ccdd", w: st ? 1.6 : 0.35 }); }
    if (s.bs) { const [x, y] = T(s.bs.E, s.bs.N); g += line(sx, sy, x, y, { stroke: "#1e3799", w: 1.6, dash: "6 4" }); }
    for (const r of s.res) { const q = cbn.get(r.name) || allbn.get(r.name); if (q) { const [x, y] = T(q.E, q.N); g += line(sx, sy, x, y, { stroke: r.used ? "#8e44ad" : COL.RED, w: 1.2, dash: "8 3 2 3" }); } }
  }
  const pbn = new Map([...survey, ...calc].map((p) => [p.name, p]));
  for (const r of rows) if (r.level.startsWith("L2") && r.dH !== null) {
    const tg = pbn.get(r.ref.split(" ")[0]), k = pbn.get(r.pt);
    if (tg && k) { const [a, b] = T(k.E, k.N), [c, d] = T(tg.E, tg.N); g += line(a, b, c, d, { stroke: COL[r.status], w: 1.2 }); }
  }
  for (const p of survey) {
    if (!vis(p)) continue;
    const st = status.get(p.name) || "INFO", [x, y] = T(p.E, p.N);
    if (p.code === "STN") g += marker("^", x, y, 6, INK, "#ffffff", 1);
    else if (p.code === "CHK") g += `<circle cx="${n2(x)}" cy="${n2(y)}" r="6" fill="none" stroke="${COL[st]}" stroke-width="1.6"/>`;
    else { const feat = !(MARKS.has(p.code) || ["BM", "RL"].includes(p.code) || (setoutMode && SETOUT_CODES.has(p.code))); g += marker("o", x, y, feat && st === "INFO" ? 1.8 : 3.4, st !== "INFO" ? COL[st] : FAINT, "#222", feat ? 0.2 : 0.4); }
    if (!isLabelled(p) && !(st === "RED" || st === "ORANGE")) continue;
    const hot = st === "RED" || st === "ORANGE";
    labels.push({ x, y, mark: 4, s: `${last(p.name)} ${p.code}`, size: 7.5, fill: hot ? COL[st] : INK, weight: hot ? "bold" : null, pri: hot ? 0 : (p.code === "STN" ? 1 : 2) });
  }
  labels.sort((a, b) => a.pri - b.pri);
  g += drawLabels(placeLabels(labels, fr));
  let svg = clipStart("mapclip", fr) + axes(fr) + g + "</g>";
  svg += `<rect x="${fr.px}" y="${fr.py}" width="${fr.pw}" height="${fr.ph}" fill="none" stroke="${INK}" stroke-width="1"/>`;
  const tl = titleLines(R);
  svg += text(62, 30, tl[0], { size: 15 }) + text(62, 52, tl[1], { size: 12 });
  const rev = rows.filter((r) => r.level === "L1 best fit" && r.status === "RED");
  const rel = rows.find((r) => r.level === "SO release");
  let by = fr.py + 8;
  if (rev.length) { svg += banner(fr.px + fr.pw / 2, by, "JOB FLAGGED FOR REVIEW - " + rev.map((r) => `${r.pt}: ${r.ref}`).join("; ") + " (minimum 3 independent agreeing marks)", COL.RED, 11); by += 28; }
  if (rel) svg += banner(fr.px + fr.pw / 2, by, "SETOUT: " + rel.comment.slice(0, 150), COL[rel.status], 10.5);
  // side panel
  const sx = 1100; let yy = 90;
  const ord = { RED: 0, ORANGE: 1, GREEN: 2, INFO: 3 };
  const tol = { "1": `after best fit: green <=${f0(R.tol.BDY_GREEN * 1000)}, orange <=${f0(R.tol.BDY_ORANGE * 1000)}, red >${f0(R.tol.BDY_ORANGE * 1000)} mm`,
    "2": `green <=${f0(R.tol.GREEN * 1000)}, orange <=${f0(R.tol.ORANGE * 1000)}, red >${f0(R.tol.ORANGE * 1000)} mm` + (R.prof.heights ? "" : " (horizontal only)"),
    "3": `pass <=${f0(R.tol.SETOUT_TOL * 1000)} mm, fail >${f0(R.tol.SETOUT_TOL * 1000)} mm` };
  const secs = SECTIONS.filter(([k]) => rows.some((r) => section(r.level) === k));
  const legendTop = 900, budget = (legendTop - 20 - yy) / Math.max(1, secs.length);
  for (const [k, name] of secs) {
    const sr = rows.filter((r) => section(r.level) === k), y0 = yy;
    const cnt = { RED: 0, ORANGE: 0, GREEN: 0 }; for (const r of sr) if (cnt[r.status] !== undefined) cnt[r.status]++;
    svg += text(sx, yy, `${k}. ${name}`, { size: 12.5, weight: "bold" });
    svg += text(W - 24, yy, `RED ${cnt.RED}  ORANGE ${cnt.ORANGE}  GREEN ${cnt.GREEN}`, { size: 10, weight: "bold", anchor: "end", fill: cnt.RED ? COL.RED : cnt.ORANGE ? COL.ORANGE : COL.GREEN });
    yy += 16; svg += text(sx + 8, yy, tol[k], { size: 8.5, fill: MUTED }); yy += 16;
    const shown = sr.filter((r) => r.status === "RED" || r.status === "ORANGE").sort((a, b) => ord[a.status] - ord[b.status] || (a.level < b.level ? -1 : 1));
    for (let i = 0; i < shown.length; i++) {
      if (yy > y0 + budget - 30) { svg += text(sx + 8, yy, `... ${shown.length - i} more - see CSV`, { size: 8.5, italic: true, fill: MUTED }); yy += 14; break; }
      const r = shown[i];
      svg += `<circle cx="${sx + 3}" cy="${yy - 3}" r="3.6" fill="${COL[r.status]}"/>`;
      const val = (r.dH !== null ? "H " + mm(r.dH) : "") + (r.dV !== null ? "  V " + mm(r.dV) : "");
      svg += text(sx + 12, yy, `${r.level.padEnd(16)}${r.pt.slice(-14).padEnd(15)}${r.ref.slice(0, 22)}`, { size: 8, mono: true });
      svg += text(W - 24, yy, val, { size: 8, mono: true, anchor: "end" });
      yy += 12;
      if (r.comment) { svg += text(sx + 16, yy, r.comment.length > 105 ? r.comment.slice(0, 104) + "..." : r.comment, { size: 7, italic: true, fill: MUTED }); yy += 12; }
    }
    if (cnt.GREEN) { svg += text(sx + 8, yy, `+ ${cnt.GREEN} checks green (see CSV)`, { size: 8.5, fill: COL.GREEN }); yy += 14; }
    yy += 14;
  }
  // legend
  let ly = legendTop; svg += text(sx, ly, "LEGEND", { size: 10, weight: "bold" }); ly += 16;
  const items = [["s", "none", "#444", "Calc mark (O-code)"], ["^", INK, "#fff", "Station (STN)"], ["ring", "none", "#555", "Check shot (ring colour = result)"],
    ["o", COL.GREEN, "#222", "GREEN - good"], ["o", COL.ORANGE, "#222", "ORANGE - investigate"], ["o", COL.RED, "#222", "RED - looks wrong, check now"], ["o", FAINT, "#222", "Not checked"],
    ["l", "#c0392b", "", "Cadastral bdy / RM lines"], ...(raw ? [["l", "#1e3799", "", "Traverse: to next station"], ["d", "#1e3799", "6 4", "Traverse: backsight"], ["d", "#8e44ad", "8 3 2 3", "Resection obs (red = excluded)"], ["l", "#82ccdd", "", "Radiations / side shots"]] : [])];
  items.forEach((it, i) => {
    const cx = sx + 8 + (i % 2) * 230, cy = ly + Math.floor(i / 2) * 17;
    if (it[0] === "ring") svg += `<circle cx="${cx}" cy="${cy - 3}" r="5" fill="none" stroke="${it[2]}" stroke-width="1.5"/>`;
    else if (it[0] === "l" || it[0] === "d") svg += line(cx - 8, cy - 3, cx + 8, cy - 3, { stroke: it[1], w: 1.6, dash: it[0] === "d" ? it[2] : null });
    else svg += marker(it[0], cx, cy - 3, 4, it[1], it[2], 0.8);
    svg += text(cx + 14, cy, it[3], { size: 8.5 });
  });
  svg += logoImg(logo, W - 230, 8, 206, 52);
  return svgWrap(svg);
}

// ---------------------------------------------------------------- drawing model shared by PDF (SVG) and CAD (DXF) output
// A sheet is a list of drawing operations in A3 sheet coordinates (px); it is emitted to SVG for the PDF and to
// DXF in real-world coordinates (model space, at the sheet's plotting scale) so CAD edits stay true to the survey.
const PX_MM = 420 / 1587;                                // paper mm per sheet px
const STD_SCALES = [50, 100, 200, 250, 500, 1000, 2000, 2500, 5000];
function frameAtScale(x0, x1, y0, y1, px, py, pw, ph) {
  const fit = Math.min(pw / (x1 - x0), ph / (y1 - y0));
  const S = STD_SCALES.find((sc) => 1000 / (sc * PX_MM) <= fit) || STD_SCALES[STD_SCALES.length - 1];
  const fr = frame(x0, x1, y0, y1, px, py, pw, ph);
  const s = 1000 / (S * PX_MM), cx = (x0 + x1) / 2, cy = (y0 + y1) / 2;
  fr.s = s; fr.scale = S;
  fr.T = (E, N) => [px + pw / 2 + (E - cx) * s, py + ph / 2 - (N - cy) * s];
  fr.inv = (x, y) => [cx + (x - (px + pw / 2)) / s, cy - (y - (py + ph / 2)) / s];
  fr.wx0 = cx - pw / 2 / s; fr.wx1 = cx + pw / 2 / s; fr.wy0 = cy - ph / 2 / s; fr.wy1 = cy + ph / 2 / s;
  return fr;
}
class Sheet {
  constructor(fr) { this.fr = fr; this.ops = []; }
  add(op) { this.ops.push(op); return this; }
  line(layer, x1, y1, x2, y2, o = {}) { return this.add({ t: "line", layer, x1, y1, x2, y2, ...o }); }
  poly(layer, pts, o = {}) { return this.add({ t: "poly", layer, pts, ...o }); }
  marker(layer, kind, x, y, r, fill, stroke, w = 1, o = {}) { return this.add({ t: "marker", layer, kind, x, y, r, fill, stroke, w, ...o }); }
  text(layer, x, y, s, o = {}) { return this.add({ t: "text", layer, x, y, s, ...o }); }
  rect(layer, x, y, w, h, o = {}) { return this.add({ t: "rect", layer, x, y, w, h, ...o }); }
  polygon(layer, pts, fill, o = {}) { return this.add({ t: "polygon", layer, pts, fill, ...o }); }
  image(x, y, w, h) { return this.add({ t: "image", layer: "", x, y, w, h }); }
}
function sheetToSVG(sh, logo, clipId) {
  const fr = sh.fr; let a = "", b = "";
  for (const op of sh.ops) {
    let s = "";
    if (op.t === "line") s = line(op.x1, op.y1, op.x2, op.y2, { stroke: op.stroke, w: op.w, dash: op.dash });
    else if (op.t === "poly") s = poly(op.pts, { stroke: op.stroke, w: op.w, dash: op.dash });
    else if (op.t === "marker") s = op.kind === "ring" ? `<circle cx="${n2(op.x)}" cy="${n2(op.y)}" r="${n2(op.r)}" fill="none" stroke="${op.stroke}" stroke-width="${op.w}"/>` : marker(op.kind, op.x, op.y, op.r, op.fill, op.stroke, op.w);
    else if (op.t === "text") s = text(op.x, op.y, op.s, op);
    else if (op.t === "rect") s = `<rect x="${n2(op.x)}" y="${n2(op.y)}" width="${n2(op.w)}" height="${n2(op.h)}"${op.rx ? ` rx="${op.rx}"` : ""} fill="${op.fill || "none"}"${op.stroke ? ` stroke="${op.stroke}" stroke-width="${op.sw || 1}"` : ""}/>`;
    else if (op.t === "polygon") s = `<polygon points="${op.pts.map((p) => n2(p[0]) + "," + n2(p[1])).join(" ")}" fill="${op.fill}"/>`;
    else if (op.t === "image") s = logoImg(logo, op.x, op.y, op.w, op.h);
    if (op.clip) a += s; else b += s;
  }
  return svgWrap(`<defs><clipPath id="${clipId}"><rect x="${fr.px}" y="${fr.py}" width="${fr.pw}" height="${fr.ph}"/></clipPath></defs><g clip-path="url(#${clipId})">${a}</g>${b}`);
}
// ---- DXF emitter (R12 ASCII - opens in BricsCAD / AutoCAD; Save As DWG there)
const ACI = [[1, "#c0392b"], [1, "#d63031"], [5, "#0984e3"], [5, "#1e3799"], [3, "#27ae60"], [30, "#f39c12"], [8, "#636e72"], [9, "#b2bec3"], [254, "#dfe6e9"], [7, "#2d3436"], [7, "#111111"], [7, "#222222"], [7, "#ffffff"], [8, "#555555"], [8, "#999999"], [6, "#8e44ad"]];
function aci(hex) { if (!hex || hex === "none") return null; hex = hex.toLowerCase(); const hit = ACI.find((c) => c[1] === hex); if (hit) return hit[0];
  const h = (x) => [parseInt(x.slice(1, 3), 16), parseInt(x.slice(3, 5), 16), parseInt(x.slice(5, 7), 16)], t = h(hex);
  let best = 7, bd = 1e9; for (const [c, hx] of ACI) { const v = h(hx), d = (v[0] - t[0]) ** 2 + (v[1] - t[1]) ** 2 + (v[2] - t[2]) ** 2; if (d < bd) { bd = d; best = c; } } return best; }
function clipSeg(x1, y1, x2, y2, xmin, ymin, xmax, ymax) {   // Liang-Barsky
  let t0 = 0, t1 = 1; const dx = x2 - x1, dy = y2 - y1;
  for (const [p, q] of [[-dx, x1 - xmin], [dx, xmax - x1], [-dy, y1 - ymin], [dy, ymax - y1]]) {
    if (p === 0) { if (q < 0) return null; } else { const r = q / p; if (p < 0) { if (r > t1) return null; if (r > t0) t0 = r; } else { if (r < t0) return null; if (r < t1) t1 = r; } }
  }
  return [x1 + t0 * dx, y1 + t0 * dy, x1 + t1 * dx, y1 + t1 * dy];
}
function sheetToDXF(sh, layers, title) {
  const fr = sh.fr, S = fr.scale, o = [];
  const g = (c, v) => { o.push(String(c)); o.push(String(v)); };
  const f = (v) => Number(v).toFixed(4);
  const P = (x, y) => fr.inv(x, y);
  const hW = (size) => size * 0.72 / fr.s;                     // text cap height in metres
  const dashW = (mmPaper) => mmPaper * S / 1000;
  g(0, "SECTION"); g(2, "HEADER"); g(9, "$ACADVER"); g(1, "AC1009"); g(9, "$INSUNITS"); g(70, 6); g(9, "$LTSCALE"); g(40, 1);
  const [ex0, ey0] = P(0, H), [ex1, ey1] = P(W, 0);
  g(9, "$EXTMIN"); g(10, f(ex0)); g(20, f(ey0)); g(30, 0); g(9, "$EXTMAX"); g(10, f(ex1)); g(20, f(ey1)); g(30, 0); g(0, "ENDSEC");
  g(0, "SECTION"); g(2, "TABLES");
  g(0, "TABLE"); g(2, "LTYPE"); g(70, 2);
  g(0, "LTYPE"); g(2, "CONTINUOUS"); g(70, 0); g(3, "Solid line"); g(72, 65); g(73, 0); g(40, 0);
  g(0, "LTYPE"); g(2, "DASHED"); g(70, 0); g(3, "__ __ __"); g(72, 65); g(73, 2); g(40, f(dashW(4.5))); g(49, f(dashW(3))); g(49, f(-dashW(1.5)));
  g(0, "ENDTAB");
  g(0, "TABLE"); g(2, "STYLE"); g(70, 1); g(0, "STYLE"); g(2, "STANDARD"); g(70, 0); g(40, 0); g(41, 1); g(50, 0); g(71, 0); g(42, 2.5); g(3, "txt"); g(4, ""); g(0, "ENDTAB");
  g(0, "TABLE"); g(2, "LAYER"); g(70, layers.length);
  for (const [n, c, lt] of layers) { g(0, "LAYER"); g(2, n); g(70, 0); g(62, c); g(6, lt || "CONTINUOUS"); }
  g(0, "ENDTAB"); g(0, "ENDSEC");
  g(0, "SECTION"); g(2, "ENTITIES");
  const col = (hex) => { const c = aci(hex); if (c !== null) g(62, c); };
  const LINE = (lay, a, b, hex, dash) => { g(0, "LINE"); g(8, lay); if (dash) g(6, "DASHED"); col(hex); g(10, f(a[0])); g(20, f(a[1])); g(30, 0); g(11, f(b[0])); g(21, f(b[1])); g(31, 0); };
  const seg = (op, x1, y1, x2, y2) => {
    if (op.clip) { const c = clipSeg(x1, y1, x2, y2, fr.px, fr.py, fr.px + fr.pw, fr.py + fr.ph); if (!c) return; [x1, y1, x2, y2] = c; }
    LINE(op.layer, P(x1, y1), P(x2, y2), op.stroke, op.dash);
  };
  const PLINE = (lay, pts, closed, hex, width, bulge) => { g(0, "POLYLINE"); g(8, lay); col(hex); g(66, 1); g(10, 0); g(20, 0); g(30, 0); g(70, closed ? 1 : 0); if (width) { g(40, f(width)); g(41, f(width)); }
    for (const p of pts) { g(0, "VERTEX"); g(8, lay); g(10, f(p[0])); g(20, f(p[1])); g(30, 0); if (bulge) g(42, bulge); } g(0, "SEQEND"); g(8, lay); };
  const SOLID = (lay, pts, hex) => { const q = pts.length === 3 ? [pts[0], pts[1], pts[2], pts[2]] : [pts[0], pts[1], pts[3], pts[2]];
    g(0, "SOLID"); g(8, lay); col(hex); [[10, 20, 30], [11, 21, 31], [12, 22, 32], [13, 23, 33]].forEach((k, i) => { g(k[0], f(q[i][0])); g(k[1], f(q[i][1])); g(k[2], 0); }); };
  const TEXT = (lay, x, y, s, size, hex, anchor, rot) => { const [wx, wy] = P(x, y), al = anchor === "middle" ? 1 : anchor === "end" ? 2 : 0;
    g(0, "TEXT"); g(8, lay); col(hex); g(10, f(wx)); g(20, f(wy)); g(30, 0); g(40, f(hW(size))); g(1, String(s).replace(/[\r\n]/g, " ")); if (rot) g(50, -rot); if (al) { g(72, al); g(11, f(wx)); g(21, f(wy)); g(31, 0); } };
  for (const op of sh.ops) {
    if (op.t === "line") seg(op, op.x1, op.y1, op.x2, op.y2);
    else if (op.t === "poly") { if (op.clip) { for (let i = 0; i + 1 < op.pts.length; i++) seg(op, op.pts[i][0], op.pts[i][1], op.pts[i + 1][0], op.pts[i + 1][1]); } else PLINE(op.layer, op.pts.map((p) => P(p[0], p[1])), false, op.stroke); }
    else if (op.t === "marker") {
      const [cx, cy] = P(op.x, op.y), r = op.r / fr.s, filled = op.fill && op.fill !== "none" && op.fill !== "#ffffff";
      if (op.kind === "s") { const sq = [[cx - r, cy - r], [cx + r, cy - r], [cx + r, cy + r], [cx - r, cy + r]]; if (filled) SOLID(op.layer, sq, op.fill); else PLINE(op.layer, sq, true, op.stroke); }
      else if (op.kind === "^") { const tri = [[cx, cy + 1.2 * r], [cx - 1.1 * r, cy - 0.8 * r], [cx + 1.1 * r, cy - 0.8 * r]]; SOLID(op.layer, tri, op.fill); }
      else if (filled) PLINE(op.layer, [[cx - r / 2, cy], [cx + r / 2, cy]], true, op.fill, r, 1);          // filled dot (donut)
      else { g(0, "CIRCLE"); g(8, op.layer); col(op.stroke); g(10, f(cx)); g(20, f(cy)); g(30, 0); g(40, f(r)); }
    }
    else if (op.t === "text") TEXT(op.layer, op.x, op.y, op.s, op.size || 10, op.fill, op.anchor, op.rot);
    else if (op.t === "rect") { const pts = [P(op.x, op.y), P(op.x + op.w, op.y), P(op.x + op.w, op.y + op.h), P(op.x, op.y + op.h)];
      if (op.fill && op.fill !== "none" && op.fill !== "#ffffff") SOLID(op.layer, pts, op.fill); if (op.stroke) PLINE(op.layer, pts, true, op.stroke); }
    else if (op.t === "polygon") { const pts = op.pts.map((p) => P(p[0], p[1])); if (pts.length <= 4) SOLID(op.layer, pts, op.fill); else for (let i = 1; i + 1 < pts.length; i++) SOLID(op.layer, [pts[0], pts[i], pts[i + 1]], op.fill); }
    else if (op.t === "image") { TEXT(title || "TITLE", op.x, op.y + op.h * 0.6, "ELEVATE SURVEYING", 18, "#2d3436", "start"); }
  }
  g(0, "ENDSEC"); g(0, "EOF");
  return o.join("\r\n") + "\r\n";
}
function labelOps(sh, layer, placed) {
  for (const p of placed) {
    if (p.far) sh.line(layer, p.x, p.y, p.anchor === "end" ? p.bx + p.bw : p.anchor === "middle" ? p.bx + p.bw / 2 : p.bx, p.by + p.bh / 2, { stroke: "#999999", w: 0.4 });
    sh.text(layer, p.lx, p.ly, p.s, { size: p.size, fill: p.fill || INK, weight: p.weight, italic: p.italic, anchor: p.anchor });
  }
}
function textBlock(sh, layer, x, y, s, n, o, step) { wrap(s, n).forEach((l, i) => sh.text(layer, x, y + i * step, l, o)); return wrap(s, n).length * step; }

// ---------------------------------------------------------------- sheet 2: setout check (internal)
function soRowsByPt(rows) { const m = new Map(); for (const r of rows) if (r.level.startsWith("SO ") && !["SO release", "SO overall", "SO field-calc", "SO unrelated"].includes(r.level)) m.set(r.pt, r); return m; }
function designLines(lines) { return lines.filter((l) => { const U = l.layer.toUpperCase(); return DESIGN_LAYER_KEYS.some((k) => U.includes(k)) && !U.includes("BDY"); }); }
const SO_LAYERS = [["SO-FRAME", 7], ["SO-GRID", 5, "DASHED"], ["SO-WALL", 8], ["SO-WALL-OTHER", 9], ["SO-PASS", 3], ["SO-FAIL", 1], ["SO-ERROR-ARROW", 1], ["SO-LABEL", 7], ["SO-TITLE", 7], ["SO-LEGEND", 7], ["SO-BANNER", 1]];
function buildSetout(R) {
  const so = soRowsByPt(R.rows), marks = R.survey.filter((p) => so.has(p.name));
  if (!marks.length) return null;
  const E = marks.map((p) => p.E), N = marks.map((p) => p.N), pad = 4;
  const fr = frameAtScale(Math.min(...E) - pad, Math.max(...E) + pad, Math.min(...N) - pad, Math.max(...N) + pad, 62, 110, 1180, 980), T = fr.T;
  const sh = new Sheet(fr);
  for (const l of designLines(R.lines)) {
    const U = l.layer.toUpperCase(), xy = l.xy.map((v) => T(v[0], v[1]));
    if (U.includes("GRID")) sh.poly("SO-GRID", xy, { stroke: "#0984e3", w: 0.7, dash: "7 4", clip: true });
    else if (U.includes("EXTERNAL") || U.includes("SUBFLOOR")) sh.poly("SO-WALL", xy, { stroke: MUTED, w: 0.9, clip: true });
    else sh.poly("SO-WALL-OTHER", xy, { stroke: "#dfe6e9", w: 0.45, clip: true });
  }
  const EX = 200, labels = [];
  for (const p of marks) {
    const r = so.get(p.name), c = COL[r.status], [x, y] = T(p.E, p.N), lay = r.status === "GREEN" ? "SO-PASS" : "SO-FAIL";
    const m = /dE ([+-]\d+), dN ([+-]\d+)/.exec(r.comment);
    if (m) { const dE = parseInt(m[1], 10) / 1000, dN = parseInt(m[2], 10) / 1000, [ax, ay] = T(p.E - dE * EX, p.N - dN * EX); sh.line("SO-ERROR-ARROW", ax, ay, x, y, { stroke: c, w: 1.3, clip: true }); const ang = Math.atan2(y - ay, x - ax);
      sh.polygon("SO-ERROR-ARROW", [[x, y], [x - 9 * Math.cos(ang - 0.4), y - 9 * Math.sin(ang - 0.4)], [x - 9 * Math.cos(ang + 0.4), y - 9 * Math.sin(ang + 0.4)]], c, { clip: true }); }
    sh.marker(lay, r.level.includes("corner") ? "s" : "o", x, y, 5, c, "#111111", 0.6, { clip: true });
    const err = r.dH === null ? "?" : f0(r.dH * 1000);
    labels.push({ x, y, mark: 6, s: `${last(p.name)}  ${err}mm`, size: 9, fill: r.status === "RED" ? c : INK, weight: r.status === "RED" ? "bold" : null, pri: r.status === "RED" ? 0 : 1 });
  }
  labels.sort((a, b) => a.pri - b.pri);
  labelOps(sh, "SO-LABEL", placeLabels(labels, fr));
  sh.rect("SO-FRAME", fr.px, fr.py, fr.pw, fr.ph, { stroke: INK, sw: 1 });
  const tl = titleLines(R);
  sh.text("SO-TITLE", 62, 30, tl[0], { size: 15 }); sh.text("SO-TITLE", 62, 52, tl[1], { size: 12 });
  sh.text("SO-TITLE", 62, 76, `BUILDING SETOUT - marks vs design, tolerance ${f0(R.tol.SETOUT_TOL * 1000)} mm (green = pass, red = fail)   Scale 1:${fr.scale} at A3`, { size: 13, weight: "bold" });
  const rel = R.rows.find((r) => r.level === "SO release");
  if (rel) { const s = "SETOUT: " + rel.comment.slice(0, 150), w = s.length * 11 * 0.55 + 20, x = fr.px + fr.pw / 2;
    sh.rect("SO-BANNER", x - w / 2, fr.py + 8, w, 21, { fill: COL[rel.status], rx: 5 }); sh.text("SO-BANNER", x, fr.py + 21, s, { size: 11, fill: "#ffffff", weight: "bold", anchor: "middle" }); }
  const ov = R.rows.find((r) => r.level === "SO overall");
  const lx = 1268; let ly = 860;
  if (ov) textBlock(sh, "SO-LEGEND", lx, 760, ov.comment, 48, { size: 9, fill: MUTED }, 13);
  sh.text("SO-LEGEND", lx, ly, "LEGEND", { size: 10, weight: "bold" }); ly += 18;
  for (const [k, lab] of [["s", "Corner mark (error = distance to design corner)"], ["o", "Grid peg (error = offset square to grid line)"]]) { sh.marker("SO-LEGEND", k, lx + 6, ly - 3, 5, "#999999", "#111111", 0.6); textBlock(sh, "SO-LEGEND", lx + 18, ly, lab, 34, { size: 8.5 }, 11); ly += 30; }
  sh.line("SO-LEGEND", lx - 2, ly - 3, lx + 14, ly - 3, { stroke: "#0984e3", w: 1.2, dash: "7 4" }); sh.text("SO-LEGEND", lx + 18, ly, "Design grid", { size: 8.5 }); ly += 18;
  sh.line("SO-LEGEND", lx - 2, ly - 3, lx + 14, ly - 3, { stroke: MUTED, w: 1.2 }); sh.text("SO-LEGEND", lx + 18, ly, "External / subfloor wall", { size: 8.5 }); ly += 18;
  sh.line("SO-LEGEND", lx - 2, ly - 3, lx + 14, ly - 3, { stroke: "#555555", w: 1.2 }); sh.text("SO-LEGEND", lx + 18, ly, `Corner error direction (x${EX})`, { size: 8.5 });
  sh.image(W - 230, 8, 206, 52);
  return sh;
}
function setoutSheet(R, logo) { const sh = buildSetout(R); return sh ? sheetToSVG(sh, logo, "soclip") : null; }
function setoutDXF(R) { const sh = buildSetout(R); return sh ? sheetToDXF(sh, SO_LAYERS, "SO-TITLE") : null; }

// ---------------------------------------------------------------- sheet 3: client setout sketch
const NOTES = ["Grid line pegs are set on the extension of the design grid line, clear of the works.",
  "Corner pegs mark the building / subfloor corners shown.",
  "Marks set to the design supplied - check against current approved plans before construction.",
  "Do not scale from this sketch. Report any disturbed mark to Elevate Surveying."];
const SK_LAYERS = [["SK-FRAME", 7], ["SK-BOUNDARY", 1], ["SK-GRID", 5, "DASHED"], ["SK-WALL", 7], ["SK-MARK", 7], ["SK-MARK-LABEL", 7], ["SK-NORTH", 7], ["SK-SCALEBAR", 7], ["SK-TITLE", 7], ["SK-LEGEND", 7], ["SK-NOTES", 7], ["SK-WATERMARK", 1]];
function buildSketch(R) {
  const so = soRowsByPt(R.rows), marks = R.survey.filter((p) => so.has(p.name));
  if (!marks.length) return null;
  const rel = R.rows.find((r) => r.level === "SO release");
  const E = marks.map((p) => p.E), N = marks.map((p) => p.N), pad = 6;
  const fr = frameAtScale(Math.min(...E) - pad, Math.max(...E) + pad, Math.min(...N) - pad, Math.max(...N) + pad, 50, 50, 1110, 1023), T = fr.T;
  const sh = new Sheet(fr);
  for (const l of R.lines) {
    const U = l.layer.toUpperCase(), xy = l.xy.map((v) => T(v[0], v[1]));
    if (U.includes("BDY") || U.includes("CADASTRAL")) sh.poly("SK-BOUNDARY", xy, { stroke: "#c0392b", w: 1.3, clip: true });
    else if (U.includes("GRID")) sh.poly("SK-GRID", xy, { stroke: "#0984e3", w: 0.8, dash: "9 5", clip: true });
    else if (U.includes("EXTERNAL") || U.includes("SUBFLOOR")) sh.poly("SK-WALL", xy, { stroke: INK, w: 0.95, clip: true });
  }
  const kinds = {}, labels = [];
  for (const p of marks) {
    const lv = so.get(p.name).level;
    let kind = lv.includes("corner") ? "Corner peg" : lv.includes("grid") ? "Grid line peg" : "Setout mark";
    if (p.code === "NAIL" || p.code === "NIP") kind = kind.replace("peg", "nail");
    kinds[kind] = (kinds[kind] || 0) + 1;
    const [x, y] = T(p.E, p.N);
    sh.marker("SK-MARK", kind.startsWith("Corner") ? "s" : "o", x, y, 5.5, kind.includes("nail") ? "#ffffff" : INK, INK, 1.5, { clip: true });
    labels.push({ x, y, mark: 6.5, s: last(p.name), size: 10, weight: "bold", pri: 0 });
  }
  labelOps(sh, "SK-MARK-LABEL", placeLabels(labels, fr));
  sh.rect("SK-FRAME", fr.px, fr.py, fr.pw, fr.ph, { stroke: INK, sw: 1.2 });
  const nx = fr.px + fr.pw - 50, ny = fr.py + 40;
  sh.polygon("SK-NORTH", [[nx, ny], [nx - 9, ny + 28], [nx, ny + 22], [nx + 9, ny + 28]], INK); sh.text("SK-NORTH", nx, ny + 48, "N", { size: 18, weight: "bold", anchor: "middle" });
  const spanM = fr.pw / fr.s, sb = spanM < 60 ? 5 : spanM < 150 ? 10 : 20, bx = fr.px + 30, byy = fr.py + fr.ph - 30;
  sh.rect("SK-SCALEBAR", bx, byy, sb * fr.s / 2, 6, { fill: INK }); sh.rect("SK-SCALEBAR", bx + sb * fr.s / 2, byy, sb * fr.s / 2, 6, { fill: "#ffffff", stroke: INK, sw: 1 });
  sh.text("SK-SCALEBAR", bx, byy - 6, "0", { size: 9 }); sh.text("SK-SCALEBAR", bx + sb * fr.s, byy - 6, `${sb} m`, { size: 9, anchor: "middle" });
  if (rel && rel.status === "RED") sh.text("SK-WATERMARK", fr.px + fr.pw / 2, fr.py + fr.ph / 2, "NOT FOR ISSUE - setout has not passed QA", { size: 44, fill: COL.RED, op: 0.22, weight: "bold", anchor: "middle", rot: -28 });
  const tx = 1195; let yy = 90;
  sh.text("SK-TITLE", tx, yy, "BUILDING SETOUT", { size: 24, weight: "bold" }); yy += 26;
  sh.text("SK-TITLE", tx, yy, "Setout marks placed", { size: 14, fill: MUTED }); yy += 44;
  for (const [lab, val] of [["JOB", R.info.job || R.fileName || ""], ["DATE SET OUT", R.jobdate], ["MARKS PLACED", String(marks.length)], ["SCALE", `1:${fr.scale} at A3`]]) {
    sh.text("SK-TITLE", tx, yy, lab, { size: 9, fill: MUTED, weight: "bold" }); yy += 18;
    for (const l of wrap(val, 28)) { sh.text("SK-TITLE", tx, yy, l, { size: 14, weight: "bold" }); yy += 18; }
    yy += 16;
  }
  yy += 6; sh.text("SK-LEGEND", tx, yy, "LEGEND", { size: 10, weight: "bold" }); yy += 22;
  for (const [mk, fill, lab] of [["s", INK, "Corner peg"], ["o", INK, "Grid line peg"], ["s", "#ffffff", "Corner nail"], ["o", "#ffffff", "Grid line nail"]]) {
    if (!kinds[lab]) continue;
    sh.marker("SK-LEGEND", mk, tx + 6, yy - 4, 5.5, fill, INK, 1.5); sh.text("SK-LEGEND", tx + 22, yy, `${lab} (${kinds[lab]})`, { size: 11 }); yy += 22;
  }
  for (const [c, dash, lab] of [["#0984e3", "9 5", "Design grid"], [INK, null, "External wall / subfloor"], ["#c0392b", null, "Boundary"]]) {
    sh.line("SK-LEGEND", tx - 2, yy - 4, tx + 16, yy - 4, { stroke: c, w: 1.4, dash }); sh.text("SK-LEGEND", tx + 22, yy, lab, { size: 11 }); yy += 22;
  }
  yy += 16; sh.text("SK-NOTES", tx, yy, "NOTES", { size: 10, weight: "bold" }); yy += 20;
  for (const nt of NOTES) { wrap("- " + nt, 44).forEach((l, i) => { sh.text("SK-NOTES", tx + (i ? 8 : 0), yy, l, { size: 9.5 }); yy += 13; }); yy += 8; }
  sh.image(tx - 4, H - 175, 240, 150);
  return sh;
}
function clientSketch(R, logo) { const sh = buildSketch(R); return sh ? sheetToSVG(sh, logo, "skclip") : null; }
function clientSketchDXF(R) { const sh = buildSketch(R); return sh ? sheetToDXF(sh, SK_LAYERS, "SK-TITLE") : null; }

// ---------------------------------------------------------------- DXF (R12, ASCII)
function dxf(R) {
  const L = [["QA_GREEN", 3], ["QA_ORANGE", 30], ["QA_RED", 1], ["QA_NOTCHECKED", 8], ["QA_STN", 7], ["QA_CALC", 6], ["QA_BDY", 1], ["QA_PLAN", 8],
    ["QA_TRAVERSE", 5], ["QA_RADIATION", 4], ["QA_RESECTION", 6], ["QA_SETOUT_PASS", 3], ["QA_SETOUT_FAIL", 1]];
  const o = [];
  const g = (c, v) => { o.push(String(c)); o.push(String(v)); };
  g(0, "SECTION"); g(2, "HEADER"); g(9, "$ACADVER"); g(1, "AC1009"); g(0, "ENDSEC");
  g(0, "SECTION"); g(2, "TABLES"); g(0, "TABLE"); g(2, "LAYER"); g(70, L.length);
  for (const [n, c] of L) { g(0, "LAYER"); g(2, n); g(70, 0); g(62, c); g(6, "CONTINUOUS"); }
  g(0, "ENDTAB"); g(0, "ENDSEC");
  g(0, "SECTION"); g(2, "ENTITIES");
  const xyz = (x, y, z = 0) => { g(10, x.toFixed(4)); g(20, y.toFixed(4)); g(30, (z || 0).toFixed(4)); };
  const ln = (a, b, lay) => { g(0, "LINE"); g(8, lay); xyz(a[0], a[1]); g(11, b[0].toFixed(4)); g(21, b[1].toFixed(4)); g(31, "0.0000"); };
  const pt = (x, y, z, lay) => { g(0, "POINT"); g(8, lay); xyz(x, y, z); };
  const circ = (x, y, r, lay) => { g(0, "CIRCLE"); g(8, lay); xyz(x, y); g(40, r); };
  const tx = (x, y, h, s, lay) => { g(0, "TEXT"); g(8, lay); xyz(x, y); g(40, h); g(1, String(s).replace(/[\r\n]/g, " ")); };
  for (const l of R.lines) { const U = l.layer.toUpperCase(), lay = (U.includes("CADASTRAL") || U.includes("BDY")) ? "QA_BDY" : "QA_PLAN"; for (let i = 0; i + 1 < l.xy.length; i++) ln(l.xy[i], l.xy[i + 1], lay); }
  const allbn = new Map(R.pts.map((p) => [p.name, p])), cbn = new Map(R.calc.map((c) => [c.name, c]));
  if (R.raw) for (const s of R.raw.setups) {
    if (!s.shots.length) continue;
    for (const sh of s.shots) { const p = allbn.get(sh.name); if (p) ln([s.E, s.N], [p.E, p.N], p.code === "STN" ? "QA_TRAVERSE" : "QA_RADIATION"); }
    if (s.bs) ln([s.E, s.N], [s.bs.E, s.bs.N], "QA_TRAVERSE");
    for (const r of s.res) { const q = cbn.get(r.name) || allbn.get(r.name); if (q) ln([s.E, s.N], [q.E, q.N], "QA_RESECTION"); }
  }
  for (const c of R.calc) if (c.code.startsWith("O")) { pt(c.E, c.N, 0, "QA_CALC"); tx(c.E + 0.15, c.N - 0.3, 0.2, `${c.name} ${c.code}`, "QA_CALC"); }
  const status = pointStatus(R.rows), so = soRowsByPt(R.rows), note = new Map();
  for (const r of R.rows) if (/^(L1|L2|DAT|SO )/.test(r.level) && r.status === status.get(r.pt) && r.dH !== null) note.set(r.pt, " D" + mm(r.dH));
  for (const p of R.survey) {
    const st = status.get(p.name) || "INFO";
    let lay = p.code === "STN" ? "QA_STN" : st === "INFO" ? "QA_NOTCHECKED" : "QA_" + st;
    if (so.has(p.name)) lay = so.get(p.name).status === "GREEN" ? "QA_SETOUT_PASS" : "QA_SETOUT_FAIL";
    pt(p.E, p.N, p.H || 0, lay); circ(p.E, p.N, p.code === "STN" ? 0.4 : 0.12, lay);
    tx(p.E + 0.2, p.N + 0.15, 0.22, `${p.name} ${p.code}${note.get(p.name) || ""}`, lay);
  }
  g(0, "ENDSEC"); g(0, "EOF");
  return o.join("\r\n") + "\r\n";
}

const API = { checkPlot, setoutSheet, clientSketch, setoutDXF, clientSketchDXF, dxf, W, H };
if (typeof module !== "undefined" && module.exports) module.exports = API; else root.FieldQARender = API;
})(typeof window !== "undefined" ? window : globalThis);
