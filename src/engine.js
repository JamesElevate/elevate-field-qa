/* Elevate Surveying - Field QA engine (JavaScript port of mxl_qa12.py).
   Runs in the browser (window.FieldQA) and in Node (module.exports) for testing. */
(function (root) {
"use strict";

// ---------------------------------------------------------------- settings
const PROFILES = {
  detail:    { label: "DETAIL SURVEY",   survey: [0.010, 0.020], calc: [0.010, 0.015], heights: true,  setout: false },
  cadastral: { label: "CADASTRAL",       survey: [0.005, 0.010], calc: [0.010, 0.015], heights: false, setout: false },
  bso:       { label: "BUILDING SETOUT", survey: [0.005, 0.010], calc: [0.010, 0.015], heights: true,  setout: true, setout_tol: 0.005 },
};
const SECTIONS = [["1", "CALC TO SURVEY (pickup)"], ["2", "SURVEY TO SURVEY (checks)"], ["3", "SETOUT TO DESIGN"]];
const FIELD_RE = /^(\d{6})([A-Z]{1,3})(GPS|GNSS|RTK)?-(\w+)$/;
const GPS_GREEN = 0.015, GPS_ORANGE = 0.025;
const SEARCH_R = 1.0, CHK_R = 0.30, HT_JUMP = 20.0;
const RL_RE = /(?:\bRL\s*|\bD\s+)(\d+\.\d+)/;
const FAMILY = { IPIN: ["OIP", "OP"], NIK: ["ONIK", "ONAIL"], NAIL: ["ONAIL", "ONIK", "ORAMNAIL"],
  SIK: ["OSIK", "OSI"], PM: ["OPM"], SCREW: ["OSCREW"], DH: ["ODH"], GI: ["OGI"], GONE: ["O"] };
const SYN = [["NIC", "NIK"], ["SIC", "SIK"]];
const SCAN_RE = /^S\d{1,3}$/;
const MARKS = new Set([...Object.keys(FAMILY), "NIC", "SIC"]);
const FD_RE = /\b(FD|FOUND)\b/i, PLD_RE = /\b(PLD|PLACED)\b/i;
const SETOUT_CODES = new Set(["DPY", "PEG", "NAIL", "NIP", "HUB", "PRO", "NINPROFILE", "SO"]);
const DESIGN_LAYER_KEYS = ["GRID", "WALL", "SUBFLOOR", "SLAB", "FOOTING", "SETOUT", "DESIGN", "ARCH"];
const MATCH_R = 0.050;
const SO_USED_R = 0.100;  // a controller-computed point is only graded when a setout mark was placed within this of it
const SO_RELATED = 1.0;   // setout marks / controller points further than this from any building design item are not part of the building setout
const COL = { GREEN: "#27ae60", ORANGE: "#f39c12", RED: "#d63031", INFO: "#7f8c8d" };

// job-dependent state (set by run)
let GREEN = 0.005, ORANGE = 0.010, BDY_GREEN = 0.010, BDY_ORANGE = 0.015, HEIGHTS = false, SETOUT_MODE = false, SETOUT_TOL = 0.005;
let _SURVEY = [];

// ---------------------------------------------------------------- helpers
function rhe(x) { // round half to even (matches Python round)
  const r = Math.round(x);
  if (Math.abs(x % 1) === 0.5) return (r % 2 === 0) ? r : r - 1;
  return r;
}
const hypot = Math.hypot, deg = (r) => r * 180 / Math.PI, rad = (d) => d * Math.PI / 180;
function f0(x) { const s = (Math.abs(x) < 0.5 && x < 0) ? "-0" : rhe(x).toString(); return s; }
function fs0(x) { const v = rhe(x); if (v === 0) return x < 0 ? "-0" : "+0"; return (v > 0 ? "+" : "") + v; }
function fx(x, n) { return Number(x).toFixed(n); }
function mm(v) { if (v === null || v === undefined) return ""; const r = rhe(v * 1000); return String(r === 0 ? 0 : r); }
function median(a) { const s = [...a].sort((x, y) => x - y); const n = s.length; return n % 2 ? s[(n - 1) / 2] : (s[n / 2 - 1] + s[n / 2]) / 2; }
function last(name) { const p = name.split("-"); return p[p.length - 1]; }
function minBy(arr, key) { let b = null, bk = Infinity; for (const x of arr) { const k = key(x); if (k < bk) { bk = k; b = x; } } return b; }
function norm(code) { for (const [a, b] of SYN) code = code.split(a).join(b); return code; }
function isScan(p) { return SCAN_RE.test(p.code) || p.layer.toUpperCase().includes("SCAN"); }
function d2(a, b) { return hypot(a.E - b.E, a.N - b.N); }
function dv(a, b) {
  if (a.H === null || b.H === null) return null;
  if (!b.survey && (b.H === 0 || b.H === 100)) return null;
  return a.H - b.H;
}
function row(level, status, pt, ref = "", dH = null, dV = null, comment = "") { return { level, status, pt, ref, dH, dV, comment }; }
const ORDER = ["INFO", "GREEN", "ORANGE", "RED"];
function worst(...ls) { return ls.reduce((a, b) => ORDER.indexOf(b) > ORDER.indexOf(a) ? b : a); }
function light(d, bdy = false) {
  if (d === null || d === undefined) return "INFO";
  d = rhe(Math.abs(d) * 1000) / 1000;
  const [g, o] = bdy ? [BDY_GREEN, BDY_ORANGE] : [GREEN, ORANGE];
  return d <= g ? "GREEN" : d <= o ? "ORANGE" : "RED";
}
function vl(v) { return (HEIGHTS && v !== null && v !== undefined) ? light(v) : "INFO"; }
function section(level) {
  if (level.startsWith("SO ")) return "3";
  if (level.startsWith("L1") || level.startsWith("DAT calc") || level.startsWith("L2 CHK vs calc")) return "1";
  return "2";
}
function rigidFit(pairs) {
  const n = pairs.length;
  let fx_ = 0, fy = 0, cx = 0, cy = 0;
  for (const [f, c] of pairs) { fx_ += f.E; fy += f.N; cx += c.E; cy += c.N; }
  fx_ /= n; fy /= n; cx /= n; cy /= n;
  let sxx = 0, sxy = 0;
  for (const [f, c] of pairs) {
    sxx += (c.E - cx) * (f.E - fx_) + (c.N - cy) * (f.N - fy);
    sxy += (c.E - cx) * (f.N - fy) - (c.N - cy) * (f.E - fx_);
  }
  const th = n >= 2 ? Math.atan2(sxy, sxx) : 0, ct = Math.cos(th), st = Math.sin(th);
  return { apply: (c) => { const x = c.E - cx, y = c.N - cy; return { E: fx_ + ct * x - st * y, N: fy + st * x + ct * y }; },
           rot: th, dE: fx_ - cx, dN: fy - cy, n };
}

// ---------------------------------------------------------------- XML helpers (tps namespace, prefix "tps:")
function lname(el) { const t = el.localName || el.nodeName; const i = t.indexOf(":"); return i >= 0 ? t.slice(i + 1) : t; }
function kids(el, name) { const out = []; if (!el) return out; for (let n = el.firstChild; n; n = n.nextSibling) if (n.nodeType === 1 && (name === undefined || lname(n) === name)) out.push(n); return out; }
function kid(el, path) { let cur = el; for (const p of path.split("/")) { if (!cur) return null; cur = kids(cur, p)[0] || null; } return cur; }
function txt(el, path, dflt = "") { const k = kid(el, path); if (!k) return dflt; return (k.textContent || ""); }
function fnum(el, path) { const t = txt(el, path, "0"); return parseFloat(t); }
function all(rootEl, name) { const out = []; const list = rootEl.getElementsByTagName("tps:" + name); for (let i = 0; i < list.length; i++) out.push(list[i]); return out; }
function desc(el, name) { const out = []; (function walk(n) { for (let c = n.firstChild; c; c = c.nextSibling) if (c.nodeType === 1) { if (lname(c) === name) out.push(c); walk(c); } })(el); return out; }

// ---------------------------------------------------------------- parsing
function parse(doc) {
  const root = doc.documentElement;
  const codes = {}, layers = {};
  for (const c of all(root, "CodeDescription")) if (c.getAttribute("id")) codes[c.getAttribute("id")] = txt(c, "Name").trim();
  for (const l of all(root, "Layer")) if (l.getAttribute("id")) layers[l.getAttribute("id")] = txt(l, "Name").trim();
  const pts = [], byid = {};
  for (const dp of all(root, "DesignPoint")) {
    const st = kid(dp, "Station");
    const neh = st ? kid(st, "Position/NEH") : null;
    if (!neh) continue;
    const cref = kid(dp, "Code/CodeDescription"), lay = kid(dp, "Layer");
    const attrs = desc(dp, "AttribValue").map((a) => (a.textContent || "").trim()).filter(Boolean);
    const h = txt(neh, "Height").trim();
    const name = txt(st, "Name").trim();
    const p = { id: dp.getAttribute("id"), name, N: fnum(neh, "North"), E: fnum(neh, "East"), H: h ? parseFloat(h) : null,
      code: cref ? (codes[cref.getAttribute("idRef")] || "").toUpperCase() : "",
      layer: lay ? (layers[lay.getAttribute("idRef")] || "") : "",
      ts: txt(st, "TimeStamp").trim(), flag: txt(st, "PointFlags").trim(),
      note: [txt(st, "Notes").trim(), ...attrs].filter(Boolean).join(" ") };
    if (Number.isNaN(p.H)) p.H = null;
    const m = FIELD_RE.exec(name), ocode = p.code.startsWith("O");
    p.survey = !!m || (!!p.ts && p.flag !== "manual" && !ocode);
    p.badname = p.survey && !m;
    p.crew = m ? m[1] + m[2] : (p.survey ? "(no prefix)" : "");
    p.gps = !!(m && m[3]);
    p.calc = !p.survey && (ocode || p.layer.toUpperCase().includes("BDY"));
    pts.push(p); byid[p.id] = p;
  }
  const crews = new Set(pts.filter((p) => p.survey && !p.badname).map((p) => p.crew));
  for (const p of pts) {
    if (p.badname && p.ts) {
      const t = Date.parse(p.ts); if (Number.isNaN(t)) continue;
      const dt = new Date(t + 10 * 3600 * 1000);
      const d = String(dt.getUTCFullYear()).slice(2) + String(dt.getUTCMonth() + 1).padStart(2, "0") + String(dt.getUTCDate()).padStart(2, "0");
      const same = [...crews].filter((c) => c.startsWith(d)).sort();
      if (same.length === 1) p.crew = same[0];
    }
  }
  const lines = [];
  for (const pl of all(root, "Polyline")) {
    let xy = kids(pl, "PointRef").filter((r) => byid[r.getAttribute("idRef")]).map((r) => [byid[r.getAttribute("idRef")].E, byid[r.getAttribute("idRef")].N]);
    if (!xy.length) for (const st of kids(pl, "Station")) { const neh = kid(st, "Position/NEH"); if (neh) xy.push([fnum(neh, "East"), fnum(neh, "North")]); }
    if (txt(pl, "Closed").trim().toLowerCase() === "true" && xy.length > 2) xy.push(xy[0]);
    const lay = kid(pl, "Layer");
    if (xy.length >= 2) lines.push({ layer: lay ? (layers[lay.getAttribute("idRef")] || "") : "", xy });
  }
  const info = { job: txt(root, "ProjectInfo/Name").trim(), app: txt(root, "ApplicationInfo/Application").trim(), version: txt(root, "ApplicationInfo/Version").trim() };
  return { pts, lines, info };
}

function parseRaw(doc, pts) {
  const root = doc.documentElement;
  const sess = kid(root, "ObservationSession");
  if (!sess) return null;
  const byid = {}; for (const p of pts) byid[p.id] = p;
  const setups = []; let cur = null;
  for (const e of kids(sess)) {
    const tag = lname(e), nm = txt(e, "Name").trim(), ht = fnum(e, "TargetHeight"), tm = txt(e, "Time");
    if (tag === "TSRawStn") {
      const neh = kid(e, "TSData/NEH");
      cur = { name: nm, time: tm, N: fnum(neh, "North"), E: fnum(neh, "East"), H: fnum(neh, "Height"), hi: ht, bs: null, bsobs: [], res: [], shots: [] };
      for (const resn of kids(e, "Resection")) for (const rs of kids(resn, "ResShot")) {
        const sd = kid(rs, "TSData/SD"), rr = kid(rs, "HVSResidials/SD");
        if (!sd || !rr) continue;
        const D = fnum(sd, "SlopeDistance");
        cur.res.push({ name: txt(rs, "Name").trim(), dist: D, lat: D * rad(fnum(rr, "HorizAngle")), dsd: fnum(rr, "SlopeDistance"),
          used: txt(rs, "UsedData").trim().toLowerCase() !== "none", coords: txt(rs, "UsedCoordinates").trim().toLowerCase() });
      }
      setups.push(cur); continue;
    }
    if (!cur) continue;
    if (tag === "TSRawBKB") { const bp = kid(e, "BSPoint"); cur.bs = bp ? (byid[bp.getAttribute("idRef")] || null) : null; continue; }
    const sd = kid(e, "TSData/SD");
    if (tag === "TSRawBS" && sd) {
      let va = fnum(sd, "VertAngle"); if (va > 180) va -= 360;
      const S = fnum(sd, "SlopeDistance");
      cur.bsobs.push({ hd: S * Math.cos(rad(va)), dz: S * Math.sin(rad(va)), ht });
    } else if (tag === "TSRawSS") cur.shots.push({ name: nm, time: tm, ht });
  }
  const merged = [];
  for (const st of setups) {
    const pv = merged[merged.length - 1];
    if (pv && pv.name === st.name && Math.abs(pv.N - st.N) < 0.001 && Math.abs(pv.E - st.E) < 0.001 &&
        (st.bs === null || (pv.bs && pv.bs.name) === st.bs.name)) {
      pv.shots.push(...st.shots); pv.bsobs.push(...st.bsobs); pv.res.push(...st.res); pv.hi = st.hi; continue;
    }
    merged.push(st);
  }
  const shot_setup = new Map();
  for (const st of merged) for (const sh of st.shots) shot_setup.set(sh.name, st);
  const order = merged.flatMap((st) => st.shots).slice().sort((a, b) => (a.time < b.time ? -1 : a.time > b.time ? 1 : 0));
  const tht = new Map(), prev_ht = new Map();
  order.forEach((sh, i) => { tht.set(sh.name, sh.ht); if (i > 0) prev_ht.set(sh.name, order[i - 1].ht); });
  return { setups: merged, shot_setup, tht, prev_ht };
}

// ---------------------------------------------------------------- target height diagnosis
function thDiag(raw, a, b, v) {
  if (!raw || v === null || v === undefined) return "";
  const ta = raw.tht.get(a.name), tb = raw.tht.get(b.name);
  if (ta === undefined || tb === undefined || Math.abs(ta - tb) < 0.05 || Math.abs(Math.abs(v) - Math.abs(ta - tb)) > 0.01) return "";
  let carried = [[a, ta], [b, tb]].filter(([p, t]) => raw.prev_ht.get(p.name) === t).map(([p]) => p);
  if (carried.length !== 1 && _SURVEY.length) {
    const near = _SURVEY.filter((p) => p !== a && p !== b && p.H !== null && p.code !== "CHK" && !p.code.startsWith("INV") && d2(p, a) < 20)
      .sort((x, y) => d2(x, a) - d2(y, a)).slice(0, 8);
    if (near.length >= 3) {
      const med = median(near.map((p) => p.H));
      const off = Math.abs(b.H - med) > Math.abs(a.H - med) ? b : a;
      const oth = off === a ? b : a;
      if (Math.abs(Math.abs(off.H - med) - Math.abs(oth.H - med)) > 0.5) carried = [off];
    }
  }
  if (carried.length === 1) {
    const bad = carried[0], good_t = bad === a ? tb : ta, bad_t = bad === a ? ta : tb;
    const fixed = bad.H + (bad_t - good_t), other = bad === a ? b : a;
    return `TARGET HEIGHT: ${last(bad.name)} used target height ${fx(bad_t, 3)}${raw.prev_ht.get(bad.name) === bad_t ? " (carried over from the previous shot)" : ""} - with ${fx(good_t, 3)} ` +
      `its height is ${fx(fixed, 3)}, agreeing with ${last(other.name)} to ${f0(Math.abs(fixed - other.H) * 1000)} mm. Fix the target height on ${last(bad.name)}`;
  }
  return `TARGET HEIGHT: height difference equals the target height difference (${fx(ta, 3)} vs ${fx(tb, 3)}) - one shot has the wrong target height`;
}

const PRIOR_RE = /^\d{6}[A-Z]*(GPS|GNSS|RTK)?-/;   // points from an earlier survey (e.g. 260701-224, 250424-117)
function isCalcMark(p) {
  const U = p.layer.toUpperCase();
  if (p.survey || PRIOR_RE.test(p.name) || p.code === "CHK" || p.code === "STN") return false;
  if (U.includes("BDY") || U.includes("CADASTRAL")) return true;
  if (U.includes("SURVEY") || DESIGN_LAYER_KEYS.some((k) => U.includes(k))) return false;
  return true;
}
function applyRawSurvey(pts, raw) {   // anything observed in the raw data was surveyed, whatever it is named or coded
  if (!raw) return;
  const crews = new Set(pts.filter((p) => p.survey && !p.badname).map((p) => p.crew));
  for (const p of pts) {
    if (raw.tht.has(p.name) && !p.survey) {
      p.survey = true; p.calc = false; p.badname = !FIELD_RE.test(p.name); p.crew = "(no prefix)";
      if (p.ts) {
        const t = Date.parse(p.ts); if (Number.isNaN(t)) continue;
        const dt = new Date(t + 10 * 3600 * 1000);
        const d = String(dt.getUTCFullYear()).slice(2) + String(dt.getUTCMonth() + 1).padStart(2, "0") + String(dt.getUTCDate()).padStart(2, "0");
        const same = [...crews].filter((c) => c.startsWith(d)).sort();
        if (same.length === 1) p.crew = same[0];
      }
    }
  }
}

// A re-observation of an existing mark is a check shot whatever it is coded: attribute/note says CHK or CHECK, or the
// note / name (e.g. NIK9002_stk) names an earlier surveyed or calc mark that the shot lands on (within CHK_R).
const CHK_TXT = /(^|[^A-Z])(CHK|CHECK)([^A-Z]|$)/;
function markChecks(pts, calcPts) {
  const survey = pts.filter((p) => p.survey), pool = [...survey, ...(calcPts || [])];
  for (const p of survey) {
    if (p.code === "CHK" || p.code === "STN") continue;
    const txt = (p.note || "").toUpperCase();
    let via = CHK_TXT.test(txt) ? "attribute says check" : null;
    if (!via) {
      const toks = [(p.note || "").trim().split(/\s+/)[0], p.name.split("_")[0]].filter((t) => t && t !== p.name);
      for (const tok of toks) {
        const T = tok.toUpperCase();
        const t = pool.find((q) => q !== p && (q.name.toUpperCase() === T || last(q.name).toUpperCase() === T || q.name.toUpperCase().endsWith("-" + T)) && (!q.survey || !q.ts || !p.ts || q.ts <= p.ts));
        if (t && d2(p, t) <= CHK_R) { via = `re-observes ${t.name}`; break; }
      }
    }
    if (via) { p.origCode = p.code; p.code = "CHK"; p.chkVia = via; }
  }
}

// ---------------------------------------------------------------- main checks
function checks(pts, calcPts, raw) {
  const survey = pts.filter((p) => p.survey);
  _SURVEY = survey;
  const fromFile = calcPts !== null;
  const calc = fromFile ? calcPts : pts.filter((p) => p.calc);
  // with a calc file every calc point counts, whatever it is coded or layered as; single file falls back to O-codes
  let calc_o = calc;
  if (!fromFile) { calc_o = calc.filter((c) => c.code.startsWith("O")); if (!calc_o.length) calc_o = calc; }
  const rows = [];

  if (fromFile) {
    const cbn = {}; for (const c of calc) cbn[c.name] = c;
    for (const p of pts) if (!p.survey && cbn[p.name]) {
      const c = cbn[p.name], d = d2(p, c);
      if (d > 0.0005) rows.push(row("DAT calc copy", "RED", p.name, `calc file ${c.name}`, d, null, "Calc point in survey file differs from calc file - altered/overwritten on controller"));
    }
  }
  for (const p of pts) if (!p.survey && p.ts && (p.calc || p.code.startsWith("O")))
    rows.push(row("DAT calc copy", "ORANGE", p.name, p.code, null, null, `O-coded point has a field timestamp (${p.ts.slice(0, 16)}) - field shot given a calc code, or calc stored over in the field`));
  const bad = survey.filter((p) => p.badname).map((p) => p.name);
  if (bad.length) rows.push(row("DAT naming", "ORANGE", `${bad.length} points`, bad.slice(0, 12).join(", ") + (bad.length > 12 ? " ..." : ""), null, null,
    "Surveyed points not named YYMMDD+initials-number (" + bad.slice(0, 15).join(", ") + ") - can be confused with calc numbering"));

  // calc file: same PM at two positions
  const pmgrp = new Map();
  for (const c of calc_o) { const m = /^OPM(\d+)/.exec(c.code); if (m) { if (!pmgrp.has(m[1])) pmgrp.set(m[1], []); pmgrp.get(m[1]).push(c); } }
  for (const [num, cs] of pmgrp) for (let i = 0; i < cs.length; i++) for (let j = i + 1; j < cs.length; j++) {
    const d = d2(cs[i], cs[j]);
    if (d > GREEN) rows.push(row("DAT calc dup", "ORANGE", `PM ${num}`, `calc pts ${cs[i].name} & ${cs[j].name}`, d, null,
      `Calc file holds PM ${num} at two positions ${f0(d * 1000)} mm apart (${cs[i].name} ${cs[i].note} / ${cs[j].name} ${cs[j].note}) - which one is the plan value?`));
  }
  // control marks
  const control = new Map(), calcNamesAll = new Set(calc_o.map((c) => c.name));
  if (raw) for (const st of raw.setups) {
    if (!st.shots.length) continue;
    const used = [...new Map(st.res.filter((r) => r.used && r.coords !== "vertical" && calcNamesAll.has(r.name)).map((r) => [r.name, r])).values()];
    let resOk = false;
    if (used.length >= 3 && used.every((r) => rhe(hypot(r.lat, r.dsd) * 1000) <= BDY_ORANGE * 1000)) {
      resOk = true;
      const worst = Math.max(...used.map((r) => hypot(r.lat, r.dsd)));
      rows.push(row("L1 resection", "INFO", st.name, `${used.length} calc marks`, worst, null,
        `Resection on ${used.length} calc marks (${used.map((r) => r.name).join(", ")}) with all residuals within ${f0(BDY_ORANGE * 1000)} mm (worst ${f0(worst * 1000)} mm) - the marks check each other, so they count as independent agreeing marks in the best fit`));
    } else for (const r of st.res) if (r.used && r.coords !== "vertical" && !control.has(r.name)) control.set(r.name, `resection pt for ${st.name}`);
    if (st.bs && !st.bs.survey && !control.has(st.bs.name) && !(resOk && used.some((r) => r.name === st.bs.name))) control.set(st.bs.name, `backsight for ${st.name}`);
  }
  // L1 found marks vs calc, matched by position
  const pairs = [];
  for (const f of survey) {
    if (SETOUT_MODE && (f.layer.toUpperCase() === "SETOUT" || SETOUT_CODES.has(f.code))) continue;
    const code = norm(f.code);
    let fam = FAMILY[code];
    if (!fam && !FD_RE.test(f.note)) continue;
    fam = fam || ["O"];
    let c = calc_o.length ? minBy(calc_o, (c) => d2(f, c)) : null;
    if (c && !c.code) {   // a coded calc point at (nearly) the same spot beats a bare vertex
      const coded = calc_o.filter((x) => x.code && d2(f, x) <= d2(f, c) + 0.005);
      if (coded.length) c = minBy(coded, (x) => d2(f, x));
    }
    if (c && d2(f, c) <= SEARCH_R) {
      const cc = norm(c.code);
      const same = code === "GONE" || cc === code || fam.some((x) => cc.startsWith(x)) || (cc.startsWith("O") && cc.slice(1).startsWith(code));
      pairs.push({ f, c, ok: code !== "GONE", d: d2(f, c), ctl: control.get(c.name) || null, same });
      continue;
    }
    if (c && code !== "GONE") {
      const near = `nearest calc ${c.name} ${c.code} @ ${fx(d2(f, c), 2)} m`;
      if (PLD_RE.test(f.note)) rows.push(row("L1 no calc", "INFO", f.name, near, null, null, "Placed mark (PLD) - no calc expected. " + f.note));
      else if (FD_RE.test(f.note)) rows.push(row("L1 no calc", "INFO", f.name, near, null, null, "Found mark (FD) with no calc within 1 m - mark not in the calc file? " + f.note));
      else rows.push(row("L1 no calc", "ORANGE", f.name, near, null, null, `${f.code} with no calc within ${fx(SEARCH_R, 1)} m and not attributed FD or PLD - record whether found or placed. ` + f.note));
    }
  }
  const crewsL1 = [...new Set(pairs.map((p) => p.f.crew))].sort();
  for (const crew of crewsL1) {
    const grp = pairs.filter((p) => p.f.crew === crew);
    const cand = grp.filter((p) => p.ok && p.d <= 0.3 && !PLD_RE.test(p.f.note));
    let fit = null, use = [];
    const resid = (ft, p) => { const q = ft.apply(p.c); return hypot(p.f.E - q.E, p.f.N - q.N); };
    if (cand.length >= 2) {
      let best = null;
      for (let i = 0; i < cand.length; i++) for (let j = i + 1; j < cand.length; j++) {
        const ft = rigidFit([[cand[i].f, cand[i].c], [cand[j].f, cand[j].c]]);
        const inl = cand.filter((p) => resid(ft, p) <= BDY_ORANGE);
        if (inl.length < 2) continue;
        const ft2 = rigidFit(inl.map((p) => [p.f, p.c]));
        const rms = Math.sqrt(inl.reduce((s, p) => s + resid(ft2, p) ** 2, 0) / inl.length);
        if (!best || inl.length > best.n || (inl.length === best.n && -rms > -best.rms)) best = { n: inl.length, rms, ft: ft2, inl };
      }
      if (best) { fit = best.ft; use = best.inl; }
    }
    if (fit) {
      const rms = Math.sqrt(use.reduce((s, p) => s + resid(fit, p) ** 2, 0) / use.length);
      const out = cand.filter((p) => !use.includes(p)).map((p) => p.f.name);
      const indep = use.filter((p) => !p.ctl), weak = indep.length < 3;
      rows.push(row("L1 best fit", weak ? "RED" : (rms > BDY_GREEN ? "ORANGE" : "INFO"), `crew ${crew}`, `${indep.length} independent / ${use.length} marks`, null, null,
        `Calc fitted to ${use.length} agreeing marks (${use.map((p) => last(p.f.name)).join(", ")}): shift E ${fs0(fit.dE * 1000)} N ${fs0(fit.dN * 1000)} mm, rotation ${fs0(deg(fit.rot) * 3600)}", RMS ${f0(rms * 1000)} mm` +
        (out.length ? `; disagree with the rest, left out: ${out.join(", ")}` : "") +
        (indep.length < use.length ? `; ${use.length - indep.length} of these were used to set up the instrument (${use.filter((p) => p.ctl).map((p) => last(p.f.name) + " = " + p.ctl).join(", ")}) so agree by construction` : "") +
        (weak ? `; REVIEW - only ${indep.length} independent agreeing marks, below the 3-mark minimum (2 acceptable only in exceptional circumstances - justify on file)` : "")));
    } else if (grp.some((p) => p.ok)) {
      rows.push(row("L1 best fit", "RED", `crew ${crew}`, "no fit", null, null, "REVIEW - fewer than 2 found marks agree with the calc; boundary position not confirmed by a best fit"));
    }
    for (const p of grp) {
      const f = p.f, c = p.c; let r, tag;
      if (fit) { const q = fit.apply(c); r = hypot(f.E - q.E, f.N - q.N); tag = `best-fit ${f0(r * 1000)} mm (raw ${f0(p.d * 1000)} mm)` + ((use.includes(p) || !p.ok) ? "" : " - not part of the fit"); }
      else { r = p.d; tag = `raw offset ${f0(r * 1000)} mm - no other agreeing mark to best-fit against`; }
      if (p.ctl && p.ok) rows.push(row("L1 vs calc", "INFO", f.name, `${c.name} (${c.code || "no code"})`, r, dv(f, c), `Control mark - ${p.ctl}, agrees by construction, not an independent check; ${tag}`));
      else if (PLD_RE.test(f.note)) rows.push(row("L1 vs calc", "INFO", f.name, `${c.name} (${c.code || "no code"})`, r, null, `Mark noted PLACED - new mark, not graded against the original calc; ${tag}. ` + f.note));
      else if (norm(f.code) === "GONE") rows.push(row("L1 vs calc", "INFO", f.name, `${c.name} (${c.code || "no code"})`, r, null, `Mark recorded GONE - position shot for reference only, not graded; ${tag}`));
      else if (!p.ok) { /* nothing */ }
      else rows.push(row("L1 vs calc", light(r, true), f.name, `${c.name} (${c.code || "no code"})`, r, dv(f, c),
        (tag + ". " + (p.same ? "" : (`Code ${f.code} vs calc ${c.code} - matched by position` + (r > BDY_ORANGE ? " - code differs AND it is well out: probably a different mark. " : ". "))) + f.note).trim()));
    }
  }

  // L2 check shots
  const sbn = new Map(survey.map((p) => [p.name, p]));
  const atRisk = new Map();
  const known = pts.filter((p) => (!p.survey && p.H !== null) || (!p.survey && p.code));
  for (const c of calc) if (!known.includes(c)) known.push(c);
  for (const k of survey.filter((p) => p.code === "CHK")) {
    const pool = survey.filter((p) => p !== k && (!k.ts || !p.ts || p.ts < k.ts));
    const near = pool.filter((p) => d2(k, p) <= CHK_R).sort((a, b) => ((a.code === "CHK") - (b.code === "CHK")) || (d2(k, a) - d2(k, b)));
    const tgt = near.length ? near[0] : (pool.length ? minBy(pool, (p) => d2(k, p)) : null);
    const ctgt = calc_o.length ? minBy(calc_o, (c) => d2(k, c)) : null;
    const ktgt = known.length ? minBy(known, (c) => d2(k, c)) : null;
    if (tgt && d2(k, tgt) <= CHK_R) {
      const dh = d2(k, tgt), v = dv(k, tgt), st = worst(light(dh), vl(v));
      let com = "";
      if (HEIGHTS && v !== null && Math.abs(v) > ORANGE && light(dh) === "GREEN") com = thDiag(raw, k, tgt, v) || "Horizontal fine but height out - check target/prism height on this shot";
      const ss = raw ? (raw.shot_setup.get(k.name) || null) : null;
      if (ss && light(dh) !== "GREEN") {
        const ux = k.E - ss.E, uy = k.N - ss.N, L = hypot(ux, uy) || 1.0, mx = k.E - tgt.E, my = k.N - tgt.N;
        const along = (mx * ux + my * uy) / L, across = (mx * uy - my * ux) / L, sec = deg(across / L) * 3600;
        let diag = `miss ${f0(Math.abs(across) * 1000)} mm across the line (${f0(Math.abs(sec))}" at ${f0(L)} m) / ${f0(Math.abs(along) * 1000)} mm along`;
        if (Math.abs(across) > 2 * Math.abs(along)) diag += " - ORIENTATION/POINTING: check if the instrument moved or the circle slipped";
        else if (Math.abs(along) > 2 * Math.abs(across)) diag += " - DISTANCE: check prism/target constant, target centring";
        const prev = ss.shots.filter((sh) => sh.time < k.ts);
        let lastchk = -1; prev.forEach((sh, i) => { if ((sbn.get(sh.name) || {}).code === "CHK") lastchk = i; });
        const after = prev.slice(lastchk + 1).filter((sh) => (sbn.get(sh.name) || {}).code !== "CHK");
        const risk = after.map((sh) => last(sh.name));
        if (risk.length && Math.abs(across) > 2 * Math.abs(along) && light(dh) === "RED") {
          diag += `; shots since the last check on this setup at risk: ${risk.slice(0, 20).join(", ")}` + (risk.length > 20 ? " ..." : "");
          for (const sh of after) if (!atRisk.has(sh.name)) atRisk.set(sh.name, [k.name, sec, ss]);
        }
        com = (com ? com + "; " : "") + diag;
      }
      const others = survey.filter((p) => p !== k && p !== tgt && d2(p, tgt) <= Math.max(CHK_R / 6, 3 * dh) && !(raw && ss && raw.shot_setup.get(p.name) === ss));
      const agree = others.filter((p) => d2(p, k) <= GREEN);
      if (light(dh) !== "GREEN" && agree.length >= 1)
        com = (com ? com + "; " : "") + `${agree.length} other obs of this mark (${agree.map((p) => last(p.name)).join(", ")}) agree with this check within ${f0(GREEN * 1000)} mm - the original shot ${last(tgt.name)} looks like the outlier (pole not plumb / wrong target?)`;
      rows.push(row("L2 CHK vs own", st, k.name, `${tgt.name} (${tgt.code})`, dh, v, com));
    } else if (ctgt && d2(k, ctgt) <= CHK_R) {
      const dh = d2(k, ctgt);
      rows.push(row("L2 CHK vs calc", light(dh, true), k.name, `${ctgt.name} (${ctgt.code})`, dh, dv(k, ctgt), "Check shot to a calc mark (no earlier own shot of it)"));
    } else if (ktgt && d2(k, ktgt) <= CHK_R) {
      const dh = d2(k, ktgt), bdy = ktgt.code.startsWith("O") || ktgt.layer.toUpperCase().includes("BDY");
      rows.push(row("L2 CHK vs known", light(dh, bdy), k.name, `${ktgt.name} (${ktgt.code || ktgt.layer})`, dh, dv(k, ktgt), "Check shot to a known point from an earlier survey / the calc file"));
    } else {
      rows.push(row("L2 CHK vs own", "RED", k.name, "-", null, null, `CHK shot does not land within ${f0(CHK_R * 1000)} mm of anything - checked to the wrong point?`));
    }
  }
  // at-risk shots
  const l2 = new Map(rows.filter((r) => r.level.startsWith("L2 CHK")).map((r) => [r.pt, r]));
  const cleared = new Map();
  for (const [nm, [kn, sec, ss]] of [...atRisk]) {
    if (!cleared.has(kn)) {
      const kt = sbn.get(kn).ts;
      const later = ss.shots.filter((sh) => sh.time > kt && (sbn.get(sh.name) || {}).code === "CHK" && l2.has(sh.name) && l2.get(sh.name).dH !== null && light(l2.get(sh.name).dH) === "GREEN").map((sh) => sh.name);
      cleared.set(kn, later);
      if (later.length && l2.has(kn)) {
        const r = l2.get(kn);
        r.comment = r.comment.split("; shots since")[0].replace(" - ORIENTATION/POINTING: check if the instrument moved or the circle slipped", "") +
          ` - but later check(s) ${later.map(last).join(", ")} on this setup are good, so the orientation did NOT move: the target or its earlier observation (${last(r.ref.split(" ")[0])}) is suspect (pole not plumb / target moved)`;
      }
    }
    if (cleared.get(kn).length) { atRisk.delete(nm); continue; }
    const p = sbn.get(nm);
    const disp = hypot(p.E - ss.E, p.N - ss.N) * rad(Math.abs(sec) / 3600);
    if (light(disp) === "GREEN") { atRisk.delete(nm); continue; }
    const reObs = survey.filter((q) => q !== p && q.code === p.code && q.ts > p.ts && d2(q, p) < 0.5 && p.code !== "" && p.code !== "CHK");
    let com;
    if (isScan(p) && reObs.length) { const q = minBy(reObs, (q) => d2(q, p)); com = `Shot while orientation had moved (${f0(Math.abs(sec))}" - see CHK ${last(kn)}); re-observed as ${last(q.name)} - make sure registration/processing uses ${last(q.name)}, not this one`; }
    else com = `Shot while orientation had moved (${f0(Math.abs(sec))}" - see CHK ${last(kn)}) - position unreliable, re-observe or discard`;
    rows.push(row("L2 at-risk shot", light(disp), nm, p.code, disp, null, `moved ~${f0(disp * 1000)} mm by the rotation. ` + com));
  }
  // scan control repeats
  const scans = survey.filter(isScan);
  for (let i = 0; i < scans.length; i++) for (let j = i + 1; j < scans.length; j++) {
    const a = scans[i], b = scans[j];
    if (a.code !== b.code) continue;
    const d = d2(a, b), v = (a.H !== null && b.H !== null) ? a.H - b.H : null;
    let com = `Scan control ${a.code} observed twice`;
    if (HEIGHTS && v !== null && Math.abs(v) > 0.1) com += "; " + (thDiag(raw, a, b, v) || `heights differ by ${fx(Math.abs(v), 3)} m - check target height on one of these shots`);
    if (atRisk.has(a.name) || atRisk.has(b.name)) com += "; one shot is from the disturbed setup (see at-risk shot)";
    rows.push(row("L2b repeat obs", worst(light(d), vl(v)), a.name, `${b.name} (${b.code})`, d, v, com));
  }
  // repeat observations of marks
  const marks = survey.filter((p) => (MARKS.has(norm(p.code)) || norm(p.code) === "BM") && norm(p.code) !== "GONE");
  const done = new Set();
  for (const a of marks) for (const b of marks) {
    if (a === b || done.has(b.name + "\u0000" + a.name) || norm(a.code) !== norm(b.code)) continue;
    const d = d2(a, b), other = a.crew !== b.crew;
    if (!((other && d < SEARCH_R) || (!other && d < 0.05))) continue;
    const cands = marks.filter((x) => x !== a && norm(x.code) === norm(a.code) && x.crew === b.crew);
    if (minBy(cands, (x) => d2(a, x)) !== b) continue;
    done.add(a.name + "\u0000" + b.name);
    const v = dv(a, b);
    const td = HEIGHTS ? thDiag(raw, a, b, v) : "";
    if (a.gps !== b.gps) {
      const g = (x) => rhe(Math.abs(x) * 1000) <= GPS_GREEN * 1000 ? "GREEN" : rhe(Math.abs(x) * 1000) <= GPS_ORANGE * 1000 ? "ORANGE" : "RED";
      rows.push(row("L2b GPS vs TS", worst(g(d), (HEIGHTS && v !== null) ? g(v) : "INFO"), a.name, `${b.name} (${b.code})`, d, v,
        `Same ${a.code} by RTK GPS and total station (GPS tolerance ${f0(GPS_GREEN * 1000)}/${f0(GPS_ORANGE * 1000)} mm). ` + (b.note || a.note)));
      continue;
    }
    rows.push(row("L2b repeat obs", worst(light(d), vl(v)), a.name, `${b.name} (${b.code})`, d, v,
      (td ? td + "; " : "") + `Same ${a.code} surveyed twice` + (other ? ` by ${a.crew} and ${b.crew}` : " (same day)")));
  }
  // raw setups
  let setups = [];
  if (raw && raw.setups.length) {
    rows.push(...rawRows(raw, survey));
    if (HEIGHTS) {
      for (const r of rows) {
        if (r.level.startsWith("L2 CHK") && r.dV !== null && Math.abs(r.dV) > GREEN) {
          const ss = raw.shot_setup.get(r.pt) || null, bz = ss ? (ss.bsdz === undefined ? null : ss.bsdz) : null;
          if (bz !== null && Math.abs(bz) > GREEN && Math.abs(r.dV - bz) < 0.015) {
            const hz = light(r.dH) !== "GREEN" ? r.comment : "";
            r.comment = (hz ? hz + "; HEIGHT: " : "") + `Height out by about the same as this setup's backsight height misclose (${fs0(bz * 1000)} mm on ${last(ss.name)}) - ` +
              `setup height error (instrument height at ${last(ss.name)} or at the station it was carried from), not a target height on this shot`;
          }
        }
      }
      for (const r of rows) {
        if (r.level === "RAW backsight" && r.dV !== null && Math.abs(r.dV) > ORANGE && r.comment.includes("Distance fine")) {
          const nm = r.pt.split(" @")[0];
          const nAff = rows.filter((x) => x.level.startsWith("L2 CHK") && x.comment.includes("backsight height misclose") && x.comment.includes(`on ${last(nm)})`)).length;
          const tlab = r.pt.includes(" @") ? r.pt.split(" @")[1].slice(0, 5) : "";
          const ss = raw.setups.find((t) => t.name === nm && t.time.slice(11, 16) === tlab) || null;
          r.comment = `Reciprocal heights disagree by ${fs0(r.dV * 1000)} mm while the distance agrees - instrument height measured wrong at one end ` +
            `(HI ${ss ? fx(ss.hi, 3) : "?"} here) or the station height carried in wrong; ${nAff} check shot(s) confirm it; all ${ss ? ss.shots.length : 0} shots from this setup carry it`;
        }
      }
    }
  } else setups = inferSetups(survey, rows);
  // heights: RLs and datum
  const ctl = survey.filter((p) => p.H !== null && p.H !== 0 && (MARKS.has(p.code) || ["STN", "BM", "CHK", "RL"].includes(p.code)));
  const rls = [];
  for (const p of survey) {
    if (HEIGHTS && (p.code === "PM" || p.code === "BM") && p.H !== null && p.H !== 0) {
      const m = RL_RE.exec(p.note);
      if (m && parseFloat(m[1]) > 0) {
        const rl = parseFloat(m[1]), dp = m[1].split(".")[1].length, d = p.H - rl, allow = dp < 3 ? 0.5 * Math.pow(10, -dp) : 0;
        rls.push([p, rl, d, allow]);
      }
    }
  }
  if (rls.length && HEIGHTS) {
    const big = rls.filter((x) => Math.abs(x[2]) > 5.0);
    if (big.length && big.length === rls.length) {
      const base = median(rls.map((x) => x[2]));
      rows.push(row("L1 height datum", "ORANGE", "job", `${rls.length} RL mark(s)`, null, null,
        `Job heights are on a different datum: ${base >= 0 ? "+" : ""}${fx(base, 3)} m from the RL(s) recorded on ` + rls.map((x) => `${last(x[0].name)} (RL ${fx(x[1], 3)})`).join(", ") +
        " - reduce to AHD in the office" + (rls.length === 1 ? "; only one RL mark, so the datum offset itself is unchecked" : "")));
      if (rls.length > 1) for (const [p, rl, d, allow] of rls) rows.push(row("L1 RL vs known", light(Math.max(0, Math.abs(d - base) - allow)), p.name, `RL ${fx(rl, 3)}`, null, d - base, "RL mark vs the others after removing the common datum offset"));
    } else {
      for (const [p, rl, d, allow] of rls) rows.push(row("L1 RL vs known", light(Math.max(0, Math.abs(d) - allow)), p.name, `RL ${fx(rl, 3)} (from note)`, null, d,
        "Field height vs RL recorded on the mark" + (allow ? ` (RL given to 2 dp, ${f0(allow * 1000)} mm allowed for rounding)` : "")));
    }
  }
  if (ctl.length && HEIGHTS) {
    const med = median(ctl.map((p) => p.H));
    for (const p of ctl) if (Math.abs(p.H - med) > HT_JUMP)
      rows.push(row("DAT height", "RED", p.name, `job median ${fx(med, 2)} m`, null, p.H - med, `Height ~${f0(p.H - med)} m off the rest of the job - wrong RL/HI or setup not reduced`));
  }
  if (!HEIGHTS) for (const r of rows) r.dV = null;
  const busts = rows.filter((r) => r.level === "RAW stn height" && r.dV !== null);
  for (const r of rows) if (r.level.startsWith("L2") && r.dV !== null && Math.abs(r.dV) > ORANGE)
    for (const b of busts) if (Math.abs(Math.abs(r.dV) - Math.abs(b.dV)) < 0.02)
      r.comment = `Height out by the same ~${f0(Math.abs(b.dV) * 1000)} mm as the station height error on setup ${b.pt} - not a target height problem`;
  return { survey, calc, setups, rows };
}

function inferSetups(survey, rows) {
  const timed = survey.filter((p) => p.ts).sort((a, b) => (a.ts < b.ts ? -1 : a.ts > b.ts ? 1 : 0));
  const setups = []; let cur = null;
  for (const p of timed) {
    if (!cur || (p.code === "STN" && cur.pts.length)) {
      cur = { stn: p.code === "STN" ? p : null, pts: [] }; setups.push(cur);
      if (p.code === "STN") continue;
    }
    cur.pts.push(p);
  }
  setups.forEach((s, i0) => {
    const i = i0 + 1, ps = s.pts; if (!ps.length) return;
    const chk = []; ps.forEach((p, j) => { if (p.code === "CHK") chk.push(j); });
    const nm = s.stn ? s.stn.name : "(first setup - no STN stored)";
    const span = `${ps[0].ts.slice(11, 16)}-${ps[ps.length - 1].ts.slice(11, 16)}Z, ${ps.length} shots`;
    const n = ps.length, start = chk.some((j) => j < Math.max(2, n * 0.25)), end = chk.some((j) => j >= n - Math.max(2, n * 0.25));
    const st = start && end ? "GREEN" : chk.length ? "ORANGE" : "RED";
    const miss = [["start", start], ["end", end]].filter((x) => !x[1]).map((x) => x[0]);
    rows.push(row("SET setup (inferred)", st, `Setup ${i}`, nm, null, null,
      `${span}; CHK shots: ${chk.map((j) => last(ps[j].name)).join(", ") || "none"}` + (miss.length ? `; missing ${miss.join(" & ")} check` : "")));
    s.label = `Setup ${i}`;
  });
  return setups;
}

function rawRows(raw, survey) {
  const rows = [], sbn = new Map(survey.map((p) => [p.name, p])), stns = raw.setups;
  stns.forEach((s) => {
    const lab = `${s.name} @${s.time.slice(11, 16)}Z`, active = s.shots.length > 0, b = s.bs;
    if (b && s.bsobs.length) {
      const chd = hypot(b.N - s.N, b.E - s.E), o = s.bsobs[s.bsobs.length - 1], dhd = o.hd - chd;
      const dz = b.H !== null ? (s.H + s.hi + o.dz - o.ht - b.H) : null;
      s.bsdz = dz;
      const st = worst(light(dhd), vl(dz));
      if (!active) rows.push(row("RAW backsight", "INFO", lab, `BS ${b.name}`, dhd, dz, "Station re-defined straight away, no shots taken - superseded" + (Math.abs(dhd) > ORANGE ? " (this definition did not fit the backsight)" : "")));
      else {
        let com = `Observed BS distance vs coordinates; ${s.bsobs.length} BS obs; HI ${fx(s.hi, 3)}`;
        if (HEIGHTS && dz !== null && Math.abs(dz) > ORANGE && light(dhd) === "GREEN") com = "Distance fine but height out - check HI/target height or the station's height " + `(stn H ${fx(s.H, 3)})`;
        rows.push(row("RAW backsight", st, lab, `BS ${b.name}`, dhd, dz, com));
      }
    } else if (b && active && !s.res.length) rows.push(row("RAW backsight", "ORANGE", lab, `BS ${b.name}`, null, null, "Orientation only - backsight not measured, so no distance/height check on this setup"));
    const usedRes = s.res.filter((r) => r.used);
    if (s.res.length && usedRes.every((r) => r.coords === "vertical")) {
      rows.push(row("RAW stn height", "INFO", lab, `from ${usedRes.map((r) => r.name).join(", ")}`, null, null, "Station height taken from a known point (height-only 'resection') - not a position resection"));
    } else if (s.res.length && (active || s === stns[stns.length - 1])) {
      const lastR = new Map(); for (const r of s.res) lastR.set(r.name, r);
      for (const r of lastR.values()) {
        const w = Math.max(Math.abs(r.lat), Math.abs(r.dsd));
        const isCalc = !sbn.has(r.name), hOnly = r.coords === "vertical";
        rows.push(row("RAW resection", r.used && !hOnly ? light(w, isCalc) : "INFO", lab, `pt ${r.name} @${f0(r.dist)}m`, null, null, (hOnly ? "height only - used for the station height, not position" : `residual lateral ${f0(r.lat * 1000)} mm, distance ${f0(r.dsd * 1000)} mm` + (isCalc && r.used ? " (calc mark - graded on the calc tolerance)" : "")) + (r.used ? "" : " - EXCLUDED from solution")));
      }
      if (usedRes.length <= 2) rows.push(row("RAW resection", "ORANGE", lab, `${usedRes.length} pts used`, null, null,
        `Only ${usedRes.length} points in the resection (${usedRes.map((r) => r.name).join(", ")}) - little or no redundancy, small residuals do not prove the setup. Excluded: ` +
        (s.res.filter((r) => !r.used).map((r) => `${r.name} (${f0(Math.max(Math.abs(r.lat), Math.abs(r.dsd)) * 1000)}mm)`).join(", ") || "none")));
    }
    if (!active) return;
    for (const t of stns) if (t !== s && hypot(t.N - s.N, t.E - s.E) < 0.005 && Math.abs(t.H - s.H) > ORANGE) {
      if (HEIGHTS && (s.H === 0 || s.H === 100)) {
        rows.push(row("RAW stn height", "RED", lab, `stn ${t.name} H ${fx(t.H, 3)}`, null, s.H - t.H,
          `Station height is the default ${fx(s.H, 3)} but the same position as ${t.name} has H ${fx(t.H, 3)} - every height from this setup (${s.shots.length} shots) and anything carried from it is out by ~${f0((s.H - t.H) * 1000)} mm`));
        break;
      }
    }
    const names = s.shots.map((x) => x.name), isChk = names.map((n) => (sbn.get(n) || {}).code === "CHK");
    const n = names.length, k = Math.min(5, n), start = isChk.slice(0, k).some(Boolean), end = isChk.slice(n - k).some(Boolean);
    const chks = names.filter((_, j) => isChk[j]).map(last), miss = [["start", start], ["end", end]].filter((x) => !x[1]).map((x) => x[0]);
    const st = !miss.length ? "GREEN" : (chks.length ? "ORANGE" : "RED");
    rows.push(row("SET setup", st, lab, `${n} shots`, null, null, `CHK shots: ${chks.join(", ") || "none"}` + (miss.length ? `; no CHK in the first/last ${k} shots (${miss.join(" & ")})` : "")));
  });
  return rows;
}

// ---------------------------------------------------------------- building setout
function perp(p, a, b) { const [x, y] = p, [x1, y1] = a, [x2, y2] = b, dx = x2 - x1, dy = y2 - y1, L = hypot(dx, dy); return [((x - x1) * dy - (y - y1) * dx) / L, ((x - x1) * dx + (y - y1) * dy) / (L * L), L]; }
const r4 = (v) => Math.round(v * 1e4) / 1e4;
function setoutRows(survey, allPts, calcPts, lines) {
  const rows = [];
  const dl = lines.filter((l) => DESIGN_LAYER_KEYS.some((k) => l.layer.toUpperCase().includes(k)) && !l.layer.toUpperCase().includes("BDY"));
  const segs = [];
  for (const l of dl) for (let i = 0; i + 1 < l.xy.length; i++) { const a = l.xy[i], b = l.xy[i + 1]; if (hypot(b[0] - a[0], b[1] - a[1]) > 0.05) segs.push([a, b, l.layer]); }
  const grids = segs.filter((s) => s[2].toUpperCase().includes("GRID")), others = segs.filter((s) => !s[2].toUpperCase().includes("GRID"));
  const corners = new Map();
  const addC = (x, y, lay) => { const kx = r4(x), ky = r4(y), key = kx + "," + ky; if (!corners.has(key)) corners.set(key, [[kx, ky], lay]); };
  for (const [a, b, lay] of others) { addC(a[0], a[1], lay); addC(b[0], b[1], lay); }
  for (const p of calcPts) if (DESIGN_LAYER_KEYS.some((k) => p.layer.toUpperCase().includes(k)) && !p.layer.toUpperCase().includes("GRID")) addC(p.E, p.N, p.layer + " pt " + p.name);
  for (let i = 0; i < grids.length; i++) for (let j = i + 1; j < grids.length; j++) {
    const [[x1, y1], [x2, y2]] = grids[i], [[x3, y3], [x4, y4]] = grids[j];
    const den = (x1 - x2) * (y3 - y4) - (y1 - y2) * (x3 - x4);
    if (Math.abs(den) < 1e-6 * hypot(x2 - x1, y2 - y1) * hypot(x4 - x3, y4 - y3)) continue;
    const px = ((x1 * y2 - y1 * x2) * (x3 - x4) - (x1 - x2) * (x3 * y4 - y3 * x4)) / den, py = ((x1 * y2 - y1 * x2) * (y3 - y4) - (y1 - y2) * (x3 * y4 - y3 * x4)) / den;
    addC(px, py, "grid intersection");
  }
  if (!segs.length) { rows.push(row("SO design", "RED", "setout", "no design", null, null, "Setout selected but no design grid/wall/subfloor lines found in the calc file")); return rows; }
  const cl = [...corners.values()];
  const nearCorner = (xy) => { const c = minBy(cl, (c) => hypot(xy[0] - c[0][0], xy[1] - c[0][1])); return [hypot(xy[0] - c[0][0], xy[1] - c[0][1]), c[0], c[1]]; };
  const nearGrid = (xy) => { let best = null; for (const [a, b, lay] of grids) { const [off, t, L] = perp(xy, a, b); if (!best || Math.abs(off) < Math.abs(best[0])) best = [off, t, L, a, b, lay]; } return best; };
  const nearSeg = (xy) => { let best = null; for (const [a, b, lay] of others) { const [off, t, L] = perp(xy, a, b); if (t >= -0.001 && t <= 1.001 && (!best || Math.abs(off) < Math.abs(best[0]))) best = [off, t, L, a, b, lay]; } return best; };
  const nearAny = (xy) => { let m = nearCorner(xy)[0]; for (const [a, b] of segs) { const [off, t] = perp(xy, a, b); if (t >= 0 && t <= 1) m = Math.min(m, Math.abs(off)); } return m; };
  const calcNames = new Set(calcPts.map((p) => p.name));
  const fcd = allPts.filter((p) => !p.survey && p.ts && !calcNames.has(p.name) && !p.code.startsWith("O"));
  const setMarks = survey.filter((m) => (m.layer.toUpperCase() === "SETOUT" || SETOUT_CODES.has(m.code)) && m.code !== "CHK" && m.code !== "STN" && !m.layer.toUpperCase().includes("CHECK"));
  const seen = new Set();
  for (const p of fcd) {
    const key = r4(p.E) + "," + r4(p.N), [d, v, lay] = nearCorner([p.E, p.N]), g = nearGrid([p.E, p.N]), dup = seen.has(key); seen.add(key);
    if (!setMarks.some((m) => hypot(m.E - p.E, m.N - p.N) <= SO_USED_R)) rows.push(row("SO field-calc", "INFO", p.name, "not set out", null, null, `Point computed on the controller with no setout mark within ${f0(SO_USED_R * 1000)} mm - not used to set out the building, so not graded`));
    else if (d <= 0.001) rows.push(row("SO field-calc", "GREEN", p.name, `= ${lay} vertex`, d, null, "Point computed on the controller - matches a design vertex in the calc file" + (dup ? " (duplicate)" : "")));
    else if (g && Math.abs(g[0]) <= 0.001) rows.push(row("SO field-calc", "GREEN", p.name, `on ${g[5]}`, Math.abs(g[0]), null, "Point computed on the controller - lies on a design grid line"));
    else if (nearAny([p.E, p.N]) > SO_RELATED) rows.push(row("SO field-calc", "ORANGE", p.name, `${fx(nearAny([p.E, p.N]), 1)} m from building design`, null, null, `Point computed on the controller is more than ${fx(SO_RELATED, 1)} m from any building design line - treated as not part of the building setout and not graded. Confirm it was not used to set out the building`));
    else rows.push(row("SO field-calc", "RED", p.name, `nearest ${lay} ${f0(d * 1000)} mm`, d, null, "Point computed on the controller does NOT match any design vertex or grid line - verify how it was derived before using it"));
  }
  const fcdXY = new Map(fcd.map((p) => [r4(p.E) + "," + r4(p.N), p.name]));
  const marks = survey.filter((p) => (p.layer.toUpperCase() === "SETOUT" || SETOUT_CODES.has(p.code)) && p.code !== "CHK" && p.code !== "STN" && !p.layer.toUpperCase().includes("CHECK"));
  const res = [];
  for (const p of marks) {
    const xy = [p.E, p.N]; let [d, v, lay] = nearCorner(xy); const g = nearGrid(xy), sgm = nearSeg(xy), tgt = fcdXY.get(v[0] + "," + v[1]);
    let alt = "";
    if (d <= MATCH_R && g && Math.abs(g[0]) < d) { alt = ` (also ${f0(d * 1000)} mm from a ${lay} corner)`; d = MATCH_R + 1; }
    else if (d <= MATCH_R && g && Math.abs(g[0]) <= MATCH_R) alt = ` (also ${f0(Math.abs(g[0]) * 1000)} mm off a grid line)`;
    let kind, err, desc_, com;
    if (d <= MATCH_R) {
      kind = "corner"; err = d; const ux = xy[0] - v[0], uy = xy[1] - v[1];
      desc_ = `${lay}` + (tgt ? ` (= field pt ${tgt})` : "");
      com = `Set ${f0(d * 1000)} mm from the design corner (dE ${fs0(ux * 1000)}, dN ${fs0(uy * 1000)})`;
      res.push([p, v]);
    } else if (g && Math.abs(g[0]) <= MATCH_R) {
      kind = "grid peg"; err = Math.abs(g[0]);
      const ext = g[1] > 1 ? (g[1] - 1) * g[2] : (g[1] < 0 ? -g[1] * g[2] : 0);
      desc_ = `${g[5]} line`; com = `Offset ${fs0(g[0] * 1000)} mm square to the grid line` + (ext > 0.01 ? ` (${fx(ext, 2)} m beyond the grid end)` : "");
    } else if (sgm && Math.abs(sgm[0]) <= MATCH_R) {
      kind = "on line"; err = Math.abs(sgm[0]); desc_ = `${sgm[5]} line`;
      com = `Offset ${fs0(sgm[0] * 1000)} mm square to the design line - no corner within ${f0(MATCH_R * 1000)} mm, position along the line not checked`;
    } else if (nearAny(xy) > SO_RELATED && !(g && Math.abs(g[0]) <= SO_RELATED)) {
      kind = "unrelated"; err = null; desc_ = `${fx(nearAny(xy), 1)} m from building design`;
      com = `More than ${fx(SO_RELATED, 1)} m from any building design line or grid - treated as not part of the building setout (e.g. a service or other design point) and not graded. Confirm what it was set to`;
    } else {
      const offs = g ? [Math.abs(g[0])] : [], rnd = offs.filter((o) => Math.abs(o - rhe(o * 2) / 2) <= 0.010 && o >= 0.4);
      kind = "unmatched"; err = null;
      desc_ = g ? `nearest corner ${fx(d, 3)} m, grid ${fx(Math.abs(g[0]), 3)} m` : `nearest corner ${fx(d, 3)} m`;
      com = rnd.length ? `Possible offset peg ~${fx(rhe(rnd[0] * 2) / 2, 1)} m off the grid - confirm intended offset` : "Set mark does not land on any design corner, grid or wall line within 50 mm - what was this set to?";
    }
    const st = kind === "unrelated" ? "ORANGE" : err !== null ? (rhe(err * 1000) <= SETOUT_TOL * 1000 ? "GREEN" : "RED") : "RED";
    rows.push(row(`SO ${kind}`, st, p.name, desc_, err, null, com + alt + (p.note ? `. ${p.note}` : "")));
  }
  if (res.length >= 3) {
    const pr = res.map(([p, v]) => [{ E: p.E, N: p.N }, { E: v[0], N: v[1] }]);
    const ft = rigidFit(pr), rr = pr.map(([f, c]) => { const q = ft.apply(c); return hypot(f.E - q.E, f.N - q.N); });
    const rawMean = hypot(pr.reduce((s, [f, c]) => s + f.E - c.E, 0) / pr.length, pr.reduce((s, [f, c]) => s + f.N - c.N, 0) / pr.length);
    rows.push(row("SO overall", rawMean <= SETOUT_TOL ? "INFO" : "ORANGE", `${pr.length} corners`, "design vs set", rawMean, null,
      `Corner marks vs design: common shift E ${fs0(ft.dE * 1000)} N ${fs0(ft.dN * 1000)} mm, rotation ${fs0(deg(ft.rot) * 3600)}", scatter after removing it ${f0(Math.sqrt(rr.reduce((s, r) => s + r * r, 0) / rr.length) * 1000)} mm RMS` +
      (rawMean > SETOUT_TOL && Math.max(...rr) <= SETOUT_TOL ? " - errors are mostly a common shift: check control/orientation for the setout" : "")));
  }
  const fails = rows.filter((r) => r.level.startsWith("SO ") && r.status === "RED");
  const nb = rows.filter((r) => r.level === "SO unrelated").length;
  rows.push(row("SO release", fails.length ? "RED" : "GREEN", "SETOUT", `${marks.length - nb} marks`, null, null,
    fails.length ? `DO NOT RELEASE - ${fails.length} setout item(s) outside ${f0(SETOUT_TOL * 1000)} mm or unverified: ` + fails.map((r) => last(r.pt)).join(", ") : `All setout marks within ${f0(SETOUT_TOL * 1000)} mm of design`));
  return rows;
}

// ---------------------------------------------------------------- run
function run(surveyDoc, calcDoc, job, opts = {}) {
  if (!PROFILES[job]) throw new Error("Unknown job type " + job);
  const prof = { ...PROFILES[job] };
  if (typeof opts.heights === "boolean" && opts.heights !== prof.heights) { prof.heights = opts.heights; prof.heightsOverride = true; }
  HEIGHTS = prof.heights; [GREEN, ORANGE] = prof.survey; [BDY_GREEN, BDY_ORANGE] = prof.calc; SETOUT_MODE = prof.setout; SETOUT_TOL = prof.setout_tol || 0.005;
  const S = parse(surveyDoc);
  let lines = S.lines, calcPts = null, calcAll = null;
  if (calcDoc) {
    const C = parse(calcDoc); calcAll = C.pts;
    calcPts = C.pts.filter(isCalcMark);
    if (C.lines.length) lines = C.lines;
  }
  const raw = parseRaw(surveyDoc, S.pts);
  applyRawSurvey(S.pts, raw);
  markChecks(S.pts, calcPts);
  const res = checks(S.pts, calcPts, raw);
  if (prof.setout) res.rows.push(...setoutRows(res.survey, S.pts, calcAll || S.pts.filter((p) => !p.survey), lines));
  const ts = res.survey.filter((p) => p.ts).map((p) => p.ts).sort();
  let jobdate = "";
  if (ts.length) { const t = new Date(Date.parse(ts[0]) + 10 * 3600 * 1000); const M = ["Jan", "Feb", "Mar", "Apr", "May", "Jun", "Jul", "Aug", "Sep", "Oct", "Nov", "Dec"]; jobdate = `${String(t.getUTCDate()).padStart(2, "0")} ${M[t.getUTCMonth()]} ${t.getUTCFullYear()}`; }
  const ord = { RED: 0, ORANGE: 1, GREEN: 2, INFO: 3 };
  const sorted = [...res.rows].sort((a, b) => section(a.level).localeCompare(section(b.level)) || (ord[a.status] - ord[b.status]) || (a.level < b.level ? -1 : a.level > b.level ? 1 : 0) || (a.pt < b.pt ? -1 : a.pt > b.pt ? 1 : 0));
  return { job, prof, tol: { GREEN, ORANGE, BDY_GREEN, BDY_ORANGE, SETOUT_TOL }, info: S.info, jobdate,
    pts: S.pts, lines, survey: res.survey, calc: res.calc, setups: res.setups, raw, rows: res.rows, sorted, hasCalc: !!calcDoc };
}

function csv(result) {
  const sname = Object.fromEntries(SECTIONS);
  const q = (s) => { s = String(s); return /[",\n]/.test(s) ? '"' + s.replace(/"/g, '""') + '"' : s; };
  const out = [["Section", "Status", "Check", "Point", "Compared to", "dH (mm)", "dV (mm)", "Comment"].join(",")];
  for (const r of result.sorted) out.push([sname[section(r.level)], r.status, r.level, r.pt, r.ref, mm(r.dH), mm(r.dV), r.comment].map(q).join(","));
  return out.join("\r\n") + "\r\n";
}

const API = { PROFILES, SECTIONS, COL, DESIGN_LAYER_KEYS, SETOUT_CODES, MARKS, run, csv, section, mm, f0, fx, last, d2, hypot, norm, isScan };
if (typeof module !== "undefined" && module.exports) module.exports = API; else root.FieldQA = API;
})(typeof window !== "undefined" ? window : globalThis);
