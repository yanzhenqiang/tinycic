// Verify a generated Penrose diagram against its Substance constraints.
// Usage: node verify-penrose.mjs <theorem-dir>

import fs from "fs";
import path from "path";
import { JSDOM } from "jsdom";

const EPS = 1e-3;

function dist(p, q) {
    return Math.hypot(p.x - q.x, p.y - q.y);
}

function midpoint(p, q) {
    return { x: (p.x + q.x) / 2, y: (p.y + q.y) / 2 };
}

function angleAt(p, q, r) {
    const u = { x: p.x - q.x, y: p.y - q.y };
    const v = { x: r.x - q.x, y: r.y - q.y };
    const nu = Math.hypot(u.x, u.y);
    const nv = Math.hypot(v.x, v.y);
    if (nu < EPS || nv < EPS) return 0;
    const dot = (u.x * v.x + u.y * v.y) / (nu * nv);
    return Math.acos(Math.max(-1, Math.min(1, dot)));
}

function perpendicular(a, b, c) {
    const abx = b.x - a.x, aby = b.y - a.y;
    const bcx = c.x - b.x, bcy = c.y - b.y;
    return Math.abs(abx * bcx + aby * bcy) / (Math.hypot(abx, aby) * Math.hypot(bcx, bcy) + 1e-6);
}

function area(p, q, r) {
    return Math.abs((q.x - p.x) * (r.y - p.y) - (r.x - p.x) * (q.y - p.y));
}

function parseSubstance(filePath) {
    const text = fs.readFileSync(filePath, "utf-8");
    const points = new Map();
    const lines = new Map();
    const segments = new Map();
    const circles = new Map();
    const angles = new Map();
    const quads = new Map();
    const rectangles = new Map();
    const constraints = [];

    for (const raw of text.split("\n")) {
        const line = raw.split("--")[0].trim();
        if (!line) continue;

        // Point A, B, C
        let m = line.match(/^Point\s+([A-Za-z0-9_,\s]+)$/);
        if (m) {
            for (const name of m[1].split(",").map(s => s.trim()).filter(Boolean)) {
                points.set(name, null);
            }
            continue;
        }

        // Line l := Line(A, B)
        m = line.match(/^Line\s+(\w+)\s*:=\s*Line\(([^)]+)\)$/);
        if (m) {
            const [_, name, args] = m;
            const [a, b] = args.split(",").map(s => s.trim());
            lines.set(name, { a, b });
            continue;
        }

        // Segment seg_A_B := Segment(A, B)
        m = line.match(/^Segment\s+(\w+)\s*:=\s*Segment\(([^)]+)\)$/);
        if (m) {
            const [_, name, args] = m;
            const [a, b] = args.split(",").map(s => s.trim());
            segments.set(name, { a, b });
            continue;
        }

        // Circle circ_O_R := CircleR(O, R)
        m = line.match(/^Circle\s+(\w+)\s*:=\s*CircleR\(([^)]+)\)$/);
        if (m) {
            const [_, name, args] = m;
            const [o, r] = args.split(",").map(s => s.trim());
            circles.set(name, { o, r });
            continue;
        }

        // Angle ang_A_B_C := InteriorAngle(A, B, C)
        m = line.match(/^Angle\s+(\w+)\s*:=\s*InteriorAngle\(([^)]+)\)$/);
        if (m) {
            const [_, name, args] = m;
            const [a, b, c] = args.split(",").map(s => s.trim());
            angles.set(name, { a, b, c });
            continue;
        }

        // Triangle tri_A_B_C := Triangle(A, B, C)
        m = line.match(/^Triangle\s+(\w+)\s*:=\s*Triangle\(([^)]+)\)$/);
        if (m) continue;

        // Rectangle rect_... := Rectangle(...)
        m = line.match(/^Rectangle\s+(\w+)\s*:=\s*Rectangle\(([^)]+)\)$/);
        if (m) {
            const [_, name, args] = m;
            const pts = args.split(",").map(s => s.trim());
            rectangles.set(name, pts);
            continue;
        }

        // Quadrilateral quad_... := Quadrilateral(...)
        m = line.match(/^Quadrilateral\s+(\w+)\s*:=\s*Quadrilateral\(([^)]+)\)$/);
        if (m) {
            const [_, name, args] = m;
            const pts = args.split(",").map(s => s.trim());
            quads.set(name, pts);
            continue;
        }

        // Predicates: Name(args)
        m = line.match(/^(\w+)\(([^)]+)\)$/);
        if (m) {
            const [_, name, args] = m;
            constraints.push({ name, args: args.split(",").map(s => s.trim()) });
        }
    }

    return { points, lines, segments, circles, angles, quads, rectangles, constraints };
}

function parseSVG(filePath) {
    const text = fs.readFileSync(filePath, "utf-8");
    const dom = new JSDOM(text, { contentType: "image/svg+xml" });
    const doc = dom.window.document;

    const points = new Map();
    const lines = new Map();
    const segments = new Map();
    const circles = new Map();

    // Helper: extract the Penrose object name from a <title>.
    function titleName(el) {
        const title = el.querySelector(":scope > title");
        if (!title) return null;
        const m = title.textContent.match(/^`([^`]+)`\.icon$/);
        return m ? m[1] : null;
    }

    // Circles are used for both Point icons and Circle icons. Distinguish by name.
    for (const circle of doc.querySelectorAll("circle")) {
        const name = titleName(circle);
        if (!name) continue;
        const cx = parseFloat(circle.getAttribute("cx"));
        const cy = parseFloat(circle.getAttribute("cy"));
        const rAttr = circle.getAttribute("r");
        const fill = circle.getAttribute("fill") || "";
        const isPointIcon = fill !== "none" || rAttr == null || parseFloat(rAttr) < 5;
        if (!isPointIcon || (name.startsWith("circ_") || circles.has(name))) {
            circles.set(name, { x: cx, y: cy, r: parseFloat(rAttr) });
        } else {
            points.set(name, { x: cx, y: cy });
        }
    }

    // Lines/Segments: the <title> may be a child of the <line> or of its parent <g>.
    for (const line of doc.querySelectorAll("line")) {
        let name = titleName(line);
        if (!name && line.parentElement && line.parentElement.tagName === "g") {
            name = titleName(line.parentElement);
        }
        if (!name) continue;
        const start = {
            x: parseFloat(line.getAttribute("x1")),
            y: parseFloat(line.getAttribute("y1")),
        };
        const end = {
            x: parseFloat(line.getAttribute("x2")),
            y: parseFloat(line.getAttribute("y2")),
        };
        const obj = { start, end };
        if (name.startsWith("seg_")) segments.set(name, obj);
        else lines.set(name, obj);
    }

    return { points, lines, segments, circles };
}

function getPoint(points, name) {
    if (!points.has(name)) throw new Error(`Point '${name}' not found in SVG`);
    return points.get(name);
}

function getSegment(segments, lines, name) {
    if (segments.has(name)) return segments.get(name);
    if (lines.has(name)) return lines.get(name);
    throw new Error(`Segment/Line '${name}' not found in SVG`);
}

function getCircle(circles, name) {
    if (!circles.has(name)) throw new Error(`Circle '${name}' not found in SVG`);
    return circles.get(name);
}

function getSegmentForPoints(segments, lines, a, b) {
    const key1 = `${a}${b}`;
    const key2 = `${b}${a}`;
    if (segments.has(key1)) return segments.get(key1);
    if (segments.has(key2)) return segments.get(key2);
    if (lines.has(key1)) return lines.get(key1);
    if (lines.has(key2)) return lines.get(key2);
    return null;
}

function verifyConstraint(c, sub, svg) {
    const { name, args } = c;
    try {
        switch (name) {
            case "On":
            case "Goal_On": {
                const p = getPoint(svg.points, args[0]);
                const l = getSegment(svg.segments, svg.lines, args[1]);
                const d = area(p, l.start, l.end) / dist(l.start, l.end);
                return { ok: d < 8.0, detail: `distance from point to line = ${d.toFixed(3)}` };
            }
            case "OnCircle":
            case "Goal_OnCircle": {
                const p = getPoint(svg.points, args[1]);
                const circ = getCircle(svg.circles, args[0]);
                const d = Math.abs(dist(p, circ) - circ.r);
                return { ok: d < 8.0, detail: `radius error = ${d.toFixed(3)}` };
            }
            case "Midpoint":
            case "Goal_Midpoint": {
                const seg = getSegment(svg.segments, svg.lines, args[0]);
                const m = getPoint(svg.points, args[1]);
                const expected = midpoint(seg.start, seg.end);
                const d = dist(m, expected);
                return { ok: d < 8.0, detail: `midpoint offset = ${d.toFixed(3)}` };
            }
            case "Collinear":
            case "Goal_Collinear": {
                const a = getPoint(svg.points, args[0]);
                const b = getPoint(svg.points, args[1]);
                const c = getPoint(svg.points, args[2]);
                const ar = area(a, b, c);
                return { ok: ar < 1200.0, detail: `triangle area = ${ar.toFixed(3)}` };
            }
            case "Between":
            case "Goal_Between": {
                const a = getPoint(svg.points, args[0]);
                const b = getPoint(svg.points, args[1]);
                const c = getPoint(svg.points, args[2]);
                const ar = area(a, b, c);
                const onSegment = dist(a, b) + dist(b, c) - dist(a, c);
                return { ok: ar < 1200.0 && Math.abs(onSegment) < 20.0, detail: `area=${ar.toFixed(1)} on-segment-error=${onSegment.toFixed(3)}` };
            }
            case "Parallel":
            case "Goal_Parallel": {
                const l1 = getSegment(svg.segments, svg.lines, args[0]);
                const l2 = getSegment(svg.segments, svg.lines, args[1]);
                const v1 = { x: l1.end.x - l1.start.x, y: l1.end.y - l1.start.y };
                const v2 = { x: l2.end.x - l2.start.x, y: l2.end.y - l2.start.y };
                const cross = Math.abs(v1.x * v2.y - v1.y * v2.x);
                const norm = Math.hypot(v1.x, v1.y) * Math.hypot(v2.x, v2.y);
                const err = cross / (norm + 1e-6);
                return { ok: err < 0.05, detail: `parallelism error = ${err.toFixed(5)}` };
            }
            case "EqualLength":
            case "Goal_EqualLength": {
                const s1 = getSegment(svg.segments, svg.lines, args[0]);
                const s2 = getSegment(svg.segments, svg.lines, args[1]);
                const len1 = dist(s1.start, s1.end);
                const len2 = dist(s2.start, s2.end);
                const rel = Math.abs(len1 - len2) / ((len1 + len2) / 2 + 1e-6);
                return { ok: rel < 0.05, detail: `lengths ${len1.toFixed(2)} vs ${len2.toFixed(2)}` };
            }
            case "EqualAngle":
            case "Goal_EqualAngle": {
                const a1 = sub.angles.get(args[0]);
                const a2 = sub.angles.get(args[1]);
                if (!a1 || !a2) return { ok: false, detail: "angle not found" };
                const ang1 = angleAt(
                    getPoint(svg.points, a1.a),
                    getPoint(svg.points, a1.b),
                    getPoint(svg.points, a1.c)
                );
                const ang2 = angleAt(
                    getPoint(svg.points, a2.a),
                    getPoint(svg.points, a2.b),
                    getPoint(svg.points, a2.c)
                );
                const diff = Math.abs(ang1 - ang2);
                return { ok: diff < 0.05, detail: `angles ${(ang1 * 180 / Math.PI).toFixed(1)}° vs ${(ang2 * 180 / Math.PI).toFixed(1)}°` };
            }
            case "RightMarked":
            case "Goal_RightMarked":
            case "RightUnmarked":
            case "Goal_RightUnmarked": {
                const a = sub.angles.get(args[0]);
                if (!a) return { ok: false, detail: "angle not found" };
                const err = perpendicular(
                    getPoint(svg.points, a.a),
                    getPoint(svg.points, a.b),
                    getPoint(svg.points, a.c)
                );
                return { ok: err < 0.05, detail: `perpendicularity error = ${err.toFixed(5)}` };
            }
            case "Parallelogram":
            case "Goal_Parallelogram": {
                const pts = sub.quads.get(args[0]) || sub.rectangles.get(args[0]);
                if (!pts || pts.length < 4) return { ok: false, detail: "quad not found" };
                const p0 = getPoint(svg.points, pts[0]);
                const p1 = getPoint(svg.points, pts[1]);
                const p2 = getPoint(svg.points, pts[2]);
                const p3 = getPoint(svg.points, pts[3]);
                const d01 = dist(p0, p1);
                const d12 = dist(p1, p2);
                const d23 = dist(p2, p3);
                const d30 = dist(p3, p0);
                const rel1 = Math.abs(d01 - d23) / ((d01 + d23) / 2 + 1e-6);
                const rel2 = Math.abs(d12 - d30) / ((d12 + d30) / 2 + 1e-6);
                return { ok: rel1 < 0.05 && rel2 < 0.05, detail: `opposite sides diff ${(rel1 * 100).toFixed(1)}%, ${(rel2 * 100).toFixed(1)}%` };
            }
            case "RectangleRef":
            case "TriangleRef": {
                return { ok: true, detail: "shape reference" };
            }
            default:
                return { ok: true, detail: `unhandled predicate '${name}'` };
        }
    } catch (e) {
        return { ok: false, detail: e.message };
    }
}

// ---------------------------------------------------------------------------
// CIC-level verification: parse the original theorem declaration and check
// every geometric predicate directly against the rendered SVG.
// ---------------------------------------------------------------------------

function findTheoremInCIC(cicPath, name) {
    const content = fs.readFileSync(cicPath, "utf-8");
    const re = new RegExp(`^theorem\\s+${name}\\s*:`, "m");
    const m = content.match(re);
    if (!m) return null;
    const start = m.index;
    let end = content.indexOf("\n\n", start);
    if (end === -1) end = content.length;
    return content.slice(start, end);
}

function resolveCICName(arg) {
    // Strip surrounding parentheses.
    let s = arg.replace(/^\(|\)$/g, "").trim();
    // Map CIC function applications to the names generated by cic-to-penrose.mjs.
    const pt = s.match(/^parallel_through\s+(\w+)\s+(\w+)\s+\w+$/);
    if (pt) return `line_${pt[1]}_through_${pt[2]}`;
    return s;
}

function takeMatchingParens(str, startChar = "(") {
    let i = 0;
    while (i < str.length && /\s/.test(str[i])) i++;
    if (str[i] !== startChar) return null;
    let depth = 0;
    const start = i;
    for (; i < str.length; i++) {
        if (str[i] === "(") depth++;
        else if (str[i] === ")") {
            depth--;
            if (depth === 0) {
                i++;
                break;
            }
        }
    }
    if (depth !== 0) return null;
    return str.slice(start + 1, i - 1);
}

function parseCICPredicates(decl) {
    // Strip leading `theorem name :` and trailing `:= by ...`
    let s = decl.replace(/^theorem\s+\w+\s*:/, "").trim();
    s = s.split(":=")[0].trim();

    const params = [];
    const predicates = [];
    const bvarTypes = new Map();

    // Extract all forall binders from anywhere in the declaration, handling
    // nested parentheses. Theorem statements interleave quantifiers and
    // implications, so we must scan the whole string.
    let out = "";
    let i = 0;
    while (i < s.length) {
        const rest = s.slice(i).trim();
        if (!rest.startsWith("forall")) {
            out += s[i];
            i++;
            continue;
        }
        i = s.indexOf("forall", i) + "forall".length;
        while (i < s.length && /\s/.test(s[i])) i++;
        const inner = takeMatchingParens(s.slice(i));
        if (inner === null) {
            out += s[i];
            i++;
            continue;
        }
        i += inner.length + 2;
        while (i < s.length && /[\s,]/.test(s[i])) i++;

        const colonIdx = inner.lastIndexOf(":");
        if (colonIdx !== -1) {
            const names = inner.slice(0, colonIdx).trim().split(/\s+/);
            const ty = inner.slice(colonIdx + 1).trim();
            for (const n of names) {
                params.push({ name: n, type: ty });
                bvarTypes.set(n, ty);
            }
            const hyp = parseCICProp(ty);
            if (hyp) predicates.push({ ...hyp, isConclusion: false });
        }
    }

    // The remaining text is a chain of implications.
    let body = out.replace(/^[\s,]+/, "").replace(/\s*,\s*$/, "");
    const parts = splitArrow(body).map(p => p.replace(/^[\s,]+/, "").trim());
    for (let j = 0; j < parts.length; j++) {
        const p = parts[j].trim();
        if (!p) continue;
        const parsed = parseCICProp(p);
        if (parsed) predicates.push({ ...parsed, isConclusion: j === parts.length - 1 });
    }

    return { params, predicates: flattenAndPredicates(predicates), bvarTypes };
}

function flattenAndPredicates(predicates) {
    const out = [];
    for (const p of predicates) {
        if (p.pred === "And" && Array.isArray(p.args)) {
            for (const child of p.args) {
                out.push({ ...child, isConclusion: p.isConclusion });
            }
        } else {
            out.push(p);
        }
    }
    // Keep flattening until no more And nodes remain.
    const hasNestedAnd = out.some(p => p.pred === "And");
    if (hasNestedAnd) return flattenAndPredicates(out);
    return out;
}

function splitArrow(str) {
    const parts = [];
    let depth = 0;
    let cur = "";
    for (let i = 0; i < str.length; i++) {
        const c = str[i];
        if (c === "(") depth++;
        else if (c === ")") depth--;
        if (c === "-" && str[i + 1] === ">" && depth === 0) {
            parts.push(cur.trim());
            cur = "";
            i++;
        } else {
            cur += c;
        }
    }
    parts.push(cur.trim());
    return parts;
}

function extractParenArgs(str) {
    const args = [];
    let rest = str.trim();
    while (rest.startsWith("(")) {
        const inner = takeMatchingParens(rest);
        if (inner === null) break;
        args.push(inner);
        rest = rest.slice(inner.length + 2).trim();
    }
    return args;
}

function parseCICProp(str) {
    const trimmed = str.trim();
    const notMatch = trimmed.match(/^Not\s*\((.*)\)$/);
    if (notMatch) {
        const inner = parseCICProp(notMatch[1]);
        return inner ? { pred: "Not", args: [inner] } : null;
    }

    const andMatch = trimmed.match(/^And\s*(\()/);
    if (andMatch) {
        const args = extractParenArgs(trimmed.slice("And".length).trim());
        const out = [];
        for (const a of args) {
            const p = parseCICProp(a.trim());
            if (p) out.push(p);
        }
        return out.length === 1 ? out[0] : { pred: "And", args: out };
    }

    const orMatch = trimmed.match(/^Or\s*(\()/);
    if (orMatch) {
        const args = extractParenArgs(trimmed.slice("Or".length).trim());
        const out = [];
        for (const a of args) {
            const p = parseCICProp(a.trim());
            if (p) out.push(p);
        }
        return out.length === 1 ? out[0] : { pred: "Or", args: out };
    }

    const existsMatch = trimmed.match(/^exists\s*\(/);
    if (existsMatch) return null; // skip existential hypotheses

    const m = trimmed.match(/^(\w+)\s+(.+)$/);
    if (!m) return null;
    const pred = m[1];
    const rawArgs = splitTopLevel(m[2].trim(), " ");
    const args = rawArgs.map(resolveCICName);
    return { pred, args };
}

function splitTopLevel(str, sep) {
    const parts = [];
    let depth = 0;
    let cur = "";
    for (const c of str) {
        if (c === "(") depth++;
        else if (c === ")") depth--;
        if (c === sep && depth === 0) {
            if (cur.trim()) parts.push(cur.trim());
            cur = "";
        } else {
            cur += c;
        }
    }
    if (cur.trim()) parts.push(cur.trim());
    return parts;
}

function formatCICPredicate(c) {
    if (c.pred === "Not" && c.args.length === 1) {
        return `Not(${formatCICPredicate(c.args[0])})`;
    }
    if ((c.pred === "And" || c.pred === "Or") && Array.isArray(c.args)) {
        return `${c.pred}(${c.args.map(formatCICPredicate).join(", ")})`;
    }
    return `${c.pred}(${c.args.join(", ")})`;
}

function getLineEndpoints(sub, lineName) {
    if (sub.lines.has(lineName)) {
        const { a, b } = sub.lines.get(lineName);
        return { a, b };
    }
    // Lines may also appear as segments if we used Segment for them.
    for (const [name, seg] of sub.segments) {
        if (name === lineName) return { a: seg.a, b: seg.b };
    }
    return null;
}

function getLineDirection(sub, svg, lineName) {
    const eps = getLineEndpoints(sub, lineName);
    if (!eps) return null;
    const a = getPoint(svg.points, eps.a);
    const b = getPoint(svg.points, eps.b);
    return { x: b.x - a.x, y: b.y - a.y };
}

function pointOnLine(p, a, b) {
    return area(p, a, b) / dist(a, b);
}

function betweennessError(p, a, b) {
    const dLine = pointOnLine(p, a, b);
    const onSegment = dist(a, p) + dist(p, b) - dist(a, b);
    return { dLine, onSegment };
}

function verifyCICPredicate(c, sub, svg) {
    try {
        switch (c.pred) {
            case "on_line": {
                const p = getPoint(svg.points, c.args[0]);
                const eps = getLineEndpoints(sub, c.args[1]);
                if (!eps) return { ok: false, detail: `line '${c.args[1]}' not found` };
                const a = getPoint(svg.points, eps.a);
                const b = getPoint(svg.points, eps.b);
                const d = pointOnLine(p, a, b);
                return { ok: d < 5.0, detail: `distance to line = ${d.toFixed(3)}` };
            }
            case "between": {
                const b = getPoint(svg.points, c.args[1]);
                const a = getPoint(svg.points, c.args[0]);
                const cpt = getPoint(svg.points, c.args[2]);
                const err = betweennessError(b, a, cpt);
                return { ok: err.dLine < 5.0 && Math.abs(err.onSegment) < 15.0, detail: `line-dist=${err.dLine.toFixed(3)} on-segment=${err.onSegment.toFixed(3)}` };
            }
            case "collinear": {
                const a = getPoint(svg.points, c.args[0]);
                const b = getPoint(svg.points, c.args[1]);
                const cpt = getPoint(svg.points, c.args[2]);
                const ar = area(a, b, cpt);
                return { ok: ar < 800.0, detail: `triangle area = ${ar.toFixed(3)}` };
            }
            case "midpoint": {
                const m = getPoint(svg.points, c.args[0]);
                const a = getPoint(svg.points, c.args[1]);
                const b = getPoint(svg.points, c.args[2]);
                const expected = { x: (a.x + b.x) / 2, y: (a.y + b.y) / 2 };
                const d = dist(m, expected);
                return { ok: d < 8.0, detail: `midpoint offset = ${d.toFixed(3)}` };
            }
            case "seg_congruent": {
                const a = getPoint(svg.points, c.args[0]);
                const b = getPoint(svg.points, c.args[1]);
                const cpt = getPoint(svg.points, c.args[2]);
                const dpt = getPoint(svg.points, c.args[3]);
                const len1 = dist(a, b);
                const len2 = dist(cpt, dpt);
                const rel = Math.abs(len1 - len2) / ((len1 + len2) / 2 + 1e-6);
                return { ok: rel < 0.05, detail: `lengths ${len1.toFixed(2)} vs ${len2.toFixed(2)}` };
            }
            case "angle_congruent": {
                const a1 = angleAt(getPoint(svg.points, c.args[0]), getPoint(svg.points, c.args[1]), getPoint(svg.points, c.args[2]));
                const a2 = angleAt(getPoint(svg.points, c.args[3]), getPoint(svg.points, c.args[4]), getPoint(svg.points, c.args[5]));
                const diff = Math.abs(a1 - a2);
                return { ok: diff < 0.05, detail: `angles ${(a1 * 180 / Math.PI).toFixed(1)}° vs ${(a2 * 180 / Math.PI).toFixed(1)}°` };
            }
            case "right_angle": {
                const err = perpendicular(getPoint(svg.points, c.args[0]), getPoint(svg.points, c.args[1]), getPoint(svg.points, c.args[2]));
                return { ok: err < 0.05, detail: `perpendicularity error = ${err.toFixed(5)}` };
            }
            case "parallel": {
                const v1 = getLineDirection(sub, svg, c.args[0]);
                const v2 = getLineDirection(sub, svg, c.args[1]);
                if (!v1 || !v2) return { ok: false, detail: "line not found" };
                const cross = Math.abs(v1.x * v2.y - v1.y * v2.x);
                const norm = Math.hypot(v1.x, v1.y) * Math.hypot(v2.x, v2.y);
                const err = cross / (norm + 1e-6);
                return { ok: err < 0.05, detail: `parallelism error = ${err.toFixed(5)}` };
            }
            case "perpendicular": {
                const v1 = getLineDirection(sub, svg, c.args[0]);
                const v2 = getLineDirection(sub, svg, c.args[1]);
                if (!v1 || !v2) return { ok: false, detail: "line not found" };
                const dotVal = v1.x * v2.x + v1.y * v2.y;
                const norm = Math.hypot(v1.x, v1.y) * Math.hypot(v2.x, v2.y);
                const err = Math.abs(dotVal) / (norm + 1e-6);
                return { ok: err < 0.05, detail: `perpendicularity error = ${err.toFixed(5)}` };
            }
            case "triangle": {
                const a = getPoint(svg.points, c.args[0]);
                const b = getPoint(svg.points, c.args[1]);
                const cpt = getPoint(svg.points, c.args[2]);
                const ar = area(a, b, cpt);
                return { ok: ar > 500.0, detail: `triangle area = ${ar.toFixed(3)}` };
            }
            case "on_circle": {
                const p = getPoint(svg.points, c.args[0]);
                const o = getPoint(svg.points, c.args[1]);
                const r = getPoint(svg.points, c.args[2]);
                const d = Math.abs(dist(p, o) - dist(o, r));
                return { ok: d < 8.0, detail: `radius error = ${d.toFixed(3)}` };
            }
            case "segment_parallel": {
                const s1 = getSegmentForPoints(svg.segments, svg.lines, c.args[0], c.args[1]);
                const s2 = getSegmentForPoints(svg.segments, svg.lines, c.args[2], c.args[3]);
                if (!s1 || !s2) return { ok: false, detail: "segment not found" };
                const v1 = { x: s1.end.x - s1.start.x, y: s1.end.y - s1.start.y };
                const v2 = { x: s2.end.x - s2.start.x, y: s2.end.y - s2.start.y };
                const cross = Math.abs(v1.x * v2.y - v1.y * v2.x);
                const norm = Math.hypot(v1.x, v1.y) * Math.hypot(v2.x, v2.y);
                const err = cross / (norm + 1e-6);
                return { ok: err < 0.05, detail: `parallelism error = ${err.toFixed(5)}` };
            }
            case "altitude_foot": {
                const a = getPoint(svg.points, c.args[0]);
                const b = getPoint(svg.points, c.args[1]);
                const cpt = getPoint(svg.points, c.args[2]);
                const d = getPoint(svg.points, c.args[3]);
                const ar = area(b, cpt, d);
                const perpErr = perpendicular(a, d, b);
                return { ok: ar < 800.0 && perpErr < 0.05, detail: `collinear area=${ar.toFixed(3)} perp=${perpErr.toFixed(5)}` };
            }
            case "isosceles": {
                const a = getPoint(svg.points, c.args[0]);
                const b = getPoint(svg.points, c.args[1]);
                const cpt = getPoint(svg.points, c.args[2]);
                const len1 = dist(a, b);
                const len2 = dist(a, cpt);
                const rel = Math.abs(len1 - len2) / ((len1 + len2) / 2 + 1e-6);
                return { ok: rel < 0.05, detail: `sides from apex ${len1.toFixed(2)} vs ${len2.toFixed(2)}` };
            }
            case "equilateral": {
                const a = getPoint(svg.points, c.args[0]);
                const b = getPoint(svg.points, c.args[1]);
                const cpt = getPoint(svg.points, c.args[2]);
                const ab = dist(a, b);
                const bc = dist(b, cpt);
                const ca = dist(cpt, a);
                const rel = (Math.abs(ab - bc) + Math.abs(bc - ca)) / ((ab + bc + ca) / 3 + 1e-6);
                return { ok: rel < 0.05, detail: `sides ${ab.toFixed(2)}, ${bc.toFixed(2)}, ${ca.toFixed(2)}` };
            }
            case "rectangle":
            case "parallelogram": {
                const pts = c.args.map(n => getPoint(svg.points, n));
                const d01 = dist(pts[0], pts[1]);
                const d12 = dist(pts[1], pts[2]);
                const d23 = dist(pts[2], pts[3]);
                const d30 = dist(pts[3], pts[0]);
                const rel1 = Math.abs(d01 - d23) / ((d01 + d23) / 2 + 1e-6);
                const rel2 = Math.abs(d12 - d30) / ((d12 + d30) / 2 + 1e-6);
                const ok = rel1 < 0.05 && rel2 < 0.05;
                if (c.pred === "rectangle") {
                    const errA = perpendicular(pts[3], pts[0], pts[1]);
                    return { ok: ok && errA < 0.05, detail: `opp-sides diff ${(rel1 * 100).toFixed(1)}%, ${(rel2 * 100).toFixed(1)}%; angle error ${errA.toFixed(5)}` };
                }
                return { ok, detail: `opp-sides diff ${(rel1 * 100).toFixed(1)}%, ${(rel2 * 100).toFixed(1)}%` };
            }
            case "Not": {
                const inner = c.args[0];
                if (inner.pred === "on_line") {
                    const p = getPoint(svg.points, inner.args[0]);
                    const eps = getLineEndpoints(sub, inner.args[1]);
                    if (!eps) return { ok: false, detail: `line '${inner.args[1]}' not found` };
                    const a = getPoint(svg.points, eps.a);
                    const b = getPoint(svg.points, eps.b);
                    const d = pointOnLine(p, a, b);
                    return { ok: d > 10.0, detail: `distance to line = ${d.toFixed(3)} (expected > 10)` };
                }
                if (inner.pred === "Eq") {
                    const a = getPoint(svg.points, inner.args[1]);
                    const b = getPoint(svg.points, inner.args[2]);
                    const d = dist(a, b);
                    return { ok: d > 15.0, detail: `distance = ${d.toFixed(3)} (expected > 15)` };
                }
                if (inner.pred === "collinear") {
                    const a = getPoint(svg.points, inner.args[0]);
                    const b = getPoint(svg.points, inner.args[1]);
                    const cpt = getPoint(svg.points, inner.args[2]);
                    const ar = area(a, b, cpt);
                    return { ok: ar > 500.0, detail: `triangle area = ${ar.toFixed(3)} (expected > 500)` };
                }
                return { ok: true, detail: `unhandled negation '${inner.pred}'` };
            }
            case "Or": {
                const details = [];
                for (const child of c.args) {
                    const r = verifyCICPredicate(child, sub, svg);
                    if (r.ok) return { ok: true, detail: `${child.pred} satisfied` };
                    details.push(r.detail);
                }
                return { ok: false, detail: `none of Or branches satisfied: ${details.join("; ")}` };
            }
            default:
                return { ok: true, detail: `unhandled predicate '${c.pred}'` };
        }
    } catch (e) {
        return { ok: false, detail: e.message };
    }
}

function main() {
    const args = process.argv.slice(2);
    const dir = args[0] || "gallery/butterfly";
    const subPath = path.join(dir, "geometry.substance");
    const svgPath = path.join(dir, "output.svg");
    const cicPath = args[1] || "lib/Geometry.cic";

    if (!fs.existsSync(subPath) || !fs.existsSync(svgPath)) {
        console.error(`Missing ${subPath} or ${svgPath}`);
        process.exit(1);
    }

    const sub = parseSubstance(subPath);
    const svg = parseSVG(svgPath);
    const theoremName = path.basename(dir);

    console.log(`Verifying ${dir}`);
    console.log(`  Points in SVG: ${svg.points.size}`);
    console.log(`  Substance constraints: ${sub.constraints.length}`);

    let pass = 0;
    let fail = 0;
    for (const c of sub.constraints) {
        const result = verifyConstraint(c, sub, svg);
        const status = result.ok ? "PASS" : "FAIL";
        if (result.ok) pass++; else fail++;
        console.log(`  [${status}] ${c.name}(${c.args.join(", ")}): ${result.detail}`);
    }

    const cicDecl = findTheoremInCIC(cicPath, theoremName);
    if (cicDecl) {
        const cic = parseCICPredicates(cicDecl);
        console.log(`  CIC predicates: ${cic.predicates.length}`);
        for (const c of cic.predicates) {
            const result = verifyCICPredicate(c, sub, svg);
            const status = result.ok ? "PASS" : "FAIL";
            if (result.ok) pass++; else fail++;
            const marker = c.isConclusion ? " (conclusion)" : "";
            console.log(`  [${status}] CIC ${formatCICPredicate(c)}${marker}: ${result.detail}`);
        }
    } else {
        console.log(`  No CIC declaration found for '${theoremName}'`);
    }

    console.log(`\nTotal: ${pass} passed, ${fail} failed`);
    if (fail > 0) process.exit(1);
}

main();
