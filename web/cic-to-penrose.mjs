// Parse .cic geometry declarations and generate Penrose trio files using the
// official Penrose Euclidean geometry domain/style.
// Usage: node cic-to-penrose.mjs <theorem-name> <out-dir> <cic-file>...

import fs from "fs";
import path from "path";
import { fileURLToPath } from "url";

const __dirname = path.dirname(fileURLToPath(import.meta.url));

const GEO_PREDICATES = {
    "on_line": { args: ["Point", "Line"] },
    "between": { args: ["Point", "Point", "Point"] },
    "seg_congruent": { args: ["Point", "Point", "Point", "Point"] },
    "angle_congruent": { args: ["Point", "Point", "Point", "Point", "Point", "Point"] },
    "parallel": { args: ["Line", "Line"] },
    "perpendicular": { args: ["Line", "Line"] },
    "collinear": { args: ["Point", "Point", "Point"] },
    "midpoint": { args: ["Point", "Point", "Point"] },
    "right_angle": { args: ["Point", "Point", "Point"] },
    "triangle": { args: ["Point", "Point", "Point"], shape: "Triangle" },
    "on_circle": { args: ["Point", "Point", "Point"] },
    "isosceles": { args: ["Point", "Point", "Point"] },
    "equilateral": { args: ["Point", "Point", "Point"] },
    "rectangle": { args: ["Point", "Point", "Point", "Point"], shape: "Rectangle" },
    "parallelogram": { args: ["Point", "Point", "Point", "Point"], shape: "Quadrilateral" },
    "segment_parallel": { args: ["Point", "Point", "Point", "Point"] },
    "altitude_foot": { args: ["Point", "Point", "Point", "Point"] },
};

function main() {
    const args = process.argv.slice(2);
    if (args.length < 3) {
        console.error("Usage: node cic-to-penrose.mjs <theorem-name> <out-dir> <cic-file>...");
        process.exit(1);
    }

    const theoremName = args[0];
    const outDir = args[1];
    const cicFiles = args.slice(2);

    let theorem = null;
    for (const file of cicFiles) {
        const content = fs.readFileSync(file, "utf-8");
        theorem = findTheorem(content, theoremName);
        if (theorem) break;
    }

    if (!theorem) {
        console.error(`Theorem '${theoremName}' not found.`);
        process.exit(1);
    }

    fs.mkdirSync(outDir, { recursive: true });

    fs.copyFileSync(path.join(__dirname, "geometry.domain"), path.join(outDir, "geometry.domain"));
    fs.copyFileSync(path.join(__dirname, "euclidean.style"), path.join(outDir, "geometry.style"));

    const substance = theoremToSubstance(theorem);
    fs.writeFileSync(path.join(outDir, "geometry.substance"), substance);

    console.log("Generated Penrose files:");
    console.log("  Domain:   ", path.join(outDir, "geometry.domain"));
    console.log("  Substance:", path.join(outDir, "geometry.substance"));
    console.log("  Style:    ", path.join(outDir, "geometry.style"));
}

function findTheorem(content, name) {
    const lines = content.split("\n");
    for (let i = 0; i < lines.length; i++) {
        const line = lines[i].trim();
        const prefix = `theorem ${name} :`;
        if (line.startsWith(prefix)) {
            let decl = line.slice(prefix.length).trim();
            for (let j = i + 1; j < lines.length; j++) {
                const nextLine = lines[j];
                if (nextLine.includes(":=")) {
                    decl += " " + nextLine.split(":=")[0].trim();
                    break;
                }
                decl += " " + nextLine.trim();
            }
            return { kind: "theorem", name, type: decl };
        }
    }
    return null;
}

function parsePiType(typeStr) {
    const params = [];
    let rest = typeStr.trim();

    const forallRegex = /^forall\s+/;
    if (forallRegex.test(rest)) rest = rest.replace(forallRegex, "").trim();

    while (true) {
        if (/^forall\s+/.test(rest)) rest = rest.replace(/^forall\s+/, "").trim();
        const binder = takeParens(rest);
        if (!binder) break;

        const binderContent = binder.content.trim();
        rest = rest.slice(binder.consumed.length).trim();

        const colonIdx = binderContent.lastIndexOf(":");
        if (colonIdx === -1) continue;

        const names = binderContent.slice(0, colonIdx).trim().split(/\s+/);
        const ty = binderContent.slice(colonIdx + 1).trim();

        for (const name of names) params.push({ name: name.trim(), type: ty });
    }

    const arrowParts = splitByArrow(rest);
    const conclusion = arrowParts.pop().trim();

    for (const hyp of arrowParts) {
        const trimmed = hyp.trim();
        if (trimmed) params.push({ name: `_hyp${params.length}`, type: trimmed });
    }

    return { params, conclusion };
}

function takeParens(str) {
    let i = 0;
    while (i < str.length && /\s/.test(str[i])) i++;
    if (str[i] !== "(") return null;

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

    const content = str.slice(start + 1, i - 1);
    let j = i;
    while (j < str.length && /\s/.test(str[j])) j++;
    if (str[j] === ",") j++;
    return { content, consumed: str.slice(0, j) };
}

function splitByArrow(str) {
    const parts = [];
    let depth = 0;
    let current = "";
    for (let i = 0; i < str.length; i++) {
        const c = str[i];
        if (c === "(") depth++;
        if (c === ")") depth--;
        if (c === "-" && str[i + 1] === ">" && depth === 0) {
            parts.push(current.trim());
            current = "";
            i++;
        } else {
            current += c;
        }
    }
    parts.push(current.trim());
    return parts;
}

function collectPredicates(str) {
    const out = [];
    let trimmed = str.trim();

    while (true) {
        const forallMatch = trimmed.match(/^forall\s*\(/);
        if (!forallMatch) break;
        const binder = takeParens(trimmed.slice(forallMatch[0].length - 1));
        if (!binder) break;
        const consumedLen = forallMatch[0].length - 1 + binder.consumed.length;
        const after = trimmed.slice(consumedLen).trim();
        if (after.startsWith(",")) trimmed = after.slice(1).trim();
        else if (after.startsWith("->")) trimmed = after.slice(2).trim();
        else trimmed = after;
    }

    const notMatch = trimmed.match(/^Not\s*\((.*)\)$/);
    if (notMatch) return out;

    const andMatch = trimmed.match(/^And\s*\(/);
    if (andMatch) {
        const afterAnd = trimmed.slice(andMatch[0].length - 1);
        let depth = 0;
        let start = 0;
        for (let i = 0; i < afterAnd.length; i++) {
            if (afterAnd[i] === "(") {
                if (depth === 0) start = i;
                depth++;
            } else if (afterAnd[i] === ")") {
                depth--;
                if (depth === 0) {
                    const arg = afterAnd.slice(start + 1, i);
                    out.push(...collectPredicates(arg));
                }
            }
        }
        return out;
    }

    const parts = splitByArrow(trimmed);
    for (const part of parts) {
        const p = part.trim();
        if (!p) continue;
        const m = p.match(/^(\w+)\s+(.+)$/);
        if (m && GEO_PREDICATES[m[1]]) out.push({ pred: m[1], argsStr: m[2] });
    }
    return out;
}

function parseArgs(str) {
    const args = [];
    let depth = 0;
    let current = "";
    for (const c of str) {
        if (c === "(") depth++;
        if (c === ")") depth--;
        if (c === " " && depth === 0) {
            if (current.trim()) args.push(current.trim());
            current = "";
        } else {
            current += c;
        }
    }
    if (current.trim()) args.push(current.trim());
    return args;
}

function cleanName(name) {
    return name.split(".")[0];
}

function argToName(argStr, bvarName) {
    const bvarMatch = argStr.match(/^BVar\((\d+)\)$/);
    if (bvarMatch) return bvarName(parseInt(bvarMatch[1]));
    if (/^[A-Z][a-zA-Z0-9_]*$/.test(argStr)) return argStr;
    return cleanName(argStr);
}

function collectTypedNames(typeStr) {
    const types = new Map();

    const binderRe = /\(\s*([^)]+)\s*\)/g;
    let m;
    while ((m = binderRe.exec(typeStr)) !== null) {
        const inner = m[1];
        const colonIdx = inner.lastIndexOf(":");
        if (colonIdx === -1) continue;
        const namesPart = inner.slice(0, colonIdx).trim();
        const ty = inner.slice(colonIdx + 1).trim();
        if (ty !== "Point" && ty !== "Line") continue;
        for (const name of namesPart.split(/\s+/)) types.set(name, ty);
    }

    for (const [pred, info] of Object.entries(GEO_PREDICATES)) {
        const re = new RegExp(`\\b${pred}\\b`, "g");
        let match;
        while ((match = re.exec(typeStr)) !== null) {
            const after = typeStr.slice(match.index + pred.length);
            const head = after.split(/\s*->\s*/)[0];
            const args = parseArgs(head);
            for (let i = 0; i < args.length && i < info.args.length; i++) {
                const arg = args[i].trim();
                const expected = info.args[i];
                if (!/^[A-Za-z][A-Za-z0-9_]*$/.test(arg)) continue;
                if (expected === "Point" || expected === "Line") {
                    if (!types.has(arg)) types.set(arg, expected);
                }
            }
        }
    }

    return types;
}

function theoremToSubstance(theorem) {
    const type = theorem.type;
    const { params, conclusion } = parsePiType(type);
    const n = params.length;

    const bvarName = (k) => {
        const idx = Math.max(0, n - 1 - k);
        if (idx < n) return cleanName(params[idx].name);
        return `v${k}`;
    };

    const typed = collectTypedNames(type);
    const points = [...typed.entries()].filter(([, ty]) => ty === "Point").map(([name]) => name);
    const lines = [...typed.entries()].filter(([, ty]) => ty === "Line").map(([name]) => name);

    const state = {
        segments: new Map(), // key -> {name, a, b, onCircle}
        angles: new Map(),
        circles: new Map(),
        triangles: new Map(),
        rectangles: new Map(),
        quads: new Map(),
        linePoints: new Map(),
        lineAuxCounter: 1,
        auxPoints: [],
    };

    for (let i = 0; i < n; i++) scanLinePoints(params[i].type, bvarName, state);
    scanLinePoints(conclusion, bvarName, state);

    const lineDeclarations = [];
    for (const lineName of lines) {
        const pts = state.linePoints.get(lineName) || new Set();
        const known = [...pts];
        if (known.length >= 2) lineDeclarations.push({ name: lineName, p: known[0], q: known[1] });
        else if (known.length === 1) {
            const aux = `${lineName}Aux${state.lineAuxCounter++}`;
            state.auxPoints.push(aux);
            lineDeclarations.push({ name: lineName, p: known[0], q: aux });
        } else {
            const aux1 = `${lineName}Aux${state.lineAuxCounter++}`;
            const aux2 = `${lineName}Aux${state.lineAuxCounter++}`;
            state.auxPoints.push(aux1, aux2);
            lineDeclarations.push({ name: lineName, p: aux1, q: aux2 });
        }
    }

    let out = `-- Theorem: ${theorem.name}\n`;
    const constructors = [];
    const predicates = [];
    const onCircleEntries = []; // { circleName, point }

    function resolveLineArg(arg) {
        const stripped = arg.replace(/^\(|\)$/g, "").trim();
        const m = stripped.match(/^(\w+)\s+(.+)$/);
        if (!m) return argToName(arg, bvarName);
        const fn = m[1];
        const fnArgs = parseArgs(m[2]).map(a => argToName(a, bvarName));
        if (fn === "parallel_through" && fnArgs.length >= 2) {
            const [baseLine, throughPoint] = [fnArgs[0], fnArgs[1]];
            const aux = `${throughPoint}Aux${state.lineAuxCounter++}`;
            const name = `line_${baseLine}_through_${throughPoint}`;
            if (!state.auxPoints.includes(aux)) state.auxPoints.push(aux);
            if (!lineDeclarations.some(ld => ld.name === name)) {
                lineDeclarations.push({ name, p: throughPoint, q: aux });
            }
            return name;
        }
        return argToName(arg, bvarName);
    }

    function ensureCircle(o, r) {
        const key = [o, r].sort().join("-");
        if (!state.circles.has(key)) {
            const name = `c_${o}_${r}`;
            state.circles.set(key, { name, o, r });
            constructors.push(`Circle ${name} := CircleR(${o}, ${r})`);
        }
        return state.circles.get(key).name;
    }

    function ensureSegment(a, b, onCircle = null) {
        const key = [a, b].sort().join("-");
        if (!state.segments.has(key)) {
            const name = `${a}${b}`;
            state.segments.set(key, { name, a, b, onCircle });
        } else if (onCircle && !state.segments.get(key).onCircle) {
            // Upgrade existing plain segment to chord.
            state.segments.get(key).onCircle = onCircle;
        }
        return state.segments.get(key).name;
    }

    function ensureAngle(a, b, c) {
        const key = [a, b, c].join("-");
        if (!state.angles.has(key)) {
            const name = `ang_${a}_${b}_${c}`;
            state.angles.set(key, { name, a, b, c });
            constructors.push(`Angle ${name} := InteriorAngle(${a}, ${b}, ${c})`);
        }
        return state.angles.get(key).name;
    }

    function ensureTriangle(a, b, c) {
        const key = [a, b, c].sort().join("-");
        if (!state.triangles.has(key)) {
            const name = `tri_${a}_${b}_${c}`;
            state.triangles.set(key, { name, a, b, c });
            constructors.push(`Triangle ${name} := Triangle(${a}, ${b}, ${c})`);
        }
        return state.triangles.get(key).name;
    }

    function ensureRectangle(a, b, c, d) {
        const key = [a, b, c, d].join("-");
        if (!state.rectangles.has(key)) {
            const name = `rect_${a}_${b}_${c}_${d}`;
            state.rectangles.set(key, { name, a, b, c, d });
            constructors.push(`Rectangle ${name} := Rectangle(${a}, ${b}, ${c}, ${d})`);
        }
        return state.rectangles.get(key).name;
    }

    function ensureQuad(a, b, c, d) {
        const key = [a, b, c, d].join("-");
        if (!state.quads.has(key)) {
            const name = `quad_${a}_${b}_${c}_${d}`;
            state.quads.set(key, { name, a, b, c, d });
            constructors.push(`Quadrilateral ${name} := Quadrilateral(${a}, ${b}, ${c}, ${d})`);
        }
        return state.quads.get(key).name;
    }

    function findCommonCircle(a, b, pointToCircles) {
        const ca = pointToCircles.get(a);
        const cb = pointToCircles.get(b);
        if (!ca || !cb) return null;
        for (const c of ca) if (cb.has(c)) return c;
        return null;
    }

    function processPredicate(pred, argsStr) {
        if (!GEO_PREDICATES[pred]) return null;

        const args = parseArgs(argsStr);
        if (args.length === 0) return null;

        const names = args.map((a, idx) => {
            const info = GEO_PREDICATES[pred];
            if (info && info.args[idx] === "Line") return resolveLineArg(a);
            return argToName(a, bvarName);
        });

        switch (pred) {
            case "on_line": {
                const [p, l] = names;
                const arg = args[1].replace(/^\(|\)$/g, "").trim();
                const isParallel = arg.match(/^parallel_through\s+/);
                const result = { type: "On", args: [p, l] };
                if (isParallel) {
                    const baseLine = argToName(arg.split(/\s+/)[1], bvarName);
                    return [result, { type: "Parallel", args: [baseLine, l] }];
                }
                return result;
            }
            case "between": {
                const [a, b, c] = names;
                return { type: "On", args: [b, ensureSegment(a, c)] };
            }
            case "collinear": {
                const [a, b, c] = names;
                // Prefer representing collinearity as a point lying on an existing or newly-created segment.
                const pairs = [[a, b, c], [a, c, b], [b, c, a]];
                for (const [p1, p2, p3] of pairs) {
                    const key = [p1, p2].sort().join("-");
                    if (state.segments.has(key)) {
                        return { type: "On", args: [p3, state.segments.get(key).name] };
                    }
                }
                for (const [p1, p2, p3] of pairs) {
                    const circle = findCommonCircle(p1, p2, pointToCircles);
                    if (circle) {
                        return { type: "On", args: [p3, ensureSegment(p1, p2, circle)] };
                    }
                }
                // Fallback: create a plain segment through the outer points.
                return { type: "On", args: [b, ensureSegment(a, c)] };
            }
            case "midpoint": {
                const [m, a, b] = names;
                return { type: "Midpoint", args: [ensureSegment(a, b), m] };
            }
            case "parallel": {
                const [l, m] = names;
                return { type: "Parallel", args: [l, m] };
            }
            case "triangle": {
                const [a, b, c] = names;
                return { type: "TriangleRef", args: [ensureTriangle(a, b, c)] };
            }
            case "on_circle": {
                const [p, o, r] = names;
                const circleName = ensureCircle(o, r);
                onCircleEntries.push({ circleName, point: p });
                return null;
            }
            case "isosceles": {
                const [a, b, c] = names;
                return { type: "EqualLength", args: [ensureSegment(a, b), ensureSegment(a, c)] };
            }
            case "equilateral": {
                const [a, b, c] = names;
                return [
                    { type: "EqualLength", args: [ensureSegment(a, b), ensureSegment(b, c)] },
                    { type: "EqualLength", args: [ensureSegment(b, c), ensureSegment(c, a)] },
                ];
            }
            case "rectangle": {
                const [a, b, c, d] = names;
                // Use explicit segments + EqualLength + RightMarked instead of the
                // Rectangle constructor or Parallelogram predicate, because the official
                // Rectangle style lacks minimum-side-length constraints and the
                // Parallelogram predicate does not reliably enforce equal opposite sides
                // in our tests.
                return [
                    { type: "EqualLength", args: [ensureSegment(a, b), ensureSegment(c, d)] },
                    { type: "EqualLength", args: [ensureSegment(b, c), ensureSegment(d, a)] },
                    { type: "RightMarked", args: [ensureAngle(d, a, b)] },
                ];
            }
            case "parallelogram": {
                const [a, b, c, d] = names;
                return [
                    { type: "EqualLength", args: [ensureSegment(a, b), ensureSegment(c, d)] },
                    { type: "EqualLength", args: [ensureSegment(b, c), ensureSegment(d, a)] },
                ];
            }
            case "segment_parallel": {
                const [d, e, b, c] = names;
                return { type: "Parallel", args: [ensureSegment(d, e), ensureSegment(b, c)] };
            }
            case "altitude_foot": {
                const [a, b, c, d] = names;
                return [
                    { type: "On", args: [d, ensureSegment(b, c)] },
                    { type: "RightMarked", args: [ensureAngle(a, d, b)] },
                ];
            }
            case "seg_congruent": {
                const [a, b, c, d] = names;
                return { type: "EqualLength", args: [ensureSegment(a, b), ensureSegment(c, d)] };
            }
            case "angle_congruent": {
                const [a, b, c, d, e, f] = names;
                return { type: "EqualAngle", args: [ensureAngle(a, b, c), ensureAngle(d, e, f)] };
            }
            case "right_angle": {
                const [a, b, c] = names;
                return { type: "RightMarked", args: [ensureAngle(a, b, c)] };
            }
            default:
                return null;
        }
    }

    const emittedParallelograms = new Set();
    const emittedEqualLengths = new Set();
    const emittedOns = new Set();
    const emittedParallels = new Set();

    function addResult(result) {
        if (!result) return;
        const items = Array.isArray(result) ? result : [result];
        for (const item of items) {
            if (item.type === "TriangleRef" || item.type === "RectangleRef") continue;
            if (item.type === "Parallelogram") {
                const key = item.args.join("-");
                if (emittedParallelograms.has(key)) continue;
                emittedParallelograms.add(key);
            }
            if (item.type === "EqualLength") {
                const key = item.args.slice().sort().join("-");
                if (emittedEqualLengths.has(key)) continue;
                emittedEqualLengths.add(key);
            }
            if (item.type === "On") {
                const key = item.args.join("-");
                if (emittedOns.has(key)) continue;
                emittedOns.add(key);
            }
            if (item.type === "Parallel") {
                const key = item.args.slice().sort().join("-");
                if (emittedParallels.has(key)) continue;
                emittedParallels.add(key);
            }
            predicates.push(item);
        }
    }

    // Collect all geometry predicates first so circle membership is known
    // before deciding how to express collinearity.
    const allPredicates = [];
    for (let i = 0; i < n; i++) {
        allPredicates.push(...collectPredicates(params[i].type));
    }
    allPredicates.push(...collectPredicates(conclusion));

    // First pass: register on_circle facts and build point -> circles map.
    for (const { pred, argsStr } of allPredicates) {
        if (pred !== "on_circle") continue;
        const args = parseArgs(argsStr);
        if (args.length < 3) continue;
        const [p, o, r] = args.map((a) => argToName(a, bvarName));
        const circleName = ensureCircle(o, r);
        onCircleEntries.push({ circleName, point: p });
    }

    const pointToCircles = new Map();
    for (const { circleName, point } of onCircleEntries) {
        if (!pointToCircles.has(point)) pointToCircles.set(point, new Set());
        pointToCircles.get(point).add(circleName);
    }

    // Second pass: process everything except on_circle (Chord implies on-circle).
    for (const { pred, argsStr } of allPredicates) {
        if (pred === "on_circle") continue;
        addResult(processPredicate(pred, argsStr));
    }

    // Upgrade segments to chords when both endpoints lie on the same circle.
    for (const seg of state.segments.values()) {
        if (seg.onCircle) continue;
        const circle = findCommonCircle(seg.a, seg.b, pointToCircles);
        if (circle) seg.onCircle = circle;
    }

    // Rebuild constructors with chord upgrades.
    constructors.length = 0;
    for (const circle of state.circles.values()) {
        constructors.push(`Circle ${circle.name} := CircleR(${circle.o}, ${circle.r})`);
    }
    for (const line of lineDeclarations) {
        // Use Segment instead of Line for drawn lines: the official Line style adds
        // arrowheads and, without a separation constraint, parallel Lines tend to
        // overlap. Segments render cleanly and still satisfy Linelike predicates.
        constructors.push(`Segment ${line.name} := Segment(${line.p}, ${line.q})`);
    }
    for (const seg of state.segments.values()) {
        if (seg.onCircle) {
            constructors.push(`Segment ${seg.name} := Chord(${seg.onCircle}, ${seg.a}, ${seg.b})`);
        } else {
            constructors.push(`Segment ${seg.name} := Segment(${seg.a}, ${seg.b})`);
        }
    }
    for (const angle of state.angles.values()) {
        constructors.push(`Angle ${angle.name} := InteriorAngle(${angle.a}, ${angle.b}, ${angle.c})`);
    }
    for (const tri of state.triangles.values()) {
        constructors.push(`Triangle ${tri.name} := Triangle(${tri.a}, ${tri.b}, ${tri.c})`);
    }
    for (const rect of state.rectangles.values()) {
        constructors.push(`Rectangle ${rect.name} := Rectangle(${rect.a}, ${rect.b}, ${rect.c}, ${rect.d})`);
    }
    for (const quad of state.quads.values()) {
        constructors.push(`Quadrilateral ${quad.name} := Quadrilateral(${quad.a}, ${quad.b}, ${quad.c}, ${quad.d})`);
    }

    // Emit OnCircle predicates only for points that are not already chord endpoints
    // (the Chord constructor already forces endpoints onto the circumference).
    const chordEndpoints = new Set();
    for (const seg of state.segments.values()) {
        if (seg.onCircle) {
            chordEndpoints.add(seg.a);
            chordEndpoints.add(seg.b);
        }
    }
    for (const { circleName, point } of onCircleEntries) {
        if (!chordEndpoints.has(point)) {
            predicates.push({ type: "OnCircle", args: [circleName, point] });
        }
    }

    if (points.length > 0 || state.auxPoints.length > 0) {
        out += `Point ${[...points, ...state.auxPoints].join(", ")}\n`;
    }

    if (constructors.length > 0) {
        out += "\n" + constructors.join("\n") + "\n";
    }

    if (predicates.length > 0) {
        out += "\n-- Constraints:\n";
        for (const item of predicates) {
            out += `${item.type}(${item.args.join(", ")})\n`;
        }
    }

    if (points.length > 0 || state.auxPoints.length > 0) {
        out += "\n-- Labels:\n";
        if (points.length > 0) {
            out += `AutoLabel ${points.join(", ")}\n`;
        }
        for (const aux of state.auxPoints) {
            out += `Label ${aux} " "\n`;
        }
    }

    return out;
}

function scanLinePoints(exprStr, bvarName, state) {
    const re = /\bon_line\b/g;
    let match;
    while ((match = re.exec(exprStr)) !== null) {
        const after = exprStr.slice(match.index + "on_line".length);
        const head = after.split(/\s*->\s*/)[0];
        const args = parseArgs(head);
        if (args.length >= 2) {
            const p = argToName(args[0].trim(), bvarName);
            const l = argToName(args[1].trim(), bvarName);
            if (!state.linePoints.has(l)) state.linePoints.set(l, new Set());
            state.linePoints.get(l).add(p);
        }
    }
}

main();
