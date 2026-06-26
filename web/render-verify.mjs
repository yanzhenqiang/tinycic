import { spawnSync } from "child_process";
import path from "path";

// Render a Penrose diagram and verify it against the original CIC theorem.
// If verification fails, retry with a new random seed up to maxAttempts times.
export function renderWithRetry(thDir, theoremName, cicPath, maxAttempts = 5, cwd = process.cwd()) {
    const subPath = path.join(thDir, "geometry.substance");
    const stylePath = path.join(thDir, "geometry.style");
    const domainPath = path.join(thDir, "geometry.domain");
    const outPath = path.join(thDir, "output.svg");

    for (let attempt = 0; attempt < maxAttempts; attempt++) {
        const variation = `${theoremName}-${Date.now()}-${attempt}`;
        const render = spawnSync("node", [
            "web/penrose-render.mjs",
            subPath,
            stylePath,
            domainPath,
            outPath,
            variation,
        ], { cwd, encoding: "utf-8" });

        if (render.status !== 0) {
            continue;
        }

        if (!cicPath) {
            return { ok: true, attempt };
        }

        const verify = spawnSync("node", [
            "web/verify-penrose.mjs",
            thDir,
            cicPath,
        ], { cwd, encoding: "utf-8" });

        if (verify.status === 0) {
            return { ok: true, attempt };
        }
    }

    return { ok: false };
}
