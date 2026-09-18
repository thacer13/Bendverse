// Pure helpers for the Bendverse pi tools.
//
// No pi imports here on purpose: this module is plain TypeScript over the
// filesystem so it can be unit-tested directly (e.g. `bun run test-lib.ts`)
// without a live pi session.

import { readdir, stat } from "node:fs/promises";
import { join } from "node:path";

/** The bend installer prints an update nag on every invocation; drop it. */
export function stripBendNoise(s: string): string {
	return s.replace(/Bend's installer changed\.[^\n]*\n?/g, "").replace(/\s+$/, "");
}

/** Keep the last `n` lines, reporting whether anything was dropped. */
export function tailLines(s: string, n: number): { text: string; truncated: boolean } {
	const lines = s.split("\n");
	if (lines.length <= n) return { text: s, truncated: false };
	return { text: lines.slice(-n).join("\n"), truncated: true };
}

/** Hard cap with an explicit marker so the model never silently loses output. */
export function capLines(s: string, n: number): string {
	const lines = s.split("\n");
	if (lines.length <= n) return s;
	return `${lines.slice(0, n).join("\n")}\n… [truncated: ${n} of ${lines.length} lines]`;
}

export interface TestResults {
	pass: string[];
	fail: string[];
}

/** Parse the `PASS name` / `FAIL name (bad)` lines emitted by app tests. */
export function parseTestResults(out: string): TestResults {
	const pass: string[] = [];
	const fail: string[] = [];
	for (const raw of out.split("\n")) {
		const line = raw.trim();
		if (line.startsWith("PASS ")) pass.push(line.slice(5).trim());
		else if (line.startsWith("FAIL ")) fail.push(line.slice(5).trim());
	}
	return { pass, fail };
}

export interface Heading {
	level: number;
	title: string;
	line: number;
}

/** All markdown ATX headings up to `maxLevel`, ignoring fenced code blocks. */
export function headings(text: string, maxLevel = 4): Heading[] {
	const out: Heading[] = [];
	const lines = text.split("\n");
	let fence = false;
	for (let i = 0; i < lines.length; i++) {
		const line = lines[i];
		if (/^\s*```/.test(line)) {
			fence = !fence;
			continue;
		}
		if (fence) continue;
		const m = /^(#{1,6})\s+(.*\S)\s*$/.exec(line);
		if (m && m[1].length <= maxLevel) out.push({ level: m[1].length, title: m[2], line: i });
	}
	return out;
}

/** Compact table of contents (indented titles only). */
export function toc(text: string, maxLevel = 3): string {
	return headings(text, maxLevel)
		.map((h) => `${"  ".repeat(h.level - 1)}${h.title}`)
		.join("\n");
}

/**
 * Extract one section: from the heading whose title equals then contains then
 * starts with `needle`, through to the next heading of the same or higher level.
 */
export function sectionByTitle(text: string, needle: string, maxLines = 220): string | undefined {
	const lines = text.split("\n");
	const hs = headings(text);
	const n = needle.toLowerCase();
	let idx = hs.findIndex((h) => h.title.toLowerCase() === n);
	if (idx < 0) idx = hs.findIndex((h) => h.title.toLowerCase().includes(n));
	if (idx < 0) idx = hs.findIndex((h) => h.title.toLowerCase().startsWith(n));
	if (idx < 0) return undefined;

	const h = hs[idx];
	let end = lines.length;
	for (let j = idx + 1; j < hs.length; j++) {
		if (hs[j].level <= h.level) {
			end = hs[j].line;
			break;
		}
	}

	const body = lines.slice(h.line, end);
	while (body.length && body[body.length - 1].trim() === "") body.pop();
	const total = body.length;
	if (total > maxLines) {
		return `${body.slice(0, maxLines).join("\n")}\n… [truncated: ${maxLines} of ${total} lines]`;
	}
	return body.join("\n");
}

export interface GrepHit {
	heading: string;
	text: string;
}

/**
 * Case-insensitive grep that returns nearby windows, each labelled with the
 * nearest preceding heading. Overlapping windows are merged, then capped.
 */
export function grepContext(
	text: string,
	query: string,
	opts: { before?: number; after?: number; max?: number } = {},
): GrepHit[] {
	const { before = 2, after = 4, max = 10 } = opts;
	const lines = text.split("\n");
	const hs = headings(text);
	const q = query.toLowerCase();

	const idxs: number[] = [];
	for (let i = 0; i < lines.length; i++) {
		if (lines[i].toLowerCase().includes(q)) idxs.push(i);
	}

	const windows: Array<[number, number]> = [];
	for (const i of idxs) {
		const lo = Math.max(0, i - before);
		const hi = Math.min(lines.length - 1, i + after);
		const last = windows[windows.length - 1];
		if (last && lo <= last[1] + 1) last[1] = Math.max(last[1], hi);
		else windows.push([lo, hi]);
	}

	return windows.slice(0, max).map(([lo, hi]) => {
		let heading = "(top)";
		for (const h of hs) {
			if (h.line <= lo) heading = h.title;
			else break;
		}
		return { heading, text: lines.slice(lo, hi + 1).join("\n") };
	});
}

/** Open/closed markdown task-list items, e.g. PLAN.md §5 milestones. */
export function parseMilestones(planText: string): { open: string[]; done: string[] } {
	const open: string[] = [];
	const done: string[] = [];
	for (const raw of planText.split("\n")) {
		const m = /^\s*- \[( |x|X)\] (.+)$/.exec(raw);
		if (!m) continue;
		const label = m[2].replace(/\*\*/g, "").replace(/\s+/g, " ").trim();
		if (m[1] === " ") open.push(label);
		else done.push(label);
	}
	return { open, done };
}

/** Compact outline of `1. Title` style docs that have no markdown headings. */
export function numberedOutline(text: string): string {
	return text
		.split("\n")
		.filter((l) => /^\d+\.\s/.test(l))
		.map((l) => l.replace(/\s+/g, " ").trim())
		.join("\n");
}

/** `law` names declared in LAWS.bend, in order. */
export function parseLaws(lawsText: string): string[] {
	const out: string[] = [];
	for (const raw of lawsText.split("\n")) {
		const m = /^law\s+([A-Za-z0-9_.]+)\s*:/.exec(raw);
		if (m) out.push(m[1]);
	}
	return out;
}

/** Appendix A headings (`A.1 …`), in order. */
export function parseAppendix(planText: string): Heading[] {
	return headings(planText).filter((h) => /^A\.\d+/.test(h.title));
}

/** Group `bend base` output into `Module(count)` so the catalogue stays cheap. */
export function parseBaseSymbols(baseAllText: string): string {
	const groups = new Map<string, number>();
	for (const raw of baseAllText.split("\n")) {
		const m = /^(?:def|type|data|law)\s+([A-Za-z0-9_.]+)/.exec(raw);
		if (!m) continue;
		const top = m[1].split(".")[0];
		groups.set(top, (groups.get(top) ?? 0) + 1);
	}
	return [...groups.entries()]
		.sort((a, b) => a[0].localeCompare(b[0]))
		.map(([k, v]) => `${k}(${v})`)
		.join("  ");
}

/**
 * Reduce full `bend base <Name>` output to declarations only. Multi-line
 * signatures are kept whole (up to the line ending in `:`); bodies are dropped.
 */
export function signatureLines(baseNameText: string): string {
	const lines = baseNameText.split("\n");
	const out: string[] = [];
	let i = 0;
	while (i < lines.length) {
		const line = lines[i];
		if (/^(def|type|data|law)\s/.test(line)) {
			out.push(line);
			let j = i;
			// Continue through multi-line signatures until the `:` terminator,
			// stopping early at a blank line or the next top-level declaration.
			while (
				!/:\s*$/.test(lines[j]) &&
				j + 1 < lines.length &&
				lines[j + 1].trim() !== "" &&
				!/^(?:def|type|data|law|#)\s*/.test(lines[j + 1])
			) {
				j++;
				out.push(lines[j]);
			}
			i = j + 1;
		} else if (/^#/.test(line)) {
			out.push(line);
			i++;
		} else {
			i++;
		}
	}
	return out.join("\n");
}

/** Newest mtime (ms) among `exts` files under `dir`, recursively. */
export async function newestMtime(dir: string, exts = [".bend"]): Promise<number> {
	let newest = 0;
	async function walk(d: string): Promise<void> {
		let entries: Awaited<ReturnType<typeof readdir>>;
		try {
			entries = await readdir(d, { withFileTypes: true });
		} catch {
			return;
		}
		for (const e of entries) {
			const p = join(d, e.name);
			if (e.isDirectory()) {
				if (e.name !== "node_modules" && !e.name.startsWith(".")) await walk(p);
			} else if (exts.some((x) => e.name.endsWith(x))) {
				try {
					const s = await stat(p);
					if (s.mtimeMs > newest) newest = s.mtimeMs;
				} catch {
					/* ignore */
				}
			}
		}
	}
	await walk(dir);
	return newest;
}
