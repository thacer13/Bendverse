/**
 * Bendverse tooling for pi.
 *
 * Six small tools that wrap the workflow in AGENTS.md so the model spends
 * tokens on reasoning, not on boilerplate command output:
 *
 *   bend_gate    run `bend PROOF.bend` (the mandatory pre-commit gate)
 *   bend_test    fast (JS) / sim (native) suites, pass-fail summary only
 *   bend_run     run any .bend file (scenarios, repros), output tail
 *   bend_api     `bend base` / `bend guide` lookup, compact by default
 *   bend_plan    search PLAN.md / LAWS.bend / coreidea.md by section/query
 *   bend_status  one-screen project digest (git, milestones, laws)
 *
 * All bend invocations are serialized: each one saturates the CPU cores, so
 * running them concurrently would only thrash.
 */

import type { ExtensionAPI } from "@earendil-works/pi-coding-agent";
import { StringEnum } from "@earendil-works/pi-ai";
import { Type } from "typebox";
import { mkdir, readFile } from "node:fs/promises";
import { basename, join } from "node:path";
import { tmpdir } from "node:os";
import {
	capLines,
	grepContext,
	headings,
	newestMtime,
	numberedOutline,
	parseAppendix,
	parseBaseSymbols,
	parseLaws,
	parseMilestones,
	parseTestResults,
	sectionByTitle,
	signatureLines,
	stripBendNoise,
	tailLines,
	toc,
} from "./lib.ts";

const DEFAULT_TIMEOUT = 240_000;

// Serialize bend invocations (they use all cores; parallel runs only thrash).
let bendQueue: Promise<unknown> = Promise.resolve();
function withBendLock<T>(fn: () => Promise<T>): Promise<T> {
	const run = bendQueue.then(fn, fn);
	bendQueue = run.then(
		() => undefined,
		() => undefined,
	);
	return run;
}

interface ExecResult {
	code: number;
	out: string;
	killed?: boolean;
}

function clean(parts: Array<string | undefined | null>): string {
	return stripBendNoise(parts.filter(Boolean).join("\n"));
}

function text(text2: string, details: Record<string, unknown> = {}) {
	return { content: [{ type: "text" as const, text: text2 }], details };
}

/** Deterministic per-project scratch path for compiled binaries. */
function scratchBin(cwd: string, name: string): string {
	const tag = basename(cwd).replace(/[^A-Za-z0-9_.-]/g, "_");
	return join(tmpdir(), "bendverse", `${tag}-${name}`);
}

export default function bendverse(pi: ExtensionAPI) {
	async function execBend(
		args: string[],
		cwd: string,
		signal: AbortSignal | undefined,
		timeout = DEFAULT_TIMEOUT,
	): Promise<ExecResult> {
		const r = await pi.exec("bend", args, { cwd, signal, timeout });
		return { code: r.code ?? 0, out: clean([r.stdout, r.stderr]), killed: r.killed };
	}

	async function execBin(
		file: string,
		cwd: string,
		signal: AbortSignal | undefined,
		timeout = DEFAULT_TIMEOUT,
	): Promise<ExecResult> {
		const r = await pi.exec(file, [], { cwd, signal, timeout });
		return { code: r.code ?? 0, out: clean([r.stdout, r.stderr]), killed: r.killed };
	}

	// ---------------------------------------------------------------- gate
	pi.registerTool({
		name: "bend_gate",
		label: "bend gate (PROOF.bend)",
		description:
			"Run the mandatory verification gate `bend PROOF.bend`. Returns one line when green, or the compiler error when red. Required before every commit.",
		promptSnippet: "Run the mandatory `bend PROOF.bend` gate (one-line result).",
		promptGuidelines: [
			"Use bend_gate before every commit; the commit is only allowed when it reports green (All terms check.).",
		],
		parameters: Type.Object({}),
		async execute(_id, _params, signal, _onUpdate, ctx) {
			return withBendLock(async () => {
				const t0 = Date.now();
				const r = await execBend(["PROOF.bend"], ctx.cwd, signal, 120_000);
				const secs = ((Date.now() - t0) / 1000).toFixed(1);
				if (r.code === 0 && /All terms check\./.test(r.out)) {
					return text(`✅ gate green — All terms check. (${secs}s)`);
				}
				throw new Error(`gate RED (exit ${r.code}) after ${secs}s\n\n${r.out}`);
			});
		},
	});

	// ---------------------------------------------------------------- tests
	pi.registerTool({
		name: "bend_test",
		label: "bend tests",
		description:
			"Run the Bendverse test suites and report only a pass/fail summary (plus FAIL lines). suite=fast runs `bend app/tests.bend` (JS, tick-free); suite=sim compiles and runs `app/simtests.bend` natively, reusing a cached binary when sources are unchanged.",
		promptSnippet: "Run fast or sim Bendverse tests; returns a compact pass/fail summary.",
		promptGuidelines: [
			"Use bend_test (suite=fast, then suite=sim when behavior changed) instead of shelling out to bend for tests; it returns only the failures.",
		],
		parameters: Type.Object({
			suite: StringEnum(["fast", "sim"] as const, {
				description: "fast = app/tests.bend (JS); sim = app/simtests.bend (native, cached)",
			}),
			rebuild: Type.Optional(Type.Boolean({ description: "Force a native rebuild for suite=sim." })),
		}),
		async execute(_id, params, signal, _onUpdate, ctx) {
			return withBendLock(async () => {
				const t0 = Date.now();
				const suite = params.suite ?? "fast";

				let r: ExecResult;
				let rebuilt = false;
				if (suite === "fast") {
					r = await execBend(["app/tests.bend"], ctx.cwd, signal);
				} else {
					const bin = scratchBin(ctx.cwd, "simtests");
					const srcNewest = Math.max(
						await newestMtime(join(ctx.cwd, "src")),
						await newestMtime(join(ctx.cwd, "app")),
					);
					let binMtime = 0;
					try {
						const { stat } = await import("node:fs/promises");
						binMtime = (await stat(bin)).mtimeMs;
					} catch {
						/* not built yet */
					}

					const needBuild = params.rebuild === true || binMtime === 0 || binMtime < srcNewest;
					if (needBuild) {
						await mkdir(join(bin, ".."), { recursive: true });
						const build = await execBend(["app/simtests.bend", "-o", bin], ctx.cwd, signal);
						if (build.code !== 0) {
							throw new Error(`simtests failed to compile (exit ${build.code})\n\n${build.out}`);
						}
						rebuilt = true;
					}
					r = await execBin(bin, ctx.cwd, signal);
				}

				const secs = ((Date.now() - t0) / 1000).toFixed(1);
				const tag = suite === "sim" ? (rebuilt ? "rebuilt" : "cached binary") : "fast";
				const { pass, fail } = parseTestResults(r.out);

				if (r.code === 0 && fail.length === 0 && pass.length > 0) {
					return text(`✅ ${suite}: ${pass.length}/${pass.length} pass (${tag}, ${secs}s)`);
				}
				if (pass.length === 0 && fail.length === 0) {
					throw new Error(`${suite} produced no results (exit ${r.code}, ${secs}s)\n\n${r.out}`);
				}
				const lines = [
					`❌ ${suite}: ${pass.length}/${pass.length + fail.length} pass (${tag}, ${secs}s)`,
					...fail.map((f) => `FAIL ${f}`),
					"",
					capLines(r.out, 60),
				];
				throw new Error(lines.join("\n"));
			});
		},
	});

	// ---------------------------------------------------------------- run
	pi.registerTool({
		name: "bend_run",
		label: "run a .bend file",
		description:
			"Run an arbitrary Bend file (e.g. app/ascii.bend for a scenario, or a scratch repro). Returns only the last `tail` lines of output. native=true compiles first (recommended for tick-heavy runners; JS ticks are slow).",
		promptSnippet: "Run any .bend file and return the tail of its output.",
		parameters: Type.Object({
			file: Type.String({ description: "Path relative to the project root, e.g. app/ascii.bend" }),
			native: Type.Optional(Type.Boolean({ description: "Compile natively before running (faster for ticks)." })),
			tail: Type.Optional(Type.Number({ description: "How many output lines to return (default 40)." })),
			timeout: Type.Optional(Type.Number({ description: "Timeout in seconds (default 240)." })),
		}),
		async execute(_id, params, signal, _onUpdate, ctx) {
			return withBendLock(async () => {
				const t0 = Date.now();
				const timeout = (params.timeout ?? 240) * 1000;
				const file = params.file.replace(/^@/, "");
				let r: ExecResult;

				if (params.native) {
					const bin = scratchBin(ctx.cwd, `run-${basename(file).replace(/\W+/g, "_")}`);
					await mkdir(join(bin, ".."), { recursive: true });
					const build = await execBend([file, "-o", bin], ctx.cwd, signal, timeout);
					if (build.code !== 0) {
						throw new Error(`compile failed for ${file} (exit ${build.code})\n\n${capLines(build.out, 80)}`);
					}
					r = await execBin(bin, ctx.cwd, signal, timeout);
				} else {
					r = await execBend([file], ctx.cwd, signal, timeout);
				}

				const secs = ((Date.now() - t0) / 1000).toFixed(1);
				const tailN = params.tail ?? 40;
				const { text: body, truncated } = tailLines(r.out, tailN);
				const head = `$ bend ${file}${params.native ? " (native)" : ""} — exit ${r.code}, ${secs}s`;
				const note = truncated ? `\n[showing last ${tailN} lines]` : "";
				if (r.code !== 0) throw new Error(`${head}${note}\n\n${body}`);
				return text(`${head}${note}\n\n${body}`);
			});
		},
	});

	// ---------------------------------------------------------------- api
	pi.registerTool({
		name: "bend_api",
		label: "bend base / guide lookup",
		description:
			"Look up the Bend Base library or language guide without guessing. kind=base with no name lists the available modules; with a name (U32, List.set, Array…) returns declarations only unless full=true. kind=guide with no name returns the guide's table of contents; with a name greps the guide for that topic.",
		promptSnippet: "Look up Bend Base APIs or the language guide (compact by default).",
		promptGuidelines: [
			"Use bend_api to confirm Bend Base signatures before writing code; do not guess the API.",
		],
		parameters: Type.Object({
			kind: StringEnum(["base", "guide"] as const, { description: "base library or language guide" }),
			name: Type.Optional(Type.String({ description: "Symbol/module for base, or a search term for guide." })),
			full: Type.Optional(Type.Boolean({ description: "base: return full definitions, not just signatures." })),
		}),
		async execute(_id, params, signal, _onUpdate, ctx) {
			return withBendLock(async () => {
				const kind = params.kind ?? "base";
				const name = params.name?.replace(/^@/, "").trim();

				if (kind === "guide") {
					const r = await execBend(["guide"], ctx.cwd, signal);
					if (!name) return text(`# bend guide — contents\n${toc(r.out, 3)}`);
					// Prefer sections whose title matches the topic over incidental greps.
					const n = name.toLowerCase();
					const named = headings(r.out).filter((h) => h.title.toLowerCase().includes(n));
					if (named.length > 0) {
						const parts = named
							.slice(0, 4)
							.map((h) => sectionByTitle(r.out, h.title, 140))
							.filter((s): s is string => !!s);
						if (parts.length > 0) return text(parts.join("\n\n———\n\n"));
					}
					const hits = grepContext(r.out, name, { before: 3, after: 8, max: 6 });
					if (hits.length === 0) return text(`No guide section matching "${name}".`);
					return text(hits.map((h) => `## ${h.heading}\n${h.text}`).join("\n\n———\n\n"));
				}

				if (!name) {
					const r = await execBend(["base"], ctx.cwd, signal);
					return text(
						`# bend base modules (decls)\n${parseBaseSymbols(r.out)}\n\n` +
							`Pass name=<Module> or name=<Module.symbol> for signatures.`,
					);
				}

				const r = await execBend(["base", name], ctx.cwd, signal);
				if (r.code !== 0 || r.out.trim() === "") {
					return text(`No Base symbol matched "${name}". Try bend_api kind=base with no name for the catalogue.`);
				}
				if (params.full) return text(capLines(r.out, 260));
				return text(signatureLines(r.out));
			});
		},
	});

	// ---------------------------------------------------------------- plan
	pi.registerTool({
		name: "bend_plan",
		label: "search project docs",
		description:
			"Search the human-owned docs without reading them whole. file=PLAN (default), LAWS, or coreidea. With section=<title fragment> returns that section; with query=<text> returns labelled grep windows; with neither returns a table of contents.",
		promptSnippet: "Read PLAN.md/LAWS.bend/coreidea.md by section or query instead of whole-file reads.",
		promptGuidelines: [
			"Use bend_plan to look up PLAN.md sections, laws, or coreidea rules instead of reading those large files in full.",
		],
		parameters: Type.Object({
			file: StringEnum(["PLAN", "LAWS", "coreidea"] as const, { description: "which doc to search" }),
			section: Type.Optional(Type.String({ description: "Heading/title fragment to extract." })),
			query: Type.Optional(Type.String({ description: "Case-insensitive text to grep for." })),
			maxLines: Type.Optional(Type.Number({ description: "Cap for section extraction (default 220)." })),
		}),
		async execute(_id, params, _signal, _onUpdate, ctx) {
			const file = params.file ?? "PLAN";
			const rel = file === "PLAN" ? "PLAN.md" : file === "LAWS" ? "LAWS.bend" : "coreidea.md";
			const content = await readFile(join(ctx.cwd, rel), "utf8");

			if (file === "LAWS" && !params.section && !params.query) {
				const laws = parseLaws(content);
				return text(`# LAWS.bend (${laws.length} laws)\n${laws.join("\n")}`);
			}

			if (params.section) {
				if (file === "LAWS") {
					const hits = grepContext(content, params.section, { before: 0, after: 24, max: 1 });
					if (hits.length === 0) return text(`No law matching "${params.section}".`);
					return text(hits[0].text);
				}
				const s = sectionByTitle(content, params.section, params.maxLines ?? 220);
				if (!s) return text(`No section matching "${params.section}" in ${rel}.`);
				return text(s);
			}

			if (params.query) {
				const hits = grepContext(content, params.query, {
					before: file === "LAWS" ? 1 : 2,
					after: file === "LAWS" ? 8 : 6,
					max: 10,
				});
				if (hits.length === 0) return text(`No match for "${params.query}" in ${rel}.`);
				return text(hits.map((h) => `## ${h.heading}\n${h.text}`).join("\n\n———\n\n"));
			}

			if (file === "LAWS") {
				const laws = parseLaws(content);
				return text(`# LAWS.bend (${laws.length} laws)\n${laws.join("\n")}`);
			}

			if (file === "coreidea") {
				const outline = numberedOutline(content);
				return text(`# coreidea.md — rules\n${outline || "(no numbered outline; use query=)"}`);
			}

			const root = toc(content, 2);

			const milestones = sectionByTitle(content, "5. Milestones", 100000) ?? content;
			const { open } = parseMilestones(milestones);
			const openList = open.length ? open.map((m) => `  - ${m.slice(0, 130)}`).join("\n") : "  (none)";
			return text(`# PLAN.md — contents\n${root}\n\n## open milestones\n${openList}`);
		},
	});

	// ---------------------------------------------------------------- status
	pi.registerTool({
		name: "bend_status",
		label: "project status digest",
		description:
			"One-screen project digest: git HEAD/dirty state, open PLAN.md §5 milestones, law names from LAWS.bend, and the newest Appendix A entry. Cheap, read-only, no bend invocation.",
		promptSnippet: "Show a compact Bendverse status digest (git, open milestones, laws).",
		promptGuidelines: [
			"Use bend_status at the start of a work session to orient without reading PLAN.md in full.",
		],
		parameters: Type.Object({}),
		async execute(_id, _params, signal, _onUpdate, ctx) {
			const [status, log, plan, laws] = await Promise.all([
				pi.exec("git", ["status", "--porcelain=v1", "-b"], { cwd: ctx.cwd, signal }),
				pi.exec("git", ["log", "-1", "--oneline"], { cwd: ctx.cwd, signal }),
				readFile(join(ctx.cwd, "PLAN.md"), "utf8").catch(() => ""),
				readFile(join(ctx.cwd, "LAWS.bend"), "utf8").catch(() => ""),
			]);

			const statusLines = clean([status.stdout, status.stderr]).split("\n").filter(Boolean);
			const branch = (statusLines[0] ?? "## (no git)").replace(/^##\s*/, "");
			const dirty = statusLines.slice(1);
			const head = clean([log.stdout]).trim() || "(no commits)";

			const milestones = sectionByTitle(plan, "5. Milestones", 100000) ?? plan;
			const { open, done } = parseMilestones(milestones);
			const appendix = parseAppendix(plan);
			const lawNames = parseLaws(laws);

			const openList = open.length
				? open.map((m) => `  - ${m.replace(/\.$/, "").slice(0, 120)}`).join("\n")
				: "  (none)";
			const lastAppendix = appendix.length ? appendix[appendix.length - 1].title : "(none)";

			const out = [
				"# Bendverse status",
				`git:    ${branch}${dirty.length ? ` — ${dirty.length} dirty: ${dirty.slice(0, 6).join(", ")}` : " — clean"}`,
				`head:   ${head}`,
				`laws:   ${lawNames.length} [${lawNames.join(", ")}]`,
				`milestones: ${done.length} done, ${open.length} open`,
				openList,
				`last appendix: ${lastAppendix}`,
			];
			return text(out.join("\n"));
		},
	});
}
