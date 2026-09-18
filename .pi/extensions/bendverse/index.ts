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
import { mkdir, readFile, readdir, unlink, writeFile } from "node:fs/promises";
import { basename, join } from "node:path";
import { tmpdir } from "node:os";
import {
	capLines,
	extractDecls,
	extractGapLines,
	findLawParams,
	grepContext,
	headings,
	lawImports,
	latestLawCountMention,
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
	trivialProofNames,
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

	// ---------------------------------------------------------------- lemmas
	pi.registerTool({
		name: "bend_lemmas",
		label: "project lemma index",
		description:
			"Index the project's own `src/*.bend` declarations with signatures and line numbers, so a new proof can reuse what is already proven instead of re-deriving it. No query lists per-file counts; a query returns matching signatures (e.g. `swap`, `set`, `mask`, `parity`).",
		promptSnippet: "Search the project's own src/ lemmas and signatures (proof reuse).",
		promptGuidelines: [
			"Use bend_lemmas to find existing proven lemmas in src/ before writing a new proof; use bend_api for Base, bend_lemmas for this project.",
		],
		parameters: Type.Object({
			query: Type.Optional(Type.String({ description: "Case-insensitive text to match against names/signatures." })),
			module: Type.Optional(Type.String({ description: "Restrict to one src file, e.g. bits, settle, parity." })),
		}),
		async execute(_id, params, _signal, _onUpdate, ctx) {
			const dir = join(ctx.cwd, "src");
			const files = (await readdir(dir).catch(() => [] as string[]))
				.filter((f) => f.endsWith(".bend"))
				.filter((f) => !params.module || f.includes(params.module))
				.sort();

			const decls: Array<{ file: string; line: number; kind: string; name: string; sig: string }> = [];
			for (const f of files) {
				const text = await readFile(join(dir, f), "utf8").catch(() => "");
				decls.push(...extractDecls(f, text));
			}

			if (!params.query) {
				const byFile = new Map<string, { defs: number; laws: number; types: number }>();
				for (const d of decls) {
					const e = byFile.get(d.file) ?? { defs: 0, laws: 0, types: 0 };
					if (d.kind === "def") e.defs++;
					else if (d.kind === "law") e.laws++;
					else e.types++;
					byFile.set(d.file, e);
				}
				const rows = [...byFile.entries()]
					.sort((a, b) => a[0].localeCompare(b[0]))
					.map(([f, e]) => `${f.padEnd(16)} ${String(e.defs).padStart(3)} defs  ${String(e.laws).padStart(2)} laws  ${e.types} types`);
				return text(`# src/ declaration index\n${rows.join("\n")}\n\npass query=<text> to search signatures.`);
			}

			const q = params.query.toLowerCase();
			const hits = decls
				.filter((d) => d.name.toLowerCase().includes(q) || d.sig.toLowerCase().includes(q))
				.sort((a, b) => Number(!a.name.toLowerCase().includes(q)) - Number(!b.name.toLowerCase().includes(q)));
			if (hits.length === 0) return text(`No src/ declaration matches "${params.query}".`);
			const shown = hits.slice(0, 40);
			const blocks = shown.map((d) => `src/${d.file}:${d.line}\n${d.sig}`);
			const more = hits.length > shown.length ? `\n\n… ${hits.length - shown.length} more matches` : "";
			return text(blocks.join("\n\n") + more);
		},
	});

	// ---------------------------------------------------------------- goal
	pi.registerTool({
		name: "bend_goal",
		label: "show proof goal",
		description:
			"Print the elaborated goal and context for a named law in LAWS.bend. It generates a scratch proof ending in `?hole` (Bend's goal printer) and returns the compiler's goal output. Use this before writing or repairing a proof.",
		promptSnippet: "Print the elaborated goal/context for a named law (proof-development loop).",
		promptGuidelines: [
			"Use bend_goal to see a law's elaborated goal before proving it, and bend_spike to print sub-goals by placing ?hole inside a candidate proof.",
		],
		parameters: Type.Object({
			law: Type.String({ description: "Law name as declared in LAWS.bend, e.g. index_roundtrip." }),
		}),
		async execute(_id, params, signal, _onUpdate, ctx) {
			return withBendLock(async () => {
				const lawsText = await readFile(join(ctx.cwd, "LAWS.bend"), "utf8").catch(() => "");
				const argNames = findLawParams(lawsText, params.law);
				if (argNames === undefined) return text(`No law "${params.law}" declared in LAWS.bend.`);

				const src = [
					...new Set(["import Base", "import ./LAWS.bend as Laws", ...lawImports(lawsText)]),
					"",
					`def Laws.${params.law}(${argNames.join(", ")}):`,
					"  ?hole",
					"",
				].join("\n");
				const file = join(ctx.cwd, ".bendverse-goal.bend");
				await writeFile(file, src, "utf8");
				try {
					const r = await execBend([basename(file)], ctx.cwd, signal, 120_000);
					return text(r.out || "(bend produced no output)");
				} finally {
					await unlink(file).catch(() => undefined);
				}
			});
		},
	});

	// ---------------------------------------------------------------- spike
	pi.registerTool({
		name: "bend_spike",
		label: "run a scratch spike",
		description:
			"Typecheck/run a throwaway Bend snippet at the project root (relative imports like ./src/x.bend work), then delete it. Non-zero exit is returned as text, not an error, so `?hole` goal output is readable. Use for isolated lemma spikes and sub-goal probing.",
		promptSnippet: "Run a throwaway Bend snippet at the project root and return its output.",
		promptGuidelines: [
			"Use bend_spike for isolated proof spikes and sub-goals; it cleans up after itself so nothing is left to commit.",
		],
		parameters: Type.Object({
			code: Type.String({ description: "Full Bend source; may use ./src/... imports from the project root." }),
			tail: Type.Optional(Type.Number({ description: "Return only the last N output lines (default: all)." })),
		}),
		async execute(_id, params, signal, _onUpdate, ctx) {
			return withBendLock(async () => {
				const file = join(ctx.cwd, ".bendverse-spike.bend");
				await writeFile(file, params.code, "utf8");
				try {
					const r = await execBend([basename(file)], ctx.cwd, signal, 120_000);
					let body = r.out || "(bend produced no output)";
					if (params.tail) body = tailLines(body, params.tail).text;
					return text(`$ bend .bendverse-spike.bend — exit ${r.code}\n\n${body}`);
				} finally {
					await unlink(file).catch(() => undefined);
				}
			});
		},
	});

	// ---------------------------------------------------------------- audit
	pi.registerTool({
		name: "bend_audit",
		label: "trust-boundary audit",
		description:
			"A review view of what the project actually guarantees: gate status, proof burden (trivial vs real), PLAN claims vs the machine artifacts, and every assumption/gap/downgrade/fallback admitted anywhere in PLAN.md, consolidated in one place. Heuristic prose extraction, clearly labelled.",
		promptSnippet: "Audit the trust boundary: gate, proof burden, and all documented gaps.",
		promptGuidelines: [
			"Use bend_audit when planning verification work or deciding what is actually safe to build on; it lists the documented gaps in one place.",
		],
		parameters: Type.Object({}),
		async execute(_id, _params, signal, _onUpdate, ctx) {
			return withBendLock(async () => {
				const [gate, lawsText, proofText, planText] = await Promise.all([
					execBend(["PROOF.bend"], ctx.cwd, signal, 120_000),
					readFile(join(ctx.cwd, "LAWS.bend"), "utf8").catch(() => ""),
					readFile(join(ctx.cwd, "PROOF.bend"), "utf8").catch(() => ""),
					readFile(join(ctx.cwd, "PLAN.md"), "utf8").catch(() => ""),
				]);

				const green = gate.code === 0 && /All terms check\./.test(gate.out);
				const laws = parseLaws(lawsText);
				const proofNames = extractDecls("PROOF.bend", proofText)
					.filter((d) => d.kind === "def" && d.name.startsWith("Laws."))
					.map((d) => d.name.slice("Laws.".length));
				const proofSet = new Set(proofNames);
				const missing = laws.filter((l) => !proofSet.has(l));
				const extra = proofNames.filter((p) => !laws.includes(p));
				const trivial = trivialProofNames(proofText);

				const milestones = sectionByTitle(planText, "5. Milestones", 100000) ?? planText;
				const { open, done } = parseMilestones(milestones);
				const claimed = latestLawCountMention(planText);

				const gaps = extractGapLines(planText, 40);
				const out = [
					"# Bendverse audit — trust boundary",
					`gate:         ${green ? "green (All terms check.)" : `RED (exit ${gate.code})`}`,
					`laws:         ${laws.length} declared; completeness is gate-enforced (a missing proof gives '1 TODO found')`,
					`proof burden: ${trivial.length} trivial (refl), ${laws.length - trivial.length} by induction/rewrite`,
					`  trivial:    ${trivial.join(", ") || "(none)"}`,
					`  → confirm each trivial claim is a closed computation, not a weakened statement`,
					`plan (§5):    ${done.length} done, ${open.length} open`,
					`law counts:   PLAN last says ${claimed ?? "?"}; actual ${laws.length}${claimed === laws.length ? " ✓" : "  ← DRIFT"}`,
				];
				if (missing.length) out.push(`MISSING PROOFS: ${missing.join(", ")}`);
				if (extra.length) out.push(`ORPHAN PROOFS:  ${extra.join(", ")}`);
				out.push("", `## documented gaps / assumptions (heuristic; ${gaps.length} hits)`, "This is what is NOT guaranteed — review it.");
				for (const g of gaps) out.push(`- [${g.heading}] ${g.text}`);
				return text(out.join("\n"));
			});
		},
	});
}
