# AGENTS.md — Bendverse working agreement

**What this is.** Bendverse is a formally-verified reference engine for scalable
falling-sand-style cellular simulation. It is not a demo: the ASCII and windowed
runners exist only to keep the model visible. The properties that make scaling
sound — determinism, conservation, settling — are stated in `LAWS.bend` and
machine-checked by `PROOF.bend`.

## Document hierarchy (read in this order)

- `coreidea.md` — **concept authority**. The immutable model: 11 rules, plus the
  ambition note.
- `PLAN.md` — **normative plan (v2)**. Design, verification architecture,
  traceability, state, the gap registry, file layout, guardrails, risks. Update
  §5 when work lands; the gap registry (§5.3) is machine-read by `bend_audit`.
- `LAWS.bend` — **the claims**. Strictly append-only: never change an existing
  law's meaning; a correction is a new law.
- `PROOF.bend` — **a proof of every law**. This is the gate; it must stay green.
- `HISTORY.md` — **milestone log** (old PLAN Appendix A). Entry bodies are
  immutable: to correct or supersede one, append a new entry *and* add a one-line
  `> **Superseded by A.n**` pointer at the top of the old entry (annotation is
  fine; editing the claim is not).
- `AGENTS.md` — **workflow authority** (this file): how to work here.

## Code layout (intent, not just paths)

- `src/` — the **pure engine**, zero IO. The rule system lives here: `cell`
  (word layout + material table), `grid` (index math), `worldgen` (pure
  coordinate-indexed gen), `rules` (fall + impact), `support` (support/crumble),
  `ops` (shared world ops), `sim` (tick pipeline), `chunk`/`store` (M8 chunk
  key/gen + radix store), `bits`/`nat`/`potential` (verified lemma + evaluation
  kernels), `settle`/`parity`/`mod`/`priority`/`order` (V1–V3 verification
  layers), `fall` (the movement/fall-gap Φ telescope).
- `runners/` — **thin front-ends**, visibility only, not part of the engine:
  `ascii.bend` (headless cross-section scenario), `window.bend` (`App.run` UI, M6).
- `test/` — **verification witnesses**, not front-end: `tests.bend` (fast,
  tick-free golden tests), `simtests.bend` (simulation tests, native-recommended).
- `scenarios/` — **setup fixtures** shared by runners and tests (`fixtures.bend`:
  `spawn`, `pull`), so `src/sim.bend` stays only the tick pipeline.
- `main.bend` — delegates to the current runner.
- `PROOF.bend` / `LAWS.bend` — verification, never runtime.

## Workflow

- Learn Bend with `bend guide`; look up Base APIs with `bend base <Name>`. Don't
  guess the API. Search the project's own lemmas with `bend_lemmas` before
  re-deriving one.
- Before every commit: `bend PROOF.bend` must print `All terms check.`
- Tests: fast JS suite `bend test/tests.bend`; simulation suite
  `bend test/simtests.bend -o bin && ./bin` (native-recommended — JS ticks are slow).
- Implement what `PLAN.md` specifies; land it only when the gate is green and
  both suites pass; then move the item from §5.2 to §5.1 and append a
  `HISTORY.md` entry (newest last). Leave the repo runnable after every step.
- If a proof stalls, follow the downgrade protocol: record the unproven claim as
  a new gap in `PLAN.md` §5.3 (with what it gates and what would close it) —
  never leave the gate red, never delete a law, never weaken a statement silently.
- Parallelize the code whenever the work is balanced.
- **Commit autonomy (granted):** the human has given standing permission to
  commit autonomously at each step without asking first. Still run the gate
  before every commit, keep each commit scoped with a message in repo style, and
  never commit build artifacts (`bin`, `.bendverse-*.bend`) or secrets.
- Tooling: the project-local pi extension (`.pi/extensions/bendverse/`) exposes
  `bend_gate`, `bend_test`, `bend_run`, `bend_api`, `bend_lemmas`, `bend_goal`,
  `bend_spike`, `bend_plan`, `bend_status`, `bend_audit`. Prefer them over
  shelling out to `bend`/`grep`; they return compact, parsed results.
