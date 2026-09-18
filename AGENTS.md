# AGENTS.md — Bendverse working agreement

**What this is.** Bendverse is a formally-verified reference engine for scalable
falling-sand-style cellular simulation. It is not a demo: the ASCII and windowed
runners exist only to keep the model visible. The properties that make scaling
sound — determinism, conservation, settling — are stated in `LAWS.bend` and
machine-checked by `PROOF.bend`.

## Document hierarchy (read in this order)

- `coreidea.md` — **concept authority**. The immutable model: 11 rules, plus the
  ambition note. Human-owned.
- `PLAN.md` — **single source of truth**. Normative design, verification
  protocol, file layout, milestones, Bend guardrails, risks. Human-owned through
  §7; Appendix A is the AI-only log, appended to and never rewritten in place.
- `LAWS.bend` — **the claims**. Human-owned and append-only: never change an
  existing law's meaning; append new laws per milestone.
- `PROOF.bend` — **a proof of every law**. This is the gate; it must stay green.
- `AGENTS.md` — **workflow authority** (this file): how to work here.

## Code layout (intent, not just paths)

- `src/` — the **pure engine**, zero IO. The rule system lives here: `cell`
  (word layout + material table), `grid` (index math), `worldgen` (pure
  coordinate-indexed gen), `rules` (fall + impact), `support` (support/crumble),
  `ops` (shared world ops), `sim` (tick pipeline), `bits`/`nat`/`potential`
  (verified lemma + evaluation kernels).
- `app/` — **thin runners and tests**, not part of the engine: `ascii.bend`
  (headless cross-section scenario), `window.bend` (`App.run` UI, M6),
  `tests.bend` (fast, tick-free golden tests), `simtests.bend` (simulation tests,
  native-recommended).
- `main.bend` — delegates to the current runner.
- `PROOF.bend` / `LAWS.bend` — verification, never runtime.

## Workflow

- Learn Bend with `bend guide`; look up Base APIs with `bend base <Name>`. Don't
  guess the API.
- Before every commit: `bend PROOF.bend` must print `All terms check.`
- Tests: fast JS suite `bend app/tests.bend`; simulation suite
  `bend app/simtests.bend -o bin && ./bin` (native-recommended — JS ticks are slow).
- Milestones: implement what `PLAN.md` specifies, check boxes off as they land,
  and leave the repo runnable with the gate green after every step.
- Parallelize the code whenever the work is balanced.
- **Commit autonomy (granted):** the human has given standing permission to
  commit autonomously at each step without asking first. Still run the gate
  before every commit, keep each commit scoped with a message in repo style, and
  never commit build artifacts (`bin`) or secrets.
- Never rewrite human-owned text in place. Record status, results, and
  observations in `PLAN.md` Appendix A; if an appendix entry conflicts with the
  text above it, the appendix wins until the human folds it back in.
