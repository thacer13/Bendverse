# AGENTS.md — Bendverse working agreement

**What this is.** Bendverse is a formally-verified reference engine for scalable
falling-sand-style cellular simulation. It is not a demo: the ASCII and windowed
runners exist only to keep the model visible. The properties that make scaling
sound — determinism, conservation, settling — are stated in `LAWS.bend` and
machine-checked by `PROOF.bend`.

## Document hierarchy (read in this order)

- `coreidea.md` — **the contract and the rules**. Normative, not scripture:
  the three-sentence contract (purity of phases, closure, cost) plus 11 rules,
  of which rules 3/4/9/10 are *corollaries* of purity. Editable when a rule is
  wrong, impossible as written, or being read in the wrong direction — but every
  edit must be logged in `HISTORY.md` and reflected in the conformance table.
- `PLAN.md` — **normative plan (v2)**. Design, verification architecture,
  traceability, state, the gap registry, file layout, guardrails, risks. Update
  §5 when work lands; the gap registry (§5.3) is machine-read by `bend_audit`.
  §2.0 restates the contract and **§4.1 is the conformance table** — per rule and
  per contract clause, whether the engine conforms, deviates, or holds by
  construction. A deviation is recorded there, never closed by rewording the
  rule to match the code.
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
  `ops` (shared world ops), `sim` (tick pipeline), `dirty` (the carried
  dirty-row work-set mask), `chunk`/`store` (M8 chunk
  key/gen + radix store), `bits`/`nat`/`list`/`potential` (verified lemma +
  evaluation kernels; `list` holds the `List` lemmas imported from BendHub), `settle`/`parity`/`mod`/`priority`/`order` (V1–V3 verification
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
- **Changing semantics is allowed; lying about it is not.** A rule that is wrong
  or impossible as written gets rewritten in `coreidea.md` (logged in
  `HISTORY.md`, status updated in §4.1). An engine change that orphans laws is a
  *retirement*: keep the law, mark it retired with the retiring entry, and say in
  §4.1 that it is no longer evidence. Never leave an orphaned mirror claim
  (`step_m`, `sup_m`) looking live — a mirror of a shape that no longer exists is
  worse than no mirror. Sunk cost is acceptable; inheriting a dead shape's
  assumptions into the next session is not.
- Parallelize the code whenever the work is balanced — see **Parallel tracks**
  below for the worktree/worker protocol.
- **Commit autonomy (granted):** the human has given standing permission to
  commit autonomously at each step without asking first. Still run the gate
  before every commit, keep each commit scoped with a message in repo style, and
  never commit build artifacts (`bin`, `.bendverse-*.bend`) or secrets.
- Tooling: the project-local pi extension (`.pi/extensions/bendverse/`) exposes
  `bend_gate`, `bend_test`, `bend_run`, `bend_api`, `bend_lemmas`, `bend_goal`,
  `bend_spike`, `bend_plan`, `bend_status`, `bend_audit`. Prefer them over
  shelling out to `bend`/`grep`; they return compact, parsed results.

## Parallel tracks (worktree workers)

Wall-clock, not tokens, is the scarce resource, so several independent tracks may
run at once — but **never two writers in one working tree**. The human keeps
talking to a single session; this protocol is the session's job, not the human's.

- **Topology.** One **supervisor** session owns `master`, integration, and the
  narrative files (`HISTORY.md`, `PLAN.md` §4/§5). Each independent track gets
  one **worker** in its own git worktree + branch, dispatched by the supervisor:
  `tools/parallel.sh dispatch <track> "<task>"` runs a non-interactive
  `pi -p` in the worktree, using `tools/worker-prompt.md` as the worker role and
  writing output to `../Bendverse-<track>.log`. Dispatch two in parallel by
  backgrounding them in one `bash` call (`… & … & wait`).
- **Dispatch backend.** Inside Herdr (`HERDR_ENV=1`) each worker runs as an
  interactive `pi` in its own pane — watchable, with Herdr's
  `idle`/`working`/`blocked`/`done` states — and the pane output is captured to
  the log; outside Herdr it is a headless `pi -p`. The worktree/branch protocol
  is identical either way. The default split is `right`, so set
  `BENDVERSE_SPLIT=down` for the second concurrent worker; `BENDVERSE_KEEP_PANES=1`
  leaves finished panes open. Workers also write their own report to
  `../Bendverse-<track>.report.md`.
- **The human adds nothing to their prompt layer.** Ask for the tracks in plain
  language; the supervisor creates the worktrees, dispatches the workers, then
  merges, rebases, gates, and updates `PLAN.md`/`HISTORY.md` itself.
- **Single writer to `master`.** Workers commit only to their branch and never
  merge/rebase/push. The supervisor lands one branch at a time, re-runs the gate
  after each merge, and rebases the rest. (Two branches here share only the
  append-only `LAWS.bend`/`PROOF.bend`/`test/tests.bend`, so merges stay trivial
  with the reservation rule below.)
- **ID reservation.** New law/def names are prefixed with the track id
  (`v3c_`, `g5_`, …); new test numbers come from a block the supervisor assigns
  (`T40+` on the current frontier); `HISTORY.md` A-numbers are the supervisor's
  to assign. Workers must not edit `HISTORY.md` or the narrative PLAN sections.
- **CPU budget.** The box has 6 cores and `bend` uses all of them. Workers run
  the gate and the fast suite; only the supervisor runs the native simulation
  suite, once, at integration. Cap concurrent tracks at ~3.
- **Lifecycle.** `tools/parallel.sh new|rm|list`; remove a worktree once its
  branch is merged. `tools/parallel.sh reap [<track>...]` closes leaked worker
  panes (no args: idle workers whose worktree is gone); a dispatch killed
  mid-wait closes its own pane via an EXIT/INT/TERM trap, so the supervisor
  should also run `reap` after a stint that was interrupted. The per-cwd scratch
  files and the per-basename native cache are isolated by construction when
  worktrees are named distinctly (the script uses `../Bendverse-<track>`).
