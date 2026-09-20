# Bendverse — Plan & Specification

**What this is.** A formally-verified reference engine for scalable
falling-sand-style cellular simulation. The engine is real: a 64×64×64
`Array<U32>` world, pure worldgen, an 8-phase tick pipeline, activity-gated
cost, optional chunks. The verification is real: every claim in `LAWS.bend` is
discharged by a machine-checked proof in `PROOF.bend`, and `bend PROOF.bend` is
the gate. The ambition is `coreidea.md`'s: determinism, conservation, stability,
and scalability as properties of the design, not features layered on top.

**Document hierarchy.**

| Doc | Role | Authority |
|---|---|---|
| `coreidea.md` | the model: 11 immutable rules + the ambition | concept |
| `PLAN.md` | this file: normative design, verification architecture, state, gaps | design |
| `AGENTS.md` | how to work here: gate, tests, commits, tooling | workflow |
| `LAWS.bend` / `PROOF.bend` | the claims and their proofs | the verified substrate |
| `HISTORY.md` | AI milestone log; immutable entry bodies, corrections via a `Superseded by` pointer (old Appendix A) | historical record |

**How work happens.** Implement what this file specifies. Land it only when the
gate is green (`bend PROOF.bend` → `All terms check.`), both test suites pass,
and a `HISTORY.md` entry is appended. Details and autonomy rules in `AGENTS.md`.

**Tooling.** A project-local pi extension (`.pi/extensions/bendverse/`) provides
the loop: `bend_gate`, `bend_test`, `bend_run`, `bend_api`, `bend_lemmas`,
`bend_goal`, `bend_spike`, `bend_plan`, `bend_status`, `bend_audit`.

---

## 0. Verified platform facts (do not re-derive)

Bend 2.0.17 (upgraded from 2.0.5 in A.80). Learned the hard way; re-checking
these costs more than reading them.

**2.0.17 breaking changes and toolchain bugs (A.80).**
- **Bare operators require a type annotation.** `a + b` (also `- * / %`, and
  the `< <= > >=` family) no longer defaults to `Nat`: the checker reports
  "a type for this operator". The bundled guide still says bare operators
  belong to `Nat`; the compiler note is authoritative ("Until 2.0.16 a bare
  operator meant Nat. That was a bug"). Project convention: write the named
  form — `Nat.add`, `Nat.mul`, `Nat.sub` — in propositions and proofs, and
  reserve `(a + b : T)` for expressions that want the namespace annotation.
  `&&`, `++`, and the `U32` operators are unaffected.
- **The `a[i] <- v` / `a[i]` sugar mangles a `../`-relative index head.**
  `parse_term_ns` treats any index head starting with `.` as an
  operator-namespace reference and prepends the element type, so `Grid.index`
  reached through `import ../src/grid.bend` becomes the nonexistent
  `U32../src/grid.index` ("expected : a defined name"); a `./src/...` import is
  unaffected. Workaround (used by `test/simtests.bend`): call
  `Array.set(T, a, i, v)` explicitly instead of the sugar. Closes when the
  compiler keys this on a single leading dot.
- **Fixed since 2.0.5:** `Array.to_list` inlines correctly, and `List.sort`
  compiles and runs (2.0.5 referenced an undefined `List.sort.go`), clearing
  both A.76 toolchain blockers. Hex literals (`0x…`) are still rejected.

**Language and termination.**
- Bend is pure and affine. Copyable values need `+` (Data kind); arrays and IO
  handles are linear (one owner).
- Termination is mandatory: recurse only on a structurally smaller
  pattern-matched argument (shrinking parameter FIRST); loop counters are `Nat`
  (`case 1n+p`); no mutual recursion (use a selector argument); unbounded loops
  take `Nat` fuel or live in the `App` event loop. `@unsafe` is banned here.
- No `if`: match `True{}`/`False{}`. The match scrutinee must be a variable,
  never a computed value (route it through a helper def). No `let` before a
  `match` on a parameter. Annotate literals: `x = {3 : U32}`.
- Numbers: `U32` wraps mod 2^32 (M1 spike confirms), `F32`, `Nat`.
  Coordinates and arithmetic are `U32`; fuel and counters are `Nat`.
  XOR is `.^.`; shift amounts are `Nat`.
- Closures are affine (call once); top-level defs are freely callable; templates
  (`~f`) inline at compile time.

**Arrays.**
- `Array<T>` is linear: never dropped, never used twice on one path, rebound
  after every write (`a = a[i] <- v` unless last statement). The `a[i]` sugar
  assumes `Array<U32>` — the world is `Array<U32>`, keep it so.
- Explicit API: `Array.get` / `Array.set` / `Array.swap` / `Array.clone` /
  `Array.map`. `Array.get` returns the array back beside the element —
  destructure and rebind.
- Sizes are powers of two (`[v : T*n]` or depth `[v : T^d]`); indexes wrap (mask).

**Parallelism and IO.**
- `a b = f(x) g(y)` is a parallel call: the branches must be independent and of
  similar duration. `f!(x)` sends the subtree to the GPU; this machine has no
  CUDA, so `!` falls back to CPU-parallel and is validated as such.
- IO is a monad (`do IO<T>:`). `App.run(~S, ~App{view, tick}, ...)` runs a
  windowed app; `tick` returning `None` quits. The App loop is the legal
  infinite loop.

**Verification mechanics.**
- `law` in `LAWS.bend` states a proposition; `def Laws.<name>(<params>)` in
  `PROOF.bend` must discharge it. An undischarged law is a TODO, so
  `bend PROOF.bend` fails with `N TODO found` if a proof is missing.
- `?name` inside a proof prints the elaborated goal and context; `?TODO` leaves
  the goal open (gate red). Use the former freely, the latter never in a commit.
- `bend f.bend` checks the file, then runs `main`. `-o out` builds. `--checkup`
  checks and runs each import alone — **unsound here**: `LAWS.bend` alone reports
  its 105 laws as TODOs. Use `bend PROOF.bend`, never `--checkup`, for the gate.
- Imports resolve relative to the importing file, not the cwd; absolute import
  paths work (`import /abs/path/x.bend as X`).
- Base APIs: `bend base <Name>`, `bend base --types`, `bend guide`. Do not guess.
- The project's own lemma libraries are large (`bits.bend` 77 decls,
  `parity.bend` 68, `settle.bend` 30). Find reuse with `bend_lemmas`, not by
  reading whole files.

---

## 1. Product

A formally-verified reference engine over a 3D falling-sand-style cellular
world: a 64×64×64 grid of cells, each one `U32` word; materials with
density/cohesion; collapse by support loss; impact by fall distance; cost
proportional to disturbance (activity bits); pure deterministic worldgen;
CPU-parallel with an optional GPU track. The ASCII and windowed front-ends are
visibility only — they keep the model observable, they are not the product.

---

## 2. Normative design

### 2.0 The contract

The normative model is `coreidea.md`'s contract, restated here because the rest
of this plan is written against it:

- **C1 — Purity of phases.** A tick is the composition of phases; each phase is
  a pure function of the state it is handed. No part of a phase reads a value
  another part of the same phase produced.
- **C2 — Closure.** The world is a closed box; rules never move material out of
  it and there is no periodic wrap. A boundary move is inert.
- **C3 — Cost tracks disturbance.** A tick's work is proportional to the
  disturbed set, not to the world.

Rules 10, 3, 4 and 9 of `coreidea.md` are *corollaries* of C1, not independent
axioms: determinism is what purity buys, single-writer and collision-free
batching are what a pure (colour × direction) schedule buys, and the settled
fixpoint is what a pure phase plus activity gating buys.

§4.1 is the conformance table: per contract clause and per rule, whether the
engine conforms, deviates, or holds by construction. A claim that deviates is
recorded there — never papered over with a hypothesis, and never "closed" by
rewording the rule to match the code.

### 2.1 World and cell word

World = one flat `Array<U32>`, 64×64×64 = 2^18 cells, built once by worldgen.
Flat index: `i = x .|. (z << 6) .|. (y << 12)`; decode `x = i & 63`,
`z = (i >> 6) & 63`, `y = i >> 12`. All `U32` (shift amounts are `Nat`).

Cell word bit layout (24-bit-safe; bits 24–31 stay 0 — never rely on them):

| bits | field | range |
|---|---|---|
| 0–4 | material id | 0–31 |
| 5–10 | cohesion | 0–63 |
| 11 | active flag | 0/1 |
| 12–16 | support level | 0–31 |
| 17–22 | fall distance (impact energy) | 0–63 |
| 23 | reserved | 0 |

**Box, not torus (C2).** `Grid.neighbor` currently wraps all three axes modulo
64, so `below` at `y = 0` is `y = 63` and Φ *increases* on that move — outside
`array_mov_lowers_phi_regime`'s `mov_S ≥ mov_T` regime. The world is closed only
because `Worldgen.gen` paints a bedrock shell on all six faces; nothing proves
the shell survives, and `runners/window.bend` can paint it away. Closing the box
**in the grid** (boundary moves inert) is `V0-2`; that the shell is generation
rather than grid is what rule 11 now says.

### 2.2 Materials (v1)

| id | material | density | static | slides | default cohesion |
|---|---|---|---|---|---|
| 0 | Empty | 0 | no | no | 0 |
| 1 | Bedrock | 255 | yes | no | 63 |
| 2 | Sand | 100 | no | yes | 0 |
| 3 | Rock | 200 | no | no | 48 |
| 4 | Rubble | 150 | no | yes | 0 |
| 5 | Water | 80 | no | yes | 0 (reserved) |

This table is pure data in `src/cell.bend` (a `match` on material id), not
per-material code paths. Static = never moves, never crumbles, is a support
source. "Lower-density-or-empty" is unified: Empty has density 0.

### 2.3 Cell encoding

`src/cell.bend`: `encode(material, cohesion, active, support, fall) -> U32` and
`decode(word) -> Cell` plus field accessors via shifts/masks. Only these
functions touch the bit layout.

### 2.4 Tick pipeline (normative order, `src/sim.bend`)

```
tick(world):
  1. support pass    — recompute support field (see 2.8)
  2. crumble pass    — cohesion := 0 on unsupported cohesive cells; Rock -> Rubble
  3. movement phases — c = 0..7 in fixed order; per phase one in-place fold over
                       all cells of color c in lexicographic scan order: x asc, z asc, y asc
  4. activity settle — every cell evaluated this tick whose word did not change: active := 0
```

Phase color: `c = (x & 1) .|. ((y & 1) << 1) .|. ((z & 1) << 2)`. Verified: any
two cells within the 26-neighborhood differ in at least one coordinate parity,
so no two same-color cells are neighbors — per-phase updates cannot conflict
through adjacency (`parity.bend`).

**Normative semantics is the sequential scan above.** Determinism (rule 10)
holds by construction: same input `Array` + same constants → same output.
Parallel/GPU work is legal only if it reproduces this exactly.

### 2.5 Tie-break (single-writer, rule 3)

Within a phase, two non-adjacent same-color movers may target the same cell
(their common neighbor). Resolution: **the mover first in the phase's
lexicographic scan order wins**; later movers see the target occupied and stay.
This is binding; any parallel implementation must reproduce it (priority = scan
order). `scan_order_total` and `neighbor_cancel` prove the order is total and
the candidate set local.

### 2.6 Universal falling rule (per evaluated cell, in its phase)

Materials differ only via the 2.2 table — the logic is shared:

```
1. Empty or static material: do nothing.
2. cohesion > 0: do not move individually (handled by support/crumble).
3. below = (x, y-1, z); y = 0 is treated as blocked (worldgen guarantees bedrock).
   If below is Empty or density(below) < density(here):
     swap(here, below); mover's fall := min(63, fall + 1); mark activity; done.
4. Else if slides:
   For (dx, dz) in fixed order (-1,0), (+1,0), (0,-1), (0,+1):
     side = (x+dx, y, z+dz); diag = (x+dx, y-1, z+dz)   [wrap is masked; borders are bedrock]
     If side and diag are both Empty-or-lower-density: swap(here, diag); fall unchanged; done.
5. Else (blocked): if fall > 0, resolve IMPACT (2.7). fall := 0. No move.
```

All moves are swaps (rule 2). No material is created or destroyed by movement.

### 2.7 Impact (rule 8)

At step 5 with `fall > 0`: `damage = fall`; target = the below cell.
- Target static (Bedrock): no damage; mover stops.
- `damage >= cohesion(target)`: target cohesion := 0; Rock → Rubble; mark
  activity on both cells + neighbors; the mover re-evaluates steps 3–4 once.
- Otherwise: mover stops (no partial wear in v1).
Then `fall := 0`. No velocities, no momentum — energy is the fall counter.

### 2.8 Support and crumble (rules 6–7) — the crumble trick

Rigid clusters are NEVER moved as units. An unsupported cohesive cell loses
cohesion (that event is "rock → rubble") and afterwards obeys the universal
falling rule individually. Everything stays local.

Support pass (step 1), scanned y ascending 0..63, active regions only,
recomputed from current neighbors every tick (never cached):

```
support(c) = 31                    if c is static
           = 31                    if any 6-neighbor is static
           = support(below)        if below is cohesive and support(below) > 0
           = 0                     otherwise
```

Crumble pass (step 2): every cohesive cell with support = 0 → cohesion := 0;
Rock → Rubble; fall := 0; mark activity (self + 26-neighbors). Loose cells need
no support (they fall).

Upgrade path (only if needed): `SUPPORT_PASSES > 1` relaxation sweeps to
propagate support through sideways cohesive chains (overhangs). v1 is the
single-pass rule above.

### 2.9 Activity (rule 9)

- Every write to any cell (movement, crumble, impact, user paint) sets active on
  that cell and all 26 neighbors, immediately.
- Phase folds evaluate a cell only if its active bit is set (v1 iterates all
  cells of the color and tests the bit; per-color active index lists are a later
  optimization).
- Settle pass (step 4) clears active on evaluated-and-unchanged cells.
  Disturbance dies out; untouched regions cost one bit-test per cell.
- Freshly generated worlds are all-inactive (rule 11). Runners wake regions on
  demand (paint/spawn marks activity).

### 2.10 Worldgen (rule 11) — pure, `src/worldgen.bend`

`gen(x, y, z, seed) -> U32`, a pure function of coordinates + seed only; build
the world by calling it per cell (`build`; `build_at` is the parallel variant).
- `SEED = 42u` (v1).
- Integer hash (all `U32`, wrapping): `h = (x * 2654435761) .^. (y * 40503)
  .^. (z * 2246822519) .^. seed`, then `h = h .^. (h >> 15)`,
  `h = h * 2246822519`, `h = h .^. (h >> 16)`.
- Value noise: hash lattice corners at period 16, top 8 bits (0–255),
  trilinear/bilinear interpolation in `F32` (purity makes it deterministic).
- Terrain height `gy(x, z) = 8 + floor(noise2(x, z) * 24)` → 8..32.
- Cell assignment: bedrock shell if any coordinate is 0 or 63; else `y > gy` →
  Empty; `y >= gy - 3` → Sand; else → Rock (cohesion 48). All start inactive,
  support 0, fall 0. The bedrock shell means movement never sees wraparound.
- Sparse feature fields (pockets, boulders) are optional additions and must stay
  pure coordinate functions.

### 2.11 Runners

- `runners/ascii.bend` (root `main.bend` delegates to it): build world, print the
  x–y cross-section at z = 32 (y top-down so up is up), run N ticks (`Nat` fuel,
  N = 20), print again. Chars: `.` Empty, `#` Bedrock, `s` Sand, `R` Rock,
  `r` Rubble.
- `runners/window.bend`: `App.run` windowed app; state = world + running flag; view
  renders the x–y cross-section at z = 32 as a 64×64 quadtree `Image`; tick
  handles left/right mouse paint (Sand/Rock) at `(mx, 63 - my, 32)`, `e` to
  erase, space to pause, close to quit. Paints set activity on 26 neighbors.
- `runners/view3d.bend` (presentation): an `App.run` windowed 3D viewer over the
  64³ world, at 1920×1080. `view/voxel.bend` is a pure (no-IO) Amanatides–Woo
  DDA voxel raycaster + perspective camera; the runner holds world + `speed` +
  render `depth` + camera + a held-key mask and renders a depth-`depth` quadtree
  `Image`. Fly the camera (W/A/S/D, Q/E or ←/→ yaw, ↑/↓ pitch, R/F rise/sink,
  mouse-drag look), space pauses, `-`/`=` set `speed` (sim ticks per rendered
  frame, 0 = paused), `,`/`.` set the render `depth` (5–8). Key codes accept
  both conventions (X11 lowercase + arrows 63232–63235, Mac/GLFW uppercase +
  262–265). The window backend maps a depth-`d` image to a w×h window by top
  bits, so `view_image` renders only the aspect-correct, integer-scaled
  sub-image the window shows (1920×1080: depth 7 → 120×68 cells at 16×, depth 8
  → 240×135 at 8×). Not part of the engine; ~50 ms/frame at depth 7, ~14 ms at
  depth 6, ~200 ms at depth 8 (native, 1920×1080).
- `runners/export.bend` (track `bridge`, P0): the binary format contract the
  renderer (`../Bendview/`) reads — a chunk-oriented snapshot (`.bvs`, all 64
  `Chunk.key` records) plus `Worldgen.gen` reference vectors (`.bvg`). IO only
  (it is a runner); the byte layout is documented at the top of the file.
  `runners/serve.bend` + `runners/SERVE.md`: the headless sidecar transport
  design (length-framed snapshots/deltas) and a skeleton.
- `src/cw.bend` (track `scale`, P3, additive): a torus-free global-coordinate
  module (global `(x,y,z)` ↔ `(chunk_key, local)`); unused by the live path.
  `SCALE.md` is the migration design. `Sim.tick_trace` (track `scale`, P1)
  returns `(world, deltas)` — the render-visible change set — leaving `tick`
  unchanged.
- `test/tests.bend`, `test/simtests.bend`: golden tests, see §3.5.
- `scenarios/fixtures.bend`: shared setup (`spawn`, `pull`), so `src/sim.bend`
  stays only the tick pipeline.

### 2.12 Purity and the determinism contract

Given the same initial `Array<U32>` and constants, every run (JS, native,
threaded, GPU) produces identical results. Witnessed by T1. This is the
acceptance bar for any parallel or GPU work.

Read through §2.0 this is not an extra requirement: a tick is a composition of
pure phases (C1), so any evaluation order at any granularity computes the same
function. Determinism is a *consequence* of the contract, and a parallel
implementation is correct when it is a different schedule of the same pure
phase — not when it reproduces the sequential scan's order effects. Until C1
holds in the engine, determinism holds only because the scan is sequential, and
that is recorded as a deviation (§4.1) rather than treated as proven.

---

## 3. Verification architecture

### 3.1 The gate

`bend PROOF.bend` must print `All terms check.` before every commit. It checks
`LAWS.bend` (the claims), `PROOF.bend` (the proofs), and every imported `src`
module against the current definitions. An undischarged law is a TODO, so a
missing proof makes the gate red. Changing `src/` can break proofs — that is the
point, not an accident.

Tests are separate and complementary: `bend test/tests.bend` (JS, tick-free) and
native `bend test/simtests.bend -o bin && ./bin`.

### 3.2 What the gate proves — and what it cannot

The gate proves: *the stated proposition is a theorem of the definitions it
names, in Bend's kernel.* It cannot prove:

1. **Intent.** A weakened statement is still a theorem. (A law that says less
   than intended passes.)
2. **Refinement.** That the definitions mirror the imperative implementation.
   Laws about `Word`, `List`, `Nat`, and `Array`-models are not, by themselves,
   laws about the running `Array<U32>` engine. This is the refinement gap.
3. **Runtime.** That golden tests pass. They are witnesses, not proofs.

Items under (1)–(3) that are not yet closed live in the trust boundary (§5.3),
with an ID. That registry — not prose — is the canonical record.

### 3.3 Claims, proofs, and trivial proofs

105 laws, every one discharged. Six are reflexivity proofs (`{==}`, both sides
definitionally equal):

`sanity`, `grid_volume`, `cell_full_mask`, `cell_reserved_bits`,
`rock_crumbles_lighter`, `sand_sinks_in_water`.

A reflexivity proof is legitimate when the statement is a closed computation.
It is also exactly what a *weakened* statement would admit, so these six are
review items in §5.3 until a human confirms each says what it should.

### 3.4 Downgrade protocol

If a proof stalls: never leave the gate red, never silently delete a law, never
quietly weaken a statement. Record the unproven claim in §5.3 with a new ID
(what is unproven, what it gates, what would close it), keep or downgrade the
property to a golden test, and proceed. `bend_audit` reads the registry, so the
record is mechanical, not narrative.

**Retirement, not deletion (added A.61).** A semantics change cannot edit a law,
and cannot delete one either, so a rewritten engine orphans the laws stated about
the old shape. The rule is *retirement*: keep the law, mark it retired by the
entry that retires it, and keep it only while its subject module exists. A
retired law is still true; it is no longer evidence. §4.1 records the retirement
so a later session cannot mistake an orphaned claim for a live one. This exists
specifically so that a rewrite does not silently inherit the old shape's
assumptions — the failure mode the append-only discipline otherwise creates.

### 3.5 Golden tests (runtime witnesses)

Fast, tick-free (`test/tests.bend`): T5 index/cell roundtrips; bit-31 and
mul-wrap spikes; T6 gen determinism; T7 terrain structure; T8 build = gen over
all cells; T10 parity/neighbor-x; T11 low6 add + ∓1 cancel; T12 dir φ
cancellation; T13 neighbor index cancellation; T14 scan-order totality; T15
`List.set` split + sum; T16 chunk key/local roundtrip + gen; T17 chunk store
set/get/overwrite; T18 store assemble = worldgen; T19 write→Φ bridge (support/active writes preserve pot, rock crumble lowers it, non-rock crush is the identity — `G9`); T20 chunk sleeping/eviction (empty store regenerates worldgen, all-gen store evicts to worldgen, one-resident eviction preserves the world, predicates); T21 conservation witness (non-empty indicator preserved by every material-preserving write; rock crush 3→4); T22 movement Φ witness (the `Rules.step` movement drops Φ by `(dens(w) − dens(gv))·(iy(i) − iy(j))` for empty and lighter targets, and `mov` preserves pot at the target); T29 `Rules.Dir4` == the `U32` direction table; T30 the direction-parity classification; T31 point writes at `Commit.ne_idx`-distinct leaves commute, and `ne_idx` is sharp (V3c-1).

Simulation, native-recommended (`test/simtests.bend`): T1 tick determinism over
10 ticks; T2 conservation of the non-Empty count; T3 Bedrock static; T4 activity
settles and far cells are untouched; T4b a settled world is a fixed point; T9
pull-base collapses rock; T18 chunk-store tick equivalence; T20 evict → assemble
→ tick equivalence; T23 phase contention is resolved from the pre-phase state;
T24 wake does not propagate within a phase; T26 a grain in an empty column
settles (the V0-1 conformance witnesses, A.63); T27 the floor painted away does
not wrap at y=0; T28 the west wall painted away does not wrap at x=0 (the V0-2
closure witnesses, A.64).

### 3.6 Proof-development loop

- `bend_goal <law>` — elaborated goal + context for a named law (`?hole`).
- `bend_spike <src>` — typecheck a throwaway snippet at the repo root; `?hole`
  output is returned verbatim (non-zero exit is not an error here).
- `bend_lemmas [query]` — signature index of `src/*.bend`. Search before
  re-deriving; `bits.bend` and `parity.bend` already prove most bit facts.

### 3.7 Normalization discipline (expansions and canaries)

`{==}` discharges *definitional* equality, so what the checker normalizes is part
of the trust boundary, not just a performance knob. Two failure directions:

- **missing / stuck normalization** — a proof that should check hangs or fails
  (A.41, A.42); or, subtler, passes because both sides are stuck in the same
  shape rather than genuinely reduced;
- **over-eager normalization** — a proof that must not check does (soundness).

Working discipline:

- **Canaries.** `tools/checker-canary.sh` (also `bend_canary`) runs positive refl
  proofs that must still check (catch missing normalization) and negative
  controls that must still be rejected (catch over-eager acceptance). Run it after
  touching proofs or the toolchain; when an interaction surprises us, first add a
  canary that captures the expected behaviour, then investigate.
- **Observe, don't guess.** Put `?h` in a candidate proof to have `bend_spike`
  print the elaborated goal — that is how you see what the checker actually has.
  If a compile is slow, bisect the touched file with `head -n` and time each
  prefix; never let the full gate run on a known cliff.
- **Known expansion triggers** (PLAN §7): a concrete-fuel loop application inside
  a proposition (A.41); a reducible term nested inside a proposition, e.g. a
  `set_support` write under `pack`→`to_pots` (A.42); an opaque `U32` selector
  (mirror it with a datatype); a timeout that does not kill the process group
  (A.43).
- **Classify and record.** Every surprise is one of *proof-engineering*,
  *checker performance*, or *checker soundness*. Record it in `HISTORY.md`, and
  in §5.3 when it is a trust boundary.

---

## 4. Traceability: coreidea rules ↔ evidence

`Laws` lists the claims that bear on the rule; `Tests` the runtime witnesses;
`Modules` where it lives. `—` means no law — that is an assurance boundary, not
an oversight to hide.

| Rule | Constraint | Laws | Tests | Modules |
|---|---|---|---|---|
| `R1` | Locality: pre-phase reads only, bounded radius | `dir_phi_cancel` `neighbor_cancel` `low6_add_independent` `parity_flip_succ` `parity_flip_pred` | T11 T12 T13 T14 | parity mod priority order |
| `R2` | Conservation: swap/transform only | `array_point_write_preserves_count` `array_point_write_count_balance` `array_mov_swap_preserves_count` `array_support_write_preserves_count` `array_fall_write_preserves_count` `array_mov_write_preserves_count` `array_wake_write_preserves_count` `array_deactivate_write_preserves_count` `write_selector_preserves_count` `write_effect_count_balance` | T2 T21 T38 T39 | count rules ops selector |
| `R3` | Single-writer per phase; tie-break from the pre-phase state | `scan_order_total` `neighbor_cancel` | T14 | order priority |
| `R4` | Phase separation: colour × direction batches, injective targets | `neighbor_x_parity` `neighbor_y_parity` `neighbor_z_parity` `parity_flip_succ` `parity_flip_pred` `batch_target_injective` `diag_target_injective` `color_of_bit0` `color_of_bit1` `color_of_bit2` `color_target_x_par` `color_target_z_par` `color_collision_x_par` `color_collision_z_par` | T10 T29 T30 | parity color batch |
| `R5` | Falling is universal (density rule) | `fall_decreases` `fall_lowers_potential` `sand_sinks_in_water` `array_mov_cross` `array_mov_lowers_phi` `array_mov_lowers_phi_regime` | T9 T22 | rules potential fall |
| `R6` | Cohesion = rigidity, a local neighbourhood property | `crumble_decreases` `crumble_lowers_potential` `crumble_lowers_pot` `guarded_crush_lowers_pot` `array_crumble_lowers_phi` `array_guarded_crush_lowers_phi` `rock_crumbles_lighter` | T9 T19 | support potential writepot tick |
| `R7` | Support derived, never carried; scoped to disturbed cells | — | T9 | support |
| `R8` | Impact is a threshold event | `rock_crumbles_lighter` `sand_sinks_in_water` | T9 | rules |
| `R9` | Activity is explicit; wake effects land next tick | `budget_exhausts` `potential_additive` `strict_events_bounded` `settling_budget` `fall_lowers_potential` `crumble_lowers_potential` `swap_refines_array` `array_swap_pots` `swap_lowers_phi` `support_write_preserves_pot` `fall_write_preserves_pot` `mov_preserves_pot` `wake_preserves_pot` `deactivate_preserves_pot` `point_write_lowers` `array_support_write_preserves_phi` `array_fall_write_preserves_phi` `array_mov_write_preserves_phi` `array_activate_write_preserves_phi` `array_deactivate_write_preserves_phi` `write_selector_preserves_phi` `write_effect_phi_balance` `sup_mirror_preserves_phi` | T4 T4b T19 T38 T39 | sim potential settle refine writepot tick selector |
| `R10` | Determinism as a corollary of phase purity | `point_writes_commute` | T1 T31 | sim commit |
| `R11` | Worldgen is a pure terrain seeding function (the shell is a box/window property) | — (purity by construction) | T6 T7 T8 T16 T18 | worldgen chunk store |
| `R0` | Encoding and arithmetic substrate | `sanity` `grid_volume` `cell_full_mask` `cell_reserved_bits` `index_roundtrip` `cell_roundtrip` `material_encode` `word_cmp_eq_reflect` `u32_cmp_eq_reflect` `n_add_sub_le` | T5 spike bit31 spike mul wrap | bits grid cell nat word |

Reading the `—` rows: R7 is test-witnessed only (recorded as `G6`); R2 now has
the `V4` count laws (A.31–A.32, A.34).
R11 holds by construction and is witnessed by tests; R10's composition step now
has `point_writes_commute` (V3c-1, A.68) alongside its by-construction purity.

### 4.1 Conformance — contract and rule status

`Laws` above says what bears on a rule; this says whether the *engine* meets it.
Deliberately four columns, so the §4 matrix parser is unaffected. Statuses:
**conforming**; **deviating** (the engine contradicts the rule); **by
construction** (true because of the code's shape, not by proof); **unproven**.
This table is what would have caught T23/T24 on the day they landed.

| Ref | Target | Status | Open deviation / evidence |
|---|---|---|---|
| `C1` | Purity of phases | conforming | `Rules.plan`/`phase_plan_w` (V0-1, A.63): the phase reads only the pre-phase array and applies its write set afterwards, so no part reads a value another part produced. T23/T24 re-witnessed as conformance |
| `C2` | Closure (box, no wrap) | conforming | `V0-2` (A.64): every rule target is guarded by `Grid.step_inside`, so a boundary step is inert rather than wrapping; T27/T28 witness it with the shell painted away. `Grid.neighbor` still wraps, but no rule follows a wrapped step. (`Ops.wake` is now bounded by `Grid.step_inside` too — `G15` closed, A.88) |
| `C3` | Cost tracks disturbance | conforming | `V0-4b-3b` (A.77): the tick carries a **dirty-row mask** (one bit per `y` row, `src/dirty.bend`) across ticks. The next active set is exactly the cells the deferred wakes marked, so the work list is built by scanning only the mask's rows (`Dirty.dirty_todo`) — the `any_active` and `active_list` world scans are gone. Rows, not 16³ chunks: a chunk-major scan interleaves `y`, which lags the support pass's bottom-up `below` propagation. Settled tick ~1.3 µs (was ~89 µs); 20000 settled ticks 1.79 s → 0.027 s. Active work is the same write set, reached without the world scan |
| `R1` | Pre-phase reads only, bounded radius | conforming | `Rules.plan` never writes the array it reads (V0-1, A.63); every read is of the pre-phase state |
| `R2` | Conservation: swap/transform only | conforming | count laws closed (`V4`). **A.79 (`V3d-2`) closed the enumeration half too:** the write *effect* is now in the type (`Rules.Write.WSet.op : Rules.Op`, a closed datatype), so `plan` cannot emit an unclassified write and `write_effect_count_balance` is total over it — the `G14` inspection gap is gone. `G10` remains closed but its subject `Rules.step` was retired by A.63, so it is no longer the evidence here. |
| `R3` | At most one writer per cell per phase | conforming | contention is resolved from the pre-phase state: of the two opposite-axis diagonal claimants of one target, the smaller index owns it (V0-1, A.63; T23). Drop/crush targets are injective within a colour |
| `R4` | Colour × direction batches, injective targets | conforming | direction batches are a closed set (`Rules.Dir4`, no `k ≥ 4` fallback) and each batch's target map is proven injective (`batch_target_injective`, `diag_target_injective`, V0-3a, A.65); bit extraction reads `color_of` back as the three coordinate parities (`color_of_bit0/1/2`, V0-3b, A.66) and a same-colour target collision forces equal displacement parities (`color_collision_x_par/_z_par`), so the only cross-direction overlap is the opposite-diagonal parity class — resolved by the pre-phase tie-break (V0-1/T23, rule 3), not by re-reading |
| `R5` | Falling is universal | conforming | `fall_*` laws |
| `R6` | Cohesion rigidity is local | conforming | `V0-5` (A.81): the support seed reads the actual neighbours — the cell below (the support contact) and, where the below cell neither grounds nor supports, the five other faces (`Ops.side_sel`) — so grounding is neighbourhood-derived. `Ops.shell_adjacent` (A.62, the hardcoded `x/z/y ∈ {1,62}` shell) is gone; T40 witnesses below-static grounding, wall adhesion and the crush control |
| `R7` | Support derived, scoped to disturbed cells | conforming | `V0-5` (A.81): `Support.sup` derives support from the current neighbourhood (`below`, then the wall faces), never by position and never carried across a structural change. The activity gate and the `—`-no-staleness part hold; the world *scan* was the separate `C3` deviation, closed by `V0-4b-3b` (A.77) |
| `R8` | Impact is a threshold event | conforming | `rock_crumbles_lighter` |
| `R9` | Activity effects land next tick | conforming | `V0-4a` (A.71) defers each phase's wakes to tick end (T33); `V0-4b-1` (A.72) made a move **clear** the mover's active bit so it is not re-evaluated by a later colour phase (T34); `V0-4b-2` (A.74) defers the support pass's crush wake too (T36). Every wake now lands at tick end |
| `R10` | Determinism under any schedule | conforming | follows from `C1`: each phase is a pure function of its input (V0-1, A.63). The composition step now has laws — point writes at `ne_idx`-distinct leaves commute (`point_writes_commute`, V3c-1, A.68); the fold lifts to the list/region equality (`v3c_write_past_fold`/`v3c_fold_commutes`, V3c-1b, A.84) and `ne_idx`'s soundness half is proven (`v3c_ne_idx_sound`, V3c-2, A.84: `U32.is_eq(i, j) == True` forces `ne_idx == False`). V3c is **complete and reaches the engine**: `v3c_ne_idx_exact` (A.89: `ne_idx == Bool.not ∘ U32.is_eq` on full in-range trees) plus the engine wire (A.90: `v3cw_commit_fold`/`v3cw_commit_commutes` prove `Rules.commit_sets` on the projected write list equals `v3c_fold`, lifting the region-split equality to the engine's actual write set) |
| `R11` | Worldgen is a pure terrain seeding function | conforming | purity by construction; the **shell is a box/window property, not an absolute coordinate** (decision A, A.98): `Worldgen.gen_terrain` is shell-free, the canonical 64³ box adds its shell at the edges bit-for-bit (so `gen_terrain`+edge == `gen`), and the moving window / infinite mode samples the shell-free terrain. Window-edge shell permanence is `G-scale-8` |
| `R0` | Encoding and arithmetic substrate | conforming | `bits`/`grid`/`cell`/`nat`/`word` laws |

`C3` is *conforming*: `V0-4b-3b` (A.77) replaced the two world scans
(`any_active` + `active_list`) with the carried dirty-row mask. `V0-1` (A.63) closed the purity cluster
`C1`/`R1`/`R3`/`R10`, and `V0-2` (A.64) closed `C2`: the box is now enforced in
the grid, not by the shell. `R4` is *conforming*: `V0-3a` (A.65) closed the
direction half — a closed direction datatype and an injective per-batch target
map — and `V0-3b` (A.66) closed the colour half — `color_of` bit extraction and
the classification that a same-colour collision forces equal displacement
parities, leaving only the opposite-diagonal class to the rule-3 tie-break.
`R9` is *conforming*: `V0-4a` (A.71) accumulates each phase's pending wakes
and applies them once at tick end (`G12` closed; T33), `V0-4b-1` (A.72) cleared
the mover's active bit so a move cannot re-activate its own target mid-tick
(T34), and `V0-4b-2` (A.74) defers the support pass's crush wake as well (`G16`
closed; T36). No write activates a cell within the tick that reads it.
`R10`'s composition step now has its list/region laws (V3c-1b, A.84): the fold
of a write list commutes with an append/region split when the writes are
pairwise distinct (`v3c_fold_commutes`, `v3c_write_past_fold`), and the
`ne_idx`↔`U32.is_eq` *soundness* half is proven (`v3c_ne_idx_sound`). What
remains is V3c-2 completeness (`G3`).
`R6`/`R7` are now *conforming*: `V0-5` (A.81) replaced the positional support
seed with a neighbourhood read — the cell below, then the five wall faces — so
"rigidity is local" holds. No row is closed by rewording a rule to match the
code.

**Retirement (A.63).** `Rules.step` was replaced by `Rules.plan`/`phase_plan_w`, so the
`step_m` mirror in `src/step.bend` (law `step_mirror_balance`) no longer mirrors
the engine. It is **retired**: still a true theorem about the old selector
machine, no longer evidence for the engine. Per §3.4 it is kept, not deleted, and
must not be extended. `sup_m` (`src/tick.bend`, law `sup_mirror_preserves_phi`)
still mirrors `Support.sup` and stays **live**: `V0-4b` moved it with the deferred
crush wake (A.74) and `V0-5` with the neighbourhood seed (A.81), and the law is
unchanged in meaning. `G10` consequently stays closed only for the retired shape; the live `Rules.plan`
write-site enumeration was recorded as `G14`, **closed by A.79 (`V3d-2`)** by typing the effect.

### 4.2 Known landmines (recorded, not yet fixed)

Active code that can turn a fault into a silent wrong answer. None of these is a
proof gap; they are robustness debts, listed so that a later session does not
discover them by accident. `V0-1` (A.63) moved two of them from active debt to
bounded/unreached:

- **Silent selector default (bounded, A.63).** The retired `Rules.step` ended
  with `case _: world`, so an unknown state ended the phase scan mid-way.
  `Rules.plan` still has a `case _` fallback, but every selector is an internal
  literal chosen by `Bool.pick`, so it is unreachable by construction — it remains
  only as the compiler-required default for a `U32` scrutinee.
- **Silent candidate default (bounded for the live engine, A.65).** The retired
  `side_index`/`diag_index` end with `case _: i`, so a `k` outside `{0,1,2,3}`
  silently becomes a self-target instead of an error. `V0-3a` adds the closed
  `Rules.Dir4` datatype and moves the live `Rules.plan` onto it — every match is
  total, so the live engine's path has no silent default and no `k` loop bound to
  establish. `side_index`/`diag_index` are frozen with the retired `step_m`
  mirror (which still uses them); they are not on the live path.
- **Silent material default.** `Cell.density`/`static`/`slides`/`cohesion`/
  `default_cohesion` all end with `case _`, so any material id ≥ 6 is treated as
  empty-like (density 0, non-static): a bad id is invisible and can be fallen
  through.
- **Unproven fuel sufficiency.** `Rules.plan` and `Support.sup` return the world
  they have at fuel `0`, and `Sim`/`Support` pass a magic `2^24` with no law that
  it is enough (~13× slack today; `plan` spends at most ~16 transitions per cell ×
  32768 cells per phase, so ~2^19). Grow the selector and a tick silently does
  half its work.
- **Fixed settling budget in tests.** `test/simtests.bend`'s `settle` runs a
  fixed 50 ticks. T4b does assert the post-settle fixpoint, so the witness is
  guarded — but the budget itself is not derived.

Ownership of the world size from A.62 onward: `Grid.size()`/`volume()` and
`Chunk.size()`/`cells()` are the single sources; the engines and mirrors no
longer carry literals. `Chunk.per_axis()` (dead, and wrong: it said `4` for a
16³ chunk) was deleted rather than corrected.

---

## 5. State

### 5.1 Landed

| Milestone | What landed | Evidence |
|---|---|---|
| `M0` | plan, law scaffold, sanity law, gate green, native build | A.1 |
| `M1` | cell word, grid index math, layout laws, T5 | A.1 |
| `M1.5` | bit-lemma library; index/cell roundtrips promoted to proven laws | A.6 |
| `M2` | pure worldgen, ASCII cross-section runner, T6–T8 | A.2 |
| `M3` | 8-phase swap movement, T1–T3 | A.3 |
| `M4` | activity gating, 26-neighbor wake, settle, T4/T4b | A.4 |
| `M5` | support pass, crumble, impact crush, T9 | A.5 |
| `M6` | windowed `App.run` runner with editing | A.11 |
| `M7a` | parallel worldgen via structural `build_at` | A.18 |
| `M8a` | chunk key/index + pure per-chunk gen | A.21 |
| `M8b` | `U32`-keyed radix-tree chunk store | A.22 |
| `M8c` | chunk-store assemble + tick equivalence, T18 | A.23 |
| `M8d` | chunk sleeping + store eviction (conservative, gen-equal), T20 | A.30 |
| `V1` | Nat arithmetic + Φ-decrease / settling kernel | A.7 |
| `V2b-i` | `List.set` split and sum lemmas | A.20 |
| `V2b-ii` | array/model swap refinement + Φ-decrease under a point update | A.27 |
| `V2b-iii` | write→Φ bridge complete (word and `Array.swap.go` level): material field, support/fall/mov/wake/deactivate preserve pot, crumble lowers pot, point-write composition | A.28–A.29 |
| `V3a` | parity model + all-axis neighbor parity | A.13–A.14 |
| `V3b` | packed-index neighbor cancel + total scan order | A.15–A.17 |
| `V4` | conservation (rule 2): non-empty count preserved by every material-preserving write, the point-write balance, and the two-write movement swap, T21 | A.31–A.32, A.34 |
| `—` | pi tooling: proof loop, lemma index, audit | A.24–A.25 |
| `G9`/`G10` | engine write-site enumeration complete: `Rules.step` mirrored on `PT` (`step_m`, pair invariant, all-fuel `step_preserves`, law `step_mirror_balance`), joining the `Support.sup` mirror; closes `G10`/`G2`'s last residual | A.48, A.56 |
| `V3c-0` | engine-level write-target separation, partial: every `Rules` write target is a `dy = -1` neighbor, so `below`'s `y`-parity flips (law `below_write_flips_y_phase`) — the `Rules`-level form of V3a | A.58 |
| `M9` | CPU perf pass: cell-resolution render, settled-world tick fixpoint, color-restricted phase scan (active tick ≈ 21→4.5 ms, settled ≈ 0.09 ms), T25 — the colour-sublattice scan was **retired by `V0-4b-1` (A.72)** in favour of the active-cell work list | A.59 |
| `—` | BendHub reuse: `src/list.bend` (the `List` lemmas Base does not ship) and count-fold completeness (`cells_m`, `cnts_m_len`, `to_counts_len`) | A.60 |
| `V0-1` | phase purity: `Rules.plan`/`phase_plan_w` replace `Rules.step` — a read-only intent fold (`plan`) that decides from the pre-phase state, resolves contention by a local tie-break, and accumulates `sets`/`wakes`, then `commit_sets`/`commit_wakes` apply it; the `step_m` mirror is retired | A.63 |
| `V0-2` | closure: `Grid.step_inside` guards every rule target, so a boundary step is inert and the box is a property of the grid, not the shell; T27/T28 witnesses | A.64 |
| `V0-3a` | direction batching core: the live phase uses the closed `Rules.Dir4` direction set (a total match, so no `k ≥ 4` self-target fallback), and each direction batch's target map is proven injective (`batch_target_injective`, `diag_target_injective` — a translation on the torus, inverted by `neighbor_cancel`); every write target flips the phase `y` bit (`diag_write_flips_y_phase` joining `below_write_flips_y_phase`); T29 guards the refactor | A.65 |
| `V0-3b` | colour × direction classification: `color_of` bit extraction (`color_of_bit0/1/2` — bit `k` of the packing is coordinate `k`'s parity) and the cross-direction target-parity laws (`color_target_x_par`/`_z_par`, `color_collision_x_par`/`_z_par` — a same-colour collision forces equal displacement parities), so cross-direction overlap is exactly the opposite-diagonal parity class; T30 witnesses the direction-parity table | A.66 |
| `V0-4a` | deferred phase wake (rule 9, `G12` closed): `Rules.phase_plan_w` returns `(written world, pending wakes)`; `Sim.phase` is the writes-only transform, `Sim.tick_active` threads all eight phases' wakes and `Rules.commit_wakes` applies them once at tick end, so no phase evaluates a cell an earlier phase of the same tick woke. `Rules.phase` (immediate wake) removed as dead code; T33 witnesses the differential (woken cell inert this tick, active after) | A.71 |
| `V0-4b-1` | move clears active + work-list phase fold: `Rules.mov` (and the slide write) clear the mover's active bit, so a later colour phase cannot re-evaluate it in the same tick (T34: one cell per tick; `mov_preserves_pot`/`nempty_mov` proof terms updated). `Rules.plan` is driven by `todo: List<&2, U32>` (the active cells of the phase) instead of the colour sub-lattice, `Sim.active_list`/`filter_color` build it; T35 witnesses the colour filter. The evaluated set is now exact | A.72 |
| `V0-4b-2` | deferred support wake + work list built by the support scan: `Support.sup` accumulates the crushed cell instead of waking inline, so every wake lands at tick end (`G16` closed; T36). The pass returns the active cells it saw (`Support.pass_gated` → `(world, wakes, todo)`), so `Sim.tick` is `any_active` → support → phases over the returned list, dropping the separate `active_list` scan. `sup_m` updated to the crush-only shape (deferred wakes Φ-neutral); settled tick ≈ 0.09 ms preserved | A.74 |
| `V0-4b-3a` | work-list support machine: `Support.sup` is driven by a scan (`scan = True`, setup) or by the work list (`Support.pass_todo`, tick), so the tick's support no longer scans the world; `Sim.active_list` builds the list ascending (bottom-up for `below` propagation). Per-cell writes unchanged, so `sup_m`'s Φ claim is unaffected by the advance. Active transient ≈ 15 % faster than A.74 | A.75 |
| `V0-4b-3b` | carried work set (`C3` closed): the tick threads a dirty-row mask (`src/dirty.bend`, one bit per `y` row) and builds the work list by scanning only the rows a wake reached (`Dirty.dirty_todo`), so the `any_active`/`active_list` world scans are gone. Rows, not 16³ chunks: a chunk-major scan interleaves `y` and lags the support pass's bottom-up `below` propagation, while the row scan reproduces the exact global ascending order. The mask is threaded only through the commit (support/phase entry points stay monomorphic), and a wake's 3-row reach is arithmetic (`Dirty.mark_wake`), not a recursive 27-neighbour walk. Settled tick ~1.3 µs (was ~89 µs); T37 witnesses the carried work set | A.77 |
| `V3c-1` | schedule-invariance kernel: point writes at leaves that `Commit.ne_idx` separates commute (`swap_m (swap_m t n i v) n j w = swap_m (swap_m t n j w) n i v`, law `point_writes_commute`), so a merged write set applies order-independently; `ne_idx` mirrors `swap_m`'s own walk (a split at some level, `False` at a leaf) and is exactly distinctness for in-range indices; T31 witnesses both the commutation and the predicate's sharpness. The engine no longer needs a `read/write` ordering argument (V0-1): this is the *composition* half. The list/region fold (V3c-1b) and the `ne_idx`↔`U32.is_eq` refinement remain | A.68 |
| `V3d` | generic material-preserving write family: the four hand-written `PT` recursions (`Tick.chg_support`/`chg_fall`/`chg_activate`/`chg_deactivate`, each with its own `chg_X_if` and `array_X_write`) are replaced by one traversal over a `Data`-kinded selector, with `mat_pres` as the whole per-site obligation. A selector is required rather than a function parameter because Bend closures are affine (callable at most once) while a write is applied at every leaf. Also lands the first executable Φ oracle: `Settle.array_phi` is proof-side and `suml` is not tail-recursive, so it overflowed on a 2^18-cell world and the flagship property had never been checked end to end. T39 pins the oracle to `Settle.pot_at`; T38 runs it — Φ is non-increasing across 60 real ticks and strictly decreases | A.78 |
| `V3d-2` | **write effects are typed (`G14` closed)**: `Rules.Write`'s `WSet` carries `op: Rules.Op` — a closed `Data` datatype with a total `Rules.apply_op` — so `plan` cannot emit an unclassified write and the write-set enumeration is a typing fact rather than an inspection. `write_effect_phi_balance`/`_count_balance` are total over `Op`; the decrease is refined per *shape* (preserving self-write / guarded crush / two-cell movement) rather than per site. The move/slide sites collapse to `OPres{OMov{}}`/`OPres{OId{}}`; `commit_sets` becomes `world[idx] <- apply_op(src, op)`, values still precomputed in `plan`, so `C1` purity and `C3` cost are untouched. Engine change only — `rules.bend` + one `sim.bend` pattern — with the fast and sim suites unchanged | A.79 |
| `V3c-1b` | schedule-invariance list/region fold: `Commit.v3c_fold` applies a `List` of point writes through `Refine.swap_m`; `v3c_write_past_fold` lifts the V3c-1 kernel past a whole fold and `v3c_fold_commutes` is the region-split equality (append in either order for pairwise-distinct writes); T32. **V3c-2 (soundness half):** `v3c_ne_idx_sound` — `U32.is_eq(i, j) == True` forces `ne_idx == False` — so a proven `ne_idx` implies the engine's distinctness; T33. Completeness (distinct in-range indices separated on a full tree) and wiring the engine's `Rules.Write` list into the fold remain `G3` | A.84 |
| `G5` (read half) | read threading between the engine and the `PT` mirror: `src/g5.bend` proves `Array.get.go`/`Tick.tget` are the same `n/2` walk (`g5_read_get_go`), the `Array.get` size wrapper (`g5_size_pack`), the composed read (`g5_read_get`), and read-after-write at the selector's index (`g5_tget_swap`), covering every live `sup_m` read at the engine's `Array.get(world, i)` index. Remaining: the `U32` mask identity and the `SupSel` branch-table transcription | A.83 |
| `G5` (mask) | G5 mask residual closed: `g5_twidth_pow` (`g5_twidth t == 2^g5_depth t`), `g5_and_mask_id` (`i < g5_twidth t` ⇒ `U32.and(i, U32.sub(g5_twidth t, 1)) == i`), and `g5_read_get_bare` (the bare-index read, chaining `g5_read_get` with the mask identity), via a self-contained `Word`-level bit-arithmetic development in `src/g5.bend` (all `g5_`); T37–T39. The only remaining `G5` caveat is the `SupSel` branch-table transcription (methodological) | A.86 |
| `V3c-2` (structural) | completeness, structural half: `v3c_ne_idx_sep`/`_same_l`/`_same_r` prove the three cases of `ne_idx`'s node recursion, and `v3c_add_sub` gives the unconditional `add ∘ sub` roundtrip (`Word.add(n, Word.sub(n, a, b), b) == a`); T34/T35 witness exactness on the 8- and 16-leaf canonical trees. Full completeness reduces to three `U32` order/range bricks (`is_lt` base reflection, `sub` range preservation, bounded `shr(two)`) | A.87 |
| `G15` | wake bounded by the grid: `Ops.wake` now guards each neighbour with `Grid.step_inside` (`wake_x` writes through `mark_if`), so a wrapped step is inert — rule 9's reach respects the closed box, matching `V0-2`'s rule-target guard. The `PT` wake mirror carries the same guard as a parameter (`wake_write_m`/`wake_write_m_preserves`); law `g15_wake_step_inert`; T43–T45 + sim T44–T46 | A.88 |
| `V3c-2` (complete) | completeness done: `v3c_ne_idx_complete` (the converse of the soundness law) and `v3c_ne_idx_exact` (`ne_idx(full k, two k, i, j) == Bool.not(U32.is_eq(i, j))` for in-range `i, j`) — the three arithmetic bricks (`is_lt` base reflection, `sub` range preservation, canonical size halves) plus the depth induction over the structural case laws; T36/T40–T42 | A.89 |
| `V3c` (engine wire) | `G3` closed: `src/v3cw.bend` proves the engine's `Rules.commit_sets` on the projected write list equals `Commit.v3c_fold` (`v3cw_commit_fold`; `WSet` via `apply_op`, `WWake` neutral) and lifts the region-split equality to the engine write set (`v3cw_commit_commutes`), keyed by `Commit.v3c_pair_ne` on the projection. T46–T48. Methodological caveat: `v3cw_lin` is the multiplicity-erased copy needed because `commit_sets` is linear | A.90 |
| `view3d` | interactive 3D viewer (presentation only): `view/voxel.bend` is a pure Amanatides–Woo DDA voxel raycaster + camera; `runners/view3d.bend` is the `App.run` shell (fly camera W/A/S/D + Q/E + arrows + mouse-drag, `speed` = sim ticks per frame, pause). T49 witnesses the DDA; `src/` untouched; ~94 ms/frame native at 128×128 | A.91 |
| `view3d` (frontend pass) | first-version frontend fixed and scaled: keyboard bug fixed (`bit_of` accepts both backend key conventions; T50), DDA rewritten to two calls/cell with a correct ray range (`dda_steps` = 256 cells; T49 still green), aspect-correct integer-scaled 1920×1080 rendering via the backend's top-bits mapping (`view_image` + `clog2`/`scale_bits`/`vis_dim`; T51), runtime render-depth control (`, `/`.`, 5–8), and both key conventions in the runner. Presentation only, `src/` untouched | A.92 |
| `bridge` (engine→renderer) | P0 export surface: `runners/export.bend` writes a chunk-oriented snapshot (`.bvs`) + `Worldgen.gen` reference vectors (`.bvg`); `runners/SERVE.md` + `runners/serve.bend` are the sidecar transport design/skeleton; T52–T55 pin the golden contract (cell word, index, chunk key, gen vector). IO only, `src/` untouched | A.93 |
| `scale` (trace + coordinates) | P1: `Sim.tick_trace` returns `(world, deltas)` (global coord + new word), `tick` unchanged, T56 witnesses replay == tick on the render-visible fields. P3: additive `src/cw.bend` global-coordinate module (T57–T60) + `SCALE.md` migration design; live `Grid`/`Sim` untouched, gate green | A.93 |
| `V0` | semantics rewrite complete: phase purity (`V0-1`), closure (`V0-2`), direction/colour batching (`V0-3`), cost via the carried dirty-row work set (`V0-4b`), and the neighbourhood support seed (`V0-5`) — every `C1`/`C2`/`C3` and `R1`–`R11` row in §4.1 now conforms | A.63–A.81 |
| `bridge2` (transport) | `runners/serve.bend` real sidecar: length-framed `[len][kind][payload]` (HELLO/SNAPSHOT/DELTA/PING/BYE out, CREDIT/REQUEST/STOP in), the sparse snapshot (`Store.evict` regenerability + `assemble`), and the **B2 decision** (DELTA = render-visible fields, `(idx, Cell.deactivate word)`, global `Grid.index`, no `WWake`); T61–T65. IO only, `src/` untouched. Residual: credit/coalescing (`G-bridge-1`) | A.94 |
| `gscale` (G-scale-3) | `src/gscale.bend` proves the `cw` split/rejoin in `Bits`/`Word`: `(w>>4)<<4 + (w&15) == w & 16383` (`gscale_global_rt`) plus the key/local model roundtrips, five laws `gscale_cw_{x,y,z,key,local}_rt`; T66–T70. Closes `G-scale-3`; mentions no `Grid.index`, so not in the torus retirement set | A.94 |
| `window` (S1 step 2) | `src/window.bend`: the `Window` model (base chunk + cell origin) and the torus-free window-local index map (`win_lx/ly/lz`, `win_index`, inverses `win_gx/gy/gz`, `win_key`), with the canonical window pinned to the 64³ box. Additive — the live path still uses `Grid`, and no `&63` appears in the map, so a global coordinate above the box keeps its chunk index. T81 (canonical `win_index == Grid.index`) / T82 (global 80 not folded). The relabelling *law* is filed as `G-scale-7` | A.95 |
| `window` (S1 step 3) | explicit resident set: `Window.resident_keys` (the window's 64 chunk keys, chunk-ordinal) and `Store.assemble_keys` (assemble over a key list instead of `assemble_go`'s loop bounds; additive, `assemble` unchanged); T95 (explicit set == implicit set) / T96 (reconstructs `Worldgen.build`). Also adapts `coreidea` rule 11 / `R11`: the shell is a box/window property, the terrain (`gen_terrain`) is shell-free — decision A for `G-scale-8` | A.99 |
| `gscale2` (full cw + winset) | `src/gscale.bend` lifts the `cw` y/z roundtrips to arbitrary `(x,y,z)` (`gscale_cw_y_rt_full`/`_z_rt_full`; field-extraction lemmas), and new `src/winset.bend` is a pure finite-set model of the resident chunk keys (`winset_mem`/`insert`/`remove`/`all`, `winset_evict`, `winset_gen_cell`) with laws `winset_mem_insert_self`/`_other`/`winset_remove_insert`; T71–T75. `G-scale-4` groundwork (the assemble/evict roundtrip law remains open) | A.96 |
| `bridge3` (sidecar flow control) | `runners/serve.bend` realises `SERVE.md` §5–§6: bounded queue, credit window (`bridge3_credit`/`bridge3_emit`, no overrun), drop-and-keyframe delta coalescing, idle PING, and a **forked** stdin reader (`Chan` + `IO.spawn`) so control is read continuously; T76–T80. `G-bridge-1` partially closed (engine/writer split + read reassembly remain) | A.96 |
| `bridge2` (snapshot framing fix) | `runners/export.bend`'s dense record encoder gathered by a flat `Grid.index` slice (`gi/4096 = y`), so each "chunk" record was a **64×64 `y`-plane** labelled with a `Chunk.key` — 130835/262144 cells misplaced, and mutually inconsistent with the (correct) sparse body. Fixed: one shared `bxe_cell_index`/`bxe_chunk_cells` gather in the `Store.chunk_list` order, reused by the dense and sparse paths (`serve.bend` drops its private copy); `G-bridge-2` closed. T47 (native, full body dense == sparse) + T83 (fast, address mapping). IO only | A.97 |
| `bridge2` (record order) | the A.97 fix corrected the record *address* but the walk still consed ascending, so each record's cells were in **reverse** `Chunk.local` order (file offset `i` held local `4095-i`). Fixed: the walk is descending so the head is local 0 (`runners/export.bend`); T84 compares the gather element-by-element to `Store.chunk_list` (T47 alone is blind — both encoders shared the order). Doc corrected: records are chunk-ordinal, not packed-key-monotonic. Files `G-bridge-3` (closed) | A.98 |

Dropped by measurement (not by budget): `M7c` parallel render (A.19).

### 5.2 Open work (frontier-first)

**Legend.** An item is `- [ ] **ID** <intent> · <state> · deps: … · serves: …`.
`state ∈ {next, parallel, open, blocked, optional, deferred}`: `next` is the
frontier (all deps met, highest priority), `parallel` may run alongside it,
`blocked` has an external dependency, `optional` is droppable, `deferred` is
deliberately not now. Groups are by state; order *within* a group is the `deps:`
chain, and the groups are independent of each other. `serves:` names the
contract clause / rule the item advances. The **Dependency view** table is the
single source of truth for order; landed detail follows it (§5.1 is the one-line
index).

#### Frontier — do next

*(`S1` — the chunk-window migration below — is the frontier; every `V0` sub-step is landed. The optional track is droppable.)*

#### Frontend — presentation track (new dimension)

- [ ] **F1** Frontend quality/speed: `view3d` at 1920×1080 is now aspect-correct
  and integer-scaled, but a per-pixel Bend raycast caps it at ≈19 fps at render
  depth 7 (120×68 visible cells at 16×) and ≈70 fps at depth 6 (60×34 at 32×);
  depth 8 (240×135 at 8×) is ≈5 fps. `,`/`.` expose the tradeoff at runtime.
  What would close the gap: (a) profile and cut the per-cell cost — the dominant
  term is the `Array.get` tree descent, one per DDA cell, so a per-frame flat
  world view or a hierarchical empty-space skip is the first thing to try;
  (b) a coarse occupancy pyramid built once per tick to skip empty regions;
  (c) the blocked GPU path (`G4`); (d) accept a lower internal resolution with
  a deliberately crisp upscale. deps: — · serves: —.

#### Engine↔renderer bridge (Bendview)

- [x] **B1** Transport implementation · landed (A.94) · deps: `bridge` P0 · serves: —
  — the real sidecar is in `runners/serve.bend` (length-framed `[len][kind][payload]`,
  all out/in kinds) plus the sparse snapshot (`Store.evict`'s sleeping ∧ gen-equal
  test; `assemble` regenerates). The flow-control residual is now largely
  realised (A.96, `bridge3`: bounded queue, credit window, coalescing, idle PING,
  forked reader); the engine/writer thread split and read reassembly remain —
  `G-bridge-1`.
- [x] **B2** Delta contract decision · landed (A.94) · deps: `scale` P1 · serves: —
  — **decided: render-visible fields only.** A `DELTA` record is `(idx, word)` with
  `word = Cell.deactivate(new)`; the activity bit is engine-internal and `WWake`
  is not transmitted. Encoded in `serve.bend`, witnessed by T65. `idx` stays the
  global `Grid.index`; the framing is coordinate-agnostic, so `S1` changes only
  the payload interpretation.
- [ ] **S1** Chunk-window migration · **in progress** · deps: `scale` P3 · serves: scale
  — `SCALE.md` steps 2–6. **Step 2 landed (A.95):** `src/window.bend` (the
  `Window` model + torus-free index map, canonical = the 64³ box; T81/T82).
  **Step 3 landed (A.99):** an explicit resident set — `Window.resident_keys`
  (the 64 chunk keys) and `Store.assemble_keys` (assemble over the key list);
  T95 (explicit == implicit set) / T96 (reconstructs `worldgen`). Remaining:
  step 4 window motion, step 5 window-sized dirty set, step 6 torus-law
  retirement. Each step gate-green; gap candidates `G-scale-1`..`G-scale-8`
  (`G-scale-3` closed). Decision A (`G-scale-8`): the window / infinite mode
  samples shell-free `Worldgen.gen_terrain`, the closed box keeps its shell as a
  **reference mode** (`R11` adapted, A.99).

#### Optional track — droppable, does not gate the frontier

- [ ] **M7d** Parallel phase folds (CPU) · optional · deps: V3c · serves: —
  — **optional, droppable**, gated on `V3c`. A core-count multiplier on top of
  `C3`, not a scale prerequisite: no CUDA (`G4`), the 64³ world is too small to
  showcase it, and dropping M7/M8 costs nothing above the scale track.

#### Blocked / external

- [ ] **M7b** / **M7e** GPU worldgen / phases · blocked · deps: — · serves: —
  — blocked on a CUDA host (`G4`).

#### Deferred

- [ ] **P1** Publish a proven slice to BendHub · deferred · deps: — · serves: —
  — **deferred** until the engine is more complete; §5.4 records what a publish
  must contain, the guardrails, and why it is not done yet.

#### Dependency view

| id | state | deps | unblocks |
|---|---|---|---|
| `V3c` | landed (A.90) | — | — |
| `B1` | landed (A.94) | `bridge` P0 | — |
| `B2` | landed (A.94) | `scale` P1 | — |
| `S1` | **next** | `scale` P3 | Bendview M3/M4 |
| `F1` | open (frontend) | — | — |
| `M7d` | optional | `V3c` (landed A.90) | — |
| `M7b`/`M7e` | blocked | — | — |
| `P1` | deferred | — | — |

**Order note.** The frontier is `S1` (`B1`/`B2` landed in A.94); the optional
parallel track is independent of it. `M8a–M8d` and `M9` have landed. M7 and V2b are independent; V2b
may proceed first if the GPU path stalls. Dropping M7/M8 costs nothing above the
scale track; dropping V2 costs the settling guarantee.

#### Landed (detail; one-line index in §5.1)

- [x] **V0** Semantics rewrite (contracts `C1` purity, `C2` closure, `C3` cost) · landed · deps: — · serves: C1 C2 C3
  — scoped in A.61; sub-steps land and test alone. All five sub-steps landed:
  `V0-1`/`V0-2`/`V0-3`/`V0-4b`/`V0-5`.
  **V0-1 done (A.63):** `Rules.plan`/`Rules.phase_plan_w` replace `Rules.step`;
  `phase(state) = commit_sets(plan(state))`, `plan` reads only the pre-phase
  state and resolves contention from it; T23/T24 re-witnessed as conformance and
  T26 (a grain in an empty column settles) added. **V0-2 done (A.64):** every rule
  target is guarded by `Grid.step_inside`, so a boundary step is inert and the
  box is a grid property, not the shell (T27/T28). **V0-3a done (A.65):** the
  live engine's directions are the closed `Rules.Dir4` set (no `k ≥ 4` default),
  each direction batch's target map is proven injective, and every write target
  flips the phase `y` bit; T29 guards the refactor. **V0-3b done (A.66):**
  `color_of` bit extraction (`color_of_bit0/1/2`) plus the cross-direction
  classification (`color_collision_x_par`/`_z_par`: a same-colour collision
  forces equal displacement parities), so the only cross-direction overlap is
  the opposite-diagonal class, resolved by the rule-3 tie-break; T30 witnesses
  the direction-parity table.
  **V0-4a done (A.71, `G12` closed):** a phase's wakes are pending — `Sim.phase`
  returns the written world, `tick_active` threads all eight phases' wake lists
  and `Rules.commit_wakes` applies them once at tick end, so a later phase never
  evaluates a cell an earlier phase of the same tick woke; T33 witnesses it.
  `Rules.phase` (immediate wake) was removed as dead code.
  **V0-4b-1 done (A.72):** a move clears the mover's active bit (`Rules.mov`,
  slide case 32), so the mover is not re-evaluated by a later colour phase in the
  same tick — this closed the last source of in-tick activation and made the
  evaluated set exact (T34: one cell per tick). The eight phase folds now run
  over an **active-cell work list** (`Sim.active_list`/`filter_color`,
  `Rules.plan` takes `todo: List<&2, U32>` and drops the colour sub-lattice
  advance) instead of scanning 32768 cells per colour; T35 witnesses the colour
  filter. Measured runtime is unchanged at 64³ because the full-world scans
  remained until `V0-4b-2`/`V0-4b-3b` removed them.
  **V0-4b-2 done (A.74, `G16` closed):** the support pass no longer applies its
  wake inline — a crush accumulates the crushed cell and the tick applies all
  wakes (support + phase) at tick end (T36). The pass also returns the active
  cells it saw, so it *builds the phase work list*: the tick is now
  `any_active` → `Support.pass_gated` → phases over the returned list, dropping
  the separate `active_list` scan. Settled tick ≈ 0.09 ms (preserved); active
  path one scan lighter. `sup_m` was updated to mirror the crush-only shape (the
  deferred wakes are Φ-neutral).
  **V0-4b-3a done (A.75):** `Support.sup` is driven either by a full scan
  (`scan = True`, setup `pass_all`) or by the work list (`Support.pass_todo`),
  so the tick's support no longer scans; `Sim.active_list` builds the list
  ascending (bottom-up for support) and both support and the phases fold it.
  Measured: the active transient is ≈ 15 % faster than A.74; settled unchanged
  (still one `any_active` scan).
  **V0-4b-3b done (A.77, `C3` closed):** the tick carries a **dirty-row mask**
  (`src/dirty.bend`, one bit per `y` row) and builds the work list by scanning
  only the rows a wake reached; the `any_active` and `active_list` world scans
  are gone. Two A.76 blockers were cleared: (1) a recursive 27-neighbour
  `block_mask`, inlined once per wake in the synchronous wake fold, overflowed
  the checker, so the row reach is arithmetic (`Dirty.mark_wake`); (2) the 16³
  chunk mask's chunk-major scan interleaves `y`, which lags the support pass's
  bottom-up `below` propagation, so the granularity is rows, whose scan order is
  exactly global ascending. The mask is threaded only through the *commit*; the
  support/phase entry points stay monomorphic. T37 witnesses the carried work
  set; settled tick ~1.3 µs (was ~89 µs).
  **V0-5 done (A.81, `R6`/`R7` closed):** the support seed is a neighbourhood
  test. `Ops.shell_adjacent` (the hardcoded `x/z/y ∈ {1,62}` shell) is gone;
  `Support.sup` reads the cell below — the support contact — and grounds a cell
  whose below is static material, falling back to a five-face wall-adhesion read
  (`Ops.side_sel`) only where the below cell neither grounds nor supports, so the
  common terrain path pays no extra reads. `sup_m`'s `S1`/`S2` move with it
  (`tstatic_side`). No coordinate is baked in, so interior bedrock grounds too;
  T40 witnesses below-static grounding, wall adhesion, and the crush control.
  `step_m`/`sup_m` (the mirror layer): `step_m` is **retired** (A.63 — it
  mirrored the removed `Rules.step`); `sup_m` was kept live and moved with
  `Support.sup` in `V0-5` (see §3.4 retirement, §4.1).

- [x] **V2b-ii** `Array.swap.go` ↔ `to_pots` point-update correspondence — landed
  (A.27): a non-linear `PT` model with a machine-checked `Array.swap.go`
  refinement, the point-update pot list, and the Φ-decrease. Closes `G1`; the
  one phrasing linearity forbids is recorded as `G8`.
- [x] **V2b-iii** `Sim.tick` as a composition of `replace_decreases` — landed
  (A.28–A.29): every write primitive's Φ effect is machine-checked at both the
  `Word`/`Cell` level and the array (`Array.swap.go`) level — support/fall/mov/
  wake/deactivate preserve pot, rock crumble lowers it, swaps lower it — and
  `point_write_lowers` is the composition step. Closes `G2`; the two residuals are
  `G9` (non-rock crush) and `G10` (write-site enumeration).
- [x] **V2 Global settling** — complete (ii and iii landed); `M8d` landed (A.30).
- [x] **M8d** Chunk sleeping/eviction — landed (A.30): `assemble` regenerates
  missing chunks from pure gen, so the store is a sparse overlay; `Store.evict`
  drops sleeping chunks that are bit-equal to gen (a checkable, conservative
  regenerability test), and eviction is lossless. Test-witnessed (T20); widening
  eviction to all sleeping chunks needs the sleep-invariance proof (`G10`).
- [x] **M9 CPU perf pass** — landed (A.59). Native at 64³, before: a tick was
  **≈ 21 ms and flat** (settled or active) because every pass scanned all
  262144 cells. Landed wins: (1) **cell-resolution render** —
  `runners/window.bend` builds a 64×64 quadtree (one leaf per cell) and lets the
  window scale it, 16× fewer `Array.get`s and ~16× fewer `Qua`/`Pix` per frame;
  (2) **settled-world tick fixpoint** — `Sim.any_active` scans for the active
  bit and `tick` returns unchanged when none is set (≈ 21 ms → ≈ 0.09 ms per
  settled tick); (3) **color-restricted phase scan** — `Grid.color_at`/
  `next_color`/`color_last` enumerate a phase color's 32768 cells in flat-index
  order and `Rules.step`/`Sim.phase` visit only those (the same acted-on cells,
  in the same order, so it is semantics-preserving), active tick ≈ 21 → ≈ 4.5
  ms; `build+pull+30 ticks` 0.62 s → 0.036 s. T25 witnessed the sublattice.
  **Retired by `V0-4b-1` (A.72):** the phase fold now runs over the active-cell
  work list, so the colour sub-lattice helpers (`Grid.color_base`/`color_at`/
  `color_last`/`color_s`/`next_color`) and T25 were removed. The measured tick is
  unchanged because the full-world scans remain (`V0-4b-2`).
  **Correction to the original win list:** the literal "skip sleeping regions in
  the scan" is *not* semantics-preserving on its own — a phase's `wake` marks
  neighbours that later phases of the same tick evaluate. `V0-4a` (A.71) closed
  the *phase* case (`G12`): wake is now pending until tick end, so a pre-phase
  activity snapshot is sound for the phase fold. What still blocks a region skip
  is the support pass's own crush-wake (`G16`) and the work-set/wake-updated-fold
  itself. That work is **`V0-4b`/`C3`**, not `M9` and not `V3c`. CUDA stays deferred: it needs CUDA 12 at
  `/usr/local/cuda` (absent here) and only pays off at M8 scale.
- [x] **V4 (conservation)** — landed (A.31–A.32, A.34): every material-preserving
  write preserves the count, `array_point_write_count_balance` gives the exact
  displacement identity, and `array_mov_swap_preserves_count` proves the
  **movement swap** (the two writes telescope). Rule 2 is fully law-covered.
- [x] **G9/G10 unlock (option-2 route)** — landed.
  1. [x] `Word.cmp` reflection proven (A.38): `word_cmp_eq_reflect` (general `n`,
     not just `32n`) and `u32_cmp_eq_reflect` in `src/word.bend`, so
     material-guarded engine logic is now provable.
  2. [x] Guard the crush sites to rock (`Rules.step` sel 22, `Support.sup` sel 6)
     via `Ops.crush_if_rock` (A.39), with the point-level law
     `guarded_crush_lowers_pot`; behaviour-validated by A.37 (non-rock
     field-reset is not load-bearing).
  3. [x] Mirror `Support.sup`/`Rules.step` on `PT` for `G10`. The crush-site
     write primitive is done (A.40): `array_guarded_crush_lowers_phi` gives the
     guarded write's Φ effect at every index (rock gap, or identity), so both
     crush sites are covered without a `G9` hypothesis. The `wake`/activate
     infrastructure is done (A.41): `array_activate_write_preserves_phi` and the
     `wake_*_m` mirrors. Both mirror obstacles are resolved (A.42, A.45): use a
     datatype selector (`SupSel`) rather than matching an opaque `U32`, and thread
     the wake fuel as an abstract `Nat` (a concrete `3` unrolls into a
     normalisation cliff). The full `sup_m` + `sup_m_preserves` is landed (A.48),
     with the `SupSel` selector, the abstract wake fuel, the top-level
     `sup_pass_m`, and law `sup_mirror_preserves_phi`; the `Support.sup` half of
     the write-site enumeration is now machine-checked. The `Rules.step`
     movement write site is now proven (A.53): `leaf_base` restores the
     size-free `chg_m` projection A.52 said was missing, so the two
     `array_swap_decreases` balances telescope into the unconditional
     `array_mov_cross`, and `array_mov_lowers_phi` gives the Φ drop by
     `fall_gap` under the fall-regime hypothesis (`G11` closed). A.54 then
     proved the Nat order lemma `n_add_sub_le` (the `{False == True}` branch is
     closed by an `Equal.cong`/`Bool.pick` motive), so the regime is the single
     order Bool `Nat.is_ge(mov_S, mov_T)` and `array_mov_lowers_phi_regime`
     derives the gap identity. The `Rules.step` fuel-loop mirror `step_m` is
     landed (A.56): `src/step.bend` mirrors the whole state machine with a
     `StepSel` datatype and the abstract wake fuel, and instead of committing to
     a single φ gap it carries a **pair** of accumulators with the invariant
     `Φ(current) + da == Φ(start) + db`. Every write composes its exact leaf
     balance `(old pot, new pot)` (`pt_write_balance`, transported
     `Refine.swap_balance`); a wake is folded by `sr_phi_cong`; `step_preserves`
     is the all-fuel theorem, and the top-level law `step_mirror_balance`
     instantiates `step_pass_m` (the `Sim.phase` entry point, wake fuel `3`). The
     balance is unconditional — the engine's `can`/fall-regime is never
     re-derived — so both write-site enumerations (`Support.sup`, `Rules.step`)
     are now machine-checked and `G10` is closed.
  See `HISTORY.md` A.36–A.56 for the analysis and probes.

**GPU expectation (honest).** The 64³ world is too small to showcase a GPU; the
GTX 1050 is discrete VRAM (transfer cost) and falling-sand work is divergent,
while the GPU's sweet spot is uniform numeric work. Worldgen/noise are the good
GPU targets and real payoff is at M8 scale. Near-term wins are CPU forks.

### 5.3 Trust boundary (the gap registry)

Machine-readable: `bend_audit` parses this table. `Kind` is `unproven` (we claim
it but have no proof), `accepted` (a deliberate assurance boundary), `standing`
(a methodological caveat that applies across claims), or `review` (needs a human
decision). Status is `open`, `accepted`, `review`, or `closed`.

| ID | Kind | Unproven / assumed | Status | Gates | Closes by |
|---|---|---|---|---|---|
| `G1` | unproven | `Array.swap.go` ↔ `to_pots` point-update correspondence (V2b-ii) | closed | M8d | proven: `swap_refines_array` + `array_swap_pots` (A.27), stated over the `PT` presentation (`G8`) |
| `G2` | unproven | `Sim.tick` is a composition of `replace_decreases` (V2b-iii) | closed | M8d | proven (A.28–A.29): all write effects at the array level + `point_write_lowers`; residuals `G9` (non-rock crush) and `G10` (write-site enumeration) |
| `G3` | unproven | schedule invariance: region-split fold = sequential fold (V3c) | closed | M7d | builds on V3a+V3b (proven). **The A.57 framing — T23 cascade, T24 intra-phase activation, "a per-cell transition + the forward activation closure (V3c-1/V3c-2)" — is obsolete:** `V0-1` removed both counterexamples, so the evaluated set is fixed and there is no activation closure left to characterise. What remains is the *composition* equality, and it gates only `M7d`, not `C3`. A.58 landed the provable fragment **V3c-0**: every `Rules` write target is a `dy = -1` neighbor, so `below`'s `y`-parity flips (law `below_write_flips_y_phase`); the full color separation (bit extraction of `color_of`, `k < 4` bounds for `diag_index`/`side_index`, `is_ne` reflection) remains. Prior art (A.60): `bend2-from-zero`'s `life/LIFE_PAR_PROOF.bend` proves `tree_is_serial` — a fork/join `tree_cells` equals the sequential `block` loop by depth induction via a `cells_add` split lemma, with `src/list.bend` supplying the list glue. It establishes equal *outputs* only (no contention), which is exactly what T23/T24 refute, so it is a proof-*shape* template, not a reusable theorem. **A.63 landed V0-1**: the engine now resolves contention from the pre-phase state (a local opposite-axis tie-break, witnessed by T23), so the target map is collision-free in the running engine; **A.65 landed V0-3a**: the live engine's directions are the closed `Rules.Dir4` set (the `k ≥ 4` self-target default is off the live path) and each direction batch's target map is proven injective (`batch_target_injective`, `diag_target_injective`), with every write target flipping the phase `y` bit (`diag_write_flips_y_phase`, T29). **A.66 landed V0-3b**: `color_of` bit extraction (`color_of_bit0/1/2` — bit `k` of the packing is coordinate `k`'s parity) and the cross-direction classification (`color_collision_x_par`/`_z_par` — a same-colour target collision forces equal `par dx` and `par dz`), so the only cross-direction overlap is the opposite-diagonal parity class `{K0,K1}`/`{K2,K3}`, which the V0-1 tie-break resolves; T30 witnesses the parity table. `is_ne` reflection of the drop-vs-slide disjointness is not needed for the claim (it is stated over parities) and the schedule-invariance *equality* (V3c) remains. **A.68 landed V3c-1**: the composition half is now a theorem — point writes at `Commit.ne_idx`-distinct leaves commute (`point_writes_commute`, T31). `ne_idx` is a computable predicate mirroring `swap_m`'s top-down walk whose stability under the recursion is what makes the induction go through with no `U32` arithmetic; it is exactly `i != j` for in-range indices, and refining it to the engine's `U32.is_eq(i, j) == False` is the open residual. What remains for the equality: fold the kernel over the engine's `List<Write>`/region split (V3c-1b) — the per-phase `plan` reflection was `G14`, **closed by A.78 (`V3d-2`)** by typing the effect in `Rules.Write`, so the composition fold is now the only thread left here. The A.57 phrase "forward activation closure" is now moot: V0-1 fixed the evaluated set and defers wake past the phase. **A.84 landed V3c-1b + V3c-2 soundness**: the fold commutes under an append/region split for pairwise-distinct writes (`v3c_fold_commutes`, `v3c_write_past_fold`, T32) and `ne_idx == True` implies `U32.is_eq(i, j) == False` (`v3c_ne_idx_sound`, T33); **A.87 landed the structural half of completeness**: the three `ne_idx` node-recursion cases (`v3c_ne_idx_sep`/`_same_l`/`_same_r`) and the unconditional `add ∘ sub` roundtrip (`v3c_add_sub`), with T34/T35 witnessing exactness on canonical 8- and 16-leaf trees. **A.89 finished completeness**: `v3c_ne_idx_complete` + `v3c_ne_idx_exact` prove `ne_idx(full k, two k, i, j) == Bool.not(U32.is_eq(i, j))` for in-range `i, j`, landing the three arithmetic bricks (`is_lt` base reflection, `sub` range preservation, canonical size halves) and the depth induction; T36/T40–T42. **A.90 closed the engine wire**: `v3cw_commit_fold`/`v3cw_commit_commutes` bridge `Rules.commit_sets` to `v3c_fold` on the projected write list (distinctness keyed by `Commit.v3c_pair_ne`), so the region-split equality reaches the engine's actual write set; caveat: `v3cw_lin` is the multiplicity-erased copy needed because `commit_sets` is linear (an alternative is making `commit_sets` take a reusable list, at a possible hot-path refcount cost) |
| `G4` | accepted | GPU (`!`) paths are unvalidated — no CUDA on the dev machine | accepted | M7b M7e | run on a CUDA host; keep `!` usage semantically correct |
| `G5` | standing | laws constrain models (`Word` `List` `Nat` `PT`), not the imperative `Array` engine | open | all Array claims | per-claim refinement; `G1` closed for `Array.swap.go`, write→Φ effects proven (A.28–A.29); the write-site enumeration instances `G10`/`G14` are now closed (A.48, A.53–A.56, A.79 — the last by typing the effect in `Rules.Write`), so what remains was the selector/read threading from `Rules.plan`/`Support.sup` to their `PT` mirrors. **A.83 closed the read half** for the support selector machine (`src/g5.bend`: `g5_read_get_go`/`g5_read_get`/`g5_size_pack`/`g5_tget_swap` — every live `sup_m` read is the engine's `Array.get(world, i)` at the same index, and the post-write read-back is the written value). **A.86 closed the mask residual**: `g5_twidth_pow`, `g5_and_mask_id` and `g5_read_get_bare` prove the bare-index read (`snd(Array.get(U32, pack t, i)) == tget(t, g5_twidth t, i)` for in-range `i`), so the read threading is closed modulo the `SupSel` branch-table transcription (a methodological residual — `sup_m` is the mirror, so it cannot be proved against itself). Non-gating observation: `Refine.pack`/`Array.size`/`Array.get` fail-stop at runtime on non-perfect packed trees; the engine only packs full power-of-two worlds, so the laws are unaffected |
| `G6` | accepted | support (rule 7) is test-witnessed only | accepted | — | a support-recompute law |
| `G7` | review | six laws are `{==}` reflexivity proofs and could admit a weakened statement | review | — | human review of each statement (§3.3) |
| `G8` | accepted | array laws must be stated over the `PT` presentation; an arbitrary `Array` variable cannot be named twice (linearity forbids the copy) | accepted | all Array claims | a language feature for non-linear array quantification; semantically closed, since every array is `pack(unpack(a))` |
| `G9` | accepted | non-rock `crush_word` potential preservation (`material(w) != 3`) — Bend cannot case-split the opaque `U32` in `Cell.density`/`crush_material`, so the identity is not a theorem | closed | G2 G10 | closed (A.38–A.40): `Word.cmp` reflection (A.38) makes the guard provable; the engine guards both crush sites with `Ops.crush_if_rock` (A.39); `array_guarded_crush_lowers_phi` (A.40) proves the guarded write's Φ effect at every index — rock: `crush_gap`, non-rock: identity — with no `material(w) == 3` hypothesis. Runtime-witnessed by T19 |
| `G10` | accepted | the tick's write-*site* enumeration over `Support.sup`/`Rules.step` was by inspection, not mirrored; each write primitive's effect is proven. Subject `Rules.step` **retired by A.63**; the live `Rules.plan` enumeration is `G14` | closed | G2 G9 | **closed (A.48, A.53–A.56):** both state machines are mirrored on `PT`. `Support.sup` (A.48): `sup_m`/`sup_m_preserves` with a datatype selector (`SupSel`), an abstract wake fuel, and law `sup_mirror_preserves_phi`. `Rules.step` (A.56): `src/step.bend`'s `step_m` mirrors the full selector machine (`StepSel`, abstract wake fuel) and carries a pair invariant `Φ(current) + da == Φ(start) + db`; every write composes its exact leaf balance via `pt_write_balance`, wakes fold through `sr_phi_cong`, `step_preserves` is the all-fuel theorem, and law `step_mirror_balance` closes over `step_pass_m` (the `Sim.phase` entry point). Unconditional, so no fall-regime or `can` hypothesis is needed; the earlier `G9` resolution (A.38–A.40) covers both crush sites. The selector/read threading of the mirror is by inspection (the `G5` caveat) |
| `G11` | unproven | the `Rules.step` movement (sel 6/12) lowers Φ by the drop; the two `array_swap_decreases` balances do not telescope | closed | G10 M8d | **closed (A.53):** a `leaf_base(t,base,n,i)` function gives the leaf index `chg_m` actually uses, so `nfst`/`nsnd(chg_m)` project onto `pot_at(tget(..), leaf_base(..))` — definitional at `PL`, where A.52's `base+i` form was false. `swap_balance` then gives one write's `new − old` at that leaf, and the two balances telescope into the unconditional cross law `array_mov_cross` (the residuals `p+q` and `r+s` are the pre/post potentials of the two leaves). `fall_gap := mov_S − mov_T` and `array_mov_lowers_phi` give the decrease under the fall-regime hypothesis `mov_T + fall_gap == mov_S`; the regime is now a single order Bool with the Nat order lemma proven (A.54: `n_add_sub_le`, law `array_mov_lowers_phi_regime`); reflecting the engine's `can` guard to it is the remaining `G10` `step_m` work |
| `G12` | unproven | wake is applied at the end of each *phase*, not accumulated for the next tick (rule 9); a later phase of the same tick can evaluate a cell an earlier phase woke | closed | — | **closed (A.71, V0-4a):** the tick threads each phase's pending wakes and applies the accumulated list once at tick end (`Rules.phase_plan_w` returns `(written world, wakes)`, `Sim.tick_active`/`phases` fold the wakes and `Rules.commit_wakes` applies them). T33 witnesses it: a cell woken by phase 0's drop but of a later colour stays put this tick and is active afterwards, while the control (same cell active at tick start) falls in the same tick. A.63 had fixed only the same-phase case (T24). The evaluated set is exact only after `V0-4b-1` (A.72) cleared the move's active bit (T34). The support pass's wake was the last same-tick instance and is now deferred too (`G16` closed, A.74) |
| `G13` | accepted | V0-1's contention tie-break over-forfeits: a diagonal mover yields to an opposite-axis `capable` neighbour even when that neighbour is not actually claiming the shared target (it may drop, or slide another way) | accepted | count | V0-3b proves the collision class is exactly the opposite-diagonal parity class, so the tie-break is *sufficient* but still over-forfeits within that class (it does not recompute the neighbour's chosen target); behaviour-only, no safety consequence |
| `G14` | unproven | V0-1's `Rules.plan` write-*site* enumeration is by inspection, not mirrored | **closed** | G5 | **closed (A.79, `V3d-2`):** the effect was pushed into the type — `Rules.Write`'s `WSet` now carries `op: Rules.Op`, a **closed** `Data` datatype (`OId`, `OSupport`, `OFall0`, `OMov`, `OAct`, `ODeact`, `OCrushIfRock`), and `Rules.apply_op` is total. `plan` therefore cannot emit an unclassified write: the enumeration is a typing fact, not an inspection. Each effect has a law: `write_effect_phi_balance`/`_count_balance` are total over `Op` (the exact balance is general in the written value, `Refine.array_swap_decreases`), and the *decrease* is refined per shape — `write_selector_preserves_phi` for the material-preserving self-writes (including `set_fall0` and `deactivate`, which had no array-level Φ law at all), `array_guarded_crush_lowers_phi` for the crush, `Fall.array_mov_cross`/`array_mov_lowers_phi` for the two-cell movement. **Two residuals are explicitly routed, not left here:** (i) movement is not a point write — its two halves must be *paired* and its decrease needs the fall regime, which is the `G3`/`G11` composition residual (V3c-1b), not an enumeration gap; (ii) that the carried `src` word is the pre-phase word is `R1`/`C1`'s existing by-construction claim. |
| `G15` | accepted | `Ops.wake` still marks wrapped neighbours from a boundary cell (the opposite face) when the shell is painted away; no material moves, so `C2` holds, but activity leaks across the box | **closed** | — | **closed (A.88):** `Ops.wake` is bounded by `Grid.step_inside` (a wrapped step is inert), the `PT` wake mirror carries the same guard, and law `g15_wake_step_inert` states it; T43–T45 + sim T44–T46 |
| `G16` | unproven | the support pass still applies wake within the pass (`Support.sup` case 6 wakes after a crush), so a cell it wakes is evaluated by the same tick's phases — the rule-9 residual after `V0-4a` | closed | — | **closed (A.74, V0-4b-2):** a crush accumulates the crushed cell into a pending wake list; `Sim.tick` applies the support and phase wakes together at tick end (`Support.pass_gated` returns `(world, wakes, todo)`, `Rules.wake_writes` converts them). T36 witnesses it: an active rock with an empty below is crushed and its neighbour stays put this tick, active afterwards. `sup_m` updated to the crush-only shape (deferred wakes are Φ-neutral) |
| `G17` | unproven | a move wrote the target with the mover's active bit set (`Rules.mov`, and the slide write of `w`), so a later colour phase re-evaluated the mover in the same tick — the evaluated set was not fixed and a grain could fall more than one cell per tick | closed | — | **closed (A.72, V0-4b-1):** `Rules.mov` and the slide write now clear the active bit (`Cell.deactivate`); the move's already-emitted `WWake` re-activates the target at tick end (V0-4a). T34 witnesses one cell per tick. `mov_preserves_pot`/`nempty_mov` proof terms updated (material is unchanged, so the laws still hold) |
| `G-scale-1` | unproven | `Grid.step_inside` conflates "off the window" with "off the world" | open | S1 | a moving window needs a margin/load rule so a rule target just outside the resident set is not silently inert; closes by a window-margin invariant plus a test/law that every `Rules.plan` target of a resident cell is resident or loaded (`SCALE.md` §6) |
| `G-scale-2` | unproven | `Dirty.Mask` is exactly 64 `y` rows | open | S1 | a window needs a window-sized mask or per-chunk dirty set; closes by a size-parameterised mask plus the `mark_wake` reach invariant |
| `G-scale-3` | unproven | the `cw` split/rejoin identity `(x>>4)<<4 + (x&15) == x` is test-witnessed (T57–T60), not proven | closed | S1 | **closed (A.94, `gscale`):** `src/gscale.bend` proves it in `Bits`/`Word` — `gscale_global_rt` (`(w>>4)<<4 + (w&15) == w & 16383`, the in-range identity via `G5.g5_and_mask_id`), the disjoint-field `add == or` brick `gscale_add_and_or`, and the `model_index_rt`-style key/local roundtrips `gscale_kmodel_rt`/`gscale_lmodel_rt`; laws `gscale_cw_{x,y,z,key,local}_rt`; T66–T70 |
| `G-scale-4` | unproven | the resident set is implicit in `assemble_go`'s loop bounds | open (partial) | S1 | a window needs an explicit set plus a load/evict policy. **A.96 groundwork (`gscale2`):** `src/winset.bend` is a pure finite-set model (`winset_mem`/`insert`/`remove`/`all`, `winset_evict`, `winset_gen_cell`) with laws `winset_mem_insert_self`/`_other`/`winset_remove_insert`; T73–T75. Still open: the `assemble`/`evict` roundtrip law (`assemble(evict(s)) == assemble(s)` for a regenerable chunk) needs an `Array` update-identity under the `G5` boundary, and general membership-after-remove needs a proof-relevant `is_eq` eliminator (the `Bool.pick` non-dependence blocker) |
| `G-scale-5` | performance | the phase fold's cost scales with the active set, not the window | open | S1 | gates the scale target; closes by measurement on a real window, not a proof |
| `G-scale-6` | retirement | every law mentioning `Grid.index`/`Grid.ix` is a torus law; migrating the live path orphans them | open | S1 | follow the `AGENTS.md` retirement protocol (keep, mark retired, update §4.1); never delete or silently weaken |
| `G-scale-7` | unproven | the canonical window map is a relabelling of `Grid.index` (`win_index(canonical,x,y,z) == Grid.index(x,y,z)`) is test-witnessed (T81), not proven | open | S1 step 3 | a `U32.sub(x,0) == x` / mask-drop development over `Bits`/`Word` (reusing `G5.g5_and_mask_id` and the `gscale` field lemmas); closes by a law `win_canonical_index` |
| `G-scale-8` | unproven | `Worldgen.gen` paints bedrock on the **absolute** planes `x/y/z ∈ {0,63}`, so in a moving window the stray wall is carried inside the resident set and there is no shell at the window's own edge — an absolute world edge cannot coexist with a moving window (or an infinite render horizon) | open | S1, Bendview M3/M4 | separate terrain from the box: `Worldgen.gen_terrain` is already shell-free, so make the *box* contribute the shell (window-local `0`/`63`), with the canonical window reproducing today's `gen` bit-for-bit so the fixed-box laws/worlds stand; expose one shell-free sampler + a border predicate the renderer can use for non-resident cells. Deciding also implies a `coreidea.md` rule-11 note (worldgen is window-relative, shell included) and a `PLAN.md` §4.1 update. Reported by Bendview (`../Bendview/docs/engine-report-gen-shell-and-window.md`) |
| `G-bridge-1` | unproven | the sidecar's credit window and delta coalescing are specified (`SERVE.md` §5–§6) | open (partial) | B1 residual | **A.96 (`bridge3`) landed the accounting:** bounded queue, credit window (no overrun/wrap), drop-and-keyframe coalescing, idle PING, and a forked `Chan` reader so control is read continuously; T76–T80, plus a manual pipe run (4 credit frames → 4 credited frames). **Still open:** (1) the engine and writer are still co-resident in one IO thread — Base has no non-blocking `Chan.try_recv`/`try_send`, so a slow renderer can still stall the engine at the stdout write (the §5 failure mode); closes by a Base try-chan or the in-process C FFI; (2) `bridge3_reader` decodes only the first frame per `read`, so partial/batched frames mis-parse — needs a header-keyed byte accumulator; (3) no `stall_ms`/`ping_ms` flags |
| `G-bridge-2` | unproven (defect) | `runners/export.bend`'s dense `.bvs` record encoder sliced the flat `Grid.index` array every 4096 words, so each record was a `y`-plane (`gi/4096 = y`), not a 16³ chunk, while labelled with a `Chunk.key` — 130835/262144 cells misplaced and inconsistent with the (correct) sparse body | closed | B1 / Bendview M5 | **closed (A.97):** the record gather is now `bxe_cell_index`/`bxe_chunk_cells` (`Grid.index(Chunk.global_x/y/z(k,i))`, the `Store.chunk_list` order), shared by `export.bend`'s dense path and `serve.bend`'s sparse path; T47 proves the two bodies byte-identical for a full store (native), T83 pins the mapping (fast). The old size-only T63 could not see placement. Reported by Bendview (`../Bendview/docs/engine-report-bvs-snapshot-framing.md`) |
| `G-bridge-3` | unproven (defect) | the A.97 record gather fixed the *address* but emitted cells in reverse `Chunk.local` order (offset `i` = local `4095-i`), so the documented port rule still did not describe the bytes; T47 (dense == sparse) could not see it (both encoders shared the order) and T83 pinned only the address | closed | B1 / Bendview M5 | **closed (A.98):** the gather walk is now descending so the head is local 0 (`bxe_chunk_cells_go`); T84 compares the gathered chunk element-by-element to `Store.chunk_list` (the ground truth `assemble_chunk` expects), which fails under either the address *or* the order defect. Follow-up to `G-bridge-2` (Bendview report §10) |

### 5.4 Deferred — publishing a proven slice to BendHub

Not done; revisit when the engine is more complete. BendHub
(`https://hub.bend-lang.com`) is a content-addressed store: a package is a
directory named by the hash of its contents, with **no names, versions or
accounts**, and `bend <file.bend> --publish` uploads one file plus everything it
imports, printing the `import 0x…/….bend as X` line to paste elsewhere. It
**refuses to publish an open law or a TODO** — the same rule as our gate, which
is why the gate must stay green for any candidate slice.

Consequences, recorded now so the decision is cheap later:

- A publish must be a **standalone proven slice** (only the modules it
transitively imports), never this repository: `G3`, `G5` and `G7` are open, and
  a hash is permanent — a published claim cannot be corrected in place, only
  superseded by a new hash.
- `G7` (six `{==}` laws that could admit a weakened statement) should be closed
  **first**: a permanent hash publishes the *statement*, not just the proof.
- Adopt the ecosystem's `seal.bend` convention (a three-line file importing
  `PROOF.bend`), so laws and proofs cannot travel apart.
- Candidate first uploads, in order of self-containedness and general value
  (A.60 survey of the hub): the `U32`/word bit-lemma library (`src/bits.bend`,
  `src/mod.bend`, `src/parity.bend` — the hub has **zero** laws on
  `U32.and/or/xor/shl/shr`); then `src/list.bend` with the count-fold
  completeness lemmas; then the Φ/potential telescope (`src/fall.bend`,
  `src/potential.bend`) and the conservation laws, which have no public
  counterpart.

---

## 6. File layout and responsibilities

| Path | Responsibility |
|---|---|
| `PLAN.md` | this file — normative design, state, gap registry |
| `coreidea.md` | the 11 immutable rules and the ambition |
| `AGENTS.md` | workflow: gate, tests, commits, tooling |
| `HISTORY.md` | milestone log; bodies immutable, corrections via a superseded-by pointer (old Appendix A) |
| `LAWS.bend` | law claims (strictly append-only; never change a law's meaning) |
| `PROOF.bend` | proofs of every law — the gate |
| `main.bend` | entry; delegates to the current runner |
| `src/cell.bend` | word encode/decode, material table, field accessors |
| `src/grid.bend` | flat↔3D index math, neighbor lookup, Array helpers |
| `src/worldgen.bend` | pure `gen(x, y, z, seed)`, noise, terrain, `build`/`build_at` |
| `src/rules.bend` | falling rule, swap, tie-break, impact |
| `src/support.bend` | support pass and crumble |
| `src/ops.bend` | shared world operations (writes, neighbor marking) |
| `src/sim.bend` | tick pipeline (passes + 8 phase folds) |
| `src/bits.bend` | Word/Nat bit lemmas and index/cell models |
| `src/nat.bend` | `Nat` arithmetic lemmas |
| `src/list.bend` | `List.append`/`reverse`/`length` lemmas (Base ships none); imported from BendHub `0x085d89db…` |
| `src/potential.bend` | Φ evaluation kernel |
| `src/settle.bend` | settling lemmas (`suml`, `app`, `List.set` splits) |
| `src/refine.bend` | array↔model refinement: `PT` model, pack/unpack, `Array.swap.go` correspondence, Φ decrease |
| `src/writepot.bend` | write→Φ bridge: `Cell.encode` material field, write effects on `pot_at`, point-write composition |
| `src/tick.bend` | array-level (`Array.swap.go` via `PT`) write effects: `tget`, support-write preservation, rock-crumble decrease |
| `src/count.bend` | rule 2 conservation: non-empty indicator, material-preserving write effects, array-level count preservation, point-write balance, and the two-write movement swap |
| `src/parity.bend` | rule 4/1: parity model, neighbor parity |
| `src/mod.bend` | rule 1: modular-add independence, ∓1 cancel |
| `src/priority.bend` | rule 1/3: `Dir` model, φ cancellation, neighbor cancel |
| `src/order.bend` | rule 3: total scan order |
| `src/chunk.bend` | chunk key/index, pure per-chunk gen |
| `src/store.bend` | `U32`-keyed radix-tree chunk store, assemble (gen fallback on evicted chunks), eviction |
| `runners/ascii.bend` | fueled ASCII runner |
| `runners/window.bend` | `App.run` windowed runner |
| `runners/view3d.bend` | `App.run` 3D voxel viewer (presentation) |
| `view/voxel.bend` | pure DDA raycaster + camera (presentation, no IO) |
| `test/tests.bend` | fast golden tests (tick-free) |
| `test/simtests.bend` | simulation golden tests (native-recommended) |
| `scenarios/fixtures.bend` | shared setup fixtures (`spawn`, `pull`) |
| `.pi/extensions/bendverse/` | project tooling (§3.6) |

All of `src/` is pure (zero IO). Runners are thin shells.

---

## 7. Bend guardrails (these WILL bite)

- Fuel every loop with `Nat`; shrinking parameter FIRST. No `@unsafe`, no mutual
  recursion.
- No `if`; match only variables; no `let` before a `match` on a parameter.
- Annotate literals. `==` is a type; runtime equality is `U32.is_eq`. XOR `.^.`;
  shifts take `Nat` amounts.
- `Array` is linear: rebind every write, never alias, powers-of-two sizes.
- Imports are relative to the importing file; absolute paths work.
- `?name` prints a goal — use it; `?TODO` leaves a hole — never commit one.
- `--checkup` is unsound for this layout (`LAWS.bend` alone is all TODOs). Gate
  with `bend PROOF.bend`.
- New bit facts: search `bend_lemmas` before proving; `bits.bend` and
  `parity.bend` are deep.
- When unsure of a Base name: `bend_api` / `bend base <Name>`. Do not guess.
- **Never state a lemma whose type applies a wrapper to a *concrete* fuel** —
  e.g. `wake_m(i, t, n)` = `wake_z_m(3, 0, i, t, n)`. The checker normalises the
  whole unrolled loop (3·3·3 swaps) and compilation hangs for minutes (A.41).
  State the lemma over the abstract-fuel function (`wake_z_m_preserves`) and
  instantiate the concrete fuel only *inside* a proof, where the equality is a
  single definitional unfold.
- **Beware reducible terms nested in a proposition (A.42).** A type that embeds a
  write like `swap_m(t, n, i, set_support(…))` inside `pack`→`to_pots`→`suml`
  makes the checker unfold `set_support`/`Cell.encode` into a large bit term,
  twice, and it can run for minutes. Prefer to keep such values as *parameters*
  (opaque, stuck) rather than inlined; mirror opaque `U32` selectors with a
  datatype (`SupSel`) so `match` reduces structurally.
- **Timeouts kill the whole process group.** The upstream `bend` launcher spawns
  `bun` as a child (no `exec`), so killing the launcher orphans `bun` at 100 % CPU.
  The pi tools run `env BEND_NO_TELEMETRY=1 timeout --kill-after=5 <secs> bend …`
  (A.43); if a compile ever takes more than ~4× the usual time, stop and bisect
  the touched file with `head -n` rather than letting the gate run.
- **Guard the checker itself with canaries** (§3.7, `bend_canary`):
  `tools/checker-canary.sh` asserts positive reductions still reduce and negative
  controls are still rejected. Add a canary for any new surprising interaction.

---

## 8. Open risks / spikes

- **Refinement (`G5`, `G8`).** The single load-bearing risk: proofs about models
  are not proofs about the engine. `G1` (`Array.swap.go`) is now proven as explicit
  refinement lemmas (A.27) and the write→Φ effects are proven (A.28); `G8` records
  the linearity limit on how an array may be named in a statement. The remaining
  instances are `G9` (non-rock crush) and `G10` (write-site enumeration); `G2` is closed.
  **`G10` is now known to depend on `G9`** (A.36): its crush sites apply
  `crush_word` to a non-provably-rock target, so mirroring the control flow alone
  cannot close it. Mitigation throughout: explicit refinement lemmas, never assumptions.
  `G9` is resolved (A.38–A.40); `G10`'s write primitives are all proven (A.39–A.41).
- **`G10` mirror: selector representation + the concrete-fuel cliff (A.42, A.45).**
  Two obstacles, both isolated and resolved. (1) A literal mirror of
  `Support.sup` matches on `sel: U32`; in a proof `sel` is abstract so `match sel`
  never reduces — fix: a datatype selector (`SupSel`), after which the mirror
  typechecks in 3 s. (2) The Φ theorem hit a normalisation cliff (>120 s at
  100 % CPU). **A.45 corrects A.42's attribution** (A.42 was contaminated by the
  leaked compile): the trigger is not the `set_support` writes but **S6's
  concrete wake fuel** — `wake_z_m(U32.to_nat(3), …)`. Minimal repro: a
  proposition containing `pack(wake_z_m(U32.to_nat(3), …))` hangs (>30 s), while
  changing *only* `U32.to_nat(3)` to an abstract `+wf: Nat` checks in 4 s. With
  concrete fuel the checker unrolls the 3·3·3 wake loop and then case-splits the
  abstract tree through `pack`/`to_pots` at every `swap_m`/`tget`. **Fix
  (verified):** thread the wake fuel as an abstract `Nat` parameter through
  `sup_m`/`sup_m_preserves` and instantiate it at `3` only at the top-level
  engine binding; the full proof then checks in 5 s for all fuels. General rule:
  never put a concrete-fuel loop application in a type (§3.7, §7).
- **Schedule invariance (`G3`).** Off the critical path: post-`V0-1` the phase
  is pure, so the residual is write-set commutativity (`V3c-1` banked). It gates
  only the optional `M7d`; `C3` does not depend on it.
- **Cost (`C3`/`V0-4b-3b`).** **Closed (A.77).** The tick carries a dirty-row
  mask and scans only the rows a wake reached, so the `any_active` and
  `active_list` world scans are gone: a settled tick is ~1.3 µs (was ~89 µs).
  A.76's two designs are recorded in `HISTORY.md`: the active-cell list needs a
  sort this Base lacks, and the 16³ chunk mask was abandoned for *correctness*
  (its chunk-major order lags the support pass's bottom-up `below` propagation).
  The wake's 3-row reach is arithmetic, not a recursive 27-neighbour walk, to
  keep the checker's stack bounded.
- **Law proof difficulty.** Bit-level inductions can stall — the downgrade
  protocol (§3.4) exists for this.
- **No CUDA (`G4`).** GPU work degrades to CPU-parallel validation; keep `!`
  usage correct anyway.
- **Parallel array reads.** Linear ownership prevents sharing one `Array` across
  split regions; clone-per-region is the fallback, semantics-preservation is the
  hard part.
