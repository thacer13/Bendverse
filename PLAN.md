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
| `HISTORY.md` | append-only AI milestone log (old Appendix A) | historical record |

**How work happens.** Implement what this file specifies. Land it only when the
gate is green (`bend PROOF.bend` → `All terms check.`), both test suites pass,
and a `HISTORY.md` entry is appended. Details and autonomy rules in `AGENTS.md`.

**Tooling.** A project-local pi extension (`.pi/extensions/bendverse/`) provides
the loop: `bend_gate`, `bend_test`, `bend_run`, `bend_api`, `bend_lemmas`,
`bend_goal`, `bend_spike`, `bend_plan`, `bend_status`, `bend_audit`.

---

## 0. Verified platform facts (do not re-derive)

Bend 2.0.5. Learned the hard way; re-checking these costs more than reading them.

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
  its 53 laws as TODOs. Use `bend PROOF.bend`, never `--checkup`, for the gate.
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

- `app/ascii.bend` (root `main.bend` delegates to it): build world, print the
  x–y cross-section at z = 32 (y top-down so up is up), run N ticks (`Nat` fuel,
  N = 20), print again. Chars: `.` Empty, `#` Bedrock, `s` Sand, `R` Rock,
  `r` Rubble.
- `app/window.bend`: `App.run` windowed app; state = world + running flag; view
  renders the x–y cross-section at z = 32 as a 64×64 quadtree `Image`; tick
  handles left/right mouse paint (Sand/Rock) at `(mx, 63 - my, 32)`, `e` to
  erase, space to pause, close to quit. Paints set activity on 26 neighbors.
- `app/tests.bend`, `app/simtests.bend`: golden tests, see §3.5.

### 2.12 Determinism contract

Given the same initial `Array<U32>` and constants, every run (JS, native,
threaded, GPU) produces identical results. Witnessed by T1. This is the
acceptance bar for any parallel or GPU work.

---

## 3. Verification architecture

### 3.1 The gate

`bend PROOF.bend` must print `All terms check.` before every commit. It checks
`LAWS.bend` (the claims), `PROOF.bend` (the proofs), and every imported `src`
module against the current definitions. An undischarged law is a TODO, so a
missing proof makes the gate red. Changing `src/` can break proofs — that is the
point, not an accident.

Tests are separate and complementary: `bend app/tests.bend` (JS, tick-free) and
native `bend app/simtests.bend -o bin && ./bin`.

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

53 laws, every one discharged. Six are reflexivity proofs (`{==}`, both sides
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

### 3.5 Golden tests (runtime witnesses)

Fast, tick-free (`app/tests.bend`): T5 index/cell roundtrips; bit-31 and
mul-wrap spikes; T6 gen determinism; T7 terrain structure; T8 build = gen over
all cells; T10 parity/neighbor-x; T11 low6 add + ∓1 cancel; T12 dir φ
cancellation; T13 neighbor index cancellation; T14 scan-order totality; T15
`List.set` split + sum; T16 chunk key/local roundtrip + gen; T17 chunk store
set/get/overwrite; T18 store assemble = worldgen; T19 write→Φ bridge (support/active writes preserve pot, rock crumble lowers it, non-rock crush is the identity — `G9`); T20 chunk sleeping/eviction (empty store regenerates worldgen, all-gen store evicts to worldgen, one-resident eviction preserves the world, predicates); T21 conservation witness (non-empty indicator preserved by every material-preserving write; rock crush 3→4).

Simulation, native-recommended (`app/simtests.bend`): T1 tick determinism over
10 ticks; T2 conservation of the non-Empty count; T3 Bedrock static; T4 activity
settles and far cells are untouched; T4b a settled world is a fixed point; T9
pull-base collapses rock; T18 chunk-store tick equivalence; T20 evict → assemble
→ tick equivalence.

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
| `R1` | Locality: neighbor-only reads, bounded radius | `dir_phi_cancel` `neighbor_cancel` `low6_add_independent` `parity_flip_succ` `parity_flip_pred` | T11 T12 T13 T14 | parity mod priority order |
| `R2` | Conservation: swap/transform only | `array_point_write_preserves_count` `array_point_write_count_balance` `array_mov_swap_preserves_count` `array_support_write_preserves_count` `array_fall_write_preserves_count` `array_mov_write_preserves_count` `array_wake_write_preserves_count` `array_deactivate_write_preserves_count` | T2 T21 | count rules ops |
| `R3` | Single-writer, deterministic tie-break | `scan_order_total` `neighbor_cancel` | T14 | order priority |
| `R4` | Phase separation: no same-color neighbors | `neighbor_x_parity` `neighbor_y_parity` `neighbor_z_parity` `parity_flip_succ` `parity_flip_pred` | T10 | parity sim |
| `R5` | Falling is universal (density rule) | `fall_decreases` `fall_lowers_potential` `sand_sinks_in_water` | T9 | rules potential |
| `R6` | Cohesion = rigidity, not material type | `crumble_decreases` `crumble_lowers_potential` `crumble_lowers_pot` `guarded_crush_lowers_pot` `array_crumble_lowers_phi` `array_guarded_crush_lowers_phi` `rock_crumbles_lighter` | T9 T19 | support potential writepot tick |
| `R7` | Support recomputed, never cached | — | T9 | support |
| `R8` | Impact is a threshold event | `rock_crumbles_lighter` `sand_sinks_in_water` | T9 | rules |
| `R9` | Activity is explicit and always settles | `budget_exhausts` `potential_additive` `strict_events_bounded` `settling_budget` `fall_lowers_potential` `crumble_lowers_potential` `swap_refines_array` `array_swap_pots` `swap_lowers_phi` `support_write_preserves_pot` `fall_write_preserves_pot` `mov_preserves_pot` `wake_preserves_pot` `deactivate_preserves_pot` `point_write_lowers` `array_support_write_preserves_phi` `array_activate_write_preserves_phi` | T4 T4b T19 | sim potential settle refine writepot tick |
| `R10` | Determinism under any schedule | — (by construction) | T1 | sim |
| `R11` | Worldgen is a pure seeding function | — (purity by construction) | T6 T7 T8 T16 T18 | worldgen chunk store |
| `R0` | Encoding and arithmetic substrate | `sanity` `grid_volume` `cell_full_mask` `cell_reserved_bits` `index_roundtrip` `cell_roundtrip` `material_encode` `word_cmp_eq_reflect` `u32_cmp_eq_reflect` | T5 spike bit31 spike mul wrap | bits grid cell nat word |

Reading the `—` rows: R7 is test-witnessed only (recorded as `G6`); R2 now has
the `V4` count laws (A.31–A.32, A.34).
R10 and R11 hold by construction and are witnessed by tests.

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

Dropped by measurement (not by budget): `M7c` parallel render (A.19).

### 5.2 Open work (dependency-ordered)

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
- [ ] **V3c** Schedule invariance: a region-split fold equals the sequential
  fold. Large and stall-prone; the fallback is V3a+V3b proven with `G3` kept open.
- [x] **M8d** Chunk sleeping/eviction — landed (A.30): `assemble` regenerates
  missing chunks from pure gen, so the store is a sparse overlay; `Store.evict`
  drops sleeping chunks that are bit-equal to gen (a checkable, conservative
  regenerability test), and eviction is lossless. Test-witnessed (T20); widening
  eviction to all sleeping chunks needs the sleep-invariance proof (`G10`).
- [ ] **M7d** Parallel phase folds (CPU) — gated on V3c.
- [ ] **M7b** / **M7e** GPU worldgen / phases — blocked on a CUDA host (`G4`).
- [x] **V4 (conservation)** — landed (A.31–A.32, A.34): every material-preserving
  write preserves the count, `array_point_write_count_balance` gives the exact
  displacement identity, and `array_mov_swap_preserves_count` proves the
  **movement swap** (the two writes telescope). Rule 2 is fully law-covered.
- [ ] **G9/G10 unlock (option-2 route)** — the current verification frontier.
  1. [x] `Word.cmp` reflection proven (A.38): `word_cmp_eq_reflect` (general `n`,
     not just `32n`) and `u32_cmp_eq_reflect` in `src/word.bend`, so
     material-guarded engine logic is now provable.
  2. [x] Guard the crush sites to rock (`Rules.step` sel 22, `Support.sup` sel 6)
     via `Ops.crush_if_rock` (A.39), with the point-level law
     `guarded_crush_lowers_pot`; behaviour-validated by A.37 (non-rock
     field-reset is not load-bearing).
  3. [~] Mirror `Support.sup`/`Rules.step` on `PT` for `G10`. The crush-site
     write primitive is done (A.40): `array_guarded_crush_lowers_phi` gives the
     guarded write's Φ effect at every index (rock gap, or identity), so both
     crush sites are covered without a `G9` hypothesis. The `wake`/activate
     infrastructure is done (A.41): `array_activate_write_preserves_phi` and the
     `wake_*_m` mirrors. The `sup_m` mirror (with a `SupSel` datatype selector)
     typechecks; its Φ theorem is blocked on a Bend2 normalisation cliff (A.42,
     §8) — the support-write branches blow up. Next: the `sup_step` opacity
     mitigation.
  See `HISTORY.md` A.36–A.42 for the analysis and probes.

Suggested order: `V3c → M7d → (M7b/M7e on CUDA)`; `M8a–M8d` have landed.
M7 and V2b are independent; V2b may proceed first if the GPU path stalls.
Dropping M7/M8 costs nothing above the scale track; dropping V2 costs the
settling guarantee.

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
| `G3` | unproven | schedule invariance: region-split fold = sequential fold (V3c) | open | M7d | builds on V3a+V3b (proven) |
| `G4` | accepted | GPU (`!`) paths are unvalidated — no CUDA on the dev machine | accepted | M7b M7e | run on a CUDA host; keep `!` usage semantically correct |
| `G5` | standing | laws constrain models (`Word` `List` `Nat` `PT`), not the imperative `Array` engine | open | all Array claims | per-claim refinement; `G1` closed for `Array.swap.go`, write→Φ effects proven (A.28–A.29); remaining instance is the write-site enumeration (`G10`) |
| `G6` | accepted | support (rule 7) is test-witnessed only | accepted | — | a support-recompute law |
| `G7` | review | six laws are `{==}` reflexivity proofs and could admit a weakened statement | review | — | human review of each statement (§3.3) |
| `G8` | accepted | array laws must be stated over the `PT` presentation; an arbitrary `Array` variable cannot be named twice (linearity forbids the copy) | accepted | all Array claims | a language feature for non-linear array quantification; semantically closed, since every array is `pack(unpack(a))` |
| `G9` | accepted | non-rock `crush_word` potential preservation (`material(w) != 3`) — Bend cannot case-split the opaque `U32` in `Cell.density`/`crush_material`, so the identity is not a theorem | closed | G2 G10 | closed (A.38–A.40): `Word.cmp` reflection (A.38) makes the guard provable; the engine guards both crush sites with `Ops.crush_if_rock` (A.39); `array_guarded_crush_lowers_phi` (A.40) proves the guarded write's Φ effect at every index — rock: `crush_gap`, non-rock: identity — with no `material(w) == 3` hypothesis. Runtime-witnessed by T19 |
| `G10` | accepted | the tick's write-*site* enumeration over `Support.sup`/`Rules.step` is by inspection, not mirrored; each write primitive's effect is proven | accepted | G2 G9 | mirror both state machines on `PT` (large, mechanical). **`G9` is resolved** (A.38–A.40): the guarded-crush write site now has an unconditional Φ theorem (`array_guarded_crush_lowers_phi`), so no crush site carries an unproven hypothesis. Remaining: the fuel-loop mirror that composes the proven write primitives (support/fall/activate/swap/guarded-crush) along `Support.sup`/`Rules.step` control flow. Would also widen `M8d` eviction |

---

## 6. File layout and responsibilities

| Path | Responsibility |
|---|---|
| `PLAN.md` | this file — normative design, state, gap registry |
| `coreidea.md` | the 11 immutable rules and the ambition |
| `AGENTS.md` | workflow: gate, tests, commits, tooling |
| `HISTORY.md` | append-only milestone log (old Appendix A) |
| `LAWS.bend` | law claims (append-only; never change a law's meaning) |
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
| `app/ascii.bend` | fueled ASCII runner |
| `app/window.bend` | `App.run` windowed runner |
| `app/tests.bend` | fast golden tests (tick-free) |
| `app/simtests.bend` | simulation golden tests (native-recommended) |
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
- **`G10` mirror: selector representation + a checker performance cliff (A.42).**
  Two obstacles, both isolated. (1) A literal mirror of `Support.sup` matches on
  `sel: U32`; in a proof `sel` is abstract so `match sel` never reduces — the fix
  is a datatype selector (`SupSel`), after which the mirror typechecks in 3 s.
  (2) The Φ theorem still hits a normalisation cliff (>120 s at 100 % CPU): the
  `set_support` write unfolds via `Cell.encode` into a large bit term nested in
  `swap_m`→`pack`→`to_pots`, and `sup_m` appears twice in the statement. Each
  piece typechecks alone in ≤3 s. Likely a Bend2 normaliser/sharing limit rather
  than a wrong answer. Mitigation under test: pass the write value through a
  `sup_step` helper so the huge term is an opaque argument; if that fails, `G10`
  is tooling-blocked, not conceptually open.
- **Schedule invariance (`G3`).** A region-split fold may differ from the
  sequential fold in tie-break corners. Mitigation: V3a+V3b stay proven; M7d
  waits for V3c or is dropped.
- **Law proof difficulty.** Bit-level inductions can stall — the downgrade
  protocol (§3.4) exists for this.
- **No CUDA (`G4`).** GPU work degrades to CPU-parallel validation; keep `!`
  usage correct anyway.
- **Parallel array reads.** Linear ownership prevents sharing one `Array` across
  split regions; clone-per-region is the fallback, semantics-preservation is the
  hard part.
