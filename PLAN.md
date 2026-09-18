# Bendverse — Plan & Specification

Single source of truth. Executors: implement what this says, check off milestones, keep the gate green.
Workflow authority: `AGENTS.md` (run `bend PROOF.bend` before every commit; learn via `bend guide`; look up APIs via `bend base <Name>`; parallelize where balanced).
Concept authority: `coreidea.md`. Where this file concretizes it, this file wins.

Toolchain: bend 2.0.5 (verified working).
Machine facts: clang 22, X11 dev headers present, 6 CPU cores, no CUDA — `!` GPU calls fall back to CPU parallel here.
Progress lives in §5 (milestone checkboxes) and Appendix A (log), newest last.

## 0. Verified platform facts (do not re-derive)

- Bend is pure + affine. Copyable values need `+` (Data kind). Arrays/IO handles are linear (one owner).
- Termination is mandatory: recurse only on structurally smaller pattern-matched args (shrinking param FIRST); loop counters are `Nat` (`case 1n+p`); no mutual recursion (use a selector arg); unbounded loops take `Nat` fuel or live in the `App` event loop; `@unsafe` is banned here.
- No `if`: match `True{}`/`False{}`. Match scrutinee must be a variable, never a computed value (route through a helper def). No `let` before a `match` on a parameter. Annotate literals: `x = {3 : U32}`.
- `Array<T>`: linear, in-place write `a[i] <- v` (rebind: `a = a[i] <- v` unless last statement); the `a[i]` sugar assumes `Array<U32>` (ours is — keep it); explicit API is `Array.get` / `Array.set` / `Array.swap` / `Array.clone` / `Array.map` (`Array.get` returns the array back beside the element — destructure and rebind). Sizes are powers of two (`[v : T*n]` or depth `[v : T^d]`). Indexes wrap (mask).
- Numbers: `U32` (wraps mod 2^32 — assumed, M1 spike confirms), `F32`, `Nat`. Coordinates/arithmetic = `U32`; fuel/counters = `Nat`. XOR is `.^.` (NOT `^`, which is lambda syntax... actually `^` is unused; use `U32.xor`/`.^.`).
- Parallelism: `a b = f(x) g(y)` parallel calls (promise: independent, similar duration). `f!(x)` sends a subtree to the GPU. Uniform numeric work is the GPU sweet spot.
- IO is a monad (`do IO<T>:`); `App.run(~S, ~App{view, tick}, title, w, h, ...)` runs a windowed app: `view : S -> S & Image`, `tick : List<Event> -> S -> IO(Maybe<S>)`, `None` quits. The App event loop is our legal "infinite" loop.
- Laws: `LAWS.bend` holds claims (treat as human-owned: never edit existing law semantics, only append per milestone instructions); `PROOF.bend` proves each via `def Laws.<name>(<law params>)`. `bend PROOF.bend` must print `All terms check.` before any commit.
- Commands: `bend f.bend` (check + run), `bend f.bend -o bin` (native; `--threads N`), `--checkup`, `bend base <Name>`, `bend guide`. Demos exist online in the Bend repo (`demos/app_pong_game_2d`) as App.run references.

## 1. Product

A formally-verified reference engine over a 3D falling-sand-style cellular world (see `coreidea.md`): a 64×64×64 grid of cells, each one `U32` word; materials with density/cohesion; collapse by support loss; impact by fall distance; cost proportional to disturbance (activity bits); pure deterministic worldgen; CPU-parallel with an optional GPU track. The ASCII and windowed front-ends are visibility only — they exist to keep the model observable, not to be the product.

## 2. Normative design

### 2.1 World & cell word
- World = one flat `Array<U32>`, 64×64×64 = 2^18 cells, built `[0u : U32^18n]`-style once by worldgen.
- Flat index: `i = x .|. (z << 6) .|. (y << 12)`; decode `x = i & 63`, `z = (i >> 6) & 63`, `y = i >> 12`. All `U32` (shift amounts are `Nat`).
- Cell word bit layout (24-bit-safe; bits 24–31 must stay 0 — M1 spike tests whether they're usable, never rely on them until proven):

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
| 5 | Water | 80 | no | yes | 0 (reserved, later milestone) |

This table is pure data in `src/cell.bend` (a `match` on material id), not per-material code paths. Static = never moves, never crumbles, is a support source. "Lower-density-or-empty" is unified: Empty has density 0.

### 2.3 Cell encoding
`src/cell.bend`: `encode(material, cohesion, active, support, fall) -> U32` and `decode(word) -> Cell` record + field accessors via shifts/masks. Only these functions touch the bit layout.

### 2.4 Tick pipeline (normative order, in `src/sim.bend`)

```
tick(world):
  1. support pass    — recompute support field (see 2.8)
  2. crumble pass    — cohesion := 0 on unsupported cohesive cells; Rock -> Rubble (see 2.8)
  3. movement phases — c = 0..7 in fixed order; per phase one in-place fold over
                       all cells of color c in lexicographic scan order: x asc, then z asc, then y asc
  4. activity settle — every cell evaluated this tick whose word did not change: active := 0
```

Phase color: `c = (x & 1) .|. ((y & 1) << 1) .|. ((z & 1) << 2)`. Verified property: any two cells within the 26-neighborhood differ in at least one coordinate parity, so no two same-color cells are neighbors — per-phase updates cannot conflict through adjacency.

**Normative semantics = the sequential scan above.** Determinism (coreidea rule 10) holds by construction: same input Array + same constants → same output, regardless of anything else. Parallel/GPU work (M7) is legal only if it reproduces this exactly.

### 2.5 Tie-break (single-writer, coreidea rule 3)
Within a phase, two non-adjacent same-color movers may target the same cell (their common neighbor). Resolution: **the mover that comes first in the phase's lexicographic scan order wins**; later movers see the target occupied and stay. This is the binding spec; any parallel implementation must reproduce it (priority = scan order).

### 2.6 Universal falling rule (per evaluated cell, in its phase)
Materials differ only via the 2.2 table (density, slides, cohesion) — the logic below is shared:

```
1. Empty or static material: do nothing.
2. cohesion > 0: do not move individually (handled only by support/crumble). 
   [Interim until M5: treat all cohesive materials as static in movement; same net effect.]
3. below = (x, y-1, z); treat y = 0 as blocked (worldgen guarantees bedrock there anyway).
   If below is Empty or density(below) < density(here):
     swap(here, below); mover's fall := min(63, fall + 1); mark activity; done.
4. Else if slides:
   For (dx, dz) in fixed order (-1,0), (+1,0), (0,-1), (0,+1):
     side = (x+dx, y, z+dz); diag = (x+dx, y-1, z+dz)   [wrap is masked; borders are bedrock]
     If side and diag are both Empty-or-lower-density: swap(here, diag); fall unchanged; done.
5. Else (blocked): if fall > 0, resolve IMPACT (2.7). fall := 0. No move.
```

All moves are swaps (coreidea rule 2). No material is created or destroyed by movement.

### 2.7 Impact (coreidea rule 8)
At step 5 with `fall > 0`: `damage = fall`. Target = below cell.
- If target is static (Bedrock): no damage; mover stops.
- Else if `damage >= cohesion(target)`: target cohesion := 0; if target is Rock → Rubble; mark activity on both cells + neighbors; then the mover re-evaluates steps 3–4 once (it may now sink into crushed Rubble or slide).
- Else: mover stops (target takes no damage in v1; no partial wear).
Then `fall := 0`. No velocities, no momentum — energy is just the fall-distance counter.

### 2.8 Support & crumble (coreidea rules 6–7) — the crumble trick
Rigid clusters are NEVER moved as units. An unsupported cohesive cell simply loses cohesion (that event IS "rock → rubble") and afterwards obeys the universal falling rule individually. This keeps everything local.

Support pass (step 1), scanned y ascending 0..63, active regions only, recomputed from current neighbors every tick (no caching):
```
support(c) = 31                          if c is static
           = 31                          if any 6-neighbor is static
           = support(below)              if below is cohesive and support(below) > 0
           = 0                           otherwise
```
Crumble pass (step 2): every cohesive cell with support = 0 → cohesion := 0; Rock → Rubble; fall := 0; mark activity (self + 26-neighbors). Loose cells don't need support (they just fall).

Upgrade path (only if needed): `SUPPORT_PASSES > 1` relaxation sweeps to propagate support through sideways cohesive chains (overhangs). v1 = the single-pass rules above.

### 2.9 Activity (coreidea rule 9)
- Every write to any cell (movement, crumble, impact, user paint) sets active on that cell and on all 26 neighbors, immediately.
- Phase folds evaluate a cell only if its active bit is set (v1 iterates all cells of the color and tests the bit — the scan is cheap; per-color active index lists are a later optimization).
- Settle pass (step 4) clears active on evaluated-and-unchanged cells. Disturbance dies out; untouched regions cost one bit-test per cell.
- Freshly generated worlds are all-inactive (coreidea rule 11). Runners "wake" regions on demand (paint/spawn marks activity).

### 2.10 Worldgen (coreidea rule 11) — pure, in `src/worldgen.bend`
`gen(x: U32, y: U32, z: U32, seed: U32) -> U32` — a pure function of coordinates + seed only. Build the world by calling it per cell (parallelizable later; sequential is fine for 2^18).
- `SEED = 42u` constant (v1).
- Integer hash (all `U32`, wrapping): `h = (x * 2654435761) .^. (y * 40503) .^. (z * 2246822519) .^. seed`, then `h = h .^. (h >> 15)`, `h = h * 2246822519`, `h = h .^. (h >> 16)`. Constants are decimal spellings of 0x9E3779B1 / 0x85EBCA6B / 0xC2B2AE35.
- Value noise: hash lattice corners at period 16, take top 8 bits (0–255), trilinear/bilinear interpolate with `F32` (purity makes this deterministic).
- Terrain height `gy(x, z) = 8 + floor(noise2(x, z) * 24)` → 8..32.
- Cell assignment: bedrock shell if `y = 0 or y = 63 or x = 0 or x = 63 or z = 0 or z = 63`; else `y > gy` → Empty; `y >= gy - 3` → Sand; else → Rock (cohesion 48). Everything starts inactive, support 0, fall 0. The bedrock shell means movement never observes array wraparound.
- Extra sparse feature fields (pockets, boulders) are optional M2+ additions — must stay pure coordinate functions.

### 2.11 Runners
- `app/ascii.bend` (+ root `main.bend` delegating to it): build world, print a cross-section (x–y plane at z = 32, y printed top-down so up is up) via `IO.print`, run N ticks (`Nat` fuel, N = 20), print again. Chars: `.` Empty, `#` Bedrock, `s` Sand, `R` Rock, `r` Rubble.
- `app/window.bend` (M6): `App.run` with state = world (+ a `Bool` running flag); view renders the x–y cross-section at z = 32 as a 64×64 `Image` quadtree (`Pix` per cell; material → color map); tick folds events: left mouse = paint Sand at `(mx, 63 - my, 32)`, right = Rock, `e` key = Empty, space = pause, `Close` → `None`. Paints set activity on the 26-neighborhood.
- `app/tests.bend`: golden tests, see §3.

### 2.12 Determinism contract
Given the same initial `Array<U32>` and constants, any run (JS, native, threaded) produces identical results. Verified by T1. This is the acceptance bar for any parallel/GPU work.

## 3. Verification protocol

**Gate:** `bend PROOF.bend` → `All terms check.` before every commit (non-negotiable, per AGENTS.md).

**Laws policy:** claims live in `LAWS.bend` (append-only, one at a time, per milestone below; never edit an existing law's meaning). Proofs live in `PROOF.bend` (`def Laws.<name>(<params>)`). If a proof stalls, downgrade that property to a golden test and record the downgrade here — never leave the gate red, never silently delete a law.
- Seeded (M0, proven): `sanity` — closed arithmetic equation.
- M1: `index_roundtrip` — flat↔3D index bijection over the 64³ domain; `cell_roundtrip` — `encode(decode(w)) == w` (or per-field roundtrip, whichever proves cleanly).
- Later milestones add laws only when cheap to prove; simulation-level properties (conservation, stability) are golden tests, not laws.

**Golden tests (`app/tests.bend`, `main` prints `PASS`/`FAIL` per line):**
- T1 determinism: two worlds from the same seed, 10 ticks each → identical Arrays.
- T2 conservation: count of non-Empty cells invariant across 10 ticks (from a disturbed start).
- T3 static: all Bedrock words identical after 10 ticks.
- T4 activity: after settling (tick until no active bits, cap 200), cells never near the disturbance equal their fresh-gen words.
- T5 encode/decode roundtrip over a spread of sample words (runtime twin of the law, if the law needed downgrading).

## 4. File layout & responsibilities

```
PLAN.md            this file — update checkboxes as work lands
LAWS.bend          law claims (append-only; treat as human-owned)
PROOF.bend         proofs of every law (the gate)
main.bend          entry: delegates to the current milestone's runner
src/cell.bend      word encode/decode, material table, field accessors
src/grid.bend      flat<->3D index math, neighbor lookup, Array helpers
src/worldgen.bend  pure gen(x, y, z, seed), noise, terrain
src/rules.bend     falling rule, swap, tie-break, impact, support, crumble, activity marking
src/sim.bend       tick pipeline (passes + 8 phase folds)
app/ascii.bend     fueled ASCII runner
app/window.bend    App.run windowed runner (M6)
app/tests.bend     golden tests T1–T5
```
All of `src/` is pure (zero IO). Runners are thin shells. Each module imports `Base` (and each other via `import ./x.bend as X`).

## 5. Milestones

Milestone IDs (`M0`–`M5`, `V1`…) are **stable historical labels**, not a mandatory execution order. Below they are grouped by purpose with the gating made explicit: independent work may proceed in parallel, and the optional scale track is droppable without weakening any verified claim. Every landed step must leave the gate green and the repo runnable.

### Foundation (landed)

- [x] **M0** Plan + scaffold + sanity law proven + gate green + native build verified. (this commit)
- [x] **M1** Cell word + index math. Spike: bit-31 roundtrip (decides whether bits 24–31 are usable; layout above already safe without them). Laws: `index_roundtrip`, `cell_roundtrip`. Accept: gate green, T5 passes.
- [x] **M1.5** Bit-lemma library (`src/bits.bend`) + Word-level index/cell model + refinement to `U32`. Upgrades `index_roundtrip`/`cell_roundtrip` from golden tests back to proven laws. Accept: gate green, T5 still passes. (See A.6.)
- [x] **M2** Worldgen + ASCII slice. Accept: `bend main.bend` prints recognizable terrain; T1-style determinism holds for gen (same seed → same world).
- [x] **M3** Movement: empty/sand/bedrock world; 8-phase tick; swap-only. Accept: T1, T2, T3 pass; the before/after ASCII cross-section shows plausible falling.
- [x] **M4** Activity: skip inactive, propagate on writes, settle. Accept: T4 passes; a tick over a fully-settled world does (near) zero writes.
- [x] **M5** Cohesion: support pass, crumble, impact crush (Rock → Rubble), cohesive-as-static interim removed. Accept: T2 still passes (crumble conserves non-Empty count); the pull-the-base scenario collapses in the ASCII runner's before/after cross-section.

### Verification layers (the claims)

These carry the properties the engine claims and touch no runtime code; they are scheduled by what they unlock, not by number.

- [x] **V1** Stability kernel: proven Nat-arithmetic library + Φ-decrease for fall/crumble + budget exhaustion. Formalizes the settling assumption M4/M8 rest on. See A.7.
- [ ] **V2 Global settling** (in progress — list measure + composition landed (A.9); array-level Φ via `to_pots` landed (A.10); the `Array.set`/`to_pots` refinement is the remaining wall): a `Sim.tick` model whose Φ-measure decreases on every activity-producing event, refined — or with the refinement gap explicitly documented — against the `Array` implementation. Certifies M4's zero-write fixed point and **gates M8**, since chunk sleeping is unsound if a disturbance need not settle. The remaining refinement shards as:
  - [ ] **V2b-i** `List.set` split/sum lemma — self-contained.
  - [ ] **V2b-ii** `Array.swap.go` ↔ `to_pots` point-update correspondence — the tree induction; the risky one.
  - [ ] **V2b-iii** `Sim.tick` as a composition of `replace_decreases` instances — including "support writes preserve Φ" and "the bedrock floor keeps every crumble at `L ≥ 1`".
- [ ] **V3 Order-independence** (only with M7, optional): a phase fold's result is invariant across the schedules M7 admits, given the §2.5 priority. Turns M7's correctness into a theorem instead of a bit-for-bit test. Sharded:
  - [ ] **V3a Parity independence** — same-color cells are never 26-neighbors (pure index/parity arithmetic on the existing bit model; small, provable now).
  - [ ] **V3b Priority is total and local** — among same-phase movers targeting one cell, scan order yields a unique winner and the losers observe it occupied; comparison radius ≤2 (medium).
  - [ ] **V3c Schedule invariance** — a region-split fold equals the sequential fold; builds on V3a+V3b. Large and stall-prone: fallback is V3a+V3b proven with V3c kept as a documented gap.

### Visibility (independent of verification)

- [x] **M6** Windowed app: `App.run`, cross-section view, mouse/keyboard editing. Accept: interactive editing visibly disturbs and settles. May proceed in parallel with V2. (See A.11; human to confirm interactively.)

### Scale (optional, droppable; M8 gated on V2)

- [ ] **M7 Parallel track**: parallel calls in phase folds via `ANode` region splits (mind the linear-owner read problem — clone-per-region is the fallback); `!` GPU on pure kernels (worldgen/noise) first. Pair with **V3**. Accept: T1 still passes bit-for-bit on native `--threads` and any GPU path (CPU fallback here — no CUDA installed). Sharded, easiest → hardest:
  - [ ] **M7a Parallel worldgen** (`build`) — pure, no shared linear state; smallest real speedup, zero semantic risk.
  - [ ] **M7b GPU worldgen** (`!` on `hash`/`noise2`/`gen`) — same semantics, needs CUDA.
  - [ ] **M7c Parallel render** (`view`) — per-pixel, but shares the world `Array` → clone-per-region; independent of movement.
  - [ ] **M7d Parallel phase folds (CPU)** — region splits + clone + the §2.5 tie-break; gated on **V3c**.
  - [ ] **M7e GPU phases** — last and most optional.
- [ ] **M8 Chunks / "infinite" world** (stretch): chunk index as a custom radix tree keyed by packed `U32` coords (`Map` is string-keyed — do not use it for this). Requires **V2**. Accept: chunk gen + tick identical to fixed-world behavior on the same region. Sharded:
  - [ ] **M8a** chunk key/index + pure per-chunk gen (easy; worldgen is already pure).
  - [ ] **M8b** radix-tree chunk store (replaces the string-keyed `Map`).
  - [ ] **M8c** region tick equivalence.
  - [ ] **M8d** sleeping/eviction (rests on **V2b**).

Suggested sequence (interleaved by dependency): **V3a → V3b → M7a → M7c → V3c → M7d → (M7b/M7e once CUDA is installed) → V2b-i → V2b-ii → V2b-iii → M8**. V3 gates M7's correctness; V2b gates M8; M7 and V2b are independent, so V2b may jump ahead if the CUDA/GPU path stalls. Dropping M7/M8 costs nothing above the scale track; dropping V2 costs the settling guarantee.

**GPU expectation (honest):** the current 64³ world is too small to showcase a GPU; the GTX 1050 is discrete VRAM (transfer cost) and falling-sand is divergent work, whereas the GPU's sweet spot is uniform numeric work. Worldgen/noise are the good GPU targets, and real GPU payoff is at M8 scale, not in the movement phases. Near-term, CPU forks (M7a/M7c) are likelier to show wins than the GPU path.

## 6. Bend guardrails (these WILL bite — read before writing code)

- Fuel every loop with `Nat` (`case 0n:` / `case 1n+p:`); shrinking parameter goes FIRST in recursive calls. No `@unsafe`, no mutual recursion (merge into one def with a selector arg).
- No `if` — `match b: case True{}: ... case False{}: ...`. Match only variables (helper def for computed scrutinees). No `let` between a def's parameters and its `match` on them.
- Annotate literals: `x = {3 : U32}`. Operators need spaces. `==` is a type; runtime equality is `U32.is_eq(a, b)`. XOR is `.^.`; shifts take `Nat` amounts.
- `Array` is linear: never drop it, never use it twice on one path; rebind after every write; `Array.get` hands back `(array & value)` — destructure. Sizes: powers of two only. `a[i]`/`a[i] <- v` sugar is for `Array<U32>` (keep the world `Array<U32>`).
- Closures are affine (call once); top-level defs are freely callable; templates (`~f`) inline at compile time.
- Parallel call: `a b = f(x) g(y)` — only where branches are balanced. `f!(x)` = GPU (falls back to CPU here).
- When unsure of a Base name: `bend base <Name>` (e.g. `bend base Array`). Do not guess APIs.
- `?name` inside a proof prints the goal; `?TODO` leaves it open (gate stays red — avoid).

## 7. Open risks / spikes

- **U32 width & wrap:** M1 spike sets/reads bit 31 and checks mul wraparound; layout is already safe without bits 24–31.
- **Read sugar semantics:** confirm exact `a[i]` read/rebind behavior in M1 with a 5-line test; else use `Array.get`/`Array.swap` explicitly.
- **Parallel Array reads across split regions:** linear ownership means parallel branches can't share one Array; clone-per-region (O(n)) is the documented fallback; semantics-preservation (tie-break by scan order) is the hard part of M7.
- **Law proof difficulty:** bit-level inductions can stall — the downgrade protocol in §3 exists for this.
- **No CUDA on this machine:** M7 GPU work degrades to CPU-parallel validation; keep `!` usage correct anyway.

---

## Appendix A — AI milestone log

> Convention: the text above is human-owned and is preserved verbatim. The AI never rewrites it in place; status changes, results, and observations are appended here, newest last. Where an appendix entry conflicts with text above, the appendix is authoritative until the human folds it back in.

### A.1 — M1 complete: cell word + index math (bend 2.0.5)

**Status:** M1 complete.

**Deliverables**
- `src/grid.bend` — `size`, `volume`, `index(x,y,z) = x | (z<<6) | (y<<12)`, decoders `ix/iy/iz`, generic `neighbor(i,dx,dy,dz)` with wrapping U32 deltas and 6-bit masks, and axis neighbors `below/above/west/east/south/north`.
- `src/cell.bend` — `Cell` record; `encode`/`decode`/`reencode`; field accessors `material/cohesion/active/support/fall`; material table (`empty..water`, `density`, `static`, `slides`, `default_cohesion`). Layout matches §2.1 exactly; bits 23–31 stay zero.
- `app/tests.bend` — T5 and spikes; `main.bend` now delegates to it.

**Laws shipped (gate green, `All terms check.`)**
- `grid_volume` — `size³ == volume` (closed arithmetic; keeps the two constants honest).
- `cell_full_mask` — `encode(31,63,1,31,63) == 2^23-1`, i.e. the five fields exactly tile bits 0–22 with no overlap or gap.
- `cell_reserved_bits` — that same max-field word ANDed with `0xFF800000` is `0`, i.e. bits 23–31 are untouched by encoding.

**Law downgrades (per §3 protocol; recorded, not deleted)**
- `index_roundtrip` and `cell_roundtrip` are **downgraded to golden tests**. Reason: both are bit-level invariants over `U32`; `U32` has no finite constructor set to case-split (2³² values), so the checker cannot reduce a symbolic `U32` through `and`/`shl`/`shr` without a shift/mask lemma library.
- The viable proof route was validated in-session: `Word(n)` **is** inductively provable (proved `Word.and(n, w, Word.zero(n)) == Word.zero(n)` by induction on the bit width `n`). So the fix is a `src/bits.bend` proven-lemma library over `Word`, a `Word`-level index/cell model, and a refinement proof that the `U32` implementation matches it.

**Golden tests / spikes shipped (all PASS, JS and native)**
- T5 index roundtrip over the **entire** 2^18 domain (exhaustive) and cell field roundtrip + `reencode(w) == w` over 4096 spread words.
- Spike: bit 31 is readable (`shln(1,31n) == 2147483648`) and `mul` wraps mod 2^32 — so `U32` is confirmed 32-bit and bits 24–31 are usable (layout keeps them reserved regardless).

**Risk-status updates (relative to §7 above)**
- §7 "U32 width & wrap" → **RESOLVED**: bits 24–31 usable; `mul` wraps mod 2^32.
- §7 "Read sugar semantics" → **DEFERRED to M2/M3**: M1 has no `Array`; confirm `a[i]` read/rebind with a small test before worldgen/movement.
- §7 "Law proof difficulty" → **OPEN, now scoped**: see the downgrade entry above; needs the `src/bits.bend` lemma library. Recommended as a dedicated **M1.5** before M5 accumulates more bit invariants.
- §7 "Parallel Array reads across split regions" → added insight: the §2.5 scan-order tie-break can be made conflict-free for parallel folds by having each mover locally compute whether it outranks every other candidate targeting the same cell (comparison radius ≤2), so determinism need not be sacrificed for parallelism.

**Recommended next:** commit M1, then either start M1.5 (`src/bits.bend` lemma library → prove `index_roundtrip`/`cell_roundtrip`) or proceed to M2 (worldgen + ASCII), where the Array read-sugar spike is the next unknown.

### A.2 — M2 complete: worldgen + ASCII slice

**Status:** M2 complete. Chosen order was M2 before M1.5: it unblocks everything and gives the first visible artifact; the bit-lemma work stays queued.

**Deliverables**
- `src/worldgen.bend` — `seed()=42`; `hash(x,y,z,s)` (the §2.10 mix, using the formula's decimal constants `2654435761 / 40503 / 2246822519`, since the parenthetical hex note in §2.10 is inconsistent with the formula); `corner` (top 8 bits); `noise2` (bilinear F32 interpolation at period 16); `height = 8 + floor(norm*24)`; `gen` (bedrock shell, then Empty/Sand/Rock by height); `build`/`build_go` filling the 2^18 `Array<U32>`.
- `src/grid.bend` — added `to_list`/`to_list_go` (array→list over `ALeaf`/`ANode`) and `value_at`/`pack` (single-cell read).
- `app/ascii.bend` — builds the world, renders the `z=32` x–y cross-section top-down (y=63 at top) via a single-pass `frame` + `finish_row`/`join_rows`; `main.bend` now delegates here.
- Golden tests added to `app/tests.bend`: **T6** gen determinism (4096 samples), **T7** terrain structure (at `height` = Sand, `height+1` = Empty, deep = Rock, `x=0` = Bedrock), **T8** built array matches `gen` at a spot. All PASS; full suite ~0.7s (JS), native `main` ~20ms.

**Verified acceptance:** `bend main.bend` prints recognizable terrain (bedrock shell, noise mountains, sand surface, rock core); gate green; native builds and runs.

**Bend sharp edges discovered in M2 (workarounds are in `src/`)**
- `Array.to_list` in Base is **broken in bend 2.0.5** (`expected a defined name, observed Array.to_list.go` when the template inlines). Workaround: `Grid.to_list_go` reimplements it directly over `ALeaf`/`ANode`.
- `Array.get` and the `a[i]` read sugar both return an `Array<T> & value` pair; **destructuring lets only accept parameters**, not computed values or local binders. Workaround: consume pairs via non-recursive helper defs (`Grid.pack`, `Grid.value_at`); for loops, restructure so no intermediate pair must be split.
- A `match` cannot be a let RHS or a term ("a match heads a def body, not a term") — route through a helper def.
- Mutual recursion is rejected ("no mutual recursion"), so fetch/consume two-phase helpers are out; the rendering uses a single recursive `frame` with two scrutinees (`cells`, `rows`).
- Nat literals like `262144n` expand to a 262144-deep term and overflow the checker; use `U32.to_nat(262144)` instead.
- Affine `+` annotations are needed on any local/param used more than once in a path (lots of these in hash/noise/render).

**Note for `src/bits.bend` (M1.5):** M2 did not add laws (nothing cheap: worldgen is numeric, not inductive). Still recommend M1.5 before M5.

**Recommended next:** proceed to M3 (movement: 8-phase tick, swap-only) — it needs the world `Array` threaded through rules and will exercise the pair/helper patterns hardest; or do M1.5 first if laws are wanted green sooner.

### A.3 — M3 complete: 8-phase movement (swap-only)

**Status:** M3 complete. Chosen order: M3 before M1.5 (movement unblocks the whole engine; laws still queued).

**Deliverables**
- `src/rules.bend` — `color_of` (the §2.4 parity color), `side_index`/`diag_index` (the 4 slide directions in spec order), `mov` (down-move with `fall := min(63, fall+1)`), `clear_fall`, and `step`: the whole per-cell universal falling rule as a **single recursive state machine** (one `Nat` fuel param, a `U32` selector `sel`, plus carried `i/c/w/k`).
- `src/sim.bend` — `phase(world, c)` runs one phase over cells of color `c` in flat (x,z,y) scan order; `tick` runs phases `0..7`; `ticks(fuel, world)` iterates. Column swap is by two in-place writes; no material created/destroyed.
- `app/ascii.bend` — builds the world, spawns a floating 5×5×7 sand block, prints the `z=32` cross-section, runs 14 ticks, prints again. `main.bend` still delegates here.
- `app/simtests.bend` — T1 (determinism: two worlds, 10 ticks, lists equal), T2 (non-Empty count invariant over 10 ticks), T3 (every gen-Bedrock cell unchanged after 10 ticks). **All PASS**, ~1s native.

**Verified acceptance:** native `main` shows the spawned block fall from y≈52 and form a pile at y≈18–30; over the untouched heightfield almost nothing moves (correct: the terrain has no overhangs and 1-cell steps are stable, so there is little to avalanche). Gate green.

**Platform finding (important for all future runners/tests):** `bend file.bend` **normalizes a value-returning `main`**, so an expensive pure computation in a `-> U32` main appears to "hang" in the checker. Always make expensive runners `main -> IO(Unit)` (print the result), or compile and run the binary. The emitted JS itself is fine.

**Timing:** native tick ≈ 45 ms; JS tick ≈ 2.9 s (≈ 8× total for a full before/after demo). `app/simtests.bend` is therefore **native-recommended**; keep `app/tests.bend` (T5–T8) tick-free so it stays fast under plain `bend`.

**Bend patterns discovered in M3 (the linear-array ruleset)**
- Fetch-then-use for linear arrays: `Array.get` returns a pair that can only be *matched as a def parameter*. The working shape is one recursive `step(fuel, gp: Array<U32> & U32, ...)` that matches `gp` each call; reads pass the new pair forward, and non-read transitions reconstruct a fresh `(world, v)` pair (passing an already-matched `gp` again counts as re-consuming it).
- Control flow on computed `Bool`s: `match` cannot scrutinize a let-bound value, so branch by selecting the next state with `Bool.pick(U32, cond, true_sel, false_sel)` and recursing; the recursive call's `sel` is a parameter, which *can* be matched.
- Multi-scrutinee `match` cannot take a pair pattern (`match a b: case .. (x,y):` is rejected); nest single matches instead. Match parameters in binder order (fuel before gp before sel).
- Affine `+` is required for any binder used twice on a path; `+b` inside a pair pattern did **not** register in the nested case here, so bind `+v = gv` *inside the branch* (a let before a `match` on a parameter is rejected — "match scrutinees in binder order").
- Worst-case ≈26 `step` calls per cell; fuel set to `2^23` (`U32.to_nat(8388608)`), which exceeds the bound. Verified the loop exits on `i == volume`, not on fuel exhaustion (doubling fuel changes nothing).

**Recommended next:** M4 (activity: skip inactive, propagate on writes, settle). This will cut the per-tick cost dramatically (only disturbed regions do work), and it fits the `step` machine by adding an active-bit gate at `sel 0`. Then M5 (support/crumble/impact). M1.5 bit-lemmas remain queued.

### A.4 — M4 complete: activity (skip inactive, wake on writes, settle)

**Status:** M4 complete.

**Deliverables / semantics**
- `src/rules.bend`: added `mark`/`wake` (sets the active bit — 2048, bit 11 — on a cell and its 26 neighbors via three forward-only nested loops `wake_z → wake_y → wake_x`, no mutual recursion). `step` sel 0/20/19/18 now gate on activity:
  - sel 0: inactive → advance (sel 19), active → sel 20.
  - sel 20: color ≠ phase → advance without clearing (sel 19, so the cell is still evaluated in *its own* phase); else sel 18.
  - sel 18: active and in-phase → **clear the active bit** (`w & 0xFFFFF7FF`) then run the skip/fall logic. So a cell that does nothing settles; a cell that moves is re-woken for next tick.
- Movement writes (down/diagonal) and `clear_fall` (only when it actually writes) call `wake` on the moved cells, so the frontier propagates one ring per tick.
- `src/sim.bend`: added `spawn`/`spawn_go` (the demo sand block, now waking each written cell). `app/ascii.bend` uses `Sim.spawn`.

**Reset of the M3 activity gap:** M3 ran every cell every phase; M4 makes an untouched, settled world do only the per-cell bit test with **zero writes** (sel 0 → 19 → advance). Fresh worlds stay all-inactive; runners wake regions on demand (`Sim.spawn`, and `wake` for future paint/editing).

**Golden tests (native, `app/simtests.bend`) — all PASS, ~4s**
- T1 determinism, T2 conservation, T3 bedrock static (as before).
- **T4**: build → spawn → settle (50 ticks) → (a) no active bits anywhere, (b) every cell outside the disturbance footprint (x,z ∉ [27,37]) is bit-identical to fresh `gen`.
- **T4b**: hashing a settled world is identical with and without one extra tick — i.e. a tick over a settled world is a **fixed point / zero writes**.

**Recommended next:** M5 (cohesion: support pass, crumble, impact crush Rock→Rubble, remove the cohesive-as-static interim). This is the last big rule-system piece; activity already gives it cheap incremental evaluation. Then M6 (windowed app). M1.5 bit-lemmas still queued (laws currently: `sanity`, `grid_volume`, `cell_full_mask`, `cell_reserved_bits`).

### A.5 — M5 complete: support, crumble, impact

**Status:** M5 complete.

**Structure**
- New `src/ops.bend`: shared world ops (`mark`/`wake` 26-neighbourhood, `set_support`, `set_fall0`, `crush_material`/`crush_word` rock→rubble, `adjacent_static`). `rules.bend` and `support.bend` both import it (avoids a rules↔support cycle).
- New `src/support.bend`: `sup` state machine implements support **and** crumble in one y-ascending pass (`tick` calls it before the 8 movement phases). Order matters: `pass` (active-gated) during ticks, `pass_all` (non-gated) once at initialisation.
- `src/rules.bend`: impact added at the "blocked" branch (`sel 8 → 21 → 22/23`): damage = fall distance; if target is non-static and `damage >= cohesion(target)` it is crushed (cohesion 0, Rock→Rubble, both sides woken), else the mover just stops; fall resets to 0. The interim is gone: cohesive cells still don't move individually, but support/crumble now converts unsupported Rock to Rubble, which then falls.
- `src/sim.bend`: `tick = support pass + 8 phases`; `build()` = `Support.pass_all(Worldgen.build())`; `pull()` = demo disturbance (remove one base rock cell + wake).

**Design decisions / deviations**
- **Support initialisation is required.** Worldgen leaves every support field 0. Without a full initial pass, the first woken isolated Rock cell reads a stale `support(below)=0` and crumbles, and the wake cascade spreads across the map. `Sim.build()` runs the non-gated pass once. **All simulated worlds must use `Sim.build()`** (pure `Worldgen.build()` is still used only by the gen-equality test T8).
- **Support is a derived field.** Because init writes support 31 into every cohesive cell, a settled world is not bit-identical to `gen`; T4 therefore compares material + cohesion + fall (ignoring support and active). `support ∈ {0,31}` in this ruleset (static-adjacency or straight-up propagation); sideways cohesion chains remain the documented upgrade path.
- **The 6-neighbour "is static" test is `adjacent_static(i)` (coordinate check x∈{1,62}, z∈{1,62}, y∈{1,62}).** Exact today because the only static material is Bedrock, which worldgen places only on the shell and which no rule creates. If more static materials are ever added, this must become a real neighbour scan.
- Impact re-evaluation is **deferred one tick** (crush, wake both cells, stop) rather than re-running steps 3–4 in the same tick. Behaviourally equivalent once the woken mover is processed next tick, and it keeps the state machine from re-entering the impact branch.

**Bugs found and fixed during M5**
- support pass read the *current* word where it needed *below* (added `sel 5` to fetch below) — this had crumbled ~71k cells at init.
- `set_fall0` preserved the active bit, so every blocked cell re-activated itself each tick and never settled (500 cells stuck active). It now clears the active bit; a blocked, evaluated cell settles.

**Golden tests (native, `app/simtests.bend`) — all PASS, ~4.3s**
- T1, T2 (now spawns a disturbance first, so movement actually happens), T3, T4 (settles, zero active, far cells unchanged in material/cohesion/fall), T4b (settled world is a fixed point), **T9** (pull one base rock cell → after 5 ticks the Rock count is strictly lower — crumble worked).
- Fast JS suite `app/tests.bend` (T5–T8) still passes in ~0.7s; `bend main.bend` = native pull-base collapse demo (before/after cross-section shows the column turn to rubble and fall into the hole). Gate green.

**Recommended next:** M6 (windowed `App.run` app: cross-section view + mouse/keyboard editing, painting wakes the 26-neighbourhood). Then M7 (parallelism), M8 (chunks). M1.5 bit-lemmas still queued.

### A.6 — M1.5 complete: bits lemma library + proven index/cell roundtrips

**Status:** M1.5 complete. The two laws downgraded in A.1 (`index_roundtrip`, `cell_roundtrip`) are **proven laws again**; the gate is green with six laws total.

**Deliverables**
- `src/bits.bend` — a self-contained proven lemma library over `Base.Word` plus Word-level index/cell models:
  - Bool: `b_and_idem/true/false/comm/absorb/or`, `b_or_idem/comm/false`, `b_not_not`, `b_and_or`.
  - Word pointwise: `w_and_zero`, `w_or_zero`, `w_and_comm/or_comm/and_idem/or_idem`, `w_and_absorb`, `w_and_or`, `w_or_and`.
  - Shifts/masks: `mask`, `shl_n`, `shr_n` (iterated, defined to match `U32.shln`/`U32.shrn` definitionally), `shl_put_or/and`, `shr_pad_or`, `shl_or`, `shr_or`, `shl_and`, `shl_put_shrpad(_alt)`, `shl_shrpad_alt`, `and_shrpad_alt`, `shl_after_shr`, `and_shl`, `and_shl_n`.
  - Models: `ixm/izm/iym`, `model_index`, `cmat/ccoh/cact/csup/cfl`, `model_cell`; with `t0/t1/t2` and `tcmat/tccoh/tcact/tcsup/tcfl` field helpers, `and_factor`, `and_factor_l`, `factor5`, `mask_index(_l)`, `mask_cell`, and the two capstones `model_index_rt` / `model_cell_rt` (at width 32).
- `LAWS.bend` (appended, existing laws untouched):
  `index_roundtrip` — `Grid.index(Grid.ix(i), Grid.iy(i), Grid.iz(i)) == U32.and(i, 262143)`;
  `cell_roundtrip` — `Cell.reencode(w) == U32.and(w, 8388607)`.
- `PROOF.bend` — `Laws.index_roundtrip` / `Laws.cell_roundtrip` by `Equal.cong` over the `U32` wrapper, delegating to `Bits.model_index_rt` / `Bits.model_cell_rt`.
- `app/tests.bend` T5 kept unchanged as the runtime twin (exhaustive index roundtrip over 2^18, cell words over 4096).

**Design decisions / deviations**
- **Law statements use a mask RHS.** `reencode(w) == w` is false whenever bits 23–31 are set, and the flat index roundtrip is false above 2^18. The unconditional true statements are `... == and(i, 2^18-1)` and `... == and(w, 2^23-1)`; in-range roundtrips follow by specializing `and` with the domain mask. This is the honest formulation of the A.1 downgrade: not weakened to a special case, but made total.
- **Left-association matters.** `Grid.index`/`Cell.encode` use left-associative `. | .`. `model_index`/`model_cell` were written left-associated to match, so the refinement is definitional (right-associated `or` is not definitionally equal to left-associated).
- **Refinement is definitional, not axiomatic.** `U32` is a transparent wrapper `U32{data: Word(32n)}` and every `U32` bit op is its `Word` op on `.data`; `mask(32, k)` reduces to the literal masks (31/63/1/…) and `shl_n`/`shr_n` reduce to `U32.shln`/`U32.shrn`. So `Equal.cong(Word(32n), U32, x => U32{x}, ...)` closes the gap with no extra lemmas. Verified: `bend PROOF.bend` → `All terms check.`
- **Proof style.** Rewrite annotations (`%e : P`, which replaces `b` with `a` at the `_`-marked occurrence) were used for tail recursion, and `Equal.trans`/`Equal.cong` for multi-step algebra where rewrite orientation was fragile. Affine lets (`+x = …`) were needed wherever a proof term mentions the same value more than once; `Nat`/word match binders that are reused get `+` in constructor patterns.

**Verification**
- `bend PROOF.bend` → `All terms check.` (6 laws).
- `bend app/tests.bend` (JS, tick-free) → all PASS, ~0.7s.
- `bend app/simtests.bend -o bin && ./bin` (native) → T1, T2, T3, T4, T4b, T9 all PASS. No simulation code changed, so no behavioural or performance change to the engine.

**Recommended next:** M6 (windowed `App.run` app). M1.5 debt is now paid; no bit-level laws remain queued.

### A.7 — V1 complete: Nat arithmetic + Φ-decrease / settling kernel

**Status:** V1 complete. Added on request after A.6, to formalize the stability assumption behind M4/M8 (a disturbance must settle; otherwise "cost proportional to disturbance" and chunk sleeping are unsound). Gate is green with **11 laws**.

**Motivation (the physics).** Every engine movement is a swap between two cells whose levels differ by exactly 1, where the mover is strictly denser than the cell it displaces (the fall/slide predicate is `density(below) < density(above)` or below empty). Crumble/impact lower a cell's density in place (Rock 200 → Rubble 150). Define the potential

> Φ = Σ over cells of density(cell) · level(cell)

Then every swap changes Φ by `−(d_heavy − d_light) < 0`, and every crumble decreases Φ by `(d_before − d_after) · level`. Φ is a `Nat`, bounded below by 0, so it can decrease only finitely often: the active set must empty. This appendix proves the kernel of that argument.

**Deliverables**
- `src/nat.bend` (new) — the minimal `Nat` arithmetic library Base lacks, all proven:
  `n_add_zero_right`, `n_add_succ_right`, `n_add_assoc`, `n_add_comm`, `n_mul_zero_right`, `n_mul_distrib_left`, `n_mul_succ_right`, `n_sub_zero`, `n_not_lt_zero`.
- `src/potential.bend` (new) — `dens` (material → `Nat`), `phi(d,L) = d·L`, `phi_up(d,L) = d·L + d` (= `d·(L+1)`, via `phi_up_eq`), and the kernel:
  - `fall_decreases(D,G,L)` — `(Φ_after) + G == Φ_before`, where the upper level holds density `D+G` and the lower `D`: the swap lowers Φ by exactly the density gap `G`. With `G` arbitrary, `G ≥ 1` captures strictness.
  - `crumble_decreases(d,G,L)` — `d·L + G·L == (d+G)·L`: lowering density by `G` at level `L` frees `G·L`.
  - `spend(k,m)` / `spend_exhausts(m)` — a `Nat` budget of `m` unit decreases is exhausted to `0` after `m` steps: `spend(m, m) == 0`.
  - Concrete material facts: `dens_empty/water/sand/rubble/rock` = 0/80/100/150/200.
- `LAWS.bend` (appended; existing laws untouched) — `rock_crumbles_lighter` (`dens(rock) == dens(rubble) + 50`), `sand_sinks_in_water` (`dens(water) + 20 == dens(sand)`), `fall_decreases`, `crumble_decreases`, `budget_exhausts`.
- `PROOF.bend` — the five new proofs; the material facts and `rock/sand` gaps by computation, the Φ laws delegated to `Pot`.

**What is proven vs. what remains (scope, honestly)**
- **Proven:** the arithmetic of the potential, the exact per-event decrease with the real density table, and the fact that a `Nat` measure admits only finitely many unit decreases.
- **Not machine-checked (documented refinement gap):** the *global* composition — that a whole `Sim.tick` over the linear `Array<U32>` performs a sum of such events, that `Φ` over the array changes only at the written cells, and therefore `Sim` settles. That needs a formal `Array`/tick model (the array is `ALeaf`/`ANode`, and `Sim.tick` is a fuelled fold), in the same spirit as A.6's warning that proving the model is not proving the imperative code without an explicit refinement. This is the remaining work to turn the kernel into an end-to-end settling theorem; it is a modeling milestone, not an arithmetic one.

**Consequences if the refinement lands.** It would certify the M4 claim ("untouched, settled worlds do zero writes" — T4b is currently the only witness), justify M8 chunk sleeping, and rule out perpetual slide/jitter configurations that tests may not sample.

**Verification**
- `bend PROOF.bend` → `All terms check.` (11 laws).
- `bend app/tests.bend` (JS) → all PASS; native `app/simtests.bend` → T1, T2, T3, T4, T4b, T9 all PASS. No engine code touched; no behavioural or performance change.

**Recommended next:** M6. Optionally, a later **V2** formalizes the `Array`/tick refinement above to close the global settling theorem.

### A.8 — plan re-ordered: verification-gated milestones, runners marked as visibility

**Status:** PLAN.md §1 and §5 revised on human request. Documentation only; no engine, law, or test change.

- **§1 Product** reframed: a formally-verified reference engine over a falling-sand world, with the ASCII/windowed front-ends explicitly marked visibility only.
- **§5** regrouped. Milestone IDs (`M0`–`M5`, `V1`…) are now stated to be **stable historical labels, not execution order**; the list is grouped by purpose (Foundation / Verification layers / Visibility / Scale) with gates explicit. **V2 (global settling) is recommended next and gates M8**; **V3 (order-independence)** is introduced as M7's enabling lemma; **M6 may run in parallel with V2**; M7/M8 remain droppable.
- **Rationale:** settling is the only claimed property with a known refinement gap, and it is load-bearing for the M4 zero-write claim (T4b is currently the only witness) and for M8 chunk sleeping. This follows the A.7 recommendation and the surrounding human discussion; the previous strictly linear M6 → M7 → M8 ordering had implied that scale could precede its own soundness argument.
- **No behavior change:** gate green, `app/tests.bend` and `app/simtests.bend` unchanged.

### A.9 — V2 in progress: potential-sum model, global composition, event bound

**Status:** in progress (not checked off). New `src/settle.bend`; **5 new laws** (16 total). Gate green; engine untouched; all tests pass. Scoped as the "documented refinement gap" branch of V2's acceptance, not the full `Array` refinement.

**Motivation / scope.** A.7 proved the per-event Φ kernel but left the *global composition* as a documented gap (that a whole tick is a sum of such decreases over the array). This entry makes the composition concrete at the level of a formal world-as-sum model and states exactly what remains to link it to `Array<U32>`.

**Deliverables**
- `src/settle.bend`:
  - `suml` — the potential of a finite world represented as a `List<Nat>` of per-site potentials (`density · level`).
  - `suml_append`, `suml_mid` — additivity over concatenation and over a middle segment.
  - `replace_decreases` — **the composition theorem**: if a middle segment `before` is replaced by `after` with `suml(after) + G == suml(before)`, the whole world's potential drops by exactly `G`. This is the missing "local event ⇒ global decrease" step (all other cells untouched).
  - `fall_before` / `fall_after` / `swap_segment_decreases` / `fall_lowers_world` — instantiate the two-site vertical swap with the real density table (heavy at level `1+L`, light at `L`; drop = density gap `G`), reusing `Pot.fall_decreases`.
  - `crumble_segment_decreases` / `crumble_lowers_world` — single-site density drop at level `L` (drop = `G·L`), reusing `Pot.crumble_decreases`.
  - `incs` / `len` / `suml_incs` — encode each strict event's drop as `1+e`; proves total drop `== len + slack`, i.e. **#events ≤ total drop**, bounding the event count by the initial potential.
  - `burn` / `burn_exhausts` — the conservative "one unit per active tick" budget: `burn(p, p) == 0`, i.e. after `p` non-stuttering ticks the potential is exhausted and every later tick stutters.
- `LAWS.bend` (appended): `potential_additive`, `fall_lowers_potential`, `crumble_lowers_potential`, `strict_events_bounded`, `settling_budget`.
- `PROOF.bend`: the five proofs delegate to the module lemmas.

**Proven vs. remaining gap (honest scope)**
- **Proven:** additivity of the potential; a local swap/crumble decreases the global potential by the exact density gap; every strict event is a ≥1 drop, so the event count over any run is at most the initial potential; the unit-drop budget exhausts.
- **Remaining (refinement gap, same kind as A.6/A.7):** the model world is a `List<Nat>` of site potentials, not `Array<U32>`. Not yet formalized: (a) `Sim`'s actual global Φ as a fold over `ALeaf`/`ANode` equal to `suml` on the corresponding list; (b) that each `Rules.step` write is exactly one `replace_decreases` instance and every non-written cell is untouched; (c) that `Support.pass` writes change no potential (material, hence density, is preserved) and that the bedrock floor keeps every crumble at level `L ≥ 1`, so its drop is strict; (d) monotonicity of `burn` in drop size (a real tick drops by ≥1, which only settles faster). Items (a)–(b) are the modeling work to reach an end-to-end `Sim` settling theorem.
- **Consequence:** V2's weaker acceptance branch ("refinement gap explicitly documented") is met; the stronger "refined against the `Array` implementation" branch is not. Keep V2 open until (a)–(b) land; M8 remains gated on it.

**Verification**
- `bend PROOF.bend` → `All terms check.` (16 laws); `bend src/settle.bend` → `All terms check.`
- `bend app/tests.bend` (JS) → all PASS; native `app/simtests.bend` → T1, T2, T3, T4, T4b, T9 all PASS. No engine code touched.

**Recommended next:** continue V2 toward the `Array`/tick refinement ((a)–(b) above), or begin M6 in parallel (visibility; independent).

### A.10 — V2: array-level potential (`to_pots`) landed; `Array.set` refinement is the remaining wall

**Status:** in progress. `src/settle.bend` extended; no new laws (the array identities are definitional plus `suml_append`). Gate green; engine untouched; tests pass.

**Deliverables**
- `pot_at(w, i)` — site potential of word `w` at flat index `i`: `density(material(w)) · iy(i)`.
- `to_pots(a, base, n)` — the positional potential list; structural over `ALeaf`/`ANode`, splitting at `h = n/2` and using `base` / `base+h` for levels. This is the array's ALeaf/ANode fold of its site potentials.
- `array_phi(a)` — the true global Φ: `suml(to_pots(a, 0, size(a)))`, with `Array.size` extracted through the `phi_got`/`size_got` pair helpers (the M2 workaround).
- `to_pots_node` — structural additivity: `suml(to_pots(ANode{xs,ys}, base, n)) == suml(to_pots(xs,base,h)) + suml(to_pots(ys,base+h,h))`, immediate from the `to_pots` definition and `suml_append`. The array potential is therefore the sum of its halves — exactly the shape `replace_decreases` consumes.

**Finding — why (a) is defined through `to_pots`.** A second, direct `Nat`-valued fold `phi_go(a, base, n)` was implemented and a proof of `phi_go(a,base,n) == suml(to_pots(a,base,n))` attempted. It is **blocked by affine arrays**: `Array<U32>` is linear, and the proof needs both folds over the same array (each consumes it) — `ihx = phi_go_eq(xs,…)` consumes `xs`, yet the goal type also mentions `to_pots(xs,…)`. Erasure lets a consumed array appear in proof *types*, but the quantity checker still rejects two runtime mentions (observed: `ys (consumed more than once)`). Resolution: define `array_phi` *through* `to_pots`, so the fold and the `suml` are one traversal and no equality proof is required. `phi_go`/`phi_go_eq` were removed rather than left dead.

**Remaining wall — (b) the `Array.set` refinement.** The precise missing lemma is the tree-update / position correspondence:
```
to_pots(Array.set(a, i, v), base, n) == List.set(to_pots(a, base, n), to_nat(i - base), pot_at(v, i))   (base ≤ i < base+n)
```
or its segment form `l ++ [pot_at(v,i)] ++ r`. Proving it needs: (i) an induction over `Array.swap.go` mirroring its `i < h` / `i-h` descent; (ii) a `List.set` split lemma over `app(l,r)` (`i < len l` → set in the left, else in the right at `i-h`) with the associated bound reasoning; (iii) `U32`/`Nat` index arithmetic connecting `base+i`. This is the same imperative-array refinement A.6 flagged, and it is substantial — the reason the `Array` is not yet linked to the `List` measure. Until it lands, the end-to-end `Sim` settling theorem stays the documented gap and **M8 remains gated on V2**.

**Verification**
- `bend src/settle.bend` → `All terms check.`; `bend PROOF.bend` → `All terms check.` (16 laws).
- `bend app/tests.bend` (JS) → all PASS; native `app/simtests.bend` → all PASS. No engine code touched.

**Recommended next:** attack (b) via the `Array.swap.go` induction plus the `List.set` split lemma (a real chunk of work), or pause V2 and start M6 (visibility; independent).

### A.11 — M6 complete: windowed app (`App.run`, scaled cross-section, editing)

**Status:** M6 complete. New `app/window.bend`; engine untouched; gate green; fast and simulation suites pass; native binary builds and runs.

**Deliverables**
- `app/window.bend` — the `App.run` app:
  - State `St{w: Array<U32>, run: Bool, mx: U32, my: U32}` (world, running, last mouse).
  - `view` renders the `z=32` x–y cross-section as a **256×256** `Image` quadtree (depth 8, each cell a 4×4 block). `render` descends the tile reading `Array.get` and emits one `Pix` per pixel; `group4`/`levels` assemble the quadtree. Colors are decimal `0xRRGGBB` values (the material table).
  - `tick`: `step_events` folds events while threading a `St & Bool` alive flag (single def — no mutual recursion), then runs one `Sim.tick` when running and alive; `Close` quits.
  - Editing: left mouse = Sand, right mouse = Rock, `e` = Empty (at last mouse), space = pause/resume. Paints write the cell with its default cohesion and `Ops.wake` the 26-neighbourhood, so the disturbance visibly collapses and settles.
- Launch: `bend app/window.bend -o bin && ./bin` (native; the JS `Window.open` is a no-display stub). `main.bend` intentionally still delegates to the headless ASCII runner so `bend main.bend` works without a display. First cut was 64×64 (too small, cut off in the corner); now 256×256.

**Bend findings (M6)**
- No hex literals in 2.0.5 (`0x…` is rejected) — use decimal.
- `U32.shr(a)` shifts right by **1**; use `U32.shrn(a, n)` for an `n`-bit shift.
- `Event` fields must be matched in declaration order; matching two fields of an event requires routing them through a helper def whose parameter order matches (`handle_mouse`, `handle_key`). Matching a let-bound value or an out-of-order field is rejected.
- Affine fields reused within a branch need `+` in the pattern (e.g. `+mx, +my`); construction sites take the plain names.
- `List.reverse` needs the matching quantity (`&1` for the cons-built `List<Image>`).

**Verification**
- `bend PROOF.bend` → `All terms check.`; `bend app/tests.bend` (JS) all PASS; native `app/simtests.bend` all PASS.
- Native `app/window.bend` built and ran a full 6 s event loop under `DISPLAY=:0` with no crash; the human confirmed the window appears (and flagged the initial size, now fixed).

**Recommended next:** continue V2 (b) `Array.set`/`to_pots`, or polish M6 (brush size, water). M7/M8 remain optional; M8 is gated on V2.

### A.12 — roadmap sharded: V3, M7, V2b, M8 split into sub-steps; interleaved sequence

**Status:** documentation only (planning). No engine, law, or test change.

**Decision.** The remaining work was reviewed for "one step, one thing". V2, V3, M7, and M8 were each judged too big as single milestones and split (see §5):
- **V2** refinement → **V2b-i** (`List.set` split/sum), **V2b-ii** (`Array.swap.go` ↔ `to_pots` correspondence; risky), **V2b-iii** (`Sim.tick` as composed `replace_decreases`, including support-writes-preserve-Φ and bedrock `L ≥ 1`).
- **V3** → **V3a** parity independence, **V3b** total/local priority, **V3c** schedule invariance (stall-prone; fallback = V3a+V3b proven, V3c documented).
- **M7** → **M7a** parallel worldgen, **M7b** GPU worldgen, **M7c** parallel render, **M7d** parallel phase folds (gated on V3c), **M7e** GPU phases.
- **M8** → **M8a** chunk key + pure per-chunk gen, **M8b** radix store, **M8c** region tick equivalence, **M8d** sleeping (needs V2b).

**Dependency shape.** V3 gates M7's correctness (otherwise parallel output is only T1-witnessed); V2b gates M8 (sleeping needs settling). M7 and V2b are mutually independent. Chosen interleave: **V3a → V3b → M7a → M7c → V3c → M7d → (M7b/M7e once CUDA is installed) → V2b-i → V2b-ii → V2b-iii → M8**. If the CUDA/GPU path stalls, V2b may proceed first.

**GPU expectation (recorded).** For the current 64³ world a GPU is unlikely to help: too little work, discrete VRAM transfer cost, and divergent cellular work vs. the GPU's uniform-numeric sweet spot. Worldgen/noise are the compelling GPU kernels; real payoff is at M8 scale. Near-term wins are expected from CPU forks (M7a/M7c).

**Not in scope / left as-is:** window centering (Bend's `window_open.c` creates at `(0,0)` with fixed size hints; a Hyprland rule experiment was reverted and the config left clean) and window sizing (draggable, left small).

### A.13 — V3a in progress: parity bit model + x-axis neighbor parity proven

**Status:** V3a **partial** (checkbox in §5 left unchecked). New `src/parity.bend`; **3 new laws** (19 total). `src/bits.bend` gained the generic `b_and_assoc` / `w_and_assoc`. Engine untouched; gate green; fast and simulation suites pass.

**Motivation.** §5 sequences **V3a** first ("same-color cells are never 26-neighbors"). The mathematical content is parity: the phase color is `(x&1) | ((y&1)<<1) | ((z&1)<<2)`, and a 26-neighbor differs by `±1` in some coordinate, which flips that coordinate's low bit. This entry lands the parity arithmetic and one full axis end-to-end; the other two axes remain.

**Deliverables (`src/parity.bend`)**
- Word-level low bit `bit0` and the carry facts: `adc_con_head` (head of `Word.adc.con` is the sum bit), `full_add_fst_true` (`full_add(a,True,False)`'s sum is `not a`), `full_add_fst_xor` (sum is `xor`).
- `add_one_flips` / `add_ones_flips`: `bit0(add(a, one(n))) == not(bit0 a)` and the same for `ones(n)` (all-ones). These are the +1 / −1 engine deltas.
- `lsb_add`: **general** — `bit0(Word.add(a,b)) == xor(bit0 a, bit0 b)`. Consequence: adding an odd word flips the low bit; the LSB of a sum is the xor of the LSBs (the carry-in is always 0 at bit 0).
- `par32` (`U32` low bit) with `par32_add`, and the U32 laws `u32_add_one_flips` / `u32_add_ones_flips`.
- Mask/parity: `bit0_and_mask6` (`par32(and(w,63)) == par32(w)`).
- Index extraction: the bit library `low6_pack` proves the low six bits of the packed index are exactly the x field, with supporting lemmas (`and_zero_l`, `shl_zero`, `and_shift_zero6/12`, `and_m6_absorb`, `and_m6_shift6/12_zero`, `or_zero_zero`). `u32_index_ix` lifts it to `U32`, so `Grid.ix(Grid.index(x,y,z)) == and(x,63)`.
- Engine-level: `u32_ix_neighbor` (`Grid.ix(Grid.neighbor(i,dx,dy,dz)) == and(add(Grid.ix(i),dx),63)`) and `neighbor_x_par`: **`par32(Grid.ix(Grid.neighbor(i,dx,0,0))) == xor(par32(Grid.ix(i)), par32(dx))`**.

**Laws appended (`LAWS.bend`; existing laws untouched)**
- `parity_flip_succ` — `par32(U32.add(x,1)) == not(par32(x))`.
- `parity_flip_pred` — `par32(U32.add(x,0xFFFFFFFF)) == not(par32(x))`.
- `neighbor_x_parity` — the x-axis neighbor parity law above. A runtime twin was added to `app/tests.bend` as **T10** (4096 samples).

**What is proven vs. remaining (honest scope)**
- **Proven:** the LSB arithmetic (sum-LSB is xor; ±1 and any odd delta flip it), the x-field extraction from the packed index, and the x-axis neighbor parity law. Since an odd `dx` flips the x color bit, two x-neighbors cannot share a color.
- **Remaining for full V3a:** the analogous **z** and **y** field extractions (`Grid.iz`/`Grid.iy` of `Grid.index`), which need `shr` to distribute over the packed `or` (`shr_n_or`), `shr ∘ and` (`shr_and`), and cancellation of `shr_n ∘ shl_n` under the 6-bit masks. These are the same style of bit induction as `low6_pack`; once landed, the 26-neighborhood corollary follows because a nonzero delta in `{−1,0,1}³` has an odd component. Until then the full "same-color ⇒ not neighbor" statement is **not** machine-checked on all axes; only the x-axis is.
- **Also not machine-checked:** the link from `par32(Grid.ix(·))` to the packed color word being unequal (trivial — bit 0 of `color_of` is `and(ix,1)`, whose LSB is the x parity; the remaining composition is a one-line `Equal.cong` once the other axes land).

**Verification**
- `bend PROOF.bend` → `All terms check.` (19 laws).
- `bend src/parity.bend` → `All terms check.`
- `bend app/tests.bend` (JS, tick-free) → all PASS incl. T10, ~1s.
- Native `bend app/simtests.bend -o bin && ./bin` → T1, T2, T3, T4, T4b, T9 all PASS. Engine untouched.

**Recommended next:** finish V3a's z/y extraction (small, same technique), then V3b (total/local priority). The alternative is to defer y/z and start **V3b**, then circle back; the interleave in A.12 favours finishing V3a first.
