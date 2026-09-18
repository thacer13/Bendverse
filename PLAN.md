# Bendverse — Plan & Specification

Single source of truth. Executors: implement what this says, check off milestones, keep the gate green.
Workflow authority: `AGENTS.md` (run `bend PROOF.bend` before every commit; learn via `bend guide`; look up APIs via `bend base <Name>`; parallelize where balanced).
Concept authority: `coreidea.md`. Where this file concretizes it, this file wins.

Status: **M0 complete.** Toolchain: bend 2.0.5 (auto-updated from 2.0.4 during planning; verified working).
Machine facts: clang 22, X11 dev headers present, 6 CPU cores, no CUDA — `!` GPU calls fall back to CPU parallel here.

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

A 3D falling-sand-style cellular world (see `coreidea.md`): a 64×64×64 grid of cells, each one `U32` word; materials with density/cohesion; collapse by support loss; impact by fall distance; cost proportional to disturbance (activity bits); pure deterministic worldgen; CPU-parallel with an optional GPU track.

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

## 5. Milestones (check off; each must leave gate green + repo runnable)

- [x] **M0** Plan + scaffold + sanity law proven + gate green + native build verified. (this commit)
- [ ] **M1** Cell word + index math. Spike: bit-31 roundtrip (decides whether bits 24–31 are usable; layout above already safe without them). Laws: `index_roundtrip`, `cell_roundtrip`. Accept: gate green, T5 passes.
- [ ] **M2** Worldgen + ASCII slice. Accept: `bend main.bend` prints recognizable terrain; T1-style determinism holds for gen (same seed → same world).
- [ ] **M3** Movement: empty/sand/bedrock world; 8-phase tick; swap-only. Accept: T1, T2, T3 pass; before/after ASCII shows plausible falling.
- [ ] **M4** Activity: skip inactive, propagate on writes, settle. Accept: T4 passes; a tick over a fully-settled world does (near) zero writes.
- [ ] **M5** Cohesion: support pass, crumble, impact crush (Rock → Rubble), cohesive-as-static interim removed. Accept: T2 still passes (crumble conserves non-Empty count); pull-the-base scenario collapses in ASCII demo.
- [ ] **M6** Windowed app: `App.run`, cross-section view, mouse/keyboard editing. Accept: interactive editing visibly disturbs and settles.
- [ ] **M7** Parallel track (optional, droppable): parallel calls in phase folds via `ANode` region splits (mind the linear-owner read problem — clone-per-region is the fallback); `!` GPU on pure kernels (worldgen/noise) first. Accept: T1 still passes bit-for-bit on native `--threads` and any GPU path (CPU fallback here — no CUDA installed).
- [ ] **M8** Chunks / "infinite" world (optional stretch): chunk index as a custom radix tree keyed by packed `U32` coords (`Map` is string-keyed — do not use it for this). Accept: chunk gen + tick identical to fixed-world behavior on the same region.

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

**Status:** M1 complete. (The `Status:` line above still reads M0; this entry supersedes it.)

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
