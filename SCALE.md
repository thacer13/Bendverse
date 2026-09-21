# SCALE — migrating the engine from a fixed 64³ torus to a moving chunk window

**Status.** Design note for the `scale` track (P3). Additive only: the live
`Grid`/`Sim` path is untouched, `src/cw.bend` defines the coordinate model, and
T57–T60 witness it. Nothing in this file is a law or a claim; the gap candidates
are for the supervisor to file in `PLAN.md` §5.3.

## 1. Why

The live engine is a fixed 64³ torus. `Grid.index` masks every axis `&63`, so
the world is closed by construction (V0-2, `Grid.step_inside`), and every proof
that mentions `Grid` is a proof about that one box. That is the right model for
a reference engine, but it caps the world at 262144 cells and makes "scale"
mean "run more ticks", not "simulate more world".

The renderer (`../Bendview/SPEC.md`) already assumes an infinite-horizon voxel
view: a dense active window of chunks streamed from a pure, coordinate-indexed
`gen`. This note is the engine side of that contract: an arbitrary-coordinate
window with the same rules, determinism, and conservation.

## 2. What assumes the fixed box

| Site | Assumption |
|---|---|
| `Grid.index` | each axis `&63`; `ix/iy/iz` are its inverse |
| `Grid.neighbor` | wraps mod 64 on every axis |
| `Grid.step_inside` | the box edge is the universe edge (a wrapped step is inert) |
| `Grid.size`/`volume` | 64 / 262144 |
| `Dirty.Mask` | exactly 64 `y` rows (`lo`/`hi`), `mark_wake` touches `y-1,y,y+1` mod 64 |
| `Store.assemble_go` | exactly 64 resident chunks, keyed by `ci & 3`, `(ci>>2)&3`, `(ci>>4)&3` |
| `Sim` | `Dirty.active_mask` scans the whole 64³ array to prime the mask |
| proofs | `index_roundtrip`, the parity/`color_of` laws, `step_m`/`sup_m`, the `PT` packing all quantify over the fixed box |

`Worldgen.gen(x, y, z, seed)` is already coordinate-indexed and needs no change:
it is the infinite ground truth the window samples. `Store` is already a sparse
overlay on it (`assemble` regenerates a missing chunk from `gen`), which is the
seed of streaming.

## 3. The coordinate model (`src/cw.bend`)

`cw` splits a global coordinate into `(chunk_key, local)` and rejoins it with
**no torus mask**:

```
cw_chunk_of(x) = x >> 4          cw_local_of(x) = x & 15
cw_key(cx,cy,cz)                 cw_local(lx,ly,lz)
cw_global_x/y/z(key, local)      cw_pack(x,y,z) -> (key, local)
```

Layout matches `src/chunk.bend` (16³ chunks, 10-bit chunk indices, 4-bit local
offsets). The difference from `Grid` is the point: `cw_global_x` of a coordinate
above 63 keeps its chunk index instead of folding. T60 pins this
(`cw_global_x(key(chunk_of(200),0,0), local(200,0,0)) == 200` while
`Grid.ix(Grid.index(200,0,0)) == 8`).

The module is deliberately tiny and dependency-free. It is the one piece of the
migration that is provably independent of the rule system, so it can land (and
be tested) before any live-path change.

## 4. Target design

A **window** is an explicit, finite set of resident chunk keys plus a focus
coordinate. The world is the union of the resident chunks over the pure `gen`
(rule 11: the store is a sparse overlay).

- **Addressing.** A cell is addressed by a global `(x,y,z)`; the engine keeps
  the window's base chunk key and converts a global coordinate to a window-local
  flat index only at the `Array` boundary. The rule fold already runs over a
  work list (`todo`), not a lattice, so the flat index is a handle, not a
  coordinate.
- **Resident set.** Replace the implicit 4×4×4 `assemble_go` loop with an
  explicit resident set (a keyed set, or a small `Store` with a window policy).
  Loading is the world-coordinate sampler (`gen_terrain`) **plus the
  world-fixed ground** (`G-scale-9`) — loading `gen` conflated the two; eviction
  is the existing sleeping + gen-equal test, which is already lossless.
- **Window motion.** When the focus crosses a chunk boundary, load the entering
  slab and evict the leaving slab. A rule target outside the resident set is a
  boundary case: either the window is kept one chunk larger than the active
  radius (so no rule ever needs a non-resident neighbour), or the step loads the
  chunk first. The former is simpler and matches the "no silent model drift"
  posture.
- **Dirty set.** Replace the 64-row mask with a window-sized row mask (same
  `y`-ascending order the support pass needs) or a per-chunk dirty flag set.
  `mark_wake`'s `y±1` reach is unchanged.
- **The `Array`.** The window is still a power-of-two tree, so the `PT`/`Refine`
  machinery (`swap_m`, `v3c_fold`, the count/Φ laws) is size-agnostic and can be
  reused verbatim for a window of `2^n` cells. What changes is the coordinate
  map, not the write algebra.

## 5. Migration order (each step gate-green)

1. **`cw` + tests** (this track). Additive, no live path. ✅
2. **Window-relative addressing.** Introduce a `Window` (base key + resident
   set) and a `cw`-based index map; keep the 64³ window as the only instance so
   the world is unchanged. The gate stays green because `cw`-of-a-64-box is a
   relabelling of `Grid`.
3. **Explicit resident set.** Replace the `assemble_go` loop bounds with the
   set; still the full 64³ set. Witness: `assemble == worldgen` (T18) still
   holds.
4. **Window motion.** Add the load/evict policy at the boundary; witness with a
   test that a window translated by one chunk agrees with `gen` on the overlap.
5. **Dirty set.** Widen the mask; witness the support order and the active-set
   invariant.
6. **Retire the torus laws.** `index_roundtrip`, the parity laws over the torus
   `Grid`, `step_m`/`sup_m` become mirrors of a shape that no longer exists.
   Per `AGENTS.md` this is a *retirement*: keep the laws, mark them retired with
   the retiring entry, and say in `PLAN.md` §4.1 that they are no longer
   evidence.

Steps 2–6 are the risky ones and are **not** landed here. The downgrade
protocol applies: if a step cannot stay green, stop at the last green step and
file the gap.

## 6. Gap candidates (for `PLAN.md` §5.3)

- **`G-scale-1` (unproven).** `Grid.step_inside` conflates "off the window" with
  "off the world". A moving window needs a load-on-demand rule (or a window
  margin) so a rule target just outside the resident set is not silently inert.
  *Gates:* arbitrary-coordinate simulation. *Closes by:* a window-margin
  invariant plus a law/test that every `Rules.plan` target of a resident cell is
  resident or explicitly loaded.
- **`G-scale-2` (unproven).** `Dirty.Mask` is exactly 64 `y` rows; a window needs
  a window-sized mask (or per-chunk dirty set). *Gates:* window motion.
  *Closes by:* a size-parameterised mask and the `mark_wake` reach invariant.
- **`G-scale-3` (unproven).** The `cw` split/rejoin identity
  `(x>>4)<<4 + (x&15) == x` (for `x < 16384`) is test-witnessed (T57–T60) but not
  proven. *Gates:* coordinate soundness of the migrated engine. *Closes by:* a
  bit lemma over the `Bits`/`Word` model, analogous to `Bits.model_index_rt`.
- **`G-scale-4` (unproven).** The resident set is implicit in the
  `assemble_go` loop bounds; a window needs an explicit set and a load/evict
  policy with no double-residency or leak. *Gates:* memory/scale. *Closes by:* a
  set model plus `assemble`/`evict` roundtrip laws.
- **`G-scale-5` (performance) — reframed.** This candidate was mis-stated. `C3`
  already makes the tick cost track disturbance; the real cost modes are (a) the
  one-time build transient from the missing ground (`G-scale-9`: the shell-free
  live build flags ~80k cells active — measured 80,438 — and crushes the
  boundary) and (b) seam/frame cost (first `DELTA`, per-`FOCUS` sparse
  `SNAPSHOT`). *Gates:* live usability. *Closes by:* a grounded build (no
  transient) plus a render-horizon vs simulation-window frame measurement.
- **`G-scale-6` (retirement).** Every law that mentions `Grid.index`/`Grid.ix`
  is a law about the torus; migrating the live path orphans them. *Gates:*
  traceability. *Closes by:* the retirement protocol in `AGENTS.md` (keep, mark
  retired, update §4.1) — not by deleting or silently weakening them.

## 7. Non-goals

- No GPU / `!` work (that is `M7b`/`M7e`, `G4`).
- No change to the rule system, the write algebra, or the conservation/Φ laws —
  the window is a coordinate and residency change, not a semantics change.
  **Correction:** decision A (A.120, serving the shell-free live window) *was* a
  semantics change riding inside this migration — it removed the shell, which was
  the world's **ground**, not just its boundary. That violation is the source of
  `G-scale-9`; the coordinate/residency discipline still holds for everything
  else.
- No refactor of the live `Grid`/`Sim` path in steps 1–6 (this note's §5).
  §8 scopes the live migration (steps 7+) **explicitly**: the same
  coordinate/residency discipline, one gate-green slice at a time.

## 8. Handoff — the live rule migration (S1 endgame, fresh-session brief)

Steps 2–4 (the model: `Window`, explicit resident set, generator selector,
window-local addressing, motion primitives, window-edge shell (a *renderer*
boundary hint — wrong as the sim's ground, `G-scale-9`), the store load/evict
policy) and the `G-scale-2` item (3) isomorphism are landed
(A.95–A.109). **W1 is landed (A.110):** `src/wgrid.bend` is the window-local
coordinate seam (`wgrid_index`, `wgrid_ix/iy/iz`, and a window-parameterised
`wgrid_neighbor`/`wgrid_step_inside`), and the resident `Window` is threaded
through `Ops`/`Rules`/`Support`/`Sim` (canonical-only: the bodies still delegate
to `Grid`, so every proof/test stands). What remains is the **rule migration**:
moving the live tick pipeline off the fixed `Grid` torus onto a window. §7 stays
binding for coordinates and residency — **except** that decision A (A.120) crossed
it by changing the live world's material (removing the ground, `G-scale-9`).

**State (verify with `bend_status` / `bend_audit` first).** Gate green, 139 laws,
fast 149/149, sim 40/40, gaps 6 open / 13 closed. Relevant landed API:
`src/window.bend` (`Window`, `win_index`, `win_lx/ly/lz`, `win_gx/gy/gz`,
`shift`, `entering`/`leaving`), `src/store.bend` (`assemble_w`, `window_store`),
`src/winshell.bend` (`win_border`/`gen_at` — renderer boundary hint only,
*not* the sim ground, `G-scale-9`), `src/maskword.bend` + `src/wordnat.bend`
(`mask_word_get`), `src/dirtyn.bend` (size-parameterised mask + wrap range).

**The seam.** The write algebra (`Refine`/`PT`, the Φ/count laws), the phase
fold, and `Support` all work on flat `Array<U32>` indices plus the `Grid` map.
Only three things assume the box: (i) `Grid.index`/`ix/iy/iz` (the coordinate
map), (ii) `Grid.neighbor` (torus wrap) and `Grid.step_inside` (box edge), and
(iii) sizes (`Grid.volume`, `active_list`, `Worldgen.build`, the 64-row
`Dirty.Mask`). The write algebra is size-agnostic and is reused verbatim.

**Contract for every slice.** The canonical window (`Window.canonical()`)
reproduces today's `Grid` behaviour bit-for-bit (`win_index == Grid.index` is the
law `win_canonical_index`, A.105), so each slice keeps the gate green and every
existing law/test standing until the retirement slice. Land one slice at a time;
each must be gate-green + fast + sim before the next.

### W1 — window-local coordinate map (`WGrid`), canonical-only — **landed (A.110)**
`src/wgrid.bend`: `wgrid_index w x y z = Window.win_index w x y z`,
`wgrid_ix/iy/iz` (via the `win_g*` inverses), and a window-parameterised
`wgrid_neighbor`/`wgrid_step_inside` (plus `wgrid_below`/`above`/`west`/`east`/
`south`/`north`). The resident `Window` is threaded through
`Rules`/`Support`/`Ops`/`Sim`; the live entry points (`tick`, `ticks`,
`tick_trace`, `wake`, `side_sel`, …) are wrappers over `Window.canonical()`, and
`tick_w`/`ticks_w`/`tick_trace_w` take the window explicitly (for W2/W5). W1 is
**canonical-only**: `wgrid_neighbor`/`wgrid_step_inside` delegate to `Grid`, so
the seam is transparent. *Evidence:* gate green; fast 118/118, sim 25/25; law
`wgrid_canonical_index` (delegating to `g7_win_canonical_index`); T122–T125.

### W2 — window-local neighbour + the margin rule (`G-scale-1`) — **landed (A.111)**
`src/wgrid.bend` now makes the guard explicit: `wgrid_axis_ok` is the per-axis
residency test, `wgrid_step_inside` is written in `Window` terms (definitionally
`Grid.step_inside`), and `wgrid_resident`/`wgrid_target_resident` are the
model-side predicates. New `src/wmarg.bend` proves the bit brick
(`wmarg_mask6_high_zero`), the per-axis margin (`wgrid_axis_guard`: in-frame ⇒
guard `True`), the three-axis `wgrid_step_margin`, and the canonical residency
bridge (`wgrid_canonical_resident`). Laws `wgrid_step_margin`/
`wgrid_canonical_resident`; T126 (exhaustive over the guard's finite domain) /
T127 (moved-window faces). Runtime semantics are unchanged (canonical guard is
bit-identical to `Grid.step_inside`). **Residual:** the driver's chunk margin
(`active ⇒ in-frame target`) is `W5`; the converse (guard ⇒ resident) is
exhaustively witnessed, not a law.
*Files:* `Rules`, `Support`, `WGrid`.

### W3 — live dirty-set rewire (step 5 item 1, `G-scale-2`) — **landed (A.118)**
Replace the two-`U32` `Dirty.Mask` with `Dirtyn` at the window's row count. For
the 64-row canonical window this is an equivalence: `mask_word_get` (A.109) is
exactly the bridge, and the `mark_wake` wrap range is `nat_mod_lt`/`dwin_up_lt`
(A.104). When the window edge becomes `2^n` the mask generalises. *Files:*
`src/dirty.bend`, `src/sim.bend`. *Evidence:* fast/sim unchanged; transparency by
`mask_word_get`.

**Status (A.118).** Landed. `Dirty.Mask` holds `Mask{w: Word(64n)}`, the row ops
delegate to `Dirtyn`, the `Word(64)` constructor sits below `dirty` (in
`src/dirtyn.bend`), and `mask_word_get` is definitional. The first attempt (A.117)
hung the native sim at T4b; the cause was a **performance cliff**, not a logic
bug — `active_mask`'s per-cell `mark_if` forced a 64-step `Word.or` for every
scanned cell (262144/tick, ~838M nodes over `settle(50)`). The fix accumulates
the canonical two-`U32` limbs natively during the prime scan and materialises the
`Word(64)` once. Canonical behaviour is bit-identical; native sim 40/40 in ~13 s;
fast T156/T157/T166. `G-scale-2` item 1 closed.

**Implementation note (A.111 — the blocker to plan around).** The rewire is not
purely local: `src/maskword.bend` imports `src/dirty.bend` (it is *about*
`Dirty.Mask`), so `dirty.bend` cannot call `Maskword.mask_word` — a cycle. The
rewire therefore needs the `Word(64)` constructor (`cat`, `u32_word`, and the
`mask_word` split) moved *below* `dirty` (into `src/dirtyn.bend`, which imports
only `nat.bend`), with `maskword.bend` re-exporting/using it. Once `Dirty`'s
`is_dirty_y`/`or_y`/`mark_wake` delegate to `Dirtyn` on that word, the
`u32_word_bit`/`mask_word_get` laws become *transparent* (likely `{==}`): the two
representations are the same, so A.107/A.109's development is superseded, not
re-proved. That is a **retirement-style simplification** and must be logged per
`AGENTS.md` (keep the laws, mark them transparent/superseded, update §4.1) — and
the `wordnat` proofs that pattern-match `Dirty.Mask{lo, hi}` must move with the
representation. Land it as its own slice; do not fold it into W4/W5.

### W4 — power-of-two window sizing
A window of edge `2^m` cells is a `2^{3m}` array; the `PT`/`Refine` machinery
(`swap_ref`, `g5_twidth`) is size-agnostic, so the write algebra needs nothing.
Parameterise the size assumptions: `active_list`/`dirty_todo` scan bounds,
`Worldgen.build*` (already coordinate-indexed), and the `[0 : U32^18n]` array
literals in `Store`. *Evidence:* gate + a 32³ or 128³ window test.

### W5 — live motion driver (`G-scale-8` wiring; closes `G-scale-5`) — **driver landed (A.112)**
`src/sim.bend` now carries the pure `w5_` driver: `w5_move` (`Window.shift` +
`Store.window_store`), `w5_checkpoint` (array→store inverse of `Store.assemble_w`,
gathering resident chunks in `Chunk.local` order via `Window.win_index`),
`w5_step` (move → assemble → `Sim.ticks_w` → checkpoint, preserving ticked
overlap state across a move), and `w5_trace_step` (same + accumulated
`List<Sim.Delta>` with global coordinates). Fast T130–T134 (tick-free) and
native T135–T139 (moved-window tick vs canonical, global deltas, state across a
move). **Residual:** the fixed-window live link is landed (`runners/serve.bend`,
A.115), the **moving-window focus protocol** (renderer-supplied focus →
`w5_trace_step`) is landed (A.117, native witness A.118), and the live link now
serves the **shell-free window** (A.120, `w5_*_sel` + `Worldgen.terrain()`), so
`--live` no longer draws the absolute bedrock walls. **Correction (`G-scale-9`):**
shell-free removed the *ground* along with the walls, so the live build is born
fully awake (~80k active cells); the fix is a **world-fixed ground**, not a
window-edge shell. `G-scale-5` was also mis-stated — the cost is the build
transient plus seam/frame cost, not a sustained phase fold (see §6). The move is
now **lossless** (A.114, `Store.move_store`).

### W6 — retirement (`step 6`, `G-scale-6`)
Once the live path no longer mentions `Grid.index`/`Grid.ix` (W1–W5), those laws
are torus laws about a shape off the live path. Follow `AGENTS.md`: keep each law,
mark it retired with the retiring entry, and state in `PLAN.md` §4.1 that it is no
longer evidence. Never delete or silently weaken. If the canonical window stays
the default address space, some `Grid` laws may remain valid evidence for the
reference mode — decide per law.

### W7 — the world-fixed ground (`G-scale-9`) — **the new frontier, and what `S1` ends on**
The shell-free live window has no ground, so `Support` has no base case: the live
build is born fully awake (~80k active cells; measured 80,438) and its material
differs from the renderer's generated backdrop until one tick clears it (A.121).
The **window-local shell** (`src/winshell.bend` `gen_at`) was the wrong fix — a
floor that follows the camera — and is **retired (A.123)**. The right fix: a
ground that is a **property of the world**, sampled by a pure world-coordinate
function, so the renderer reproduces it and the served window is born settled.
Choose the form (world-fixed bedrock plane / fixed-`y` boundary rule / void), make
`Support.sup` ground against it (the boundary means "can't move *and* holds you
up"), re-point the live link at the grounded sampler, and regenerate the `.bgt`
oracle. *Files:* `src/worldgen.bend`, `src/support.bend`, `runners/serve.bend`,
`runners/export.bend`.

### Independent pieces (safe worker tracks, no live-path edits)
- `G-scale-4` residual: the `assemble`/`evict` roundtrip law (`Array` update
  identity under `G5` + a proof-relevant `is_eq` eliminator).
- `A.109` residual: the `Word.inc` value lemma and explicit `to_nat`/`from_nat`
  roundtrips (T110/T116 witness them; only the `inc` brick is missing).
- `G-scale-1`'s margin *model* lemma, before W1 threads it.

**Before starting W1:** read `AGENTS.md` (retirement + downgrade protocols,
parallel-track rules). W1 is one writer; the independent pieces above are the
only safe parallel tracks.
