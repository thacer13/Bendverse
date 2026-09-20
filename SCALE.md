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
  Loading is `gen`; eviction is the existing sleeping + gen-equal test, which is
  already lossless.
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
- **`G-scale-5` (performance).** `Sim` primes the work list by scanning the whole
  world; at scale the scan is the window (bounded), but the phase fold's
  cost still scales with the active set, not the window. *Gates:* the scale
  target. *Closes by:* measurement on a real window, not a proof.
- **`G-scale-6` (retirement).** Every law that mentions `Grid.index`/`Grid.ix`
  is a law about the torus; migrating the live path orphans them. *Gates:*
  traceability. *Closes by:* the retirement protocol in `AGENTS.md` (keep, mark
  retired, update §4.1) — not by deleting or silently weakening them.

## 7. Non-goals

- No GPU / `!` work (that is `M7b`/`M7e`, `G4`).
- No change to the rule system, the write algebra, or the conservation/Φ laws —
  the window is a coordinate and residency change, not a semantics change.
- No refactor of the live `Grid`/`Sim` path in this track.
