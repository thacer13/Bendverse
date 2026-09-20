# Bendverse — History

AI milestone log: one entry per landed step, newest last. This file
was `PLAN.md`'s Appendix A until the v2 rewrite; `PLAN.md` is now the normative
plan and this file is the record of how the implementation got there.

Entry **bodies are immutable** — never rewrite what an entry claimed. When a later
entry **corrects** an earlier claim ("that is wrong"), the earlier one gets a
one-line pointer at its top:

> **Superseded by A.n** — the claim or line that is wrong

That pointer is annotation, not a rewrite. Otherwise entries are **snapshots**: a
`Status`, law count, or "remains gated" line describes that moment, not today —
current state is `PLAN.md` §5 (landed/open) and §5.3 (gaps). `LAWS.bend` is
stricter still — a law's meaning is never changed; a correction is a new law.

The quote below preserves the original transition note; its "never rewrite in
place" rule now means *immutable bodies*, with the pointer above allowed.

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

### A.14 — V3a complete: y/z field extraction + all-axis neighbor parity

**Status:** V3a **complete** (§5 box checked). Continues A.13 (x-axis + parity bit model). New laws in `LAWS.bend`; `src/parity.bend` and `src/bits.bend` extended. Engine untouched; gate green; fast and simulation suites pass.

**What A.13 left open.** The y/z fields (bits 12–17 / 6–11 of the packed index) force `shr_n`, and `Word.shl`/`Word.shr` are pattern-match definitions that get *stuck* on the symbolic `Word.and(u, mask(n,6))`. `{==}` cannot close the extraction; a shift/mask induction library is required.

**Deliverables (`src/bits.bend`, general shift lemmas)**
- `shr_pad_and` / `shr_and`: one-step `shr` distributes over `and` (pointwise, via `shr.pad`).
- `shr_n_and` / `shr_n_or` / `shr_n_zero`: iterated versions (the `or` form restates Base `shl/shr` distributivity at `shr_n`).
- `shr_pad_shl_put` / `shr_shl_one`: the one-step shift-cancel `Word.shr(Word.shl(w)) == Word.and(w, mask(n, n-1))`, proved via a padded helper rather than a direct induction.
- `and_ones`: `Word.and(w, mask(n,n)) == w`.

**Deliverables (`src/parity.bend`, clear-top mask library)**
- `kmask(k)` — the recursive "top k bits cleared" mask (`kmask(0)` all ones, `kmask(1+q)=shr(kmask(q))`), with `mask31_eq_kmask1`, `shr_kmask`, `shr_kmask1`, `kmask_nest`, and the concrete `kmask(6) = mask(32,26)`, `kmask(12) = mask(32,20)`.
- `shr_shl_kmask(k, X)`: **the spike that unblocked V3a** — `shr_n(k, shl_n(X,k)) == and(X, kmask(k))` for arbitrary `X`. Induction uses `shr_shl_one` + `shr_n_and` + `shr_kmask` + `kmask_nest`, and works because the clear-top masks nest (`kmask(k+1) ⊆ kmask(k)`).
- `shr_shl66` / `shr_shl1212`: the masked-aligned cases `shr_n(k, shl_n(and(u,6),k)) = and(u,6)` for k = 6, 12.
- `pack6`; `mid6_pack` (`and(shr_n(pack6,6),6) = and(z,6)`) and `high6_pack` (`shr_n(pack6,12) = and(y,6)`), assembled from `shr_n_or`, the aligned cancellations, and the "shifted-out contribution is zero" facts (`shr126_low6_zero`, `shr6_high_zero`).
- U32 lifts `u32_index_iz` / `u32_index_iy` and `u32_iz_neighbor` / `u32_iy_neighbor`, mirroring `u32_ix_neighbor`.
- `neighbor_z_par` / `neighbor_y_par`: `par32(iz(neighbor(i,0,0,dz))) == xor(par32(iz(i)), par32(dz))`, likewise y.

**Laws appended (21 total; existing laws untouched)**
- `neighbor_y_parity`, `neighbor_z_parity` (x was `neighbor_x_parity` in A.13). Runtime twin **T10** extended to all three axes (4096 samples).

**Why V3a is now complete.** The phase color is exactly `(x&1) | ((y&1)<<1) | ((z&1)<<2)`, i.e. the three coordinate parities; `neighbor_*_parity` says an odd delta in an axis flips that axis's color bit. Since every 26-neighbor differs by `±1` in some coordinate and `par32(±1) = True`, any two 26-neighbors differ in at least one color bit. Same-color cells therefore cannot be 26-neighbors, which is the non-adjacency premise behind the §2.4 phase argument and §2.5 single-writer tie-break. (The corollary "color words differ", from a differing parity bit, is the immediate contrapositive of `Equal.cong`; no packed-component reasoning is needed.)

**Process note.** This was executed exactly as sharded in A.13/A.14 planning: YZ-0 and YZ-1 (distribution + mask-to-zero) landed and committed first; YZ-2's shift-cancel was treated as an isolated spike in a throwaway `scratch.bend`, and the clear-top `kmask` route closed it before any extraction work began. The stop rule (fall back to a documented gap if the spike stalled) was not needed.

**Verification**
- `bend PROOF.bend` → `All terms check.` (21 laws).
- `bend src/parity.bend` / `bend src/bits.bend` → `All terms check.`
- `bend app/tests.bend` (JS, tick-free) → all PASS incl. T10, ~1.2s.
- Native `bend app/simtests.bend -o bin && ./bin` → T1, T2, T3, T4, T4b, T9 all PASS. Engine untouched.

**Recommended next:** **V3b** (priority is total and local: unique scan-order winner among same-phase movers, comparison radius ≤2), then **M7a** (parallel worldgen) per the A.12 interleave.

### A.15 — V3b in progress: V3b-0 modular-add core

**Status:** V3b **partial** (§5 box unchecked). New `src/mod.bend`; **1 new law** (22 total). Engine untouched; gate green; fast and simulation suites pass.

**What V3b needs, and what Base lacked.** Locality ("comparison radius ≤2") turns a common destination into a bound on the sources: per axis, two sources `i, j` targeting the same cell satisfy `φ_b(y) = φ_a(x)` where `φ_k(z) = and(z + k, 63)` and `a, b ∈ {−1, 0, +1}` (the move offsets). Recovering `y` from that needs the ±1-translation inverse, i.e. "add 1 then add −1 is the identity mod 64". Base has no `Word.add` associativity, no `Word.sub` semantics, and no mask/add interaction lemmas, so a small modular-add layer was required. (General add associativity is **not** needed — only the concrete ±1 cancels — which keeps the shard bounded.)

**Deliverables (`src/mod.bend`)**
- `lowadc(k, a, b, c)`: **the crux** — masking the sum `a + b` (with carry-in `c`) to its low `k` bits equals masking the *inputs* to `k` bits first. Proven by induction on the word, with the 8-way ripple carry case split used in Base's own `Word.add_comm`. `and_mask0` handles the `k = 0` branch.
- `one` / `ones`; `add_zero` (`a + 0 = a`); `addc_ones_true` (`a + (−1) + 1 = a`, one induction).
- `add_one_eq` (`a + 1` equals the carry-in-one form, by reduction). This aligns the recursion so the cancel lemmas close.
- `add_one_ones` (`(a + 1) + (−1) = a`) and `add_ones_one` (`(a + (−1)) + 1 = a`): the ±1-translation inverses, by structural induction (each branch uses one prior lemma; no general associativity).
- `low_mask_absorb_w` / `low_mask_absorb`: **the reusable form** — `and(and(x,63) + w, 63) = and(x + w, 63)`. Assembled from `lowadc` and `w_and_absorb`; this is what lets locality strip a mask before applying a cancel.
- `low6_add_indep` (U32 lift): the law below.

**Law appended (`LAWS.bend`; existing laws untouched)**
- `low6_add_independent` — `and(a + b, 63) = and(and(a,63) + and(b,63), 63)`. A runtime twin was added to `app/tests.bend` as **T11**, which also checks the two ±1 cancels over 4096 samples.

**Torus caveat (recorded for M7d).** "Radius 2" holds on the **torus**: e.g. `x = 0` and `x = 62` both target `x = 63`, so a parallel halo around a region must **wrap**, and raw index distance is not the metric.

**Honest remaining for V3b**
- **V3b-1 locality**: per-axis `φ` inverse over an enumerated `Dir` (`0 / +1 / −1`), then the radius-2 statement assembled coordinate-wise via `u32_ix_neighbor` and the index roundtrip. No new bit arithmetic expected — V3b-0 is the dependency.
- **V3b-2 totality/uniqueness**: `U32.cmp`/`is_lt` is a total order, so a nonempty candidate set has a unique least scan-order index (the winner); losers observe it occupied.

**Process note.** Per AGENTS, the risky piece (`lowadc`) was spiked in a throwaway `scratch.bend` before any module work; it closed in one iteration, so the shard proceeded rather than downgrading. The two cancel lemmas needed a few term-shaping passes (Bend's `{==}` is definitional, so the inner `add a one` had to be rewritten explicitly through `add_one_eq`). The scratch file was removed before commit.

**Verification**
- `bend PROOF.bend` → `All terms check.` (22 laws).
- `bend src/mod.bend` → `All terms check.`
- `bend app/tests.bend` (JS, tick-free) → all PASS incl. T11, ~1.2s.
- Native `bend app/simtests.bend -o bin && ./bin` → T1, T2, T3, T4, T4b, T9 all PASS. Engine untouched.

**Recommended next:** **V3b-1** (co-target locality / radius-2), then **V3b-2** (total order + unique winner); the A.12 interleave then goes to M7a.

### A.16 — V3b in progress: V3b-1a per-axis `Dir` cancellation

**Status:** V3b still **partial** (§5 box unchecked). New `src/priority.bend`; `src/mod.bend` gained three U32 wrappers; **1 new law** (23 total). Engine untouched; gate green; fast suite passes (T12 added).

**Why this split.** A.15 left "locality" as V3b-1. Executing it, the axis arithmetic and the packed-index assembly turned out to be separable, so V3b-1 is being landed as **1a** (per-axis translation cancellation) and **1b** (index-level radius-2 assembly). 1a is done here.

**Deliverables (`src/priority.bend`)**
- `Dir` (`Dno` / `Dup` / `Ddn`), `dir_val` (0 / 1 / 0xFFFFFFFF), `dir_neg` (the additive inverse per axis), and `phi(d, x) = and(x + val(d), 63)`.
- `phi_cancel(d, x)`: **`phi(neg d, phi(d, x)) = and(x, 63)`** — advancing by one `{−1,0,+1}` step and then its opposite returns to the masked original. Proven per `Dir` from A.15's two cancels plus `low_mask_absorb`; `Dno` uses `add_zero` twice.
- `src/mod.bend`: U32 wrappers `u32_add_one_ones` / `u32_add_ones_one` / `u32_add_zero_r`.

**Law appended (`LAWS.bend`; existing laws untouched)**
- `dir_phi_cancel` — the per-axis cancellation above. Runtime twin **T12** checks all three `Dir` values over 4096 samples.

**Why this is the heart of locality.** A source targeting cell `d` sits one ±1/0 step from `d` in each axis. `phi_cancel` says that step is recoverable, so for a fixed destination the candidate sources are exactly its `{neighbor(d, u) : u ∈ Dir³}` (≤ 27 cells), and any two such candidates are within two steps in each axis — the **comparison radius ≤2** premise. The remaining work is to assemble this coordinate-wise result into the packed-index statement.

**Remaining for V3b-1b (index level).** Prove `Grid.neighbor(Grid.neighbor(i, d), neg d) == U32.and(i, 262143)` by combining `Parity.u32_ix_neighbor`/`u32_iy_neighbor`/`u32_iz_neighbor` with `phi_cancel`, then reassembling equal coordinates via the `index_roundtrip` def. This needs small mask-18 absorptions (`ix(and(i, 262143)) = ix(i)`, and the same for `iy`/`iz`) plus a "neighbor output is bounded" lemma; no new carry arithmetic.

**Verification**
- `bend PROOF.bend` → `All terms check.` (23 laws).
- `bend src/mod.bend` / `bend src/priority.bend` → `All terms check.`
- `bend app/tests.bend` (JS, tick-free) → all PASS incl. T11, T12, ~1.2s.

**Recommended next:** **V3b-1b** (packed-index radius-2 locality), then **V3b-2** (total order + unique winner); then M7a per A.12.

### A.17 — V3b complete: index-level locality + total scan order

**Status:** V3b **complete** (§5 box checked). `src/priority.bend` extended, new `src/order.bend`; **2 new laws** (25 total). Engine untouched; gate green; fast and simulation suites pass.

**V3b-1b (packed-index cancel).** The A.16 plan predicted the real work was mask-18 assembly; in fact the cleaner route needed **no boundedness lemma**. `Grid.neighbor` is definitionally `Grid.index(masked sums)`, so:
- Full-axis lemmas `u32_iy_neighbor_full` / `u32_iz_neighbor_full`: `iy`/`iz` of `neighbor(i, dx, dy, dz)` depend only on the matching offset and on `iy i`/`iz i` (lifted from `Parity.u32_index_iy`/`u32_index_iz`; `u32_ix_neighbor` was already full). These remove the off-axis offsets from the outer composition.
- `index_rebuild(i)`: `Grid.index(ix i, iy i, iz i) = and(i, 262143)` (the reusable form of the `index_roundtrip` law).
- Axis cancels `ix_cancel`/`iy_cancel`/`iz_cancel`: `and(and(x ∓ 1) ± 1, 63) = x` for an already-masked coordinate, from A.15/A.16. The `iy`/`iz` forms absorb against the shifted argument (`and63_absorb(U32.shrn(i, 12))` etc.).
- `neighbor_cancel`: **`neighbor(neighbor(i, d), −d) = and(i, 262143)`** — the packed-index statement that a source is recovered from its destination by the opposite step. Proof: rewrite each coordinate of the outer neighbor through the inner neighbor and the axis cancel, then `Equal.cong` the three `Grid.index` arguments into `index_rebuild`.

**V3b-2 (total scan order).** New `src/order.bend`. `cmp_fin_total` shows `Word.cmp.fin` returns one of `LT`/`EQ`/`GT` for any tail comparison (the `EQ` branch is the one 4-way `Bool` split), so the 32-bit comparison needs no induction: `cmp32_total` destructures one bit and delegates, and `u32_cmp_total` lifts. Law **`scan_order_total`**: `lt ∨ gt ∨ eq` is always `True`. Combined with locality, this is the "unique winner": for two *distinct* candidate indices `eq` is definitionally `False`, so a strict scan-order winner exists; `neighbor_cancel` bounds the comparison to the ≤27 cells `neighbor(d, Dir³)`, i.e. torus radius 2.

**Laws appended (`LAWS.bend`; existing laws untouched)**
- `neighbor_cancel`, `scan_order_total`. Runtime twins **T13** (six representative `Dir³` compositions over 4096 samples) and **T14** (totality over 4096 samples).

**Scope note (honest).** "Losers observe the target occupied" is the sequential fold's behaviour, not a separate theorem; V3b proves the two properties a parallel fold must respect — the candidate set is local (`neighbor_cancel`) and the order is total (`scan_order_total`). V3c (schedule invariance) remains the large, stall-prone shard.

**Verification**
- `bend PROOF.bend` → `All terms check.` (25 laws).
- `bend src/priority.bend` / `bend src/order.bend` → `All terms check.`
- `bend app/tests.bend` (JS, tick-free) → all PASS incl. T13, T14, ~1.3s.
- Native `bend app/simtests.bend -o bin && ./bin` → T1, T2, T3, T4, T4b, T9 all PASS. Engine untouched.

**Recommended next:** **M7a** (parallel worldgen) per the A.12 interleave, or **V3c** (schedule invariance) — but V3c gates only M7d, whereas M7a needs nothing new.

### A.18 — M7a complete: parallel worldgen (`build_at`)

**Status:** M7a **complete** (§5 box checked). `src/worldgen.bend` rewritten; no new laws (engine-only, as M7a predicts). Engine semantics unchanged; gate green; fast and simulation suites pass on native `--threads 1` and `--threads 6`.

**Deliverables**
- `src/worldgen.bend`: the sequential `build_go`/`build` (fill a fresh `[0 : U32^18n]` by index) is replaced by
  `build_at(depth, base)` — structural recursion on a `Nat` depth that builds the array tree directly: at `0n` an `ALeaf{gen(ix base, iy base, iz base, 42)}`, at `1n+ +p` the two halves
  `xs ys = build_at(p, base) build_at(p, U32.add(base, U32.shln(1, p)))` followed by `ANode{xs, ys}`. The `ALeaf` site at `base` is flat index `base`, so in-order leaves match the flat-index scan exactly. `build()` is `build_at(18n, 0)`. No array is ever shared: each half owns its subtree, so the linear-owner problem does not arise (M7a's whole point).
- `app/tests.bend`: **T8 strengthened** from a single spot check to an exhaustive check — every one of the 2^18 cells of `Worldgen.build()` is compared to `Worldgen.gen(ix, iy, iz, 42)`, the structural-refactor witness (in JS, which runs sequentially). Suite ~2.0s (was ~1.3s).

**Why the tree rewrite rather than indexed writes.** An `Array<U32>` is linear, so a parallel `build` cannot have two branches write one shared array. Recursing on the array's own `ALeaf`/`ANode` shape gives each parallel branch an independently owned subtree, and the tree shape from `[v : T^n]` already matches `Array.index`/`Array.get`'s `h = n/2` split, so leaf order is the flat index order. The first prototype (which recurred over an existing array, matching it) was discarded in favour of building the structure from `depth` — no dummy array, and the termination is structural on `depth`.

**Verification**
- Prototype (in a throwaway `scratch.bend`, removed before commit): `build_at(18n, 0)` equals the old sequential `build()` over **all** 2^18 cells (0 mismatches), confirming the tree/leaf-order assumption before the edit landed.
- Determinism / bit-for-bit: a 50× build-and-hash harness prints the identical `U32` under `--threads 1` and `--threads 6` (`1732778124`), so the parallel schedule does not perturb the world.
- Speedup (honest, small as A.12 predicted): the same 50× harness is 0.80s (`--threads 1`) → 0.48s (`--threads 6`), ≈1.7× wall for the build+hash mix; a single build is only a few ms, so `app/simtests.bend` total time is unchanged (~4.3s — the 8 phase folds dominate and are still sequential). "Smallest real speedup, zero semantic risk", as planned.
- `bend PROOF.bend` → `All terms check.` (25 laws); `bend src/worldgen.bend` → `All terms check.`
- `bend app/tests.bend` (JS, tick-free) → all PASS incl. exhaustive T8, ~2.0s.
- Native `bend app/simtests.bend -o bin && ./bin --threads 1` and `--threads 6` → T1, T2, T3, T4, T4b, T9 all PASS; T1's two builds share the parallel path and agree bit-for-bit.
- `bend main.bend -o bin && ./bin` prints the before/after ASCII collapse as before.

**Recommended next:** **M7c** (parallel render, clone-per-region; independent of movement) per the A.12 interleave, or **V2b-i** (`List.set` split/sum) if the scale track is paused. **M7b** (`!` GPU worldgen) still needs CUDA, which this machine lacks.

### A.19 — M7c dropped: render measured not worth parallelizing

**Status:** M7c **not implemented**, by explicit decision after measurement (human chose "Skip M7c, go to V2b-i"). §5 now records the drop. No code change for this entry.

**Measurement.** On native (`--threads 6`), a `view` (256×256 = 65536 pixels, reading the `z=32` cross-section from the 2^18 world) is **~1.2 ms**; 100 views + `build` + image hash run in 0.147 s. For context, a tick over an active collapse is **~20 ms** (20 spawn+ticks + hash in 0.43 s). Render is therefore ~6% of a frame while collapsing and near-zero once settled.

**Why this contradicts the A.12 expectation.** A.12 guessed "near-term wins from CPU forks (M7a/M7c)". M7a did give a real ~1.7× on `build`; M7c does not, because the render is already tiny relative to the tick and the only Bend-legal sharing strategy is clone-per-region, whose O(array) copy exceeds the ~1 ms it would hide. A slice-then-parallel variant was considered (extract the 4096-cell cross-section once, split, parallel-fill) but the ceiling is <1 ms saved for non-trivial plumbing and risk, so it was not built.

**Consequence.** Nothing depends on M7c: `view` is pure and does not touch world state, so dropping it weakens no claim and changes no output. M7b/M7e still need CUDA; M7d (parallel phase folds) is gated on V3c and is where the frame time actually is.

**Recommended next:** **V2b-i** (`List.set` split/sum), per the human decision.

### A.20 — V2b-i complete: `List.set` split and sum lemmas

**Status:** V2b-i **complete** (§5 box checked). **2 new laws** (27 total). Engine untouched; gate green; fast and simulation suites pass.

**Deliverables**
- `src/settle.bend`:
  - `pick_cons(h, a, b, c)` — `Bool.pick(c, h<>a, h<>b) == h <> Bool.pick(c, a, b)` (the congruence the split proof needs once the pick is stuck on a symbolic condition).
  - `set_append(l, r, n, v)` — **the split lemma**, stated *piecewise* so it is total and needs no hypothesis: `List.set(app(l,r), n, v)` equals `app(List.set(l,n,v), r)` when `n < len l`, else `app(l, List.set(r, n-len l, v))`, as a single `Bool.pick` over `Nat.is_lt(n, len l)`. Proved by induction on `l` with `n` matched in lockstep (`match l n` in binder order); both "runs off the end" cases are handled directly, and the recursive case is one `Equal.cong` under `h <> _` plus `pick_cons`. This is why no `i < len l` hypothesis (and no impossible-case elimination) is required.
  - `suml_cons_mid(l, x, r)` — `suml(app(l, x<>r)) == suml(l) + (x + suml(r))`, from `suml_mid(l,[x],r)` and `n_add_zero_right`.
  - `set_sum(l, x, r, v)` — **the sum lemma**: `(suml(app(l, v<>r)) + x) == (suml(app(l, x<>r)) + v)`, i.e. a point update changes the sum by exactly `x - v` (in `+`-form, so it feeds `replace_decreases` in V2b-iii). Reduces to the arithmetic `n_add_mid_swap` under `suml_cons_mid`.
- `src/nat.bend`: `n_add_mid_swap(L, x, v, R)` — `((L+(v+R))+x) == ((L+(x+R))+v)`, the pure-`Nat` reordering, proved with `n_add_assoc`/`n_add_comm`.
- `LAWS.bend` (appended): `list_set_split` (the piecewise `Set`/`Bool.pick` identity) and `list_set_sum`.
- `PROOF.bend`: both delegate to the module lemmas.
- `app/tests.bend`: **T15** runtime twin — the split formula over `n = 0..6` on `[10,20,30,40] ++ [50,60]` (including indices past both halves, exercising the "unchanged" out-of-range behaviour) and the sum identity on a sample.

**Bend findings (V2b-i)**
- **Prove the piecewise form, not a conditional.** The natural statement `i < len l ⇒ set(app(l,r),i,v) = app(set(l,i,v),r)` needs the impossible `l = Nil` case eliminated; stating it as `Bool.pick(is_lt(i,len l), left, right)` makes every case reachable and the proof a clean lockstep induction. Bound discharge moves to V2b-ii (where `U32.is_lt(i,h)` is known).
- **Binder order for multi-scrutinee induction.** A nested `match l` inside `match n` is rejected ("match scrutinees in binder order"); use one `match l n:` with combined patterns. The first matched binder is the termination measure, so the recursive call passes the structural tail.
- **The `+` in list literals.** A local `+xs = [...]` cannot infer the list quantifier; route literals through helper defs with a declared `+List<Nat>` return type. `+v = 99n` similarly needs `{99n : Nat}`.
- A recurring transcription hazard: `List<&2, Nat>` vs `List<&2, Nat)` (a stray `)` for `>`) yields a misleading "expected a term, observed ')'". Verified against a working scratch before porting.

**Why this unblocks V2b-ii.** The remaining `Array.set`/`to_pots` wall (A.10) at an `ANode` halves the list as `app(to_pots(xs,…), to_pots(ys,…))`; the RHS `List.set(P, i-base, v)` then needs exactly this split, and the matching index/length facts (`len(to_pots(xs,…)) = h`, `Nat.is_lt(·,·) ↔ U32.is_lt(·,·)`) are the "bound reasoning" V2b-ii owns.

**Verification**
- `bend PROOF.bend` → `All terms check.` (27 laws); `bend src/settle.bend` and `bend src/nat.bend` → `All terms check.`
- `bend app/tests.bend` (JS, tick-free) → all PASS incl. T15.
- Native `bend app/simtests.bend -o bin && ./bin` → T1, T2, T3, T4, T4b, T9 all PASS. No engine code touched.

**Recommended next:** **V2b-ii** (`Array.swap.go` ↔ `to_pots`), the risky tree induction; the split lemma plus a `len(to_pots) = n` and a `Nat`/`U32` comparison correspondence are its dependencies.

### A.21 — M8a complete: chunk key/index + pure per-chunk gen

**Status:** M8a **complete** (§5 box checked). New `src/chunk.bend`; **no new laws** (golden test only — see below). Engine untouched; gate green; fast and simulation suites pass.

**Interpretation chosen.** M8's acceptance is "chunk gen + tick identical to fixed-world behavior on the same region", so M8a **chunks the existing 64³ world** rather than changing `gen`'s semantics for an unbounded world. Per-chunk gen calls the same pure `Worldgen.gen` on **global** coordinates, so a chunk reproduces its region of `Worldgen.build()` exactly (T8 already proves `build == gen` cellwise). Generalizing `gen` for a true infinite world (drop the x/z/63 side shells, keep the y=0 floor) is deliberately deferred; it is a model change, not a key/index one.

**Deliverables (`src/chunk.bend`)**
- `size() = 16`, `bits() = 4n`, `cells() = 4096`, `per_axis() = 4` (64³ = 4³ chunks of 16³).
- `local(x,y,z) = x | (z<<4) | (y<<8)` and decoders `local_x/y/z` — the 12-bit chunk-local flat index, mirroring the world's `index`/`ix/iy/iz` shape at 4-bit width.
- `key(cx,cy,cz) = cx | (cz<<10) | (cy<<20)` with decoders `key_x/y/z` — **10 bits per axis** (30 usable bits), i.e. up to 1024³ chunks, leaving room for a genuinely large world beyond the 4³ used today.
- `global_x/y/z(k,i)` — the local → global coordinate map (`chunk_coord*16 + local`), and `gen_local(k,i) = Worldgen.gen(global…, 42)`.
- `build_at(depth, base, k)` / `build(k) = build_at(12n, 0, k)` — the M7a structural parallel build pattern (a 4096-leaf tree, `ALeaf` at flat local index `base`), so chunk gen is parallel with no shared linear state.

**Golden test (`app/tests.bend`, T16)**
- `key ∘ (key_x,key_y,key_z) == id` on 30 bits, 4096 sampled keys.
- `local ∘ (local_x,local_y,local_z) == id` on 12 bits, 4096 sampled values.
- For 8 chunks (all corners plus interior/mixed keys): every one of the 4096 cells equals `Worldgen.gen` at its global coordinate — 32768 cells, validating the local/global decomposition and leaf order. Combined with T8 (`build == gen`), this gives chunk-region equality with the fixed world.

**Why no law.** A chunk-key roundtrip is the same bit shape as `index_roundtrip`, but at **10-bit** fields, while the `src/bits.bend` model is specialized to the 6-bit masks/shifts (`mask(32,6)`, `shl/shr` by 6 and 12). Re-proving the mask/shift library at width 10 would be real work for a claim §3 classifies as a golden test ("simulation-level properties … not laws"). Recorded here rather than silently omitted; can be promoted to a law later by parameterizing the bit model over the field width.

**Verification**
- `bend PROOF.bend` → `All terms check.` (27 laws); `bend src/chunk.bend` → `All terms check.`
- `bend app/tests.bend` (JS, tick-free) → all PASS incl. T16, ~2.05s.
- Native `bend app/simtests.bend -o bin && ./bin` → T1, T2, T3, T4, T4b, T9 all PASS. No engine code touched.

**Recommended next:** **M8b** (radix-tree chunk store keyed by the packed `U32` chunk key; not `Map`, which is string-keyed), then **M8c** (region tick equivalence). Both are independent of V2b-ii; **M8d** (sleeping/eviction) remains gated on V2b.

### A.22 — M8b complete: U32-keyed radix-tree chunk store

**Status:** M8b **complete** (§5 box checked). New `src/store.bend`; **no new laws** (data structure — runtime test only). Engine untouched; gate green; fast and simulation suites pass.

**Design.** A persistent binary radix trie over the **32 key bits**, `Store is Data` (`STip{}` / `SLeaf{key: U32, val: List<&2, U32>}` / `SNode{lo, hi}`). Chunk keys are the M8a packed `U32`s, so no string hashing and no `Map` (which is string-keyed). Values are `List<&2, U32>` (Data) rather than `Array<U32>`, deliberately: it makes the store itself **copyable**, so `get` is a pure lookup that does not consume the store — which M8c needs in order to read a chunk's neighbors (halo) without popping them. Array↔list conversion happens at the call site (`Store.chunk_list`, via `relist`).

**Bend constraint that shaped it.** The natural implementation — recurse on a `Nat` bit-depth, and branch on the key bit through a small helper that matches the computed `Bool` — is **mutually recursive** (`set` → helper → `set`), which Bend rejects ("expected a defined name" on the forward reference). The working formulation walks the key as a `Word`: `set_w(n, w, s, k, v)` matches `n` (a `Word(n)` is the type family `Word.Nil`/`Word.Con`, so the `Nat` must be matched first), then `match w: case WCon{head, tail}`, branches on `head` (a pattern binder, so a legal scrutinee), and recurses on the structural `tail`. One recursive def, structural termination, no computed-value match, no helpers.

**Deliverables (`src/store.bend`)**
- `empty()`, `set(s, k, v)` (persistent overwrite/insert), `get(s, k) -> Maybe<&2, List<&2, U32>>`, `relist`/`chunk_list` (`Array<U32>` → Data list via `Chunk.build`).
- Insertion builds the single-child spine down to the 32-bit leaf; the "leaf met above depth 0" case is impossible by construction and handled defensively.

**Golden test (`app/tests.bend`, T17)**
- Seed a store with the 8 `chunk_keys()` (all corners plus interior/mixed — exercising shared prefixes); each `get` returns the full 4096-cell list equal to `Chunk.chunk_list(k)`.
- An unstored key (`key(2,2,2)`) returns `None`.
- Overwrite `key(0,0,0)` with another chunk and confirm the new value reads back.

**Bend findings (M8b)**
- `Word(n)` is a **type family**: matching `WNil{}`/`WCon{}` requires matching the `Nat` first (`match n: case 0n: … case 1n+p: match w:`). Threading the `Nat` and recur`.
- A `Data` field cannot hold `List<U32>` (that defaults to the linear `&1` list, i.e. `Type`); use `List<&2, U32>`.
- An imported type is qualified by the module alias in a consumer: `Store.Store`, not `Store`.
- `match` on a returned `Maybe` is a computed scrutinee — route it through a helper that matches the parameter (same workaround as elsewhere).

**Scope note.** M8b is a *store*, not yet a region engine: it does not assemble halos, run `Sim.tick`, or scatter results. That is M8c (`region tick equivalence`), which is independent of V2b; only M8d (sleeping/eviction) remains gated on V2b.

**Verification**
- `bend PROOF.bend` → `All terms check.` (27 laws); `bend src/store.bend` → `All terms check.`
- `bend app/tests.bend` (JS, tick-free) → all PASS incl. T17, ~2.28s.
- Native `bend app/simtests.bend -o bin && ./bin` → T1, T2, T3, T4, T4b, T9 all PASS. No engine code touched.

**Recommended next:** **M8c** — region tick equivalence: assemble the fixed world from the store into an `Array<U32>`, run `Sim.tick`, compare to `Sim.tick` on `Sim.build()`, and (optionally) scatter back into the store.

### A.23 — M8c complete: chunk-store assemble + tick equivalence

**Status:** M8c **complete** (§5 box checked). `src/store.bend` extended; **no new laws**. Engine untouched; gate green; fast and simulation suites pass.

**Interpretation (scope, honestly).** "Region tick equivalence" is implemented as **representation equivalence under the tick pipeline**, not independent per-chunk ticking: the chunked world is gathered back into an `Array<U32>`, and that world is shown to equal the fixed-world build and to evolve identically through `Sim.tick`. Independent per-region ticking (a chunk + halo ticked in isolation) is **not** claimed and would need **V3c** (schedule invariance) to be sound — the sequential scan order and §2.5 tie-break are global. So the non-gated M8 work stops here; only **M8d** (sleeping/eviction) still rests on V2b.

**Deliverables (`src/store.bend`)**
- `assemble(s) -> Array<U32>` — gather: `assemble_go` walks the 64 chunk coordinates (decoded from a single `ci = 0..63`), `assemble_cells` matches the `get` result, and `assemble_chunk` walks each chunk's local-ordered list writing `world[Grid.index(global…)] <- cell`. All three are tail-recursive (fuelled), so JS does not blow its stack.
- `build_all() -> Store` — `put_all_go` inserts all 64 chunks (`chunk_list ∘ key`) — the canonical chunked world, used by both suites.

**Tests**
- `app/tests.bend` **T18**: `assemble(build_all())` equals `Worldgen.build()` cell-for-cell. The comparator is a **tail-recursive** mismatch count (`list_cmp_go`) — the obvious non-tail `list_eq` over 262144 elements overflows the JS stack (`memory fault`).
- `app/simtests.bend` **T18** (native): (a) `Support.pass_all(assemble(build_all()))` equals `Sim.build()` cell-for-cell; (b) `Sim.spawn` + 10 ticks on the assembled world equals `Sim.spawn` + 10 ticks on `Sim.build()`, bit-for-bit. This closes "chunk gen + tick identical to fixed-world behavior".

**Bend findings (M8c)**
- `U32.shrn` shift amounts are `Nat`: use `2n`/`4n`, not `2`/`4`.
- A non-tail `List` compare over 262144 elements overflows the JS stack; fuelled tail recursion does not.
- `+List<U32>` is rejected ("expected Data, observed Type") — `List<U32>` is the linear `&1` list; only `List<&2, U32>` is `Data` and can take `+`. The comparator takes it plain and consumes it.

**Where the scale track now stands.** M8a (keys + pure per-chunk gen), M8b (radix store), M8c (assemble + tick equivalence) are all landed and non-gated. The remaining pieces are the ones the plan always marked as gated/risky: **M8d** (sleeping — needs V2b-ii/iii) and, if ever wanted, true per-region ticking (needs V3c). Neither is required for any verified claim or for the fixed-world engine.

**Verification**
- `bend PROOF.bend` → `All terms check.` (27 laws); `bend src/store.bend` → `All terms check.`
- `bend app/tests.bend` (JS, tick-free) → all PASS incl. T16–T18, ~3.0s.
- Native `bend app/simtests.bend -o bin && ./bin` → T1, T2, T3, T4, T4b, T9, T18 all PASS (~4.9s).

**Recommended next:** the non-gated scale track is complete. The remaining meaningful work is the verification frontier — **V2b-ii** (`Array.swap.go` ↔ `to_pots`, which then unlocks M8d), **V2b-iii**, or **V3c** — each large/risky and each with the §5 documented-gap fallback. Everything above them is landed.

### A.24 — pi tooling: `bendverse` extension (6 tools)

**Status:** developer-experience only. Engine, `LAWS.bend`, and the gate are untouched; gate green (27 laws), fast and sim suites pass.

Added a project-local pi extension at `.pi/extensions/bendverse/` (`index.ts` + pure, testable `lib.ts`) that wraps the AGENTS.md workflow so the model spends tokens on reasoning instead of command boilerplate:

- `bend_gate` — runs `bend PROOF.bend`; one line green, or the raw compiler error red.
- `bend_test` — fast (JS) and sim (native, mtime-cached binary) suites; returns only a PASS/FAIL summary.
- `bend_run` — runs any `.bend` file (`native` optional), tail-capped output, for scenarios/repros.
- `bend_api` — `bend base` / `bend guide` lookup; module catalogue or signatures-only by default.
- `bend_plan` — section/query search over `PLAN.md`, `LAWS.bend`, `coreidea.md` (fence-aware heading index; numbered outline for coreidea).
- `bend_status` — git HEAD/dirty, open §5 milestones, law list, newest Appendix A entry.

All bend invocations are serialized (each saturates the cores). Pure helpers were unit-tested against the real docs and every tool was exercised end-to-end through a stubbed-`pi` harness. Activation: project-local extensions load once the project is trusted (`~/.pi/agent/trust.json`); `/reload` or restart picks them up in a running session.

### A.25 — pi tooling, wave 2: proof-frontier and trust-boundary tools

**Status:** developer-experience only. Engine, laws, and gate untouched; gate green (27 laws), fast and sim suites pass.

**Motivation (honest).** A.24 wrapped command output — the cheapest layer. Re-examining where value and risk actually sit surfaced two pools the first wave ignored:

1. **The proof frontier** (V2b-ii, V2b-iii, V3c) is the only remaining meaningful work, and A.24 gave it nothing.
2. **The trust boundary** — proven vs. test-witnessed vs. assumed — is prose spread across §3, §5, §7 and 23 Appendix entries, and nothing derives it.

Wave 2 adds four tools:

- `bend_goal <law>` — prints the *elaborated* goal and context for a named law by generating a scratch proof ending in Bend's `?hole` goal printer. This is the missing proof loop; `neighbor_cancel`'s elaborated goal is otherwise impractical to reconstruct by hand.
- `bend_spike <code>` — typechecks/runs a throwaway snippet at the project root (relative `./src/...` imports work), returns non-zero output as text (so `?hole` is readable), and deletes it. The scratch-spike pattern of A.14/A.18 is now first-class and auto-cleaned (`.bendverse-*.bend` gitignored).
- `bend_lemmas [query]` — signature index of the project's own `src/*.bend` (77 decls in `bits.bend`, 68 in `parity.bend`, 30 in `settle.bend`). Proof reuse needs discoverability, and `bend_api` only covers Base; this is the project's own `bend base`.
- `bend_audit` — one trust-boundary view: gate status, proof burden (6 trivial refl / 21 induction), PLAN law-count claims vs. actual (27 ✓), §5 open count, and every assumption/gap/downgrade/fallback line in PLAN.md labelled by section.

**Deliberately not built (verified first).** A claims↔proofs integrity checker would be redundant: the gate already enforces it — deleting one `def Laws.<x>` yields `1 TODO found`. And `bend PROOF.bend --checkup` is unsound here (it checks `LAWS.bend` alone and reports "27 TODOs"), so it is not used for localization.

**Caveat.** `bend_audit`'s gap list is heuristic prose extraction — a review aid, not a proof. The durable fix is a machine-readable gap registry plus a coreidea-rule ↔ law ↔ test traceability matrix, so status is *derived* rather than narrated. That touches human-owned text and awaits a decision.

### A.26 — PLAN.md v2: normative plan, derived state, gap registry, traceability

**Status:** documentation/process only. Engine, laws, and proofs untouched; gate green (27 laws); fast and sim suites pass.

**What changed.** PLAN.md was rewritten as a normative spec instead of an archaeological log:

- **History split out.** Old Appendix A (25 entries, ~630 lines, the majority of the file) moved verbatim to `HISTORY.md`, now the append-only milestone log. PLAN.md points there instead of carrying it.
- **§3 Verification architecture** reframed around what the gate does and does not prove: intent, refinement (`Array` vs model), and runtime witnesses are named as the trust boundary; the downgrade protocol writes to the registry.
- **§4 Traceability matrix** (new): coreidea rules `R1`–`R11` (plus `R0` encoding) → laws → tests → modules. The `—` rows (R2 conservation, R7 support) expose assurance boundaries that were previously implicit.
- **§5.3 Gap registry** (new, machine-readable): `G1`–`G7` with kind, status, what each gates, and what closes it. `bend_audit` parses this table rather than grepping prose; the old heuristic remains only as a fallback.
- **§5 State**: landed milestones compressed to a table (evidence → history); open work as a dependency-ordered checklist.
- **§0 platform facts / §7 guardrails** extended with post-v1 findings: absolute import paths work; imports resolve relative to the importing file; `?hole` prints goal+context; `--checkup` is unsound for `LAWS.bend`; the project lemma libraries are deep enough to need `bend_lemmas`.

**Consequences.** `AGENTS.md` updated to the new hierarchy and to the downgrade-into-§5.3 protocol. `bend_plan` gained `HISTORY` and now reports open work + gap summary; `bend_status` reads the landed table, gap registry, and `HISTORY.md`; `bend_audit` is table-driven (gap registry + lawless rules + law-count drift). Parsers were unit-tested against the new docs and every tool re-exercised through the stubbed-pi harness.

**Verification:** `bend PROOF.bend` → `All terms check.`; `bend app/tests.bend` 16/16; native sim tests 7/7.

### A.27 — V2b-ii complete: `Array.swap.go` ↔ `to_pots` refinement + Φ decrease

**Status:** V2b-ii **complete** (§5.2 box checked, `G1` closed). **3 new laws** (30 total). Engine untouched; gate green; fast (16/16) and simulation (7/7) suites pass.

**What landed** (`src/refine.bend`, new, pure):
- `PT` — a non-linear (`Data`) model of `Array<U32>`'s `ALeaf`/`ANode` shape, with `pack`/`unpack` and both roundtrips (`unpack_pack`, `pack_unpack`).
- `swap_m` — the model point-update, mirroring `Array.swap.go` (and its `h = shr n` / `is_lt(i,h)` split).
- `swap_ref` — **the refinement**: `unpack(afst(Array.swap.go(U32, pack t, n, i, v))) == swap_m(t, n, i, v)`. This is a machine-checked statement about Base's actual `Array.swap.go`, over arrays presented as `pack t`.
- `pots_m` / `pots_swap_m` / `chg_m` — the positional potential list, the incrementally-swapped list, and the old/new potential at the changed leaf.
- `to_pots_pack` — `to_pots(pack t, base, n) == pots_m(t, base, n)` (connects the model fold to the real array fold).
- `pots_corr` — `pots_m(swap_m t …, base, n) == pots_swap_m(t, base, n, i, v)` (the point-update list correspondence).
- `dec` — the **Φ decrease**: `suml(pots_swap_m …) + old == suml(pots_m …) + new`, no bound hypotheses (`i < n` is unnecessary: the walk hits some leaf and both sides agree there; range discharge belongs to V2b-iii).
- `array_swap_pots` / `array_swap_decreases` — the composed array-level statements.

**Laws added:** `swap_refines_array`, `array_swap_pots`, `swap_lowers_phi` (LAWS.bend + PROOF.bend). §4 R9 gains all three; §6 gains `src/refine.bend`; §5.3 `G1` → closed.

**Bend findings (V2b-ii).** These are the reasons the induction took the shape it did:
- **Arrays can never be copied.** `Array` is `Type`, so `+a` is rejected and a law like `to_pots(Array.set a …) == to_pots a` cannot even be *stated* (`List<&1,Nat>` vs `List<&2,Nat>`), and a proof body that consumes `a` twice is rejected (`consumed more than once`). The fix is a `Data` presentation: every array is definitionally `pack(unpack a)`, so all claims go through `PT`.
- **No forward references to unfilled laws.** Base's mutual `Array.swap.if` ↔ `Array.swap.go` works only in the prelude; user code that calls an unfilled `law` gets `an unfilled law is a dead claim: live code cannot use it`. Mutual recursion is therefore unavailable.
- **No matching a computed scrutinee.** `+z = U32.is_lt(i, h)` then `match z` is `a match cannot scrutinize a local binder`. The replacement is `Bool.pick` + a helper that takes `z` as a *parameter*; matching the parameter is fine.
- **Mutual recursion in proofs is broken by passing IHs.** A `z`-helper that would call the recursive lemma is defined *first*, taking the child proofs as arguments; the recursive lemma evaluates both children's IHs and passes them in. No mutual recursion, same induction.
- **Pair-returning Base defs don't reduce on stuck inputs.** `Array.swap.lo/hi` destructure their third argument, so `afst(Array.swap.lo(…, go))` is stuck while `go = Array.swap.go(pack xs, …)` is stuck (`pack xs` is a match on a variable). `lo_fst`/`hi_fst` (`afst(swap.lo(ys, r)) == ANode{afst r, ys}` by matching `r`) expose the component and unblock the congruence.
- **Erased positions still count for definitional equality, not for quantity.** `Equal.cong`'s `a`/`b`/`f` are erased, so a stuck `Array.swap.go …` may be duplicated there, but the live use must be unique.

**Honest scope note.** The laws are stated over `PT`, not over an arbitrary `Array` variable, because linearity forbids naming one twice. This is recorded as new gap `G8` (`accepted`): it is a language expressiveness limit, not a semantic one — the refinement is against Base's real `Array.swap.go` and every array is `pack(unpack a)`. The next step, V2b-iii, must make the same move for the support pass (writes that change bits, not material, so `pots` is unchanged).

**Verification**
- `bend PROOF.bend` → `All terms check.` (30 laws).
- `bend app/tests.bend` (JS, tick-free) → 16/16.
- Native `bend app/simtests.bend -o bin && ./bin` → 7/7.

### A.28 — V2b-iii (partly): write→Φ bridge; support/fall/mov preserve pot, crumble lowers pot

**Status:** V2b-iii **partly landed** (§5.2 box still open; `G2` narrowed, not closed). **6 new laws** (36 total). Engine untouched; gate green; fast (16/16) and simulation (7/7) suites pass. `V2` therefore still gated, so `M8d` stays gated.

**What landed** (`src/writepot.bend`, new, pure):
- `mat_encode` — `Cell.material(Cell.encode(m, c, a, s, f)) == U32.and(m, 31)`: the material field of an encoded cell is the material argument alone. The engine's write primitives are all `Cell.encode` re-encodings, so this is the load-bearing bit fact.
- `pot_set_support`, `pot_set_fall0`, `pot_mov` — `pot_at` is unchanged by the support, fall-reset, and fall-increment writes (the "support writes preserve Φ" claim, pointwise).
- `pot_crush_rock` — for `Cell.material(w) == 3`, `pot_at(crush_word(w), i) + 50·L == pot_at(w, i)` where `L = iy(i)`: the crumble (rock→rubble, density 200→150) lowers Φ by `50·L`, and the "bedrock floor" `L ≥ 1` makes it a strict decrease.
- `point_write_lowers` — the composition step: a whole-world point write that replaces a pot `v + g` by `v` lowers Φ by `g` (a `replace_decreases` instance at an arbitrary segment split; V2b-i's `list_set_sum` in decrease form).

**Laws added:** `material_encode`, `support_write_preserves_pot`, `fall_write_preserves_pot`, `mov_preserves_pot`, `crumble_lowers_pot`, `point_write_lowers`. §4 R0/R6/R9 and §6 updated; §5.1/§5.2/§5.3 and `HISTORY.md` record the partial status.

**What is still open (honest).** `G2` needs the tick's write *sites* enumerated over `Support.pass`/`Rules.step` and `point_write_lowers` instantiated at each; that is control-flow bookkeeping, not new mathematics. The fully array-level `Sim.tick` statement is blocked by linearity (recorded as `G8`), so the closure will be model/pot-list level with the refinement argument in `A.27`/`G5`. Until then `V2` is not complete and `M8d` remains gated.

**Bend findings (V2b-iii).**
- **The bit proof is the cost centre.** The `Word(32n)` model prints literals byte-by-byte (`WCon{…}`), so errors are pages long; iterate by diffing normalized goal text, not by eye.
- **Peel, don't factor.** The first attempt distributed `and(mask5, ·)` over the 5-way `or` with `factor5`, which produced unmanageable congruence goals. Rewriting one shifted term at a time with a generic `peel` (`and(mask5, or(A, shl_n(X,k))) == and(mask5, A)`, given `shr_n(k, mask5) == 0`) is far simpler: four applications plus `absorb_mat`.
- **Polymorphic shifts need the hypothesis, not reduction.** `Bits.and_shl_n` with a *variable* `k` leaves `shr_n(k, mask5)` stuck, so the hypothesis `h : shr_n(k, mask5) == zero` must be applied by `Equal.cong` (a literal `k` would reduce, a variable one will not).
- **Proof hypotheses are `+`-able.** `+h: {Cell.material(w) == 3 : U32}` is accepted, so a proof can be used twice; distinct `Equal` facts needed by different branches do not require re-derivation.
- **`pot_at` unfolds to `dens ∘ material`.** Every write lemma is therefore a material-field equality plus `dens_rock`/`dens_rubble` (`{==}` laws) and the `+`-form Nat algebra; no order lemmas were needed.

**Verification**
- `bend PROOF.bend` → `All terms check.` (36 laws).
- `bend app/tests.bend` (JS, tick-free) → 16/16.
- Native `bend app/simtests.bend -o bin && ./bin` → 7/7.

### A.29 — V2b-iii complete: array-level write→Φ effects; `G2` closed, V2 complete

**Status:** V2b-iii **complete**; `G2` closed; **V2 Global settling complete**, so `M8d` is ungated. **4 new laws** (40 total); one new test (T19). Engine untouched; gate green; fast (17/17) and simulation (7/7) suites pass.

**What landed.**
- `src/nat.bend`: `n_sub_add` (subtract-the-addend) and `n_add_cancel_right` — the cancellation needed to turn `Φ_new + P == Φ_old + P` into `Φ_new == Φ_old` (and the `+ gap` variant). Bend has no successor-injectivity, so cancellation is proved via truncated subtraction.
- `src/writepot.bend`: the active-bit writes — `mat_or_hi`/`mat_and_hi` (material preserved) and `pot_or_hi`/`pot_and_hi`: `wake` (`or 2048`) and deactivate (`and ~2048`) preserve `pot_at`. With A.28's support/fall/mov lemmas, *every* material-preserving write in the engine is covered.
- `src/tick.bend` (new): `tget` (the packed word at an index, same walk as `chg_m`), `crush_gap` (the leaf's `50·L`), `chg_support` (support write ⇒ old pot = new pot at the changed leaf), `array_support_write` (**`Array.swap.go` preserves Φ under a support write**), `chg_crush_rock` + `array_crumble_lowers` (**a rock crumble lowers Φ by `50·L` at the array level**).
- `app/tests.bend`: **T19** — a runtime witness over sampled words/levels that support/active writes preserve material, rock crumble lowers pot, and non-rock crush is the identity.

**Laws added:** `wake_preserves_pot`, `deactivate_preserves_pot`, `array_support_write_preserves_phi`, `array_crumble_lowers_phi`. §4 R6/R9 and §6 updated; §5.1/§5.2/§5.3 and `HISTORY.md` record completion.

**Trust boundary after this.** `G2` is closed with two explicit accepted residuals:
- `G9` — non-rock `crush_word` potential preservation. Bend **cannot** case-split the opaque `U32` in `Cell.density`/`crush_material`: the wildcard branch of `match m` refines `m` to a *partial* `Word` (`WCon{…, _69}`), not a literal, so the identity is not a theorem. It is semantically the identity and is runtime-witnessed by T19.
- `G10` — the tick's write-*site* enumeration over `Support.sup`/`Rules.step` is by inspection, not mirrored; every primitive's effect is proven, so `Sim.tick` non-increase follows once that finite list is checked (and, for non-rock crushes, `G9`).

**Bend findings (V2b-iii closure).**
- **`Nat.sub` does not reduce with a stuck first argument.** `Nat.sub(Nat.add(a,0n),0n)` stays put, so subtraction facts must be rewritten explicitly (`n_sub_zero`) rather than expected definitionally.
- **Reusable pattern tails.** `case 1n+p:` binds `p` affinely; a short recursive use needs `case 1n+ +p:`.
- **Function-typed IHs.** To thread a leaf hypothesis through a `Bool.pick` split, pass the IH as a function `({material(...) == 3} -> {…})`; after matching `z` the *type* of the hypothesis normalizes to the branch fact, so `ihx(hm)` closes the branch.
- **Wildcard on `U32` is partial.** `case _` refines the scrutinee to a `Word` with a variable tail, which is why arbitrary-material claims (G9) are out of reach.
- **Literals normalize to definitions.** `2048 ≡ U32.shln(1,11n)` and `4294965247 ≡ U32.not(2048)` are definitional, so active-bit goals reduce when written as `shln`/`not` and closed with `and_shl_n`/`and` reductions.

**Verification**
- `bend PROOF.bend` → `All terms check.` (40 laws).
- `bend app/tests.bend` (JS, tick-free) → 17/17 (incl. T19).
- Native `bend app/simtests.bend -o bin && ./bin` → 7/7.

### A.30 — M8d complete: chunk sleeping + lossless store eviction (conservative)

**Status:** M8d **complete** (§5 box checked). **No new laws** — test-witnessed
(T20), like M8a–M8c. Engine (`rules`/`support`/`sim`) untouched; gate green; fast
(21/21) and simulation (8/8) suites pass.

**Interpretation (scope, honestly).** "Sleeping/eviction" is implemented at the
**chunk-store** level, not as a changed tick. Sleeping chunks are already the
engine's activity semantics (rule 9 / §2.9: an inactive cell is never written by
its own evaluation); M8d adds the *eviction* half: the store is a sparse overlay
on worldgen, and a chunk that is **sleeping and bit-equal to its pure gen** is
dropped, then regenerated exactly by `assemble`. The regenerability test is
conservative and checkable: gen-equality implies all-inactive, so every evicted
chunk is genuinely sleeping, but a chunk that has settled to a *modified*
inactive state is (correctly) kept. Widening eviction from gen-equal chunks to
every sleeping chunk is exactly the unproven sleep-invariance argument recorded as
`G10`; it does not affect the soundness of what landed.

**Deliverables (`src/store.bend`).**
- `assemble_cells` now **regenerates a missing chunk from `chunk_list(k)`** instead
  of leaving it zero. The store becomes a sparse overlay on pure worldgen (rule
  11); `assemble(empty()) == Worldgen.build()` and, with a full store, T18 is
  unchanged.
- `sleeping_cells(cells)` — no active bit in a stored chunk list.
- `gen_eq_cells(cells, gen)` — bit-equality with the pure gen list (both local
  order, as produced by `chunk_list`).
- `keep_cells` / `evict_key` / `evict` — walk the 64 keys, drop a chunk iff
  `sleeping && gen_eq`, else keep its exact cells. `evict_key` recurses on the
  key index (no mutual recursion), reading the source store with `+s` (Store is
  `Data`, so `get` does not disturb it) and accumulating residents.

**Tests**
- `app/tests.bend` **T20**: (a) `assemble(empty()) == Worldgen.build()`;
  (b) an all-gen store evicts to nothing and re-assembles to worldgen;
  (c) a store with one modified chunk keeps exactly that chunk and assembles
  identically before/after eviction; (d) `sleeping`/`gen_eq` are true of a fresh
  chunk and false of a modified (activated) one.
- `app/simtests.bend` **T20** (native): `pass_all(assemble(evict(build_all())))`
  equals `Sim.build()`, and `spawn` + 10 ticks from both worlds is bit-for-bit
  identical — the evict → assemble → tick pipeline matches the fixed world.

**Bend findings (M8d).**
- **`Array.get` owns, it does not borrow.** `Array.get(T, a, i)` consumes `a` and
  returns `Array<T> & T`; a read-scan must thread that pair and re-read, and a
  read-only predicate cannot keep the array without returning the pair. Working
  on `List<&2, U32>` (chunk cell lists) avoids the whole problem — `&2` lists are
  `Data` and freely reusable.
- **Matches scrutinize parameters, in binder order.** A match cannot scrutinize a
  local binder (`give it its own def`), cannot follow a `let` in a def body, and
  nested matches must follow the signature's binder order. This is why
  `evict_key` carries the `Maybe` as its second parameter and recurses on itself.
- **Tuple-destructuring `let` must be the last binding** before the tail term;
  it cannot be followed by another `let`.

**Where the scale track now stands.** M8a–M8d are all landed. The remaining
gated/risky pieces are unchanged: **V3c** (schedule invariance, gates M7d) and
the accepted gaps `G9` (non-rock crush, runtime-witnessed) and `G10` (write-site
enumeration, which would widen eviction). Nothing landed rests on an unproven
claim.

**Verification**
- `bend PROOF.bend` → `All terms check.` (40 laws; unchanged).
- `bend app/tests.bend` (JS, tick-free) → 21/21 (incl. T20a–d).
- Native `bend app/simtests.bend -o bin && ./bin` → 8/8 (incl. T20).

### A.31 — V4 conservation: the non-empty count layer; R2 gains laws

**Status:** conservation layer **landed**; **6 new laws** (46 total); one new test
(T21). Engine untouched; gate green; fast (22/22) and simulation (8/8) suites
pass. This is the natural companion to the V2 settling layer: same `PT`/array
machinery, but an *equality* (the count is conserved) instead of a decrease.

**What landed.**
- `src/count.bend` (new): `nempty(w)` — the non-empty indicator (1 for any
  material other than Empty, 0 for Empty). Material-preserving write facts:
  `nempty_set_support`, `nempty_set_fall0`, `nempty_mov`, `nempty_wake`,
  `nempty_deactivate`, each reduced to `mat_encode`/`mat_or_hi`/`mat_and_hi` plus
  `and31_absorb` (the same facts the pot layer uses). Count folds `to_counts(a)`
  and `cnts_m(t)` with `to_counts_pack`; the swap congruence `cnts_same`
  (a point write changes one leaf; if the written cell's non-emptiness matches the
  displaced one, the whole count list is *equal*); and the array-level
  `array_point_write_preserves_count`, plus the five concrete instances.
- `LAWS.bend`: `array_point_write_preserves_count` (generic, with the leaf-count
  hypothesis) and `array_support_write_preserves_count`,
  `array_fall_write_preserves_count`, `array_mov_write_preserves_count`,
  `array_wake_write_preserves_count`, `array_deactivate_write_preserves_count`.
- `app/tests.bend` **T21**: sampled words — every material-preserving write keeps
  the non-empty indicator; rock crush keeps it (3 → 4, both non-empty); non-rock
  crush is the identity (`G9`).

**Interpretation (scope, honestly).** These are *world-level* conservation laws
for the transform ops: `array_support_write_preserves_count` says a support write
anywhere leaves `suml(to_counts(...))` unchanged, and likewise for fall/mov/wake/
deactivate. They rest on `Array.swap.go` refinement, exactly as the pot laws do.
The rule-2 **swap** case (a movement exchanges two cells) is *not* yet a theorem:
it needs the count *balance* primitive — `count_new + nempty(old) == count_old +
nempty(new)`, the mirror of `array_swap_decreases` — and then a two-write
composition whose `+`-terms telescope. That is left as the open V4 item; `G6`
stays open for it (and for rule 7 support).

**Bend findings (V4).**
- **The count layer is simpler than the pot layer.** `nempty` has no positional
  (y-level) dependence, so `to_counts`/`cnts_m` take no `base` and every induction
  loses the index arithmetic; `cnts_same` is a plain structural equality rather
  than a decrease.
- **Congruence under an equality hypothesis reduces cleanly.** `Equal.cong(U32,
  Nat, m => nempty_m(m), material(f(w)), material(w), mat_encode(...))` turns any
  material-preserving write into a count fact with no order lemmas.
- **`Equal.cong` accepts `+List<Nat>` as the target type** (as in the V2b code),
  so list equalities lift to `suml` equalities directly.

**Verification**
- `bend PROOF.bend` → `All terms check.` (46 laws).
- `bend app/tests.bend` (JS, tick-free) → 22/22 (incl. T20, T21).
- Native `bend app/simtests.bend -o bin && ./bin` → 8/8.

### A.32 — V4 balance: the point-write count balance (the swap primitive)

> **Partly superseded by A.34/A.35** — the "Interpretation (scope)" note below
> ("not yet a theorem", "needs U32 subtraction injectivity", "`G6` therefore
> stays open for the composition") is obsolete: the composition landed in A.34 and
> A.35 retracts the injectivity claim. The balance primitive above stands.

**Status:** the conservation count *balance* landed; **1 new law** (47 total).
Engine untouched; gate green; fast (22/22) and simulation (8/8) suites pass.

**What landed (`src/count.bend`).**
- `cnts_swap_m` / `cnt_chg_m` — the written count list and the (displaced,
  written) count pair, mirroring `pots_swap_m`/`chg_m` with no positional base.
- `cnts_corr` (the written list equals the model swap's count list) and
  `cnt_balance` / `cnt_balance_if` — the count analog of `dec`/`dec_if`: for a
  point write, `suml(cnts_swap_m) + nempty(old) == suml(cnts_m) + nempty(new)`.
- `array_swap_counts` (lift through `swap_ref`/`swap_refines_array`, as
  `array_swap_pots` does) and `array_point_write_count_balance` — the array-level
  balance law.
- `LAWS.bend`/`PROOF.bend`: `array_point_write_count_balance`.

**Interpretation (scope, honestly).** This is the identity that makes a *swap*
conservative: a read-modify-write changes the count by exactly
`nempty(written) - nempty(displaced)`, so a swap (write the displaced value back)
nets zero. It is the count analogue of `array_swap_decreases`. What is **not**
yet a theorem is the engine's *two-write* movement composition: applying the
balance at the target and then at the source leaves one residual term,
`nempty(tget(swap_m(t, n, j, v), n, i))`, which must be shown to equal
`nempty(tget(t, n, i))` when `i ≠ j` — a read-after-write/valid-index lemma. That
lemma needs U32 subtraction injectivity (a swap at `j` does not disturb a distinct
valid index `i`) plus a carried validity invariant through the tree descent, none
of which exists yet. `G6` therefore stays open for the composition (and rule 7
support); the balance primitive is landed and reusable.

**Bend findings (V4 balance).**
- **Mirroring works, but argument arity is the trap.** `cnts_m(t)` takes no index
  (unlike `pots_m(t, base, n)`); carrying the `pots`-shaped call `cnts_m(xs, h)`
  type-checks as `(cnts_m xs) h` and fails with a misleading "expected a function
  type". Strip positional arguments when mirroring a base-dependent fold.
- **The balance proof is `dec_if` with `chg_m` → `cnt_chg_m`** and no `base`; the
  `S.swap_add`/`suml_append`/`NatL.n_add_assoc` skeleton transfers verbatim.

**Verification**
- `bend PROOF.bend` → `All terms check.` (47 laws).
- `bend app/tests.bend` (JS, tick-free) → 22/22.
- Native `bend app/simtests.bend -o bin && ./bin` → 8/8.

### A.33 — V4 correction: the movement composition's obstacle (recorded, not landed)

> **Superseded by A.34/A.35** — the composition landed (A.34); A.35 retracts the
> "validity invariant / subtraction injectivity" claim *and* the
> "decision-parameterized double swap" framing. The obstacle description below is
> of historical interest only.

**Status:** no code change; a correction to A.32's "remaining" note. Gate green;
suites unchanged. Appended per the downgrade protocol (never rewrite an entry).

A.32 said the two-write movement composition "needs a read-after-write/valid-index
lemma". That is one route, but the first attempt at it hit a **Bend-specific**
obstacle worth recording before the next try:

- A `match` only reduces when it scrutinizes a **parameter** (or field), in
  signature binder order. The composition's goal contains `T.tget(t, n, i)` and
  `R.swap_m(t, n, j, …)`, whose internal `U32.is_lt(i, U32.shr n)` decisions are
  *not* parameters, so matching the decision does not reduce the goal.
- `swap_ref_if`/`swap_if` solve this for **one** swap by threading the decision
  (`z`) as a parameter and phrasing the goal with `Bool.pick(…, z, …)`. A **nested**
  swap (`swap_m(swap_m(t, n, j, v1), n, i, v2)`) needs the same treatment for both
  decisions *and* the written values (`w = tget`, `gv = tget`), i.e. a
  decision-parameterized double swap. That is real plumbing, not a lemma.
- The alternative (read-after-write: `tget(swap_m(t, n, j, v), n, i)` is untouched
  for a distinct valid `i`) needs a carried validity invariant and U32 subtraction
  injectivity, which `src/` does not have.

Either route is viable; both are larger than the balance primitive. The balance
law (`array_point_write_count_balance`, A.32) is landed and is the reusable
primitive; `G6` stays open for the composition. The unfinished attempt was
reverted so the gate stays green.

### A.34 — V4 complete: the two-write movement swap (rule 2 is law-covered)

**Status:** the movement swap landed; **1 new law** (48 total); **rule 2 is now
fully law-covered**. Engine untouched; gate green; fast (22/22) and simulation
(8/8) suites pass.

**What landed (`src/count.bend`).**
- `tget_pick` — `tget` distributes over the swap's `Bool.pick` (proved by matching
  the decision). This is the key that unlocks a nested read-back: `tget`/`swap_m`
  are structural matches and do **not** reduce through a `Bool.pick`, so
  `tget(swap_m(t,…), …)` is stuck when `t` is abstract until the decision is
  exposed.
- `nfst_pick`/`nsnd_pick`/`nempty_pick`/`pick_same`, `cnt_chg_fst`/`cnt_chg_snd`
  (the displaced/written counts as `nempty`), and `cnt_balance_tget` — the balance
  with the displaced count written as `nempty` of the model read.
- `nempty_tget_swap_mov` — read-back: after writing `mov(w)` at `j`, the
  non-emptiness at `i` is still `nempty(w)` (i is untouched, or holds `mov` of its
  old value). A two-decision induction; the written value is `mov` of the
  whole-tree read, inlined as a `Bool.pick` on the i-decision so it reduces.
- `mov_count` — the two balances telescope (no case analysis): apply
  `cnt_balance_tget` at `j` then at `i`, use read-back + `nempty_mov`, cancel.
- `afst_swap_m` (`afst(Array.swap.go(pack t,…)) == pack(swap_m t…)`) and
  `array_mov_swap_preserves_count` — the array-level law.
- `LAWS.bend`/`PROOF.bend`: `array_mov_swap_preserves_count`.

**Why this closes rule 2.** A movement is two point writes: the target receives
`mov(w)` and the source receives the displaced target value. Each write's count
balance leaves a `+`-term; the terms telescope because `mov` preserves the count.
So `suml(to_counts(world))` is invariant under the rule-2 swap, machine-checked.
(Transform writes — support/fall/active — are already outright count-preserving,
A.31.) `G6` now reduces to rule 7 (support), which stays test-witnessed.

**Bend findings (V4 movement).**
- **Structural matches do not reduce through `Bool.pick`.** `tget`/`swap_m` on a
  `Bool.pick` are stuck; a *distribution lemma* (`tget_pick`, trivial by matching
  the decision) is the way through, not a reformulation of the definitions.
- **A nested induction's hypotheses must match the reduced goal.** The helper's
  written value had to be `mov(Bool.pick(zi, …))` *inlined* (not a parameter), so
  that matching `zi` reduces it to the recursive hypothesis's `mov(tget …)`.
- **`Array<U32>` is `Type`, not `Data`** — array values cannot be named twice, so
  the array-level lift inlines the nested `Array.swap.go` rather than binding an
  intermediate `a1`.

**Verification**
- `bend PROOF.bend` → `All terms check.` (48 laws).
- `bend app/tests.bend` (JS, tick-free) → 22/22.
- Native `bend app/simtests.bend -o bin && ./bin` → 8/8.

### A.35 — Correction to A.33 (the read-after-write route needed no validity/injectivity)

A.33 claimed the read-after-write alternative "needs a carried validity invariant
and U32 subtraction injectivity". That is **wrong**, and A.34 supersedes it: the
read-back fact only needs **non-emptiness** (not value equality or `i ≠ j`), and
`mov` preserves that, so no validity invariant, no index distinctness, and no
subtraction injectivity are required. The only real obstacle was that `tget`/
`swap_m` do not reduce through a `Bool.pick`; the fix is the (trivial)
distribution lemma `tget_pick` plus inlining the written value as a
`Bool.pick(zi, …)` in the induction. A.33's "decision-parameterized double swap"
framing was an unnecessary detour.

### A.36 — G10 scoped: it is gated by G9, not just "large and mechanical"

**Status:** analysis recorded; no code change beyond naming the activity bit and
`swap_m_pick` (A.35/A.36 preamble). Gate green; suites unchanged.

**The conundrum, made explicit.** The registry said `G10` closes by "mirroring the
control flow on `PT`". Enumerating the write sites shows that is necessary but
**not sufficient**:

| site | write | Φ effect |
|---|---|---|
| `Rules.step` sel 18 | `deactivate` | preserves (material-preserving) |
| `Rules.step` sel 5/6 | `mov(w)` + displaced value | swap; `array_swap_decreases` |
| `Rules.step` sel 12 | diagonal swap | swap; `array_swap_decreases` |
| `Rules.step` sel 22 | `crush_word(target)` + `set_fall0` | **rock: decreases; non-rock: needs G9** |
| `Rules.step` sel 23 | `set_fall0` | preserves |
| `Support.sup` sel 3/4 | `set_support` | preserves |
| `Support.sup` sel 6 | `crush_word(w)` + wake | **rock: decreases; non-rock: needs G9** |
| `Ops.wake` | `activate` | preserves (needs a composition over its loop) |

Every effect is either proven or has a clear route **except the two crush sites**.
`Rules.step` sel 22 fires `crush_word(gv)` whenever the target is non-static and
`fall(w) >= cohesion(target)` — for sand/rubble `cohesion = 0`, so it *does* fire
on non-rock targets. `Support.sup` sel 6 fires on any cohesive, non-static cell,
which is not provably rock. The needed non-rock fact is only
`dens(material(crush_word(w))) <= dens(material(w))` (equal for non-rock; `mov`/
crush preserve non-emptiness), but:

- `Bend rejects non-exhaustive matches` (a 32-literal `match m` with no wildcard
  errors "expected cases for True"), so we cannot enumerate the 32 material
  values to close each case as a computation;
- and in the `case _` branch `crush_material(m)` is **stuck** (the wildcard
  refines `m` to a partial `Word`, not a literal/range), so `dens` cannot reduce.

So `G10`'s close is "mirror **and** resolve `G9`". This is the A.33 pattern again:
a mechanical-looking close with a hard case (here a language limitation) in the
middle. Registry and §8 updated.

**Options (for a human decision).**
1. Prove `G10` *modulo* `G9`: mirror both machines, take the non-rock crush
   potential non-increase as a hypothesis. Mechanical but large; sharpens the
   boundary to exactly `G9`.
2. Make non-rock `crush_word` **definitionally the identity** (`match
   Cell.material(w): case 3: encode(4,…); case _: w`). Then `G9` is moot for the
   tick and `G10` becomes a pure mirror. This is an **engine semantics change**
   (today non-rock crush zeroes cohesion/active/support/fall); it must be shown
   behavior-preserving against T1–T4b/T9/T18/T20 before adopting.
3. Accept and document (current state).

**Verification**
- `bend PROOF.bend` → `All terms check.` (48 laws).
- `bend app/tests.bend` → 22/22; native `app/simtests.bend` → 8/8.

### A.37 — G9's root: the non-rock crush is an oversight, but the guard needs reflection

**Status:** two probes, no landed code. Gate green; suites unchanged. This sharpens
`G9`/`G10` from "can't case-split `U32`" to a precise, actionable root cause.

**Probe 1 — is the non-rock crush load-bearing?** Temporarily redefined
`Ops.crush_word` so that non-rock returns `w` unchanged (rock still `encode(4,…)`):
**all 8 simulation tests pass** (T1/T2/T3/T4/T4b/T9/T18/T20). So the current
behaviour — `crush_word` also zeroes a non-rock target's cohesion/support/fall —
is **not needed by the tested dynamics**. That supports the reading that applying
`crush_word` to non-rock targets is an oversight (rule 8 wants Rock → Rubble and
`cohesion := 0`; zeroing the other fields is extra). Probe reverted.

**Probe 2 — can the fix be *proved*?** A guard `material(x) == 3` at the call sites
is the right fix, but turning it into a proof needs **reflection** — from a Bool
test back to a fact:
- `U32.is_eq(a, b)` unfolds to `Cmp.is_eq(Word.cmp(32n, x, y))` and does **not**
  reduce for abstract arguments (even `is_eq(a,a) == True` is not definitional);
- a hand-written `is_rock(m)` matched on a parameter is stuck in the wildcard
  branch, and the wildcard refines `m` to a *partial* `Word` (`WCon{…, _73}`), not
  to "not 3" — so no contradiction can be extracted;
- Base exposes no reflection lemma for `U32.cmp`/`Word.cmp`.

So the required lemmas are `Cmp.is_eq(Word.cmp(32n, x, y)) == True → x == y` (and
its `Nat`/`is_eq` corollaries). This is a bounded `Word`-structural induction
(mirroring `order.cmp_fin_total`, with `Word.cmp.fin`'s LT/GT/EQ × head-bit cases).
It is the real unlock: with it, guard-based material logic becomes provable, `G9`
can be closed by *fixing the rule*, and `G10`'s crush sites stop being special.

**Plan (option-2 route).**
1. Prove the `Word.cmp` reflection lemma in a new `src/word.bend` (Base-level but
   in-project, since Base cannot be edited). Gate-checked; no engine change.
2. Guard the crush sites to rock (behaviour-validated by probe 1).
3. Then mirror `Support.sup`/`Rules.step` for `G10` with every write site provable.

**Verification**
- `bend PROOF.bend` → `All terms check.` (48 laws); fast 22/22; sim 8/8.

### A.38 — `Word.cmp` reflection: the G9/G10 unlock is proven (step 1 of 3)

**Status:** new `src/word.bend`, two new laws (`word_cmp_eq_reflect`,
`u32_cmp_eq_reflect`); gate green (50 laws); no engine change. This lands exactly
the reflection lemma A.37 identified as the blocker, so material-guarded engine
logic is now provable.

**What landed.**
- `b_cmp_eq`: the `Bool` base case —
  `Cmp.is_eq(Bool.cmp(a, b)) == True → a == b`. The two impossible branches
  (`False/True`, `True/False`) are closed directly: one returns the hypothesis
  (its normal form is the goal), the other uses `Equal.sym`.
- `w_cmp_fin_eq_bits` / `w_cmp_fin_eq_t`: split on `t` in `Word.cmp.fin`. The
  `EQ` case is `b_cmp_eq` / reflexivity; the `LT`/`GT` cases are impossible — the
  hypothesis normalizes to `{False == True}` — and are discharged by
  `Equal.cong` along a `Bool.pick` motive, which transports the contradiction to
  the arbitrary goal *without* needing the opaque `U32` to reduce.
- `w_cmp_eq`: structural induction over the bit prefix. The recursive step
  recovers the head bits (`w_cmp_fin_eq_bits`) and the tail comparison
  (`w_cmp_fin_eq_t`), recurses, and glues the two `Equal.cong`s with
  `Equal.trans`. Stated for general `n` (not just `32n`).
- `u32_cmp_eq`: the `U32.is_eq` corollary, wrapping `w_cmp_eq` under
  `U32{…}`.

**Why it was hard (now resolved).** `U32.is_eq`/`Word.cmp` do not reduce for
abstract arguments, and matching an opaque `U32` only refines it to a partial
constructor (A.37). The trick is that the *hypothesis* carries the comparison
result: matching on the `Cmp` value `t` passed as a parameter lets `Word.cmp.fin`
and the hypothesis' type reduce together, and `Bool.pick` builds a motive that
turns a stuck `{False == True}` into whatever goal a branch needs.

**Next.** §5.2 step 2: guard the crush sites (`Rules.step` sel 22,
`Support.sup` sel 6) to rock, using `u32_cmp_eq_reflect` to prove the guard
(invoking `material(w) == 3` on the non-crumbling branch). Behaviour is already
validated by A.37 probe 1. Then step 3 (`G10` mirroring).

**Verification**
- `bend PROOF.bend` → `All terms check.` (50 laws); fast 22/22; sim 8/8.

### A.39 — The crush guard: non-rock targets are no longer crushed (step 2 of 3)

**Status:** engine change at both crush sites, one new law
(`guarded_crush_lowers_pot`); gate green (51 laws); both suites pass. This lands
step 2 of the option-2 route: the guard whose proof A.38's reflection lemma
unlocked.

**What landed.**
- `Ops.crush_if_rock(+w)`: `Bool.pick(U32, U32.is_eq(Cell.material(w), 3),
  crush_word(w), w)` — the rule-8 impact/crumble material change, guarded to
  rock. Non-rock keeps the field reset *out*: a target with no cohesion has no
  threshold to cross, so the reset was never load-bearing (A.37 probe 1).
- `Rules.step` sel 22 (impact target) and `Support.sup` sel 6 (crumble source)
  now write `Ops.crush_if_rock(·)` instead of `Ops.crush_word(·)`. Behaviour is
  identical to A.37 probe 1, which passed all sim tests.
- `W.pot_crush_if` / `W.pot_crush_guarded`: the point-level theorem —
  `pot_at(crush_if_rock(w), i) + (rock ? 50·L : 0) == pot_at(w, i)`. The guard
  Bool is threaded as a parameter so both branches are definitional; the rock
  branch reflects `U32.is_eq(material(w), 3) == True` to `material(w) == 3`
  via `Word.u32_cmp_eq` (A.38) and applies `pot_crush_rock`. This is the first
  use of the reflection lemma in a real engine-effect proof.

**Why the guard is the right fix.** Rule 8's event converts rock (→ rubble) and
drops cohesion; for a non-rock target there is nothing to convert and cohesion is
already 0, so applying `crush_word` there was an oversight (A.37). Guarding keeps
the rule's meaning and makes every actual crush argument provably rock — which is
exactly the hypothesis `array_crumble_lowers_phi` already carries.

**Next.** §5.2 step 3 (`G10`): mirror `Support.sup`/`Rules.step` on `PT`, where
each crush write site now carries a guard Bool that the `pot_crush_if` pattern
discharges.

**Verification**
- `bend PROOF.bend` → `All terms check.` (51 laws); fast 22/22; sim 8/8.

### A.40 — G9 closed: the guarded crush has an unconditional Φ theorem

**Status:** two new laws (`array_guarded_crush_lowers_phi`, and the reuse lemma
`pots_write_same` as a non-law helper); gate green (52 laws); both suites pass.
The write primitive at both crush sites is now fully proven, so `G9` is closed
and `G10`'s hard case is gone.

**What landed (`src/tick.bend`).**
- `pots_write_same`: writing the current value back is the identity at the pot
  level (`pots_swap_m(t, base, n, i, tget(t, n, i)) == pots_m(t, base, n)`).
  This is the non-rock branch of a guarded crush. Proved by structural induction:
  `pots_swap_m` and `tget` make the same `is_lt` decision, so the two sides reduce
  together (`pots_write_same_if`).
- `guard_gap`: the Φ slack of a guarded crush — `crush_gap` for rock, `0`
  otherwise.
- `array_guarded_crush_lowers`: the guarded write's array-level Φ effect, with the
  guard Bool threaded as a parameter and a hypothesis tying it to
  `material(tget) == 3`. Case split: *rock* → reflect the guard with
  `Word.u32_cmp_eq` (A.38) and apply `array_crumble_lowers`; *non-rock* → the
  value is `tget` (definitional), `pots_write_same` collapses it, arithmetic
  closes. `array_guarded_crush_lowers_auto` is the wrapper over
  `Ops.crush_if_rock`/`guard_gap`.

**Why this closes `G9`.** `G9` was "non-rock crush is not a theorem". The engine
no longer crushes non-rock (A.39), and the new array law covers the guarded write
*without* a `material(w) == 3` hypothesis — rock and non-rock are both proven,
with the gap exactly `guard_gap`. So no crush site carries an unproven premise.

**Remaining `G10`.** Proving the write-*site enumeration* still means mirroring
`Support.sup`/`Rules.step` on `PT` along their fuel loops and composing the proven
primitives (`set_support`/`set_fall0`/`activate` preserve; `mov`/diagonal swap
decrease via `array_swap_decreases`; guarded crush decreases via
`array_guarded_crush_lowers_phi`). That mirror is the last mechanical piece.

**Verification**
- `bend PROOF.bend` → `All terms check.` (52 laws); fast 22/22; sim 8/8.

### A.41 — G10 infrastructure: `activate` write + the `wake` mirror (and a compiler trap)

**Status:** one new law (`array_activate_write_preserves_phi`) plus the internal
`wake` mirror; gate green (53 laws); both suites pass. This is the write-primitive
coverage the `Support.sup` mirror needs. Mid-step, compilation hung for minutes —
diagnosed and turned into a guardrail.

**What landed (`src/tick.bend`).**
- `chg_activate` / `array_activate_write`: the array-level Φ law for an
  `activate` write, mirroring `array_support_write` but with `pot_or_hi` at the
  leaf (bit 11 does not touch the material field). Law
  `array_activate_write_preserves_phi`.
- `to_pots_swap_pack`: bridges `pack(swap_m(t,n,j,v))` to
  `afst(Array.swap.go(pack(t),n,j,v))` (via `swap_ref` + `pack_unpack`), so the
  array laws apply to the mirror's writes.
- `wake_x_m` / `wake_y_m` / `wake_z_m` / `wake_m`: the `Ops.wake` 26-neighbor
  loop mirrored on `PT`; each `mark` becomes a `swap_m` of `activate(tget)`.
- `wake_x_m_preserves` / `wake_y_m_preserves` / `wake_z_m_preserves`: the nested
  fuel induction composing `array_activate_write`, so `wake` preserves Φ.

**The trap (now a guardrail, PLAN §7).** Stating `wake_m_preserves` over
`wake_m(i,t,n)` — a wrapper for `wake_z_m(3,…)` — made `bend src/tick.bend` run
for >90 s at 100% CPU (it never finished). Cause: the checker normalises the
*statement*, unrolling the concrete fuel `3` into 3·3·3 = 27 `swap_m`/`activate`
steps, plus the `pack`/`to_pots` over that tree. Bisection (`head -n` on the
file: 316/339/362/365 fast, 368 hangs) pinned it exactly to that one lemma's
type. Fixed by deleting `wake_m_preserves`; `sup` will instantiate the
abstract-fuel `wake_z_m_preserves` at `3` *inside* its proof, where the fold is a
single definitional unfold. Rule of thumb: never put a concrete-fuel loop
application in a proposition.

**Next.** The `Support.sup` fuel-loop mirror (`sup_m : PT & Nat`, gap
accumulated at the guarded crush; `set_support`/`wake` add 0), then `Rules.step`.

**Verification**
- `bend PROOF.bend` → `All terms check.` (53 laws); fast 22/22; sim 8/8.

### A.42 — G10 mirror: selector representation, then a checker performance cliff

> **Superseded by A.45** — the root cause given below (the `set_support` branches)
> is wrong; the real trigger is the concrete wake fuel in S6. A.42's bisection was
> contaminated by a leaked 100 %-CPU compile. See A.45 for the minimal repro and fix.

**Status:** probe only — nothing landed; gate green (53 laws); suites unchanged.
The `Support.sup` fuel-loop mirror was built and typechecks as a *definition*, but
its Φ theorem does not check in reasonable time. Two distinct obstacles, both
isolated by bisection. This is a tooling finding, not bad mathematics.

**Obstacle 1 — the selector is an opaque `U32` (the A.37 problem again).** A
literal mirror matches on `sel: U32`. In a proof `sel` is abstract, so
`match sel` never reduces: the goal stays `sup_m(1n+p, …)` and no branch fires.
Fix: a proper datatype selector (`SupSel`: `S0`…`S11`). Matching then reduces
structurally in both definition and proof, and the recursive calls pass
`Bool.pick(SupSel, cond, S1{}, S9{})` — which the universally-quantified
induction hypothesis accepts without needing to reduce the pick. `sup_m` with
`SupSel` typechecks in 3 s. The mapping `SupSel` → the engine's numeric selectors
belongs to the `G5` refinement, by inspection.

**Obstacle 2 — a normalisation cliff in the support-write branches.** With
`SupSel`, `sup_m_preserves` still runs >120 s at 100 % CPU (reproducible). The
bisection (`?h`-stubbing branches, then timing):
- statement alone (trivial body): 3 s — and note the goal keeps `sup_m(1n+p, …)`
  opaque, so the type is not the problem;
- no-write branches (S0/S1/S2/S5/S9/S10/S11) + S6: 3 s;
- stubbing S3/S4 (the two `set_support` writes): 3 s;
- S3/S4 present: hang.
Each ingredient typechecks *alone* in ≤3 s (`sup_m`; `swap_support_preserves`;
`array_support_write`). The cliff is the interaction: `sup_m_preserves`' statement
mentions `sr_tree(sup_m …)` **and** `sr_gap(sup_m …)`, so reducing
`sup_m(1n+p, …, S3{}, …)` inlines the write as
`swap_m(t, n, i, set_support(tget(t, n, i), s2))`, normalisation unfolds
`set_support`/`Cell.encode` into a large `U32.or(…shifts…)` bit term, and that
term is embedded inside `swap_m`→`pack`→`to_pots`, twice. This is a normaliser
performance limit (no wrong answer); whether it is a *bug* or just absent
sharing/opacity is unclear.

**Assessment.** Obstacle 1 is ours to fix. Obstacle 2 looks like a Bend2
limitation on large unfolded terms in nested positions. This is the same family as
the A.41 concrete-fuel blowup — both are "the checker expanded something huge
inside a type". Candidate mitigations, neither yet tried:
1. **`sup_step` opacity** — move the write into a helper
   `sup_step(..., v)` so the large term is an *argument* (`swap_m(t, n, i, v)`
   stays stuck with `v` abstract) instead of nested inside the tree in the type.
2. **Single-occurrence statement** — bind the `SupR` result once and state the Φ
   theorem against that binding, so `sup_m` appears once, not twice.

**Verification**
- `bend PROOF.bend` → `All terms check.` (53 laws); fast 22/22; sim 8/8.
- Probe files removed (`.bendverse-*` is gitignored); no stray compiler processes.

### A.43 — Tooling: hangs now die cleanly (no more orphaned 100%-CPU compiles)

**Status:** `.pi/extensions/bendverse/index.ts` only; gate green (53 laws); no
engine or proof change. Tooling hardening after the A.41–A.42 hangs.

**Root cause.** The `bend` launcher ends with `"$BUN" …/bend2/main.ts "$@"` — no
`exec` — so `bun` is a *child* of the launcher shell. `pi.exec`'s timeout killed
only the launcher, orphaning `bun` (reparented, 100 % CPU). A leaked
`bend_spike` compile ran ~15 min; the hung `PROOF.bend` run ~12 min.

**Fix.** `execBend` now runs
`env BEND_NO_TELEMETRY=1 timeout --kill-after=5 <secs> bend …`. GNU `timeout`
signals the whole child process group (verified against a synthetic
launcher-that-spawns-a-child), so `bun` dies with the launcher; `--kill-after`
SIGKILLs stragglers. `pi.exec`'s timeout is now only a longer backstop.
Telemetry is off (no background curl / self-update subshell). Gate timeout
120→90 s, spike/goal probes 120→60 s; a green gate is ~4 s, so a cliff fails fast
with an explicit "checker expansion" message instead of frying the CPU.

**New guardrails (PLAN §7).** (1) no concrete-fuel loop application in a
proposition (A.41); (2) avoid reducible terms nested inside a proposition — keep
write values as opaque parameters, and mirror opaque `U32` selectors with a
datatype (A.42); (3) if a compile exceeds ~4× the usual time, stop and bisect the
touched file with `head -n` instead of letting the gate run.

**Verification**
- extension transpiles (`bun build … --external '*'`);
- `bend PROOF.bend` → `All terms check.` (53 laws); no stray `bend2/main.ts`.

**Note.** This session cannot exercise the new code path (the extension is loaded
at startup); it takes effect on the next pi session. The `timeout` fix was
validated standalone against a synthetic hang.

### A.44 — Checker canaries: normalization as part of the trust boundary

**Status:** new `tools/checker-canary.sh` + six canaries, plus a `bend_canary`
tool; gate green (53 laws); no engine/proof change.

**Why.** A.41–A.43 treated the expansion cliffs as time/CPU waste. They are also a
*proof-integrity* concern: `{==}` discharges *definitional* equality, so what the
checker reduces is part of the trust boundary. Both directions matter:
- **missing / stuck normalization** — a proof that should check hangs or fails,
  or passes while both sides are stuck in the same shape;
- **over-eager normalization** — a proof that must not check does (soundness).

**What.** `tools/checker-canary.sh` runs `tools/canaries/*.bend` and compares each
against its filename:
- `.pass.` — positive refl proofs that must still check: `U32.add` computes,
  `U32.is_eq` on literals reduces, `Word.cmp` on concrete words reduces through
  `Cmp.is_eq` (the reflection surface the material guards depend on);
- `.fail.` — negative controls that must still be rejected: `{False == True}`,
  `U32.add(2, 3) == 6`, and `add` non-commutativity on abstract words.
A timeout on a pass canary is reported separately as a *cliff*, not a wrong
answer. The set is 6/6 in ~0 s today. `bend_canary` exposes the same run.

**Protocol (PLAN §3.7).** When an interaction surprises us: add a canary that
captures the expected behaviour, print the actual goal with `?h`, bisect with
`head -n`, classify it (proof-engineering / checker performance / checker
soundness), and record it here (and in §5.3 if it is a boundary).

**Verification**
- `tools/checker-canary.sh` → 6 ok, 0 bad; extension transpiles
  (`bun build … --external '*'`);
- `bend PROOF.bend` → `All terms check.` (53 laws).

### A.45 — A.42 corrected: the cliff is the *concrete* wake fuel, and it has a fix

**Status:** probes only, no landed engine/proof change; gate green (53 laws).
This corrects A.42's attribution — which was contaminated by the leaked 100%-CPU
compile — and reduces the cliff to a 10-line repro plus a verified fix.

**Corrected root cause.** A.42 blamed the `set_support` branches (S3/S4). Clean
delta-debugging (remove one branch from the full mirror, time it) shows the
opposite: **S6 is the trigger**. Removing S3+S4 still hangs; removing S6 → 3 s.
Inside S6 the culprit is the *concrete* wake fuel:
`Tick.wake_z_m_preserves(U32.to_nat(3), …)` with `Tick.wake_m(i, t2, n)`.

**Minimal repro** (in-repo; needs `src/`):
```python
import Base
import ./src/tick.bend as Tick
import ./src/refine.bend as R
import ./src/settle.bend as S

def th_con(+t: R.PT, +base: U32, +n: U32, +i: U32)
  -> {S.suml(S.to_pots(R.pack(Tick.wake_z_m(U32.to_nat(3), 0, i, t, n)), base, n))
      == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  Tick.wake_z_m_preserves(U32.to_nat(3), 0, i, t, n, base)
```
Concrete fuel: **>30 s (timeout)**. Change *only* `U32.to_nat(3)` to an abstract
`+wf: Nat`: **4 s, checks**. One literal vs a variable decides the cliff.
Mechanism: with concrete fuel the checker unrolls the 3·3·3 wake loop, and to
reduce `pack`/`to_pots`/`suml` over the result it case-splits the abstract tree at
every `swap_m`/`tget` (the A.37 partial-refinement behaviour) — a large /
exponential normal form. Abstract fuel is stuck at the first `match` and never
unrolls.

**Verified fix.** Parameterise the mirror over the wake fuel and keep it abstract:
`sup_m(…, +wf: Nat)` using `Tick.wake_z_m(wf, 0, i, t2, n)` and
`Tick.wake_z_m_preserves(wf, …)`, instantiating `wf := U32.to_nat(3)` only at the
top-level engine binding. The full `sup_m_preserves` (all ten selectors, S6
included) then checks in **5 s**, and the Φ theorem holds for *all* wake fuels
(stronger). This unblocks `G10`.

**Assessment.** A Bend2 normalizer performance issue, not a wrong answer: a
concrete-fuel recursion inside a proposition is fully unrolled, and the resulting
term is then normalised through `pack`/`to_pots`. The workaround is robust and
general: **never put a concrete-fuel loop application in a type; thread the fuel
as an abstract parameter and instantiate at the use site.**

**Verification**
- `bend PROOF.bend` → `All terms check.` (53 laws); probe files removed; no strays.

### A.46 — History policy: immutable bodies + superseded pointers

**Status:** docs only (`HISTORY.md` preamble, `AGENTS.md`, `PLAN.md`); gate green
(53 laws); no code.

**The change.** Strict "append-only, never touch" was correct in spirit but wrong
for a log whose entries are written in present tense: a stale entry reads as
current and a targeted retrieval (e.g. `bend_plan HISTORY section=A.42`) returns a
superseded claim with no warning. Policy is now: **entry bodies are immutable**
(never rewrite what an entry claimed), but a superseded entry carries a one-line
pointer at its top — `> **Superseded by A.n** — what changed` — which is
annotation, not a rewrite. `LAWS.bend` stays *strictly* append-only: a law's
meaning is never changed, a correction is a new law.

**Demonstration.** A.42 now carries `Superseded by A.45`; A.45 is the correction.
Provenance is intact, and a reader who lands on A.42 is no longer misled.


### A.47 — Corrections only: pointers on the wrong entries, none on snapshots

**Status:** docs only (`HISTORY.md`); gate green (53 laws); no code.

Applying the A.46 policy, but keeping it to *corrections*. Two more entries were
corrected by later ones and now carry a `Superseded by` pointer: A.32 (its
"read-after-write needs validity / subtraction injectivity" was retracted by A.35)
and A.33 (same, per A.35). A.42 already points at A.45.

Deliberately **not** annotated: entries that are merely snapshots — A.9, A.10,
A.21, A.22, A.28, A.36, A.37 and the "in progress / partial" headings. Their status
and "remains gated" lines were true when written; the preamble says as much, and
`PLAN.md` §5/§5.3 is the current state. A pointer means a claim is *wrong*, not
that time moved on.

**Verification**
- `bend PROOF.bend` → `All terms check.` (53 laws).

### A.48 — G10: the `Support.sup` fuel-loop mirror lands (`sup_m` + `sup_m_preserves`)

**Status:** one new law (`sup_mirror_preserves_phi`); gate green (54 laws); fast
22/22. The `Support.sup` half of the `G10` write-site enumeration is now
machine-checked — no crush/`set_support` site in the support pass relies on
inspection. `Rules.step` remains.

**What landed (`src/tick.bend`).**
- `SupSel` (`S0`…`S11`): the datatype selector that avoids matching an opaque
  `U32` in a proof (A.42). The `SupSel` → engine numeric-selector mapping stays a
  `G5` refinement, by inspection.
- `sup_m(fuel, t, gv, sel, i, gated, n, wf, base) -> PT & Nat`: `Support.sup`
  mirrored on `PT`. It carries the running Φ gap in the second component;
  `set_support` steps add `0`, the guarded crush (sel 6) adds `guard_gap`. The
  wake fuel is abstract (`wf`), so the 3·3·3 wake loop is never unrolled in a
  type; `sup_pass_m` instantiates it at `U32.to_nat(3)`.
- `sup_phi(r, base, n) = suml(to_pots(pack(fst r), base, n)) + snd r`; `sup_phi`
  is how the theorem mentions the mirror result **once**. `sup_add_gap`,
  `sup_phi_add_gap`, and `gap_swap_add` move a freshly added gap out of the pair.
- `sup_support_step` / `sup_crush_step`: the two writing steps, each composing
  the already-proven array write law (`array_support_write`,
  `array_guarded_crush_lowers_auto`) with the wake law via `to_pots_swap_pack`.
- `sup_m_preserves`: induction on the abstract fuel, case-split on `SupSel`,
  composing the steps. `.bendverse`-probe timing ≤5 s; the gate stays ~5 s.
- `sup_pass_m(fuel, t, n, gated)`: the top-level binding at the engine entry
  point (sel `S0`, `i = 0`, `gv = tget(t, n, 0)`, `wf = 3`, `base = 0`).
- Law `sup_mirror_preserves_phi` (in `LAWS.bend`/`PROOF.bend`): for **all**
  fuels, `sup_phi(sup_pass_m(fuel, t, n, gated), 0, n) == suml(to_pots(pack(t), 0, n))`.

**Two proof-engineering notes worth keeping.**
1. `PT & Nat` is not a projectable `let`: `+rr = sup_m(…)` is rejected (`+` wants
   a `Data`/dupable type) and a local `match rr` is rejected too. Stating the
   theorem through `sup_phi` (one occurrence, result projected inside the
   helper) sidesteps both, and `sup_phi_add_gap` handles the stuck pair
   generically by matching its `r` parameter.
2. The theorem's fuel must be `+fuel`: in the `1n+p` branch the pattern variable
   `p` occurs both in the reduced goal type and in the recursive call, which the
   linear checker otherwise reads as “consumed more than once”.

**Next.** Mirror `Rules.step` on `PT` (sel 22 crush, the fall/mov swaps) with the
same `sup_m`/`sup_phi` pattern; then the two mirrors compose to a tick-level Φ
theorem and `G10` closes.

**Verification**
- `bend PROOF.bend` → `All terms check.` (54 laws); fast 22/22.

### A.49 — G10 prep: the `deactivate` and `set_fall0` array Φ primitives

> **Superseded by A.51** — the "movement swap … same technique as
> `array_mov_swap_preserves_count`" claim below is wrong: count is
> position-blind, so it preserves; Φ depends on the leaf's y-coordinate, so the
> movement is a *decrease*.

**Status:** `src/tick.bend` only, no new law; gate green (54 laws); fast 22/22.
Two `Rules.step` write primitives now have array-level Φ theorems, so the
remaining mirror work is only the movement telescope.

**What landed.**
- `chg_fall_if` / `chg_fall` / `array_fall_write`: a `set_fall0` write preserves
  Φ at every index (mirrors `chg_support`/`array_support_write`, with
  `W.pot_set_fall0` at the leaf). Covers `Rules.step` sel 22 and sel 23.
- `chg_deactivate_if` / `chg_deactivate` / `array_deactivate_write`: a
  `deactivate` write preserves Φ (mirrors `chg_activate`/`array_activate_write`,
  with `W.pot_and_hi`). Covers `Rules.step` sel 18.

Both are internal lemmas in the `wake_*_m` style (no law wrapper yet); the gate
still elaborates them on import, verified by injecting a wrong leaf lemma into
`chg_deactivate` and seeing `bend PROOF.bend` fail at it. They are unused until
the `step_m` mirror lands, which is fine for prep lemmas.

**Remaining for `G10`.** The `Rules.step` fuel-loop mirror (`step_m`) needs the
movement swap (sel 6/12): `world[j] <- mov(w)`, `world[i] <- gv`, then wakes.
Its Φ proof is a two-swap telescope over `Refine.array_swap_decreases`, and it
needs the pot analogue of count's `nempty_tget_swap_mov` (read-after-write at a
different index) plus `W.pot_mov`. Same technique as
`Count.array_mov_swap_preserves_count`. The guarded crush (sel 22) is already
covered by `array_guarded_crush_lowers_auto`.

**Verification**
- `bend PROOF.bend` → `All terms check.` (54 laws); fast 22/22.

### A.50 — Repo shape: `runners/` + `test/`, and a `scenarios/` fixtures module

**Status:** restructure only — no engine, law, or proof change; gate green
(54 laws); fast 22/22; sim 8/8. This makes the existing boundaries explicit
instead of changing behavior.

**The split.** `app/` bundled two different things — *runners* (visibility) and
*tests* (verification evidence). Now:
- `runners/ascii.bend`, `runners/window.bend` — thin front-ends;
- `test/tests.bend`, `test/simtests.bend` — golden tests;
- `scenarios/fixtures.bend` — shared setup (`spawn`, `pull`) moved out of
  `src/sim.bend`, which is now only `build`/`phase`/`tick`/`ticks` (and drops its
  now-unused `grid`/`cell`/`ops` imports).

**Wiring updated.** `main.bend`; the runners'/tests' imports (`Fixtures.*`); the
pi extension (`.pi/extensions/bendverse/index.ts`): `bend_test`/`bend_run`
paths and the sim-cache mtime dirs (`src` + `test` + `runners` + `scenarios`);
`AGENTS.md` code layout/workflow; `PLAN.md` §2.11, §3.1, §3.5, §6.
`HISTORY.md` bodies are immutable and still say `app/…` — they are snapshots.

**Note.** The extension is loaded at pi startup (A.43), so this session's
`bend_test`/`bend_run` still held the old paths; the suites were verified by
shell (`bend test/…`), and the new paths take effect next session.

**Verification**
- `bend PROOF.bend` → `All terms check.` (54 laws); `bend test/tests.bend` 22/22;
  `bend test/simtests.bend -o bin && ./bin` 8/8; `bend runners/ascii.bend` runs;
  extension transpiles (`bun build … --external '*'`).

### A.51 — Correction to A.49: the `Rules.step` movement is a Φ *decrease*, not a preserve

**Status:** analysis only, no code; gate green (54 laws). Corrects A.49's
"Remaining" paragraph, which proposed mirroring the movement with the count
technique.

**Why count and Φ differ.** `array_mov_swap_preserves_count` holds because
`nempty` depends only on the material, so a swap of two cells' values is
position-blind. Φ is not: `pot_at(w, x) = dens(material(w)) * iy(x)` carries the
leaf's **y-coordinate**. Moving `w` from `i` down to `j = below(i)` (or
`diag_index(i, k)`) and `gv` from `j` up to `i` changes Φ by
`(dens(w) − dens(gv)) · (iy(i) − iy(j))`, which is `≥ 0` in the fall regime
(`gv` empty or lower-density), so Φ decreases by that drop. Two
`array_swap_decreases` steps therefore do **not** telescope to equality — the
residual is exactly the drop.

**Witness.** A probe with sand at `y=1` (index 4096) and empty at `j=0` checks
`after() < before()` by reflexivity: `pot(mov(sand), 0) + pot(0, 4096) <
pot(sand, 4096) + pot(0, 0)`.

**Consequence for `G10`.** The `step_m` mirror accumulates a **fall gap** in
addition to the crush gap. The movement law is a `…_lowers_phi` with gap
`(dens(w) − dens(gv)) · (iy(i) − iy(j))`, needing the fall condition
(`dens(material(gv)) ≤ dens(material(w))`) to keep it a `Nat`, and the index
relation for the drop. Note `diag_index` wraps `y` at 0, so the gap must use the
actual indices, not a constant 1. `array_swap_decreases` still composes; only the
final cancellation is replaced by a residual-gap argument.

**Next.** `fall_gap` function + `array_mov_lowers_phi`, then `step_m`
(sel 18/22/23 primitives already proven, A.49).

**Verification**
- `bend PROOF.bend` → `All terms check.` (54 laws); witness probe checks; no code
  changed.

### A.52 — The movement Φ decrease is blocked: `PT` is size-free (registered `G11`)

**Status:** analysis only, no code; gate green (54 laws). Scopes the last piece of
`G10` and registers it as `G11` rather than leaving a half-proof.

**The blocked step.** The movement law wants
`Nat.add(suml(after), gap) == suml(before)` with `gap = (dens(w) − dens(gv)) ·
(iy(L_i) − iy(L_j))`. Composing the two `array_swap_decreases` balances gives
`A1 + a == A0 + b` and `A2 + c == A1 + d` (the old/new pots at the two leaves),
so `A2 + (a+c) == A0 + (b+d)` and `gap = (a+c) − (b+d)`. That needs `a,b,c,d`
concretely — i.e. the projection `nfst(chg_m(t, base, n, i, v)) ==
pot_at(tget(t,n,i), base+i)`.

**Why it fails.** `PT` carries no size: `PL` is a leaf regardless of the `n` it is
handed, and `chg_m`'s `PL` case returns `pot_at(x, base)`, ignoring `i`. So the
projection's `PL` case requires `iy(base) = iy(base+i)`, which is false for
`i ≠ 0` (a spike fails there immediately). Equivalently, the leaf's linear index
is not recoverable from `(base, i)` alone. Worse, a *single* swap can raise Φ
(`b > a` when the target is lighter and the source moves down), so the two
balances cannot be collapsed by a per-step gap — only the net over the pair
decreases, which is exactly the quantity the projection would expose.

**Routes to close `G11`.** (1) A `leaf_base(t, base, n, i)` function plus a
`chg_m` projection against it, then a `leaf_base`-difference gap; (2) a
size-indexed `PT` (a `PL` constructor that pins `n = 1`), which makes the `PL`
projection definitional; or (3) a direct list-surgery proof that the concrete
pot segment around `i`/`j` is `fall_before(D, G, L)`/`fall_after(D, G, L)`, then
invoke `fall_lowers_world` (settle.bend). Option (1) is the least invasive.

**What is *not* blocked.** The support-pass mirror (A.48), and the `Rules.step`
write primitives for `deactivate` (sel 18) and `set_fall0` (sel 22/23) (A.49).
`G11` gates only the movement sites and the tick-level Φ composition.

**Verification**
- `bend PROOF.bend` → `All terms check.` (54 laws); projection spike fails at
  `PL` as described; no code changed.

### A.53 — `G11` closed: `leaf_base` unblocks the movement Φ telescope
> **Superseded in part by A.54** — the Nat order lemma *is* provable; `step_m` is not blocked on it.

**Status:** proof. Gate green (56 laws). Adds `src/fall.bend` and the laws
`array_mov_cross` and `array_mov_lowers_phi`; closes `G11` and the movement
write site of `G10`.

**The fix.** A.52 located the blocker in the size-free `chg_m` projection.
`leaf_base(t, base, n, i)` returns the index of the `ALeaf` holding `i` — the
base `chg_m` actually uses — so `nfst`/`nsnd(chg_m(t, base, n, i, v))` project
onto `pot_at(tget(t, n, i), leaf_base(...))` / `pot_at(v, leaf_base(...))`, and
the `PL` case is *definitional* (the failed `base + i` form was not). `swap_balance`
then turns `dec` (V2b) into the one-write balance `Φ(swap) + old == Φ + new` at
that leaf, and two of them compose:

    Φ(t2) + (p + q) == Φ(t) + (r + s)

with `p, q` the source/target pots at their own levels and `r, s` the same words
at the swapped levels. This is the telescope A.52 said was missing: the two
single-write balances *do* combine; the residual is exactly the pair's net pot
change, not a per-step gap. A read at `i` after a write at `j` is handled by
`pot_swap` (the write either misses `i` or writes `mov(w)`, whose material is
`w`'s), mirroring the count-level `nempty_tget_swap_mov`.

**What landed.** `src/fall.bend`: `leaf_base` plus its shape-invariance under
`swap_m`, the `chg_m` projections, `swap_balance`, `pot_swap`, `mov_m`, and the
`pots_m`-level cross law `mov_cross`; array-level `mov_array` and
`array_mov_cross`. Then `mov_S`/`mov_T` name the two cross terms,
`fall_gap := mov_S − mov_T`, and `array_mov_lowers_phi` gives
`Φ(mov_array) + fall_gap == Φ` under the fall-regime hypothesis
`mov_T + fall_gap == mov_S`. The hypothesis is a law parameter, not a gap: it
is the statement that the move is a fall (the target leaf is not heavier and not
higher), which the engine's `can` check supplies.

**Residual (recorded under `G10`, not a new gap).** Discharging
`mov_T + fall_gap == mov_S` from `dens(gv) ≤ dens(w)` and
`iy(leaf_base j) ≤ iy(leaf_base i)` is Nat arithmetic (`T + (S − T) = S` for
`T ≤ S`) that `src/nat.bend` does not yet provide; `step_m` (the remaining
`Rules.step` fuel-loop mirror) needs it, and accumulates the crush gap and the
fall gap together. The movement *write site* itself is proven, so `G11` is
closed.

**Verification**
- `bend PROOF.bend` → `All terms check.` (56 laws).
- `bend test/tests.bend` → all PASS (JS, T5–T21).
- `bend test/simtests.bend -o /tmp/bendverse/Bendverse-simtests && ./…` →
  T1, T2, T3, T4, T4b, T9, T18, T20 all PASS.

### A.54 — The Nat order lemma is provable: `Equal.cong` as false-elimination (`step_m` unblocked)

**Status:** proof + test. Gate green (57 laws). Corrects the A.53 residual note:
the `T + (S − T) = S` arithmetic is **not** blocked. Adds `n_add_sub_le`
(`src/nat.bend`), law `array_mov_lowers_phi_regime`, and the T22 runtime twin.

**The insight.** A.53 argued the regime could not be turned into a proposition
because Base has no false-elimination primitive. That is wrong.
`Equal.cong(Bool, A, f, False{}, True{}, h)` yields `{f(False) == f(True)}` for
*any* `f : Bool -> A`, so choosing `f(z) = Bool.pick(A, z, R, L)` gives
`{L == R}` for any goal at any type — a full false-eliminator. `src/word.bend`
already used exactly this to close the impossible `LT`/`GT` branches of
`Word.cmp` equality reflection (A.37); the A.53 note simply missed it. So a
decidable guard *can* be reflected into a proposition.

**What landed.**
- `NatL.n_add_sub_le(a, b, h : is_ge(a,b) = True) : {b + (a − b) == a}` —
  induction on `a, b`; the unreachable `0 / 1+p` case is closed by the
  `Bool.pick` motive. `src/nat.bend` had `n_sub_add` (the other direction) but
  not this.
- Law `array_mov_lowers_phi_regime` (`src/fall.bend`): the fall-regime
  hypothesis is the single order Bool `Nat.is_ge(mov_S, mov_T) == True`, and the
  gap identity `mov_T + fall_gap == mov_S` follows from `n_add_sub_le`. This is
  the cleanest regime form — an order *test*, not a carried witness, and no
  subtraction in the statement.
- T22 runtime twin (`test/tests.bend`): the concrete movement account
  `after + gap == before` with
  `gap = (dens(w) − dens(gv)) · (iy(i) − iy(j))`, for an empty target (gap 100)
  and a lighter non-empty target (gap 20), plus `mov`-preserves-pot at the
  target and `before ≥ after`.

**Note (checker limit, not a soundness issue).** A runtime twin over
`Array.swap.go` (the full array-level cross) hits a Bend elaborator limit: the
identical snippet typechecks standalone, but inside `test/tests.bend` it reports
“an open Array element type”. T22 therefore stays at the point level; the
array-level cross itself is kernel-proven (`array_mov_cross`).

**Next.** `step_m` is unblocked: its movement site can carry the regime Bool and
apply `array_mov_lowers_phi_regime`. The remaining design choice is whether to
show the engine's `can` guard implies the regime (needs `U32`/`iy` order
reflection) or to add the regime to the mirror's guard.

**Verification**
- `bend PROOF.bend` → `All terms check.` (57 laws).
- `bend test/tests.bend` → 23/23 PASS (incl. T22).
- `bend test/simtests.bend` native → T1, T2, T3, T4, T4b, T9, T18, T20 PASS.

### A.55 — `step_m` scoped: the pair invariant and two normalisation cliffs

**Status:** analysis only, no code (the mirror typechecked but its preservation
law did not land); gate green (57 laws). Scopes the `Rules.step` mirror and
records two expansion triggers so the next attempt starts warm.

**Design that typechecks.** A `StepSel` datatype (numeric selector -> constructor,
the `G5` refinement by inspection, as with `Tick.SupSel`) and
`step_m(fuel, t, gv, sel, i, c, w, k, wf, n, base) -> StepRes{t, gv, da, db}`.
Because a movement is only a Φ decrease *under the fall regime*, the mirror does
**not** carry a single gap and does **not** add a guard; it carries a **pair** of
accumulators with the invariant `Φ(current) + da == Φ(start) + db`: a movement
adds `mov_S`/`mov_T` (from `mov_cross`), a guarded crush adds `guard_gap`/`0`,
and every other write preserves both. This is unconditional and faithful (the
engine's `can` check is never re-derived).

**Two cliffs (both are the known PLAN §7 triggers).**
1. *Concrete wake fuel in a proposition (A.41/A.45).* `wake_m` is
   `wake_z_m(U32.to_nat(3), …)`; mentioning it in a lemma *statement* makes the
   elaborator unroll the 3-fuel loop. Fix: thread `wf : Nat` abstractly through
   `step_m` (exactly as `sup_m` does), instantiate `3` only in the top-level
   `step_pass_m`. After that the whole module checked in ~4 s.
2. *Two potential presentations.* `mov_cross`/`mov_lowers_phi` live over
   `pots_m`, while the `pt_wake`/array-bridged laws live over
   `to_pots(pack t)`. Mixing them in one goal fails definitionally. Fix: keep a
   single presentation per helper and bridge explicitly (`pt_swap_phi`,
   `pt_mov_cross` via `afst_swap_m`/`to_pots_swap_pack`).

**Composition that was left unfinished.** `sr_add_phi` (compose the inner
invariant with one write's balance `Φ(after) + ds == Φ(before) + dt`) and the
selector-by-selector `step_preserves` were ~90% written; the remaining failures
were presentational (the `pt_crush` bridge), not conceptual.

**Also learned.** Bisect probes with `head -n` *inside `src/`* (relative imports
do not resolve under `/tmp`), and never launch a 300 s compile on an unknown
cliff: prefixes through the mirror checked in 4 s, the cliff was found in one
40 s probe.

**Next.** Rebuild `src/step.bend` with `wf` from the start and the pair
invariant, land `step_preserves`, then the `step_pass_m` top-level law
(`Sim.phase`'s `step_m(16777216, pack-unpack world, 0, c)`), closing `G10`.

### A.56 — `G10` closed: the `Rules.step` fuel-loop mirror (`step_m`) and the pair invariant

**Status:** proof. Gate green (58 laws). Adds `src/step.bend` and law
`step_mirror_balance`; closes `G10`, the last residual of `G2`, so both engine
write-site enumerations (`Support.sup`, `Rules.step`) are machine-checked. The
mirror's selector/read threading is by inspection (the `G5` caveat).

**The pair invariant.** A move is only a Φ decrease under the fall regime, so
`step_m` does not commit to a single gap. It returns
`StepRes{t, da, db}` and follows the engine on the invariant

    Φ(current) + da == Φ(start) + db

Every write composes its **exact** leaf balance `(old pot, new pot)` through
`sr_add_phi`; a wake (`wake_z_m`) preserves Φ and is folded by `sr_phi_cong`.
The identity is unconditional — the engine's `can`/fall-regime is never
re-derived — which is what A.55 sized up and left to land.

**What landed.**
- `StepSel` (numeric selector -> constructor, the `G5` refinement by inspection,
  as with `Tick.SupSel`) and `step_m(fuel, t, gv, sel, i, c, w, k, wf, n, base)`:
  the whole `Rules.step` selector machine mirrored on `PT`, including both
  movement sites (sel 6 `mov(w)` at `below(i)`, sel 12 plain `w` at `diag_index`),
  the guarded crush (sel 22), `set_fall0` (sel 23), deactivate (sel 18), and the
  wakes. The wake fuel is threaded as an abstract `Nat` (`wf`); `3` is
  instantiated only in `step_pass_m` (A.55 cliff 1).
- `wr_old`/`wr_new` and `pt_write_balance`: one write's exact balance at the
  array (`to_pots`) presentation, `Refine.swap_balance` transported across
  `to_pots(pack(swap_m ..)) == pots_m(swap_m ..)`.
- `sr_add`/`sr_add_phi`: the one-write composition (pure Nat shuffling),
  `sr_phi_cong`: retargeting an inner invariant across an equal-Φ wake.
- `step_preserves`: the all-fuel theorem, selector by selector.
- `step_pass_m` + law `step_mirror_balance`: the `Sim.phase` entry point
  (`step_m(fuel, pack-unpack world, 0, c)`, wake fuel `3`).

**Two things that kept the proof small.**
1. *Exact balances, not named gaps.* Using `wr_old`/`wr_new` at every write
   avoids threading a `material(w) == material(tget(t,i))` invariant: at the
   movement sites the source value `w` is the **pre-deactivation** value carried
   from sel 18, so it differs from the current (deactivated) leaf in the active
   bit. The balance `(old pot, new pot)` is exact regardless, and the folded
   `da`/`db` equal `mov_S`/`mov_T` only when that material equality holds (which
   it does in the engine, by construction).
2. *Nested `sr_add`, not one combined gap.* Composing the two writes/wakes of a
   movement as nested `sr_add_phi` steps (with `sr_phi_cong` across the wakes)
   reuses the single generic Nat lemma instead of a bespoke telescope per site.

**Verification**
- `bend PROOF.bend` → `All terms check.` (58 laws).
- `bend test/tests.bend` → 23/23 PASS.

**Next.** `V3c` (schedule invariance), then `M7d`. `G10` closing is the
per-claim refinement `G5` asked for at the write-site level; the remaining
`G5` instance is the selector/read threading of the mirrors, by inspection.

### A.57 — V3c scoped: the phase fold is an ordered cascade, not a local recomputation

**Status:** analysis + witnesses, no new laws (gate green, 58 laws). `V3c`
(schedule invariance) is deferred: the naive target statement is **false**, and
the two runtime witnesses below pin down why. `G3` stays open with a sharper
"closes by".

**Target statement.** "A region-split fold equals the sequential fold": that
splitting a phase's cell range into regions, folding each, and combining gives
the same world as the global scan (`Rules.step`, index order).

**Why the naive form is false (both runtime-witnessed).**
1. *Contention is an ordered cascade, not a single winner* (T23). Two
   same-phase movers can target the same cell and **both move**. `sand` at
   `(4,40,4)` and `rubble` at `(6,40,4)` both slide onto `(5,39,4)`: scan order
   puts sand first, then rubble re-reads the just-written sand
   (`100 < 150`) and overwrites it, taking the sand into its own source. The
   target ends `rubble` (`4`), its source `sand` (`2`). Plan §2.5's prose
   ("later movers see the target occupied and stay") describes the *blocked*
   case only; a denser later mover passes the density guard. So the phase result
   is a function of the ordered candidate list, not of a local winner predicate.
2. *Activity propagates within a phase* (T24). `Ops.wake` activates all 26
   neighbors immediately, and the scan visits newly activated cells whose index
   is later, in the **same** phase. `i` at `(4,40,4)` slides onto `(5,39,4)`,
   waking the **inactive** `sand` at `(6,40,4)`, which is then evaluated and
   falls to `(6,39,4)`. So a cell's output is *not* a bounded-radius function of
   the initial state — the activation chain (and with it the dependency cone)
   grows along the scan direction. Rule 9's prose says "marks its neighbors
   active next tick"; the implementation also pulls them in this tick when they
   are scanned later.

Together: the phase fold is a **forward fold over the global index order** with
a local per-cell transition, where writes can (a) overwrite a shared target and
(b) activate later cells. It is deterministic by construction (fixed scan), but
it is not a local recomputation, and it cannot be region-split freely.

**What IS proven (the parallel-safety contract that stands).** `V3a` gives write
confinement — a move target is always in a *different* phase color — and `V3b`
gives the two properties a contended parallel fold can use: the candidate set
targeting a cell is local (`neighbor_cancel`, torus radius 2) and the tie-break
order is total (`scan_order_total`). So contention is local; what remains is the
*order*, and the activation closure.

**Decomposition for a future attempt.**
- **V3c-0** (tractable): engine-level target-phase separation —
  `color_of(below(i)) != color_of(i)`, likewise `side_index`/`diag_index` — the
  `Rules`-level form of V3a, and a `Rules.side_index`/`diag_index` candidate-set
  locality lemma restating `neighbor_cancel`.
- **V3c-1**: extract a one-cell transition from `Rules.step` and prove the
  global fold is its left fold over index order. This is the real prerequisite
  and is where the engine's selector machine must be reflected (the same `G5`
  by-inspection caveat as `step_m`).
- **V3c-2**: characterise the phase's *evaluated set* as a forward closure
  (monotone in index). No bounded radius exists; the cone can span a region.
- **V3c-3**: the equivalence a sound parallel fold needs — either regions
  processed in index order with the intra-phase wake dependency respected (i.e.
  essentially sequential, and not a speedup), or an explicit model change that
  makes the activation closure a fixed point computed before any parallel write.
  The latter must be shown to preserve the sequential result; it is the open
  research question, and it is a *model* change, not a scheduling one.

**Consequences.** `M7d` (parallel phase folds) stays blocked on `G3`; the
verified safety contract is V3a+V3b. The intra-phase activation (finding 2) is
also worth a human design decision: if rule 9's "next tick" is the intent, the
fold's activity closure is the model bug; if not, it is the scheduling blocker.

**Verification**
- `bend PROOF.bend` → `All terms check.` (58 laws; no law changed).
- `bend test/simtests.bend` native → 10/10 PASS, incl. the new **T23**
  (contention cascade) and **T24** (intra-phase activity) witnesses.

### A.58 — V3c-0 (partial): every `Rules` write target is a `dy = −1` neighbor

**Status:** proof. Gate green (59 laws). Adds `src/phase.bend` and law
`below_write_flips_y_phase`. This is the provable fragment of V3c-0 (the
`Rules`-level form of V3a); `G3` stays open with a sharper remainder.

**What it proves.** Every cell `Rules.step` *writes* is a neighbor with
`dy = −1`: `below(i)` for the fall (sel 6) and impact crush (sel 22), and
`diag_index` for the diagonal slide (sel 12). For any `dy = −1` neighbor the
`iy` parity flips, so the phase color's `y` bit — which is exactly
`par32(iy i)` — flips too: a phase's writes never land on a cell in the same
`y`-phase. The side cell (`side_index`, `dy = 0`) is read only and keeps the
parity.

**What landed (`src/phase.bend`).**
- `iy_par`: the general `y`-component of the neighbor parity,
  `par32(iy(neighbor(i, dx, dy, dz))) = xor(par32(iy i), par32 dy)`, by lifting
  `Priority.u32_iy_neighbor_full` through `par32` (`par32_mask6`, `par32_add`).
- `neighbor_y_flip` / `neighbor_y_keep`: the `dy = −1` and `dy = 0` instances.
- `below_y_flip` + law `below_write_flips_y_phase`.

**Why not the full color separation (the honest remainder).** Two pieces remain
for "the target's *color* differs, not just its `y` bit":
1. **`color_of` bit extraction.** `par32(shr 1 (color_of i)) = par32(iy i)`
   needs a small `Word` bit library (`bit0` distributes over `or`/`and`,
   `shr`/`shl` distribution, `and(w, 1)` bit facts). The first bricks check
   (`par32_or`, `par32_and`, `par32_and1`, `par32_shl`, `par_shr1_or`,
   `shr1_shl1`, `shr1_and1_zero`), but the full chain is a real tail and was
   time-boxed out rather than forced.
2. **`k < 4` bounds for `diag_index`/`side_index`.** Both are `match`-guarded on
   `k` with an `_ -> i` fallback, so their per-branch statements need the
   engine's `k ∈ {0,1,2,3}` invariant threaded (the same by-inspection `G5`
   caveat as the `step_m`/`sup_m` selectors).

**Why it is still worth landing.** It is the adjacency half of V3c's conflict
freedom, at the `Rules` level rather than the model level, and it is
unconditional. A.57 established the *hard* part is order (the contention
cascade and the intra-phase activation), not adjacency; this closes the part
that was cleanly provable.

**Verification**
- `bend PROOF.bend` → `All terms check.` (59 laws).
- `bend test/tests.bend` → 23/23 PASS.
- `bend test/simtests.bend` native → 10/10 PASS (A.57 witnesses included).

### A.59 — M9 CPU perf pass: render resolution, settled fixpoint, color-restricted phases

**Status:** performance. Gate green (59 laws; no law changed). Touches the
imperative engine (`src/sim.bend`, `src/rules.bend` scan advance, `src/grid.bend`
helpers) and the window runner; adds the fast-suite witness T25. No proof burden
added — this is a deliberate stop on proof work, so the change is
behaviour-preserving by construction and witnessed by the existing golden/sim
suites plus T25.

**Baseline (native, 64³).** Before this entry a tick was **≈ 21 ms and flat**:
`Sim.build()` ≈ 7 ms, and a tick cost the same whether the world was settled or
active. The cost was the 262144-cell × ~9-pass scan (support + 8 color phases),
not per-cell work. The landed entry-level measurement was in `PLAN.md` §5.2.

**Win 1 — render at cell resolution (`runners/window.bend`).** The view built a
256×256 quadtree whose every 4×4 leaf block read the same cell, then grouped
65536 leaves up to a root. It now builds a 64×64 quadtree (one leaf per cell) and
lets `Window.frame` scale it: 16× fewer `Array.get`s and ~16× fewer `Qua`/`Pix`
nodes per frame. The leaf index changed from
`index(x0>>2, 63-(y0>>2))` at depth 8 to `index(x0, 63-y0)` at depth 6; the
`render` recursion (which fixes the quadtree orientation for `levels`) is
untouched, so the 64² image is exactly the 256² image downsampled by 4.

**Win 2 — settled-world tick fixpoint (`src/sim.bend`).** Rule 9's active bit
gates both passes: `Support.pass` is activity-gated and `Rules.step` skips
inactive cells, so a world with no active cell is a whole-tick identity.
`Sim.any_active` walks the flat array with an OR accumulator (carrying the
`(world, value)` pair and `i+1` the way `Rules.step` threads state) and `tick`
returns the world unchanged when the accumulator is false. Measured: settled
tick **≈ 21 ms → ≈ 0.09 ms** (1000 settled ticks in 89 ms excluding build). The
scan is one pass and effectively free next to a running tick.

**Win 3 — color-restricted phase scan (`src/grid.bend`, `src/rules.bend`).** A
phase `c` acts only on cells with `color_of(i) == c`; the other 7/8 of the flat
scan were visited and skipped. `Grid.color_at(s, c)` enumerates the color-c
sublattice in strictly increasing flat-index order — with `cx = c&1`,
`cy = (c>>1)&1`, `cz = (c>>2)&1`, `base(c) = cx | (cz<<6) | (cy<<12)`, the
sublattice is `base + 2*(s&31) + 128*((s>>5)&31) + 8192*(s>>10)` for
`s ∈ [0, 32768)` — and `next_color`/`color_last` are its successor and terminal.
`Sim.phase` starts at `Grid.color_base(c)`; `Rules.step`'s advance cases 14/16
now test `i == color_last(c)` and step to `next_color(i, c)`. The machine still
visits the *same acted-on cells in the same order* (a color mismatch was already
a no-op), so the fold is unchanged; it just visits 32768 cells per phase instead
of 262144. Measured: active tick **≈ 21 ms → ≈ 4.5 ms**; `build+pull+30 ticks`
0.62 s → 0.036 s (the settled tail is now ~0.09 ms each). T25 checks the
sublattice (every `color_at(s,c)` is color `c`, `next_color` is the successor,
the order is strictly increasing, and `color_last(c)` is the last cell).

**Correction to the planned win list (honest).** `PLAN.md` had listed win 3 as
"skip sleeping regions in the scan (reuses the M8 store)". That is **not**
semantics-preserving on its own: T24 (A.57) shows a phase's `Ops.wake` activates
same-color cells *later in scan order*, which the same phase then evaluates — so
a pre-phase activity snapshot would drop real work. A sound region skip needs a
worklist updated by `wake`, or a neighbourhood margin (a chunk whose 3×3×3
neighbourhood is inactive cannot be written this tick), and the intra-phase
activation question is exactly `V3c`/`G3`. The color scan gives the dominant part
of the scan win without touching that semantics, and it is independent of V3c.
Region-level skipping is therefore folded into the `V3c`/`G3` track rather than
landed here.

**Mirror note (G5).** `src/step.bend`'s `step_m` mirror still scans the flat
index space (`i+1`, terminal 262144); only the engine's advance changed. The
mirror's per-write-site Φ balances are unaffected (they are per-site, not per
scan domain), but the "by inspection" scan correspondence is now coarser. This is
recorded, not closed.

**Verification**
- `bend PROOF.bend` → `All terms check.` (59 laws; gate unchanged).
- `bend test/tests.bend` → 24/24 PASS (T25 added).
- `bend test/simtests.bend` native → 10/10 PASS (T23/T24 included, so the
  ordered-cascade and intra-phase-activation witnesses still hold).
- `bend_canary` → 6 ok, 0 bad.
- Native 64³: settled tick ≈ 0.09 ms (was ≈ 21 ms); active tick ≈ 4.5 ms (was
  ≈ 21 ms); `build+pull+30 ticks` 0.62 s → 0.036 s.

### A.60 — BendHub survey; imported `List` lemmas and count-fold completeness

**Status:** reuse landed (gate green, 59 laws unchanged); publishing recorded as
deferred (`P1`, §5.4).

**What was surveyed.** BendHub is a static, account-free store (`GET /index.json`;
raw files at `/<hash>/<file>`): 69 packages, 312 files, ~1.8 MB. Ranked by actual
proof content, ~30 packages are one author's "definitional laws" template
(`LAWS`/`PROOF`/`lib`/`seal`, ~550 `{==}` reflexivity proofs, zero induction).
Six packages carry real induction: `list.bend` (`0x085d89db…`), `string.bend`,
`nat.bend`, the `0xd5e93625…` math library (5 026 LOC: `Dvd`, Bezout `Cop`,
Euclid by subtraction, Gauss's lemma, `sqrt2`), tinygrad and bend-ml bills. The
hub's `GLIDER` Life package (`0xbdd0ed82…`) has **no** proofs; its lemmas come
from the book repo `github.com/nohzafk/bend2-from-zero`, which owns the actual
cellular-automaton proofs.

**Landed.**
- `src/list.bend` — the six `List` lemmas Base does not ship (`append_nil2`,
  `append_assoc2`, `reverse_go_spec`, `reverse_append2`, `reverse_reverse`,
  `length_append`), imported from `0x085d89db…` and checked verbatim in Bend
  2.0.5. It is indexed by `bend_lemmas`, and since `Settle.app` *is*
  `List.append(&2, Nat, …)` the lemmas apply without a bridge. Verified
  load-bearing by a mutation test (a false `length_append` turns the gate red),
  so the module is not silently unchecked.
- `src/count.bend` — `cells_m` (leaves of the `PT` model) and
  `cnts_m_len`/`to_counts_len`: the count fold emits **exactly one entry per
  leaf**. This is the half of rule 2 that `suml` alone cannot state (mass could
  be conserved while dropping a cell), and `cnts_m_len` consumes
  `ListL.length_append` — the hub import doing real work.

**Findings.**
- Nothing else was needed: `nat.bend` duplicates `src/nat.bend`, and the math
  library is 250 KB of a foreign `Nat`/`Int` stack that would clash with ours —
  its value is idioms (`Equal.trans/cong`, `Empty.absurd`, `Data` records as
  reusable propositions), not code to vendor.
- **Linearity confirms `G8` in practice.** An `Array` parameter cannot be marked
  reusable (`+a: Array<U32>` is rejected: "expected Data, observed Type"), so the
  hub's `reverse_go_spec` shape — which names its list argument twice — does not
  transfer to `Grid.to_list_go`. Array-side statements must go through `PT` and
  `pack`, which is exactly why `to_counts_len` is stated on `R.pack(t)`.
- Prior art for `G3` (recorded in §5.3): `bend2-from-zero`'s
  `life/LIFE_PAR_PROOF.bend` proves `tree_is_serial` by depth induction with a
  `cells_add` loop-split lemma. It is the nearest public claim to V3c, but it
  proves equal *outputs* only and is silent on contention — precisely the T23/T24
  counterexamples — so it is a shape to borrow, not a theorem to reuse.

**Deferred.** Publishing is recorded in `PLAN.md` §5.4 (and as `P1` in §5.2):
`bend --publish` refuses an open law or a TODO, and a hash is permanent, so a
publish must be a standalone proven slice, `G7` should be closed first, and the
`seal.bend` convention adopted. Candidate first uploads: the `U32`/word bit
lemmas (the hub has **zero** laws on `U32.and/or/xor/shl/shr`), then
`src/list.bend` + the completeness lemmas, then the Φ telescope and conservation.

**Verification**
- `bend PROOF.bend` → `All terms check.` (59 laws; count unchanged).
- `bend test/tests.bend` → 24/24 PASS; `bend test/simtests.bend` native → 10/10
  PASS (no runtime code touched).
- `bend_canary` → 6 ok, 0 bad.
- Mutation test: a falsified `length_append` makes the gate red, proving
  `src/list.bend` is traversed by the checker.

### A.61 — Semantics rewrite: the contract, the conformance table, and `V0`

**Status:** specification and governance. **No engine behaviour changed** — gate
green, 59 laws, both suites pass. This entry exists so the next session cannot
mistake the old shape's assumptions for decisions.

**Why.** Reading `coreidea.md` against the code (prompted by A.57/A.58 and the
BendHub survey in A.60) showed that the load-bearing rules were not merely
imprecise — several were *false of the engine they governed*, and nothing
mechanical said so. The test suite was the de facto specification, which is
exactly why T23/T24 landed as "hard cases" instead of conformance failures.

What is actually wrong, with evidence:

1. **Rule 3 vs T23.** `Rules.step` sel 6/12 writes its target unconditionally,
   and a later same-colour mover re-reads the freshly written target
   (sel 5: `Array.get(world, Grid.below(i))`) and passes the density guard
   (`100 < 150`). Two applications write one cell in one phase. This is the
   "silent overwrite" rule 3 forbids, not a tie-break.
2. **Rule 9 vs T24.** `Ops.wake` activates immediately, and sel 16 advances via
   `Grid.next_color` to a cell first read *now*, so sel 0 evaluates a cell the
   same phase woke. Rule 9 says next tick; `PLAN §2.9` said "immediately" and so
   agreed with the bug.
3. **Rule 4 is unachievable as written.** "No two cells being updated are
   neighbours ⇒ zero coordination" ignores that a move also writes the *target*,
   and two same-colour cells can share one (`(4,40,4)`/`(6,40,4)` → `(5,39,4)`,
   both colour 0). Zero coordination is a property of the *schedule*, not of the
   colouring alone.
4. **Rule 1 as worded conflicts with conflict resolution**, which must read other
   cells' targets.
5. **The box is a convention, not a fact.** `Grid.neighbor` wraps mod 64 on all
   axes, so `below` at `y=0` is `y=63` and Φ *increases* — outside
   `array_mov_lowers_phi_regime`'s `mov_S ≥ mov_T` regime. The world is closed
   only because `Worldgen.gen` paints bedrock on six faces, nothing proves the
   shell survives, and `runners/window.bend` paints material `0`, so the floor
   is removable from the shipped UI.
6. **C3 is false.** `Sim.any_active` and `Support.pass` each scan all 262144
   cells every tick, and `Support.sup` hardcodes that bound; the 8 phases walk
   their colour sublattice. Cost is O(world), not O(disturbance) — ~0.09 ms
   settled at 64³, ~370 s at 1024³. `src/store.bend`'s chunks and sleeping are
   not wired into the tick at all.
7. **Size is a constant in ≥4 places.** `Grid.size()=64`, `index` packs 6+6+6,
   `Support.sup` hardcodes `is_eq(ni, 262144)`, `Sim.any_active` hardcodes
   `to_nat(262143)`, and the laws hardcode `volume()`. 8 bits/axis fits the same
   U32 index for free, so 64³ is a choice, not a limit.
8. **Rule 6 and rule 7 were vibes.** There is no connected-component code; rule 7's
   "recompute whenever anything nearby changes" implied O(world) rescans.
9. **The mirror layer agrees with a non-conforming engine.** `step_m`'s
   `step_preserves`/`step_mirror_balance` faithfully mirror the behaviour that
   violates R1/R3/R4/R9. They are true, and they buy no conformance.

**What changed (specification only).**
- `coreidea.md` rewritten around a three-sentence **contract**: **C1** purity of
  phases, **C2** closure (box, no wrap), **C3** cost tracks disturbance. Rules 3,
  4, 9 and 10 are now stated as *corollaries* of C1 rather than independent
  axioms. Rule 1 now says pre-phase reads; rule 4 now specifies (colour ×
  direction) batches with a provable injective target map; rule 6 is a local
  property (no cluster analysis); rule 7 is about staleness, scoped to disturbed
  cells; rule 9 makes wake effects land next tick; rule 10 derives from C1;
  rule 11 states that the shell is generation, not grid. Rule numbers and titles
  are unchanged so existing references stay valid.
- `PLAN.md`: **§2.0** restates the contract; **§4.1** is the new conformance
  table (4 columns, so the §4 matrix parser is untouched) marking `C1`/`C2`/`C3`
  and `R1`/`R3`/`R4`/`R9`/`R10` **deviating**, with evidence; §2.1 records the
  torus; §2.12 reframes determinism as a consequence of C1; §3.4 adds
  **retirement** for laws orphaned by a semantics change; §5.2 adds `V0` and
  marks `V3c` superseded by it.
- `AGENTS.md`: `coreidea.md` is no longer "immutable" — it is normative and
  editable, with the edit procedure (log in `HISTORY.md`, update §4.1), plus the
  retirement rule and an explicit ban on extending `step_m`/`sup_m`.

**Decisions.**
- **Purity first.** `V0-1` (intent/resolve/apply) is the unblocker; `V3c` becomes
  a corollary, not a research problem.
- **Box, not torus.** Closed in the grid (`V0-2`), because a rule that only holds
  while the user does not paint the floor is not a rule.
- **Colour × direction batches** (`V0-3`): fixing the displacement makes target
  collision impossible, which is what makes rule 4 provable rather than asserted.
- **Freeze the mirror layer.** No further `step_m`/`sup_m` work; it mirrors the
  shape `V0-1` replaces. Sunk cost acknowledged and retired, per §3.4.
- **No band-aids.** `paint_at` was *not* patched to protect the shell, because
  the correct fix is grid-level (`V0-2`); a paint clamp would be exactly the
  "kind of right" adaptation that hides the deviation.

**Not done (deliberately).** No engine behaviour change this session, so no law
is invalidated and no law needs retiring yet. `V0-1` is the first entry that will
orphan anything, and it must land with the retirement recorded.

**Verification**
- `bend PROOF.bend` → `All terms check.` (59 laws; unchanged).
- `bend test/tests.bend` → 24/24 PASS; `bend test/simtests.bend` native → 10/10
  PASS.
- `bend_canary` → 6 ok, 0 bad.
- Nothing in `src/`, `LAWS.bend`, `PROOF.bend`, `test/` or `runners/` was touched,
  so T23/T24 still witness the *old* behaviour; they are re-witnessed by `V0`.

### A.62 — Pre-`V0` audit: slop, landmines, and one wrong constant

> **Superseded by A.81** — `Ops.shell_adjacent` was replaced by a neighbourhood
> seed read; `R6`/`R7` are now conforming.

**Status:** cleanup. Gate green, 59 laws, both suites pass (sim rebuilt). No
semantics changed — every edit is behaviour-preserving, verified by rebuilding
and re-running the native simulation suite.

**Method.** Name-level reference analysis across `src/`, `test/`, `runners/`,
`scenarios/`, `LAWS.bend`, `PROOF.bend` (defs referenced nowhere, imports whose
alias is never used), plus a read of every match/fallback site and every
world-size literal. The point was to ask, per artifact: does this fight the
direction we just committed to?

**Fixed (behaviour-preserving).**
- **`Chunk.per_axis()` deleted.** It was referenced nowhere and returned `4` for
  a 16³ chunk — a wrong constant waiting to be used. A wrong constant is worse
  than no constant. (`size()`/`cells()` remain the sources.)
- **World size / chunk size centralised.** `Support.sup` (`262144`),
  `Sim.any_active` (`262143`), `src/store.bend` (`4096` ×4), and the `step_m`/
  `sup_m` mirrors (`262144` ×4) now read `Grid.volume()` / `Chunk.cells()`. These
  were eight copies of "the world is 64³"; under `V0-2` (size as a parameter)
  each copy was a silent breakage.
- **`Grid.color_last` derived.** Was `color_base(c) + 257982` — a hand-computed
  literal. Now `color_at(32767, c)`, which is exactly what T25 asserts, so the
  witness's first check became definitional.
- **`Ops.adjacent_static` renamed to `Ops.shell_adjacent`** and documented for
  what it is: the support *seed* for the layer next to the bedrock shell. It is
  **coordinate-based, not a neighbourhood test** — the old name claimed a
  property it never had, and it bakes in the 64³ shell (`1`/`62` = `0+1`/`63-1`).
  Three call sites updated (`Support.sup`, `sup_m`, `sup_m_preserves`).
- **§4.1 corrected.** The rows I wrote in A.61 marked `R6`/`R7` **conforming**
  with "`Ops.adjacent_static` is neighbourhood-local; no cluster code exists".
  That was wrong on its own evidence. Both are now **deviating**: the support
  seed is positional, so "rigidity is local" is not yet true. A second,
  independent deviation group, fixed by `V0-2`/`V0-4`.
- **Dead imports removed** (`src/chunk.bend`: `grid`, `cell`;
  `test/tests.bend`: `refine`, `fall`; `test/simtests.bend`: `chunk`). An import
  whose alias is unused reads as a dependency that does not exist.
- **`PROOF.bend`'s imports annotated as the coverage root.** They look unused
  (the aliases are), but they are *load-bearing*: `bend PROOF.bend` checks every
  module reachable from that file, so removing one silently removes a module from
  the verified set — and the gate would stay green. The A.60 mutation test (a
  falsified `src/list.bend` lemma turning the gate red) is the evidence. The
  comment exists so a future tidy cannot shrug them off.
- **A.60's lemma chain labelled.** `cells_m`/`cnts_m_len`/`to_counts_len` are
  consumed by nothing; they are now marked *library, not evidence* so no later
  session reads them as a claim about the engine. This corrects my own A.60
  framing, which called them "the use" of the hub import.

**Recorded, not fixed (PLAN §4.2 "known landmines").** Silent selector default
(`Rules.step` `case _: world` ends the phase scan mid-way); silent candidate
default (`side_index`/`diag_index` `case _: i`); silent material default
(`Cell.density`/`static`/`slides`/`cohesion` `case _`, so any material id ≥ 6 is
empty-like and fall-through-able); unproven fuel sufficiency (a magic `2^24`,
~13× slack, no law); the test suite's fixed 50-tick `settle` budget (T4b does
guard the fixpoint). All are robustness debts, and all are removed or bounded by
`V0-1`.

**Checked and left alone (deliberately).**
- 52 unused-by-other-files defs in `src/bits.bend`, 52 in `src/parity.bend`, 27
  in `src/tick.bend`, etc. — nearly all are *internal proof helpers* used within
  their own file, or live *library* lemmas (`src/list.bend`). That is the repo's
  lemma library, not slop; deleting it would be churn with a loss of reuse.
- Dead-but-true Φ wrappers in `src/tick.bend` (`array_fall_write`,
  `array_deactivate_write`): superseded by the `V4` count laws delegating to the
  underlying `chg_*` functions. Inert, proof-only, frozen with the mirror layer.
- `Grid.west/east/south/north`, `Cell.decode`, `src/potential.bend`'s `dens_*`
  anchors: symmetric API surface and one-line constant anchors. Inert and true.
- `runners/ascii.bend` already shares `scenarios/fixtures.bend`; no duplication.
- `LAWS.bend`'s 59 laws, all proofs, and the witness T23/T24: untouched, because
  they still describe the *current* engine faithfully. `V0` is what retires them.

**Verification**
- `bend PROOF.bend` → `All terms check.` (59 laws, unchanged).
- `bend test/tests.bend` → 24/24 PASS.
- `bend test/simtests.bend -o bin && ./bin` (forced rebuild) → 10/10 PASS — the
  behaviour-preservation check for the constant/`color_last` edits.
- `bend_canary` → 6 ok, 0 bad.

### A.63 — V0-1: phase purity — `intent → resolve → apply`, and the first retirement

**Status:** engine semantics change + retirement. Gate green (59 laws, unchanged),
fast suite 24/24, sim suite **11/11** (rebuilt, +T26), canaries 6 ok.

**Why.** A.61 scoped `V0` and showed that `C1`/`R1`/`R3`/`R4`/`R9`/`R10` are one
problem: a phase read the array it was writing. `Rules.step` wrote `deactivate`
to the cell it was inspecting, re-read targets a sibling had just moved into
(T23, an ordered cascade), and evaluated cells it had woken in the same scan
(T24). `V0-1` is the unblocker: define the phase as a pure function
`phase(state) = apply(resolve(intent(state)))`.

**What changed.**
- `src/rules.bend`: `Rules.step` **removed**; the pure phase added.
  `Write` is `WSet{idx, val} | WWake{idx}`. `plan` is a read-only state machine
  (fuel loop, `gp` threads the array through reads and is never written) that,
  for each cell of the phase colour, decides from the *pre-phase* state, resolves
  contention, and conses its writes onto `sets`/`wakes`. `commit_sets` applies
  the value writes and `commit_wakes` applies `Ops.wake` afterwards;
  `phase_commit`/`phase` wrap them. `side_index`/`diag_index`/`color_of`/`mov`
  are unchanged (the proof layer and `Sim.phase` still use them).
- `src/sim.bend`: `Sim.phase` now delegates to `Rules.phase`; the tick pipeline is
  otherwise untouched.
- `src/step.bend`: header marks the mirror **retired**.

**Design.** Purity is structural, not incidental: `plan` cannot write the array it
reads, so no part of a phase observes another part's output. The only new rule
logic is the contention tie-break at states 30/31. Within a colour a target can be
claimed by at most two cells — the two opposite-direction diagonal claimants on
one axis (`(4,40,4)`/`(6,40,4)` → `(5,39,4)`); drop and crush targets are already
injective within a colour. The tie-break is pre-phase and order-free: if the
opposite claimant is `capable` and has the smaller flat index, this cell forfeits
to the impact path. Wake is a post-write marking pass, so a phase never pulls in a
cell it woke (rule 9). Even the wake writes are pure functions of the pre-phase
state: the woken *index set* is planned, and `activate` of the post-set value is
`activate` of a planned (hence pre-phase-derived) value.

**Witnesses (re-witnessed as conformance).**
- **T23** now asserts the target is **sand (2)**: the smaller-index claimant wins
  and the later mover forfeits — no re-read, no cascade.
- **T24** now asserts `(6,39,4)` is **empty (0)** after one phase: the woken cell
  is not in the phase's evaluated set.
- **T26 (new)** "a grain in an empty column settles": a lone grain falls straight
  down (drop has priority over sliding) and rests at `y=1` on the bedrock floor.

**Retirement (per §3.4).** `Rules.step` no longer exists, so the `step_m` mirror
(`law step_mirror_balance`) is orphaned: kept (append-only `LAWS.bend`), still
true about the old machine, **retired** as evidence and not to be extended
(recorded in §4.1). `sup_m` still mirrors `Support.sup`, which `V0-1` did not
touch, so it stays live until `V0-4`. `G10` is therefore closed *only for the
shape it enumerated*; the live `Rules.plan` write-site enumeration is recorded
as `G14` (open).

**Honest residuals (recorded, not hidden).**
- **`G12`** (new, open): wake is applied at the end of each *phase*, not
  accumulated for the next tick, so a later phase of the same tick can evaluate a
  woken cell. T24 rules out only the same-phase case.
- **`G13`** (new, accepted): the tie-break over-forfeits — a diagonal mover yields
  to a `capable` opposite-axis neighbour even when that neighbour is not actually
  claiming the shared target. Behaviour-only; `V0-3`'s batching removes the need.
- `side_index`/`diag_index`'s `case _: i` default is unchanged; `V0-3`'s
  injectivity proof must establish the `k < 4` bound.
- Fuel sufficiency is still a magic `2^24` with no law (`plan` needs ~2^19).

**Not done (deliberately).** `V0-2` (close the box), `V0-3` (explicit colour ×
direction batching + the injectivity proof), `V0-4` (drive the tick from the
chunk work set). `G3` remains open; A.63 narrows it to the batching theorem.

**Verification**
- `bend PROOF.bend` → `All terms check.` (59 laws; no law added or removed).
- `bend test/tests.bend` → 24/24 PASS.
- `bend test/simtests.bend -o bin && ./bin` (rebuilt) → **11/11** PASS.
- `bend_canary` → 6 ok, 0 bad.
- `runners/ascii.bend` native runs and settles.

### A.64 — V0-2: closure — the box is the grid's, not the shell's

**Status:** engine semantics change (only off the generated world). Gate green
(59 laws, unchanged), fast 24/24, sim **13/13** (+T27/T28), canaries 6 ok.

**Why.** `C2` was deviating: `Grid.neighbor` wraps mod 64 on every axis, and the
world was closed only because `Worldgen.gen` paints bedrock on the six faces.
Nothing proved the shell survives, and `runners/window.bend` paints material `0`,
so the floor was removable from the shipped UI. A rule that only holds while the
user does not paint the floor is not a rule (A.61).

**What changed.**
- `src/grid.bend`: `step_inside(i, dx, dy, dz)` — the closure guard. It adds the
  *raw* offset to each coordinate and tests the bits above the axis mask, which
  are non-zero exactly when `neighbor` would wrap. `neighbor` is unchanged, so
  every law about it (parity, `neighbor_cancel`, …) still holds; the guard is an
  extra predicate the rules consult.
- `src/rules.bend` (`plan`): the drop target (state 6), the diagonal target
  (state 13), the impact crush (state 21), and the contention competitor
  (state 31 — a wrapped neighbour cannot reach the shared target, so it must not
  steal it) are all `Bool.and`ed with `Grid.step_inside`. A boundary step now
  falls through to the inert path instead of wrapping.

**Why the default world is unchanged.** The generated shell already makes every
wrapped step blocked (bedrock is static and densest), so gating those steps
changes no outcome when the shell is intact. That is why the existing 11 sim
witnesses stay green unmodified; only the painted-away cases differ.

**Witnesses (new, V0-2 conformance).**
- **T27**: floor painted away — sand at `(4,0,4)` with `(4,63,4)` cleared stays at
  `(4,0,4)`; without the guard `below` wraps to `(4,63,4)` and the grain escapes
  to the top face.
- **T28**: west wall painted away, down and every in-box diagonal blocked — the
  grain at `(0,40,4)` cannot take the wrap to `(63,39,4)`; without the guard it
  slides across the box.

**No law added (deliberate).** A concrete `{==}` law (e.g. "a step down from
`y=0` is outside") would be closed-computation reflexivity, and §3.3/`G7` already
flags six such laws for review — adding a seventh increases that burden. A
*general* `step_inside` lemma needs the bit lemmas (the `~mask` argument); worth
doing when `V0-3`/`V0-4` next touch `Grid`. `C2` is therefore recorded as
**conforming by construction + witness** (T27/T28), which the §4.1 status
vocabulary allows.

**Residual (`G15`, accepted).** `Ops.wake` still marks wrapped neighbours from a
boundary cell, so with the shell painted away activity leaks to the opposite
face. No material moves, so `C2` holds; bounding `Ops.wake` would touch the wake
laws and the `sup_m` mirror, so it is recorded rather than done here.

**Not done.** `V0-3` (explicit colour × direction batching + the target-map
injectivity proof; `G3`), `V0-4` (chunk-work-set tick; `C3`). `R4`/`R9` remain
partial and `G12`/`G14` remain open.

**Verification**
- `bend PROOF.bend` → `All terms check.` (59 laws).
- `bend test/tests.bend` → 24/24 PASS.
- `bend test/simtests.bend -o bin && ./bin` (rebuilt) → **13/13** PASS.
- `bend_canary` → 6 ok, 0 bad.

### A.65 — V0-3a: direction batching — a closed direction set and an injective target map

**Status:** engine refactor (behaviour-preserving) + 3 new laws. Gate green
(**62** laws, +3), fast suite **25/25** (+T29), sim suite **13/13** (rebuilt),
canaries 6 ok.

**Why.** `R4`/`G3` asked for (colour × direction) batches with an *injective*
target map. `V0-1` resolved contention with a local tie-break but proved nothing
about the batch map, and the direction index was a raw `U32 k` with a silent
`case _: i` fallback (`PLAN §4.2` landmine): a `k` outside `{0,1,2,3}` became a
self-target. `V0-3a` closes the direction half: make the directions a closed set
and prove that a fixed displacement's target map is injective.

**What changed.**
- `src/rules.bend`: `Rules.Dir4` (`K0..K3`) — the four slide directions as a
  datatype, with `dir_dx`/`dir_dz`, `side4`/`diag4`, `dir_last`/`dir_next` total
  matches. `Rules.plan` now threads `k : Dir4`; the diagonal loop ends via
  `dir_last`/`dir_next` instead of `U32.add k 1`/`is_eq · 4`. The retired
  `side_index`/`diag_index` (`U32`, with the `case _: i` default) stay for the
  frozen `step_m` mirror; they are no longer on the live path, so the silent
  default is off the engine that runs.
- `src/batch.bend` (new): `move_inj` — for a fixed `(dx, dy, dz)`, equal targets
  force equal (torus) sources. The proof composes the assumed collision with
  `Priority.neighbor_cancel` (the translation's two-sided inverse), so it is a
  three-step `Equal` chain, not a per-cell argument. `below_inj` and `diag4_inj`
  instantiate it for the drop and for each of the four slides (the `Dir4` match
  is total).
- `src/phase.bend`: `diag4_y_flip` — a slide target has `dy = -1`, so it flips
  the phase `y` bit, matching `below_y_flip` for the drop. Every movement write
  target therefore lands on the opposite `y`-parity (colour half, `y` bit).
- `LAWS.bend`: laws `batch_target_injective`, `diag_target_injective`,
  `diag_write_flips_y_phase`; proofs in `PROOF.bend` (imports `batch.bend`).
- `test/tests.bend`: **T29** checks, over 4096 cells, that `diag4`/`side4` agree
  with the retired `diag_index`/`side_index` table for all four constructors —
  the behaviour-preservation witness for the refactor and a total-match check.

**Rule-4 reading.** A direction batch fixes the displacement, so its target map
is a translation `i ↦ neighbor(i, d)`; `neighbor_cancel` inverts it, giving
injectivity — "distinct cells have distinct targets", with no coordination. The
endpoint colour separation (every write target flips the `y` bit) is the first
of the three parity bits.

**Honest residual (`V0-3b`, `G3` narrowed).** What is *not* yet a theorem: the
*cross-direction* half. Two same-colour cells in *different* directions can still
share a target — exactly the opposite-diagonal pair (`(4,40,4)`/`(6,40,4)` →
`(5,39,4)`), which the V0-1 tie-break (T23) resolves locally. Proving they are
the only cross-direction collision needs the full `color_of` bit extraction
(`bit1(color_of i) = par32(iy i)`, then the x/z parities) and `is_ne` reflection;
`V0-3a` does not attempt it, so `R4` stays *partial* and `G13`'s over-forfeit is
unchanged. The old `side_index`/`diag_index` defaults remain in the frozen
mirror (not extended, not on the live path).

**Verification**
- `bend PROOF.bend` → `All terms check.` (62 laws; +3, none retired).
- `bend test/tests.bend` → 25/25 PASS (+T29).
- `bend test/simtests.bend -o bin && ./bin` (rebuilt) → 13/13 PASS.
- `bend_canary` → 6 ok, 0 bad.

### A.66 — V0-3b: colour × direction classification — `color_of` bit extraction and the collision theorem

**Status:** proof landing (no engine semantics change). Gate green (**69** laws,
+7), fast suite **26/26** (+T30), sim suite **13/13**, canaries 6 ok.

**Why.** `V0-3a` (A.65) proved a direction batch's target map injective, but the
*cross-direction* half of rule 4 was open: two same-colour cells in different
directions can share a target (the opposite diagonals), and there was no
theorem cutting down which pairs can. `PLAN §5.3`/`G3` named the missing piece
precisely — "bit extraction of `color_of`, `k < 4` bounds, `is_ne`
reflection" — and `src/phase.bend`'s `V3c-0` comment recorded it as the second
half of the colour separation.

**What changed (all `src/color.bend`, new).**
- **`color_of` bit extraction.** `Rules.color_of` packs the three coordinate
  parities as `(ix&1) | ((iy&1)<<1) | ((iz&1)<<2)`. The inverse is now proven:
  `color_bit0`/`color_bit1`/`color_bit2` read bit 0/1/2 back as `par32 ix`,
  `par32 iy`, `par32 iz`. The plumbing is `bit0_or`/`bit0_and`/`bit0_shl`, a
  `shr_and_mask1_zero`, and (for the 1- and 2-shifts) the `Bits` library's
  `shr_or`/`shr_n_or`, `shr_shl_one`, `shr_shl_kmask`, `shr_and`.
- **Same colour ⇒ equal parities.** `same_color_x`/`_y`/`_z` reflect colour
  equality (`Word.u32_cmp_eq`) and transport it along the extraction laws.
- **Target parity.** `target_x_par`/`target_z_par` give the `dy = -1` target's
  x/z parity as `xor` of the source parity with the displacement parity
  (`neighbor_y_flip`, A.58, already gave the y flip).
- **Classification.** `same_color_target_x_par`/`_z_par`: a same-colour target
  collision forces `par dx` equal and `par dz` equal. The only engine directions
  sharing a `(par dx, par dz)` class are the opposite-diagonal pairs (`K0`/`K1`
  and `K2`/`K3`); the drop is the `(False, False)` class. Same-direction pairs
  are injective (V0-3a). So cross-direction overlap is *exactly* the
  opposite-diagonal class — which the V0-1 pre-phase tie-break resolves
  (rule 3, T23). The proof needs a Bool `xor_cancel_left` (discharged via
  `b_not_not`).
- `test/tests.bend`: **T30** witnesses the direction-parity table (K0/K1 share
  `(True, False)`, K2/K3 share `(False, True)`, the drop is `(False, False)`).
- `LAWS.bend`/`PROOF.bend`: laws `color_of_bit0/1/2`, `color_target_x_par`,
  `color_target_z_par`, `color_collision_x_par`, `color_collision_z_par`.

**Rule reading.** Rule 4 asks for (colour × direction) batches with injective
targets. Within a direction batch the targets are a translation and injective
(V0-3a). Across directions, the classification shows the only possible overlap
is one parity class (the opposite diagonals), and rule 3 explicitly allows a
deterministic pre-phase tie-break for exactly that. `R4` is therefore marked
**conforming** in `PLAN §4.1`.

**Honest residuals.** The claim is stated over the parity bits, so the `is_ne`
reflection the plan mentioned is *not* needed for it; turning
`color_collision_*_par` into a literal `U32.is_eq(below i, diag4 j k) == False`
would need that reflection and is left as polish. The `div`-free classification
does not by itself prove the *equality* `region-split fold = sequential fold`
(V3c); that is the remaining schedule-invariance item, now unblocked by phase
purity (V0-1) + injectivity (V0-3a) + colour separation (V0-3b). `G13`'s
over-forfeit stands: the tie-break is sufficient but does not recompute the
neighbour's chosen target.

**Verification**
- `bend PROOF.bend` → `All terms check.` (69 laws; +7, none retired).
- `bend test/tests.bend` → 26/26 PASS (+T30).
- `bend test/simtests.bend -o bin && ./bin` (rebuilt) → 13/13 PASS.
- `bend_canary` → 6 ok, 0 bad.

### A.67 — proof-library consolidation: hoist V0-3b's generic bit/Bool lemmas

**Status:** cleanup (no engine, law, or test change). Gate green (69 laws, no law
touched), fast 26/26, canaries 6 ok.

**Why.** V0-3b (A.66) needed seven lemmas that are not about colours at all —
they are generic `Word`/`Bool` facts about `bit0`, masks, and `xor`. Leaving
them in `src/color.bend` made that module ~500 lines and buried the colour
argument under plumbing, and any future "bit `k` of a packed word" proof would
have re-derived them. The A.66 session was ~80% `Equal.trans`/`cong`
bookkeeping, so the reusable part is the part worth sharing.

**What changed (move only).**
- `src/parity.bend`: `bit0_or`, `bit0_and`, `bit0_shl` (bit-0 extraction from
  `Word.or`/`and`/`shl`), next to `bit0`.
- `src/bits.bend`: `mask_zero`, `not_eq_inv`, `xor_cancel_left`,
  `shr_and_mask1_zero`, appended after their dependencies.
- `src/color.bend`: the seven defs removed and their call sites qualified
  (`Parity.bit0_*`, `Bits.*`); the two colour-specific constants
  (`bit0_mask1`, `bit0_mask31`) stay. 500+ -> 383 lines.

**Deliberately not done.** No new checker/gate/registry tooling: `bend_audit`
already detects the drift class we hit (it flagged the 59→69 law-count mismatch),
and a `conform`-vs-`gate` split or machine-readable status file would be real
tooling for a small, currently-handled risk. The cheap lever was the shared
lemma library, not process.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (69 laws; unchanged).
- `bend test/tests.bend` -> 26/26 PASS.
- `bend_canary` -> 6 ok, 0 bad.

### A.68 — V3c-1: point writes at distinct leaves commute (the schedule-invariance kernel)

**Status:** proof landing (no engine change). Gate green (**70** laws, +1),
fast suite **27/27** (+T31), sim suite **13/13**, canaries 6 ok. Adds
`src/commit.bend` and law `point_writes_commute`.

**Why — and a correction to the V3c-1 framing.** The session started from A.57's
decomposition ("per-cell transition + forward-activation closure"). That framing
is **obsolete**: both A.57 counterexamples were properties of the retired
`Rules.step`. `V0-1` (A.63) made a phase a pure function of the pre-phase state,
so the evaluated set is fixed (all cells of the colour; wake lands *after* the
phase's writes), and each cell's decision no longer depends on scan order. There
is no intra-phase activation closure left to characterise (V3c-2). What remains
for "a region-split fold equals the sequential fold" is the *composition* step:
the merged write set must *apply* order-independently, i.e. point writes at
distinct targets must commute. That is what V3c-1 lands.

**What it proves.** For the `Refine.PT` presentation of `Array` (whose
`Refine.swap_m` refines `Array.swap.go`/`Array.set`),
`swap_m (swap_m t n i v) n j w = swap_m (swap_m t n j w) n i v` whenever `i` and
`j` name distinct leaves. With `Rules.plan` already reading only the pre-phase
world, this is exactly the algebraic fact a region merge needs: the merge is
order-independent, so a region-split fold has the same value as the sequential
fold *given* the engine's writes are pairwise distinct (V0-3a/V0-3b).

**The distinctness hypothesis (`ne_idx`).** The natural statement needs `i != j`,
but threading `U32.is_eq(i,j) == False` through `swap_m`'s tree recursion would
need new `U32` order/subtraction lemmas (`sub` injectivity on `[h, 2h)`). The
landing instead encodes distinctness as the *shape of the recursion*: `ne_idx t n
i j` walks exactly as `swap_m` does and returns `True` when the two indices split
into different subtrees at some level, `False` at a leaf (where every index
collides). Because the predicate reduces to the child's predicate at each node,
the induction hypothesis applies verbatim and **no `U32` arithmetic is needed**.
For a full tree with in-range indices `ne_idx` is `i != j`; refining that to the
engine's `U32.is_eq ... == False` is the recorded residual.

**Proof engineering (why `set_m_if`).** `Refine.swap_m` recomputes its left/right
decision `U32.is_lt(i, U32.shr(n))` internally, so a composition of two `swap_m`s
is stuck on a `Bool.pick` whose scrutinee is a *term*, never a `match`-able
variable — and matching a local `let` Bool inside a `match t` branch trips Bend's
binder-order rule. `set_m_if` takes that decision as a parameter and mirrors
`swap_m` exactly (proved as `swap_m_eq_set_m`); `set_m_if_pick` then pushes a
write past the `Bool.pick` a previous write leaves behind. With every pick on a
parameter, `match zj`/`match zi` reduces all four cases to IH-left, refl, refl,
IH-right. The unsatisfiable leaf hypothesis `{False == True}` is eliminated by
`Equal.cong` under `Bool.pick` (no-confusion).

**Honest residuals (recorded, not hidden).**
- **V3c-1b** (open): fold the kernel over the engine's `List<Write>` and state
  the region-split equality as one law. The single-write kernel is the
  load-bearing algebraic fact; the fold is list bookkeeping.
- **`ne_idx` ↔ `U32.is_eq`** (open): refine the hypothesis to the engine's
  `i != j`. Needs `U32` order/subtraction arithmetic (`sub` is injective on
  `[h, 2h)`), deliberately not attempted here.
- `G3` stays open; the engine's write-set *distinctness* is V0-3a/V0-3b at the
  parity level, and the `plan` write-site reflection is `G14`.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (70 laws; +1).
- `bend test/tests.bend` -> 27/27 PASS (+T31).
- `bend test/simtests.bend -o bin && ./bin` (rebuilt) -> 13/13 PASS.
- `bend_canary` -> 6 ok, 0 bad.

### A.69 — Plan correction: `C3` is the critical path; the `V3c`→`M7d` coupling is void

**Status:** documentation/governance only (no engine, law, or test change).
Gate green (70 laws, unchanged), fast 27/27, canaries untouched.

**Why.** The `§5.2` ordering and the `V3c`↔`C3` coupling were written before
`V0-1` (A.63). A.59 tied the remaining CPU scale lever ("region-skipping the
scan") to `V3c`/`G3` because `Ops.wake` pulled later cells into the same phase
(T24). `V0-1` removed exactly that: the evaluated set is fixed and wake lands
after the phase, so the read-set bound is `V3a`/`V3b` locality (proven) and the
residual is the per-tick wake cone (`G12`). **`C3`/`V0-4` is therefore
independent of `V3c`** — and `C3` (cost tracks disturbance) is the asymptotic
product claim, while `M7d` is a droppable core-count multiplier.

**What changed (PLAN.md only).**
- `§5.2`: the `V0` item names **`V0-4` (`C3`) as `NEXT`/critical path**; the
  `V3c` item is **off the critical path** (gates only `M7d`); `M7d` is optional
  and droppable; the `M9` "correction" no longer routes the region-skip through
  `V3c`; the **Suggested order** is now
  `V0-4 (C3) → (optional) V3c-1b/M7d → (M7b/M7e on CUDA)`.
- `§5.3` `G3`: the obsolete "per-cell transition + forward activation closure"
  framing is removed and marked obsolete; the row gates only `M7d`.
- `§8`: the schedule-invariance risk is restated as off-critical-path, and a
  `C3`/`V0-4` risk (imperative-engine refinement + the per-tick wake cone) is
  added.

**Not done (deliberately).** No engine work; `V0-4`/`C3` starts next. The stale
notion survives only in `HISTORY.md` (the log), which is where it belongs.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (70 laws; unchanged).
- `bend test/tests.bend` -> 27/27 PASS.
- `bend_canary` -> 6 ok, 0 bad.

### A.70 — Work-item labels: a frontier-first convention (`state · deps · serves`)

**Status:** documentation + tooling only (no engine, law, or test change). Gate
green (70 laws), fast 27/27, canaries 6 ok.

**Why.** Order, independence, and schedulability of open work lived in prose
("gated on", "independent of", "optional", "deferred"), so every session
re-derived the DAG by reading §5.2. And IDs doubled as ordering hints (`V0-4`
"after" `V0-3`), which broke the moment `V3c` was reordered (A.69).

**What changed.**
- `PLAN.md` §5.2 is now **frontier-first**: a legend, then groups by state
  (`Frontier` / `Optional track` / `Blocked` / `Deferred`), then a
  **Dependency view** table (the single source of truth for order), then the
  landed detail. Every open item carries a tag `· <state> · deps: … · serves: …`;
  `serves` names the contract clause / rule the item advances. **IDs are
  unchanged** (history cites them) and the item prose is unchanged.
- `.pi/extensions/bendverse/lib.ts`: `milestoneInfo`/`milestoneDigest` parse the
  tag; `index.ts` uses them so `bend_status`/`bend_plan` render `[next] V0 …`
  instead of the raw tag. `parseMilestones` (the `- [ ]`/`- [x]` scan) and the
  landed/gap/trace table parsers are untouched, so the gate and the rest of the
  digests are unaffected.

**Deliberately not done.** No rename to a single `W*` namespace (it would
invalidate every `HISTORY` reference and the `[MV]` landed-table regex), and no
dependency-graph tooling — a markdown table is enough.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (70 laws; unchanged).
- `bend test/tests.bend` -> 27/27 PASS.
- `bend_canary` -> 6 ok, 0 bad.
- extension: `bun build lib.ts` clean; `milestoneDigest` unit-checked on the five
  open labels.

### A.71 — V0-4a: deferred phase wake (rule 9, `G12` closed)

**Status:** engine semantics + witness. Gate green (70 laws; no law changed, no
proof touched). Touches `src/rules.bend`, `src/sim.bend`, three comment
references, `test/simtests.bend` (T33 added). Closes `G12`; opens `G16` for the
support pass's remaining same-tick wake. `coreidea.md` and `PLAN.md` §4.1/§5.1/
§5.2/§5.3/§8 updated.

**Why.** `C3` (cost tracks disturbance) needs the set of cells a tick evaluates
to be fixed at tick start, otherwise a work set derived from a pre-tick activity
snapshot would silently drop work that a phase's `wake` pulls in later in the
same tick (`G12`; the A.59 correction). `V0-1` had fixed only the *same-phase*
case (T24): a phase does not evaluate a cell it wakes, but the wake *mark* was
committed at the end of that phase, so a later phase of the same tick still saw
it. `V0-4a` defers the mark to tick end.

**What changed.**
- `src/rules.bend`: `phase_pending` now commits only the write set and returns
  the pending `wakes` as `(world, wakes)`; `phase_plan(world, c)` exposes it.
  The old `phase`/`phase_wakes`/`phase_commit` (immediate wake) were removed as
  dead code — the tick is the only caller and it defers.
- `src/sim.bend`: `Sim.phase` is now the tick-composable *writes-only*
  transform (`phase_get(phase_w(world, c))`); `phases`/`phases_commit` run all
  eight colours, accumulate their wake lists (`List.append`, since `<>` is
  cons), and `Rules.commit_wakes` applies them once. `tick_active` is the only
  entry point. The fold threads the phase result as a parameter and matches
  `fuel` before `pair` (Bend matches parameters in binder order).
- `test/simtests.bend`: **T33** — a differential witness. A (colour 0, active)
  drops in phase 0 and wakes B at (5,39,4) (colour 3). With B inactive at tick
  start it does not move this tick but is active afterwards; with B active at
  tick start (control) phase 3 evaluates it and it falls. T24's comment updated:
  `Sim.phase` is the writes-only transform, wake lands at tick end.
- Comment references to the removed `Rules.phase` updated in `LAWS.bend`
  (V3c-1 header), `src/commit.bend`, and `src/step.bend` (no law meaning
  changed — comment text only).

**Why this is safe.** Deferring activation only makes the engine more
conservative: the wake marks themselves are unchanged, so the post-tick active
set is a subset of the old one and every golden/sim test passes. The change only
removes same-tick movement of a cell an earlier phase woke.

**Not done (deliberately).** `Support.sup` case 6 still wakes after a crush
within the support pass, so a cell it wakes *is* evaluated by the same tick's
phases. That is now the only rule-9 residual, recorded as `G16` (not `G12`);
`V0-4b`'s Support rewrite closes it. No proof work: the `sup_m`/`step_m` mirrors
are untouched.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (70 laws; unchanged).
- `bend test/tests.bend` -> 27/27 PASS.
- `bend test/simtests.bend` native -> 14/14 PASS (T33 added; T23/T24/T26–T28
  unaffected).
- `bend_canary` -> 6 ok, 0 bad.

### A.72 — V0-4b-1: one move per tick, and the work-list phase fold

**Status:** engine semantics + structural refactor. Gate green (70 laws; no law
changed — two proof terms updated). Touches `src/rules.bend`, `src/sim.bend`,
`src/writepot.bend`, `src/count.bend`, `test/simtests.bend` (T34/T35). Closes
`G17`; `V0-4b-2` (maintain the work set) is next. `PLAN.md` §4.1/§5.1/§5.2/§5.3
and `coreidea.md` updated.

**Why.** `V0-4b` needs the tick's *evaluated set* to be exact, so that a work
list derived before the phases is complete. Probing the engine turned up a
second in-tick activation path that `V0-4a` had not touched: `Rules.mov` (and the
slide write `WSet{nd, w}`) kept the mover's **active bit**, so after a grain
dropped from a colour-`c` cell into the `dy = -1` neighbour (a different colour)
a *later* phase re-evaluated it and it fell again — **two cells in one tick**.
That is a rule-9 violation (a write's activity should land next tick) and it
makes any pre-phase work list unsound. The impact path already clears active
(`Ops.set_fall0`) and relies on the deferred wake, so drop/slide were simply
inconsistent with it.

**What changed.**
- `src/rules.bend`: `mov` writes active `0` (was `Cell.active(w)`); the slide
  case 32 writes `Cell.deactivate(w)`. The move already emits `WWake{nb}` (and
  the slide `WWake{nd}`), which `V0-4a` applies at tick end, so the mover is
  re-activated next tick. A grain now falls exactly one cell per tick.
- `src/rules.bend`: `plan` is driven by `todo: List<&2, U32>` — the active cells
  of the phase — instead of the colour sub-lattice. `c` was only ever used for
  the advance (`color_last`/`next_color`); the per-cell decisions never read it,
  and V0-1 makes a phase order-independent, so any `todo` order gives the same
  write set. The terminal selector advances to the next `todo` entry or stops.
  `phase_plan_w(world, todo)` is the entry.
- `src/sim.bend`: `active_list` collects the active cells after the support pass,
  `filter_color` selects a phase's colour, and `phases` folds the eight colours
  over the shared list (reused via `+todo`); wakes are still threaded and applied
  once at tick end. `Sim.phase` uses the same path.
- `src/writepot.bend`/`src/count.bend`: `pot_mov`/`nempty_mov` unfold `mov`'s
  material projection; the `mat_encode` argument is now `0` for active (material
  is unchanged, so both laws still hold). No law's statement changed.
- `test/simtests.bend`: **T34** (one move per tick, and the mover is active
  again) and **T35** (the work-list phase acts on its colour only).

**Retirement (A.72).** With the phase fold off the colour sub-lattice, `Grid`'s
M9 helpers (`color_base`/`color_at`/`color_last`/`color_s`/`next_color`) and the
fast-suite witness T25 became dead — the engine no longer scans a colour's
32768-cell sub-lattice. They were removed (not kept as a stale mirror);
`Rules.color_of` stays live (`Sim.filter_color` uses it). The M9 note in PLAN
§5.2 records the retirement.

**Measured (honest).** Native 64³ `build+pull+30 ticks` is **unchanged** (~40 ms
vs the A.59 ~36 ms): the phase sub-lattice scans are gone, but `any_active`,
`Support.pass` and the new `active_list` still scan the whole world, so the
replacement is net-neutral. `C3` is therefore **not** closed by this entry — the
phase half is done and the evaluated set is exact, but cost is not yet
disturbance-proportional. That is `V0-4b-2`.

**Not done (deliberately).** No maintained work list across ticks; no support
work list; `Support.sup` case 6 still wakes within the pass (`G16`); `sup_m` is
untouched (it mirrors `Support.sup`, which `V0-4b-2` will replace).

**Verification**
- `bend PROOF.bend` -> `All terms check.` (70 laws; unchanged).
- `bend test/tests.bend` -> 26/26 PASS (T25 retired with the sublattice).
- `bend test/simtests.bend` native -> 16/16 PASS (T34/T35 added; the goldens
  T1–T9/T18/T20 and T23–T28/T33 still pass, which is the equivalence witness for
  the work-list fold).
- `bend_canary` -> 6 ok, 0 bad.

### A.73 — `coreidea.md`: restore the conceptual register

**Status:** documentation/governance only. Gate green (70 laws), fast 26/26,
sim 16/16, canaries 6 ok. No rule or law changed; `PLAN.md` §4 is unchanged.

**Why.** `coreidea.md` is the contract and the rules — conceptual and
deliberately stable. Its "Where the code stands" paragraph had drifted into a
status log: version tags (`V0-4a`/`V0-4b-1`), implementation identifiers
(`Rules.plan`/`phase_plan_w`, `Sim.active_list`), and gap IDs (`G16`), refreshed
every milestone. That duplicates `PLAN.md` §4 (which is machine-read) and makes
the contract document churn with the code.

**What changed.** The paragraph now states only the *shape* of the gap in model
terms — purity and closure hold; the deviations are all consequences of the
engine still sweeping the world (cost not disturbance-proportional; support
seeded positionally rather than from the neighbourhood; the support pass's
activity effect still landing within its own pass) — and says explicitly that it
changes only when a contract clause or a rule's status changes, not per
milestone. `PLAN.md` §4 is named as the single source of truth for per-rule
conformance.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (70 laws; unchanged).
- `bend test/tests.bend` -> 26/26 PASS; `bend test/simtests.bend` -> 16/16 PASS.

### A.74 — V0-4b-2: deferred support wake (`G16` closed); the support scan builds the work list

**Status:** engine semantics + structure. Gate green (70 laws; no law changed —
`sup_m`'s crush step and its proof updated). Touches `src/support.bend`,
`src/sim.bend`, `src/rules.bend`, `src/tick.bend`, `test/simtests.bend` (T36).
Closes `G16`; `V0-4b-3` (drive/maintain the work set) is next. `PLAN.md`
§4.1/§5.1/§5.2/§5.3/§8 and `coreidea.md` updated.

**Why.** `V0-4a` deferred the *phase* wakes and `V0-4b-1` cleared the mover's
active bit, but the support pass still applied its own wake inline after a crush
(`G16`), so a cell it woke was evaluated by the same tick's phases. That was the
last source of in-tick activation, and it also forced the tick to rebuild its
work list *after* support (a second full scan) to see the woken cells.

**What changed.**
- `src/support.bend`: `sup` conses a crushed cell onto `wakes` instead of calling
  `Ops.wake`, and threads a `todo` list — the active cells it sees at `sel 0`.
  `pass_gated` returns `(world, wakes, todo)`; `pass`/`pass_all` (setup) apply the
  wakes immediately via `wake_all`. Within a tick the pass now only ever *clears*
  active bits, so the pre-tick active set is a superset of everything the phases
  can act on.
- `src/sim.bend`: the tick is `any_active` (cheap settled check) →
  `Support.pass_gated` (which returns the work list) → the eight phases over that
  list → `Rules.commit_wakes` applies the support and phase wakes together.
  Removed the separate `active_list` scan from the tick path (`active_list`
  remains only for the single-phase `Sim.phase` probe).
- `src/rules.bend`: `wake_writes` converts the support pass's `List<U32>` wake
  indices to `WWake` writes so they fold with the phase wakes.
- `src/tick.bend`: `sup_m`'s `S6` and `sup_crush_step` drop the inline wake — the
  mirror now tracks the crush writes only; the deferred wakes are Φ-neutral
  (`wake_z_m_preserves` / law `wake_preserves_pot`). No law statement changed.
- `test/simtests.bend`: **T36** — an active rock with an empty below is crushed,
  and its neighbour stays put this tick (active afterwards).
- `coreidea.md`: rule 9's "effects land next tick" now holds; the status
  paragraph drops the support-pass clause (still conceptual, no identifiers).

**Measured (honest).** Settled tick is **≈ 0.09 ms**, preserved (2000 settled
ticks ≈ 180 ms, matching the A.59 baseline). The active path dropped one full
scan (the separate `active_list` build). A `pull` transient is *longer* than
before — the crumble now propagates one ring per tick (the intended rule-9
physics), not faster within a tick. `C3` is still not closed: the tick sweeps
the world twice (`any_active` + the gated `Support.pass`), which is `V0-4b-3`.

**Not done (deliberately).** No support work list (support still scans); no
maintained list across ticks; the chunk `M8` store is not wired in.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (70 laws; unchanged).
- `bend test/tests.bend` -> 26/26 PASS.
- `bend test/simtests.bend` native -> 17/17 PASS (T36 added; all goldens pass).
- `bend_canary` -> 6 ok, 0 bad.

### A.75 — V0-4b-3a: the support pass runs over the work list

**Status:** engine structure. Gate green (70 laws; unchanged). Touches
`src/support.bend`, `src/sim.bend`. `V0-4b-3b` (maintain the work set) is next.
`PLAN.md` §4.1/§5.1/§5.2 updated.

**Why.** After A.74 the tick was `any_active` + a gated `Support.pass` (which
scanned the world and built the phase list) + phases over the list. The support
scan did selector work on all 262144 cells to act on a handful; driving it from
the work list removes that.

**What changed.**
- `src/support.bend`: `sup` gained a `scan` mode — `True` advances `i+1` to
  `volume` (the setup `pass_all`), `False` pops the next work-list entry and
  stops when it is empty. `pass_todo(world, todo)` is the tick's entry. The
  per-cell writes are identical, so `sup_m`'s Φ claim is unaffected by the
  advance (the mode is Φ-neutral).
- `src/sim.bend`: `active_list` now scans *downward* and conses, so the list is
  ascending — the bottom-up order the support pass needs for its `below`
  propagation. `tick` is `any_active` → `active_list` → `Support.pass_todo` →
  phases over the list → commit wakes.

**Measured.** `build+pull+300 ticks` ≈ 128 ms (was ≈ 151 ms in A.74, ≈ 145 ms
in A.72): the active transient is ≈ 15 % faster. Settled tick is unchanged
(≈ 0.09 ms) — the settled path is still the single `any_active` scan, which
`V0-4b-3b` removes.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (70 laws; unchanged).
- `bend test/tests.bend` -> 26/26 PASS.
- `bend test/simtests.bend` native -> 17/17 PASS.
- `bend_canary` -> 6 ok, 0 bad.

### A.76 — `V0-4b-3b` scoping: two maintained-work-set designs, two toolchain blockers

> **Superseded by A.80** — the `List.sort` / `Array.to_list` blockers below are fixed in Bend 2.0.17.

**Status:** documentation/scoping only (the two code attempts were reverted; the
tree is at A.75). Gate green (70 laws), fast 26/26, sim 17/17, canaries 6 ok.
`PLAN.md` §5.2/§8 updated. No engine, law, or test change.

**Why.** `V0-4b-3b` is the last step to `C3`: stop scanning the world for the
settled check (`any_active`) and the work-list build (`active_list`) by carrying
the work set across ticks. The next active set is exactly the cells the deferred
wakes marked, so the tick must collect those marks and return them.

**Design (a) — carry the active-cell list.** The tick returns the marked
neighbours (a `List<&2, U32>`); the next tick folds it. Duplicates are safe (a
phase is a pure pre-phase fold, so re-processing a cell produces idempotent
writes), but the **support** pass reads `below(i)` and needs the list in
ascending index order for its bottom-up propagation, so the list must be sorted.
**Blocker:** `List.sort` does not compile in this Base — its own definition
references an undefined `List.sort.go` — and an O(n²) insertion sort is
unacceptable at `n = 2^18`. A hand-written merge sort is possible but needs a
split/merge pair whose mutual recursion Bend's no-forward-reference rule makes
awkward; not landed.

**Design (b) — carry a dirty-chunk mask.** Two `U32`s (64 chunks of 16³ cells).
A wake marks the 26 neighbours' chunks; the next tick scans only dirty chunks
(4096 cells each, ascending) to build the work list, so no sort and no dedup.
The chunk scan, `is_dirty`, `chunk_of` and the mask-setting wake were written and
each compiled and ran in isolation (scanning all 64 chunks is fine).
**Blocker:** the full tick stack-overflowed in the checker ("a deep recursion, or
a literal too large to expand") when the work list was passed *symbolically*
through the support/phase fold (`tick_sup`); the same call with a literal empty
list compiled. The mask threading through `Ops.wake`/`Rules.commit_mark` was not
the trigger (each worked alone). This is a toolchain/plumbing issue, not a
semantics one.

**Concrete next step.** Land (b) but thread the mask only through the *commit*
(where wakes are applied), keeping the support/phase entry points monomorphic
(no symbolic work list across the fold), or diagnose the symbolic-list overflow.
Both designs are recorded here so the next session does not re-derive them.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (70 laws; unchanged).
- `bend test/tests.bend` -> 26/26 PASS; `bend test/simtests.bend` -> 17/17 PASS.
- `bend_canary` -> 6 ok, 0 bad.

### A.77 — `V0-4b-3b`: the dirty-row mask carries the work set (`C3` closed)

**Status:** engine + docs. The tick no longer scans the world: it carries a
64-bit dirty-row mask (`src/dirty.bend`) and builds the active-cell work list by
scanning only the rows a wake can reach. `src/dirty.bend` added; `src/sim.bend`
tick pipeline replaced; dead `Rules.commit_wakes` removed and the one-line
`Support.cons_if` list helper inlined (so `dirty.bend` no longer depends on
`support.bend`); `src/ops.bend` seed note re-pointed, `PROOF.bend` now covers the
new module; T37 added. Gate green (70 laws), fast 26/26, sim 18/18, canaries
6 ok.

**Why.** `C3` was the last contract deviation: every tick paid two world scans
(`any_active` + `active_list`). The next active set is exactly the cells the
deferred wakes marked, so the set can be *carried* instead of recomputed.

**Design — the dirty-row mask.** Two `U32`s, one bit per `y` row. A wake marks
the three rows it can reach (`y-1`, `y`, `y+1`, mod 64 — the same wrap
`Grid.neighbor` uses); `active_mask` primes the mask from the world (one scan);
`dirty_todo` walks rows descending and, within a dirty row, cells descending,
consing, which reproduces `active_list`'s exact global ascending order.

**Two A.76 blockers, resolved.**
1. **Checker overflow.** A recursive 27-neighbour `block_mask`, inlined once per
   wake inside the symbolic wake fold, overflowed the checker's stack even after
   the work list was bound to a local. The row reach is instead *arithmetic* —
   three `or_y`s, with no recursion inlined per wake.
2. **Chunk granularity is wrong, not just fiddly.** A 16³ chunk mask compiles
   with the arithmetic marking, but its chunk-major scan order interleaves `y`
   (all 16 rows of one chunk before the next chunk), which lags the support
   pass's bottom-up `below` propagation and diverges from `active_list` after a
   few ticks. Row granularity is the coarsest unit whose scan order is exactly
   global ascending.
The mask is threaded only through the *commit* (`commit_wakes_mask` applies each
`Ops.wake` and marks its rows); `Support.pass_todo`/`Sim.phases` stay
monomorphic, so no symbolic work list crosses a pair-returning fold.

**Measurement (native, 64³).** Settled: 20000 ticks 1.79 s → 0.027 s (~66×,
~89 µs → ~1.3 µs per tick). Mixed 1000-tick `spawn` 0.113 s → 0.032 s. The active
work set is unchanged, so an active tick trades the two world scans for the mask
walk (comparable at 64³; the win is that cost no longer scales with the world).

**Verification**
- `bend PROOF.bend` -> `All terms check.` (70 laws; unchanged).
- `bend test/tests.bend` -> 26/26 PASS; `bend test/simtests.bend` -> 18/18 PASS.
- `bend_canary` -> 6 ok, 0 bad.
- Equivalence: the mask tick is bit-identical to the pre-mask tick on
  `build`/`spawn`/`pull` for 1–30 ticks (hash probes), and T37 witnesses the
  carried work set across a row boundary.

### A.78 — `V3d`: the material-preserving write family becomes one law, and Φ gets a runtime oracle

> **Annotation (A.79):** the selector types named below moved from `selector.bend`
> (`Selector.WrSel`/`apply_w`) into the engine as `Rules.PresOp`/`Rules.apply_pres`
> when the write effect was pushed into `Rules.Write`. Same family, same statements;
> only the type's home and name changed. `G14` was subsequently closed by A.79.

**Status:** verification + tests. Prompted by an outside review of whether the
refinement ladder is actually tractable. Two things came out of it.

**1. The per-write mirror was avoidable.** Every material-preserving write
(`set_support`, `set_fall0`, `mov`, `activate`, `deactivate`) has the same Φ and
count obligation, but the potential layer said it four times over: `Tick.chg_support`,
`chg_fall`, `chg_activate`, `chg_deactivate`, each a full recursive walk of the
`PT` tree, each with its own `chg_X_if` distribution lemma and its own
`array_X_write`. The count layer already had the factored form
(`Count.array_point_write_preserves_count` + five one-line instances); Φ did not.

The reason it could not be factored with an ordinary function parameter is a
language fact, not a modelling one: **Bend closures are affine, so a parameter
`f : U32 -> U32` may be called at most once** (probe: `f(f(x))` is rejected with
"consumed more than once"), and a write function must be applied at *every* leaf.
It has to be `Data`. So the write choice is a `Data`-kinded selector
(`Selector.WrSel`), `apply_w` is a top-level def, and the traversal is written
once. This is the device `SupSel`/`StepSel` already use, generalised.

`src/selector.bend` added: `WrSel`, `apply_w`, `mat_pres` (the whole per-site
obligation — material is untouched), `pot_pres`/`nempty_pres` (material
preservation at *any* index is exactly what `pot_at`/`nempty` need), generic
`chg_wr`/`cnt_wr` walks, and the two array-level theorems. Laws added (75 total):
`write_selector_preserves_phi`, `write_selector_preserves_count`,
`array_fall_write_preserves_phi`, `array_mov_write_preserves_phi`,
`array_deactivate_write_preserves_phi`.

**Coverage, not just size.** `set_fall0` and `deactivate` are emitted by the live
`Rules.plan` on every tick (sel 22/23 and 4) and had **no array-level Φ law at
all** — the only thing that accounted for them was `step_m`, which mirrors the
retired `Rules.step` (A.63). The selector family covers them unconditionally, so
`G14` now owes only that `plan` emits no other kind of write. `step_mirror_balance`
is marked RETIRED in `LAWS.bend` (it was documented as retired in PLAN §3.4/§4.1
but still read as live evidence in the law list), and the `R2` conformance row no
longer cites the closed `G10` as write-site coverage while `G14` is open.

**2. There was no executable Φ.** `Settle.array_phi` is a proof-side definition
and `Settle.suml` is not tail-recursive, so it overflows the stack on a
2^18-cell world — which is *why* the flagship property had never been checked
end to end. `test/simtests.bend` now carries a tail-recursive oracle
(`phi_acc`/`phi_run`, reading `Grid.to_list` in ascending flat-index order, the
order `Settle.to_pots` walks). T39 pins it to the model by comparing against
`Settle.pot_at` at the packed index for three heights (so a wrong list order, a
wrong counter start, or a wrong `iy` decode all fail); T38 runs it: **Φ is
non-increasing across 60 real engine ticks and strictly decreases over the span**
(non-vacuity).

Two language traps found while landing the oracle, both worth knowing:
large `Nat` literals are expanded unary and blow the compiler (`Nat.is_eq(6300n,
6300n)` overflows; the same value built at runtime is fine), and `match` cannot
scrutinize a local binder or a computed value, so pair-returning folds must be
unpacked through a parameter. T39 therefore derives its expectation from the
model rather than from a literal.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (75 laws).
- `bend test/tests.bend` -> 26/26 PASS; `bend test/simtests.bend` -> 20/20 PASS.
- `bend_canary` -> 6 ok, 0 bad.
- Φ oracle validated three ways (y=1, y=5, y=63 against `Settle.pot_at`).

### A.79 — `V3d-2`: write effects are typed (`G14` closed)

**Status:** engine + verification. The A.78 review ended on a claim worth testing:
that the remaining cost of this project is not the maths but a single untyped
field. It was. `Rules.Write` was

```
type Write is Data:
  WSet{idx: U32, val: U32}
  WWake{idx: U32}
```

and every `WSet` value `plan` emits is `f(source_word)` for a *closed* set of `f`
(`Cell.deactivate`, `mov`, the displaced target, `set_fall0`, `crush_if_rock`).
The classification was already in the code's shape; `val: U32` threw it away. That
is the whole content of `G14`, and it is why each write site needed its own mirror
to re-derive what the type no longer said.

**The fix.** The effect is now a value:

```
type PresOp is Data:      # material-preserving
  OId{} OSupport{s: U32} OFall0{} OMov{} OAct{} ODeact{}
type Op is Data:
  OPres{op: PresOp} OCrushIfRock{}
type Write is Data:
  WSet{idx: U32, op: Op, src: U32}
  WWake{idx: U32}
```

`apply_op` is total, so **`plan` cannot emit an unclassified write** — the write
set is closed by construction, not by inspection. The split into `PresOp` and the
material-changing crush is what lets the preserving laws be total over their own
type: material preservation *is* the hypothesis `mat_pres` discharges.

**The laws.** `write_effect_phi_balance` and `write_effect_count_balance` are
**total over `Rules.Op`** and need no case split, because the exact point-write
balance is already general in the written value (`Refine.array_swap_decreases`,
`Count.array_point_write_count_balance`) — a `WSet` is *some* value written at a
known index. The *decrease* is the refinement on top and splits by effect **shape**,
not by site:

| shape | law |
|---|---|
| material-preserving self-write | `write_selector_preserves_phi` (Φ unchanged) |
| guarded crush self-write | `array_guarded_crush_lowers_phi` (Φ down by a gap) |
| two-cell movement | `Fall.array_mov_cross` / `array_mov_lowers_phi` (fall regime) |

The last row is why the shapes are not all the same, and it is the honest limit of
this change: **movement is not a point write.** Its two halves (`WSet{nb, OMov{}, w}`
+ `WSet{i, OId{}, gv}`, and the slide's `ODeact` variant) must be *paired*, and its
decrease needs the fall regime. That pairing is the `G3`/`G11` composition residual
(V3c-1b), not an enumeration gap, and it is now recorded there rather than here.
`G14`'s second residual — that the carried `src` word is the pre-phase word — is
`R1`/`C1`'s existing by-construction claim.

**Why the values stay precomputed.** `commit_sets` is `world[idx] <- apply_op(src, op)`;
the values are still computed in `plan`, not re-read at commit. That is forced, not
lazy: a move writes `nb` reading `i` and writes `i` reading `nb`, so a sequential
commit that re-read the array would read the *already-updated* `nb` and be wrong.
Reading from a snapshot would cost O(volume) per tick and kill `C3`. So the effect
is typed **and** the value is precomputed — which is exactly why the effect could
not be recovered from the value alone.

**Engine change, and it is small.** `src/rules.bend` (the two effect types,
`apply_pres`/`apply_op`, the `Write` type, six `plan` emission sites, `commit_sets`)
plus one pattern in `src/sim.bend`. Behaviour-preserving: the fast suite (26/26) and
the sim suite (20/20, including T38's 60-tick Φ monotonicity and T39's oracle check)
are unchanged.

**Prognosis, stated so it can be falsified.** Every future write site now costs one
`Op` constructor plus one `mat_pres` case (~10 lines) *if* it is a point write. If a
new optimisation needs a different traversal shape, the mirror cost returns in full.
That is the tripwire: five milestones each costing a constructor means the
architecture is right; one costing a mirror means it is not.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (77 laws).
- `bend test/tests.bend` -> 26/26 PASS; `bend test/simtests.bend` -> 20/20 PASS.
- `bend_canary` -> 6 ok, 0 bad.

### A.80 — toolchain: Bend 2.0.5 → 2.0.17 (operator annotations, index-sugar workaround)

**Status:** toolchain upgrade + docs. `~/.bend` moved to Bend 2.0.17 (the 2.0.5
self-updating launcher refuses the new tarball layout, so the announced installer
`curl -fsSL https://bend-lang.com/install.sh | sh` was used; the pre-upgrade tree
is backed up at `~/.bend.bak-2.0.5-20260919`). Two compiled breaking changes were
adapted and one 2.0.17 compiler bug worked around; two former toolchain blockers
are confirmed fixed. No engine, law, or test *meaning* changed — the engine edits
are operator annotations and an explicit-sugar rewrite. Gate green (77 laws),
fast 26/26, sim 20/20 (rebuilt), canaries 6 ok.

**Breaking change 1 — bare operators demand annotation.** In 2.0.5 a bare
`a + b` (and `- * / %`, and the `< <= > >=` family) defaulted to `Nat`; 2.0.16
made that an error ("a type for this operator… Until 2.0.16 a bare operator meant
Nat. That was a bug"). The bundled guide still documents the old default, so it is
stale. Adapted by writing the named form in propositions and proofs — `Nat.add` /
`Nat.mul` / `Nat.sub` — already the dominant style in `src/` and free of nested
`(… : Nat)` parens. Touched: `LAWS.bend` (5 laws), `PROOF.bend` (2),
`src/nat.bend` (17), `src/potential.bend` (3), `src/settle.bend` (2),
`src/writepot.bend` (6), `test/tests.bend` (1). Law statements are unchanged in
meaning (annotation only), consistent with the `LAWS.bend` append-only rule.
`&&`, `++`, and the `U32` operators are unaffected.

**Breaking change 2 / compiler bug — `../`-relative index sugar.** The
`a[i] <- v` and `a[i]` sugar routes the index through
`parse_term_ns(p, ix, Ref("U32"))`, which treats *any* index head whose resolved
name starts with `.` as an operator-namespace reference and prepends the element
type. A `../`-relative import leaves the leading dot in the def's name, so
`import ../src/grid.bend` + `w[Grid.index(…)]` became the nonexistent
`U32../src/grid.index` ("expected : a defined name"); a `./src/...` import is
unaffected. The only affected file was `test/simtests.bend` (the only
`../`-importing file that indexes with `Grid.index`). Adapted by calling
`Array.set(U32, w, i, v)` explicitly — the fallback the 2.0.17 guide itself gives
— for the 34 sites: 29 rebinding, and 5 function-final statement writes, which now
return the written array instead of rebinding. Reads were unaffected (they use
`Grid.value_at`).

**Former blockers now clear.** `Array.to_list` inlines and checks (2.0.5 reported
`expected a defined name, observed Array.to_list.go`), and `List.sort` compiles and
sorts correctly (2.0.5 referenced an undefined `List.sort.go`). That removes both
A.76 toolchain blockers. `--checkup` still exists and the no-hex-literal rule still
holds, so those §0 facts are unchanged. The `Array.to_list` / `Grid.to_list_go`
workaround is now unneeded but was left in place (behaviour-identical); retiring it
is optional.

**Docs.** `PLAN.md` §0 retitled to Bend 2.0.17 with a new "2.0.17 breaking changes
and toolchain bugs" block; `src/list.bend`'s version note bumped; A.76 got a
superseded-by pointer for its blocker claim.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (77 laws).
- `bend test/tests.bend` -> 26/26 PASS; `bend test/simtests.bend` native -> 20/20 PASS.
- `bend_canary` -> 6 ok, 0 bad.

### A.81 — V0-5: the support seed is a neighbourhood read (`R6`/`R7` closed)

**Status:** engine semantics change (support seed) + mirror update + test + docs.
`V0`'s last sub-step, and the last row of the §4.1 conformance table to leave
*deviating*. Gate green (77 laws, unchanged — no law's meaning moved), fast 26/26,
sim 21/21 (rebuilt, +T40), canaries 6 ok.

**What was wrong.** Rules 6/7 say cohesion rigidity is a *local* property derived
from the pre-phase neighbourhood, and support is derived, never carried. The
support pass seeded grounding with `Ops.shell_adjacent(i)`, which returned
`x/z/y ∈ {1,62}` — the layer next to the bedrock shell — and never read an
adjacent cell. So a cell was grounded by *position*, and `R6`/`R7` were recorded
as deviating (A.62). `V0-2` had closed the box at the grid level and `V0-4b` had
closed `C3`, but neither touched the seed.

**The change.** The seed is now read from the world:
- `src/ops.bend`: `Ops.shell_adjacent` is gone. `face` maps a direction code
  0..5 to the neighbour index, `seed_go` folds reads of the faces (threading the
  linear `Array`), and `side_sel` is the wall-adhesion half over the five
  non-below faces (selector 4 = grounded, 6 = crush).
- `src/support.bend`: `Support.sup` case 1 reads `below` first (the support
  contact — and the common propagation path), and case 2 decides on it: below
  static → set support 31 (case 4); below cohesive *and* supported → inherit
  (case 3); otherwise the wall faces are probed (`side_sel`, cases 30/31). An
  eager six-face read was tried first and cost ~50 % on the build scenario; the
  lazy order means the common terrain path (below already supported) pays no
  extra reads, and the residual regression is ~24 % on build+pull+14 ticks.
  Settled ticks are unchanged (no active cells → no support work).
- `src/tick.bend`: the `sup_m` mirror moves with it — `tstatic_side` is the `PT`
  form of the wall read, and `S1`/`S2` route to the new decision. `sup_m` stays
  live (it mirrors the current `Support.sup`), unlike the retired `step_m`;
  `sup_mirror_preserves_phi` is unchanged in meaning and still checks.
- No coordinate is baked in, so interior bedrock now grounds too: a rock resting
  on an interior bedrock block stays rock with support 31, and a rock against an
  interior wall with empty below is held by wall adhesion.

**Witness (`T40`).** Three clauses, all against a hand-built world (no worldgen
shell): (a) a rock on interior bedrock → rock + support 31; (b) a rock against an
interior bedrock wall, empty below → rock + support 31; (c) an isolated active
rock (no static neighbour, empty below) → rubble. Under the retired coordinate
seed (a) and (b) would crush — `(32,39,32)`/`(31,40,32)` are not shell-adjacent —
so the witness is a real differential. Sim suite 21/21.

**Docs.** PLAN §4.1 `R6`/`R7` → **conforming**; the `V0` frontier block moved to
§5.2 "Landed (detail)" with the `V0-5` note; §5.1 gains the `V0` row; the
dependency view drops the `V0-5` row and the order note records the empty
frontier. §5.3 gaps are untouched: `G6` ("support test-witnessed only") still
stands, because no support-*recompute* law was added — this changes engine
behaviour, not the proof burden.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (77 laws).
- `bend test/tests.bend` -> 26/26 PASS; `bend test/simtests.bend` native -> 21/21 PASS.
- `bend_canary` -> 6 ok, 0 bad.

### A.82 — parallel tracks: worktree workers under one supervisor

**Status:** workflow/tooling only; no engine, law, or test change. Gate green
(77 laws). Adds the protocol that lets several independent tracks run at once
without ever putting a second writer in the working tree.

**Why.** Wall-clock is the scarce resource (tokens are not). PLAN's frontier is
empty, so parallel work means deliberately opening tracks; the failure mode is
two writers in one tree — A.80 and the in-flight V0-5 overlapped in this repo and
were harmless only by luck (disjoint files). The human should not have to spawn a
session by hand or ask for each merge/rebase.

**What.** `AGENTS.md` gains a "Parallel tracks" section: one **supervisor**
session owns `master`, integration, and the narrative files (`HISTORY.md`,
`PLAN.md` §4/§5); each track is one **worker** in its own git worktree + branch,
dispatched non-interactively. `tools/parallel.sh` (`new`/`dispatch`/`list`/`rm`)
creates the worktree and runs `pi -p --approve` with `tools/worker-prompt.md` as
the worker role, tee'ing output to `../Bendverse-<track>.log`.
`tools/worker-prompt.md` encodes the worker's scope, ID reservation, and reduced
verification budget. The human's prompt layer is unchanged — ask for the tracks
in plain language; the supervisor dispatches and integrates.

**Why worktrees.** They isolate the per-cwd scratch files
(`.bendverse-spike.bend`, `.bendverse-goal.bend`) and the native cache
(`$TMPDIR/bendverse/<basename>-simtests`), and keep the two writers off each
other's files. Only the append-only `LAWS.bend`/`PROOF.bend`/`test/tests.bend`
are shared; ID reservation keeps those merges trivial. CPU: 6 cores and `bend`
uses all of them, so workers run the gate + fast suite and only the supervisor
runs the native sim suite, once, at integration.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (77 laws).
- `tools/parallel.sh list` -> one worktree (master).

### A.83 — `G5` (read half): the support mirror's reads are the engine's array reads

**Status:** verification only; no engine, law-meaning, or test change. New
`src/g5.bend` + four laws. Gate green, fast 26/26, sim 21/21 (native, integration
run). `PLAN.md` §5.1/§5.3 updated.

**Why.** `G5` is the standing caveat that the laws constrain the `PT`/`Word`/`Nat`
models, not the imperative `Array` engine. `G10`/`G14` had closed the *write-site*
enumeration (the last by typing the effect in `Rules.Write`, A.79), leaving the
*read/selector threading* from `Rules.plan`/`Support.sup` to their `PT` mirrors as
inspection. This lands the read half for the live support selector machine.

**What.** `src/g5.bend` proves `Array.get.go(U32, pack t, n, i) == (pack t,
Tick.tget t n i)` — the same `n/2`/`is_lt` walk as `Refine.swap_ref`, G1's write
bridge — plus the `Array.get` size wrapper (`g5_size_pack`), the composed read
(`g5_read_get`), and read-after-write at the selector's index (`g5_tget_swap`).
Together these cover every read the live `sup_m` performs — S5's `below` read,
S3/S4/S6's self read and read-back, S11's advance read — at the same index as the
engine's `Array.get(world, i)`. `step_m` (retired, A.63) is referenced only as
retired. Laws: `g5_read_get_go`, `g5_size_pack`, `g5_read_get`, `g5_tget_swap`.

**Residuals (recorded in §5.3).** (i) The bare-index form needs the `U32` mask
identity `i < 2^k → U32.and(i, U32.sub(2^k, 1)) == i` plus `g5_twidth(t) = 2^depth`;
no current Base/project lemma covers `U32.and`/`U32.is_lt` bit arithmetic. (ii) The
`SupSel` → numeric `sel` branch table is a hand transcription of `Support.sup`;
since `sup_m` *is* the mirror it cannot be discharged against itself — a
methodological residual.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (branch and merged master).
- `bend test/tests.bend` -> 26/26 PASS; `bend test/simtests.bend` native -> 21/21 PASS.

### A.84 — `V3c-1b` + `V3c-2` (soundness): the schedule-invariance fold

**Status:** verification only; no engine or law-meaning change. `src/commit.bend`
extended; three laws; T32/T33. Gate green, fast 28/28, sim 21/21, canaries 6 ok.
`PLAN.md` §4.1 (R10), §5.1/§5.2/§5.3 updated.

**Why.** `V3c` is the composition half of rule 10: `V0-1` made each phase a pure
function of the pre-phase state, so a cell's decision is scan-order-independent;
what remained is that *applying* the merged write set is order-independent. `V3c-1`
(A.68) proved the single-write kernel (`point_writes_commute`); this lands the
list/region layer and the soundness half of the `ne_idx`↔`U32.is_eq` refinement.

**What.** `Commit.v3c_fold` applies a `List` of point writes through
`Refine.swap_m`. `v3c_write_past_fold` lifts the kernel past a whole fold (a write
at a leaf no list write touches commutes), and `v3c_fold_commutes` is the
region-split equality — `fold(xs++ys) == fold(ys++xs)` for pairwise-distinct writes
— by induction with `swap_m_comm` per step. `v3c_ne_idx_sound` proves
`U32.is_eq(i, j) == True` forces `ne_idx == False`, so any proven `ne_idx` implies
the engine's distinctness (the soundness direction; no range/fullness hypothesis
needed). T32 witnesses the fold/region equality and `pair_ne`/`all_ne` sharpness;
T33 witnesses the soundness law.

**Residual (recorded in §5.3, `G3`).** V3c-2 *completeness*: for a full `Refine.PT`
and in-range `i, j`, `ne_idx(t, n, i, j) == (U32.is_eq(i, j) == False)`. Closes with
a canonical `full(k)`/`pow(k)` plus `U32` lemmas (`shr(pow(k+1)) = pow(k)`, the
`is_lt` top-bit split, subtraction clearing the top bit, `is_eq` decomposition) and
shape-invariance of `ne_idx` across equal-shape trees. Also outstanding: the fold is
stated over the abstract `Commit.V3cWrite` list, not the engine's `Rules.Write`
output — part of the broader `G5` threading.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (branch and merged master).
- `bend test/tests.bend` -> 28/28 PASS; `bend test/simtests.bend` native -> 21/21 PASS.
- `bend_canary` -> 6 ok, 0 bad.

### A.85 — parallel dispatch: Herdr backend (watchable workers)

**Status:** workflow/tooling only; no engine/law/test change. Gate green (84 laws).
Extends A.82. **The Herdr path is unverified from outside Herdr** — it only
activates when `HERDR_ENV=1`; the headless `pi -p` path is unchanged and was
smoke-tested.

**Why.** A.82's workers ran headless `pi -p`, which emits only the final report, so
the human could watch nothing until a worker finished. Herdr (already installed)
runs each worker as an interactive `pi` in a pane with lifecycle states.

**What.** `tools/parallel.sh dispatch` picks a backend. With `HERDR_ENV=1` it
splits the caller pane (`herdr pane split --current --cwd <worktree> --env
BENDVERSE_TRACK=<track>`), starts `herdr agent start <track> --kind pi --pane <id>
-- --approve --append-system-prompt tools/worker-prompt.md`, submits the task with
`herdr agent prompt --wait`, captures the pane to `../Bendverse-<track>.log`, and
closes the pane (unless `BENDVERSE_KEEP_PANES=1`). Outside Herdr it is the previous
`pi -p` path. `tools/worker-prompt.md` now also has workers write
`../Bendverse-<track>.report.md`; `AGENTS.md` documents the backend and the
`BENDVERSE_SPLIT=down` knob for a second concurrent worker.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (84 laws).
- `bash -n tools/parallel.sh`; `tools/parallel.sh list`; missing-worktree error path.
- Herdr path: syntax/help-checked against `herdr agent start|prompt|wait|read` and
  `herdr pane split` (pi is a supported kind); **not executed** — it requires the
  supervisor to run inside Herdr.

### A.86 — `G5` mask residual closed: the bare-index read

**Status:** verification only; no engine or law-meaning change. `src/g5.bend` +352,
three laws, T37–T39. Gate green, fast 31/31 (branch), canaries 6 ok; sim 21/21 at
integration. `PLAN.md` §5.1/§5.3 updated.

**Why.** A.83 closed the read half of `G5` modulo a recorded residual: `g5_read_get`
states the engine read with the masked index `i & (g5_twidth t - 1)`, and no Base
or project lemma covered `U32.and`/`U32.is_lt` bit arithmetic. This closes it.

**What.** `src/g5.bend` gains a self-contained `Word`-level bit-arithmetic
development (all `g5_`-prefixed): `g5_mpow n d = 2^d` peeling `n`/`d` together so the
tail of `g5_mpow (1+p) (1+q)` is definitionally `g5_mpow p q`;
`g5_pow_shl`/`g5_shl_eq_put`/`g5_shlput_*` linking `Word.shl`/`U32.shl` to it;
`g5_sub_pow2`/`g5_add_pow_ones`/`g5_mask_inc`/`g5_sub_one_ones`/`g5_adc_zero_ones`
bridging `2^d - 1` to `Bits.mask`; and `g5_wand_mask_lt` (the mask identity) with the
`Cmp` helpers `g5_cmp_zero_not_lt`/`g5_lt_one`/`g5_lt_cons_false`/`g5_cmp_fin_not_lt`/
`g5_absurd` discharging the impossible branches. Laws: `g5_twidth_pow`
(`g5_twidth t == 2^g5_depth t`), `g5_and_mask_id` (`i < g5_twidth t` ⇒
`U32.and(i, U32.sub(g5_twidth t, 1)) == i`), and `g5_read_get_bare` (the bare-index
read, chaining `g5_read_get` with the mask identity). T37–T39 witness them.

**Residual / observation.** The only remaining `G5` caveat is the `SupSel`
branch-table transcription (methodological — `sup_m` is the mirror, so it cannot be
proved against itself). Non-gating: `Refine.pack`/`Array.size`/`Array.get`
fail-stop at runtime on non-perfect packed trees (hence T39 uses a balanced tree);
the engine only packs full power-of-two worlds, so the laws are unaffected.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (branch and merged master).
- `bend test/tests.bend` -> 33/33 PASS on merged master; `bend test/simtests.bend` native -> 21/21 PASS.
- `bend_canary` -> 6 ok, 0 bad.

### A.87 — `V3c-2` completeness (structural half) + the `add ∘ sub` roundtrip

**Status:** verification only; no engine or law-meaning change. `src/commit.bend`
+217, three laws, T34/T35. Gate green, fast 33/33 (merged), sim 21/21. `PLAN.md`
§4.1 (R10), §5.1/§5.2/§5.3 updated.

**Why.** `V3c-2` (the `ne_idx`↔`U32.is_eq` refinement) had its soundness half (A.84);
completeness — for a full `2^k`-leaf tree and in-range `i, j`,
`ne_idx(t, n, i, j) == (U32.is_eq(i, j) == False)` — remained. This lands its
structural skeleton and one of the two arithmetic residuals.

**What.** `src/commit.bend` gains `v3c_two(k) = U32.shln(1, k)` and the canonical
`v3c_full(k)`; `v3c_is_eq_refl` (`U32.is_eq(a, a) == True`, via `Word.cmp`
reflexivity `v3c_w_cmp_refl`), `v3c_shr_shl` (via `Bits.shr_shl_one`), `v3c_sub_zero`;
the three node-recursion cases as laws — `v3c_ne_idx_sep` (opposite children ⇒
`True`), `v3c_ne_idx_same_l`/`_same_r` (both-left/both-right reduce to the child's
`ne_idx`), discharged by congruence helpers `v3c_pick_lr`/`_ll`/`_rr`; and
`v3c_add_sub`: `Word.add(n, Word.sub(n, a, b), b) == a` unconditionally (per-bit
two's-complement identity through `Word.adc`, so no borrow/no-overflow reasoning is
needed). T34/T35 witness exactness of `ne_idx == Bool.not(U32.is_eq(i, j))` on the
canonical 8- and 16-leaf trees.

**Residual (recorded in §5.3, `G3`).** Completeness is now purely arithmetic:
(i) `is_lt` base reflection `i < 1 ⇒ i == 0` (needs `Word.cmp == LT` reflection;
`w_cmp_eq` only reflects `EQ` today); (ii) range preservation under the right shift
(`is_lt(i, two(k+1))` ∧ ¬`is_lt(i, two(k))` ⇒ `is_lt(sub(i, two(k)), two(k))`);
(iii) `shr(two(k+1)) == two(k)` (bounded `k < 31`). With those, the main induction
follows from the three landed case laws. Also outstanding: wiring the engine's
`Rules.Write` list into `Commit.v3c_fold` (the broader `G5` threading).

**Verification**
- `bend PROOF.bend` -> `All terms check.` (branch and merged master).
- `bend test/tests.bend` -> 33/33 PASS; `bend test/simtests.bend` native -> 21/21 PASS.

### A.88 — `G15` closed: wake is bounded by the grid

**Status:** engine + verification. `src/ops.bend`, `src/tick.bend`, `src/dirty.bend`
(comment), one law, T43–T45 + sim T44–T46. Gate green, fast 40/40 (merged), sim
24/24. `PLAN.md` §4.1 (C2)/§5.1/§5.3 updated.

**Why.** `Ops.wake` marked the wrapped neighbours of a boundary cell (the opposite
face) when the shell is painted away. No material moved (`C2` held), but activity
leaked across the box — rule 9's reach did not respect the closed grid.

**What.** `src/ops.bend`: `wake_x` computes `ok = Grid.step_inside(i, ox, oy, oz)`
and writes through `mark_if ok`, so a rejected step returns the world untouched —
V0-2's rule-target guard applied to the wake reach. `src/tick.bend`: the `PT` wake
mirror gains `wake_write_m(ok, t, n, j)` (identity on `False`, `Cell.activate` swap
on `True`) and `wake_write_m_preserves`; `wake_x_m` carries the same guard and
`wake_x_m_preserves` composes the helper. Keeping the guard a *parameter* is what
lets the proof go through with no `Grid.step_inside` reflection. `src/dirty.bend`:
comment only — the dirty-row mask still marks `y-1,y,y+1` mod 64, which now
*over*-approximates the reach, so "every active cell lies in a dirty row" is intact.
Law `g15_wake_step_inert`: a guard-rejected step is the identity. `wake_preserves_pot`
is a point-write law independent of reach, so it is unchanged.

**Witnesses.** Fast T43 (x=0 face wrap inert), T44 (y=0/z=0 corner), T45 (interior
control); sim T44 (an x-face move does not activate the x=63 face), T45 (vertical
analogue), T46 (in-box control). The worker verified the fast tests *fail* against
the pre-fix behaviour.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (branch and merged master).
- `bend test/tests.bend` -> 40/40 PASS; `bend test/simtests.bend` native -> 24/24 PASS.
- `bend_canary` -> 6 ok, 0 bad.

### A.89 — `V3c-2` complete: `ne_idx` is exactly `¬is_eq` on full trees

**Status:** verification only; no engine or law-meaning change. `src/commit.bend`
+608, two laws, T36/T40–T42. Gate green, fast 40/40, sim 24/24. `PLAN.md`
§4.1 (R10)/§5.1/§5.2/§5.3 updated.

**Why.** `V3c-2`'s soundness half (A.84) and structural half (A.87) were landed;
completeness — for a full `2^k`-leaf tree and in-range `i, j`,
`ne_idx(t, n, i, j) == (U32.is_eq(i, j) == False)` — was the remaining `G3` residual,
"purely arithmetic".

**What.** `src/commit.bend` gains the three arithmetic bricks and the depth
induction. (i) `is_lt` base reflection (`v3c_lt_one`/`v3c_lt_one_u32`): `Word.cmp`'s
`LT` reflects to `WCon{False,_} == Word.zero` (a sibling of `w_cmp_eq`), so
`is_lt(i, 1) == True` forces `i == 0`. (ii) `sub` range preservation
(`v3c_sub_pow_lt`/`v3c_sub_two_lt`): `is_lt(i, 2^(k+1))` ∧ ¬`is_lt(i, 2^k)` ⇒
`is_lt(sub(i, 2^k), 2^k)`, by structural recursion on the word width + exponent (the
head bit survives the even subtraction). (iii) Canonical size halves
(`v3c_two_shr_ne`/`v3c_two_shr_of_lt`): `U32.shr(v3c_two(k+1)) == v3c_two(k)` when
`v3c_two(k+1) != 0`; the `k = 31` boundary is vacuous and discharged by the size
hypothesis. Laws: `v3c_ne_idx_complete` (the converse of `v3c_ne_idx_sound`) and
`v3c_ne_idx_exact` (`ne_idx(full k, two k, i, j) == Bool.not(U32.is_eq(i, j))`), via a
depth induction over the structural case laws (with `v3c_ne_idx_sep_fl` for the
mirror orientation). T36 (32-leaf exactness), T40 (brick ii), T41 (brick iii), T42
(brick i).

**Integration note.** The append-only conflict in `test/tests.bend` was resolved by
*reconstructing* the file (master's version + the worker's added block) after a naive
keep-both fused two `match fuel:` bodies into one function — caught immediately by the
fast suite. Lesson for the worktree protocol: keep-both is safe for whole appended
*blocks* with distinct bodies, but not when two appended defs share body lines; a
3-way apply is not automatically safer.

**Residual (recorded in §5.3, `G3`).** The only remaining `V3c`/`G3` thread is wiring
the engine's `Rules.Write` list into the `v3c_fold` (the broader `G5` threading); `G3`
still gates only `M7d`, not `C3`.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (branch and merged master).
- `bend test/tests.bend` -> 40/40 PASS; `bend test/simtests.bend` native -> 24/24 PASS.

### A.90 — `V3c` engine wire: `Rules.commit_sets` is the fold (`G3` closed)

**Status:** verification only; no engine or law-meaning change. New `src/v3cw.bend`
+297, two laws, T46–T48. Gate green, fast 44/44 (merged), sim 24/24. `PLAN.md`
§4.1 (R10)/§5.1/§5.2/§5.3 updated.

**Why.** `V3c`'s fold (`v3c_fold`, A.84) and its distinctness predicate
(`v3c_ne_idx_exact`, A.89) were about the abstract `Commit.V3cWrite` list; the
engine commits a `Rules.Write` list (`commit_sets`). This wires the two, closing
`G3`'s last thread.

**What.** `src/v3cw.bend`: `v3cw_proj` maps `WSet{idx, op, src}` to
`MkWrite{idx, apply_op(src, op)}` and drops `WWake` (the tick's wake pass is
separate and Φ/state-neutral for the set fold); `v3cw_set_swap` shows the engine's
`Array.set(pack t, i, v)` equals `pack(swap_m(t, n, i, v))` when `n == g5_twidth(t)`
and `i` is in range (via `g5_size_pack`, `g5_and_mask_id`, `Count.afst_swap_m`);
`v3cw_twidth_swap_m` keeps the size hypothesis across the induction; and
`v3cw_commit_fold` proves `unpack(commit_sets(lin ws, pack t)) ==
v3c_fold(proj ws, t, n)`. `v3cw_commit_commutes` is the region-split equality
(`v3c_fold_commutes` transported), with distinctness keyed by `Commit.v3c_pair_ne`
on the projection — so `ne_idx`/`U32.is_eq` is the engine predicate. Laws:
`v3cw_commit_fold`, `v3cw_commit_commutes`.

**Methodological caveat.** `Rules.commit_sets` consumes its list linearly
(`List<&1, Write>`), while the fold/region laws mention the list twice (reusable,
`&2`); the laws are stated over a reusable `ws` plus `v3cw_lin ws`, a
multiplicity-erased copy that rebuilds the identical write list. It is the identity
on the write data, so the law is about the engine's write data; the only difference
is the kind annotation. The alternative — making `commit_sets` take `+writes` — is
an engine-signature change with a possible hot-path refcount cost.

**Verification**
- `bend PROOF.bend` -> `All terms check.` (branch and merged master).
- `bend test/tests.bend` -> 44/44 PASS; `bend test/simtests.bend` native -> 24/24 PASS.

### A.91 — `view3d`: an interactive 3D voxel viewer (presentation)

**Status:** presentation only; **no engine, law, or test-meaning change** (no `src/`
edit, no `LAWS.bend` claim). New `view/voxel.bend` + `runners/view3d.bend`, T49.
Gate green, fast 44/44, sim 24/24. `PLAN.md` §2.11/§5.1/§6 updated.

**Why.** The runners keep the model observable; the existing `window.bend` shows a
2D cross-section. This adds a real 3D view — the first presentation milestone since
M6 — without touching the verified engine.

**What.** `view/voxel.bend` (pure, zero IO) is an Amanatides–Woo DDA voxel raycaster
+ perspective camera: per pixel it builds a ray from the camera basis, marches the
64³ `Array<U32>` world, stops at the first non-empty cell, and shades material
colour × a face-normal lambert term; it builds a 128×128 quadtree `Image`.
`runners/view3d.bend` is the `App.run` shell: state = world + `speed` + camera + a
held-key mask + mouse-drag. `view` folds held keys into the camera each frame and
renders; `tick` runs `Sim.ticks(speed)` per frame (`speed` 0/1/2/4 =
paused/normal/faster) — `App.run` is frame-driven, so this is the natural tick rate.
Controls: W/A/S/D, Q/E or ←/→ yaw, ↑/↓ pitch, R/F rise/sink, mouse-drag look, space
pause, `-`/`=` speed. `main.bend` still delegates to `ascii.bend`.

**Evidence.** T49 checks the six axis rays against a shell-only world (material,
face normal, nearest-hit distance). Native: worldgen + build + a full 128×128 render
≈ 94 ms (~15–20 fps; JS interpreter ≈4.8 s, so run it compiled). The raycaster was
exercised headlessly via `bend_spike`; `runners/view3d.bend --check-only` passes and
it builds (`bend runners/view3d.bend -o bin/view3d`). `tick` could not be driven
headlessly — this Bend build rejects monadic `<-` binds in `do` blocks, so there is
no in-repo harness for `App.tick` without a window.

**Verification**
- `bend PROOF.bend` -> `All terms check.`; `bend test/tests.bend` -> 44/44 PASS;
  `bend test/simtests.bend` native -> 24/24 PASS.
- `bend runners/view3d.bend --check-only` -> `All terms check.`; native build ok.

### A.92 — `view3d` frontend pass: keyboard fix, correct ray range, 1920×1080 viewport

**Status:** presentation only; **no engine, law, or test-meaning change** (no `src/`
edit, no `LAWS.bend` claim). `view/voxel.bend` and `runners/view3d.bend` rewritten,
T50/T51 added. Gate green, fast 46/46, sim run at integration. `PLAN.md`
§2.11/§5.1/§5.2 updated.

**Why.** The first `view3d` (A.91) was correct on the DDA witness but its keyboard
did nothing on X11 and its 128×128 square image was cropped, not scaled, by a
1920×1080 window. This is the first pass on the presentation dimension: fix the
input, fix the ray range, and render the aspect-correct sub-image the window
actually shows.

**Keyboard bug.** The X11 backend reports a printable key's *character* (lowercase)
and the arrows as `63232..63235`, while the Mac/GLFW convention reports uppercase
letters and `262..265`. A.91's `bit_of` only knew the Mac codes, so W/A/S/D/Q/E/R/F
and the arrows were inert on Linux (space and `-`/`=` happened to match). `bit_of`
now accepts both conventions; T50 witnesses W/w, the two Left codes and the two Up
codes, plus depth/speed/pause.

**Ray-range bug.** `dda_steps()` was documented as cells but the four-selector DDA
consumed one fuel per *phase*, so 256 fuel reached only ~64 cells and rays past that
returned `Miss` (sky). The DDA is rewritten as a self-recursive two-calls-per-cell
machine (classify, then advance; the next cell's word is fetched during the step), so
`dda_steps()` = 256 really is 256 cells and `trace` passes `2 × dda_steps()`. T49
still witnesses the six axis rays; the old 128² image and the new DDA now agree
byte-for-byte once the old renderer is given the same 256-cell range.

**1920×1080 viewport.** `Window.frame` maps a depth-`d` square `Image` to a w×h
window by top bits: pixel `(x, y)` shows cell `(x >> s, y >> s)` with `s = k - d`
and `2^k` the smallest power of two ≥ `max(w, h)`. So a non-power-of-two window
*crops* a square image. `view_image` turns that into a feature: it computes
`clog2`, `scale_bits`, `vis_dim`, renders only the top-left `ceil(w/2^s) ×
ceil(h/2^s)` sub-image with an aspect-correct projection, and fills the rest with
sky without raycasting. At 1920×1080: depth 7 → 120×68 cells at 16×, depth 8 →
240×135 at 8×, depth 6 → 60×34 at 32×. `image` keeps the square form for T49.
T51 pins the arithmetic (`clog2 1920 = 11`, `1920×1080 @ 7 → 120×68`, etc.); the
first draft had `clog2`'s done flag inverted and T51 caught it.

**Controls.** `,`/`.` set the render depth (5–8) at runtime, so the quality/speed
tradeoff is live; window is 1920×1080; movement is unchanged.

**Evidence.** Native, 1920×1080, world build excluded: render ≈ 14 ms at depth 6,
≈ 52 ms at depth 7, ≈ 202 ms at depth 8 (Bend compiles the raycast; JS is far
slower). `bend runners/view3d.bend -o /tmp/view3d` builds and the window ran for
5 s on the live display without error.

**Verification**
- `bend PROOF.bend` -> `All terms check.`; `bend test/tests.bend` -> 46/46 PASS.
- `bend runners/view3d.bend --check-only` -> `All terms check.`; native build ok.

### A.93 — engine→renderer surfaces: export format, trace deltas, chunk-window design

**Status:** two parallel tracks landed; **no law-count change** (95 laws, PLAN
agrees), no `src/` semantics change. `bridge` (P0/P2) and `scale` (P1/P3) landed,
merged in order, `test/tests.bend` append conflict resolved. Gate green, fast
**55/55**, sim **24/24**, canary 6/6. `PLAN.md` §2.11/§5.1/§5.2/§5.3 updated.

**Why.** The sibling renderer `../Bendview/` (SPEC) consumes the engine's world.
That needs four surfaces: a serialization, a per-tick delta, a pure-gen reference
for its port conformance test, and a coordinate model that is not the fixed 64³
torus. This entry lands the first two, designs the transport, and starts the
third — without touching the rule system.

**`bridge` (track A, `runners/` only).** `runners/export.bend` is the format
contract: a chunk-oriented snapshot (`.bvs`; magic `BVS1`, v1, all 64 `Chunk.key`
records of 4096 cells in `Store.chunk_list` local order) and `Worldgen.gen`
reference vectors (`.bvg`; 128 samples spanning all four gen material classes).
The byte layout is documented at the top of the file. `runners/serve.bend` +
`runners/SERVE.md` are the headless sidecar transport design (length-framed
`[len][kind][payload]`, credit/backpressure, delta coalescing) and a skeleton
whose first snapshot is byte-identical to the exporter's. T52–T55 pin the golden
contract (cell word, `Grid.index`, `Chunk.key`, gen vector), so an engine change
that would break the renderer fails here instead of drifting.

**`scale` (track B, `src/` + proofs).** `Sim.tick_trace` returns
`(world, List<Delta>)`, a `Delta` carrying a changed cell's **global coordinate**
and **new word** (`Rules.apply_op(src, op)`), so the renderer never re-implements
an op. The write list is threaded out of `phases` before `commit_sets`; `WWake`
is ignored (activity, not a world change). `tick` is unchanged
(`tick = tick_world(tick_trace(world))`) and the carried-mask hot path
`ticks`/`tick_m` stays non-trace. T56 witnesses trace/non-trace path agreement and
delta replay on the render-visible fields. `src/cw.bend` is a new **additive**
torus-free global-coordinate module (global `(x,y,z)` ↔ `(chunk_key, local)`,
matching `Chunk`'s 16³/10-bit layout), unused by the live path; T57–T60 witness
the roundtrips and that a coordinate above the 64 box is preserved. `SCALE.md` is
the migration design (window, resident set, window motion, dirty set, `Array`
reuse) and its gap candidates are now `PLAN.md` §5.3 `G-scale-1`..`G-scale-6`.
`PROOF.bend` now imports `src/sim.bend` and `src/cw.bend` (coverage root).

**Open (filed §5.2).** `B1` transport implementation (sidecar or in-process C
FFI) + sparse snapshot; `B2` delta contract (render-visible fields vs full-word,
including wake activations); `S1` the `SCALE.md` steps 2–6 migration.

**Verification**
- `bend PROOF.bend` -> `All terms check.`; `bend test/tests.bend` -> 55/55 PASS;
  `bend test/simtests.bend` native -> 24/24 PASS; `bend_canary` -> 6 ok, 0 bad.
- `bend runners/export.bend --check-only` and `bend runners/serve.bend
  --check-only` -> `All terms check.`; both build natively.

### A.94 — bridge + scale integration: sidecar transport, B2 decision, G-scale-3 proof

**Status:** two worker branches (`bridge2`, `gscale`) landed on `master`, merged in
order (`bridge2` fast-forward, `gscale` with an append conflict in
`test/tests.bend` resolved by keeping T61–T65 then T66–T70). **Laws 95 → 100**
(PLAN agrees). Gate green, fast **65/65**, sim **24/24**, canary 6/6.

**Why.** With the export surface (A.93) landed, the two remaining engine-side
surfaces Bendview's M3/M5 need were the live transport/delta contract and the
coordinate soundness of the window migration. Both were parallelizable and were
dispatched as workers; the supervisor kept the critical path (`S1`).

**`bridge2` (track, `runners/` only).** `runners/serve.bend` is no longer a
skeleton: the length-framed little-endian `[payload_len][kind][payload]`
transport, all out kinds (HELLO/SNAPSHOT/DELTA/PING/BYE) and in kinds
(CREDIT/REQUEST/STOP), the dense first snapshot byte-identical to
`runners/export.bend`'s body, and a **sparse** snapshot that omits chunks the
engine's own regenerability test (`Store.evict`: sleeping ∧ gen-equal) can
recover via `Store.assemble`. **`B2` decided: render-visible fields only** — a
`DELTA` record is `(idx, word)` with `word = Cell.deactivate(new)`; the activity
bit is engine-internal and `WWake` is not transmitted. `idx` stays the global
`Grid.index`; the framing names no coordinate, so `S1` changes only the payload
interpretation. T61–T65 witness framing, kinds, the dense/sparse snapshots, and
the delta bytes. Residual filed as `G-bridge-1`: the credit window and delta
coalescing (`SERVE.md` §5–§6) are specified but not realised (synchronous
writer).

**`gscale` (track, `src/` + proofs).** `src/gscale.bend` closes **`G-scale-3`**:
the `cw` split/rejoin `(w>>4)<<4 + (w&15) == w & 16383` (`gscale_global_rt`) is
now a theorem in the `Bits`/`Word` model, with the disjoint-field `add == or`
brick (`gscale_add_and_or`), the shifted-field-zero bricks, and the
`model_index_rt`-style key/local model roundtrips (`gscale_kmodel_rt`,
`gscale_lmodel_rt`); the in-range reflection reuses `G5.g5_and_mask_id`. Five
laws `gscale_cw_{x,y,z,key,local}_rt`; T66–T70 witness them (T69/T70 are
stronger than T57/T58 — unconditional masked reconstruction). The laws mention
no `Grid.index`, so they are **not** in the `G-scale-6` torus retirement set.
Scoping note (not a gap): the y/z laws place the axis in its own slot with `0`
elsewhere — exactly the y/z identity, since `cw_global_y`/`_z` read only that
field; the x law uses all three coordinates and lifting y/z is a mechanical
extension.

**Frontier.** `B1`/`B2` landed; `S1` (`SCALE.md` steps 2–6) is now the frontier
and stays with the supervisor. `G-scale-1`..`G-scale-6` remain open except
`G-scale-3` (closed here).

**Verification**
- `bend PROOF.bend` -> `All terms check.`; `bend test/tests.bend` -> 65/65 PASS
  (was 55); `bend test/simtests.bend` native -> 24/24 PASS; `bend_canary` -> 6 ok,
  0 bad.
- `bend runners/serve.bend --check-only` -> `All terms check.`; native run emits
  and re-parses the six-frame stream.

### A.95 — S1 step 2: the window model and the torus-free index map

**Status:** additive step on `master`; **no law-count change** (100 laws). Gate
green, fast **67/67**, canary unchanged. Live path (`Grid`/`Sim`/`Dirty`/`Store`)
untouched.

**Why.** `S1` (`SCALE.md`) migrates the fixed 64³ torus to a moving chunk window.
Step 2 is the model and the map, landed additively so the 64³ box stays the only
instance and every existing test/world is unchanged.

**`src/window.bend`.** A `Window` is a base chunk `(bx, by, bz)`; the canonical
instance is the 64³ box at origin `(0,0,0)`. The window-local index is the
`Grid.index` layout over window-local coordinates: `lx + lz*64 + ly*4096` with
`lx = x - (bx<<4)` (the `cw` split/rejoin at a chunk-aligned origin — the proven
`gscale_global_rt` — but consuming each coordinate once, since Bend is affine and
`cw_chunk_of(x)`/`cw_local_of(x)` cannot both take `x`). Crucially there is **no
`&63`** anywhere, so a global coordinate above the box keeps its chunk index
instead of folding to the opposite face. Inverses `win_ix/iy/iz` and
`win_gx/gy/gz`; `win_key` gives the base chunk as a `cw` key. `window.bend` is
added to the `PROOF.bend` coverage root (so it is checked) but has no laws yet.

**Witnesses.** T81: `win_index(canonical, x, y, z) == Grid.index(x, y, z)` over
the box, and `win_gx/gy/gz` invert it. T82: a window at chunk `(1,1,1)` maps
global `x = 79` to window-local `63` and `x = 80` to `64` (not folded), while
`Grid.ix(Grid.index(80,0,0)) == 16` — the torus contrast.

**Filed gap.** The relabelling *law* (`win_canonical_index`) is not proven — it
needs a `U32.sub(x,0) == x` / mask-drop development — so it is `G-scale-7`
(test-witnessed by T81), following the same test-witness→gap→prove pattern as
`G-scale-3`. `S1` steps 3–6 remain.

**Verification**
- `bend PROOF.bend` -> `All terms check.`; `bend test/tests.bend` -> 67/67 PASS
  (was 65).
