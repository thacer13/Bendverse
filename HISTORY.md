# Bendverse — History

Append-only AI milestone log: one entry per landed step, newest last. This file
was `PLAN.md`'s Appendix A until the v2 rewrite; `PLAN.md` is now the normative
plan and this file is the record of how the implementation got there.

Entries are append-only — never rewrite one in place; append a correction.

The first line below preserves the original transition note; the convention it
describes now applies to *this* file.

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
