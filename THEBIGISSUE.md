# THE BIG ISSUE

*Standalone assessment, written 2026-09-19 (A.78). Deliberately outside the
document hierarchy in `AGENTS.md`: this is not a claim, a plan, or a milestone.
It is the "if a full rewrite has to come, start here" note. Nothing in `src/`,
`LAWS.bend`, or `PROOF.bend` depends on it.*

---

## The question

Can this system maintain a **tractable refinement relationship** between an
abstract mathematical simulation and an efficient, mutation-heavy
implementation, while deriving meaningful global properties from local laws?

Measured answer: **yes, but the ladder stops one rung short of the tick, and one
language limitation decides whether it stays tractable.**

The one rung:

```
abstract List-world + Φ + budget      Settle, Potential — small, clean, GLOBAL theorems
        ↓  per-write, over PT          swap_m, chg_m, array_* laws
        ↓  [MISSING]                   List<Write> fold (V3c-1b); plan mirror (G14)
        tick / Sim                    the 1113-LOC engine
```

Global theorems exist, but only at the top (`fall_lowers_potential`,
`crumble_lowers_potential`, `strict_events_bounded`, `settling_budget`,
`potential_additive` — about an abstract `List` world and Φ = Σ density×height).
Nothing yet has the live tick as its subject.

---

## Measurements (not impressions)

| | value |
|---|---|
| engine reachable from `main.bend` | 1113 LOC / 8 files |
| verification tree (everything else in `src/`) | 7066 LOC / 22 files |
| ratio | **6.3×** (seL4 ≈ 10×, CompCert ≈ 7×) |
| `srcLOC / lawsLOC` over history | 22.6 → 25.8 → 17.3 → 17.4 → 18.1 → 19.5 → **17.1** — stable |
| laws | 70 → 75 (A.78), gate green in ~5.8 s |
| `Equal.trans` + `Equal.cong` uses in `src/` | **788** |
| laws spelling out a whole-array Φ sum by hand | 24 of 75 |
| holes / `believe_me` / `admit` | **0** |
| checker canaries | 6 ok, 0 bad (3 are negative controls) |
| world | 64³ = 262144 cells, 1 MB |
| tests | 26 fast, 20 sim |

## The eight worries, adjudicated

1. **"Law files growing faster than the implementation" — FALSE.** The ratio is
   stable across the whole history. The 6.3× proof:code ratio is normal for
   verified software, not pathological.
2. **"Proofs are manual equality threading" — TRUE.** 788 `Equal.trans/cong`.
   `rotate2` in `potential.bend` is 5 nested `Equal.trans` for
   `(Y+D)+G == (D+G)+Y`; `src/nat.bend` (178 LOC) is a hand-rolled arithmetic
   library. No tactics, no `omega`/`ring`. This is the largest standing tax: a
   10-LOC mathematical fact costs ~30 LOC of term.
3. **"Every optimization duplicates the abstract model" — TRUE, already paid once
   at a loss.** `src/step.bend` (452 LOC) mirrors `Rules.step`, which A.63
   **deleted**; it is now marked RETIRED in-file and in `LAWS.bend`. `G14` asks
   for a *fresh* mirror of `Rules.plan` (~120-line, 24-state selector machine).
4. **"The abstract model looks almost identical to the implementation" — TRUE in
   the mirrors, FALSE in the math.** `Refine.swap_m` is structurally
   `Array.swap.go`; `tick.bend`'s `tget`/`chg_m`/`sup_m` (618 lines of plain
   defs) re-spell the engine's array walk over a tree; `step_m` re-encodes
   numeric selectors as datatypes. The mirror exists because of a *language*
   limitation (linearity forbids naming an `Array` twice — `G8`), not a modelling
   insight. The top of the ladder (86 + 329 LOC) is genuinely abstract and clean.
5. **"potential/count/refinement laws never elevated to global theorems" — TRUE
   for the live engine, FALSE for the model.** See the ladder above. One rung
   short, not absent.
6. **"Compiler/runtime opaque despite all the proofs" — TRUE, managed.** Zero
   holes; green gate in 5.8 s; canaries with negative controls. But the proof
   language's reduction behaviour is load-bearing and subtle: `swap_m` "does not
   reduce through a `Bool.pick`"; a concrete `3` in a proposition "unrolls the
   loop"; `match` cannot scrutinize a local binder or a computed value; large
   `Nat` literals are expanded unary and blow the compiler
   (`Nat.is_eq(6300n, 6300n)` overflows, the same value built at runtime is
   fine). See "Language traps" below.
7. **"Tractable only because the state is tiny" — FALSE.** 262144 cells, ~1.3 µs
   settled tick, and the proofs are *size-generic* (`n` a parameter, `t: PT`
   arbitrary depth) — verification cost does not scale with world size at all.
8. **"Cumbersome to navigate" — PARTLY.** Navigation aids are unusually good
   (machine-read gap registry, `bend_status`/`audit`, a conformance table that
   honestly records R6/R7 as **deviating**). The awkwardness is that the map is
   bigger than the territory, and staleness risk concentrates in the mirror
   files: 77 history entries, ~90 lines mentioning retirement/refutation/
   obsolescence; A.52's `base+i` form was outright false; A.57's framing went
   obsolete.

---

## The decisive constraint

**Bend closures are affine: a parameter `f : U32 -> U32` may be called at most
once.** Probe:

```python
def app2(f: U32 -> U32, x: U32) -> U32:
  f(f(x))     # rejected: "consumed more than once"
```

A write function must be applied at *every leaf* of a traversal, so it cannot be
a function parameter. It must be `Data`. That single fact is why:

- each write site grew its own `chg_X` / `chg_X_if` / `array_X_write` triple;
- `SupSel` and `StepSel` exist as datatype re-encodings of numeric selectors;
- `Refine.PT` exists at all (linearity forbids naming an `Array` twice — `G8`).

The escape hatch is a **`Data`-kinded selector**. A.78 proved it works: one
traversal (`Selector.chg_wr`), one per-site obligation (`Selector.mat_pres`),
and two array-level laws that hold for the whole family at once.

```python
type WrSel is Data:
  WSupport{s: U32}
  WFall0{}
  WMov{}
  WAct{}
  WDeact{}
```

**This is the investment decision.** If a new optimization can be expressed as a
constructor on a `Data` selector, it costs a statement. If it needs a *new kind*
of traversal (a different fold shape, a read, a two-leaf effect), it costs a
mirror. `step_m` is the precedent for the second case, and it was written off.

---

## What A.78 actually changed

1. `src/selector.bend` — the generic family. 5 new laws (75 total). The four
   hand-written Φ recursions collapse to one.
2. **A real coverage hole closed.** `set_fall0` and `deactivate` are emitted by
   the live `Rules.plan` on every tick (sel 22/23 and 4) and had **no
   array-level Φ law at all**. Their only coverage was `step_m` — which mirrors
   the retired `Rules.step`. Now unconditional.
3. `step_mirror_balance` marked RETIRED in `LAWS.bend`; the `R2` conformance row
   no longer cites the closed `G10` as write-site coverage while `G14` is open.
4. **The first executable Φ oracle.** `Settle.array_phi` is proof-side and
   `Settle.suml` is not tail-recursive, so it overflows on a 2^18-cell world —
   which is *why* the flagship property had never been checked end to end. T38
   now runs it: Φ is non-increasing across 60 real ticks and strictly decreases.
   T39 pins the oracle to `Settle.pot_at`.

Remaining for `G14`: only that `Rules.plan` emits no other *kind* of write.

---

## Language traps (all hit while doing the above)

| trap | consequence |
|---|---|
| closures are affine (one call) | generic-over-a-function is impossible; use a `Data` selector |
| `match` cannot scrutinize a computed value or a local binder | pair-returning folds must be unpacked through a parameter; adds a def per step |
| large `Nat` literals are expanded unary | `Nat.is_eq(6300n, 6300n)` overflows the compiler; build the value at runtime |
| `+` requires `Data`-kinded | `Array` and function values cannot be marked reusable |
| `suml` is not tail-recursive | no proof-side function is executable on a real world |
| the JS backend overflows on some shapes | tick-heavy tests must run native (`bend_test suite=sim`) |

None of these is a soundness problem. All of them are why proof files are
verbose, and all of them are undocumented outside this file.

---

## What to do next (cheapest first)

1. **Prove V3c-1b** — fold `point_writes_commute` over `List<Write>`. That turns
   T1's determinism from "by construction" into a theorem and is the other half
   of `G3`. Highest value per LOC on the board.
2. **Close `G14`** — with A.78 the write side is covered; what is left is that
   `plan` emits only those primitives. Consider mirroring `plan` with a `Data`
   selector from the start rather than a fresh hand-written walk.
3. **Check whether the *other* mirrors can go selector-shaped.** `sup_m` and the
   `Count` family are the obvious candidates.
4. **Retire `src/step.bend` entirely** (or move it under a `retired/` path) once
   `G14` lands. A dead mirror that still compiles is a maintenance trap.
5. **Consider a `V0-5`/R6/R7 item**: `Ops.shell_adjacent` seeds support from
   *coordinates*, not the neighbourhood — the one place the conformance table
   says the engine deviates from the rules it is verified against.

## If a rewrite comes

Keep, in this order:

1. `Potential`/`Settle` — the abstract Φ and the settling budget. Small, clean,
   and the only place global theorems live. Untouched by all of the above.
2. `Refine.PT` + `swap_ref` + `array_swap_decreases` — the *general* point-write
   balance. This is the load-bearing refinement; everything else is an instance.
3. `Selector` — one traversal per *family* of effects, never one per write site.
4. The gap registry and the conformance table. They are the reason this review
   could be done at all, and the reason R6/R7 are not silently "conforming".

Drop: any hand-written `chg_X` recursion; any mirror whose subject has been
retired; any proof-side function that is expected to run.

**The contract that decides everything:** every new effect must be expressible as
a `Data` selector over a *fixed* fold shape. The moment an optimization needs a
new traversal shape, the mirror cost returns in full — and that is the signal to
stop and redesign rather than pay it.
