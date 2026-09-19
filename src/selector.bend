import Base
import ./refine.bend as R
import ./settle.bend as S
import ./count.bend as C
import ./tick.bend as T
import ./cell.bend as Cell
import ./ops.bend as Ops
import ./rules.bend as Rules
import ./potential.bend as Pot
import ./grid.bend as Grid
import ./nat.bend as NatL
import ./writepot.bend as W

# ============================================================================
# V3d — one generic law for the whole material-preserving write family
#
# Why this module exists (measured, A.78).
#
# Every engine write that keeps the cell's material field also keeps its
# potential and its non-empty count. The count layer already said that once
# (`Count.array_point_write_preserves_count`, with five one-line instances), but
# the potential layer said it *four times over*: `Tick.chg_support`/`chg_fall`/
# `chg_activate`/`chg_deactivate`, each a full recursive walk of the `PT` tree,
# each paired with its own `chg_X_if` distribution lemma and its own
# `array_X_write`. Same proof, different leaf function.
#
# The reason it could not be factored with an ordinary function parameter is a
# language fact, not a modelling one: **Bend closures are affine, so a parameter
# `f : U32 -> U32` may be called at most once** (spike: `f(f(x))` is rejected
# with "consumed more than once"). A write function must be applied at *every*
# leaf of the traversal, so it cannot be a parameter. It must be `Data`.
#
# So the write choice is a `Data`-kinded selector: one constructor per
# material-preserving write primitive. `apply_w` is then a top-level def (freely
# callable) and the traversal is written once. This is the same device `SupSel`
# and `StepSel` already use, generalised to the write family.
#
# Coverage win, not just a size win. Because the family is enumerated here,
# `array_write_preserves_phi` holds for *every* constructor at once, including
# two sites (`set_fall0`, `deactivate`) that previously had no array-level Φ law
# at all — the live `Rules.plan` emits both on every tick (sel 22/23 and 4), and
# the only thing that used to account for them was `step_m`, which mirrors the
# *retired* `Rules.step` (A.63, `G10`) and is no longer evidence (`G14`).
#
# Scope: material-preserving writes only. Rock crush/crumble changes material and
# is a genuine Φ *decrease*; it stays in `writepot`/`tick` with its own gap
# (`crush_gap`/`guard_gap`). Movement is two writes; the only one that changes Φ
# is the displacement, accounted by `Fall.array_mov_cross`.
# ============================================================================

type WrSel is Data:
  WSupport{s: U32}
  WFall0{}
  WMov{}
  WAct{}
  WDeact{}

# The write primitive, selected by a `Data` value. Total and matchable at every
# leaf of a recursion.
def apply_w(+w: U32, +sel: WrSel) -> U32:
  match sel:
    case WSupport{+s}: Ops.set_support(w, s)
    case WFall0{}: Ops.set_fall0(w)
    case WMov{}: Rules.mov(w)
    case WAct{}: Cell.activate(w)
    case WDeact{}: Cell.deactivate(w)

# ------------------------- the whole per-site obligation -------------------------
# Everything a new write site has to prove: that it does not touch the material
# field. Two cases are direct (`mat_or_hi`/`mat_and_hi`), three go through the
# encoder (`mat_encode` + `and31_absorb`).
def mat_pres(+w: U32, +sel: WrSel)
  -> {Cell.material(apply_w(w, sel)) == Cell.material(w) : U32}:
  match sel:
    case WSupport{+s}:
      Equal.trans(U32,
        Cell.material(Ops.set_support(w, s)),
        U32.and(Cell.material(w), 31),
        Cell.material(w),
        W.mat_encode(Cell.material(w), Cell.cohesion(w), Cell.active(w), s, Cell.fall(w)),
        W.and31_absorb(w))
    case WFall0{}:
      Equal.trans(U32,
        Cell.material(Ops.set_fall0(w)),
        U32.and(Cell.material(w), 31),
        Cell.material(w),
        W.mat_encode(Cell.material(w), Cell.cohesion(w), 0, Cell.support(w), 0),
        W.and31_absorb(w))
    case WMov{}:
      +nf = U32.min(U32.add(Cell.fall(w), 1), 63)
      Equal.trans(U32,
        Cell.material(Rules.mov(w)),
        U32.and(Cell.material(w), 31),
        Cell.material(w),
        W.mat_encode(Cell.material(w), Cell.cohesion(w), 0, Cell.support(w), nf),
        W.and31_absorb(w))
    case WAct{}:
      W.mat_or_hi(w)
    case WDeact{}:
      W.mat_and_hi(w)

# ------------------------- generic consequences of material preservation -------------------------
# `pot_at(w, k) = dens(material(w)) * to_nat(iy(k))`: material preservation at any
# index is exactly what Φ needs, so no per-site Φ arithmetic remains.
def pot_pres(+w: U32, +k: U32, +sel: WrSel)
  -> {S.pot_at(apply_w(w, sel), k) == S.pot_at(w, k) : Nat}:
  Equal.cong(U32, Nat, m => Nat.mul(Pot.dens(m), U32.to_nat(Grid.iy(k))),
    Cell.material(apply_w(w, sel)), Cell.material(w), mat_pres(w, sel))

# Same for the non-empty count (`nempty` is `nempty_m ∘ material`).
def nempty_pres(+w: U32, +sel: WrSel)
  -> {C.nempty(apply_w(w, sel)) == C.nempty(w) : Nat}:
  Equal.cong(U32, Nat, m => C.nempty_m(m),
    Cell.material(apply_w(w, sel)), Cell.material(w), mat_pres(w, sel))

# ------------------------- generic Φ tree walk (`nfst chg_m == nsnd chg_m`) -------------------------
def chg_wr_if(
  +sel: WrSel, +xs: R.PT, +ys: R.PT, +base: U32, +h: U32, +i: U32, +z: Bool,
  ihx: {R.nfst(R.chg_m(xs, base, h, i, apply_w(T.tget(xs, h, i), sel))) == R.nsnd(R.chg_m(xs, base, h, i, apply_w(T.tget(xs, h, i), sel))) : Nat},
  ihy: {R.nfst(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), apply_w(T.tget(ys, h, U32.sub(i, h)), sel))) == R.nsnd(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), apply_w(T.tget(ys, h, U32.sub(i, h)), sel))) : Nat}
) -> {R.nfst(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, apply_w(Bool.pick(U32, z, T.tget(xs, h, i), T.tget(ys, h, U32.sub(i, h))), sel)),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), apply_w(Bool.pick(U32, z, T.tget(xs, h, i), T.tget(ys, h, U32.sub(i, h))), sel))))
      == R.nsnd(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, apply_w(Bool.pick(U32, z, T.tget(xs, h, i), T.tget(ys, h, U32.sub(i, h))), sel)),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), apply_w(Bool.pick(U32, z, T.tget(xs, h, i), T.tget(ys, h, U32.sub(i, h))), sel))))
      : Nat}:
  match z:
    case True{}: ihx
    case False{}: ihy

def chg_wr(+sel: WrSel, t: R.PT, +base: U32, +n: U32, +i: U32)
  -> {R.nfst(R.chg_m(t, base, n, i, apply_w(T.tget(t, n, i), sel))) == R.nsnd(R.chg_m(t, base, n, i, apply_w(T.tget(t, n, i), sel))) : Nat}:
  match t:
    case R.PL{x}:
      Equal.sym(Nat, S.pot_at(apply_w(x, sel), base), S.pot_at(x, base), pot_pres(x, base, sel))
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      chg_wr_if(sel, xs, ys, base, h, i, z,
        chg_wr(sel, xs, base, h, i),
        chg_wr(sel, ys, U32.add(base, h), h, U32.sub(i, h)))

# ------------------------- generic count tree walk -------------------------
def cnt_wr_if(
  +sel: WrSel, +xs: R.PT, +ys: R.PT, +n: U32, +i: U32, +z: Bool,
  ihx: {R.nfst(C.cnt_chg_m(xs, U32.shr(n), i, apply_w(T.tget(xs, U32.shr(n), i), sel))) == R.nsnd(C.cnt_chg_m(xs, U32.shr(n), i, apply_w(T.tget(xs, U32.shr(n), i), sel))) : Nat},
  ihy: {R.nfst(C.cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), apply_w(T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n))), sel))) == R.nsnd(C.cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), apply_w(T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n))), sel))) : Nat}
) -> {R.nfst(Bool.pick(Nat & Nat, z,
        C.cnt_chg_m(xs, U32.shr(n), i, apply_w(Bool.pick(U32, z, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))), sel)),
        C.cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), apply_w(Bool.pick(U32, z, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))), sel))))
      == R.nsnd(Bool.pick(Nat & Nat, z,
        C.cnt_chg_m(xs, U32.shr(n), i, apply_w(Bool.pick(U32, z, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))), sel)),
        C.cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), apply_w(Bool.pick(U32, z, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))), sel))))
      : Nat}:
  match z:
    case True{}: ihx
    case False{}: ihy

def cnt_wr(+sel: WrSel, t: R.PT, +n: U32, +i: U32)
  -> {R.nfst(C.cnt_chg_m(t, n, i, apply_w(T.tget(t, n, i), sel))) == R.nsnd(C.cnt_chg_m(t, n, i, apply_w(T.tget(t, n, i), sel))) : Nat}:
  match t:
    case R.PL{x}:
      Equal.sym(Nat, C.nempty(apply_w(x, sel)), C.nempty(x), nempty_pres(x, sel))
    case R.PN{+xs, +ys}:
      +z = U32.is_lt(i, U32.shr(n))
      cnt_wr_if(sel, xs, ys, n, i, z,
        cnt_wr(sel, xs, U32.shr(n), i),
        cnt_wr(sel, ys, U32.shr(n), U32.sub(i, U32.shr(n))))

# ------------------------- the two array-level theorems -------------------------
# Φ is preserved by any selected write, at any index. One proof, all five sites.
def array_write_preserves_phi(+sel: WrSel, +t: R.PT, +base: U32, +n: U32, +i: U32)
  -> {S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, apply_w(T.tget(t, n, i), sel))), base, n)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  +v = apply_w(T.tget(t, n, i), sel)
  +after = S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), base, n))
  +before = S.suml(S.to_pots(R.pack(t), base, n))
  +w1 = R.nfst(R.chg_m(t, base, n, i, v))
  +w2 = R.nsnd(R.chg_m(t, base, n, i, v))
  +eq = chg_wr(sel, t, base, n, i)
  +dec = R.array_swap_decreases(t, base, n, i, v)
  +e1 = Equal.cong(Nat, Nat, x => Nat.add(after, x), w2, w1, Equal.sym(Nat, w1, w2, eq))
  +e2 = Equal.trans(Nat, Nat.add(after, w2), Nat.add(after, w1), Nat.add(before, w2), e1, dec)
  NatL.n_add_cancel_right(after, before, w2, e2)

# Conservation is preserved by any selected write, at any index.
def array_write_preserves_count(+sel: WrSel, +t: R.PT, +n: U32, +i: U32)
  -> {S.suml(C.to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, apply_w(T.tget(t, n, i), sel))))) == S.suml(C.to_counts(R.pack(t))) : Nat}:
  +v = apply_w(T.tget(t, n, i), sel)
  +after = S.suml(C.to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v))))
  +before = S.suml(C.to_counts(R.pack(t)))
  +w1 = R.nfst(C.cnt_chg_m(t, n, i, v))
  +w2 = R.nsnd(C.cnt_chg_m(t, n, i, v))
  +eq = cnt_wr(sel, t, n, i)
  +bal = C.array_point_write_count_balance(t, n, i, v)
  +e1 = Equal.cong(Nat, Nat, x => Nat.add(after, x), w2, w1, Equal.sym(Nat, w1, w2, eq))
  +e2 = Equal.trans(Nat, Nat.add(after, w2), Nat.add(after, w1), Nat.add(before, w2), e1, bal)
  NatL.n_add_cancel_right(after, before, w2, e2)
