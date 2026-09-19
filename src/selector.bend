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
# V3d — the engine's write *effects*, and one law per effect shape
#
# `Rules.Op` is the engine's closed set of write effects, and `Rules.Write` now
# carries one (`WSet{idx, op, src}`). That is the whole point: `plan` can only
# emit an `Op`, so "the write set is exactly the classified effects" is a typing
# fact, not an inspection of `plan` (`G14`). This module supplies the laws that
# make the type meaningful — one per effect *shape*, not one per write site.
#
# Two shapes, and they are genuinely different:
#
#   self-write    t[i] := f(t[i])          -- a point write at the index it reads
#   cross-write   t[j] := f(t[i])          -- a point write elsewhere
#
# Every `WSet` is *some* point write of an arbitrary value at a known index, and
# the exact balance is already general in that value (`Refine.array_swap_decreases`,
# `Count.array_point_write_count_balance`). So `array_op_phi_balance` /
# `array_op_count_balance` below are **total over `Rules.Op`** — whatever `plan`
# emits, its Φ and count balance is a theorem. That is `G14` closed for the
# effect classification and the balance.
#
# The *decrease* is the refinement on top, and it splits by shape:
#
#   material-preserving self-write -> Φ unchanged      (this module, PresOp family)
#   guarded crush self-write       -> Φ down by a gap  (Tick.array_guarded_crush_lowers)
#   movement                       -> a two-cell swap whose writes telescope into
#                                     the fall gap, under the fall regime
#                                     (Fall.array_mov_cross, array_mov_lowers_phi)
#
# Movement is the one shape that is *not* a single point write, which is why it
# has its own family and why the whole-tick composition (V3c-1b) has to pair the
# two halves. That pairing — and the fall regime — are the residuals, tracked as
# `G3`/`G11`; they are not effect-classification gaps.
#
# Why the preserving family is a selector rather than a function parameter: Bend
# closures are affine, so `f : U32 -> U32` may be called at most once (probe:
# `f(f(x))` is rejected, "consumed more than once"), and the traversal applies the
# write at every leaf. It has to be `Data`. `Rules.PresOp` is.
# ============================================================================

# ------------------------- the whole per-site obligation -------------------------
# Everything a new preserving write site has to prove: that it does not touch the
# material field. Two cases are direct (`mat_or_hi`/`mat_and_hi`), three go
# through the encoder (`mat_encode` + `and31_absorb`), one is the identity.
def mat_pres(+w: U32, +op: Rules.PresOp)
  -> {Cell.material(Rules.apply_pres(w, op)) == Cell.material(w) : U32}:
  match op:
    case Rules.OId{}:
      {==}
    case Rules.OSupport{+s}:
      Equal.trans(U32,
        Cell.material(Ops.set_support(w, s)),
        U32.and(Cell.material(w), 31),
        Cell.material(w),
        W.mat_encode(Cell.material(w), Cell.cohesion(w), Cell.active(w), s, Cell.fall(w)),
        W.and31_absorb(w))
    case Rules.OFall0{}:
      Equal.trans(U32,
        Cell.material(Ops.set_fall0(w)),
        U32.and(Cell.material(w), 31),
        Cell.material(w),
        W.mat_encode(Cell.material(w), Cell.cohesion(w), 0, Cell.support(w), 0),
        W.and31_absorb(w))
    case Rules.OMov{}:
      +nf = U32.min(U32.add(Cell.fall(w), 1), 63)
      Equal.trans(U32,
        Cell.material(Rules.mov(w)),
        U32.and(Cell.material(w), 31),
        Cell.material(w),
        W.mat_encode(Cell.material(w), Cell.cohesion(w), 0, Cell.support(w), nf),
        W.and31_absorb(w))
    case Rules.OAct{}:
      W.mat_or_hi(w)
    case Rules.ODeact{}:
      W.mat_and_hi(w)

# ------------------------- generic consequences of material preservation -------------------------
# `pot_at(w, k) = dens(material(w)) * to_nat(iy(k))`: material preservation at any
# index is exactly what Φ needs, so no per-site Φ arithmetic remains.
def pot_pres(+w: U32, +k: U32, +op: Rules.PresOp)
  -> {S.pot_at(Rules.apply_pres(w, op), k) == S.pot_at(w, k) : Nat}:
  Equal.cong(U32, Nat, m => Nat.mul(Pot.dens(m), U32.to_nat(Grid.iy(k))),
    Cell.material(Rules.apply_pres(w, op)), Cell.material(w), mat_pres(w, op))

# Same for the non-empty count (`nempty` is `nempty_m ∘ material`).
def nempty_pres(+w: U32, +op: Rules.PresOp)
  -> {C.nempty(Rules.apply_pres(w, op)) == C.nempty(w) : Nat}:
  Equal.cong(U32, Nat, m => C.nempty_m(m),
    Cell.material(Rules.apply_pres(w, op)), Cell.material(w), mat_pres(w, op))

# ------------------------- generic Φ tree walk (`nfst chg_m == nsnd chg_m`) -------------------------
def chg_wr_if(
  +op: Rules.PresOp, +xs: R.PT, +ys: R.PT, +base: U32, +h: U32, +i: U32, +z: Bool,
  ihx: {R.nfst(R.chg_m(xs, base, h, i, Rules.apply_pres(T.tget(xs, h, i), op))) == R.nsnd(R.chg_m(xs, base, h, i, Rules.apply_pres(T.tget(xs, h, i), op))) : Nat},
  ihy: {R.nfst(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Rules.apply_pres(T.tget(ys, h, U32.sub(i, h)), op))) == R.nsnd(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Rules.apply_pres(T.tget(ys, h, U32.sub(i, h)), op))) : Nat}
) -> {R.nfst(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, Rules.apply_pres(Bool.pick(U32, z, T.tget(xs, h, i), T.tget(ys, h, U32.sub(i, h))), op)),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Rules.apply_pres(Bool.pick(U32, z, T.tget(xs, h, i), T.tget(ys, h, U32.sub(i, h))), op))))
      == R.nsnd(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, Rules.apply_pres(Bool.pick(U32, z, T.tget(xs, h, i), T.tget(ys, h, U32.sub(i, h))), op)),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Rules.apply_pres(Bool.pick(U32, z, T.tget(xs, h, i), T.tget(ys, h, U32.sub(i, h))), op))))
      : Nat}:
  match z:
    case True{}: ihx
    case False{}: ihy

def chg_wr(+op: Rules.PresOp, t: R.PT, +base: U32, +n: U32, +i: U32)
  -> {R.nfst(R.chg_m(t, base, n, i, Rules.apply_pres(T.tget(t, n, i), op))) == R.nsnd(R.chg_m(t, base, n, i, Rules.apply_pres(T.tget(t, n, i), op))) : Nat}:
  match t:
    case R.PL{x}:
      Equal.sym(Nat, S.pot_at(Rules.apply_pres(x, op), base), S.pot_at(x, base), pot_pres(x, base, op))
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      chg_wr_if(op, xs, ys, base, h, i, z,
        chg_wr(op, xs, base, h, i),
        chg_wr(op, ys, U32.add(base, h), h, U32.sub(i, h)))

# ------------------------- generic count tree walk -------------------------
def cnt_wr_if(
  +op: Rules.PresOp, +xs: R.PT, +ys: R.PT, +n: U32, +i: U32, +z: Bool,
  ihx: {R.nfst(C.cnt_chg_m(xs, U32.shr(n), i, Rules.apply_pres(T.tget(xs, U32.shr(n), i), op))) == R.nsnd(C.cnt_chg_m(xs, U32.shr(n), i, Rules.apply_pres(T.tget(xs, U32.shr(n), i), op))) : Nat},
  ihy: {R.nfst(C.cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), Rules.apply_pres(T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n))), op))) == R.nsnd(C.cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), Rules.apply_pres(T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n))), op))) : Nat}
) -> {R.nfst(Bool.pick(Nat & Nat, z,
        C.cnt_chg_m(xs, U32.shr(n), i, Rules.apply_pres(Bool.pick(U32, z, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))), op)),
        C.cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), Rules.apply_pres(Bool.pick(U32, z, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))), op))))
      == R.nsnd(Bool.pick(Nat & Nat, z,
        C.cnt_chg_m(xs, U32.shr(n), i, Rules.apply_pres(Bool.pick(U32, z, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))), op)),
        C.cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), Rules.apply_pres(Bool.pick(U32, z, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))), op))))
      : Nat}:
  match z:
    case True{}: ihx
    case False{}: ihy

def cnt_wr(+op: Rules.PresOp, t: R.PT, +n: U32, +i: U32)
  -> {R.nfst(C.cnt_chg_m(t, n, i, Rules.apply_pres(T.tget(t, n, i), op))) == R.nsnd(C.cnt_chg_m(t, n, i, Rules.apply_pres(T.tget(t, n, i), op))) : Nat}:
  match t:
    case R.PL{x}:
      Equal.sym(Nat, C.nempty(Rules.apply_pres(x, op)), C.nempty(x), nempty_pres(x, op))
    case R.PN{+xs, +ys}:
      +z = U32.is_lt(i, U32.shr(n))
      cnt_wr_if(op, xs, ys, n, i, z,
        cnt_wr(op, xs, U32.shr(n), i),
        cnt_wr(op, ys, U32.shr(n), U32.sub(i, U32.shr(n))))

# ------------------------- the two array-level theorems -------------------------
# Φ is preserved by any *material-preserving self-write*, at any index: one proof,
# all six constructors.
def array_write_preserves_phi(+op: Rules.PresOp, +t: R.PT, +base: U32, +n: U32, +i: U32)
  -> {S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, Rules.apply_pres(T.tget(t, n, i), op))), base, n)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  +v = Rules.apply_pres(T.tget(t, n, i), op)
  +after = S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), base, n))
  +before = S.suml(S.to_pots(R.pack(t), base, n))
  +w1 = R.nfst(R.chg_m(t, base, n, i, v))
  +w2 = R.nsnd(R.chg_m(t, base, n, i, v))
  +eq = chg_wr(op, t, base, n, i)
  +dec = R.array_swap_decreases(t, base, n, i, v)
  +e1 = Equal.cong(Nat, Nat, x => Nat.add(after, x), w2, w1, Equal.sym(Nat, w1, w2, eq))
  +e2 = Equal.trans(Nat, Nat.add(after, w2), Nat.add(after, w1), Nat.add(before, w2), e1, dec)
  NatL.n_add_cancel_right(after, before, w2, e2)

# Conservation is preserved by any material-preserving self-write, at any index.
def array_write_preserves_count(+op: Rules.PresOp, +t: R.PT, +n: U32, +i: U32)
  -> {S.suml(C.to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, Rules.apply_pres(T.tget(t, n, i), op))))) == S.suml(C.to_counts(R.pack(t))) : Nat}:
  +v = Rules.apply_pres(T.tget(t, n, i), op)
  +after = S.suml(C.to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v))))
  +before = S.suml(C.to_counts(R.pack(t)))
  +w1 = R.nfst(C.cnt_chg_m(t, n, i, v))
  +w2 = R.nsnd(C.cnt_chg_m(t, n, i, v))
  +eq = cnt_wr(op, t, n, i)
  +bal = C.array_point_write_count_balance(t, n, i, v)
  +e1 = Equal.cong(Nat, Nat, x => Nat.add(after, x), w2, w1, Equal.sym(Nat, w1, w2, eq))
  +e2 = Equal.trans(Nat, Nat.add(after, w2), Nat.add(after, w1), Nat.add(before, w2), e1, bal)
  NatL.n_add_cancel_right(after, before, w2, e2)

# ------------------------- total over `Rules.Op`: the G14 closure -------------------------
# A `WSet{idx, op, src}` writes `apply_op(src, op)` at `idx`. That is a point write
# of *some* value at a known index, and the exact balance is general in the value
# — so this is total over `Op`, and needs no case split. `src` is the word `plan`
# read; the balance does not depend on where it came from.
def array_op_phi_balance(+op: Rules.Op, +t: R.PT, +base: U32, +n: U32, +i: U32, +src: U32)
  -> {Nat.add(S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, Rules.apply_op(src, op))), base, n)), R.nfst(R.chg_m(t, base, n, i, Rules.apply_op(src, op)))) == Nat.add(S.suml(S.to_pots(R.pack(t), base, n)), R.nsnd(R.chg_m(t, base, n, i, Rules.apply_op(src, op)))) : Nat}:
  R.array_swap_decreases(t, base, n, i, Rules.apply_op(src, op))

def array_op_count_balance(+op: Rules.Op, +t: R.PT, +n: U32, +i: U32, +src: U32)
  -> {Nat.add(S.suml(C.to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, Rules.apply_op(src, op))))), R.nfst(C.cnt_chg_m(t, n, i, Rules.apply_op(src, op)))) == Nat.add(S.suml(C.to_counts(R.pack(t))), R.nsnd(C.cnt_chg_m(t, n, i, Rules.apply_op(src, op)))) : Nat}:
  C.array_point_write_count_balance(t, n, i, Rules.apply_op(src, op))
