import Base
import ./cell.bend as Cell
import ./settle.bend as S
import ./refine.bend as R
import ./tick.bend as T
import ./ops.bend as Ops
import ./rules.bend as Rules
import ./writepot.bend as W

# Conservation (rule 2) at the cell level: the non-empty indicator. Movement is
# a swap and transforms are material-preserving, so the count of non-Empty cells
# is the conserved quantity. This mirrors the potential (settling) layer with an
# equality instead of a decrease.

def nempty_m(m: U32) -> Nat:
  Bool.pick(Nat, U32.is_eq(m, 0), 0n, 1n)

def nempty(+w: U32) -> Nat:
  nempty_m(Cell.material(w))

# ------------------------- material-preserving writes -------------------------
# Every engine write except rock crush/crumble keeps the material field, so it
# keeps the non-empty count of the cell it touches.

def nempty_set_support(+w: U32, +s: U32) -> {nempty(Ops.set_support(w, s)) == nempty(w) : Nat}:
  Equal.cong(U32, Nat, m => nempty_m(m),
    Cell.material(Ops.set_support(w, s)), Cell.material(w),
    Equal.trans(U32,
      Cell.material(Ops.set_support(w, s)),
      U32.and(Cell.material(w), 31),
      Cell.material(w),
      W.mat_encode(Cell.material(w), Cell.cohesion(w), Cell.active(w), s, Cell.fall(w)),
      W.and31_absorb(w)))

def nempty_set_fall0(+w: U32) -> {nempty(Ops.set_fall0(w)) == nempty(w) : Nat}:
  Equal.cong(U32, Nat, m => nempty_m(m),
    Cell.material(Ops.set_fall0(w)), Cell.material(w),
    Equal.trans(U32,
      Cell.material(Ops.set_fall0(w)),
      U32.and(Cell.material(w), 31),
      Cell.material(w),
      W.mat_encode(Cell.material(w), Cell.cohesion(w), 0, Cell.support(w), 0),
      W.and31_absorb(w)))

def nempty_mov(+w: U32) -> {nempty(Rules.mov(w)) == nempty(w) : Nat}:
  +nf = U32.min(U32.add(Cell.fall(w), 1), 63)
  Equal.cong(U32, Nat, m => nempty_m(m),
    Cell.material(Rules.mov(w)), Cell.material(w),
    Equal.trans(U32,
      Cell.material(Rules.mov(w)),
      U32.and(Cell.material(w), 31),
      Cell.material(w),
      W.mat_encode(Cell.material(w), Cell.cohesion(w), Cell.active(w), Cell.support(w), nf),
      W.and31_absorb(w)))

def nempty_wake(+w: U32) -> {nempty(U32.or(w, 2048)) == nempty(w) : Nat}:
  Equal.cong(U32, Nat, m => nempty_m(m),
    Cell.material(U32.or(w, 2048)), Cell.material(w), W.mat_or_hi(w))

def nempty_deactivate(+w: U32) -> {nempty(U32.and(w, 4294965247)) == nempty(w) : Nat}:
  Equal.cong(U32, Nat, m => nempty_m(m),
    Cell.material(U32.and(w, 4294965247)), Cell.material(w), W.mat_and_hi(w))

# ------------------------- count folds -------------------------

def to_counts(a: Array<U32>) -> +List<Nat>:
  match a:
    case ALeaf{x}:
      [nempty(x)]
    case ANode{xs, ys}:
      S.app(to_counts(xs), to_counts(ys))

def cnts_m(t: R.PT) -> +List<Nat>:
  match t:
    case R.PL{x}:
      [nempty(x)]
    case R.PN{+xs, +ys}:
      S.app(cnts_m(xs), cnts_m(ys))

def to_counts_pack(t: R.PT) -> {to_counts(R.pack(t)) == cnts_m(t) : +List<Nat>}:
  match t:
    case R.PL{x}:
      {==}
    case R.PN{+xs, +ys}:
      +e1 = Equal.cong(List<&2, Nat>, List<&2, Nat>, x => S.app(x, to_counts(R.pack(ys))),
        to_counts(R.pack(xs)), cnts_m(xs), to_counts_pack(xs))
      +e2 = Equal.cong(List<&2, Nat>, List<&2, Nat>, y => S.app(cnts_m(xs), y),
        to_counts(R.pack(ys)), cnts_m(ys), to_counts_pack(ys))
      Equal.trans(List<&2, Nat>,
        to_counts(ANode{R.pack(xs), R.pack(ys)}),
        S.app(cnts_m(xs), to_counts(R.pack(ys))),
        S.app(cnts_m(xs), cnts_m(ys)),
        e1, e2)

# ------------------------- swap congruence -------------------------
# A point write changes one leaf. Its non-empty count is the same as before
# exactly when the written cell has the same non-emptiness as the displaced one;
# then the whole count list is *equal* (only that leaf could differ).

def cnts_same_if(
  +xs: R.PT, +ys: R.PT, +n: U32, +i: U32, +v: U32, +z: Bool,
  ihx: ({nempty(v) == nempty(T.tget(xs, U32.shr(n), i)) : Nat} -> {cnts_m(R.swap_m(xs, U32.shr(n), i, v)) == cnts_m(xs) : +List<Nat>}),
  ihy: ({nempty(v) == nempty(T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))) : Nat} -> {cnts_m(R.swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v)) == cnts_m(ys) : +List<Nat>}),
  h: {nempty(v) == nempty(Bool.pick(U32, z, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n))))) : Nat}
) -> {cnts_m(Bool.pick(R.PT, z, R.PN{R.swap_m(xs, U32.shr(n), i, v), ys}, R.PN{xs, R.swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v)})) == cnts_m(R.PN{xs, ys}) : +List<Nat>}:
  match z:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, x => S.app(x, cnts_m(ys)),
        cnts_m(R.swap_m(xs, U32.shr(n), i, v)),
        cnts_m(xs),
        ihx(h))
    case False{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, x => S.app(cnts_m(xs), x),
        cnts_m(R.swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v)),
        cnts_m(ys),
        ihy(h))

def cnts_same(+t: R.PT, +n: U32, +i: U32, +v: U32, +h: {nempty(v) == nempty(T.tget(t, n, i)) : Nat})
  -> {cnts_m(R.swap_m(t, n, i, v)) == cnts_m(t) : +List<Nat>}:
  match t:
    case R.PL{x}:
      Equal.cong(Nat, List<&2, Nat>, a => [a], nempty(v), nempty(x), h)
    case R.PN{+xs, +ys}:
      +z = U32.is_lt(i, U32.shr(n))
      cnts_same_if(xs, ys, n, i, v, z,
        hx => cnts_same(xs, U32.shr(n), i, v, hx),
        hy => cnts_same(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, hy),
        h)

# ------------------------- array-level conservation -------------------------

def array_point_write_preserves_count(
  +t: R.PT, +n: U32, +i: U32, +v: U32,
  +h: {nempty(v) == nempty(T.tget(t, n, i)) : Nat}
) -> {S.suml(to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)))) == S.suml(to_counts(R.pack(t))) : Nat}:
  +ea = Equal.sym(Array<U32>,
    R.pack(R.unpack(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)))),
    R.afst(Array.swap.go(U32, R.pack(t), n, i, v)),
    R.pack_unpack(R.afst(Array.swap.go(U32, R.pack(t), n, i, v))))
  +eb = Equal.cong(R.PT, Array<U32>, t2 => R.pack(t2),
    R.unpack(R.afst(Array.swap.go(U32, R.pack(t), n, i, v))), R.swap_m(t, n, i, v),
    R.swap_ref(t, n, i, v))
  +arr_eq = Equal.trans(Array<U32>,
    R.afst(Array.swap.go(U32, R.pack(t), n, i, v)),
    R.pack(R.unpack(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)))),
    R.pack(R.swap_m(t, n, i, v)),
    ea, eb)
  +e1 = Equal.cong(Array<U32>, +List<Nat>, a => to_counts(a),
    R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), R.pack(R.swap_m(t, n, i, v)), arr_eq)
  +lft = Equal.trans(+List<Nat>,
    to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v))),
    to_counts(R.pack(R.swap_m(t, n, i, v))),
    cnts_m(R.swap_m(t, n, i, v)),
    e1, to_counts_pack(R.swap_m(t, n, i, v)))
  +rgt = to_counts_pack(t)
  +same = cnts_same(t, n, i, v, h)
  Equal.trans(Nat,
    S.suml(to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)))),
    S.suml(cnts_m(R.swap_m(t, n, i, v))),
    S.suml(to_counts(R.pack(t))),
    Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
      to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v))),
      cnts_m(R.swap_m(t, n, i, v)), lft),
    Equal.trans(Nat,
      S.suml(cnts_m(R.swap_m(t, n, i, v))),
      S.suml(cnts_m(t)),
      S.suml(to_counts(R.pack(t))),
      Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
        cnts_m(R.swap_m(t, n, i, v)), cnts_m(t), same),
      Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
        cnts_m(t), to_counts(R.pack(t)),
        Equal.sym(+List<Nat>, to_counts(R.pack(t)), cnts_m(t), rgt))))

# ------------------------- instances for the engine's writes -------------------------

def array_support_write_preserves_count(+t: R.PT, +n: U32, +i: U32, +s: U32)
  -> {S.suml(to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, Ops.set_support(T.tget(t, n, i), s))))) == S.suml(to_counts(R.pack(t))) : Nat}:
  array_point_write_preserves_count(t, n, i, Ops.set_support(T.tget(t, n, i), s), nempty_set_support(T.tget(t, n, i), s))

def array_fall_write_preserves_count(+t: R.PT, +n: U32, +i: U32)
  -> {S.suml(to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, Ops.set_fall0(T.tget(t, n, i)))))) == S.suml(to_counts(R.pack(t))) : Nat}:
  array_point_write_preserves_count(t, n, i, Ops.set_fall0(T.tget(t, n, i)), nempty_set_fall0(T.tget(t, n, i)))

def array_mov_write_preserves_count(+t: R.PT, +n: U32, +i: U32)
  -> {S.suml(to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, Rules.mov(T.tget(t, n, i)))))) == S.suml(to_counts(R.pack(t))) : Nat}:
  array_point_write_preserves_count(t, n, i, Rules.mov(T.tget(t, n, i)), nempty_mov(T.tget(t, n, i)))

def array_wake_write_preserves_count(+t: R.PT, +n: U32, +i: U32)
  -> {S.suml(to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, U32.or(T.tget(t, n, i), 2048))))) == S.suml(to_counts(R.pack(t))) : Nat}:
  array_point_write_preserves_count(t, n, i, U32.or(T.tget(t, n, i), 2048), nempty_wake(T.tget(t, n, i)))

def array_deactivate_write_preserves_count(+t: R.PT, +n: U32, +i: U32)
  -> {S.suml(to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, U32.and(T.tget(t, n, i), 4294965247))))) == S.suml(to_counts(R.pack(t))) : Nat}:
  array_point_write_preserves_count(t, n, i, U32.and(T.tget(t, n, i), 4294965247), nempty_deactivate(T.tget(t, n, i)))
