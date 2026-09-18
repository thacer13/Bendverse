import Base
import ./nat.bend as NatL
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

# The written list and the (displaced, written) count pair, mirroring
# `pots_swap_m`/`chg_m` but with no positional dependence (counts need no base).
def cnts_swap_m(t: R.PT, +n: U32, +i: U32, +v: U32) -> +List<Nat>:
  match t:
    case R.PL{x}:
      [nempty(v)]
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      Bool.pick(List<&2, Nat>, z,
        S.app(cnts_swap_m(xs, h, i, v), cnts_m(ys)),
        S.app(cnts_m(xs), cnts_swap_m(ys, h, U32.sub(i, h), v)))

def cnt_chg_m(t: R.PT, +n: U32, +i: U32, +v: U32) -> Nat & Nat:
  match t:
    case R.PL{x}:
      (nempty(x), nempty(v))
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      Bool.pick(Nat & Nat, z,
        cnt_chg_m(xs, h, i, v),
        cnt_chg_m(ys, h, U32.sub(i, h), v))

# The written count list equals the model swap's count list.
def cnts_corr_if(
  +xs: R.PT, +ys: R.PT, +n: U32, +i: U32, +v: U32, +z: Bool,
  ihx: {cnts_m(R.swap_m(xs, U32.shr(n), i, v)) == cnts_swap_m(xs, U32.shr(n), i, v) : +List<Nat>},
  ihy: {cnts_m(R.swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v)) == cnts_swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v) : +List<Nat>}
) -> {cnts_m(Bool.pick(R.PT, z, R.PN{R.swap_m(xs, U32.shr(n), i, v), ys}, R.PN{xs, R.swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v)}))
    == Bool.pick(List<&2, Nat>, z,
        S.app(cnts_swap_m(xs, U32.shr(n), i, v), cnts_m(ys)),
        S.app(cnts_m(xs), cnts_swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v)))
    : +List<Nat>}:
  match z:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>,
        x => S.app(x, cnts_m(ys)),
        cnts_m(R.swap_m(xs, U32.shr(n), i, v)),
        cnts_swap_m(xs, U32.shr(n), i, v), ihx)
    case False{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>,
        x => S.app(cnts_m(xs), x),
        cnts_m(R.swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v)),
        cnts_swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v), ihy)

def cnts_corr(t: R.PT, +n: U32, +i: U32, +v: U32)
  -> {cnts_m(R.swap_m(t, n, i, v)) == cnts_swap_m(t, n, i, v) : +List<Nat>}:
  match t:
    case R.PL{x}:
      {==}
    case R.PN{+xs, +ys}:
      +z = U32.is_lt(i, U32.shr(n))
      cnts_corr_if(xs, ys, n, i, v, z,
        cnts_corr(xs, U32.shr(n), i, v),
        cnts_corr(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v))

# The count balance: a point write displaces `old` and inserts `new`, so the new
# count plus the displaced count equals the old count plus the written count.
def cnt_balance_if(
  +xs: R.PT, +ys: R.PT, +n: U32, +i: U32, +v: U32, +z: Bool,
  ihx: {Nat.add(S.suml(cnts_swap_m(xs, U32.shr(n), i, v)), R.nfst(cnt_chg_m(xs, U32.shr(n), i, v))) == Nat.add(S.suml(cnts_m(xs)), R.nsnd(cnt_chg_m(xs, U32.shr(n), i, v))) : Nat},
  ihy: {Nat.add(S.suml(cnts_swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v)), R.nfst(cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v))) == Nat.add(S.suml(cnts_m(ys)), R.nsnd(cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v))) : Nat}
) -> {Nat.add(S.suml(Bool.pick(List<&2, Nat>, z,
        S.app(cnts_swap_m(xs, U32.shr(n), i, v), cnts_m(ys)),
        S.app(cnts_m(xs), cnts_swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v)))),
      R.nfst(Bool.pick(Nat & Nat, z, cnt_chg_m(xs, U32.shr(n), i, v), cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v))))
    == Nat.add(S.suml(S.app(cnts_m(xs), cnts_m(ys))),
      R.nsnd(Bool.pick(Nat & Nat, z, cnt_chg_m(xs, U32.shr(n), i, v), cnt_chg_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v))))
    : Nat}:
  match z:
    case True{}:
      +h = U32.shr(n)
      +BX = S.suml(cnts_m(xs))
      +R = S.suml(cnts_m(ys))
      +OLD = R.nfst(cnt_chg_m(xs, h, i, v))
      +NEW = R.nsnd(cnt_chg_m(xs, h, i, v))
      +ea = S.suml_append(cnts_swap_m(xs, h, i, v), cnts_m(ys))
      +eb = S.suml_append(cnts_m(xs), cnts_m(ys))
      +s1 = S.swap_add(S.suml(cnts_swap_m(xs, h, i, v)), R, OLD)
      +s2 = Equal.cong(Nat, Nat, x => Nat.add(x, R),
        Nat.add(S.suml(cnts_swap_m(xs, h, i, v)), OLD), Nat.add(BX, NEW), ihx)
      +s3 = Equal.sym(Nat, Nat.add(Nat.add(BX, R), NEW), Nat.add(Nat.add(BX, NEW), R), S.swap_add(BX, R, NEW))
      Equal.trans(Nat,
        Nat.add(S.suml(S.app(cnts_swap_m(xs, h, i, v), cnts_m(ys))), OLD),
        Nat.add(Nat.add(BX, R), NEW),
        Nat.add(S.suml(S.app(cnts_m(xs), cnts_m(ys))), NEW),
        Equal.trans(Nat,
          Nat.add(S.suml(S.app(cnts_swap_m(xs, h, i, v), cnts_m(ys))), OLD),
          Nat.add(Nat.add(S.suml(cnts_swap_m(xs, h, i, v)), R), OLD),
          Nat.add(Nat.add(BX, R), NEW),
          Equal.cong(Nat, Nat, s => Nat.add(s, OLD),
            S.suml(S.app(cnts_swap_m(xs, h, i, v), cnts_m(ys))),
            Nat.add(S.suml(cnts_swap_m(xs, h, i, v)), R), ea),
          Equal.trans(Nat,
            Nat.add(Nat.add(S.suml(cnts_swap_m(xs, h, i, v)), R), OLD),
            Nat.add(Nat.add(BX, NEW), R),
            Nat.add(Nat.add(BX, R), NEW),
            Equal.trans(Nat,
              Nat.add(Nat.add(S.suml(cnts_swap_m(xs, h, i, v)), R), OLD),
              Nat.add(Nat.add(S.suml(cnts_swap_m(xs, h, i, v)), OLD), R),
              Nat.add(Nat.add(BX, NEW), R),
              s1, s2),
            s3)),
        Equal.sym(Nat,
          Nat.add(S.suml(S.app(cnts_m(xs), cnts_m(ys))), NEW),
          Nat.add(Nat.add(BX, R), NEW),
          Equal.cong(Nat, Nat, s => Nat.add(s, NEW),
            S.suml(S.app(cnts_m(xs), cnts_m(ys))),
            Nat.add(BX, R), eb)))
    case False{}:
      +h = U32.shr(n)
      +AX = S.suml(cnts_m(xs))
      +BY = S.suml(cnts_m(ys))
      +OLD = R.nfst(cnt_chg_m(ys, h, U32.sub(i, h), v))
      +NEW = R.nsnd(cnt_chg_m(ys, h, U32.sub(i, h), v))
      +ea = S.suml_append(cnts_m(xs), cnts_swap_m(ys, h, U32.sub(i, h), v))
      +eb = S.suml_append(cnts_m(xs), cnts_m(ys))
      +s1 = NatL.n_add_assoc(AX, S.suml(cnts_swap_m(ys, h, U32.sub(i, h), v)), OLD)
      +s2 = Equal.cong(Nat, Nat, x => Nat.add(AX, x),
        Nat.add(S.suml(cnts_swap_m(ys, h, U32.sub(i, h), v)), OLD), Nat.add(BY, NEW), ihy)
      +s3 = NatL.n_add_assoc(AX, BY, NEW)
      Equal.trans(Nat,
        Nat.add(S.suml(S.app(cnts_m(xs), cnts_swap_m(ys, h, U32.sub(i, h), v))), OLD),
        Nat.add(AX, Nat.add(BY, NEW)),
        Nat.add(S.suml(S.app(cnts_m(xs), cnts_m(ys))), NEW),
        Equal.trans(Nat,
          Nat.add(S.suml(S.app(cnts_m(xs), cnts_swap_m(ys, h, U32.sub(i, h), v))), OLD),
          Nat.add(AX, Nat.add(S.suml(cnts_swap_m(ys, h, U32.sub(i, h), v)), OLD)),
          Nat.add(AX, Nat.add(BY, NEW)),
          Equal.trans(Nat,
            Nat.add(S.suml(S.app(cnts_m(xs), cnts_swap_m(ys, h, U32.sub(i, h), v))), OLD),
            Nat.add(Nat.add(AX, S.suml(cnts_swap_m(ys, h, U32.sub(i, h), v))), OLD),
            Nat.add(AX, Nat.add(S.suml(cnts_swap_m(ys, h, U32.sub(i, h), v)), OLD)),
            Equal.cong(Nat, Nat, s => Nat.add(s, OLD),
              S.suml(S.app(cnts_m(xs), cnts_swap_m(ys, h, U32.sub(i, h), v))),
              Nat.add(AX, S.suml(cnts_swap_m(ys, h, U32.sub(i, h), v))), ea),
            s1),
          s2),
        Equal.sym(Nat,
          Nat.add(S.suml(S.app(cnts_m(xs), cnts_m(ys))), NEW),
          Nat.add(AX, Nat.add(BY, NEW)),
          Equal.trans(Nat,
            Nat.add(S.suml(S.app(cnts_m(xs), cnts_m(ys))), NEW),
            Nat.add(Nat.add(AX, BY), NEW),
            Nat.add(AX, Nat.add(BY, NEW)),
            Equal.cong(Nat, Nat, s => Nat.add(s, NEW),
              S.suml(S.app(cnts_m(xs), cnts_m(ys))),
              Nat.add(AX, BY), eb),
            s3)))

def cnt_balance(t: R.PT, +n: U32, +i: U32, +v: U32)
  -> {Nat.add(S.suml(cnts_swap_m(t, n, i, v)), R.nfst(cnt_chg_m(t, n, i, v))) == Nat.add(S.suml(cnts_m(t)), R.nsnd(cnt_chg_m(t, n, i, v))) : Nat}:
  match t:
    case R.PL{+x}:
      Equal.trans(Nat,
        Nat.add(S.suml([nempty(v)]), nempty(x)),
        Nat.add(nempty(v), nempty(x)),
        Nat.add(S.suml([nempty(x)]), nempty(v)),
        Equal.cong(Nat, Nat, s => Nat.add(s, nempty(x)),
          S.suml([nempty(v)]), nempty(v), S.suml1(nempty(v))),
        Equal.trans(Nat,
          Nat.add(nempty(v), nempty(x)),
          Nat.add(nempty(x), nempty(v)),
          Nat.add(S.suml([nempty(x)]), nempty(v)),
          NatL.n_add_comm(nempty(v), nempty(x)),
          Equal.sym(Nat,
            Nat.add(S.suml([nempty(x)]), nempty(v)),
            Nat.add(nempty(x), nempty(v)),
            Equal.cong(Nat, Nat, s => Nat.add(s, nempty(v)),
              S.suml([nempty(x)]), nempty(x), S.suml1(nempty(x))))))
    case R.PN{+xs, +ys}:
      +z = U32.is_lt(i, U32.shr(n))
      cnt_balance_if(xs, ys, n, i, v, z,
        cnt_balance(xs, U32.shr(n), i, v),
        cnt_balance(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v))

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

def array_swap_counts(+t: R.PT, +n: U32, +i: U32, +v: U32)
  -> {to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v))) == cnts_swap_m(t, n, i, v) : +List<Nat>}:
  +ea = Equal.sym(Array<U32>,
    R.pack(R.unpack(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)))),
    R.afst(Array.swap.go(U32, R.pack(t), n, i, v)),
    R.pack_unpack(R.afst(Array.swap.go(U32, R.pack(t), n, i, v))))
  +eb = Equal.cong(R.PT, Array<U32>, t2 => R.pack(t2),
    R.unpack(R.afst(Array.swap.go(U32, R.pack(t), n, i, v))), R.swap_m(t, n, i, v),
    R.swap_ref(t, n, i, v))
  +e1 = Equal.cong(Array<U32>, +List<Nat>, a => to_counts(a),
    R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), R.pack(R.swap_m(t, n, i, v)),
    Equal.trans(Array<U32>,
      R.afst(Array.swap.go(U32, R.pack(t), n, i, v)),
      R.pack(R.unpack(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)))),
      R.pack(R.swap_m(t, n, i, v)),
      ea, eb))
  Equal.trans(+List<Nat>,
    to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v))),
    to_counts(R.pack(R.swap_m(t, n, i, v))),
    cnts_swap_m(t, n, i, v),
    e1,
    Equal.trans(+List<Nat>,
      to_counts(R.pack(R.swap_m(t, n, i, v))),
      cnts_m(R.swap_m(t, n, i, v)),
      cnts_swap_m(t, n, i, v),
      to_counts_pack(R.swap_m(t, n, i, v)),
      cnts_corr(t, n, i, v)))

def array_point_write_count_balance(+t: R.PT, +n: U32, +i: U32, +v: U32)
  -> {Nat.add(S.suml(to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)))), R.nfst(cnt_chg_m(t, n, i, v))) == Nat.add(S.suml(to_counts(R.pack(t))), R.nsnd(cnt_chg_m(t, n, i, v))) : Nat}:
  +e1 = Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
    to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v))),
    cnts_swap_m(t, n, i, v), array_swap_counts(t, n, i, v))
  +e2 = Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
    to_counts(R.pack(t)), cnts_m(t), to_counts_pack(t))
  Equal.trans(Nat,
    Nat.add(S.suml(to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)))), R.nfst(cnt_chg_m(t, n, i, v))),
    Nat.add(S.suml(cnts_swap_m(t, n, i, v)), R.nfst(cnt_chg_m(t, n, i, v))),
    Nat.add(S.suml(to_counts(R.pack(t))), R.nsnd(cnt_chg_m(t, n, i, v))),
    Equal.cong(Nat, Nat, x => Nat.add(x, R.nfst(cnt_chg_m(t, n, i, v))),
      S.suml(to_counts(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)))),
      S.suml(cnts_swap_m(t, n, i, v)), e1),
    Equal.trans(Nat,
      Nat.add(S.suml(cnts_swap_m(t, n, i, v)), R.nfst(cnt_chg_m(t, n, i, v))),
      Nat.add(S.suml(cnts_m(t)), R.nsnd(cnt_chg_m(t, n, i, v))),
      Nat.add(S.suml(to_counts(R.pack(t))), R.nsnd(cnt_chg_m(t, n, i, v))),
      cnt_balance(t, n, i, v),
      Equal.cong(Nat, Nat, x => Nat.add(x, R.nsnd(cnt_chg_m(t, n, i, v))),
        S.suml(cnts_m(t)), S.suml(to_counts(R.pack(t))),
        Equal.sym(Nat, S.suml(to_counts(R.pack(t))), S.suml(cnts_m(t)), e2))))

# ------------------------- instances for the engine's writes -------------------------

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
