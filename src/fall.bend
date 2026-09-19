import Base
import ./refine.bend as R
import ./settle.bend as S
import ./nat.bend as NatL
import ./rules.bend as Rules
import ./writepot.bend as W
import ./tick.bend as T
import ./count.bend as C

# ------------------------------------------------------------------ fall gap
# The `Rules.step` movement (sel 6/12) writes `mov(w)` at the target `j` and the
# old target `gv` at `i`, i.e. it swaps the two leaves' values while keeping the
# two y-levels. Φ is position-sensitive (`pot_at(w, x) = dens(material(w)) *
# iy(x)`), so a *single* swap can raise Φ; only the net over the pair lowers it
# by `(dens(w) − dens(gv)) · (iy(i) − iy(j))`.
#
# The size-free `PT` model blocks the naive projection of `chg_m`'s leaf to
# `base + i` (A.52). The fix is `leaf_base`: the index of the leaf holding `i`,
# which *is* the base `chg_m` uses, so the projection is definitional. The two
# swap balances then telescope into a single cross equation (`mov_cross`).

def leaf_base(t: R.PT, +base: U32, +n: U32, +i: U32) -> U32:
  match t:
    case R.PL{x}:
      base
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      Bool.pick(U32, U32.is_lt(i, h),
        leaf_base(xs, base, h, i),
        leaf_base(ys, U32.add(base, h), h, U32.sub(i, h)))

# `leaf_base` depends only on the tree shape and the index, so a value write
# (which preserves shape) does not move it.
def leaf_base_swap_if(+xs: R.PT, +ys: R.PT, +base: U32, +n: U32, +i: U32, +j: U32, +v: U32, +zj: Bool,
  ihx: {leaf_base(R.swap_m(xs, U32.shr(n), j, v), base, U32.shr(n), i) == leaf_base(xs, base, U32.shr(n), i) : U32},
  ihy: {leaf_base(R.swap_m(ys, U32.shr(n), U32.sub(j, U32.shr(n)), v), U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n))) == leaf_base(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n))) : U32}
) -> {leaf_base(Bool.pick(R.PT, zj,
        R.PN{R.swap_m(xs, U32.shr(n), j, v), ys},
        R.PN{xs, R.swap_m(ys, U32.shr(n), U32.sub(j, U32.shr(n)), v)}), base, n, i)
      == Bool.pick(U32, U32.is_lt(i, U32.shr(n)),
           leaf_base(xs, base, U32.shr(n), i),
           leaf_base(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)))) : U32}:
  match zj:
    case True{}:
      Equal.cong(U32, U32, z => Bool.pick(U32, U32.is_lt(i, U32.shr(n)), z, leaf_base(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)))),
        leaf_base(R.swap_m(xs, U32.shr(n), j, v), base, U32.shr(n), i),
        leaf_base(xs, base, U32.shr(n), i), ihx)
    case False{}:
      Equal.cong(U32, U32, z => Bool.pick(U32, U32.is_lt(i, U32.shr(n)), leaf_base(xs, base, U32.shr(n), i), z),
        leaf_base(R.swap_m(ys, U32.shr(n), U32.sub(j, U32.shr(n)), v), U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n))),
        leaf_base(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n))), ihy)

def leaf_base_swap(t: R.PT, +base: U32, +n: U32, +i: U32, +j: U32, +v: U32)
  -> {leaf_base(R.swap_m(t, n, j, v), base, n, i) == leaf_base(t, base, n, i) : U32}:
  match t:
    case R.PL{x}: {==}
    case R.PN{+xs, +ys}:
      +zj = U32.is_lt(j, U32.shr(n))
      leaf_base_swap_if(xs, ys, base, n, i, j, v, zj,
        leaf_base_swap(xs, base, U32.shr(n), i, j, v),
        leaf_base_swap(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)), U32.sub(j, U32.shr(n)), v))

# The displaced / written potentials of a point write, projected onto the leaf
# `leaf_base` names: this is the A.52 projection, and it is definitional at the
# `PL` leaf (unlike the `base + i` form, which is false there).
def chg_proj_fst_if(+xs: R.PT, +ys: R.PT, +base: U32, +h: U32, +i: U32, +v: U32, +z: Bool,
  ihx: {R.nfst(R.chg_m(xs, base, h, i, v)) == S.pot_at(T.tget(xs, h, i), leaf_base(xs, base, h, i)) : Nat},
  ihy: {R.nfst(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), v)) == S.pot_at(T.tget(ys, h, U32.sub(i, h)), leaf_base(ys, U32.add(base, h), h, U32.sub(i, h))) : Nat}
) -> {R.nfst(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, v),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), v)))
      == S.pot_at(Bool.pick(U32, z, T.tget(xs, h, i), T.tget(ys, h, U32.sub(i, h))),
                  Bool.pick(U32, z, leaf_base(xs, base, h, i), leaf_base(ys, U32.add(base, h), h, U32.sub(i, h)))) : Nat}:
  match z:
    case True{}: ihx
    case False{}: ihy

def chg_proj_fst(t: R.PT, +base: U32, +n: U32, +i: U32, +v: U32)
  -> {R.nfst(R.chg_m(t, base, n, i, v)) == S.pot_at(T.tget(t, n, i), leaf_base(t, base, n, i)) : Nat}:
  match t:
    case R.PL{x}: {==}
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      chg_proj_fst_if(xs, ys, base, h, i, v, z,
        chg_proj_fst(xs, base, h, i, v),
        chg_proj_fst(ys, U32.add(base, h), h, U32.sub(i, h), v))

def chg_proj_snd_if(+xs: R.PT, +ys: R.PT, +base: U32, +h: U32, +i: U32, +v: U32, +z: Bool,
  ihx: {R.nsnd(R.chg_m(xs, base, h, i, v)) == S.pot_at(v, leaf_base(xs, base, h, i)) : Nat},
  ihy: {R.nsnd(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), v)) == S.pot_at(v, leaf_base(ys, U32.add(base, h), h, U32.sub(i, h))) : Nat}
) -> {R.nsnd(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, v),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), v)))
      == S.pot_at(v, Bool.pick(U32, z, leaf_base(xs, base, h, i), leaf_base(ys, U32.add(base, h), h, U32.sub(i, h)))) : Nat}:
  match z:
    case True{}: ihx
    case False{}: ihy

def chg_proj_snd(t: R.PT, +base: U32, +n: U32, +i: U32, +v: U32)
  -> {R.nsnd(R.chg_m(t, base, n, i, v)) == S.pot_at(v, leaf_base(t, base, n, i)) : Nat}:
  match t:
    case R.PL{x}: {==}
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      chg_proj_snd_if(xs, ys, base, h, i, v, z,
        chg_proj_snd(xs, base, h, i, v),
        chg_proj_snd(ys, U32.add(base, h), h, U32.sub(i, h), v))

# One point write's balance, with the leaf potentials named by `leaf_base`: the
# pot sum drops by exactly `new − old` at that leaf.
def swap_balance(+t: R.PT, +base: U32, +n: U32, +i: U32, +v: U32)
  -> {Nat.add(S.suml(R.pots_m(R.swap_m(t, n, i, v), base, n)), S.pot_at(T.tget(t, n, i), leaf_base(t, base, n, i)))
      == Nat.add(S.suml(R.pots_m(t, base, n)), S.pot_at(v, leaf_base(t, base, n, i))) : Nat}:
  +A2 = S.suml(R.pots_m(R.swap_m(t, n, i, v), base, n))
  +A1 = S.suml(R.pots_swap_m(t, base, n, i, v))
  +LP = S.pot_at(T.tget(t, n, i), leaf_base(t, base, n, i))
  +OLD = R.nfst(R.chg_m(t, base, n, i, v))
  +B = S.suml(R.pots_m(t, base, n))
  +NEW = R.nsnd(R.chg_m(t, base, n, i, v))
  +NP = S.pot_at(v, leaf_base(t, base, n, i))
  +e1 = Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
    R.pots_m(R.swap_m(t, n, i, v), base, n), R.pots_swap_m(t, base, n, i, v),
    R.pots_corr(t, base, n, i, v))
  +e2 = Equal.sym(Nat, OLD, LP, chg_proj_fst(t, base, n, i, v))
  +e3 = chg_proj_snd(t, base, n, i, v)
  +dec = R.dec(t, base, n, i, v)
  +eab = Equal.trans(Nat,
    Nat.add(A2, LP), Nat.add(A1, LP), Nat.add(A1, OLD),
    Equal.cong(Nat, Nat, x => Nat.add(x, LP), A2, A1, e1),
    Equal.cong(Nat, Nat, y => Nat.add(A1, y), LP, OLD, e2))
  +ec = Equal.cong(Nat, Nat, y => Nat.add(B, y), NEW, NP, e3)
  Equal.trans(Nat,
    Nat.add(A2, LP),
    Nat.add(A1, OLD),
    Nat.add(B, NP),
    eab,
    Equal.trans(Nat, Nat.add(A1, OLD), Nat.add(B, NEW), Nat.add(B, NP), dec, ec))

# Reading `i` after the swap at `j` gives the same potential: either the write
# missed `i` (i ≠ j) or it wrote `mov(w)`, whose material is `w`'s.
def pot_swap_if(
  +xs: R.PT, +ys: R.PT, +base: U32, +n: U32, +i: U32, +j: U32, +zj: Bool, +zi: Bool,
  ihx: {S.pot_at(T.tget(R.swap_m(xs, U32.shr(n), j, Rules.mov(T.tget(xs, U32.shr(n), i))), U32.shr(n), i), base) == S.pot_at(T.tget(xs, U32.shr(n), i), base) : Nat},
  ihy: {S.pot_at(T.tget(R.swap_m(ys, U32.shr(n), U32.sub(j, U32.shr(n)), Rules.mov(T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n))))), U32.shr(n), U32.sub(i, U32.shr(n))), base) == S.pot_at(T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n))), base) : Nat}
) -> {S.pot_at(Bool.pick(U32, zj,
        Bool.pick(U32, zi, T.tget(R.swap_m(xs, U32.shr(n), j, Rules.mov(Bool.pick(U32, zi, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))))), U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))),
        Bool.pick(U32, zi, T.tget(xs, U32.shr(n), i), T.tget(R.swap_m(ys, U32.shr(n), U32.sub(j, U32.shr(n)), Rules.mov(Bool.pick(U32, zi, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))))), U32.shr(n), U32.sub(i, U32.shr(n))))), base)
     == S.pot_at(Bool.pick(U32, zi, T.tget(xs, U32.shr(n), i), T.tget(ys, U32.shr(n), U32.sub(i, U32.shr(n)))), base) : Nat}:
  match zj:
    case True{}:
      match zi:
        case True{}: ihx
        case False{}: {==}
    case False{}:
      match zi:
        case True{}: {==}
        case False{}: ihy

def pot_swap(t: R.PT, +base: U32, +n: U32, +i: U32, +j: U32)
  -> {S.pot_at(T.tget(R.swap_m(t, n, j, Rules.mov(T.tget(t, n, i))), n, i), base) == S.pot_at(T.tget(t, n, i), base) : Nat}:
  match t:
    case R.PL{x}:
      W.pot_mov(x, base)
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +zj = U32.is_lt(j, h)
      +zi = U32.is_lt(i, h)
      +w = Bool.pick(U32, zi, T.tget(xs, h, i), T.tget(ys, h, U32.sub(i, h)))
      +A = R.swap_m(xs, h, j, Rules.mov(w))
      +B = R.swap_m(ys, h, U32.sub(j, h), Rules.mov(w))
      +tp = C.tget_pick(zj, R.PN{A, ys}, R.PN{xs, B}, n, i)
      +hh = pot_swap_if(xs, ys, base, n, i, j, zj, zi,
        pot_swap(xs, base, h, i, j),
        pot_swap(ys, base, h, U32.sub(i, h), U32.sub(j, h)))
      +ceq = Equal.cong(U32, Nat, w2 => S.pot_at(w2, base),
        T.tget(R.swap_m(R.PN{xs, ys}, n, j, Rules.mov(T.tget(R.PN{xs, ys}, n, i))), n, i),
        Bool.pick(U32, zj,
          Bool.pick(U32, zi, T.tget(A, h, i), T.tget(ys, h, U32.sub(i, h))),
          Bool.pick(U32, zi, T.tget(xs, h, i), T.tget(B, h, U32.sub(i, h)))),
        tp)
      Equal.trans(Nat,
        S.pot_at(T.tget(R.swap_m(R.PN{xs, ys}, n, j, Rules.mov(T.tget(R.PN{xs, ys}, n, i))), n, i), base),
        S.pot_at(Bool.pick(U32, zj,
          Bool.pick(U32, zi, T.tget(A, h, i), T.tget(ys, h, U32.sub(i, h))),
          Bool.pick(U32, zi, T.tget(xs, h, i), T.tget(B, h, U32.sub(i, h)))), base),
        S.pot_at(T.tget(R.PN{xs, ys}, n, i), base),
        ceq, hh)

def leaf_pot_swap_mov(+t: R.PT, +base: U32, +n: U32, +i: U32, +j: U32)
  -> {S.pot_at(T.tget(R.swap_m(t, n, j, Rules.mov(T.tget(t, n, i))), n, i),
               leaf_base(R.swap_m(t, n, j, Rules.mov(T.tget(t, n, i))), base, n, i))
      == S.pot_at(T.tget(t, n, i), leaf_base(t, base, n, i)) : Nat}:
  +t1 = R.swap_m(t, n, j, Rules.mov(T.tget(t, n, i)))
  +li = leaf_base(t, base, n, i)
  +hlb = leaf_base_swap(t, base, n, i, j, Rules.mov(T.tget(t, n, i)))
  +e1 = Equal.cong(U32, Nat, L => S.pot_at(T.tget(t1, n, i), L), leaf_base(t1, base, n, i), li, hlb)
  +e2 = pot_swap(t, li, n, i, j)
  Equal.trans(Nat,
    S.pot_at(T.tget(t1, n, i), leaf_base(t1, base, n, i)),
    S.pot_at(T.tget(t1, n, i), li),
    S.pot_at(T.tget(t, n, i), li),
    e1, e2)

def mov_m(+t: R.PT, +n: U32, +i: U32, +j: U32) -> R.PT:
  R.swap_m(R.swap_m(t, n, j, Rules.mov(T.tget(t, n, i))), n, i, T.tget(t, n, j))

# The telescope: the two writes' balances cancel into one cross equation. The
# left cross term (`p + q`) is the pre-move potential at the two leaves; the
# right (`r + s`) is the post-move potential there.
def mov_cross(+t: R.PT, +base: U32, +n: U32, +i: U32, +j: U32)
  -> {Nat.add(S.suml(R.pots_m(mov_m(t, n, i, j), base, n)),
             Nat.add(S.pot_at(T.tget(t, n, i), leaf_base(t, base, n, i)),
                     S.pot_at(T.tget(t, n, j), leaf_base(t, base, n, j))))
      == Nat.add(S.suml(R.pots_m(t, base, n)),
             Nat.add(S.pot_at(T.tget(t, n, j), leaf_base(t, base, n, i)),
                     S.pot_at(T.tget(t, n, i), leaf_base(t, base, n, j)))) : Nat}:
  +wi = T.tget(t, n, i)
  +wj = T.tget(t, n, j)
  +t1 = R.swap_m(t, n, j, Rules.mov(wi))
  +t2 = R.swap_m(t1, n, i, wj)
  +li = leaf_base(t, base, n, i)
  +lj = leaf_base(t, base, n, j)
  +A2 = S.suml(R.pots_m(t2, base, n))
  +A1 = S.suml(R.pots_m(t1, base, n))
  +A0 = S.suml(R.pots_m(t, base, n))
  +p = S.pot_at(wi, li)
  +q = S.pot_at(wj, lj)
  +r = S.pot_at(wj, li)
  +s = S.pot_at(wi, lj)
  +lp1 = S.pot_at(T.tget(t1, n, i), leaf_base(t1, base, n, i))
  +b1 = swap_balance(t, base, n, j, Rules.mov(wi))
  +pm = W.pot_mov(wi, lj)
  +b1b = Equal.trans(Nat,
    Nat.add(A1, q),
    Nat.add(A0, S.pot_at(Rules.mov(wi), lj)),
    Nat.add(A0, s),
    b1,
    Equal.cong(Nat, Nat, x => Nat.add(A0, x), S.pot_at(Rules.mov(wi), lj), s, pm))
  +b2 = swap_balance(t1, base, n, i, wj)
  +lpt = leaf_pot_swap_mov(t, base, n, i, j)
  +hlb = leaf_base_swap(t, base, n, i, j, Rules.mov(wi))
  +npc = Equal.cong(U32, Nat, L => S.pot_at(wj, L), leaf_base(t1, base, n, i), li, hlb)
  +b2b = Equal.trans(Nat,
    Nat.add(A2, p),
    Nat.add(A2, lp1),
    Nat.add(A1, r),
    Equal.sym(Nat, Nat.add(A2, lp1), Nat.add(A2, p),
      Equal.cong(Nat, Nat, x => Nat.add(A2, x), lp1, p, lpt)),
    Equal.trans(Nat,
      Nat.add(A2, lp1),
      Nat.add(A1, S.pot_at(wj, leaf_base(t1, base, n, i))),
      Nat.add(A1, r),
      b2,
      Equal.cong(Nat, Nat, x => Nat.add(A1, x), S.pot_at(wj, leaf_base(t1, base, n, i)), r, npc)))
  Equal.trans(Nat,
    Nat.add(A2, Nat.add(p, q)),
    Nat.add(Nat.add(A2, p), q),
    Nat.add(A0, Nat.add(r, s)),
    Equal.sym(Nat, Nat.add(Nat.add(A2, p), q), Nat.add(A2, Nat.add(p, q)), NatL.n_add_assoc(A2, p, q)),
    Equal.trans(Nat,
      Nat.add(Nat.add(A2, p), q),
      Nat.add(Nat.add(A1, r), q),
      Nat.add(A0, Nat.add(r, s)),
      Equal.cong(Nat, Nat, x => Nat.add(x, q), Nat.add(A2, p), Nat.add(A1, r), b2b),
      Equal.trans(Nat,
        Nat.add(Nat.add(A1, r), q),
        Nat.add(Nat.add(A1, q), r),
        Nat.add(A0, Nat.add(r, s)),
        S.swap_add(A1, r, q),
        Equal.trans(Nat,
          Nat.add(Nat.add(A1, q), r),
          Nat.add(Nat.add(A0, s), r),
          Nat.add(A0, Nat.add(r, s)),
          Equal.cong(Nat, Nat, x => Nat.add(x, r), Nat.add(A1, q), Nat.add(A0, s), b1b),
          Equal.trans(Nat,
            Nat.add(Nat.add(A0, s), r),
            Nat.add(A0, Nat.add(s, r)),
            Nat.add(A0, Nat.add(r, s)),
            NatL.n_add_assoc(A0, s, r),
            Equal.cong(Nat, Nat, x => Nat.add(A0, x), Nat.add(s, r), Nat.add(r, s), NatL.n_add_comm(s, r)))))))

# The two cross terms named: `mov_S` is the pre-move potential of the source and
# target leaves, `mov_T` the post-move potential (source at the target's level
# and target at the source's). Their difference is the fall gap.
def mov_S(+t: R.PT, +base: U32, +n: U32, +i: U32, +j: U32) -> Nat:
  Nat.add(S.pot_at(T.tget(t, n, i), leaf_base(t, base, n, i)),
          S.pot_at(T.tget(t, n, j), leaf_base(t, base, n, j)))

def mov_T(+t: R.PT, +base: U32, +n: U32, +i: U32, +j: U32) -> Nat:
  Nat.add(S.pot_at(T.tget(t, n, j), leaf_base(t, base, n, i)),
          S.pot_at(T.tget(t, n, i), leaf_base(t, base, n, j)))

def fall_gap(+t: R.PT, +base: U32, +n: U32, +i: U32, +j: U32) -> Nat:
  Nat.sub(mov_S(t, base, n, i, j), mov_T(t, base, n, i, j))

def mov_array(+t: R.PT, +n: U32, +i: U32, +j: U32) -> Array<U32>:
  R.afst(Array.swap.go(U32,
    R.afst(Array.swap.go(U32, R.pack(t), n, j, Rules.mov(T.tget(t, n, i)))),
    n, i, T.tget(t, n, j)))

# The array-level telescope: `mov_cross` transported across
# `pack(swap_m(..)) == afst(Array.swap.go(..))` (the two-write composition).
def array_mov_cross(+t: R.PT, +base: U32, +n: U32, +i: U32, +j: U32)
  -> {Nat.add(S.suml(S.to_pots(mov_array(t, n, i, j), base, n)), mov_S(t, base, n, i, j))
      == Nat.add(S.suml(S.to_pots(R.pack(t), base, n)), mov_T(t, base, n, i, j)) : Nat}:
  +wi = T.tget(t, n, i)
  +wj = T.tget(t, n, j)
  +t1 = R.swap_m(t, n, j, Rules.mov(wi))
  +t2 = R.swap_m(t1, n, i, wj)
  +a2eq = Equal.trans(Array<U32>,
    R.afst(Array.swap.go(U32, R.afst(Array.swap.go(U32, R.pack(t), n, j, Rules.mov(wi))), n, i, wj)),
    R.afst(Array.swap.go(U32, R.pack(t1), n, i, wj)),
    R.pack(t2),
    Equal.cong(Array<U32>, Array<U32>, a => R.afst(Array.swap.go(U32, a, n, i, wj)),
      R.afst(Array.swap.go(U32, R.pack(t), n, j, Rules.mov(wi))), R.pack(t1),
      C.afst_swap_m(t, n, j, Rules.mov(wi))),
    C.afst_swap_m(t1, n, i, wj))
  +lhs = Equal.trans(List<&2, Nat>,
    S.to_pots(R.afst(Array.swap.go(U32, R.afst(Array.swap.go(U32, R.pack(t), n, j, Rules.mov(wi))), n, i, wj)), base, n),
    S.to_pots(R.pack(t2), base, n),
    R.pots_m(t2, base, n),
    Equal.cong(Array<U32>, List<&2, Nat>, a => S.to_pots(a, base, n),
      R.afst(Array.swap.go(U32, R.afst(Array.swap.go(U32, R.pack(t), n, j, Rules.mov(wi))), n, i, wj)),
      R.pack(t2), a2eq),
    R.to_pots_pack(t2, base, n))
  +rhs = R.to_pots_pack(t, base, n)
  +mc = mov_cross(t, base, n, i, j)
  Equal.trans(Nat,
    Nat.add(S.suml(S.to_pots(mov_array(t, n, i, j), base, n)), mov_S(t, base, n, i, j)),
    Nat.add(S.suml(R.pots_m(t2, base, n)), mov_S(t, base, n, i, j)),
    Nat.add(S.suml(S.to_pots(R.pack(t), base, n)), mov_T(t, base, n, i, j)),
    Equal.cong(Nat, Nat, x => Nat.add(x, mov_S(t, base, n, i, j)),
      S.suml(S.to_pots(mov_array(t, n, i, j), base, n)),
      S.suml(R.pots_m(t2, base, n)),
      Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
        S.to_pots(mov_array(t, n, i, j), base, n),
        R.pots_m(t2, base, n), lhs)),
    Equal.trans(Nat,
      Nat.add(S.suml(R.pots_m(t2, base, n)), mov_S(t, base, n, i, j)),
      Nat.add(S.suml(R.pots_m(t, base, n)), mov_T(t, base, n, i, j)),
      Nat.add(S.suml(S.to_pots(R.pack(t), base, n)), mov_T(t, base, n, i, j)),
      mc,
      Equal.cong(Nat, Nat, x => Nat.add(x, mov_T(t, base, n, i, j)),
        S.suml(R.pots_m(t, base, n)),
        S.suml(S.to_pots(R.pack(t), base, n)),
        Equal.sym(Nat, S.suml(S.to_pots(R.pack(t), base, n)), S.suml(R.pots_m(t, base, n)),
          Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
            S.to_pots(R.pack(t), base, n), R.pots_m(t, base, n), rhs)))))

# The decrease law: whenever the move shifts the two leaves' potentials by a net
# `fall_gap` (`mov_T + fall_gap == mov_S`), Φ drops by exactly `fall_gap`.
def array_mov_lowers_phi(+t: R.PT, +base: U32, +n: U32, +i: U32, +j: U32,
  hg: {Nat.add(mov_T(t, base, n, i, j), fall_gap(t, base, n, i, j)) == mov_S(t, base, n, i, j) : Nat})
  -> {Nat.add(S.suml(S.to_pots(mov_array(t, n, i, j), base, n)), fall_gap(t, base, n, i, j)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  +Phi2 = S.suml(S.to_pots(mov_array(t, n, i, j), base, n))
  +Phi0 = S.suml(S.to_pots(R.pack(t), base, n))
  +g = fall_gap(t, base, n, i, j)
  +TT = mov_T(t, base, n, i, j)
  +SS = mov_S(t, base, n, i, j)
  +cross = array_mov_cross(t, base, n, i, j)
  +eq1 = NatL.n_add_assoc(Phi2, g, TT)
  +eq2 = Equal.cong(Nat, Nat, x => Nat.add(Phi2, x), Nat.add(g, TT), Nat.add(TT, g), NatL.n_add_comm(g, TT))
  +eq3 = Equal.cong(Nat, Nat, x => Nat.add(Phi2, x), Nat.add(TT, g), SS, hg)
  +step = Equal.trans(Nat, Nat.add(Nat.add(Phi2, g), TT), Nat.add(Phi2, Nat.add(g, TT)), Nat.add(Phi0, TT),
    eq1,
    Equal.trans(Nat, Nat.add(Phi2, Nat.add(g, TT)), Nat.add(Phi2, Nat.add(TT, g)), Nat.add(Phi0, TT),
      eq2,
      Equal.trans(Nat, Nat.add(Phi2, Nat.add(TT, g)), Nat.add(Phi2, SS), Nat.add(Phi0, TT), eq3, cross)))
  NatL.n_add_cancel_right(Nat.add(Phi2, g), Phi0, TT, step)
