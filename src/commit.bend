import Base
import ./refine.bend as R

# ------------------------------------------------------------------ V3c-1
# Schedule invariance, the algebraic core: point writes at *distinct* indices
# commute.
#
# `Rules.plan` is a pure function of the pre-phase state (V0-1, A.63), so each
# evaluated cell decides its writes from the same `world` regardless of what any
# other cell does. What is left for "a region-split fold equals the sequential
# fold" is therefore not a read/write ordering argument any more — it is that
# *applying* the merged write set is order-independent. That holds exactly when
# no two writes target the same cell. This module proves the algebraic fact:
#
#   swap_m (swap_m t n i v) n j w  =  swap_m (swap_m t n j w) n i v
#
# for two writes at distinct leaves `i != j` of the `2^n`-leaf tree `t`
# (over `Refine.PT`, the presentation `Refine.swap_m` refines `Array.set`).
#
# The distinctness hypothesis is `ne_idx`, a computable predicate that mirrors
# `swap_m`'s own top-down walk: it returns `True` when the two indices split into
# different subtrees at some level and `False` at a leaf (where every index
# collides). Encoding distinctness as the *shape of the recursion* is what makes
# the induction go through without any `U32` arithmetic: at each node the
# predicate reduces to the child's predicate, so the induction hypothesis
# applies verbatim.
#
# Why `set_m_if`. `Refine.swap_m` recomputes its left/right decision
# `U32.is_lt(i, U32.shr(n))` internally, so a composition of two `swap_m`s is
# stuck on a `Bool.pick` whose scrutinee is a *term*, never the variable a
# `match` introduces. `set_m_if` takes that decision as a parameter and mirrors
# `swap_m` exactly (`swap_m_eq_set_m`), so the proof can match on the parameter
# and every nested pick reduces. `set_m_if_pick` pushes a `set_m_if` past a
# `Bool.pick`, which is what lets a write be applied to the (stuck) result of the
# previous write.
#
# Scope (bounded fragment). This is the single-write commutation kernel — the
# load-bearing algebraic fact. The list/region layer that folds it over a
# `List<Write>` and states the region-split equality is the next step (V3c-1b);
# the refinement of `ne_idx` to the engine's `U32.is_eq(i, j) == False` needs the
# `U32` order/subtraction arithmetic and is recorded as an open residual in
# `PLAN.md` §5.3 (`G3`).

# The left/right decision at a node of size `h` is taken from the *child's*
# size: `swap_m` at a node of size `n` decides with `U32.is_lt(i, U32.shr(n))`,
# and recurses to a child of size `U32.shr(n)`, whose own decision is
# `U32.is_lt(i, U32.shr(U32.shr(n)))`. `set_m_if` reproduces that walk with the
# current decision supplied as `z`.
def set_m_if(t: R.PT, n: U32, +i: U32, +v: U32, +z: Bool) -> R.PT:
  match t:
    case R.PL{x}:
      R.PL{v}
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +hh = U32.shr(h)
      Bool.pick(R.PT, z,
        R.PN{set_m_if(xs, h, i, v, U32.is_lt(i, hh)), ys},
        R.PN{xs, set_m_if(ys, h, U32.sub(i, h), v, U32.is_lt(U32.sub(i, h), hh))})

# Push a write past the `Bool.pick` a previous write leaves behind: the pick's
# decision is independent of the write, so it distributes.
def set_m_if_pick(A: R.PT, B: R.PT, n: U32, +i: U32, +v: U32, +zt: Bool, +z: Bool)
  -> {set_m_if(Bool.pick(R.PT, zt, A, B), n, i, v, z) == Bool.pick(R.PT, zt, set_m_if(A, n, i, v, z), set_m_if(B, n, i, v, z)) : R.PT}:
  match zt:
    case True{}: {==}
    case False{}: {==}

# ------------------------------------------------------------------ ne_idx
# `ne_idx(t, n, i, j)` is the distinctness predicate. `ne_idx_if` is the
# decision-table form (so the node's two branch Bools are matchable parameters);
# `ne_idx` instantiates it with the same `is_lt` walk `swap_m`/`set_m_if` use.
#
#   split at this node              -> True
#   both go left  -> recurse left
#   both go right -> recurse right
#   leaf (no split possible)        -> False
#
# For a full tree with in-range indices this is exactly `i != j`; the connection
# to `U32.is_eq` is the documented residual (it needs `U32` arithmetic).
def ne_idx_if(nzi: Bool, nzj: Bool, +zj: Bool, +zi: Bool) -> Bool:
  Bool.pick(Bool, zi,
    Bool.pick(Bool, zj, nzi, True{}),
    Bool.pick(Bool, zj, True{}, nzj))

def ne_idx(t: R.PT, n: U32, +i: U32, +j: U32) -> Bool:
  match t:
    case R.PL{x}:
      False{}
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      ne_idx_if(ne_idx(xs, h, i, j), ne_idx(ys, h, U32.sub(i, h), U32.sub(j, h)),
        U32.is_lt(j, h), U32.is_lt(i, h))

# The commutativity induction. `set_m_comm_if` is the `PN` case, with the two
# node decisions and the (fixed) child hypotheses passed in: `match zj`/`match zi`
# then reduces every `Bool.pick`, and the four cases are IH-left, refl, refl,
# IH-right.
def set_m_comm_if(
  +xs: R.PT, +ys: R.PT, +n: U32, +i: U32, +j: U32, +v: U32, +w: U32,
  +zj: Bool, +zi: Bool,
  ihx: {ne_idx(xs, U32.shr(n), i, j) == True{} : Bool} ->
    {set_m_if(set_m_if(xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))), U32.shr(n), j, w, U32.is_lt(j, U32.shr(U32.shr(n)))) == set_m_if(set_m_if(xs, U32.shr(n), j, w, U32.is_lt(j, U32.shr(U32.shr(n)))), U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))) : R.PT},
  ihy: {ne_idx(ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.sub(j, U32.shr(n))) == True{} : Bool} ->
    {set_m_if(set_m_if(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), U32.shr(n), U32.sub(j, U32.shr(n)), w, U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n)))) == set_m_if(set_m_if(ys, U32.shr(n), U32.sub(j, U32.shr(n)), w, U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n)))), U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))) : R.PT},
  hne: {ne_idx_if(ne_idx(xs, U32.shr(n), i, j), ne_idx(ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.sub(j, U32.shr(n))), zj, zi) == True{} : Bool}
) -> {Bool.pick(R.PT, zi,
        set_m_if(R.PN{set_m_if(xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))), ys}, n, j, w, zj),
        set_m_if(R.PN{xs, set_m_if(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))}, n, j, w, zj))
      == Bool.pick(R.PT, zj,
        set_m_if(R.PN{set_m_if(xs, U32.shr(n), j, w, U32.is_lt(j, U32.shr(U32.shr(n)))), ys}, n, i, v, zi),
        set_m_if(R.PN{xs, set_m_if(ys, U32.shr(n), U32.sub(j, U32.shr(n)), w, U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n))))}, n, i, v, zi)) : R.PT}:
  match zj:
    case True{}:
      match zi:
        case True{}:
          Equal.cong(R.PT, R.PT, x => R.PN{x, ys},
            set_m_if(set_m_if(xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))), U32.shr(n), j, w, U32.is_lt(j, U32.shr(U32.shr(n)))),
            set_m_if(set_m_if(xs, U32.shr(n), j, w, U32.is_lt(j, U32.shr(U32.shr(n)))), U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n)))),
            ihx(hne))
        case False{}:
          {==}
    case False{}:
      match zi:
        case True{}:
          {==}
        case False{}:
          Equal.cong(R.PT, R.PT, y => R.PN{xs, y},
            set_m_if(set_m_if(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))), U32.shr(n), U32.sub(j, U32.shr(n)), w, U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n)))),
            set_m_if(set_m_if(ys, U32.shr(n), U32.sub(j, U32.shr(n)), w, U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n)))), U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n)))),
            ihy(hne))

def set_m_comm(
  +t: R.PT, +n: U32, +i: U32, +j: U32, +v: U32, +w: U32,
  +hne: {ne_idx(t, n, i, j) == True{} : Bool}
) -> {set_m_if(set_m_if(t, n, i, v, U32.is_lt(i, U32.shr(n))), n, j, w, U32.is_lt(j, U32.shr(n))) == set_m_if(set_m_if(t, n, j, w, U32.is_lt(j, U32.shr(n))), n, i, v, U32.is_lt(i, U32.shr(n))) : R.PT}:
  match t:
    case R.PL{x}:
      # At a leaf every index names the same cell, so `ne_idx` is `False` and the
      # hypothesis is `{False == True}`; `Bool.pick` turns it into the goal.
      Equal.cong(Bool, R.PT, b => Bool.pick(R.PT, b, R.PL{v}, R.PL{w}), False{}, True{}, hne)
    case R.PN{+xs, +ys}:
      +X = set_m_if(xs, U32.shr(n), i, v, U32.is_lt(i, U32.shr(U32.shr(n))))
      +Y = set_m_if(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v, U32.is_lt(U32.sub(i, U32.shr(n)), U32.shr(U32.shr(n))))
      +Xp = set_m_if(xs, U32.shr(n), j, w, U32.is_lt(j, U32.shr(U32.shr(n))))
      +Yp = set_m_if(ys, U32.shr(n), U32.sub(j, U32.shr(n)), w, U32.is_lt(U32.sub(j, U32.shr(n)), U32.shr(U32.shr(n))))
      +eL = set_m_if_pick(R.PN{X, ys}, R.PN{xs, Y}, n, j, w, U32.is_lt(i, U32.shr(n)), U32.is_lt(j, U32.shr(n)))
      +eR = set_m_if_pick(R.PN{Xp, ys}, R.PN{xs, Yp}, n, i, v, U32.is_lt(j, U32.shr(n)), U32.is_lt(i, U32.shr(n)))
      Equal.trans(R.PT,
        set_m_if(set_m_if(R.PN{xs, ys}, n, i, v, U32.is_lt(i, U32.shr(n))), n, j, w, U32.is_lt(j, U32.shr(n))),
        Bool.pick(R.PT, U32.is_lt(i, U32.shr(n)), set_m_if(R.PN{X, ys}, n, j, w, U32.is_lt(j, U32.shr(n))), set_m_if(R.PN{xs, Y}, n, j, w, U32.is_lt(j, U32.shr(n)))),
        set_m_if(set_m_if(R.PN{xs, ys}, n, j, w, U32.is_lt(j, U32.shr(n))), n, i, v, U32.is_lt(i, U32.shr(n))),
        eL,
        Equal.trans(R.PT,
          Bool.pick(R.PT, U32.is_lt(i, U32.shr(n)), set_m_if(R.PN{X, ys}, n, j, w, U32.is_lt(j, U32.shr(n))), set_m_if(R.PN{xs, Y}, n, j, w, U32.is_lt(j, U32.shr(n)))),
          Bool.pick(R.PT, U32.is_lt(j, U32.shr(n)), set_m_if(R.PN{Xp, ys}, n, i, v, U32.is_lt(i, U32.shr(n))), set_m_if(R.PN{xs, Yp}, n, i, v, U32.is_lt(i, U32.shr(n)))),
          set_m_if(set_m_if(R.PN{xs, ys}, n, j, w, U32.is_lt(j, U32.shr(n))), n, i, v, U32.is_lt(i, U32.shr(n))),
          set_m_comm_if(xs, ys, n, i, j, v, w, U32.is_lt(j, U32.shr(n)), U32.is_lt(i, U32.shr(n)),
            hh => set_m_comm(xs, U32.shr(n), i, j, v, w, hh),
            hh => set_m_comm(ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.sub(j, U32.shr(n)), v, w, hh),
            hne),
          Equal.sym(R.PT,
            set_m_if(set_m_if(R.PN{xs, ys}, n, j, w, U32.is_lt(j, U32.shr(n))), n, i, v, U32.is_lt(i, U32.shr(n))),
            Bool.pick(R.PT, U32.is_lt(j, U32.shr(n)), set_m_if(R.PN{Xp, ys}, n, i, v, U32.is_lt(i, U32.shr(n))), set_m_if(R.PN{xs, Yp}, n, i, v, U32.is_lt(i, U32.shr(n)))),
            eR)))

# `set_m_if` with the natural decision is `swap_m` (definitional by induction).
def swap_m_eq_set_m(+t: R.PT, +n: U32, +i: U32, +v: U32)
  -> {R.swap_m(t, n, i, v) == set_m_if(t, n, i, v, U32.is_lt(i, U32.shr(n))) : R.PT}:
  match t:
    case R.PL{x}:
      {==}
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      Equal.trans(R.PT,
        R.swap_m(R.PN{xs, ys}, n, i, v),
        Bool.pick(R.PT, U32.is_lt(i, h),
          R.PN{R.swap_m(xs, h, i, v), ys},
          R.PN{xs, R.swap_m(ys, h, U32.sub(i, h), v)}),
        set_m_if(R.PN{xs, ys}, n, i, v, U32.is_lt(i, U32.shr(n))),
        {==},
        Equal.trans(R.PT,
          Bool.pick(R.PT, U32.is_lt(i, h),
            R.PN{R.swap_m(xs, h, i, v), ys},
            R.PN{xs, R.swap_m(ys, h, U32.sub(i, h), v)}),
          Bool.pick(R.PT, U32.is_lt(i, h),
            R.PN{set_m_if(xs, h, i, v, U32.is_lt(i, U32.shr(h))), ys},
            R.PN{xs, set_m_if(ys, h, U32.sub(i, h), v, U32.is_lt(U32.sub(i, h), U32.shr(h)))}),
          set_m_if(R.PN{xs, ys}, n, i, v, U32.is_lt(i, U32.shr(n))),
          Equal.trans(R.PT,
            Bool.pick(R.PT, U32.is_lt(i, h),
              R.PN{R.swap_m(xs, h, i, v), ys},
              R.PN{xs, R.swap_m(ys, h, U32.sub(i, h), v)}),
            Bool.pick(R.PT, U32.is_lt(i, h),
              R.PN{set_m_if(xs, h, i, v, U32.is_lt(i, U32.shr(h))), ys},
              R.PN{xs, R.swap_m(ys, h, U32.sub(i, h), v)}),
            Bool.pick(R.PT, U32.is_lt(i, h),
              R.PN{set_m_if(xs, h, i, v, U32.is_lt(i, U32.shr(h))), ys},
              R.PN{xs, set_m_if(ys, h, U32.sub(i, h), v, U32.is_lt(U32.sub(i, h), U32.shr(h)))}),
            Equal.cong(R.PT, R.PT,
              x => Bool.pick(R.PT, U32.is_lt(i, h), x, R.PN{xs, R.swap_m(ys, h, U32.sub(i, h), v)}),
              R.PN{R.swap_m(xs, h, i, v), ys},
              R.PN{set_m_if(xs, h, i, v, U32.is_lt(i, U32.shr(h))), ys},
              Equal.cong(R.PT, R.PT, x => R.PN{x, ys}, R.swap_m(xs, h, i, v), set_m_if(xs, h, i, v, U32.is_lt(i, U32.shr(h))), swap_m_eq_set_m(xs, h, i, v))),
            Equal.cong(R.PT, R.PT,
              x => Bool.pick(R.PT, U32.is_lt(i, h), R.PN{set_m_if(xs, h, i, v, U32.is_lt(i, U32.shr(h))), ys}, x),
              R.PN{xs, R.swap_m(ys, h, U32.sub(i, h), v)},
              R.PN{xs, set_m_if(ys, h, U32.sub(i, h), v, U32.is_lt(U32.sub(i, h), U32.shr(h)))},
              Equal.cong(R.PT, R.PT, x => R.PN{xs, x}, R.swap_m(ys, h, U32.sub(i, h), v), set_m_if(ys, h, U32.sub(i, h), v, U32.is_lt(U32.sub(i, h), U32.shr(h))), swap_m_eq_set_m(ys, h, U32.sub(i, h), v)))),
          {==}))

# The V3c-1 kernel, stated on the engine-facing `Refine.swap_m`: two point
# writes at distinct leaves commute.
def swap_m_comm(
  +t: R.PT, +n: U32, +i: U32, +j: U32, +v: U32, +w: U32,
  +hne: {ne_idx(t, n, i, j) == True{} : Bool}
) -> {R.swap_m(R.swap_m(t, n, i, v), n, j, w) == R.swap_m(R.swap_m(t, n, j, w), n, i, v) : R.PT}:
  +zi = U32.is_lt(i, U32.shr(n))
  +zj = U32.is_lt(j, U32.shr(n))
  +A = set_m_if(t, n, i, v, zi)
  +B = set_m_if(t, n, j, w, zj)
  +e1 = swap_m_eq_set_m(t, n, i, v)
  +e2 = swap_m_eq_set_m(t, n, j, w)
  +eA = swap_m_eq_set_m(A, n, j, w)
  +eB = swap_m_eq_set_m(B, n, i, v)
  Equal.trans(R.PT,
    R.swap_m(R.swap_m(t, n, i, v), n, j, w),
    R.swap_m(A, n, j, w),
    R.swap_m(R.swap_m(t, n, j, w), n, i, v),
    Equal.cong(R.PT, R.PT, x => R.swap_m(x, n, j, w), R.swap_m(t, n, i, v), A, e1),
    Equal.trans(R.PT,
      R.swap_m(A, n, j, w),
      set_m_if(A, n, j, w, zj),
      R.swap_m(R.swap_m(t, n, j, w), n, i, v),
      eA,
      Equal.trans(R.PT,
        set_m_if(A, n, j, w, zj),
        set_m_if(B, n, i, v, zi),
        R.swap_m(R.swap_m(t, n, j, w), n, i, v),
        set_m_comm(t, n, i, j, v, w, hne),
        Equal.sym(R.PT,
          R.swap_m(R.swap_m(t, n, j, w), n, i, v),
          set_m_if(B, n, i, v, zi),
          Equal.trans(R.PT,
            R.swap_m(R.swap_m(t, n, j, w), n, i, v),
            R.swap_m(B, n, i, v),
            set_m_if(B, n, i, v, zi),
            Equal.cong(R.PT, R.PT, x => R.swap_m(x, n, i, v), R.swap_m(t, n, j, w), B, e2),
            eB)))))
