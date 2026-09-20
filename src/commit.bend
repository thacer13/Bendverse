import Base
import ./refine.bend as R
import ./word.bend as WR
import ./bits.bend as Bits

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

# ------------------------------------------------------------------ V3c-1b
# Schedule invariance, the list/region layer: folding a `List` of point writes
# equals folding under any region split, provided the writes target distinct
# leaves. This lifts the single-write kernel `swap_m_comm` (V3c-1) to the shape
# the engine actually produces.
#
# A `V3cWrite` is one point write `(index, value)`. `v3c_fold(ws, t, n)` applies
# the writes of `ws` in order to the `2^n`-leaf tree `t`, each by the engine-facing
# `Refine.swap_m` (the `Refine.PT` presentation of `Array.set`). The two facts
# proved here are:
#
#   v3c_write_past_fold:  one write commutes past an entire fold of writes that
#                         all target leaves distinct from its own;
#   v3c_fold_commutes:    an append/permutation of pairwise-distinct writes
#                         yields the same tree as the sequential fold.
#
# `v3c_fold_commutes` is the region-split equality: two regions may fold their
# write lists independently onto the same starting tree and the merged result is
# the same tree, so the scheduler is free to choose the region order.
#
# Distinctness is `v3c_all_ne(ws, t, n, i)` (every write of `ws` avoids leaf `i`)
# and `v3c_pair_ne(xs, ys, t, n)` (every write of `xs` avoids every write of
# `ys`); both are built from `ne_idx`. Because `ne_idx` reads only the tree's
# constructor shape, it is invariant under a write (`v3c_ne_idx_swap`), which is
# what lets the distinctness hypotheses survive the changing accumulator tree.
# The fold itself is a structural recursion on the write list, so it stays in the
# well-founded fragment.


# ---------------- fold over a list of point writes ----------------

type V3cWrite is Data:
  MkWrite{index: U32, value: U32}

def v3c_fold(+ws: +List<V3cWrite>, t: R.PT, +n: U32) -> R.PT:
  match ws:
    case Nil{}:
      t
    case Con{+h, +tl}:
      match h:
        case MkWrite{index, value}:
          v3c_fold(tl, R.swap_m(t, n, index, value), n)

def v3c_band(+a: Bool, +b: Bool) -> Bool:
  Bool.pick(Bool, a, b, False{})

def v3c_band_cong2(+a1: Bool, +a2: Bool, +b1: Bool, +b2: Bool,
  +ha: {a1 == a2 : Bool}, +hb: {b1 == b2 : Bool})
  -> {v3c_band(a1, b1) == v3c_band(a2, b2) : Bool}:
  Equal.trans(Bool,
    v3c_band(a1, b1),
    v3c_band(a1, b2),
    v3c_band(a2, b2),
    Equal.cong(Bool, Bool, x => v3c_band(a1, x), b1, b2, hb),
    Equal.cong(Bool, Bool, x => v3c_band(x, b2), a1, a2, ha))

def v3c_and_true_l(+a: Bool, +b: Bool, +h: {v3c_band(a, b) == True{} : Bool})
  -> {a == True{} : Bool}:
  match a:
    case True{}: {==}
    case False{}: h

def v3c_and_true_r(+a: Bool, +b: Bool, +h: {v3c_band(a, b) == True{} : Bool})
  -> {b == True{} : Bool}:
  match a:
    case True{}: h
    case False{}:
      Equal.cong(Bool, Bool, x => Bool.pick(Bool, x, True{}, b), False{}, True{}, h)

# ---------------- distinctness predicates ----------------

def v3c_all_ne(+ws: +List<V3cWrite>, +t: R.PT, +n: U32, +i: U32) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+h, +tl}:
      match h:
        case MkWrite{index, value}:
          v3c_band(ne_idx(t, n, i, index), v3c_all_ne(tl, t, n, i))

def v3c_pair_ne(+xs: +List<V3cWrite>, +ys: +List<V3cWrite>, +t: R.PT, +n: U32) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+h, +tl}:
      match h:
        case MkWrite{index, value}:
          v3c_band(v3c_all_ne(ys, t, n, index), v3c_pair_ne(tl, ys, t, n))

# ---------------- tree-shape invariance of ne_idx ----------------

def v3c_ne_idx_pick(A: R.PT, B: R.PT, +n: U32, +i: U32, +j: U32, +z: Bool)
  -> {ne_idx(Bool.pick(R.PT, z, A, B), n, i, j) == Bool.pick(Bool, z, ne_idx(A, n, i, j), ne_idx(B, n, i, j)) : Bool}:
  match z:
    case True{}: {==}
    case False{}: {==}

def v3c_bool_pick_same(+z: Bool, +b: Bool) -> {Bool.pick(Bool, z, b, b) == b : Bool}:
  match z:
    case True{}: {==}
    case False{}: {==}

def v3c_pick_cong2(+z: Bool, +a1: Bool, +a2: Bool, +b1: Bool, +b2: Bool,
  +ha: {a1 == a2 : Bool}, +hb: {b1 == b2 : Bool})
  -> {Bool.pick(Bool, z, a1, b1) == Bool.pick(Bool, z, a2, b2) : Bool}:
  Equal.trans(Bool,
    Bool.pick(Bool, z, a1, b1),
    Bool.pick(Bool, z, a2, b1),
    Bool.pick(Bool, z, a2, b2),
    Equal.cong(Bool, Bool, x => Bool.pick(Bool, z, x, b1), a1, a2, ha),
    Equal.cong(Bool, Bool, x => Bool.pick(Bool, z, a2, x), b1, b2, hb))

def v3c_mkt(+A: R.PT, +B: R.PT) -> R.PT:
  R.PN{A, B}

def v3c_ne_idx_swap(+t: R.PT, +n: U32, +ii: U32, +v: U32, +i: U32, +j: U32)
  -> {ne_idx(R.swap_m(t, n, ii, v), n, i, j) == ne_idx(t, n, i, j) : Bool}:
  match t:
    case R.PL{x}:
      {==}
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +zi = U32.is_lt(ii, h)
      +zj = U32.is_lt(j, h)
      +zii = U32.is_lt(i, h)
      +A = v3c_mkt(R.swap_m(xs, h, ii, v), ys)
      +B = v3c_mkt(xs, R.swap_m(ys, h, U32.sub(ii, h), v))
      +ihx = v3c_ne_idx_swap(xs, h, ii, v, i, j)
      +ihy = v3c_ne_idx_swap(ys, h, U32.sub(ii, h), v, U32.sub(i, h), U32.sub(j, h))
      +Xsp = ne_idx(R.swap_m(xs, h, ii, v), h, i, j)
      +Xs = ne_idx(xs, h, i, j)
      +Ysp = ne_idx(R.swap_m(ys, h, U32.sub(ii, h), v), h, U32.sub(i, h), U32.sub(j, h))
      +Ys = ne_idx(ys, h, U32.sub(i, h), U32.sub(j, h))
      +W = ne_idx_if(Xs, Ys, zj, zii)
      +eA = Equal.cong(Bool, Bool, x => ne_idx_if(x, Ys, zj, zii), Xsp, Xs, ihx)
      +eB = Equal.cong(Bool, Bool, x => ne_idx_if(Xs, x, zj, zii), Ysp, Ys, ihy)
      +ep = Equal.trans(Bool,
        Bool.pick(Bool, zi, ne_idx(A, n, i, j), ne_idx(B, n, i, j)),
        Bool.pick(Bool, zi, W, W),
        W,
        v3c_pick_cong2(zi, ne_idx(A, n, i, j), W, ne_idx(B, n, i, j), W, eA, eB),
        v3c_bool_pick_same(zi, W))
      Equal.trans(Bool,
        ne_idx(Bool.pick(R.PT, zi, A, B), n, i, j),
        Bool.pick(Bool, zi, ne_idx(A, n, i, j), ne_idx(B, n, i, j)),
        ne_idx(R.PN{xs, ys}, n, i, j),
        v3c_ne_idx_pick(A, B, n, i, j, zi),
        ep)

# ---------------- predicate transport ----------------

def v3c_all_ne_swap(+ws: +List<V3cWrite>, +t: R.PT, +n: U32, +ii: U32, +v: U32, +i: U32)
  -> {v3c_all_ne(ws, R.swap_m(t, n, ii, v), n, i) == v3c_all_ne(ws, t, n, i) : Bool}:
  match ws:
    case Nil{}:
      {==}
    case Con{+h, +tl}:
      match h:
        case MkWrite{index, value}:
          v3c_band_cong2(
            ne_idx(R.swap_m(t, n, ii, v), n, i, index),
            ne_idx(t, n, i, index),
            v3c_all_ne(tl, R.swap_m(t, n, ii, v), n, i),
            v3c_all_ne(tl, t, n, i),
            v3c_ne_idx_swap(t, n, ii, v, i, index),
            v3c_all_ne_swap(tl, t, n, ii, v, i))

def v3c_pair_ne_swap(+xs: +List<V3cWrite>, +ys: +List<V3cWrite>, +t: R.PT, +n: U32, +ii: U32, +v: U32)
  -> {v3c_pair_ne(xs, ys, R.swap_m(t, n, ii, v), n) == v3c_pair_ne(xs, ys, t, n) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +tl}:
      match h:
        case MkWrite{index, value}:
          v3c_band_cong2(
            v3c_all_ne(ys, R.swap_m(t, n, ii, v), n, index),
            v3c_all_ne(ys, t, n, index),
            v3c_pair_ne(tl, ys, R.swap_m(t, n, ii, v), n),
            v3c_pair_ne(tl, ys, t, n),
            v3c_all_ne_swap(ys, t, n, ii, v, index),
            v3c_pair_ne_swap(tl, ys, t, n, ii, v))

# ---------------- the two algebraic lemmas ----------------

def v3c_append_split(+xs: +List<V3cWrite>, +ys: +List<V3cWrite>, t: R.PT, +n: U32)
  -> {v3c_fold(List.append(&2, V3cWrite, xs, ys), t, n) == v3c_fold(ys, v3c_fold(xs, t, n), n) : R.PT}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +tl}:
      match h:
        case MkWrite{index, value}:
          v3c_append_split(tl, ys, R.swap_m(t, n, index, value), n)

def v3c_write_past_fold(+ws: +List<V3cWrite>, +t: R.PT, +n: U32, +i: U32, +v: U32,
  +hne: {v3c_all_ne(ws, t, n, i) == True{} : Bool})
  -> {v3c_fold(ws, R.swap_m(t, n, i, v), n) == R.swap_m(v3c_fold(ws, t, n), n, i, v) : R.PT}:
  match ws:
    case Nil{}:
      {==}
    case Con{+h, +tl}:
      match h:
        case MkWrite{index, value}:
          +hh = v3c_and_true_l(ne_idx(t, n, i, index), v3c_all_ne(tl, t, n, i), hne)
          +ht = v3c_and_true_r(ne_idx(t, n, i, index), v3c_all_ne(tl, t, n, i), hne)
          +ecomm = swap_m_comm(t, n, i, index, v, value, hh)
          +htp = Equal.trans(Bool,
            v3c_all_ne(tl, R.swap_m(t, n, index, value), n, i),
            v3c_all_ne(tl, t, n, i),
            True{},
            v3c_all_ne_swap(tl, t, n, index, value, i),
            ht)
          Equal.trans(R.PT,
            v3c_fold(tl, R.swap_m(R.swap_m(t, n, i, v), n, index, value), n),
            v3c_fold(tl, R.swap_m(R.swap_m(t, n, index, value), n, i, v), n),
            R.swap_m(v3c_fold(tl, R.swap_m(t, n, index, value), n), n, i, v),
            Equal.cong(R.PT, R.PT, x => v3c_fold(tl, x, n),
              R.swap_m(R.swap_m(t, n, i, v), n, index, value),
              R.swap_m(R.swap_m(t, n, index, value), n, i, v),
              ecomm),
            v3c_write_past_fold(tl, R.swap_m(t, n, index, value), n, i, v, htp))

def v3c_fold_region(+xs: +List<V3cWrite>, +ys: +List<V3cWrite>, +t: R.PT, +n: U32,
  +hpn: {v3c_pair_ne(xs, ys, t, n) == True{} : Bool})
  -> {v3c_fold(ys, v3c_fold(xs, t, n), n) == v3c_fold(xs, v3c_fold(ys, t, n), n) : R.PT}:
  match xs:
    case Nil{}:
      {==}
    case Con{+h, +tl}:
      match h:
        case MkWrite{index, value}:
          +hne_ys = v3c_and_true_l(v3c_all_ne(ys, t, n, index), v3c_pair_ne(tl, ys, t, n), hpn)
          +hpn_tl = v3c_and_true_r(v3c_all_ne(ys, t, n, index), v3c_pair_ne(tl, ys, t, n), hpn)
          +hpn_tlp = Equal.trans(Bool,
            v3c_pair_ne(tl, ys, R.swap_m(t, n, index, value), n),
            v3c_pair_ne(tl, ys, t, n),
            True{},
            v3c_pair_ne_swap(tl, ys, t, n, index, value),
            hpn_tl)
          +ewp = v3c_write_past_fold(ys, t, n, index, value, hne_ys)
          Equal.trans(R.PT,
            v3c_fold(ys, v3c_fold(tl, R.swap_m(t, n, index, value), n), n),
            v3c_fold(tl, v3c_fold(ys, R.swap_m(t, n, index, value), n), n),
            v3c_fold(tl, R.swap_m(v3c_fold(ys, t, n), n, index, value), n),
            v3c_fold_region(tl, ys, R.swap_m(t, n, index, value), n, hpn_tlp),
            Equal.cong(R.PT, R.PT, x => v3c_fold(tl, x, n),
              v3c_fold(ys, R.swap_m(t, n, index, value), n),
              R.swap_m(v3c_fold(ys, t, n), n, index, value),
              ewp))

def v3c_fold_commutes(+xs: +List<V3cWrite>, +ys: +List<V3cWrite>, +t: R.PT, +n: U32,
  +hpn: {v3c_pair_ne(xs, ys, t, n) == True{} : Bool})
  -> {v3c_fold(List.append(&2, V3cWrite, xs, ys), t, n) == v3c_fold(List.append(&2, V3cWrite, ys, xs), t, n) : R.PT}:
  Equal.trans(R.PT,
    v3c_fold(List.append(&2, V3cWrite, xs, ys), t, n),
    v3c_fold(ys, v3c_fold(xs, t, n), n),
    v3c_fold(List.append(&2, V3cWrite, ys, xs), t, n),
    v3c_append_split(xs, ys, t, n),
    Equal.trans(R.PT,
      v3c_fold(ys, v3c_fold(xs, t, n), n),
      v3c_fold(xs, v3c_fold(ys, t, n), n),
      v3c_fold(List.append(&2, V3cWrite, ys, xs), t, n),
      v3c_fold_region(xs, ys, t, n, hpn),
      Equal.sym(R.PT,
        v3c_fold(List.append(&2, V3cWrite, ys, xs), t, n),
        v3c_fold(xs, v3c_fold(ys, t, n), n),
        v3c_append_split(ys, xs, t, n))))

# -------------------------------------------------------- V3c-2 (soundness)
# The kernel hypothesis `ne_idx(t, n, i, j) == True` must mean the engine's own
# distinctness `U32.is_eq(i, j) == False`; otherwise the fold/region law (V3c-1b)
# could separate two writes that collide. This section proves the *sound*
# direction: equal indices are never separated,
#
#   U32.is_eq(i, j) == True  =>  ne_idx(t, n, i, j) == False,
#
# equivalently `ne_idx == True => U32.is_eq(i, j) == False`. It needs no tree
# fullness or range hypothesis: `ne_idx` splits only when `is_lt` differs, and for
# `i == j` both decisions coincide at every node (`v3c_ne_idx_refl`), leaving the
# leaf case `False`. The reflected engine equality comes from `Word.u32_cmp_eq`.
#
# The converse — for an in-range `i != j` on a full tree, `ne_idx == True`
# (completeness) — needs the `U32` order/subtraction arithmetic and remains the
# open residual recorded in `PLAN.md` §5.3 (`G3`, V3c-2).
def v3c_ne_idx_refl_if(+xs: R.PT, +ys: R.PT, +h: U32, +i: U32, +z: Bool,
  ihx: {ne_idx(xs, h, i, i) == False{} : Bool},
  ihy: {ne_idx(ys, h, U32.sub(i, h), U32.sub(i, h)) == False{} : Bool})
  -> {ne_idx_if(ne_idx(xs, h, i, i), ne_idx(ys, h, U32.sub(i, h), U32.sub(i, h)), z, z) == False{} : Bool}:
  match z:
    case True{}:
      ihx
    case False{}:
      ihy

def v3c_ne_idx_refl(+t: R.PT, +n: U32, +i: U32) -> {ne_idx(t, n, i, i) == False{} : Bool}:
  match t:
    case R.PL{x}:
      {==}
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      v3c_ne_idx_refl_if(xs, ys, h, i, U32.is_lt(i, h),
        v3c_ne_idx_refl(xs, h, i),
        v3c_ne_idx_refl(ys, h, U32.sub(i, h)))

def v3c_ne_idx_sound(+t: R.PT, +n: U32, +i: U32, +j: U32,
  +he: {U32.is_eq(i, j) == True{} : Bool})
  -> {ne_idx(t, n, i, j) == False{} : Bool}:
  +eij = WR.u32_cmp_eq(i, j, he)
  Equal.trans(Bool,
    ne_idx(t, n, i, j),
    ne_idx(t, n, i, i),
    False{},
    Equal.sym(Bool, ne_idx(t, n, i, i), ne_idx(t, n, i, j),
      Equal.cong(U32, Bool, x => ne_idx(t, n, i, x), i, j, eij)),
    v3c_ne_idx_refl(t, n, i))

# ---------------------------------------------------- V3c-2 (completeness)
# The converse of `v3c_ne_idx_sound`: for a full `2^k`-leaf tree and in-range
# indices, distinctness implies `ne_idx == True`, so `ne_idx` is *exactly*
# `U32.is_eq(i, j) == False`. This section lands the structural half — the
# canonical tree/size pairs, the reflection and arithmetic groundwork, and the
# three cases of `ne_idx`'s defining recursion (top split, both-left,
# both-right). The remaining residual is the arithmetic that the child
# hypothesis stays in range (subtraction clearing the top bit) and that the
# canonical size halves under `U32.shr`; see `PLAN.md` §5.3 (`G3`).
#
# `v3c_two(k)` is the leaf count `2^k` and `v3c_full(k)` the canonical full tree
# of that size. `v3c_is_eq_refl` reflects the equal case (`Word.cmp` on a word
# with itself is `EQ`); `v3c_shr_shl` is the shift-roundtrip (a right shift undoes
# a left shift when the top bit is clear, via the shared `Bits.shr_shl_one`);
# `v3c_sub_zero` is the first additive identity toward the `add ∘ sub` roundtrip
# that the both-right case needs.

def v3c_two(+k: Nat) -> U32:
  U32.shln(1, k)

def v3c_full(k: Nat) -> R.PT:
  match k:
    case 0n:
      R.PL{0}
    case 1n+p:
      +q = p
      R.PN{v3c_full(q), v3c_full(q)}

def v3c_w_cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+p:
      match w:
        case WCon{wh, wt}:
          match wh:
            case False{}:
              %Equal.sym(Cmp, Word.cmp(p, wt, wt), EQ{}, v3c_w_cmp_refl(p, wt)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
              {==}
            case True{}:
              %Equal.sym(Cmp, Word.cmp(p, wt, wt), EQ{}, v3c_w_cmp_refl(p, wt)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
              {==}

def v3c_is_eq_refl(+a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{w}:
      Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), Word.cmp(32n, w, w), EQ{}, v3c_w_cmp_refl(32n, w))

def v3c_shr_shl(+w: Word(32n), +h: {Word.and(32n, w, Bits.mask(32n, 31n)) == w : Word(32n)})
  -> {U32.shr(U32.shl(U32{w})) == U32{w} : U32}:
  Equal.cong(Word(32n), U32, x => U32{x},
    Word.shr(32n, Word.shl(32n, w)),
    w,
    Equal.trans(Word(32n),
      Word.shr(32n, Word.shl(32n, w)),
      Word.and(32n, w, Bits.mask(32n, 31n)),
      w,
      Bits.shr_shl_one(31n, w),
      h))

def v3c_sub_zero(n: Nat, a: Word(n)) -> {Word.sub(n, a, Word.zero(n)) == a : Word(n)}:
  match n:
    case 0n:
      match a:
        case WNil{}: {==}
    case 1n+p:
      match a:
        case WCon{ah, at}:
          match ah:
            case False{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
                Word.sub(p, at, Word.zero(p)), at, v3c_sub_zero(p, at))
            case True{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
                Word.sub(p, at, Word.zero(p)), at, v3c_sub_zero(p, at))

# ---------------- the three cases of `ne_idx`'s node recursion ----------------
# At a `R.PN` node with `h = U32.shr(n)` and decisions `zi = is_lt(i, h)`,
# `zj = is_lt(j, h)`, `ne_idx` is the definitional `Bool.pick` of the decision
# table. The pick-helpers turn the hypotheses `zi`/`zj` into the reduced form by
# congruence (no case analysis), and the wrappers expose the three outcomes.

def v3c_pick_lr(+nzi: Bool, +nzj: Bool, +zi: Bool, +zj: Bool,
  +hzi: {zi == True{} : Bool}, +hzj: {zj == False{} : Bool})
  -> {Bool.pick(Bool, zi, Bool.pick(Bool, zj, nzi, True{}), Bool.pick(Bool, zj, True{}, nzj)) == True{} : Bool}:
  +A = Bool.pick(Bool, zj, nzi, True{})
  +B = Bool.pick(Bool, zj, True{}, nzj)
  +e1 = Equal.cong(Bool, Bool, b => Bool.pick(Bool, b, A, B), zi, True{}, hzi)
  +eA = Equal.cong(Bool, Bool, b => Bool.pick(Bool, b, nzi, True{}), zj, False{}, hzj)
  Equal.trans(Bool, Bool.pick(Bool, zi, A, B), A, True{}, e1, eA)

def v3c_pick_ll(+nzi: Bool, +nzj: Bool, +zi: Bool, +zj: Bool,
  +hzi: {zi == True{} : Bool}, +hzj: {zj == True{} : Bool})
  -> {Bool.pick(Bool, zi, Bool.pick(Bool, zj, nzi, True{}), Bool.pick(Bool, zj, True{}, nzj)) == nzi : Bool}:
  +A = Bool.pick(Bool, zj, nzi, True{})
  +B = Bool.pick(Bool, zj, True{}, nzj)
  +e1 = Equal.cong(Bool, Bool, b => Bool.pick(Bool, b, A, B), zi, True{}, hzi)
  +eA = Equal.cong(Bool, Bool, b => Bool.pick(Bool, b, nzi, True{}), zj, True{}, hzj)
  Equal.trans(Bool, Bool.pick(Bool, zi, A, B), A, nzi, e1, eA)

def v3c_pick_rr(+nzi: Bool, +nzj: Bool, +zi: Bool, +zj: Bool,
  +hzi: {zi == False{} : Bool}, +hzj: {zj == False{} : Bool})
  -> {Bool.pick(Bool, zi, Bool.pick(Bool, zj, nzi, True{}), Bool.pick(Bool, zj, True{}, nzj)) == nzj : Bool}:
  +A = Bool.pick(Bool, zj, nzi, True{})
  +B = Bool.pick(Bool, zj, True{}, nzj)
  +e1 = Equal.cong(Bool, Bool, b => Bool.pick(Bool, b, A, B), zi, False{}, hzi)
  +eB = Equal.cong(Bool, Bool, b => Bool.pick(Bool, b, True{}, nzj), zj, False{}, hzj)
  Equal.trans(Bool, Bool.pick(Bool, zi, A, B), B, nzj, e1, eB)

# Top split: the two indices go to opposite children, so `ne_idx` is `True`
# regardless of the children. Together with `v3c_ne_idx_same_l`/`_r` this is the
# full structural content of completeness.
def v3c_ne_idx_sep(+xs: R.PT, +ys: R.PT, +n: U32, +i: U32, +j: U32,
  +hzi: {U32.is_lt(i, U32.shr(n)) == True{} : Bool},
  +hzj: {U32.is_lt(j, U32.shr(n)) == False{} : Bool})
  -> {ne_idx(R.PN{xs, ys}, n, i, j) == True{} : Bool}:
  +h = U32.shr(n)
  +nzi = ne_idx(xs, h, i, j)
  +nzj = ne_idx(ys, h, U32.sub(i, h), U32.sub(j, h))
  v3c_pick_lr(nzi, nzj, U32.is_lt(i, h), U32.is_lt(j, h), hzi, hzj)

# Both-left: both indices stay in the left child, so the node is the child.
def v3c_ne_idx_same_l(+xs: R.PT, +ys: R.PT, +n: U32, +i: U32, +j: U32,
  +hzi: {U32.is_lt(i, U32.shr(n)) == True{} : Bool},
  +hzj: {U32.is_lt(j, U32.shr(n)) == True{} : Bool})
  -> {ne_idx(R.PN{xs, ys}, n, i, j) == ne_idx(xs, U32.shr(n), i, j) : Bool}:
  +h = U32.shr(n)
  +nzi = ne_idx(xs, h, i, j)
  +nzj = ne_idx(ys, h, U32.sub(i, h), U32.sub(j, h))
  v3c_pick_ll(nzi, nzj, U32.is_lt(i, h), U32.is_lt(j, h), hzi, hzj)

# Both-right: both indices shift into the right child.
def v3c_ne_idx_same_r(+xs: R.PT, +ys: R.PT, +n: U32, +i: U32, +j: U32,
  +hzi: {U32.is_lt(i, U32.shr(n)) == False{} : Bool},
  +hzj: {U32.is_lt(j, U32.shr(n)) == False{} : Bool})
  -> {ne_idx(R.PN{xs, ys}, n, i, j) == ne_idx(ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.sub(j, U32.shr(n))) : Bool}:
  +h = U32.shr(n)
  +nzi = ne_idx(xs, h, i, j)
  +nzj = ne_idx(ys, h, U32.sub(i, h), U32.sub(j, h))
  v3c_pick_rr(nzi, nzj, U32.is_lt(i, h), U32.is_lt(j, h), hzi, hzj)
