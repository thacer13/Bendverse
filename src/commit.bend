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

# ---------------- the `add ∘ sub` roundtrip ----------------
# `U32` arithmetic is modular, so `sub(i, h) + h = i` holds for *all* `i`, `h`
# (the ignored borrow is exactly the carry the addition puts back). This is the
# identity the both-right completeness case needs to cancel `U32.sub` and to
# carry range facts, and it is the suggested "subtraction clears the top bit"
# step in unconditional form. `v3c_addsub_bit` is the per-bit two's-complement
# fact; `v3c_addsub_go` threads the coupled borrow/carry through `Word.adc`.

def v3c_bfst(p: Bool & Bool) -> Bool:
  match p:
    case (a, _): a

def v3c_bsnd(p: Bool & Bool) -> Bool:
  match p:
    case (_, b): b

def v3c_addsub_bit(ah: Bool, bh: Bool, c: Bool)
  -> {Bool.full_add(v3c_bfst(Bool.full_add(ah, Bool.not(bh), c)), bh, Bool.not(c))
        == (ah, Bool.not(v3c_bsnd(Bool.full_add(ah, Bool.not(bh), c)))) : Bool & Bool}:
  match ah bh c:
    case False{} False{} False{}: {==}
    case False{} False{} True{}: {==}
    case False{} True{} False{}: {==}
    case False{} True{} True{}: {==}
    case True{} False{} False{}: {==}
    case True{} False{} True{}: {==}
    case True{} True{} False{}: {==}
    case True{} True{} True{}: {==}

def v3c_addsub_go(n: Nat, a: Word(n), b: Word(n), c: Bool)
  -> {Word.adc(n, Word.adc(n, a, b, True{}, c), b, False{}, Bool.not(c)) == a : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}: {==}
    case 1n+p:
      match a b c:
        case WCon{False{}, at} WCon{False{}, bt} False{}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}),
            at, v3c_addsub_go(p, at, bt, False{}))
        case WCon{False{}, at} WCon{True{}, bt} False{}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}),
            at, v3c_addsub_go(p, at, bt, False{}))
        case WCon{True{}, at} WCon{False{}, bt} False{}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
            Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}),
            at, v3c_addsub_go(p, at, bt, True{}))
        case WCon{True{}, at} WCon{True{}, bt} False{}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
            Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}),
            at, v3c_addsub_go(p, at, bt, False{}))
        case WCon{False{}, at} WCon{False{}, bt} True{}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}),
            at, v3c_addsub_go(p, at, bt, True{}))
        case WCon{False{}, at} WCon{True{}, bt} True{}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.adc(p, Word.adc(p, at, bt, True{}, False{}), bt, False{}, True{}),
            at, v3c_addsub_go(p, at, bt, False{}))
        case WCon{True{}, at} WCon{False{}, bt} True{}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
            Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}),
            at, v3c_addsub_go(p, at, bt, True{}))
        case WCon{True{}, at} WCon{True{}, bt} True{}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
            Word.adc(p, Word.adc(p, at, bt, True{}, True{}), bt, False{}, False{}),
            at, v3c_addsub_go(p, at, bt, True{}))

def v3c_add_sub(n: Nat, a: Word(n), b: Word(n))
  -> {Word.add(n, Word.sub(n, a, b), b) == a : Word(n)}:
  v3c_addsub_go(n, a, b, True{})

# ============================================================ V3c-2 (complete)
# The arithmetic that finishes completeness (`G3`, V3c-2). The structural half
# (`v3c_ne_idx_sep`/`_same_l`/`_same_r`) reduces the claim to three `U32`
# order/range bricks, all landed here:
#
#   1. `v3c_lt_one`/`v3c_lt_one_u32` — `i < 1` forces `i = 0` (a leaf collides),
#      reflecting `Word.cmp`'s `LT` (the sibling of `w_cmp_eq`).
#   2. `v3c_sub_pow_lt`/`v3c_sub_two_lt` — for `i` in `[2^k, 2^(k+1))`,
#      `i - 2^k < 2^k` (range preservation under the subtraction), so the right
#      child's index is in range.
#   3. `v3c_two_shr_ne`/`v3c_two_shr_of_lt` — the canonical size halves:
#      `shr(two(k+1)) = two(k)` whenever `two(k+1) != 0` (the `k = 31` boundary
#      is vacuous: `two(32) = 0` is never an in-range bound).
#
# `v3c_ne_idx_complete_imp` is the induction: distinct in-range indices on the
# full `2^k`-leaf tree are separated. Together with the soundness half
# (`v3c_ne_idx_sound`) it yields `v3c_ne_idx_exact`: `ne_idx` is *exactly*
# `Bool.not (U32.is_eq i j)`.
#
# The `v3c_mpow` development is the `Word`-level `2^d` (mirroring `G5.g5_mpow`)
# kept local so this section depends only on `word`/`bits`/`refine`; `v3c_absurd`
# is the `{False == True}` eliminator.

def v3c_absurd(T: Type, X: T, Y: T, +h: {False{} == True{} : Bool}) -> {X == Y : T}:
  Equal.cong(Bool, T, x => Bool.pick(T, x, Y, X), False{}, True{}, h)

def v3c_mpow(n: Nat, d: Nat) -> Word(n):
  match n:
    case 0n: WNil{}
    case 1n+p:
      match d:
        case 0n: WCon{True{}, Word.zero(p)}
        case 1n+q: WCon{False{}, v3c_mpow(p, q)}

def v3c_shl_eq_put(n: Nat, X: Word(n)) -> {Word.shl(n, X) == Word.shl.put(n, False{}, X) : Word(n)}:
  match n:
    case 0n:
      match X: case WNil{}: {==}
    case 1n+p:
      match X:
        case WCon{xh, xt}: {==}

def v3c_shlput_false_zero(n: Nat) -> {Word.shl.put(n, False{}, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p),
        v3c_shlput_false_zero(p))

def v3c_shlput_true_zero(p: Nat) -> {Word.shl.put(p, True{}, Word.zero(p)) == v3c_mpow(p, 0n) : Word(p)}:
  match p:
    case 0n: {==}
    case 1n+q:
      Equal.cong(Word(q), Word(1n+q), t => WCon{True{}, t},
        Word.shl.put(q, False{}, Word.zero(q)), Word.zero(q),
        v3c_shlput_false_zero(q))

def v3c_pow_shl(n: Nat, d: Nat) -> {Word.shl(n, v3c_mpow(n, d)) == v3c_mpow(n, 1n+d) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      match d:
        case 0n:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.shl.put(p, True{}, Word.zero(p)), v3c_mpow(p, 0n),
            v3c_shlput_true_zero(p))
        case 1n+ +q:
          +X = v3c_mpow(p, q)
          +e = Equal.trans(Word(p),
                 Word.shl.put(p, False{}, X), Word.shl(p, X), v3c_mpow(p, 1n+q),
                 Equal.sym(Word(p), Word.shl(p, X), Word.shl.put(p, False{}, X), v3c_shl_eq_put(p, X)),
                 v3c_pow_shl(p, q))
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.shl.put(p, False{}, X), v3c_mpow(p, 1n+q), e)

def v3c_two_mpow(k: Nat) -> {v3c_two(k) == U32{v3c_mpow(32n, k)} : U32}:
  match k:
    case 0n: {==}
    case 1n+ +q:
      +ih = v3c_two_mpow(q)
      +e1 = Equal.cong(U32, U32, U32.shl, v3c_two(q), U32{v3c_mpow(32n, q)}, ih)
      +e2 = v3c_pow_shl(32n, q)
      +e3 = Equal.cong(Word(32n), U32, w => U32{w}, Word.shl(32n, v3c_mpow(32n, q)), v3c_mpow(32n, 1n+q), e2)
      Equal.trans(U32, v3c_two(1n+q), U32.shl(U32{v3c_mpow(32n, q)}), U32{v3c_mpow(32n, 1n+q)}, e1, e3)

def v3c_shrpad_zero(p: Nat) -> {Word.shr.pad(p, Word.zero(p)) == Word.zero(1n+p) : Word(1n+p)}:
  match p:
    case 0n: {==}
    case 1n+ +q:
      Equal.cong(Word(1n+q), Word(1n+(1n+q)), t => WCon{False{}, t},
        Word.shr.pad(q, Word.zero(q)), Word.zero(1n+q),
        v3c_shrpad_zero(q))

def v3c_shrpad_pow(n: Nat, k: Nat, +h: {Nat.is_ne(n, k) == True{} : Bool})
  -> {Word.shr.pad(n, v3c_mpow(n, k)) == v3c_mpow(1n+n, k) : Word(1n+n)}:
  match n:
    case 0n:
      match k:
        case 0n:
          v3c_absurd(Word(1n+0n), Word.shr.pad(0n, v3c_mpow(0n, 0n)), v3c_mpow(1n, 0n), h)
        case 1n+q: {==}
    case 1n+ +p:
      match k:
        case 0n:
          Equal.cong(Word(1n+p), Word(1n+(1n+p)), t => WCon{True{}, t},
            Word.shr.pad(p, Word.zero(p)), Word.zero(1n+p),
            v3c_shrpad_zero(p))
        case 1n+ +q:
          +ih = v3c_shrpad_pow(p, q, h)
          Equal.cong(Word(1n+p), Word(1n+(1n+p)), t => WCon{False{}, t},
            Word.shr.pad(p, v3c_mpow(p, q)), v3c_mpow(1n+p, q), ih)

def v3c_two_shr_ne(+k: Nat, +h: {Nat.is_ne(31n, k) == True{} : Bool})
  -> {U32.shr(v3c_two(1n+k)) == v3c_two(k) : U32}:
  +e1 = v3c_two_mpow(1n+k)
  +ec1 = Equal.cong(U32, U32, U32.shr, v3c_two(1n+k), U32{v3c_mpow(32n, 1n+k)}, e1)
  +e2 = v3c_shrpad_pow(31n, k, h)
  +ec2 = Equal.cong(Word(32n), U32, w => U32{w}, Word.shr.pad(31n, v3c_mpow(31n, k)), v3c_mpow(32n, k), e2)
  +e3 = Equal.sym(U32, v3c_two(k), U32{v3c_mpow(32n, k)}, v3c_two_mpow(k))
  Equal.trans(U32, U32.shr(v3c_two(1n+k)), U32{Word.shr.pad(31n, v3c_mpow(31n, k))}, v3c_two(k), ec1, Equal.trans(U32, U32{Word.shr.pad(31n, v3c_mpow(31n,k))}, U32{v3c_mpow(32n,k)}, v3c_two(k), ec2, e3))

def v3c_cmp_fin_not_lt(+ih: Bool, +c: Cmp, +h: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_lt(Word.cmp.fin(ih, False{}, c)) == False{} : Bool}:
  match ih c:
    case False{} LT{}: h
    case False{} EQ{}: h
    case False{} GT{}: h
    case True{} LT{}: h
    case True{} EQ{}: h
    case True{} GT{}: h

def v3c_cmp_zero_not_lt(n: Nat, iw: Word(n)) -> {Cmp.is_lt(Word.cmp(n, iw, Word.zero(n))) == False{} : Bool}:
  match n:
    case 0n:
      match iw: case WNil{}: {==}
    case 1n+ +p:
      match iw:
        case WCon{ih, +it}:
          v3c_cmp_fin_not_lt(ih, Word.cmp(p, it, Word.zero(p)), v3c_cmp_zero_not_lt(p, it))

def v3c_lt_one_cons(+p: Nat, +ih: Bool, +it: Word(p), +c: Cmp,
   +hl: {Word.cmp(p, it, Word.zero(p)) == c : Cmp},
   +h: {Cmp.is_lt(Word.cmp.fin(ih, True{}, c)) == True{} : Bool},
   +hc: {Cmp.is_lt(c) == False{} : Bool})
  -> {WCon{ih, it} == Word.zero(1n+p) : Word(1n+p)}:
  match ih c:
    case False{} LT{}:
      v3c_absurd(Word(1n+p), WCon{False{}, it}, Word.zero(1n+p),
        Equal.sym(Bool, True{}, False{}, hc))
    case False{} EQ{}:
      +heqc = Equal.trans(Bool,
        Cmp.is_eq(Word.cmp(p, it, Word.zero(p))), Cmp.is_eq(c), True{},
        Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, it, Word.zero(p)), c, hl),
        {==})
      +eit = WR.w_cmp_eq(p, it, Word.zero(p), heqc)
      Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, it, Word.zero(p), eit)
    case False{} GT{}:
      v3c_absurd(Word(1n+p), WCon{False{}, it}, Word.zero(1n+p), h)
    case True{} LT{}:
      v3c_absurd(Word(1n+p), WCon{True{}, it}, Word.zero(1n+p),
        Equal.sym(Bool, True{}, False{}, hc))
    case True{} EQ{}:
      v3c_absurd(Word(1n+p), WCon{True{}, it}, Word.zero(1n+p), h)
    case True{} GT{}:
      v3c_absurd(Word(1n+p), WCon{True{}, it}, Word.zero(1n+p), h)

def v3c_lt_one(n: Nat, iw: Word(n), +h: {Cmp.is_lt(Word.cmp(n, iw, v3c_mpow(n, 0n))) == True{} : Bool}) -> {iw == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match iw: case WNil{}: {==}
    case 1n+ +p:
      match iw:
        case WCon{ih, +it}:
          v3c_lt_one_cons(p, ih, it, Word.cmp(p, it, Word.zero(p)), {==}, h, v3c_cmp_zero_not_lt(p, it))

def v3c_lt_one_u32(+i: U32, +h: {U32.is_lt(i, 1) == True{} : Bool}) -> {i == 0 : U32}:
  match i:
    case U32{iw}:
      match iw:
        case WCon{ih, +it}:
          +e = v3c_lt_one_cons(31n, ih, it, Word.cmp(31n, it, Word.zero(31n)), {==}, h, v3c_cmp_zero_not_lt(31n, it))
          Equal.cong(Word(32n), U32, w => U32{w}, WCon{ih, it}, Word.zero(32n), e)

def v3c_cmp_fin_false_lt(+ih: Bool, +c: Cmp) -> {Cmp.is_lt(Word.cmp.fin(ih, False{}, c)) == Cmp.is_lt(c) : Bool}:
  match ih c:
    case False{} LT{}: {==}
    case False{} EQ{}: {==}
    case False{} GT{}: {==}
    case True{} LT{}: {==}
    case True{} EQ{}: {==}
    case True{} GT{}: {==}

def v3c_cmp_fin_false_lt_true(+ih: Bool, +c: Cmp,
  +h: {Cmp.is_lt(Word.cmp.fin(ih, False{}, c)) == True{} : Bool})
  -> {Cmp.is_lt(c) == True{} : Bool}:
  Equal.trans(Bool, Cmp.is_lt(c), Cmp.is_lt(Word.cmp.fin(ih, False{}, c)), True{},
    Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(ih, False{}, c)), Cmp.is_lt(c), v3c_cmp_fin_false_lt(ih, c)),
    h)

def v3c_cmp_fin_false_lt_false(+ih: Bool, +c: Cmp,
  +h: {Cmp.is_lt(Word.cmp.fin(ih, False{}, c)) == False{} : Bool})
  -> {Cmp.is_lt(c) == False{} : Bool}:
  Equal.trans(Bool, Cmp.is_lt(c), Cmp.is_lt(Word.cmp.fin(ih, False{}, c)), False{},
    Equal.sym(Bool, Cmp.is_lt(Word.cmp.fin(ih, False{}, c)), Cmp.is_lt(c), v3c_cmp_fin_false_lt(ih, c)),
    h)

def v3c_fah_self(ih: Bool) -> {Bool.full_add(ih, True{}, True{}) == (ih, True{}) : Bool & Bool}:
  match ih:
    case False{}: {==}
    case True{}: {==}

def v3c_adc_not_self(+p: Nat, +ah: Bool, +at: Word(p)) -> {Word.adc(1n+p, WCon{ah, at}, WCon{ah, at}, True{}, True{}) == WCon{False{}, Word.adc(p, at, at, True{}, True{})} : Word(1n+p)}:
  match ah:
    case False{}: {==}
    case True{}: {==}

def v3c_sub_self(n: Nat, a: Word(n)) -> {Word.sub(n, a, a) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n+ +p:
      match a:
        case WCon{ah, +at}:
          +e = v3c_adc_not_self(p, ah, at)
          +ih = v3c_sub_self(p, at)
          Equal.trans(Word(1n+p),
            Word.adc(1n+p, WCon{ah, at}, WCon{ah, at}, True{}, True{}),
            WCon{False{}, Word.adc(p, at, at, True{}, True{})},
            Word.zero(1n+p),
            e,
            Equal.trans(Word(1n+p),
              WCon{False{}, Word.adc(p, at, at, True{}, True{})},
              WCon{False{}, Word.zero(p)},
              Word.zero(1n+p),
              Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
                Word.adc(p, at, at, True{}, True{}), Word.zero(p), ih),
              {==}))

def v3c_sub_even(+p: Nat, +ih: Bool, +it: Word(p), +X: Word(p))
  -> {Word.sub(1n+p, WCon{ih, it}, WCon{False{}, X}) == WCon{ih, Word.sub(p, it, X)} : Word(1n+p)}:
  +e = v3c_fah_self(ih)
  Equal.cong(Bool & Bool, Word(1n+p),
    pr => Word.adc.con(p, it, X, True{}, pr),
    Bool.full_add(ih, True{}, True{}), (ih, True{}), e)

def v3c_lt_two_one_ih(+p: Nat, +ih: Bool, +it: Word(p),
  +eit: {it == Word.zero(p) : Word(p)},
  +h0z: {Cmp.is_lt(Word.cmp(1n+p, WCon{ih, Word.zero(p)}, WCon{True{}, Word.zero(p)})) == False{} : Bool})
  -> {WCon{ih, it} == WCon{True{}, Word.zero(p)} : Word(1n+p)}:
  match ih:
    case True{}:
      Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t}, it, Word.zero(p), eit)
    case False{}:
      +ec = v3c_w_cmp_refl(p, Word.zero(p))
      +h0e = Equal.trans(Bool,
        Cmp.is_lt(Word.cmp.fin(False{}, True{}, EQ{})),
        Cmp.is_lt(Word.cmp(1n+p, WCon{False{}, Word.zero(p)}, WCon{True{}, Word.zero(p)})),
        False{},
        Equal.sym(Bool,
          Cmp.is_lt(Word.cmp(1n+p, WCon{False{}, Word.zero(p)}, WCon{True{}, Word.zero(p)})),
          Cmp.is_lt(Word.cmp.fin(False{}, True{}, EQ{})),
          Equal.cong(Cmp, Bool, cc => Cmp.is_lt(Word.cmp.fin(False{}, True{}, cc)), Word.cmp(p, Word.zero(p), Word.zero(p)), EQ{}, ec)),
        h0z)
      v3c_absurd(Word(1n+p), WCon{False{}, it}, WCon{True{}, Word.zero(p)}, Equal.sym(Bool, True{}, False{}, h0e))

def v3c_lt_two_one(+p: Nat, +iw: Word(1n+p),
  +h1: {Cmp.is_lt(Word.cmp(1n+p, iw, WCon{False{}, v3c_mpow(p, 0n)})) == True{} : Bool},
  +h0: {Cmp.is_lt(Word.cmp(1n+p, iw, WCon{True{}, Word.zero(p)})) == False{} : Bool})
  -> {iw == WCon{True{}, Word.zero(p)} : Word(1n+p)}:
  match iw:
    case WCon{+ih, +it}:
      +h1x = v3c_cmp_fin_false_lt_true(ih, Word.cmp(p, it, v3c_mpow(p, 0n)), h1)
      +eit = v3c_lt_one(p, it, h1x)
      +eitw = Equal.cong(Word(p), Word(1n+p), t => WCon{ih, t}, it, Word.zero(p), eit)
      +h0z = Equal.trans(Bool,
        Cmp.is_lt(Word.cmp(1n+p, WCon{ih, Word.zero(p)}, WCon{True{}, Word.zero(p)})),
        Cmp.is_lt(Word.cmp(1n+p, WCon{ih, it}, WCon{True{}, Word.zero(p)})),
        False{},
        Equal.sym(Bool,
          Cmp.is_lt(Word.cmp(1n+p, WCon{ih, it}, WCon{True{}, Word.zero(p)})),
          Cmp.is_lt(Word.cmp(1n+p, WCon{ih, Word.zero(p)}, WCon{True{}, Word.zero(p)})),
          Equal.cong(Word(1n+p), Bool, x => Cmp.is_lt(Word.cmp(1n+p, x, WCon{True{}, Word.zero(p)})), WCon{ih, it}, WCon{ih, Word.zero(p)}, eitw)),
        h0)
      v3c_lt_two_one_ih(p, ih, it, eit, h0z)

def v3c_sub_pow_lt(n: Nat, +k: Nat, +iw: Word(n),
  +h1: {Cmp.is_lt(Word.cmp(n, iw, v3c_mpow(n, 1n+k))) == True{} : Bool},
  +h0: {Cmp.is_lt(Word.cmp(n, iw, v3c_mpow(n, k))) == False{} : Bool})
  -> {Cmp.is_lt(Word.cmp(n, Word.sub(n, iw, v3c_mpow(n, k)), v3c_mpow(n, k))) == True{} : Bool}:
  match n:
    case 0n:
      v3c_absurd(Bool, Cmp.is_lt(Word.cmp(0n, Word.sub(0n, iw, v3c_mpow(0n, k)), v3c_mpow(0n, k))), True{}, h1)
    case 1n+ +p:
      match k:
        case 0n:
          +e1 = v3c_lt_two_one(p, iw, h1, h0)
          +g1 = Equal.cong(Word(1n+p), Bool,
            t => Cmp.is_lt(Word.cmp(1n+p, Word.sub(1n+p, t, v3c_mpow(1n+p, 0n)), v3c_mpow(1n+p, 0n))),
            iw, WCon{True{}, Word.zero(p)}, e1)
          +subz = v3c_sub_self(1n+p, WCon{True{}, Word.zero(p)})
          +g2 = Equal.cong(Word(1n+p), Bool,
            t => Cmp.is_lt(Word.cmp(1n+p, t, v3c_mpow(1n+p, 0n))),
            Word.sub(1n+p, WCon{True{}, Word.zero(p)}, v3c_mpow(1n+p, 0n)), Word.zero(1n+p), subz)
          +g3 = Equal.cong(Cmp, Bool, c => Cmp.is_lt(Word.cmp.fin(False{}, True{}, c)),
            Word.cmp(p, Word.zero(p), Word.zero(p)), EQ{}, v3c_w_cmp_refl(p, Word.zero(p)))
          Equal.trans(Bool,
            Cmp.is_lt(Word.cmp(1n+p, Word.sub(1n+p, iw, v3c_mpow(1n+p, 0n)), v3c_mpow(1n+p, 0n))),
            Cmp.is_lt(Word.cmp(1n+p, Word.sub(1n+p, WCon{True{}, Word.zero(p)}, v3c_mpow(1n+p, 0n)), v3c_mpow(1n+p, 0n))),
            True{},
            g1,
            Equal.trans(Bool,
              Cmp.is_lt(Word.cmp(1n+p, Word.sub(1n+p, WCon{True{}, Word.zero(p)}, v3c_mpow(1n+p, 0n)), v3c_mpow(1n+p, 0n))),
              Cmp.is_lt(Word.cmp(1n+p, Word.zero(1n+p), v3c_mpow(1n+p, 0n))),
              True{},
              g2, g3))
        case 1n+ +q:
          match iw:
            case WCon{+ih, +it}:
              +h1x = v3c_cmp_fin_false_lt_true(ih, Word.cmp(p, it, v3c_mpow(p, 1n+q)), h1)
              +h0x = v3c_cmp_fin_false_lt_false(ih, Word.cmp(p, it, v3c_mpow(p, q)), h0)
              +ihres = v3c_sub_pow_lt(p, q, it, h1x, h0x)
              +cmid = Word.cmp(p, Word.sub(p, it, v3c_mpow(p, q)), v3c_mpow(p, q))
              +sap = Equal.cong(Word(1n+p), Bool,
                t => Cmp.is_lt(Word.cmp(1n+p, t, WCon{False{}, v3c_mpow(p, q)})),
                Word.sub(1n+p, WCon{ih, it}, WCon{False{}, v3c_mpow(p, q)}),
                WCon{ih, Word.sub(p, it, v3c_mpow(p, q))},
                v3c_sub_even(p, ih, it, v3c_mpow(p, q)))
              Equal.trans(Bool,
                Cmp.is_lt(Word.cmp(1n+p, Word.sub(1n+p, WCon{ih, it}, v3c_mpow(1n+p, 1n+q)), v3c_mpow(1n+p, 1n+q))),
                Cmp.is_lt(Word.cmp(1n+p, WCon{ih, Word.sub(p, it, v3c_mpow(p, q))}, WCon{False{}, v3c_mpow(p, q)})),
                True{},
                sap,
                Equal.trans(Bool,
                  Cmp.is_lt(Word.cmp(1n+p, WCon{ih, Word.sub(p, it, v3c_mpow(p, q))}, WCon{False{}, v3c_mpow(p, q)})),
                  Cmp.is_lt(cmid),
                  True{},
                  v3c_cmp_fin_false_lt(ih, cmid),
                  ihres))

def v3c_not_false_true(+c: Bool, +h: {Bool.not(c) == False{} : Bool}) -> {c == True{} : Bool}:
  match c:
    case False{}: v3c_absurd(Bool, False{}, True{}, Equal.sym(Bool, True{}, False{}, h))
    case True{}: {==}

def v3c_nat_eq_reflect(+a: Nat, +b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n: {==}
    case 0n 1n+p: v3c_absurd(Nat, 0n, Nat.add(1n, p), h)
    case 1n+q 0n: v3c_absurd(Nat, Nat.add(1n, q), 0n, h)
    case 1n+q 1n+r: Equal.cong(Nat, Nat, x => Nat.add(1n, x), q, r, v3c_nat_eq_reflect(q, r, h))

def v3c_nat_ne_false_eq(+a: Nat, +b: Nat, +h: {Nat.is_ne(a, b) == False{} : Bool}) -> {a == b : Nat}:
  v3c_nat_eq_reflect(a, b, v3c_not_false_true(Nat.is_eq(a, b), h))

def v3c_lt_zero_false(+x: U32) -> {U32.is_lt(x, 0) == False{} : Bool}:
  match x:
    case U32{xw}: v3c_cmp_zero_not_lt(32n, xw)

def v3c_two_shr_of_lt_go(+k: Nat, +x: U32, +b: Bool, +hb: {b == Nat.is_ne(31n, k) : Bool}, +h: {U32.is_lt(x, v3c_two(1n+k)) == True{} : Bool})
  -> {U32.shr(v3c_two(1n+k)) == v3c_two(k) : U32}:
  match b:
    case True{}:
      v3c_two_shr_ne(k, Equal.sym(Bool, True{}, Nat.is_ne(31n, k), hb))
    case False{}:
      +hk = v3c_nat_ne_false_eq(31n, k, Equal.sym(Bool, False{}, Nat.is_ne(31n, k), hb))
      +e0 = Equal.cong(Nat, U32, j => v3c_two(1n+j), 31n, k, hk)
      +hT = Equal.trans(Bool, U32.is_lt(x, v3c_two(32n)), U32.is_lt(x, v3c_two(1n+k)), True{},
              Equal.cong(U32, Bool, y => U32.is_lt(x, y), v3c_two(32n), v3c_two(1n+k), e0),
              h)
      +hF = v3c_lt_zero_false(x)
      v3c_absurd(U32, U32.shr(v3c_two(1n+k)), v3c_two(k),
        Equal.trans(Bool, False{}, U32.is_lt(x, v3c_two(32n)), True{},
          Equal.sym(Bool, U32.is_lt(x, v3c_two(32n)), False{}, hF), hT))

def v3c_two_shr_of_lt(+k: Nat, +x: U32, +h: {U32.is_lt(x, v3c_two(1n+k)) == True{} : Bool})
  -> {U32.shr(v3c_two(1n+k)) == v3c_two(k) : U32}:
  v3c_two_shr_of_lt_go(k, x, Nat.is_ne(31n, k), {==}, h)

def v3c_sub_two_lt(+k: Nat, +i: U32,
  +h1: {U32.is_lt(i, v3c_two(1n+k)) == True{} : Bool},
  +h0: {U32.is_lt(i, v3c_two(k)) == False{} : Bool})
  -> {U32.is_lt(U32.sub(i, v3c_two(k)), v3c_two(k)) == True{} : Bool}:
  match i:
    case U32{iw}:
      +h1a = Equal.trans(Bool,
        Cmp.is_lt(Word.cmp(32n, iw, v3c_mpow(32n, 1n+k))),
        U32.is_lt(U32{iw}, v3c_two(1n+k)),
        True{},
        Equal.sym(Bool, U32.is_lt(U32{iw}, v3c_two(1n+k)), Cmp.is_lt(Word.cmp(32n, iw, v3c_mpow(32n, 1n+k))),
          Equal.cong(U32, Bool, y => U32.is_lt(U32{iw}, y), v3c_two(1n+k), U32{v3c_mpow(32n, 1n+k)}, v3c_two_mpow(1n+k))),
        h1)
      +h0a = Equal.trans(Bool,
        Cmp.is_lt(Word.cmp(32n, iw, v3c_mpow(32n, k))),
        U32.is_lt(U32{iw}, v3c_two(k)),
        False{},
        Equal.sym(Bool, U32.is_lt(U32{iw}, v3c_two(k)), Cmp.is_lt(Word.cmp(32n, iw, v3c_mpow(32n, k))),
          Equal.cong(U32, Bool, y => U32.is_lt(U32{iw}, y), v3c_two(k), U32{v3c_mpow(32n, k)}, v3c_two_mpow(k))),
        h0)
      +res = v3c_sub_pow_lt(32n, k, iw, h1a, h0a)
      +esub = Equal.cong(U32, U32, y => U32.sub(U32{iw}, y), v3c_two(k), U32{v3c_mpow(32n, k)}, v3c_two_mpow(k))
      +elt1 = Equal.cong(U32, Bool, y => U32.is_lt(y, v3c_two(k)),
        U32.sub(U32{iw}, v3c_two(k)), U32{Word.sub(32n, iw, v3c_mpow(32n, k))}, esub)
      +elt2 = Equal.cong(U32, Bool, y => U32.is_lt(U32{Word.sub(32n, iw, v3c_mpow(32n, k))}, y),
        v3c_two(k), U32{v3c_mpow(32n, k)}, v3c_two_mpow(k))
      Equal.trans(Bool,
        U32.is_lt(U32.sub(U32{iw}, v3c_two(k)), v3c_two(k)),
        U32.is_lt(U32{Word.sub(32n, iw, v3c_mpow(32n, k))}, v3c_two(k)),
        True{},
        elt1,
        Equal.trans(Bool,
          U32.is_lt(U32{Word.sub(32n, iw, v3c_mpow(32n, k))}, v3c_two(k)),
          U32.is_lt(U32{Word.sub(32n, iw, v3c_mpow(32n, k))}, U32{v3c_mpow(32n, k)}),
          True{},
          elt2, res))

def v3c_u32_add_sub(a: U32, b: U32) -> {U32.add(U32.sub(a, b), b) == a : U32}:
  match a:
    case U32{aw}:
      match b:
        case U32{bw}:
          Equal.cong(Word(32n), U32, w => U32{w}, Word.add(32n, Word.sub(32n, aw, bw), bw), aw, v3c_add_sub(32n, aw, bw))

def v3c_is_eq_sub_false_go(+a: U32, +b: U32, +h: U32, +e: Bool,
  +he: {e == U32.is_eq(U32.sub(a, h), U32.sub(b, h)) : Bool},
  +hne: {U32.is_eq(a, b) == False{} : Bool})
  -> {U32.is_eq(U32.sub(a, h), U32.sub(b, h)) == False{} : Bool}:
  match e:
    case False{}:
      Equal.sym(Bool, False{}, U32.is_eq(U32.sub(a, h), U32.sub(b, h)), he)
    case True{}:
      +hes = Equal.sym(Bool, True{}, U32.is_eq(U32.sub(a, h), U32.sub(b, h)), he)
      +esub = WR.u32_cmp_eq(U32.sub(a, h), U32.sub(b, h), hes)
      +eadd = Equal.cong(U32, U32, x => U32.add(x, h), U32.sub(a, h), U32.sub(b, h), esub)
      +ea = v3c_u32_add_sub(a, h)
      +eb = v3c_u32_add_sub(b, h)
      +eab = Equal.trans(U32, a, U32.add(U32.sub(a, h), h), b,
               Equal.sym(U32, U32.add(U32.sub(a, h), h), a, ea),
               Equal.trans(U32, U32.add(U32.sub(a, h), h), U32.add(U32.sub(b, h), h), b, eadd, eb))
      +et = Equal.trans(Bool, U32.is_eq(a, b), U32.is_eq(a, a), True{},
              Equal.cong(U32, Bool, y => U32.is_eq(a, y), b, a, Equal.sym(U32, a, b, eab)),
              v3c_is_eq_refl(a))
      +hft = Equal.trans(Bool, False{}, U32.is_eq(a, b), True{}, Equal.sym(Bool, U32.is_eq(a, b), False{}, hne), et)
      v3c_absurd(Bool, U32.is_eq(U32.sub(a, h), U32.sub(b, h)), False{}, hft)

def v3c_is_eq_sub_false(+a: U32, +b: U32, +h: U32, +hne: {U32.is_eq(a, b) == False{} : Bool})
  -> {U32.is_eq(U32.sub(a, h), U32.sub(b, h)) == False{} : Bool}:
  v3c_is_eq_sub_false_go(a, b, h, U32.is_eq(U32.sub(a, h), U32.sub(b, h)), {==}, hne)

def v3c_lt_cong_rgt_true(+i: U32, +a: U32, +b: U32, +h: {a == b : U32}, +ha: {U32.is_lt(i, a) == True{} : Bool}) -> {U32.is_lt(i, b) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(i, b), U32.is_lt(i, a), True{},
    Equal.sym(Bool, U32.is_lt(i, a), U32.is_lt(i, b), Equal.cong(U32, Bool, x => U32.is_lt(i, x), a, b, h)), ha)

def v3c_lt_cong_rgt_false(+i: U32, +a: U32, +b: U32, +h: {a == b : U32}, +ha: {U32.is_lt(i, a) == False{} : Bool}) -> {U32.is_lt(i, b) == False{} : Bool}:
  Equal.trans(Bool, U32.is_lt(i, b), U32.is_lt(i, a), False{},
    Equal.sym(Bool, U32.is_lt(i, a), U32.is_lt(i, b), Equal.cong(U32, Bool, x => U32.is_lt(i, x), a, b, h)), ha)

def v3c_lt_cong_lft_true(+a: U32, +b: U32, +c: U32, +h: {a == b : U32}, +ha: {U32.is_lt(a, c) == True{} : Bool}) -> {U32.is_lt(b, c) == True{} : Bool}:
  Equal.trans(Bool, U32.is_lt(b, c), U32.is_lt(a, c), True{},
    Equal.sym(Bool, U32.is_lt(a, c), U32.is_lt(b, c), Equal.cong(U32, Bool, x => U32.is_lt(x, c), a, b, h)), ha)

def v3c_pick_fl(+nzi: Bool, +nzj: Bool, +zi: Bool, +zj: Bool,
  +hzi: {zi == False{} : Bool}, +hzj: {zj == True{} : Bool})
  -> {Bool.pick(Bool, zi, Bool.pick(Bool, zj, nzi, True{}), Bool.pick(Bool, zj, True{}, nzj)) == True{} : Bool}:
  +A = Bool.pick(Bool, zj, nzi, True{})
  +B = Bool.pick(Bool, zj, True{}, nzj)
  +e1 = Equal.cong(Bool, Bool, b => Bool.pick(Bool, b, A, B), zi, False{}, hzi)
  +eB = Equal.cong(Bool, Bool, b => Bool.pick(Bool, b, True{}, nzj), zj, True{}, hzj)
  Equal.trans(Bool, Bool.pick(Bool, zi, A, B), B, True{}, e1, eB)

def v3c_ne_idx_sep_fl(+xs: R.PT, +ys: R.PT, +n: U32, +i: U32, +j: U32,
  +hzi: {U32.is_lt(i, U32.shr(n)) == False{} : Bool},
  +hzj: {U32.is_lt(j, U32.shr(n)) == True{} : Bool})
  -> {ne_idx(R.PN{xs, ys}, n, i, j) == True{} : Bool}:
  +h = U32.shr(n)
  +nzi = ne_idx(xs, h, i, j)
  +nzj = ne_idx(ys, h, U32.sub(i, h), U32.sub(j, h))
  v3c_pick_fl(nzi, nzj, U32.is_lt(i, h), U32.is_lt(j, h), hzi, hzj)

def v3c_ne_idx_complete_node(+p: Nat, +i: U32, +j: U32,
  +zi: Bool, +zj: Bool,
  +hzi: {zi == U32.is_lt(i, U32.shr(v3c_two(1n+p))) : Bool},
  +hzj: {zj == U32.is_lt(j, U32.shr(v3c_two(1n+p))) : Bool},
  +hi: {U32.is_lt(i, v3c_two(1n+p)) == True{} : Bool},
  +hj: {U32.is_lt(j, v3c_two(1n+p)) == True{} : Bool},
  +hne: {U32.is_eq(i, j) == False{} : Bool},
  ihL: {U32.is_lt(i, v3c_two(p)) == True{} : Bool} ->
       {U32.is_lt(j, v3c_two(p)) == True{} : Bool} ->
       {U32.is_eq(i, j) == False{} : Bool} ->
       {ne_idx(v3c_full(p), v3c_two(p), i, j) == True{} : Bool},
  ihR: {U32.is_lt(U32.sub(i, U32.shr(v3c_two(1n+p))), v3c_two(p)) == True{} : Bool} ->
       {U32.is_lt(U32.sub(j, U32.shr(v3c_two(1n+p))), v3c_two(p)) == True{} : Bool} ->
       {U32.is_eq(U32.sub(i, U32.shr(v3c_two(1n+p))), U32.sub(j, U32.shr(v3c_two(1n+p)))) == False{} : Bool} ->
       {ne_idx(v3c_full(p), v3c_two(p), U32.sub(i, U32.shr(v3c_two(1n+p))), U32.sub(j, U32.shr(v3c_two(1n+p)))) == True{} : Bool})
  -> {ne_idx(R.PN{v3c_full(p), v3c_full(p)}, v3c_two(1n+p), i, j) == True{} : Bool}:
  match zi:
    case True{}:
      match zj:
        case True{}:
          +esh_i = v3c_two_shr_of_lt(p, i, hi)
          +esh_j = v3c_two_shr_of_lt(p, j, hj)
          +hziT = Equal.sym(Bool, True{}, U32.is_lt(i, U32.shr(v3c_two(1n+p))), hzi)
          +hzjT = Equal.sym(Bool, True{}, U32.is_lt(j, U32.shr(v3c_two(1n+p))), hzj)
          +esl = v3c_ne_idx_same_l(v3c_full(p), v3c_full(p), v3c_two(1n+p), i, j, hziT, hzjT)
          +econg = Equal.cong(U32, Bool, x => ne_idx(v3c_full(p), x, i, j), U32.shr(v3c_two(1n+p)), v3c_two(p), esh_i)
          +hip = v3c_lt_cong_rgt_true(i, U32.shr(v3c_two(1n+p)), v3c_two(p), esh_i, hziT)
          +hjp = v3c_lt_cong_rgt_true(j, U32.shr(v3c_two(1n+p)), v3c_two(p), esh_j, hzjT)
          +ihres = ihL(hip, hjp, hne)
          Equal.trans(Bool,
            ne_idx(R.PN{v3c_full(p), v3c_full(p)}, v3c_two(1n+p), i, j),
            ne_idx(v3c_full(p), U32.shr(v3c_two(1n+p)), i, j),
            True{},
            esl,
            Equal.trans(Bool,
              ne_idx(v3c_full(p), U32.shr(v3c_two(1n+p)), i, j),
              ne_idx(v3c_full(p), v3c_two(p), i, j),
              True{},
              econg, ihres))
        case False{}:
          +hziT = Equal.sym(Bool, True{}, U32.is_lt(i, U32.shr(v3c_two(1n+p))), hzi)
          +hzjF = Equal.sym(Bool, False{}, U32.is_lt(j, U32.shr(v3c_two(1n+p))), hzj)
          v3c_ne_idx_sep(v3c_full(p), v3c_full(p), v3c_two(1n+p), i, j, hziT, hzjF)
    case False{}:
      match zj:
        case True{}:
          +hziF = Equal.sym(Bool, False{}, U32.is_lt(i, U32.shr(v3c_two(1n+p))), hzi)
          +hzjT = Equal.sym(Bool, True{}, U32.is_lt(j, U32.shr(v3c_two(1n+p))), hzj)
          v3c_ne_idx_sep_fl(v3c_full(p), v3c_full(p), v3c_two(1n+p), i, j, hziF, hzjT)
        case False{}:
          +esh_i = v3c_two_shr_of_lt(p, i, hi)
          +esh_j = v3c_two_shr_of_lt(p, j, hj)
          +hziF = Equal.sym(Bool, False{}, U32.is_lt(i, U32.shr(v3c_two(1n+p))), hzi)
          +hzjF = Equal.sym(Bool, False{}, U32.is_lt(j, U32.shr(v3c_two(1n+p))), hzj)
          +h = U32.shr(v3c_two(1n+p))
          +esi = U32.sub(i, h)
          +esj = U32.sub(j, h)
          +esr = v3c_ne_idx_same_r(v3c_full(p), v3c_full(p), v3c_two(1n+p), i, j, hziF, hzjF)
          +econg = Equal.cong(U32, Bool, x => ne_idx(v3c_full(p), x, esi, esj), h, v3c_two(p), esh_i)
          +h0i = v3c_lt_cong_rgt_false(i, h, v3c_two(p), esh_i, hziF)
          +h0j = v3c_lt_cong_rgt_false(j, h, v3c_two(p), esh_j, hzjF)
          +esub_i = Equal.cong(U32, U32, x => U32.sub(i, x), h, v3c_two(p), esh_i)
          +esub_j = Equal.cong(U32, U32, x => U32.sub(j, x), h, v3c_two(p), esh_j)
          +hri = v3c_lt_cong_lft_true(U32.sub(i, v3c_two(p)), esi, v3c_two(p), Equal.sym(U32, esi, U32.sub(i, v3c_two(p)), esub_i), v3c_sub_two_lt(p, i, hi, h0i))
          +hrj = v3c_lt_cong_lft_true(U32.sub(j, v3c_two(p)), esj, v3c_two(p), Equal.sym(U32, esj, U32.sub(j, v3c_two(p)), esub_j), v3c_sub_two_lt(p, j, hj, h0j))
          +hnesub = v3c_is_eq_sub_false(i, j, h, hne)
          +ihres = ihR(hri, hrj, hnesub)
          Equal.trans(Bool,
            ne_idx(R.PN{v3c_full(p), v3c_full(p)}, v3c_two(1n+p), i, j),
            ne_idx(v3c_full(p), h, esi, esj),
            True{},
            esr,
            Equal.trans(Bool,
              ne_idx(v3c_full(p), h, esi, esj),
              ne_idx(v3c_full(p), v3c_two(p), esi, esj),
              True{},
              econg, ihres))

def v3c_ne_idx_complete_imp(+k: Nat, +i: U32, +j: U32,
  +hi: {U32.is_lt(i, v3c_two(k)) == True{} : Bool},
  +hj: {U32.is_lt(j, v3c_two(k)) == True{} : Bool},
  +hne: {U32.is_eq(i, j) == False{} : Bool})
  -> {ne_idx(v3c_full(k), v3c_two(k), i, j) == True{} : Bool}:
  match k:
    case 0n:
      +ei = v3c_lt_one_u32(i, hi)
      +ej = v3c_lt_one_u32(j, hj)
      +eij = Equal.trans(Bool, U32.is_eq(i, j), U32.is_eq(0, 0), True{},
               Equal.trans(Bool, U32.is_eq(i, j), U32.is_eq(0, j), U32.is_eq(0, 0),
                 Equal.cong(U32, Bool, x => U32.is_eq(x, j), i, 0, ei),
                 Equal.cong(U32, Bool, y => U32.is_eq(0, y), j, 0, ej)),
               v3c_is_eq_refl(0))
      +hft = Equal.trans(Bool, False{}, U32.is_eq(i, j), True{}, Equal.sym(Bool, U32.is_eq(i, j), False{}, hne), eij)
      v3c_absurd(Bool, ne_idx(v3c_full(0n), v3c_two(0n), i, j), True{}, hft)
    case 1n+ +p:
      v3c_ne_idx_complete_node(p, i, j,
        U32.is_lt(i, U32.shr(v3c_two(1n+p))), U32.is_lt(j, U32.shr(v3c_two(1n+p))),
        {==}, {==}, hi, hj, hne,
        h1 => h2 => h3 => v3c_ne_idx_complete_imp(p, i, j, h1, h2, h3),
        h1 => h2 => h3 => v3c_ne_idx_complete_imp(p, U32.sub(i, U32.shr(v3c_two(1n+p))), U32.sub(j, U32.shr(v3c_two(1n+p))), h1, h2, h3))

def v3c_ne_idx_exact_go(+k: Nat, +i: U32, +j: U32, +e: Bool,
  +he: {e == U32.is_eq(i, j) : Bool},
  +hi: {U32.is_lt(i, v3c_two(k)) == True{} : Bool},
  +hj: {U32.is_lt(j, v3c_two(k)) == True{} : Bool})
  -> {ne_idx(v3c_full(k), v3c_two(k), i, j) == Bool.not(U32.is_eq(i, j)) : Bool}:
  match e:
    case True{}:
      +hes = Equal.sym(Bool, True{}, U32.is_eq(i, j), he)
      +hsound = v3c_ne_idx_sound(v3c_full(k), v3c_two(k), i, j, hes)
      +econg = Equal.cong(Bool, Bool, Bool.not, U32.is_eq(i, j), True{}, hes)
      Equal.trans(Bool,
        ne_idx(v3c_full(k), v3c_two(k), i, j), False{}, Bool.not(U32.is_eq(i, j)),
        hsound,
        Equal.sym(Bool, Bool.not(U32.is_eq(i, j)), False{}, econg))
    case False{}:
      +hes = Equal.sym(Bool, False{}, U32.is_eq(i, j), he)
      +hcomp = v3c_ne_idx_complete_imp(k, i, j, hi, hj, hes)
      +econg = Equal.cong(Bool, Bool, Bool.not, U32.is_eq(i, j), False{}, hes)
      Equal.trans(Bool,
        ne_idx(v3c_full(k), v3c_two(k), i, j), True{}, Bool.not(U32.is_eq(i, j)),
        hcomp,
        Equal.sym(Bool, Bool.not(U32.is_eq(i, j)), True{}, econg))

def v3c_ne_idx_exact(+k: Nat, +i: U32, +j: U32,
  +hi: {U32.is_lt(i, v3c_two(k)) == True{} : Bool},
  +hj: {U32.is_lt(j, v3c_two(k)) == True{} : Bool})
  -> {ne_idx(v3c_full(k), v3c_two(k), i, j) == Bool.not(U32.is_eq(i, j)) : Bool}:
  v3c_ne_idx_exact_go(k, i, j, U32.is_eq(i, j), {==}, hi, hj)
