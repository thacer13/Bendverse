import Base
import ./refine.bend as R
import ./g5.bend as G5
import ./count.bend as C
import ./rules.bend as Rul
import ./commit.bend as Commit

# ============================================================================
# V3c/G3 — wiring the engine's write list into the schedule-invariance fold.
#
# `V3c-1b` (`src/commit.bend`) proves the list/region equality for the abstract
# write list `List<Commit.V3cWrite>` folded by `Commit.v3c_fold` through the
# engine-facing `Refine.swap_m` (the `Array.set` presentation). What was left
# (`PLAN.md` §5.3, `G3`) is the *bridge to the engine*: the engine does not fold a
# `V3cWrite` list, it folds a `List<Rules.Write>` — `Rules.commit_sets`, where
#
#   WSet{idx, op, src}  ->  world[idx] <- Rules.apply_op(src, op)
#   WWake{idx}          ->  the world is unchanged (a wake is applied later, at
#                           tick end, by `Sim.commit_wakes_mask`)
#
# This module defines the projection `v3cw_proj` from the engine's write list to
# the fold's write list and proves that the engine's sequential commit equals the
# abstract fold on that projection. `v3c_fold_commutes` then applies verbatim to
# the engine's actual write set.
#
# Three facts make the bridge go through:
#
#   * a `WSet` step of the engine is a *point write of the projected value*, so
#     `Array.set(pack t, i, v)` is `pack(swap_m(t, n, i, v))` once `n` is the
#     tree's own width (`g5_twidth`) and `i` is in range — `v3cw_set_swap`, built
#     from `g5_size_pack` + `g5_and_mask_id` + `Count.afst_swap_m`;
#   * `v3cw_twidth_swap_m` keeps the width fixed across a write, so the
#     in-range hypothesis survives the induction;
#   * `WWake` steps are the identity on both sides, so they are simply dropped
#     by the projection (state/Φ-neutral *for the set fold*; the tick's wake
#     pass reads them, and is out of scope here).
#
# Multiplicity note. `Rules.commit_sets` consumes its list *linearly* (`&1`),
# while the abstract fold's distinctness/region lemmas need a *reusable* list
# (`&2`, e.g. `Commit.v3c_pair_ne(xs, ys, …)` and `List.append` both use the list
# twice). `v3cw_lin` is the multiplicity-erased copy: it rebuilds the same
# `Rules.Write` list as a linear value. It is operationally the identity on the
# engine's write data; it exists only so a single law can mention the engine
# commit and the fold at once without changing the engine signature.
# ============================================================================

# ------------------------------------------------------------------ projection
# `rules -> fold` write list: a `WSet` becomes a point write of its effect
# (`apply_op`), a `WWake` is dropped (identity on the set fold).
def v3cw_proj(+ws: +List<Rul.Write>) -> +List<Commit.V3cWrite>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+h, +tl}:
      match h:
        case Rul.WSet{idx, op, src}:
          Commit.MkWrite{idx, Rul.apply_op(src, op)} <> v3cw_proj(tl)
        case Rul.WWake{idx}:
          v3cw_proj(tl)

# The linear copy of the engine's write list (see the multiplicity note above).
def v3cw_lin(+ws: +List<Rul.Write>) -> List<Rul.Write>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+h, +tl}:
      h <> v3cw_lin(tl)

# In-range predicate: every `WSet` index is a valid leaf of a `2^n`-leaf world.
# (`WWake` indices are not writes and are ignored.)
def v3cw_in_range(+ws: +List<Rul.Write>, +n: U32) -> Bool:
  match ws:
    case Nil{}:
      True{}
    case Con{+h, +tl}:
      match h:
        case Rul.WSet{idx, op, src}:
          Commit.v3c_band(U32.is_lt(idx, n), v3cw_in_range(tl, n))
        case Rul.WWake{idx}:
          v3cw_in_range(tl, n)

# ------------------------------------------------------------------ the step
# `Array.set.fin` is the pair's first projection (`Refine.afst`).
def v3cw_setfin_afst(r: Array<U32> & U32) -> {Array.set.fin(U32, r) == R.afst(r) : Array<U32>}:
  match r:
    case (na, old): {==}

# The engine's point write is the model's `swap_m`, on a full `pack t` whose
# width is `n` and at an in-range index. This is the only place the engine's
# `Array.set` (with its size/mask wrapper) meets `Refine.swap_m`.
def v3cw_set_swap(+t: R.PT, +n: U32, +i: U32, +v: U32,
  +hn: {n == G5.g5_twidth(t) : U32},
  +hi: {U32.is_lt(i, n) == True{} : Bool})
  -> {Array.set(U32, R.pack(t), i, v) == R.pack(R.swap_m(t, n, i, v)) : Array<U32>}:
  +TW = G5.g5_twidth(t)
  +hiw = Equal.trans(Bool, U32.is_lt(i, TW), U32.is_lt(i, n), True{},
           Equal.sym(Bool, U32.is_lt(i, n), U32.is_lt(i, TW),
             Equal.cong(U32, Bool, x => U32.is_lt(i, x), n, TW, hn)),
           hi)
  +hmask = G5.g5_and_mask_id(t, i, hiw)
  +esz = G5.g5_size_pack(t)
  +e1 = Equal.cong(Array<U32> & U32, Array<U32>,
          r => Array.set.fin(U32, Array.swap.at(U32, i, v, r)),
          Array.size(U32, R.pack(t)), (R.pack(t), TW), esz)
  +e2a = v3cw_setfin_afst(Array.swap.at(U32, i, v, (R.pack(t), TW)))
  +e2 = Equal.trans(Array<U32>,
          Array.set.fin(U32, Array.swap.at(U32, i, v, (R.pack(t), TW))),
          R.afst(Array.swap.at(U32, i, v, (R.pack(t), TW))),
          R.afst(Array.swap.go(U32, R.pack(t), TW, U32.and(i, U32.sub(TW, 1)), v)),
          e2a, {==})
  +e3 = Equal.cong(U32, Array<U32>,
          x => R.afst(Array.swap.go(U32, R.pack(t), TW, x, v)),
          U32.and(i, U32.sub(TW, 1)), i, hmask)
  +e4a = Equal.cong(U32, Array<U32>,
          w => R.afst(Array.swap.go(U32, R.pack(t), w, i, v)),
          TW, n, Equal.sym(U32, n, TW, hn))
  +e4 = Equal.trans(Array<U32>,
          R.afst(Array.swap.go(U32, R.pack(t), TW, i, v)),
          R.afst(Array.swap.go(U32, R.pack(t), n, i, v)),
          R.pack(R.swap_m(t, n, i, v)),
          e4a, C.afst_swap_m(t, n, i, v))
  Equal.trans(Array<U32>,
    Array.set(U32, R.pack(t), i, v),
    Array.set.fin(U32, Array.swap.at(U32, i, v, (R.pack(t), TW))),
    R.pack(R.swap_m(t, n, i, v)),
    e1,
    Equal.trans(Array<U32>,
      Array.set.fin(U32, Array.swap.at(U32, i, v, (R.pack(t), TW))),
      R.afst(Array.swap.go(U32, R.pack(t), TW, U32.and(i, U32.sub(TW, 1)), v)),
      R.pack(R.swap_m(t, n, i, v)),
      e2,
      Equal.trans(Array<U32>,
        R.afst(Array.swap.go(U32, R.pack(t), TW, U32.and(i, U32.sub(TW, 1)), v)),
        R.afst(Array.swap.go(U32, R.pack(t), TW, i, v)),
        R.pack(R.swap_m(t, n, i, v)),
        e3, e4)))

# ------------------------------------------------------------------ width is a shape invariant
# `g5_twidth` reads only the leftmost spine, so a write (which preserves the
# `PL`/`PN` shape) preserves it. Needed to carry `n == g5_twidth t` across the
# induction.
def v3cw_twidth_pick(+z: Bool, A: R.PT, B: R.PT)
  -> {G5.g5_twidth(Bool.pick(R.PT, z, A, B)) == Bool.pick(U32, z, G5.g5_twidth(A), G5.g5_twidth(B)) : U32}:
  match z:
    case True{}: {==}
    case False{}: {==}

def v3cw_mkt(A: R.PT, B: R.PT) -> R.PT:
  R.PN{A, B}

def v3cw_pick_same_u32(+z: Bool, +b: U32) -> {Bool.pick(U32, z, b, b) == b : U32}:
  match z:
    case True{}: {==}
    case False{}: {==}

def v3cw_pick_cong2_u32(+z: Bool, +a1: U32, +a2: U32, +b1: U32, +b2: U32,
  +ha: {a1 == a2 : U32}, +hb: {b1 == b2 : U32})
  -> {Bool.pick(U32, z, a1, b1) == Bool.pick(U32, z, a2, b2) : U32}:
  Equal.trans(U32,
    Bool.pick(U32, z, a1, b1),
    Bool.pick(U32, z, a2, b1),
    Bool.pick(U32, z, a2, b2),
    Equal.cong(U32, U32, x => Bool.pick(U32, z, x, b1), a1, a2, ha),
    Equal.cong(U32, U32, x => Bool.pick(U32, z, a2, x), b1, b2, hb))

def v3cw_twidth_swap_m(+t: R.PT, +n: U32, +i: U32, +v: U32)
  -> {G5.g5_twidth(R.swap_m(t, n, i, v)) == G5.g5_twidth(t) : U32}:
  match t:
    case R.PL{x}: {==}
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      +A = v3cw_mkt(R.swap_m(xs, h, i, v), ys)
      +B = v3cw_mkt(xs, R.swap_m(ys, h, U32.sub(i, h), v))
      +ihx = v3cw_twidth_swap_m(xs, h, i, v)
      +eA = Equal.cong(U32, U32, U32.shl, G5.g5_twidth(R.swap_m(xs, h, i, v)), G5.g5_twidth(xs), ihx)
      +e1 = v3cw_twidth_pick(z, A, B)
      +e2 = v3cw_pick_cong2_u32(z, G5.g5_twidth(A), U32.shl(G5.g5_twidth(xs)), G5.g5_twidth(B), U32.shl(G5.g5_twidth(xs)), eA, {==})
      +e3 = v3cw_pick_same_u32(z, U32.shl(G5.g5_twidth(xs)))
      Equal.trans(U32,
        G5.g5_twidth(Bool.pick(R.PT, z, A, B)),
        Bool.pick(U32, z, G5.g5_twidth(A), G5.g5_twidth(B)),
        G5.g5_twidth(R.PN{xs, ys}),
        e1,
        Equal.trans(U32,
          Bool.pick(U32, z, G5.g5_twidth(A), G5.g5_twidth(B)),
          Bool.pick(U32, z, U32.shl(G5.g5_twidth(xs)), U32.shl(G5.g5_twidth(xs))),
          G5.g5_twidth(R.PN{xs, ys}),
          e2,
          Equal.trans(U32,
            Bool.pick(U32, z, U32.shl(G5.g5_twidth(xs)), U32.shl(G5.g5_twidth(xs))),
            U32.shl(G5.g5_twidth(xs)),
            G5.g5_twidth(R.PN{xs, ys}),
            e3, {==})))

# ------------------------------------------------------------------ the bridge
# The engine's sequential commit (`Rules.commit_sets`) on the linear copy of a
# reusable write list equals the abstract fold of its projection. `hn` pins the
# fold's size to the tree's own width (`g5_twidth`), and `hir` keeps every write
# in range — the two hypotheses the `Array.set` presentation needs.
def v3cw_commit_fold(+ws: +List<Rul.Write>, +t: R.PT, +n: U32,
  +hn: {n == G5.g5_twidth(t) : U32},
  +hir: {v3cw_in_range(ws, n) == True{} : Bool})
  -> {R.unpack(Rul.commit_sets(v3cw_lin(ws), R.pack(t))) == Commit.v3c_fold(v3cw_proj(ws), t, n) : R.PT}:
  match ws:
    case Nil{}:
      R.unpack_pack(t)
    case Con{+h, +tl}:
      match h:
        case Rul.WSet{idx, op, src}:
          +val = Rul.apply_op(src, op)
          +hi = Commit.v3c_and_true_l(U32.is_lt(idx, n), v3cw_in_range(tl, n), hir)
          +hir_tl = Commit.v3c_and_true_r(U32.is_lt(idx, n), v3cw_in_range(tl, n), hir)
          +e_set = v3cw_set_swap(t, n, idx, val, hn, hi)
          +t1 = R.swap_m(t, n, idx, val)
          +e_cong = Equal.cong(Array<U32>, R.PT, a => R.unpack(Rul.commit_sets(v3cw_lin(tl), a)),
                      Array.set(U32, R.pack(t), idx, val), R.pack(t1), e_set)
          +e_tw = v3cw_twidth_swap_m(t, n, idx, val)
          +hn1 = Equal.trans(U32, n, G5.g5_twidth(t), G5.g5_twidth(t1), hn, Equal.sym(U32, G5.g5_twidth(t1), G5.g5_twidth(t), e_tw))
          +e_ih = v3cw_commit_fold(tl, t1, n, hn1, hir_tl)
          Equal.trans(R.PT,
            R.unpack(Rul.commit_sets(v3cw_lin(Con{Rul.WSet{idx, op, src}, tl}), R.pack(t))),
            R.unpack(Rul.commit_sets(v3cw_lin(tl), R.pack(t1))),
            Commit.v3c_fold(v3cw_proj(Con{Rul.WSet{idx, op, src}, tl}), t, n),
            e_cong,
            e_ih)
        case Rul.WWake{idx}:
          v3cw_commit_fold(tl, t, n, hn, hir)

# ------------------------------------------------------------------ region split
# The projection distributes over append, so the fold law can be applied to the
# engine's write set split into regions.
def v3cw_proj_append(+xs: +List<Rul.Write>, +ys: +List<Rul.Write>)
  -> {v3cw_proj(List.append(&2, Rul.Write, xs, ys)) == List.append(&2, Commit.V3cWrite, v3cw_proj(xs), v3cw_proj(ys)) : +List<Commit.V3cWrite>}:
  match xs:
    case Nil{}: {==}
    case Con{+h, +tl}:
      match h:
        case Rul.WSet{idx, op, src}:
          Equal.cong(+List<Commit.V3cWrite>, +List<Commit.V3cWrite>,
            t2 => Commit.MkWrite{idx, Rul.apply_op(src, op)} <> t2,
            v3cw_proj(List.append(&2, Rul.Write, tl, ys)),
            List.append(&2, Commit.V3cWrite, v3cw_proj(tl), v3cw_proj(ys)),
            v3cw_proj_append(tl, ys))
        case Rul.WWake{idx}:
          v3cw_proj_append(tl, ys)

# The engine-level region-split equality: two regions' write lists (on the
# multiplicity-erased copy) commit to the same `Refine.PT` in either order,
# provided their projections target pairwise-distinct leaves. This is
# `Commit.v3c_fold_commutes` transported through `v3cw_commit_fold`.
def v3cw_commit_commutes(+xs: +List<Rul.Write>, +ys: +List<Rul.Write>,
  +t: R.PT, +n: U32,
  +hn: {n == G5.g5_twidth(t) : U32},
  +hxy: {v3cw_in_range(List.append(&2, Rul.Write, xs, ys), n) == True{} : Bool},
  +hyx: {v3cw_in_range(List.append(&2, Rul.Write, ys, xs), n) == True{} : Bool},
  +hpn: {Commit.v3c_pair_ne(v3cw_proj(xs), v3cw_proj(ys), t, n) == True{} : Bool})
  -> {R.unpack(Rul.commit_sets(v3cw_lin(List.append(&2, Rul.Write, xs, ys)), R.pack(t)))
        == R.unpack(Rul.commit_sets(v3cw_lin(List.append(&2, Rul.Write, ys, xs)), R.pack(t))) : R.PT}:
  +e1 = v3cw_commit_fold(List.append(&2, Rul.Write, xs, ys), t, n, hn, hxy)
  +e2 = v3cw_commit_fold(List.append(&2, Rul.Write, ys, xs), t, n, hn, hyx)
  +ep1 = v3cw_proj_append(xs, ys)
  +ep2 = v3cw_proj_append(ys, xs)
  +efold = Commit.v3c_fold_commutes(v3cw_proj(xs), v3cw_proj(ys), t, n, hpn)
  +c1 = Equal.cong(+List<Commit.V3cWrite>, R.PT, l => Commit.v3c_fold(l, t, n),
          v3cw_proj(List.append(&2, Rul.Write, xs, ys)),
          List.append(&2, Commit.V3cWrite, v3cw_proj(xs), v3cw_proj(ys)), ep1)
  +c2 = Equal.cong(+List<Commit.V3cWrite>, R.PT, l => Commit.v3c_fold(l, t, n),
          List.append(&2, Commit.V3cWrite, v3cw_proj(ys), v3cw_proj(xs)),
          v3cw_proj(List.append(&2, Rul.Write, ys, xs)),
          Equal.sym(+List<Commit.V3cWrite>,
            v3cw_proj(List.append(&2, Rul.Write, ys, xs)),
            List.append(&2, Commit.V3cWrite, v3cw_proj(ys), v3cw_proj(xs)), ep2))
  Equal.trans(R.PT,
    R.unpack(Rul.commit_sets(v3cw_lin(List.append(&2, Rul.Write, xs, ys)), R.pack(t))),
    Commit.v3c_fold(v3cw_proj(List.append(&2, Rul.Write, xs, ys)), t, n),
    R.unpack(Rul.commit_sets(v3cw_lin(List.append(&2, Rul.Write, ys, xs)), R.pack(t))),
    e1,
    Equal.trans(R.PT,
      Commit.v3c_fold(v3cw_proj(List.append(&2, Rul.Write, xs, ys)), t, n),
      Commit.v3c_fold(List.append(&2, Commit.V3cWrite, v3cw_proj(xs), v3cw_proj(ys)), t, n),
      R.unpack(Rul.commit_sets(v3cw_lin(List.append(&2, Rul.Write, ys, xs)), R.pack(t))),
      c1,
      Equal.trans(R.PT,
        Commit.v3c_fold(List.append(&2, Commit.V3cWrite, v3cw_proj(xs), v3cw_proj(ys)), t, n),
        Commit.v3c_fold(List.append(&2, Commit.V3cWrite, v3cw_proj(ys), v3cw_proj(xs)), t, n),
        R.unpack(Rul.commit_sets(v3cw_lin(List.append(&2, Rul.Write, ys, xs)), R.pack(t))),
        efold,
        Equal.trans(R.PT,
          Commit.v3c_fold(List.append(&2, Commit.V3cWrite, v3cw_proj(ys), v3cw_proj(xs)), t, n),
          Commit.v3c_fold(v3cw_proj(List.append(&2, Rul.Write, ys, xs)), t, n),
          R.unpack(Rul.commit_sets(v3cw_lin(List.append(&2, Rul.Write, ys, xs)), R.pack(t))),
          c2,
          Equal.sym(R.PT,
            R.unpack(Rul.commit_sets(v3cw_lin(List.append(&2, Rul.Write, ys, xs)), R.pack(t))),
            Commit.v3c_fold(v3cw_proj(List.append(&2, Rul.Write, ys, xs)), t, n),
            e2)))))
