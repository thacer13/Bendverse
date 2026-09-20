import Base
import ./refine.bend as R
import ./tick.bend as Tick

# G5 (read threading): the read companion of `R.swap_ref`.
#
# The `G10`/`G14` closures enumerated and typed the *writes* the tick performs;
# what was left of the `G5` caveat ("laws constrain models, not the imperative
# `Array` engine") was the *reads*: `Tick.tget(t, n, i)` is how the live `PT`
# mirror `sup_m` reads a cell (the `Rules.step` mirror `step_m` is retired,
# A.63), while `Support.sup`/`Rules.plan` read
# `Array.get(U32, world, i)`. Base's `Array.get.go` walks a tree with the same
# `h = n/2` / `U32.is_lt(i, h)` recursion as `tget` (and as `swap_m`, which
# `swap_ref` already bridges to `Array.swap.go`), so the two reads coincide at
# every index. This file proves that, unconditionally in `n`:
#
#   * `g5_tget_get_go`  : `Array.get.go(pack t, n, i)` reads `tget(t, n, i)`;
#   * `g5_size_pack`    : `Array.size(pack t)` is `(pack t, g5_twidth t)`, so the
#                         `Array.get`/`Array.swap` size/mask wrapper is threaded;
#   * `g5_read_get`     : the composed engine read `Array.get(U32, pack t, i)`;
#   * `g5_tget_swap`    : read-after-write at the selector's index
#                         (`q = Array.get(world, i)` after `world[i] <- v`,
#                         `Support.sup` cases 3/4/6).
#
# The only residual is the standard array-index mask `i & (size - 1) == i` for an
# in-range `i` on a power-of-two world (see LAWS.bend / the report); it is a fact
# about `U32`, not about the mirror, and is not needed to state the read law.

# `Array.get.go` at a node: `Array.get.if` picks the same branch as `tget`'s
# `Bool.pick`, and `Array.swap.lo`/`hi` rebuild exactly `ANode{pack xs, pack ys}`
# when the recursive read is rewritten by the induction hypothesis.
def g5_tget_get_if(
  +xs: R.PT, +ys: R.PT, +h: U32, +i: U32, +z: Bool,
  ihx: {Array.get.go(U32, R.pack(xs), h, i) == (R.pack(xs), Tick.tget(xs, h, i)) : Array<U32> & U32},
  ihy: {Array.get.go(U32, R.pack(ys), h, U32.sub(i, h)) == (R.pack(ys), Tick.tget(ys, h, U32.sub(i, h))) : Array<U32> & U32}
) -> {Array.get.if(U32, R.pack(xs), R.pack(ys), h, i, z) == (ANode{R.pack(xs), R.pack(ys)}, Bool.pick(U32, z, Tick.tget(xs, h, i), Tick.tget(ys, h, U32.sub(i, h)))) : Array<U32> & U32}:
  match z:
    case True{}:
      Equal.cong(Array<U32> & U32, Array<U32> & U32,
        r => Array.swap.lo(U32, R.pack(ys), r),
        Array.get.go(U32, R.pack(xs), h, i),
        (R.pack(xs), Tick.tget(xs, h, i)),
        ihx)
    case False{}:
      Equal.cong(Array<U32> & U32, Array<U32> & U32,
        r => Array.swap.hi(U32, R.pack(xs), r),
        Array.get.go(U32, R.pack(ys), h, U32.sub(i, h)),
        (R.pack(ys), Tick.tget(ys, h, U32.sub(i, h))),
        ihy)

# The engine's array read primitive at level-size `n` is the mirror's `tget`.
def g5_tget_get_go(t: R.PT, +n: U32, +i: U32)
  -> {Array.get.go(U32, R.pack(t), n, i) == (R.pack(t), Tick.tget(t, n, i)) : Array<U32> & U32}:
  match t:
    case R.PL{x}: {==}
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      g5_tget_get_if(xs, ys, h, i, z,
        g5_tget_get_go(xs, h, i),
        g5_tget_get_go(ys, h, U32.sub(i, h)))

# The level-size of a `PT`: `Array.size` doubles the *left* subtree width, which
# is what the `pack`ed tree's shape gives (a `PN`'s size ignores its right half,
# exactly `Array.size.node`).
def g5_twidth(t: R.PT) -> U32:
  match t:
    case R.PL{x}: 1
    case R.PN{+xs, +ys}: U32.shl(g5_twidth(xs))

# `Array.size(pack t)` is `(pack t, g5_twidth t)` — the size half of the
# `Array.get`/`Array.swap` wrapper, so the engine's masking index is
# `i & (g5_twidth t - 1)`.
def g5_size_pack(t: R.PT)
  -> {Array.size(U32, R.pack(t)) == (R.pack(t), g5_twidth(t)) : Array<U32> & U32}:
  match t:
    case R.PL{x}: {==}
    case R.PN{+xs, +ys}:
      Equal.cong(Array<U32> & U32, Array<U32> & U32,
        r => Array.size.node(U32, R.pack(ys), r),
        Array.size(U32, R.pack(xs)),
        (R.pack(xs), g5_twidth(xs)),
        g5_size_pack(xs))

# The composed engine read: `Array.get` is `get.go` at `Array.size`, with the
# index masked to range.
def g5_read_get(+t: R.PT, +i: U32)
  -> {Array.get(U32, R.pack(t), i) == (R.pack(t), Tick.tget(t, g5_twidth(t), U32.and(i, U32.sub(g5_twidth(t), 1)))) : Array<U32> & U32}:
  +e1 = Equal.cong(Array<U32> & U32, Array<U32> & U32,
          r => Array.get.at(U32, i, r),
          Array.size(U32, R.pack(t)),
          (R.pack(t), g5_twidth(t)),
          g5_size_pack(t))
  +e2 = g5_tget_get_go(t, g5_twidth(t), U32.and(i, U32.sub(g5_twidth(t), 1)))
  Equal.trans(Array<U32> & U32,
    Array.get(U32, R.pack(t), i),
    Array.get.at(U32, i, (R.pack(t), g5_twidth(t))),
    (R.pack(t), Tick.tget(t, g5_twidth(t), U32.and(i, U32.sub(g5_twidth(t), 1)))),
    e1, e2)

# `tget`/`swap_m` do not reduce through a `Bool.pick`, so a read-back after a
# write is stuck unless the write's decision is exposed. (Companion of
# `swap_m_pick` / `Count.tget_pick`.)
def g5_tget_pick(+z: Bool, A: R.PT, B: R.PT, n: U32, +i: U32)
  -> {Tick.tget(Bool.pick(R.PT, z, A, B), n, i) == Bool.pick(U32, z, Tick.tget(A, n, i), Tick.tget(B, n, i)) : U32}:
  match z:
    case True{}: {==}
    case False{}: {==}

def g5_tget_swap_if(+z: Bool, +xs: R.PT, +ys: R.PT, +h: U32, +i: U32, +v: U32,
  ihx: {Tick.tget(R.swap_m(xs, h, i, v), h, i) == v : U32},
  ihy: {Tick.tget(R.swap_m(ys, h, U32.sub(i, h), v), h, U32.sub(i, h)) == v : U32}
) -> {Bool.pick(U32, z,
        Bool.pick(U32, z, Tick.tget(R.swap_m(xs, h, i, v), h, i), Tick.tget(ys, h, U32.sub(i, h))),
        Bool.pick(U32, z, Tick.tget(xs, h, i), Tick.tget(R.swap_m(ys, h, U32.sub(i, h), v), h, U32.sub(i, h))))
      == v : U32}:
  match z:
    case True{}: ihx
    case False{}: ihy

# Read-after-write at the selector's index: `tget(swap_m(t, n, i, v), n, i) = v`.
# This is the engine's `q = Array.get(world, i)` after `world[i] <- v`
# (`Support.sup` cases 3/4/6, `Rules.plan`'s post-write read-back).
def g5_tget_swap(t: R.PT, +n: U32, +i: U32, +v: U32)
  -> {Tick.tget(R.swap_m(t, n, i, v), n, i) == v : U32}:
  match t:
    case R.PL{x}: {==}
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      +tp = g5_tget_pick(z, R.PN{R.swap_m(xs, h, i, v), ys}, R.PN{xs, R.swap_m(ys, h, U32.sub(i, h), v)}, n, i)
      +e = g5_tget_swap_if(z, xs, ys, h, i, v,
             g5_tget_swap(xs, h, i, v),
             g5_tget_swap(ys, h, U32.sub(i, h), v))
      Equal.trans(U32,
        Tick.tget(R.swap_m(R.PN{xs, ys}, n, i, v), n, i),
        Bool.pick(U32, z,
          Tick.tget(R.PN{R.swap_m(xs, h, i, v), ys}, n, i),
          Tick.tget(R.PN{xs, R.swap_m(ys, h, U32.sub(i, h), v)}, n, i)),
        v,
        tp, e)
