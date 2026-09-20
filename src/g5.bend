import Base
import ./refine.bend as R
import ./tick.bend as Tick
import ./bits.bend as Bits
import ./mod.bend as Mod
import ./word.bend as WR

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

# --------------------------------------------- G5 mask residual (bit arithmetic)
#
# `g5_read_get` above states the engine read with the *masked* index
# `i & (g5_twidth t - 1)`; the bare-index form needs the standard array-index
# fact for an in-range `i` on a power-of-two world. This is the small `U32`/`Word`
# bit-arithmetic development that closes it. It is deliberately self-contained
# (`g5_mpow`, `Bits.mask` are the two presentations of the same width):
#
#   * `g5_mpow n d`  is `2^d` in `Word(n)`, peeling `n` and `d` together so the
#                    tail of `g5_mpow (1+p) (1+q)` is definitionally `g5_mpow p q`;
#   * `g5_wand_mask_lt` is the mask identity at the word level:
#                    `i < 2^d` (a `Cmp.is_lt`) implies `Word.and(n, i, mask n d) = i`;
#   * `g5_sub_pow2`   is `2^d - 1 = mask n d`, the bridge from the engine's
#                    `U32.sub (g5_twidth t) 1` to `Bits.mask`;
#   * `g5_twidth_pow` is law 1, `g5_twidth t = 2^depth(t)`.
#
# The comparison recursion is why `g5_mpow` peels `n` too: at a leaf of the
# comparison the mask is `mask p q` at the *reduced* width, so the induction has
# to run at every width. Impossible `Cmp` branches are discharged by
# `g5_cmp_zero_not_lt` (a comparison to zero is never `LT`) and by `g5_absurd`
# (any `{False == True}` yields any equality), with `WR.w_cmp_eq` supplying the
# `EQ` reflection.

def g5_mpow(n: Nat, d: Nat) -> Word(n):
  match n:
    case 0n: WNil{}
    case 1n+p:
      match d:
        case 0n: WCon{True{}, Word.zero(p)}
        case 1n+q: WCon{False{}, g5_mpow(p, q)}

# `Word.shl` and `Word.shl.put _ False` are the same shift.
def g5_shl_eq_put(n: Nat, X: Word(n)) -> {Word.shl(n, X) == Word.shl.put(n, False{}, X) : Word(n)}:
  match n:
    case 0n:
      match X: case WNil{}: {==}
    case 1n+p:
      match X:
        case WCon{xh, xt}: {==}

def g5_shlput_false_zero(n: Nat) -> {Word.shl.put(n, False{}, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p),
        g5_shlput_false_zero(p))

def g5_shlput_true_zero(p: Nat) -> {Word.shl.put(p, True{}, Word.zero(p)) == g5_mpow(p, 0n) : Word(p)}:
  match p:
    case 0n: {==}
    case 1n+q:
      Equal.cong(Word(q), Word(1n+q), t => WCon{True{}, t},
        Word.shl.put(q, False{}, Word.zero(q)), Word.zero(q),
        g5_shlput_false_zero(q))

# `Word.shl` is the doubling `g5_mpow _ d -> g5_mpow _ (d+1)`; this is the link
# between `U32.shl` (engine `g5_twidth`) and the `Word`-level width.
def g5_pow_shl(n: Nat, d: Nat) -> {Word.shl(n, g5_mpow(n, d)) == g5_mpow(n, 1n+d) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      match d:
        case 0n:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.shl.put(p, True{}, Word.zero(p)), g5_mpow(p, 0n),
            g5_shlput_true_zero(p))
        case 1n+ +q:
          +X = g5_mpow(p, q)
          +e = Equal.trans(Word(p),
                 Word.shl.put(p, False{}, X), Word.shl(p, X), g5_mpow(p, 1n+q),
                 Equal.sym(Word(p), Word.shl(p, X), Word.shl.put(p, False{}, X), g5_shl_eq_put(p, X)),
                 g5_pow_shl(p, q))
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.shl.put(p, False{}, X), g5_mpow(p, 1n+q), e)

# The carry chain of `a + zero + k` equals that of `a + ones + k`: adding the
# all-ones word inverts `b` and clears the input carry, which is the same bit
# computation at every position.
def g5_adc_zero_ones(n: Nat, a: Word(n), k: Bool) -> {Word.adc(n, a, Word.zero(n), True{}, k) == Word.adc(n, a, Mod.ones(n), False{}, k) : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n+ +p:
      match a:
        case WCon{ah, +at}:
          match ah k:
            case False{} False{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
                Word.adc(p, at, Word.zero(p), True{}, False{}),
                Word.adc(p, at, Mod.ones(p), False{}, False{}),
                g5_adc_zero_ones(p, at, False{}))
            case False{} True{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
                Word.adc(p, at, Word.zero(p), True{}, True{}),
                Word.adc(p, at, Mod.ones(p), False{}, True{}),
                g5_adc_zero_ones(p, at, True{}))
            case True{} False{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
                Word.adc(p, at, Word.zero(p), True{}, True{}),
                Word.adc(p, at, Mod.ones(p), False{}, True{}),
                g5_adc_zero_ones(p, at, True{}))
            case True{} True{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
                Word.adc(p, at, Word.zero(p), True{}, True{}),
                Word.adc(p, at, Mod.ones(p), False{}, True{}),
                g5_adc_zero_ones(p, at, True{}))

# `a - 1 = a + all-ones` (two's complement, `2^n - 1` instead of a borrow).
def g5_sub_one_ones(n: Nat, a: Word(n)) -> {Word.sub(n, a, Mod.one(n)) == Word.add(n, a, Mod.ones(n)) : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n+ +p:
      match a:
        case WCon{ah, +at}:
          match ah:
            case False{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
                Word.adc(p, at, Word.zero(p), True{}, False{}),
                Word.adc(p, at, Mod.ones(p), False{}, False{}),
                g5_adc_zero_ones(p, at, False{}))
            case True{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
                Word.adc(p, at, Word.zero(p), True{}, True{}),
                Word.adc(p, at, Mod.ones(p), False{}, True{}),
                g5_adc_zero_ones(p, at, True{}))

# `mask n d + 1 = 2^d`: the lower-`d`-ones word increments to the width.
def g5_mask_inc(n: Nat, d: Nat) -> {Word.add(n, Bits.mask(n, d), Mod.one(n)) == g5_mpow(n, d) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      match d:
        case 0n:
          Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
            Word.add(p, Word.zero(p), Word.zero(p)), Word.zero(p),
            Mod.add_zero(p, Word.zero(p)))
        case 1n+ +q:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.adc(p, Bits.mask(p, q), Word.zero(p), False{}, True{}),
            g5_mpow(p, q),
            Equal.trans(Word(p),
              Word.adc(p, Bits.mask(p, q), Word.zero(p), False{}, True{}),
              Word.add(p, Bits.mask(p, q), Mod.one(p)),
              g5_mpow(p, q),
              Equal.sym(Word(p),
                Word.add(p, Bits.mask(p, q), Mod.one(p)),
                Word.adc(p, Bits.mask(p, q), Word.zero(p), False{}, True{}),
                Mod.add_one_eq(p, Bits.mask(p, q))),
              g5_mask_inc(p, q)))

# `2^d + all-ones = mask n d` (`2^d - 1` modulo `2^n`), by `mask+1=2^d` and
# `(mask+1)+ones = mask` (`Mod.add_one_ones`).
def g5_add_pow_ones(+n: Nat, +d: Nat) -> {Word.add(n, g5_mpow(n, d), Mod.ones(n)) == Bits.mask(n, d) : Word(n)}:
  Equal.trans(Word(n),
    Word.add(n, g5_mpow(n, d), Mod.ones(n)),
    Word.add(n, Word.add(n, Bits.mask(n, d), Mod.one(n)), Mod.ones(n)),
    Bits.mask(n, d),
    Equal.sym(Word(n),
      Word.add(n, Word.add(n, Bits.mask(n, d), Mod.one(n)), Mod.ones(n)),
      Word.add(n, g5_mpow(n, d), Mod.ones(n)),
      Equal.cong(Word(n), Word(n), t => Word.add(n, t, Mod.ones(n)),
        Word.add(n, Bits.mask(n, d), Mod.one(n)), g5_mpow(n, d),
        g5_mask_inc(n, d))),
    Mod.add_one_ones(n, Bits.mask(n, d)))

# The engine's `2^d - 1` is the lower-`d`-ones mask: `g5_sub_pow2 n d`.
def g5_sub_pow2(+n: Nat, +d: Nat) -> {Word.sub(n, g5_mpow(n, d), Mod.one(n)) == Bits.mask(n, d) : Word(n)}:
  Equal.trans(Word(n),
    Word.sub(n, g5_mpow(n, d), Mod.one(n)),
    Word.add(n, g5_mpow(n, d), Mod.ones(n)),
    Bits.mask(n, d),
    g5_sub_one_ones(n, g5_mpow(n, d)),
    g5_add_pow_ones(n, d))

# A comparison to zero is never `LT`.
def g5_cmp_fin_not_lt(+ih: Bool, +c: Cmp, +h: {Cmp.is_lt(c) == False{} : Bool}) -> {Cmp.is_lt(Word.cmp.fin(ih, False{}, c)) == False{} : Bool}:
  match ih c:
    case False{} LT{}: h
    case False{} EQ{}: h
    case False{} GT{}: h
    case True{} LT{}: h
    case True{} EQ{}: h
    case True{} GT{}: h

def g5_cmp_zero_not_lt(n: Nat, iw: Word(n)) -> {Cmp.is_lt(Word.cmp(n, iw, Word.zero(n))) == False{} : Bool}:
  match n:
    case 0n:
      match iw: case WNil{}: {==}
    case 1n+ +p:
      match iw:
        case WCon{ih, +it}:
          g5_cmp_fin_not_lt(ih, Word.cmp(p, it, Word.zero(p)), g5_cmp_zero_not_lt(p, it))

# `{False == True}` eliminates into any equality (`Equal.cong` along a `Bool.pick`).
def g5_absurd(T: Type, X: T, Y: T, +h: {False{} == True{} : Bool}) -> {X == Y : T}:
  Equal.cong(Bool, T, x => Bool.pick(T, x, Y, X), False{}, True{}, h)

# `i < 1` (the `d = 0` comparison) forces `i = 0`, so `mask 0` absorbs it.
def g5_lt_one_cons(+p: Nat, +ih: Bool, +it: Word(p), +c: Cmp,
   +hl: {Word.cmp(p, it, Word.zero(p)) == c : Cmp},
   +h: {Cmp.is_lt(Word.cmp.fin(ih, True{}, c)) == True{} : Bool},
   +hc: {Cmp.is_lt(c) == False{} : Bool})
  -> {WCon{ih, it} == Word.zero(1n+p) : Word(1n+p)}:
  match ih c:
    case False{} LT{}:
      g5_absurd(Word(1n+p), WCon{False{}, it}, Word.zero(1n+p),
        Equal.sym(Bool, True{}, False{}, hc))
    case False{} EQ{}:
      +heqc2 = Equal.trans(Bool,
        Cmp.is_eq(Word.cmp(p, it, Word.zero(p))), Cmp.is_eq(c), True{},
        Equal.cong(Cmp, Bool, x => Cmp.is_eq(x), Word.cmp(p, it, Word.zero(p)), c, hl),
        {==})
      +eit = WR.w_cmp_eq(p, it, Word.zero(p), heqc2)
      Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, it, Word.zero(p), eit)
    case False{} GT{}:
      g5_absurd(Word(1n+p), WCon{False{}, it}, Word.zero(1n+p), h)
    case True{} LT{}:
      g5_absurd(Word(1n+p), WCon{True{}, it}, Word.zero(1n+p),
        Equal.sym(Bool, True{}, False{}, hc))
    case True{} EQ{}:
      g5_absurd(Word(1n+p), WCon{True{}, it}, Word.zero(1n+p), h)
    case True{} GT{}:
      g5_absurd(Word(1n+p), WCon{True{}, it}, Word.zero(1n+p), h)

def g5_lt_one(n: Nat, iw: Word(n), +h: {Cmp.is_lt(Word.cmp(n, iw, g5_mpow(n, 0n))) == True{} : Bool}) -> {iw == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match iw: case WNil{}: {==}
    case 1n+ +p:
      match iw:
        case WCon{ih, +it}:
          g5_lt_one_cons(p, ih, it, Word.cmp(p, it, Word.zero(p)), {==}, h, g5_cmp_zero_not_lt(p, it))

# `LT` of a `False`-headed comparison reduces to `LT` of the tail.
def g5_lt_cons_false(+ih: Bool, +c: Cmp, +h: {Cmp.is_lt(Word.cmp.fin(ih, False{}, c)) == True{} : Bool}) -> {Cmp.is_lt(c) == True{} : Bool}:
  match ih c:
    case False{} LT{}: {==}
    case False{} EQ{}: h
    case False{} GT{}: h
    case True{} LT{}: {==}
    case True{} EQ{}: h
    case True{} GT{}: h

# The mask identity at word level: for any width `n`, `i < 2^d` implies
# `Word.and(n, i, mask n d) = i`. Induction on `n` (the comparison and the mask
# both peel a bit), with `d` split inside.
def g5_wand_mask_lt(n: Nat, +d: Nat, iw: Word(n), +h: {Cmp.is_lt(Word.cmp(n, iw, g5_mpow(n, d))) == True{} : Bool}) -> {Word.and(n, iw, Bits.mask(n, d)) == iw : Word(n)}:
  match n:
    case 0n:
      match iw: case WNil{}: {==}
    case 1n+ +p:
      match d:
        case 0n:
          match iw:
            case WCon{+ih, +it}:
              +e0 = g5_lt_one(1n+p, WCon{ih, it}, h)
              +e1 = Equal.cong(Word(1n+p), Word(1n+p),
                t => Word.and(1n+p, t, Bits.mask(1n+p, 0n)),
                WCon{ih, it}, Word.zero(1n+p), e0)
              +e2 = Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
                Word.and(p, Word.zero(p), Word.zero(p)), Word.zero(p),
                Bits.w_and_zero(p, Word.zero(p)))
              Equal.trans(Word(1n+p),
                Word.and(1n+p, WCon{ih, it}, Bits.mask(1n+p, 0n)),
                Word.and(1n+p, Word.zero(1n+p), Bits.mask(1n+p, 0n)),
                WCon{ih, it},
                e1,
                Equal.trans(Word(1n+p),
                  Word.and(1n+p, Word.zero(1n+p), Bits.mask(1n+p, 0n)),
                  Word.zero(1n+p),
                  WCon{ih, it},
                  e2,
                  Equal.sym(Word(1n+p), WCon{ih, it}, Word.zero(1n+p), e0)))
        case 1n+ +q:
          match iw:
            case WCon{+ih, +it}:
              +c = Word.cmp(p, it, g5_mpow(p, q))
              +hc = g5_lt_cons_false(ih, c, h)
              +eit = g5_wand_mask_lt(p, q, it, hc)
              +X = Word.and(p, it, Bits.mask(p, q))
              +ehead = Equal.cong(Bool, Word(1n+p), b => WCon{b, X},
                Bool.and(ih, True{}), ih, Bits.b_and_true(ih))
              +etail = Equal.cong(Word(p), Word(1n+p), t => WCon{ih, t}, X, it, eit)
              Equal.trans(Word(1n+p),
                Word.and(1n+p, WCon{ih, it}, Bits.mask(1n+p, 1n+q)),
                WCon{Bool.and(ih, True{}), X},
                WCon{ih, it},
                {==},
                Equal.trans(Word(1n+p),
                  WCon{Bool.and(ih, True{}), X}, WCon{ih, X}, WCon{ih, it},
                  ehead, etail))

# Law 1: the width of a packed tree is `2^depth`.
def g5_depth(t: R.PT) -> Nat:
  match t:
    case R.PL{x}: 0n
    case R.PN{+xs, +ys}: Nat.add(1n, g5_depth(xs))

def g5_twidth_pow(t: R.PT) -> {g5_twidth(t) == U32{g5_mpow(32n, g5_depth(t))} : U32}:
  match t:
    case R.PL{x}: {==}
    case R.PN{+xs, +ys}:
      +d = g5_depth(xs)
      +eih = g5_twidth_pow(xs)
      +e1 = Equal.cong(U32, U32, U32.shl, g5_twidth(xs), U32{g5_mpow(32n, d)}, eih)
      +e2 = Equal.cong(Word(32n), U32, w => U32{w}, Word.shl(32n, g5_mpow(32n, d)), g5_mpow(32n, 1n+d), g5_pow_shl(32n, d))
      Equal.trans(U32,
        g5_twidth(R.PN{xs, ys}),
        U32{Word.shl(32n, g5_mpow(32n, d))},
        U32{g5_mpow(32n, 1n+d)},
        e1, e2)

# Law 2: the bare-index mask identity. `g5_sub_pow2` turns the engine's
# `g5_twidth t - 1` into `Bits.mask (32) (g5_depth t)`, and `g5_wand_mask_lt`
# is the bit fact.
def g5_and_mask_id(+t: R.PT, i: U32, +h: {U32.is_lt(i, g5_twidth(t)) == True{} : Bool}) -> {U32.and(i, U32.sub(g5_twidth(t), 1)) == i : U32}:
  match i:
    case U32{iw}:
      +d = g5_depth(t)
      +etw = g5_twidth_pow(t)
      +congAB = Equal.cong(U32, Bool, x => U32.is_lt(U32{iw}, x), g5_twidth(t), U32{g5_mpow(32n, d)}, etw)
      +hw0 = Equal.trans(Bool,
          U32.is_lt(U32{iw}, U32{g5_mpow(32n, d)}),
          U32.is_lt(U32{iw}, g5_twidth(t)),
          True{},
          Equal.sym(Bool, U32.is_lt(U32{iw}, g5_twidth(t)), U32.is_lt(U32{iw}, U32{g5_mpow(32n, d)}), congAB),
          h)
      +ewm = g5_wand_mask_lt(32n, d, iw, hw0)
      +esub = g5_sub_pow2(32n, d)
      +eg1 = Equal.cong(U32, U32, x => U32.and(U32{iw}, U32.sub(x, 1)), g5_twidth(t), U32{g5_mpow(32n, d)}, etw)
      +eg2 = Equal.cong(Word(32n), U32, w => U32{Word.and(32n, iw, w)}, Word.sub(32n, g5_mpow(32n, d), Mod.one(32n)), Bits.mask(32n, d), esub)
      +eg3 = Equal.cong(Word(32n), U32, w => U32{w}, Word.and(32n, iw, Bits.mask(32n, d)), iw, ewm)
      Equal.trans(U32,
        U32.and(U32{iw}, U32.sub(g5_twidth(t), 1)),
        U32{Word.and(32n, iw, Word.sub(32n, g5_mpow(32n, d), Mod.one(32n)))},
        U32{iw},
        Equal.trans(U32,
          U32.and(U32{iw}, U32.sub(g5_twidth(t), 1)),
          U32.and(U32{iw}, U32.sub(U32{g5_mpow(32n, d)}, 1)),
          U32{Word.and(32n, iw, Word.sub(32n, g5_mpow(32n, d), Mod.one(32n)))},
          eg1, {==}),
        Equal.trans(U32,
          U32{Word.and(32n, iw, Word.sub(32n, g5_mpow(32n, d), Mod.one(32n)))},
          U32{Word.and(32n, iw, Bits.mask(32n, d))},
          U32{iw},
          eg2, eg3))
