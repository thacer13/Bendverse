import Base
import ./nat.bend as NatL
import ./bits.bend as Bits
import ./mod.bend as Mod
import ./word.bend as WR
import ./dirtyn.bend as Dirtyn
import ./dirty.bend as Dirty
import ./maskword.bend as Maskword

# ============================================================================
# wordnat (S1 / PLAN `G-scale-2` item 3) -- the `U32 <-> Nat` *index* value theory.
#
# Originally this module closed the `Dirty.Mask <-> Word(64)` composition: the
# lo/hi `Dirty.Mask` was `U32`-indexed (`U32.and(y,31)`, `U32.is_lt(y,32)`) while
# `Dirtyn.dwin_get` is `Nat`-indexed, so the composition needed the value theory
# of the `Word` encoding.
#
# S1/W3 rewire. `Dirty.is_dirty_y` now *is* `Dirtyn.dwin_get(64, mask_word m,
# to_nat y)`, so the composition is definitional and `wnat_mask_word_get` is
# `{==}`; the lo/hi composition lemmas inherited from A.109 are retired with the
# `Dirty.Mask{lo, hi}` representation (see the retirement note near the end).
# The generic value theory below is size-agnostic and kept:
#
#   * the `Nat` order/value lemmas (`wnat_n_*`) and a `Nat.cmp` reflection;
#   * `wnat_w_cmp`: `Word.cmp` agrees with `Nat.cmp` on `Word.to_nat` values
#     (`wnat_to_nat_cons` unfolds the `Word.to_nat` cons step);
#   * `wnat_mask_bound`: a `k`-bit mask caps a `Word.to_nat` value at `2^k`
#     (`wnat_two_pow` is the structural `2^k`, avoiding `Nat.pow`);
#   * `wnat_mask_step`: the masked value of the next bit (`dwin_get` supplies the
#     bit), so `and(y,31)` / `and(y,63)` differ by bit 5;
#   * `wnat_mask_word_get`: the headline law, now `{==}`.
#
# All names are prefixed `wnat_`; the module is additive.
# ============================================================================

# `{False == True}` yields any equality (`Equal.cong` along a `Bool.pick`).
def wnat_absurd(T: Type, X: T, Y: T, +h: {False{} == True{} : Bool}) -> {X == Y : T}:
  Equal.cong(Bool, T, x => Bool.pick(T, x, Y, X), False{}, True{}, h)

# ------------------------------------------------------------------ Nat order
def wnat_n_le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n: {==}
    case 1n+ +p: wnat_n_le_refl(p)

def wnat_n_self_le_succ(c: Nat) -> {Nat.is_le(c, Nat.add(1n, c)) == True{} : Bool}:
  match c:
    case 0n: {==}
    case 1n+ +p: wnat_n_self_le_succ(p)

# `v < P` implies `2v+1 < 2P`.
def wnat_n_succ_double_lt(v: Nat, P: Nat, +h: {Nat.is_lt(v, P) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(1n, Nat.double(v)), Nat.double(P)) == True{} : Bool}:
  match v P:
    case 0n 0n: h
    case 0n 1n+ +q: {==}
    case 1n+ +p 0n: h
    case 1n+ +p 1n+ +q: wnat_n_succ_double_lt(p, q, h)

def wnat_n_double_lt(x: Nat, +y: Nat) -> {Nat.is_lt(Nat.double(x), Nat.double(y)) == Nat.is_lt(x, y) : Bool}:
  match x y:
    case 0n 0n: {==}
    case 0n 1n+ +q: {==}
    case 1n+ +p 0n: {==}
    case 1n+ +p 1n+ +q: wnat_n_double_lt(p, q)

def wnat_n_le_lt_trans(a: Nat, b: Nat, c: Nat,
    +hle: {Nat.is_le(a, b) == True{} : Bool}, +hlt: {Nat.is_lt(b, c) == True{} : Bool})
  -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b:
    case 0n 0n:
      match c:
        case 0n: hlt
        case 1n+ +r: {==}
    case 0n 1n+ +q:
      match c:
        case 0n: hlt
        case 1n+ +r: {==}
    case 1n+ +p 0n: wnat_absurd(Bool, Nat.is_lt(1n+p, c), True{}, hle)
    case 1n+ +p 1n+ +q:
      match c:
        case 0n: hlt
        case 1n+ +r: wnat_n_le_lt_trans(p, q, r, hle, hlt)

def wnat_n_lt_le_trans(a: Nat, b: Nat, c: Nat,
    +hlt: {Nat.is_lt(a, b) == True{} : Bool}, +hle: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b:
    case 0n 0n: wnat_absurd(Bool, Nat.is_lt(0n, c), True{}, hlt)
    case 0n 1n+ +q:
      match c:
        case 0n: hle
        case 1n+ +r: {==}
    case 1n+ +p 0n: wnat_absurd(Bool, Nat.is_lt(1n+p, c), True{}, hlt)
    case 1n+ +p 1n+ +q:
      match c:
        case 0n: wnat_absurd(Bool, Nat.is_lt(1n+p, 0n), True{}, hle)
        case 1n+ +r: wnat_n_lt_le_trans(p, q, r, hlt, hle)

def wnat_n_pt_le(+TA: Bool, +A: Nat)
  -> {Nat.is_le(Nat.add(Bool.pick(Nat, TA, 1n, 0n), Nat.double(A)), Nat.add(1n, Nat.double(A))) == True{} : Bool}:
  match TA:
    case True{}: wnat_n_le_refl(Nat.add(1n, Nat.double(A)))
    case False{}: wnat_n_self_le_succ(Nat.double(A))

def wnat_n_pt_le_hi(+TB: Bool, +B: Nat)
  -> {Nat.is_le(Nat.double(B), Nat.add(Bool.pick(Nat, TB, 1n, 0n), Nat.double(B))) == True{} : Bool}:
  match TB:
    case True{}: wnat_n_self_le_succ(Nat.double(B))
    case False{}: wnat_n_le_refl(Nat.double(B))

# The cons-value step: `A < B` implies `TA + 2A < TB + 2B` (`TA,TB in {0,1}`).
def wnat_n_lt_step(+A: Nat, +B: Nat, +TA: Bool, +TB: Bool, h: {Nat.is_lt(A, B) == True{} : Bool})
  -> {Nat.is_lt(Nat.add(Bool.pick(Nat, TA, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, TB, 1n, 0n), Nat.double(B))) == True{} : Bool}:
  +h1 = wnat_n_succ_double_lt(A, B, h)
  +hA = wnat_n_pt_le(TA, A)
  +hC = wnat_n_pt_le_hi(TB, B)
  wnat_n_lt_le_trans(
    Nat.add(Bool.pick(Nat, TA, 1n, 0n), Nat.double(A)),
    Nat.double(B),
    Nat.add(Bool.pick(Nat, TB, 1n, 0n), Nat.double(B)),
    wnat_n_le_lt_trans(
      Nat.add(Bool.pick(Nat, TA, 1n, 0n), Nat.double(A)),
      Nat.add(1n, Nat.double(A)),
      Nat.double(B),
      hA, h1),
    hC)

# Reflect `Nat.is_lt` / `Nat.is_gt` back to the comparison value.
def wnat_n_cmp_lt(x: Nat, y: Nat, +h: {Nat.is_lt(x, y) == True{} : Bool})
  -> {Nat.cmp(x, y) == LT{} : Cmp}:
  match x y:
    case 0n 0n: wnat_absurd(Cmp, EQ{}, LT{}, h)
    case 0n 1n+ +q: {==}
    case 1n+ +p 0n: wnat_absurd(Cmp, GT{}, LT{}, h)
    case 1n+ +p 1n+ +q: wnat_n_cmp_lt(p, q, h)

def wnat_n_cmp_gt(x: Nat, y: Nat, +h: {Nat.is_gt(x, y) == True{} : Bool})
  -> {Nat.cmp(x, y) == GT{} : Cmp}:
  match x y:
    case 0n 0n: wnat_absurd(Cmp, EQ{}, GT{}, h)
    case 0n 1n+ +q: wnat_absurd(Cmp, LT{}, GT{}, h)
    case 1n+ +p 0n: {==}
    case 1n+ +p 1n+ +q: wnat_n_cmp_gt(p, q, h)

def wnat_n_gt_lt(a: Nat, b: Nat) -> {Nat.is_gt(a, b) == Nat.is_lt(b, a) : Bool}:
  match a b:
    case 0n 0n: {==}
    case 0n 1n+ +q: {==}
    case 1n+ +p 0n: {==}
    case 1n+ +p 1n+ +q: wnat_n_gt_lt(p, q)

# Adding the same constant is order-preserving at the comparison level.
def wnat_n_add_const_cmp(+x: Nat, +y: Nat, c: Nat)
  -> {Nat.cmp(Nat.add(x, c), Nat.add(y, c)) == Nat.cmp(x, y) : Cmp}:
  match c:
    case 0n:
      +ex = NatL.n_add_zero_right(x)
      +ey = NatL.n_add_zero_right(y)
      Equal.trans(Cmp,
        Nat.cmp(Nat.add(x, 0n), Nat.add(y, 0n)),
        Nat.cmp(x, Nat.add(y, 0n)),
        Nat.cmp(x, y),
        Equal.cong(Nat, Cmp, z => Nat.cmp(z, Nat.add(y, 0n)), Nat.add(x, 0n), x, ex),
        Equal.cong(Nat, Cmp, z => Nat.cmp(x, z), Nat.add(y, 0n), y, ey))
    case 1n+ +s:
      +ex = NatL.n_add_succ_right(x, s)
      +ey = NatL.n_add_succ_right(y, s)
      Equal.trans(Cmp,
        Nat.cmp(Nat.add(x, Nat.add(1n, s)), Nat.add(y, Nat.add(1n, s))),
        Nat.cmp(Nat.add(1n, Nat.add(x, s)), Nat.add(1n, Nat.add(y, s))),
        Nat.cmp(x, y),
        Equal.trans(Cmp,
          Nat.cmp(Nat.add(x, Nat.add(1n, s)), Nat.add(y, Nat.add(1n, s))),
          Nat.cmp(Nat.add(1n, Nat.add(x, s)), Nat.add(y, Nat.add(1n, s))),
          Nat.cmp(Nat.add(1n, Nat.add(x, s)), Nat.add(1n, Nat.add(y, s))),
          Equal.cong(Nat, Cmp, z => Nat.cmp(z, Nat.add(y, Nat.add(1n, s))), Nat.add(x, Nat.add(1n, s)), Nat.add(1n, Nat.add(x, s)), ex),
          Equal.cong(Nat, Cmp, z => Nat.cmp(Nat.add(1n, Nat.add(x, s)), z), Nat.add(y, Nat.add(1n, s)), Nat.add(1n, Nat.add(y, s)), ey)),
        Equal.trans(Cmp,
          Nat.cmp(Nat.add(1n, Nat.add(x, s)), Nat.add(1n, Nat.add(y, s))),
          Nat.cmp(Nat.add(x, s), Nat.add(y, s)),
          Nat.cmp(x, y),
          {==},
          wnat_n_add_const_cmp(x, y, s)))

def wnat_bool_pick_cmp(a: Bool, b: Bool)
  -> {Nat.cmp(Bool.pick(Nat, a, 1n, 0n), Bool.pick(Nat, b, 1n, 0n)) == Bool.cmp(a, b) : Cmp}:
  match a b:
    case True{} True{}: {==}
    case True{} False{}: {==}
    case False{} True{}: {==}
    case False{} False{}: {==}

# ------------------------------------------------------------------ cmp bridge
# `Word.to_nat` on a cons is the `pick` plus twice the tail value.
def wnat_to_nat_cons(+p: Nat, +ah: Bool, +at: Word(p))
  -> {Word.to_nat(1n+p, WCon{ah, at}) == Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(Word.to_nat(p, at))) : Nat}:
  match ah:
    case True{}: {==}
    case False{}: {==}

# The cons step of the bridge, by cases on the tail comparison.
def wnat_w_cmp_cons(+c: Cmp, +p: Nat, +ah: Bool, +at: Word(p), +bh: Bool, +bt: Word(p),
    +hc: {Word.cmp(p, at, bt) == c : Cmp},
    +hih: {Word.cmp(p, at, bt) == Nat.cmp(Word.to_nat(p, at), Word.to_nat(p, bt)) : Cmp})
  -> {Word.cmp.fin(ah, bh, Word.cmp(p, at, bt)) == Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(Word.to_nat(p, at))), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(Word.to_nat(p, bt)))) : Cmp}:
  match c:
    case LT{}:
      +A = Word.to_nat(p, at)
      +B = Word.to_nat(p, bt)
      +hnat = Equal.trans(Cmp, Nat.cmp(A, B), Word.cmp(p, at, bt), c, Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(A, B), hih), hc)
      +hltAB = Equal.cong(Cmp, Bool, Cmp.is_lt, Nat.cmp(A, B), c, hnat)
      +hstep = wnat_n_lt_step(A, B, ah, bh, hltAB)
      +href = wnat_n_cmp_lt(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B)), hstep)
      Equal.trans(Cmp,
        Word.cmp.fin(ah, bh, Word.cmp(p, at, bt)),
        LT{},
        Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B))),
        Equal.cong(Cmp, Cmp, z => Word.cmp.fin(ah, bh, z), Word.cmp(p, at, bt), c, hc),
        Equal.sym(Cmp, Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B))), LT{}, href))
    case GT{}:
      +A = Word.to_nat(p, at)
      +B = Word.to_nat(p, bt)
      +hnat = Equal.trans(Cmp, Nat.cmp(A, B), Word.cmp(p, at, bt), c, Equal.sym(Cmp, Word.cmp(p, at, bt), Nat.cmp(A, B), hih), hc)
      +hgtAB = Equal.cong(Cmp, Bool, Cmp.is_gt, Nat.cmp(A, B), c, hnat)
      +hltBA = Equal.trans(Bool, Nat.is_lt(B, A), Nat.is_gt(A, B), True{}, Equal.sym(Bool, Nat.is_gt(A, B), Nat.is_lt(B, A), wnat_n_gt_lt(A, B)), hgtAB)
      +hstep = wnat_n_lt_step(B, A, bh, ah, hltBA)
      +hgtXY = Equal.trans(Bool, Nat.is_gt(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B))), Nat.is_lt(Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B)), Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A))), True{}, wnat_n_gt_lt(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B))), hstep)
      +href = wnat_n_cmp_gt(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B)), hgtXY)
      Equal.trans(Cmp,
        Word.cmp.fin(ah, bh, Word.cmp(p, at, bt)),
        GT{},
        Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B))),
        Equal.cong(Cmp, Cmp, z => Word.cmp.fin(ah, bh, z), Word.cmp(p, at, bt), c, hc),
        Equal.sym(Cmp, Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B))), GT{}, href))
    case EQ{}:
      +A = Word.to_nat(p, at)
      +B = Word.to_nat(p, bt)
      +heqW = Equal.trans(Bool, Cmp.is_eq(Word.cmp(p, at, bt)), Cmp.is_eq(c), True{}, Equal.cong(Cmp, Bool, Cmp.is_eq, Word.cmp(p, at, bt), c, hc), {==})
      +eat = WR.w_cmp_eq(p, at, bt, heqW)
      +hAB = Equal.cong(Word(p), Nat, w => Word.to_nat(p, w), at, bt, eat)
      +hdouble = Equal.cong(Nat, Nat, Nat.double, B, A, Equal.sym(Nat, A, B, hAB))
      +hY = Equal.cong(Nat, Nat, z => Nat.add(Bool.pick(Nat, bh, 1n, 0n), z), Nat.double(B), Nat.double(A), hdouble)
      +hstep1 = Equal.cong(Nat, Cmp, z => Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), z), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(A)), hY)
      +hstep2 = wnat_n_add_const_cmp(Bool.pick(Nat, ah, 1n, 0n), Bool.pick(Nat, bh, 1n, 0n), Nat.double(A))
      +hstep3 = wnat_bool_pick_cmp(ah, bh)
      +href = Equal.trans(Cmp,
        Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B))),
        Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(A))),
        Bool.cmp(ah, bh),
        hstep1,
        Equal.trans(Cmp,
          Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(A))),
          Nat.cmp(Bool.pick(Nat, ah, 1n, 0n), Bool.pick(Nat, bh, 1n, 0n)),
          Bool.cmp(ah, bh),
          hstep2, hstep3))
      Equal.trans(Cmp,
        Word.cmp.fin(ah, bh, Word.cmp(p, at, bt)),
        Bool.cmp(ah, bh),
        Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B))),
        Equal.cong(Cmp, Cmp, z => Word.cmp.fin(ah, bh, z), Word.cmp(p, at, bt), c, hc),
        Equal.sym(Cmp, Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(A)), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(B))), Bool.cmp(ah, bh), href))

# The bridge: `Word.cmp` agrees with `Nat.cmp` on `Word.to_nat` values.
def wnat_w_cmp(n: Nat, a: Word(n), b: Word(n))
  -> {Word.cmp(n, a, b) == Nat.cmp(Word.to_nat(n, a), Word.to_nat(n, b)) : Cmp}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}: {==}
    case 1n+ +p:
      match a b:
        case WCon{+ah, +at} WCon{+bh, +bt}:
          +ih = wnat_w_cmp(p, at, bt)
          +hR = Equal.cong(Nat, Cmp, z => Nat.cmp(z, Word.to_nat(1n+p, WCon{bh, bt})),
            Word.to_nat(1n+p, WCon{ah, at}),
            Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(Word.to_nat(p, at))),
            wnat_to_nat_cons(p, ah, at))
          +hR2 = Equal.cong(Nat, Cmp, z => Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(Word.to_nat(p, at))), z),
            Word.to_nat(1n+p, WCon{bh, bt}),
            Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(Word.to_nat(p, bt))),
            wnat_to_nat_cons(p, bh, bt))
          +hgoal = wnat_w_cmp_cons(Word.cmp(p, at, bt), p, ah, at, bh, bt, {==}, ih)
          Equal.trans(Cmp,
            Word.cmp(1n+p, WCon{ah, at}, WCon{bh, bt}),
            Word.cmp.fin(ah, bh, Word.cmp(p, at, bt)),
            Nat.cmp(Word.to_nat(1n+p, WCon{ah, at}), Word.to_nat(1n+p, WCon{bh, bt})),
            {==},
            Equal.trans(Cmp,
              Word.cmp.fin(ah, bh, Word.cmp(p, at, bt)),
              Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(Word.to_nat(p, at))), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(Word.to_nat(p, bt)))),
              Nat.cmp(Word.to_nat(1n+p, WCon{ah, at}), Word.to_nat(1n+p, WCon{bh, bt})),
              hgoal,
              Equal.sym(Cmp,
                Nat.cmp(Word.to_nat(1n+p, WCon{ah, at}), Word.to_nat(1n+p, WCon{bh, bt})),
                Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(Word.to_nat(p, at))), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(Word.to_nat(p, bt)))),
                Equal.trans(Cmp,
                  Nat.cmp(Word.to_nat(1n+p, WCon{ah, at}), Word.to_nat(1n+p, WCon{bh, bt})),
                  Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(Word.to_nat(p, at))), Word.to_nat(1n+p, WCon{bh, bt})),
                  Nat.cmp(Nat.add(Bool.pick(Nat, ah, 1n, 0n), Nat.double(Word.to_nat(p, at))), Nat.add(Bool.pick(Nat, bh, 1n, 0n), Nat.double(Word.to_nat(p, bt)))),
                  hR, hR2))))

# ------------------------------------------------------------------ value bound
# `wnat_two_pow k` is `2^k` structurally (no `Nat.pow`), so the mask induction
# sees `Nat.double` directly.
def wnat_two_pow(k: Nat) -> Nat:
  match k:
    case 0n: 1n
    case 1n+ +p: Nat.double(wnat_two_pow(p))

def wnat_n_pos_double(P: Nat, +h: {Nat.is_lt(0n, P) == True{} : Bool})
  -> {Nat.is_lt(0n, Nat.double(P)) == True{} : Bool}:
  match P:
    case 0n: h
    case 1n+ +s: {==}

def wnat_to_nat_zero(n: Nat) -> {Word.to_nat(n, Word.zero(n)) == 0n : Nat}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      Equal.trans(Nat, Word.to_nat(1n+p, Word.zero(1n+p)), Nat.double(Word.to_nat(p, Word.zero(p))), 0n,
        {==},
        Equal.trans(Nat, Nat.double(Word.to_nat(p, Word.zero(p))), Nat.double(0n), 0n,
          Equal.cong(Nat, Nat, Nat.double, Word.to_nat(p, Word.zero(p)), 0n, wnat_to_nat_zero(p)),
          {==}))

def wnat_two_pow_pos(k: Nat) -> {Nat.is_lt(0n, wnat_two_pow(k)) == True{} : Bool}:
  match k:
    case 0n: {==}
    case 1n+ +q: wnat_n_pos_double(wnat_two_pow(q), wnat_two_pow_pos(q))

def wnat_n_double_add(a: Nat, +b: Nat)
  -> {Nat.double(Nat.add(a, b)) == Nat.add(Nat.double(a), Nat.double(b)) : Nat}:
  match a:
    case 0n: {==}
    case 1n+ +p:
      Equal.cong(Nat, Nat, x => Nat.add(2n, x),
        Nat.double(Nat.add(p, b)), Nat.add(Nat.double(p), Nat.double(b)),
        wnat_n_double_add(p, b))

def wnat_n_double_pick(+b: Bool, +P: Nat)
  -> {Nat.double(Bool.pick(Nat, b, 0n, P)) == Bool.pick(Nat, b, 0n, Nat.double(P)) : Nat}:
  match b:
    case True{}: {==}
    case False{}: {==}

def wnat_mask_bound_cons(+p: Nat, +q: Nat, +wh: Bool, +wt: Word(p),
    +ih: {Nat.is_lt(Word.to_nat(p, Word.and(p, wt, Bits.mask(p, q))), wnat_two_pow(q)) == True{} : Bool})
  -> {Nat.is_lt(Word.to_nat(1n+p, Word.and(1n+p, WCon{wh, wt}, Bits.mask(1n+p, 1n+q))), wnat_two_pow(1n+q)) == True{} : Bool}:
  match wh:
    case True{}:
      Equal.trans(Bool,
        Nat.is_lt(Word.to_nat(1n+p, Word.and(1n+p, WCon{True{}, wt}, Bits.mask(1n+p, 1n+q))), wnat_two_pow(1n+q)),
        Nat.is_lt(Nat.add(1n, Nat.double(Word.to_nat(p, Word.and(p, wt, Bits.mask(p, q))))), Nat.double(wnat_two_pow(q))),
        True{},
        {==},
        wnat_n_succ_double_lt(Word.to_nat(p, Word.and(p, wt, Bits.mask(p, q))), wnat_two_pow(q), ih))
    case False{}:
      Equal.trans(Bool,
        Nat.is_lt(Word.to_nat(1n+p, Word.and(1n+p, WCon{False{}, wt}, Bits.mask(1n+p, 1n+q))), wnat_two_pow(1n+q)),
        Nat.is_lt(Nat.double(Word.to_nat(p, Word.and(p, wt, Bits.mask(p, q)))), Nat.double(wnat_two_pow(q))),
        True{},
        {==},
        Equal.trans(Bool,
          Nat.is_lt(Nat.double(Word.to_nat(p, Word.and(p, wt, Bits.mask(p, q)))), Nat.double(wnat_two_pow(q))),
          Nat.is_lt(Word.to_nat(p, Word.and(p, wt, Bits.mask(p, q))), wnat_two_pow(q)),
          True{},
          wnat_n_double_lt(Word.to_nat(p, Word.and(p, wt, Bits.mask(p, q))), wnat_two_pow(q)),
          ih))

def wnat_mask_bound(n: Nat, +k: Nat, w: Word(n))
  -> {Nat.is_lt(Word.to_nat(n, Word.and(n, w, Bits.mask(n, k))), wnat_two_pow(k)) == True{} : Bool}:
  match n:
    case 0n:
      match w: case WNil{}: wnat_two_pow_pos(k)
    case 1n+ +p:
      match k:
        case 0n:
          +ez = Mod.and_mask0(1n+p, w)
          Equal.trans(Bool,
            Nat.is_lt(Word.to_nat(1n+p, Word.and(1n+p, w, Bits.mask(1n+p, 0n))), wnat_two_pow(0n)),
            Nat.is_lt(Word.to_nat(1n+p, Word.zero(1n+p)), 1n),
            True{},
            Equal.cong(Word(1n+p), Bool, z => Nat.is_lt(Word.to_nat(1n+p, z), wnat_two_pow(0n)), Word.and(1n+p, w, Bits.mask(1n+p, 0n)), Word.zero(1n+p), ez),
            Equal.trans(Bool,
              Nat.is_lt(Word.to_nat(1n+p, Word.zero(1n+p)), 1n),
              Nat.is_lt(0n, 1n),
              True{},
              Equal.cong(Nat, Bool, z => Nat.is_lt(z, 1n), Word.to_nat(1n+p, Word.zero(1n+p)), 0n, wnat_to_nat_zero(1n+p)),
              {==}))
        case 1n+ +q:
          match w:
            case WCon{+wh, +wt}:
              wnat_mask_bound_cons(p, q, wh, wt, wnat_mask_bound(p, q, wt))

# ------------------------------------------------------------------ decomposition
def wnat_n_double_pick2(+b: Bool, +P: Nat)
  -> {Nat.double(Bool.pick(Nat, b, P, 0n)) == Bool.pick(Nat, b, Nat.double(P), 0n) : Nat}:
  match b:
    case True{}: {==}
    case False{}: {==}

# The cons step of `mask(k+1)` vs `mask(k)`: `dwin_get` reads the new bit.
def wnat_mask_step_succ(+p: Nat, +q: Nat, +wh: Bool, +wt: Word(p),
    +ih: {Word.to_nat(p, Word.and(p, wt, Bits.mask(p, Nat.add(1n, q)))) == Nat.add(Word.to_nat(p, Word.and(p, wt, Bits.mask(p, q))), Bool.pick(Nat, Dirtyn.dwin_get(p, wt, q), wnat_two_pow(q), 0n)) : Nat})
  -> {Word.to_nat(1n+p, Word.and(1n+p, WCon{wh, wt}, WCon{True{}, Bits.mask(p, Nat.add(1n, q))}))
      == Nat.add(Word.to_nat(1n+p, Word.and(1n+p, WCon{wh, wt}, WCon{True{}, Bits.mask(p, q)})),
                 Bool.pick(Nat, Dirtyn.dwin_get(p, wt, q), Nat.double(wnat_two_pow(q)), 0n)) : Nat}:
  match wh:
    case True{}:
      +T1 = Word.to_nat(p, Word.and(p, wt, Bits.mask(p, Nat.add(1n, q))))
      +T0 = Word.to_nat(p, Word.and(p, wt, Bits.mask(p, q)))
      +X = Bool.pick(Nat, Dirtyn.dwin_get(p, wt, q), wnat_two_pow(q), 0n)
      +Y = Bool.pick(Nat, Dirtyn.dwin_get(p, wt, q), Nat.double(wnat_two_pow(q)), 0n)
      +hd = wnat_n_double_add(T0, X)
      +hX = wnat_n_double_pick2(Dirtyn.dwin_get(p, wt, q), wnat_two_pow(q))
      +hd1 = Equal.trans(Nat, Nat.double(T1), Nat.double(Nat.add(T0, X)), Nat.add(Nat.double(T0), Nat.double(X)), Equal.cong(Nat, Nat, Nat.double, T1, Nat.add(T0, X), ih), hd)
      +hdouble = Equal.trans(Nat, Nat.double(T1), Nat.add(Nat.double(T0), Nat.double(X)), Nat.add(Nat.double(T0), Y), hd1, Equal.cong(Nat, Nat, z => Nat.add(Nat.double(T0), z), Nat.double(X), Y, hX))
      Equal.trans(Nat,
        Nat.add(1n, Nat.double(T1)),
        Nat.add(1n, Nat.add(Nat.double(T0), Y)),
        Nat.add(Nat.add(1n, Nat.double(T0)), Y),
        Equal.cong(Nat, Nat, z => Nat.add(1n, z), Nat.double(T1), Nat.add(Nat.double(T0), Y), hdouble),
        Equal.sym(Nat, Nat.add(Nat.add(1n, Nat.double(T0)), Y), Nat.add(1n, Nat.add(Nat.double(T0), Y)), NatL.n_add_assoc(1n, Nat.double(T0), Y)))
    case False{}:
      +T1 = Word.to_nat(p, Word.and(p, wt, Bits.mask(p, Nat.add(1n, q))))
      +T0 = Word.to_nat(p, Word.and(p, wt, Bits.mask(p, q)))
      +X = Bool.pick(Nat, Dirtyn.dwin_get(p, wt, q), wnat_two_pow(q), 0n)
      +Y = Bool.pick(Nat, Dirtyn.dwin_get(p, wt, q), Nat.double(wnat_two_pow(q)), 0n)
      +hd = wnat_n_double_add(T0, X)
      +hX = wnat_n_double_pick2(Dirtyn.dwin_get(p, wt, q), wnat_two_pow(q))
      +hd1 = Equal.trans(Nat, Nat.double(T1), Nat.double(Nat.add(T0, X)), Nat.add(Nat.double(T0), Nat.double(X)), Equal.cong(Nat, Nat, Nat.double, T1, Nat.add(T0, X), ih), hd)
      Equal.trans(Nat, Nat.double(T1), Nat.add(Nat.double(T0), Nat.double(X)), Nat.add(Nat.double(T0), Y), hd1, Equal.cong(Nat, Nat, z => Nat.add(Nat.double(T0), z), Nat.double(X), Y, hX))

# `to_nat(and(w, mask(k+1)))` is `to_nat(and(w, mask(k)))` plus the `k`-th bit.
def wnat_mask_step(n: Nat, +k: Nat, w: Word(n))
  -> {Word.to_nat(n, Word.and(n, w, Bits.mask(n, Nat.add(1n, k))))
      == Nat.add(Word.to_nat(n, Word.and(n, w, Bits.mask(n, k))),
                 Bool.pick(Nat, Dirtyn.dwin_get(n, w, k), wnat_two_pow(k), 0n)) : Nat}:
  match n:
    case 0n:
      match w: case WNil{}: {==}
    case 1n+ +p:
      match k:
        case 0n:
          match w:
            case WCon{+wh, +wt}:
              match wh:
                case True{}:
                  +V0 = Word.to_nat(p, Word.and(p, wt, Bits.mask(p, 0n)))
                  +V0p = Word.to_nat(p, Word.and(p, wt, Word.zero(p)))
                  +eand = Equal.cong(Word(p), Word(p), m => Word.and(p, wt, m), Bits.mask(p, 0n), Word.zero(p), Bits.mask_zero(p))
                  +eV = Equal.cong(Word(p), Nat, w2 => Word.to_nat(p, w2), Word.and(p, wt, Bits.mask(p, 0n)), Word.and(p, wt, Word.zero(p)), eand)
                  Equal.trans(Nat,
                    Nat.add(1n, Nat.double(V0)),
                    Nat.add(1n, Nat.double(V0p)),
                    Nat.add(Nat.double(V0p), 1n),
                    Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.double(V0), Nat.double(V0p), Equal.cong(Nat, Nat, Nat.double, V0, V0p, eV)),
                    NatL.n_add_comm(1n, Nat.double(V0p)))
                case False{}:
                  +V0 = Word.to_nat(p, Word.and(p, wt, Bits.mask(p, 0n)))
                  +V0p = Word.to_nat(p, Word.and(p, wt, Word.zero(p)))
                  +eand = Equal.cong(Word(p), Word(p), m => Word.and(p, wt, m), Bits.mask(p, 0n), Word.zero(p), Bits.mask_zero(p))
                  +eV = Equal.cong(Word(p), Nat, w2 => Word.to_nat(p, w2), Word.and(p, wt, Bits.mask(p, 0n)), Word.and(p, wt, Word.zero(p)), eand)
                  Equal.trans(Nat,
                    Nat.double(V0),
                    Nat.double(V0p),
                    Nat.add(Nat.double(V0p), 0n),
                    Equal.cong(Nat, Nat, Nat.double, V0, V0p, eV),
                    Equal.sym(Nat, Nat.add(Nat.double(V0p), 0n), Nat.double(V0p), NatL.n_add_zero_right(Nat.double(V0p))))
        case 1n+ +q:
          match w:
            case WCon{+wh, +wt}:
              wnat_mask_step_succ(p, q, wh, wt, wnat_mask_step(p, q, wt))

# ------------------------------------------------------------------ mask absorption
def wnat_n_lt_one(a: Nat, +h: {Nat.is_lt(a, 1n) == True{} : Bool}) -> {a == 0n : Nat}:
  match a:
    case 0n: {==}
    case 1n+ +p:
      +hneg = Equal.trans(Bool, False{}, Nat.is_lt(p, 0n), True{},
        Equal.sym(Bool, Nat.is_lt(p, 0n), False{}, NatL.n_not_lt_zero(p)), h)
      wnat_absurd(Nat, 1n+p, 0n, hneg)

def wnat_n_double_zero_inv(a: Nat, +h: {Nat.double(a) == 0n : Nat}) -> {a == 0n : Nat}:
  match a:
    case 0n: {==}
    case 1n+ +p:
      +that = Equal.cong(Nat, Bool, z => Nat.is_lt(0n, z), Nat.double(1n+p), 0n, h)
      wnat_absurd(Nat, 1n+p, 0n, Equal.sym(Bool, True{}, False{}, that))

def wnat_to_nat_zero_inv(n: Nat, +w: Word(n), +h: {Word.to_nat(n, w) == 0n : Nat})
  -> {w == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w: case WNil{}: {==}
    case 1n+ +p:
      match w:
        case WCon{+wh, +wt}:
          match wh:
            case True{}:
              +that = Equal.cong(Nat, Bool, z => Nat.is_lt(0n, z), Nat.add(1n, Nat.double(Word.to_nat(p, wt))), 0n, h)
              wnat_absurd(Word(1n+p), WCon{True{}, wt}, Word.zero(1n+p), Equal.sym(Bool, True{}, False{}, that))
            case False{}:
              +hT = wnat_n_double_zero_inv(Word.to_nat(p, wt), h)
              +hwt = wnat_to_nat_zero_inv(p, wt, hT)
              Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, wt, Word.zero(p), hwt)

# A value below `2^k` is fixed by the `k`-bit mask.
def wnat_and_mask_eq(n: Nat, +k: Nat, +w: Word(n),
    +h: {Nat.is_lt(Word.to_nat(n, w), wnat_two_pow(k)) == True{} : Bool})
  -> {Word.and(n, w, Bits.mask(n, k)) == w : Word(n)}:
  match n:
    case 0n:
      match w: case WNil{}: {==}
    case 1n+ +p:
      match k:
        case 0n:
          +hz = wnat_n_lt_one(Word.to_nat(1n+p, w), h)
          +hw = wnat_to_nat_zero_inv(1n+p, w, hz)
          Equal.trans(Word(1n+p),
            Word.and(1n+p, w, Bits.mask(1n+p, 0n)),
            Word.zero(1n+p),
            w,
            Mod.and_mask0(1n+p, w),
            Equal.sym(Word(1n+p), w, Word.zero(1n+p), hw))
        case 1n+ +q:
          match w:
            case WCon{+wh, +wt}:
              match wh:
                case True{}:
                  +hle = wnat_n_pt_le_hi(True{}, Word.to_nat(p, wt))
                  +hlt2 = wnat_n_le_lt_trans(Nat.double(Word.to_nat(p, wt)), Nat.add(1n, Nat.double(Word.to_nat(p, wt))), Nat.double(wnat_two_pow(q)), hle, h)
                  +hT = Equal.trans(Bool,
                    Nat.is_lt(Word.to_nat(p, wt), wnat_two_pow(q)),
                    Nat.is_lt(Nat.double(Word.to_nat(p, wt)), Nat.double(wnat_two_pow(q))),
                    True{},
                    Equal.sym(Bool, Nat.is_lt(Nat.double(Word.to_nat(p, wt)), Nat.double(wnat_two_pow(q))), Nat.is_lt(Word.to_nat(p, wt), wnat_two_pow(q)), wnat_n_double_lt(Word.to_nat(p, wt), wnat_two_pow(q))),
                    hlt2)
                  +hwt = wnat_and_mask_eq(p, q, wt, hT)
                  Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t}, Word.and(p, wt, Bits.mask(p, q)), wt, hwt)
                case False{}:
                  +hT = Equal.trans(Bool,
                    Nat.is_lt(Word.to_nat(p, wt), wnat_two_pow(q)),
                    Nat.is_lt(Nat.double(Word.to_nat(p, wt)), Nat.double(wnat_two_pow(q))),
                    True{},
                    Equal.sym(Bool, Nat.is_lt(Nat.double(Word.to_nat(p, wt)), Nat.double(wnat_two_pow(q))), Nat.is_lt(Word.to_nat(p, wt), wnat_two_pow(q)), wnat_n_double_lt(Word.to_nat(p, wt), wnat_two_pow(q))),
                    h)
                  +hwt = wnat_and_mask_eq(p, q, wt, hT)
                  Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t}, Word.and(p, wt, Bits.mask(p, q)), wt, hwt)

# ------------------------------------------------------------------ U32 comparison
def wnat_u32_lt_const(y: U32, c: U32)
  -> {U32.is_lt(y, c) == Nat.is_lt(U32.to_nat(y), U32.to_nat(c)) : Bool}:
  match y:
    case U32{yw}:
      match c:
        case U32{cw}:
          Equal.cong(Cmp, Bool, Cmp.is_lt, Word.cmp(32n, yw, cw),
            Nat.cmp(Word.to_nat(32n, yw), Word.to_nat(32n, cw)),
            wnat_w_cmp(32n, yw, cw))

def wnat_u32_lt32(y: U32) -> {U32.is_lt(y, 32) == Nat.is_lt(U32.to_nat(y), 32n) : Bool}:
  wnat_u32_lt_const(y, 32)

def wnat_u32_lt64(y: U32) -> {U32.is_lt(y, 64) == Nat.is_lt(U32.to_nat(y), 64n) : Bool}:
  wnat_u32_lt_const(y, 64)

# ------------------------------------------------------------------ mask split
# `to_nat y` (for `y < 64`) is `to_nat(and(y,31))` plus bit 5.
def wnat_mask_decomp(+yw: Word(32n), +h: {Nat.is_lt(Word.to_nat(32n, yw), 64n) == True{} : Bool})
  -> {Word.to_nat(32n, yw) == Nat.add(Word.to_nat(32n, Word.and(32n, yw, Bits.mask(32n, 5n))),
                                    Bool.pick(Nat, Dirtyn.dwin_get(32n, yw, 5n), 32n, 0n)) : Nat}:
  +h_and = wnat_and_mask_eq(32n, 6n, yw, h)
  +hstep = wnat_mask_step(32n, 5n, yw)
  +hleft = Equal.sym(Nat,
    Word.to_nat(32n, Word.and(32n, yw, Bits.mask(32n, 6n))),
    Word.to_nat(32n, yw),
    Equal.cong(Word(32n), Nat, w => Word.to_nat(32n, w), Word.and(32n, yw, Bits.mask(32n, 6n)), yw, h_and))
  Equal.trans(Nat,
    Word.to_nat(32n, yw),
    Word.to_nat(32n, Word.and(32n, yw, Bits.mask(32n, 6n))),
    Nat.add(Word.to_nat(32n, Word.and(32n, yw, Bits.mask(32n, 5n))), Bool.pick(Nat, Dirtyn.dwin_get(32n, yw, 5n), 32n, 0n)),
    hleft,
    hstep)

# In the high half, `to_nat y = 32 + to_nat(and(y,31))`.
def wnat_hi_dec(+b5: Bool, +A: Nat, +ty: Nat,
    +hd: {ty == Nat.add(A, Bool.pick(Nat, b5, 32n, 0n)) : Nat},
    +hge: {Nat.is_lt(ty, 32n) == False{} : Bool},
    +hA: {Nat.is_lt(A, 32n) == True{} : Bool})
  -> {ty == Nat.add(32n, A) : Nat}:
  match b5:
    case True{}:
      Equal.trans(Nat, ty, Nat.add(A, 32n), Nat.add(32n, A), hd, NatL.n_add_comm(A, 32n))
    case False{}:
      +hdA = Equal.trans(Nat, ty, Nat.add(A, 0n), A, hd, NatL.n_add_zero_right(A))
      +hAge = Equal.trans(Bool, Nat.is_lt(A, 32n), Nat.is_lt(ty, 32n), False{},
        Equal.cong(Nat, Bool, z => Nat.is_lt(z, 32n), A, ty, Equal.sym(Nat, ty, A, hdA)), hge)
      +hTF = Equal.trans(Bool, True{}, Nat.is_lt(A, 32n), False{},
        Equal.sym(Bool, Nat.is_lt(A, 32n), True{}, hA), hAge)
      wnat_absurd(Nat, ty, Nat.add(32n, A), Equal.sym(Bool, True{}, False{}, hTF))

# ------------------------------------------------------------------ retirement (S1/W3)
# The `Dirty.Mask <-> Word(64)` split is now definitional, not a bridge: since
# `src/dirty.bend` holds the `Word(64)` directly and its row operations delegate
# to `src/dirtyn.bend`, `Dirty.is_dirty_y(m, y)` *is* `dwin_get(64, mask_word m,
# to_nat y)`. The lo/hi composition lemmas above (`wnat_dirty_true`/`_false`,
# `wnat_mask_get_lo`/`_hi`, `wnat_mask_word_get_z`) are therefore retired with
# the `Dirty.Mask{lo, hi}` representation; the law below is now `{==}`.
# The generic `wnat_*` value theory above (the `Word.cmp`/`Nat.cmp` bridge, the
# masked-value bound, the mask split) is size-agnostic and kept.

# The `Dirty.Mask <-> Word(64)` index bridge, now definitional.
def wnat_mask_word_get(+m: Dirty.Mask, +y: U32, +h: {U32.is_lt(y, 64) == True{} : Bool})
  -> {Dirty.is_dirty_y(m, y) == Dirtyn.dwin_get(64n, Maskword.mask_word(m), U32.to_nat(y)) : Bool}:
  {==}
