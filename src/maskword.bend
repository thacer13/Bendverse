import Base
import ./bits.bend as Bits
import ./nat.bend as NatL
import ./dirty.bend as Dirty
import ./dirtyn.bend as Dirtyn

# ============================================================================
# maskword (S1 / PLAN `G-scale-2` item 3) -- the `Dirty.Mask <-> Word(64)`
# isomorphism.
#
# `Dirty.Mask{lo, hi}` is two `U32`s (bit `y & 31` of `lo` for `y < 32`, else of
# `hi`); `Dirtyn`'s model is a `Word(w)` (head = bit 0, LSB first). The two agree
# only by test (T94); this module proves the bridge. The 64-bit word is
# `mask_word m = cat 32 lo hi`, where `cat` places `lo` in bits 0..31 and `hi` in
# 32..63 (`Word(Nat.add(32n, n))` -- `32` is a literal, so the width index
# reduces).
#
# The development is bottom-up:
#   * `and_wbit`      -- `and(w, {k})` is `{k}` or `0` by bit `k` of `w`;
#   * `cmp_wbit_zero` -- a single-bit word is non-zero (so `is_ne` is `True`);
#   * `shln_one`      -- `U32.shln(1, k) = U32{Dirtyn.dwin_bit(32, k)}`;
#   * `u32_bit`       -- `U32.is_ne(and(a, shln(1,k)), 0) = dwin_get(32, aWord, k)`;
#   * `cat_get`       -- `dwin_get` into the concatenation (the 64-bit split);
#   * `mask_word_get` -- the law: `dwin_get(64, mask_word m, y) = is_dirty_y(m,y)`.
# ============================================================================

# `cat n lo hi`: `lo` (width n) in the low bits, `hi` (width 32) in the high bits.
def cat(n: Nat, lo: Word(n), hi: Word(32n)) -> Word(Nat.add(32n, n)):
  match n:
    case 0n:
      hi
    case 1n+ +p:
      match lo:
        case WCon{h, t}:
          WCon{h, cat(p, t, hi)}

def u32_word(a: U32) -> Word(32n):
  match a:
    case U32{w}: w

def mask_word(m: Dirty.Mask) -> Word(64n):
  match m:
    case Dirty.Mask{lo, hi}:
      cat(32n, u32_word(lo), u32_word(hi))

# ------------------------------------------------------------------ bit algebra
def pick_cons_false(p: Nat, +b: Bool, +x: Word(p), +y: Word(p))
  -> {WCon{False{}, Bool.pick(Word(p), b, x, y)} == Bool.pick(Word(1n+p), b, WCon{False{}, x}, WCon{False{}, y}) : Word(1n+p)}:
  match b:
    case True{}: {==}
    case False{}: {==}

def pick_wbit0(p: Nat, +h: Bool)
  -> {WCon{h, Word.zero(p)} == Bool.pick(Word(1n+p), h, WCon{True{}, Word.zero(p)}, WCon{False{}, Word.zero(p)}) : Word(1n+p)}:
  match h:
    case True{}: {==}
    case False{}: {==}

def and_wbit(n: Nat, +w: Word(n), +k: Nat)
  -> {Word.and(n, w, Dirtyn.dwin_bit(n, k)) == Bool.pick(Word(n), Dirtyn.dwin_get(n, w, k), Dirtyn.dwin_bit(n, k), Word.zero(n)) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match w:
        case WCon{h, t}:
          match k:
            case 0n:
              +ha = Bits.b_and_true(h)
              +hb = Bits.w_and_zero(p, t)
              +h1 = Equal.cong(Bool, Word(1n+p), a => WCon{a, Word.and(p, t, Word.zero(p))}, Bool.and(h, True{}), h, ha)
              +h2 = Equal.cong(Word(p), Word(1n+p), a => WCon{h, a}, Word.and(p, t, Word.zero(p)), Word.zero(p), hb)
              +hlhs = Equal.trans(Word(1n+p), WCon{Bool.and(h, True{}), Word.and(p, t, Word.zero(p))}, WCon{h, Word.and(p, t, Word.zero(p))}, WCon{h, Word.zero(p)}, h1, h2)
              Equal.trans(Word(1n+p), Word.and(1n+p, WCon{h, t}, Dirtyn.dwin_bit(1n+p, 0n)), WCon{h, Word.zero(p)}, Bool.pick(Word(1n+p), h, Dirtyn.dwin_bit(1n+p, 0n), Word.zero(1n+p)), hlhs, pick_wbit0(p, h))
            case 1n+ +q:
              +ih = and_wbit(p, t, q)
              +ha = Bits.b_and_false(h)
              +h0 = Equal.cong(Bool, Word(1n+p), a => WCon{a, Word.and(p, t, Dirtyn.dwin_bit(p, q))}, Bool.and(h, False{}), False{}, ha)
              +hih = Equal.cong(Word(p), Word(1n+p), a => WCon{False{}, a}, Word.and(p, t, Dirtyn.dwin_bit(p, q)), Bool.pick(Word(p), Dirtyn.dwin_get(p, t, q), Dirtyn.dwin_bit(p, q), Word.zero(p)), ih)
              +hlhs = Equal.trans(Word(1n+p), WCon{Bool.and(h, False{}), Word.and(p, t, Dirtyn.dwin_bit(p, q))}, WCon{False{}, Word.and(p, t, Dirtyn.dwin_bit(p, q))}, WCon{False{}, Bool.pick(Word(p), Dirtyn.dwin_get(p, t, q), Dirtyn.dwin_bit(p, q), Word.zero(p))}, h0, hih)
              Equal.trans(Word(1n+p), Word.and(1n+p, WCon{h, t}, Dirtyn.dwin_bit(1n+p, 1n+q)), WCon{False{}, Bool.pick(Word(p), Dirtyn.dwin_get(p, t, q), Dirtyn.dwin_bit(p, q), Word.zero(p))}, Bool.pick(Word(1n+p), Dirtyn.dwin_get(1n+p, WCon{h, t}, 1n+q), Dirtyn.dwin_bit(1n+p, 1n+q), Word.zero(1n+p)), hlhs, pick_cons_false(p, Dirtyn.dwin_get(p, t, q), Dirtyn.dwin_bit(p, q), Word.zero(p)))

# `cmp` of the all-zero word with itself is `EQ`.
def cmp_zero_zero(n: Nat) -> {Word.cmp(n, Word.zero(n), Word.zero(n)) == EQ{} : Cmp}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      Equal.cong(Cmp, Cmp, t => Word.cmp.fin(False{}, False{}, t),
        Word.cmp(p, Word.zero(p), Word.zero(p)), EQ{}, cmp_zero_zero(p))

# A single-bit word is greater than the all-zero word (so `is_eq` is `False`).
def cmp_wbit_zero(n: Nat, +k: Nat, h: {Nat.is_lt(k, n) == True{} : Bool})
  -> {Word.cmp(n, Dirtyn.dwin_bit(n, k), Word.zero(n)) == GT{} : Cmp}:
  match n:
    case 0n:
      +hf = Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{},
        Equal.sym(Bool, Nat.is_lt(k, 0n), False{}, NatL.n_not_lt_zero(k)), h)
      Equal.cong(Bool, Cmp, z => Bool.pick(Cmp, z, GT{}, EQ{}), False{}, True{}, hf)
    case 1n+ +p:
      match k:
        case 0n:
          Equal.cong(Cmp, Cmp, t => Word.cmp.fin(True{}, False{}, t),
            Word.cmp(p, Word.zero(p), Word.zero(p)), EQ{}, cmp_zero_zero(p))
        case 1n+ +q:
          Equal.cong(Cmp, Cmp, t => Word.cmp.fin(False{}, False{}, t),
            Word.cmp(p, Dirtyn.dwin_bit(p, q), Word.zero(p)), GT{}, cmp_wbit_zero(p, q, h))

# `shl.put` with a `False` on the zero word is the zero word.
def shlput_zero(n: Nat) -> {Word.shl.put(n, False{}, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p), shlput_zero(p))

# `shl.put` with a `True` on the zero word is the single-bit word `{0}`.
def shlput_true_bit0(n: Nat)
  -> {Word.shl.put(n, True{}, Word.zero(n)) == Dirtyn.dwin_bit(n, 0n) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p), shlput_zero(p))

# `shl.put` with a `False` shifts the single-bit word up one position.
def shlput_bit(n: Nat, +k: Nat)
  -> {Word.shl.put(n, False{}, Dirtyn.dwin_bit(n, k)) == Dirtyn.dwin_bit(n, Nat.add(1n, k)) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      match k:
        case 0n:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.shl.put(p, True{}, Word.zero(p)), Dirtyn.dwin_bit(p, 0n), shlput_true_bit0(p))
        case 1n+ +q:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.shl.put(p, False{}, Dirtyn.dwin_bit(p, q)), Dirtyn.dwin_bit(p, Nat.add(1n, q)), shlput_bit(p, q))

# `Word.shl` shifts the single-bit 32-bit word up one position (dropping bit 31).
def shl_bit_32(k: Nat)
  -> {Word.shl(32n, Dirtyn.dwin_bit(32n, k)) == Dirtyn.dwin_bit(32n, Nat.add(1n, k)) : Word(32n)}:
  match k:
    case 0n:
      Equal.cong(Word(31n), Word(32n), t => WCon{False{}, t},
        Word.shl.put(31n, True{}, Word.zero(31n)), Dirtyn.dwin_bit(31n, 0n), shlput_true_bit0(31n))
    case 1n+ +q:
      Equal.cong(Word(31n), Word(32n), t => WCon{False{}, t},
        Word.shl.put(31n, False{}, Dirtyn.dwin_bit(31n, q)), Dirtyn.dwin_bit(31n, Nat.add(1n, q)), shlput_bit(31n, q))

# `U32.shln(1, k)` is the `U32` wrapping of the single-bit word `{k}`.
def shln_one(k: Nat)
  -> {U32.shln(1, k) == U32{Dirtyn.dwin_bit(32n, k)} : U32}:
  match k:
    case 0n:
      {==}
    case 1n+ +q:
      Equal.trans(U32,
        U32.shln(1, 1n+q),
        U32{Word.shl(32n, Dirtyn.dwin_bit(32n, q))},
        U32{Dirtyn.dwin_bit(32n, Nat.add(1n, q))},
        Equal.cong(U32, U32, a => U32.shl(a), U32.shln(1, q), U32{Dirtyn.dwin_bit(32n, q)}, shln_one(q)),
        Equal.cong(Word(32n), U32, w => U32{w},
          Word.shl(32n, Dirtyn.dwin_bit(32n, q)), Dirtyn.dwin_bit(32n, Nat.add(1n, q)), shl_bit_32(q)))

# A single-bit word is non-zero, so `is_ne(_, 0)` is `True`.
def is_ne_wbit(k: Nat, h: {Nat.is_lt(k, 32n) == True{} : Bool})
  -> {U32.is_ne(U32{Dirtyn.dwin_bit(32n, k)}, 0) == True{} : Bool}:
  +hc = cmp_wbit_zero(32n, k, h)
  Equal.cong(Cmp, Bool, c => Bool.not(Cmp.is_eq(c)),
    Word.cmp(32n, Dirtyn.dwin_bit(32n, k), Word.zero(32n)), GT{}, hc)

# `is_ne` on the `pick` of a single bit and zero is the pick condition.
def is_ne_pick_wbit(k: Nat, +b: Bool, h: {Nat.is_lt(k, 32n) == True{} : Bool})
  -> {U32.is_ne(U32{Bool.pick(Word(32n), b, Dirtyn.dwin_bit(32n, k), Word.zero(32n))}, 0) == b : Bool}:
  match b:
    case True{}:
      is_ne_wbit(k, h)
    case False{}:
      {==}

# The U32 bit test: `is_ne(and(a, shln(1, k)), 0)` is bit `k` of `a`'s word.
def u32_bit(a: U32, +k: Nat, h: {Nat.is_lt(k, 32n) == True{} : Bool})
  -> {U32.is_ne(U32.and(a, U32.shln(1, k)), 0) == Dirtyn.dwin_get(32n, u32_word(a), k) : Bool}:
  match a:
    case U32{aw0}:
      +aw = aw0
      +hs = shln_one(k)
      +hw = and_wbit(32n, aw, k)
      +hA = Equal.cong(U32, U32, b => U32.and(U32{aw}, b), U32.shln(1, k), U32{Dirtyn.dwin_bit(32n, k)}, hs)
      +hW = Equal.cong(Word(32n), U32, w => U32{w},
        Word.and(32n, aw, Dirtyn.dwin_bit(32n, k)),
        Bool.pick(Word(32n), Dirtyn.dwin_get(32n, aw, k), Dirtyn.dwin_bit(32n, k), Word.zero(32n)), hw)
      +hU = Equal.trans(U32,
        U32.and(U32{aw}, U32.shln(1, k)),
        U32.and(U32{aw}, U32{Dirtyn.dwin_bit(32n, k)}),
        U32{Bool.pick(Word(32n), Dirtyn.dwin_get(32n, aw, k), Dirtyn.dwin_bit(32n, k), Word.zero(32n))},
        hA, hW)
      Equal.trans(Bool,
        U32.is_ne(U32.and(U32{aw}, U32.shln(1, k)), 0),
        U32.is_ne(U32{Bool.pick(Word(32n), Dirtyn.dwin_get(32n, aw, k), Dirtyn.dwin_bit(32n, k), Word.zero(32n))}, 0),
        Dirtyn.dwin_get(32n, aw, k),
        Equal.cong(U32, Bool, x => U32.is_ne(x, 0), U32.and(U32{aw}, U32.shln(1, k)),
          U32{Bool.pick(Word(32n), Dirtyn.dwin_get(32n, aw, k), Dirtyn.dwin_bit(32n, k), Word.zero(32n))}, hU),
        is_ne_pick_wbit(k, Dirtyn.dwin_get(32n, aw, k), h))

# ------------------------------------------------------------------ cat split
# A `dwin_get` whose index falls in the low `n` bits reads `lo`.
def cat_get_low(n: Nat, lo: Word(n), hi: Word(32n), +y: Nat, h: {Nat.is_lt(y, n) == True{} : Bool})
  -> {Dirtyn.dwin_get(Nat.add(32n, n), cat(n, lo, hi), y) == Dirtyn.dwin_get(n, lo, y) : Bool}:
  match n:
    case 0n:
      +hf = Equal.trans(Bool, False{}, Nat.is_lt(y, 0n), True{},
        Equal.sym(Bool, Nat.is_lt(y, 0n), False{}, NatL.n_not_lt_zero(y)), h)
      Equal.cong(Bool, Bool, z => Bool.pick(Bool, z, False{}, Dirtyn.dwin_get(32n, hi, y)), False{}, True{}, hf)
    case 1n+ +p:
      match lo:
        case WCon{lh, lt}:
          match y:
            case 0n:
              {==}
            case 1n+ +q:
              cat_get_low(p, lt, hi, q, h)

# A `dwin_get` whose index has walked past the low `n` bits reads `hi`.
def cat_get_high(n: Nat, lo: Word(n), hi: Word(32n), y: Nat)
  -> {Dirtyn.dwin_get(Nat.add(32n, n), cat(n, lo, hi), Nat.add(n, y)) == Dirtyn.dwin_get(32n, hi, y) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+ +p:
      match lo:
        case WCon{lh, lt}:
          cat_get_high(p, lt, hi, y)
