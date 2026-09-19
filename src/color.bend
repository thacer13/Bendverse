import Base
import ./bits.bend as Bits
import ./grid.bend as Grid
import ./rules.bend as Rules
import ./parity.bend as Parity
import ./priority.bend as Priority
import ./word.bend as Word

# ------------------------------------------------------------------ V0-3b
# `color_of` bit extraction.
#
# `Rules.color_of(i) = (ix(i) & 1) | ((iy(i) & 1) << 1) | ((iz(i) & 1) << 2)`
# packs the three coordinate parities into bits 0..2. The cross-direction target
# classification needs the *inverse*: bit `k` of `color_of(i)` is the parity of
# coordinate `k`. These lemmas extract it (`bit0` of bit 0, of the 1-shift, and
# of the 2-shift), so equal colours force equal coordinate parities.

def bit0_or(+n: Nat, +a: Word(n), +b: Word(n))
  -> {Parity.bit0(n, Word.or(n, a, b)) == Bool.or(Parity.bit0(n, a), Parity.bit0(n, b)) : Bool}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          {==}

def bit0_and(+n: Nat, +a: Word(n), +b: Word(n))
  -> {Parity.bit0(n, Word.and(n, a, b)) == Bool.and(Parity.bit0(n, a), Parity.bit0(n, b)) : Bool}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          {==}

def bit0_shl(+n: Nat, +X: Word(n)) -> {Parity.bit0(n, Word.shl(n, X)) == False{} : Bool}:
  match n:
    case 0n:
      match X:
        case WNil{}:
          {==}
    case 1n+p:
      match X:
        case WCon{h, t}:
          {==}

def mask_zero(n: Nat) -> {Bits.mask(n, 0n) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def bit0_mask1() -> {Parity.bit0(32n, Bits.mask(32n, 1n)) == True{} : Bool}:
  {==}

def bit0_mask31() -> {Parity.bit0(32n, Bits.mask(32n, 31n)) == True{} : Bool}:
  {==}

def shr_and_mask1_zero(+n: Nat, +X: Word(n))
  -> {Word.shr(n, Word.and(n, X, Bits.mask(n, 1n))) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match X:
        case WNil{}:
          {==}
    case 1n+p:
      match X:
        case WCon{h, t}:
          +e_m = Equal.cong(Word(p), Word(p), s => Word.and(p, t, s), Bits.mask(p, 0n), Word.zero(p), mask_zero(p))
          +e_and = Equal.trans(Word(p), Word.and(p, t, Bits.mask(p, 0n)), Word.and(p, t, Word.zero(p)), Word.zero(p),
            e_m, Bits.w_and_zero(p, t))
          +e = Equal.cong(Word(p), Word(1n+p), s => Word.shr.pad(p, s),
            Word.and(p, t, Bits.mask(p, 0n)), Word.zero(p), e_and)
          Equal.trans(Word(1n+p),
            Word.shr(1n+p, Word.and(1n+p, WCon{h, t}, Bits.mask(1n+p, 1n))),
            Word.shr.pad(p, Word.and(p, t, Bits.mask(p, 0n))),
            Word.zero(1n+p),
            {==},
            Equal.trans(Word(1n+p),
              Word.shr.pad(p, Word.and(p, t, Bits.mask(p, 0n))),
              Word.shr.pad(p, Word.zero(p)),
              Word.zero(1n+p),
              e,
              Bits.shr_pad_zero(p)))

# color_bit0: bit 0 of the packed colour is the x parity.
def color_bit0(+i: U32) -> {Parity.par32(Rules.color_of(i)) == Parity.par32(Grid.ix(i)) : Bool}:
  match i:
    case U32{w}:
      +m1 = Bits.mask(32n, 1n)
      +m6 = Bits.mask(32n, 6n)
      +A = Word.and(32n, Word.and(32n, w, m6), m1)
      +B0 = Word.and(32n, Word.and(32n, Bits.shr_n(32n, 12n, w), m6), m1)
      +B = Word.shl(32n, B0)
      +C0 = Word.and(32n, Word.and(32n, Bits.shr_n(32n, 6n, w), m6), m1)
      +C = Word.shl(32n, Word.shl(32n, C0))
      +bA = Parity.bit0(32n, A)
      +bB = Parity.bit0(32n, B)
      +bC = Parity.bit0(32n, C)
      +bw6 = Parity.bit0(32n, Word.and(32n, w, m6))
      +E0 = Parity.bit0(32n, Word.or(32n, Word.or(32n, A, B), C))
      +E1 = Bool.or(Parity.bit0(32n, Word.or(32n, A, B)), bC)
      +E2 = Bool.or(Bool.or(bA, bB), bC)
      +E3 = Bool.or(Bool.or(bA, bB), False{})
      +E4 = Bool.or(bA, bB)
      +E5 = Bool.or(bA, False{})
      +E6 = bA
      +E7 = Bool.and(bw6, Parity.bit0(32n, m1))
      +E8 = Bool.and(bw6, True{})
      +e1 = bit0_or(32n, Word.or(32n, A, B), C)
      +e2 = bit0_or(32n, A, B)
      +e3 = bit0_shl(32n, Word.shl(32n, Word.and(32n, Word.and(32n, Bits.shr_n(32n, 6n, w), m6), m1)))
      +e4 = bit0_shl(32n, Word.and(32n, Word.and(32n, Bits.shr_n(32n, 12n, w), m6), m1))
      +e5 = bit0_and(32n, Word.and(32n, w, m6), m1)
      +e6 = bit0_mask1()
      +e7 = Bits.b_and_true(bw6)
      +c2 = Equal.cong(Bool, Bool, t => Bool.or(t, bC), Parity.bit0(32n, Word.or(32n, A, B)), Bool.or(bA, bB), e2)
      +c3 = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(bA, bB), t), bC, False{}, e3)
      +c4 = Equal.cong(Bool, Bool, t => Bool.or(bA, t), bB, False{}, e4)
      +c6 = Equal.cong(Bool, Bool, t => Bool.and(bw6, t), Parity.bit0(32n, m1), True{}, e6)
      Equal.trans(Bool, E0, E4, bw6,
        Equal.trans(Bool, E0, E2, E4,
          Equal.trans(Bool, E0, E1, E2, e1, c2),
          Equal.trans(Bool, E2, E3, E4, c3, Bits.b_or_false(Bool.or(bA, bB)))),
        Equal.trans(Bool, E4, E6, bw6,
          Equal.trans(Bool, E4, E5, E6, c4, Bits.b_or_false(bA)),
          Equal.trans(Bool, E6, E7, bw6, e5,
            Equal.trans(Bool, E7, E8, bw6, c6, e7))))

# color_bit1: bit 1 of the packed colour is the y parity.
def color_bit1(+i: U32) -> {Parity.par32(U32.shrn(Rules.color_of(i), 1n)) == Parity.par32(Grid.iy(i)) : Bool}:
  match i:
    case U32{w}:
      +m1 = Bits.mask(32n, 1n)
      +m6 = Bits.mask(32n, 6n)
      +m31 = Bits.mask(32n, 31n)
      +A = Word.and(32n, Word.and(32n, w, m6), m1)
      +B0 = Word.and(32n, Word.and(32n, Bits.shr_n(32n, 12n, w), m6), m1)
      +B = Word.shl(32n, B0)
      +C0 = Word.and(32n, Word.and(32n, Bits.shr_n(32n, 6n, w), m6), m1)
      +C = Word.shl(32n, Word.shl(32n, C0))
      +sA = Word.shr(32n, A)
      +sB = Word.shr(32n, B)
      +sC = Word.shr(32n, C)
      +rA = Parity.bit0(32n, sA)
      +rB = Parity.bit0(32n, sB)
      +rC = Parity.bit0(32n, sC)
      +tB = Word.and(32n, B0, m31)
      +tC = Word.and(32n, Word.shl(32n, C0), m31)
      +bw12 = Parity.bit0(32n, Word.and(32n, Bits.shr_n(32n, 12n, w), m6))
      +L0 = Parity.bit0(32n, Word.shr(32n, Word.or(32n, Word.or(32n, A, B), C)))
      +L1 = Parity.bit0(32n, Word.or(32n, Word.or(32n, sA, sB), sC))
      +L2 = Bool.or(Bool.or(rA, rB), rC)
      +L3 = Bool.or(Bool.or(False{}, rB), False{})
      +L4 = rB
      +L5 = Parity.bit0(32n, tB)
      +L6 = Parity.bit0(32n, B0)
      +e_shr = Equal.trans(Word(32n), Word.shr(32n, Word.or(32n, Word.or(32n, A, B), C)),
        Word.or(32n, Word.shr(32n, Word.or(32n, A, B)), sC),
        Word.or(32n, Word.or(32n, sA, sB), sC),
        Bits.shr_or(32n, Word.or(32n, A, B), C),
        Equal.cong(Word(32n), Word(32n), t => Word.or(32n, t, sC),
          Word.shr(32n, Word.or(32n, A, B)), Word.or(32n, sA, sB), Bits.shr_or(32n, A, B)))
      +e_a = shr_and_mask1_zero(32n, Word.and(32n, w, m6))
      +e_c = Bits.shr_shl_one(31n, Word.shl(32n, C0))
      +e_b = Bits.shr_shl_one(31n, B0)
      +e1 = bit0_or(32n, Word.or(32n, sA, sB), sC)
      +e2 = bit0_or(32n, sA, sB)
      +e3 = bit0_shl(32n, C0)
      +e_ba = Equal.trans(Bool, rA, Parity.bit0(32n, Word.zero(32n)), False{},
        Equal.cong(Word(32n), Bool, t => Parity.bit0(32n, t), sA, Word.zero(32n), e_a),
        {==})
      +e_sc = Equal.trans(Bool, rC, Parity.bit0(32n, tC), False{},
        Equal.cong(Word(32n), Bool, t => Parity.bit0(32n, t), sC, tC, e_c),
        Equal.trans(Bool,
          Parity.bit0(32n, tC),
          Parity.bit0(32n, Word.shl(32n, C0)),
          False{},
          Equal.trans(Bool,
            Parity.bit0(32n, tC),
            Bool.and(Parity.bit0(32n, Word.shl(32n, C0)), True{}),
            Parity.bit0(32n, Word.shl(32n, C0)),
            Equal.trans(Bool,
              Parity.bit0(32n, tC),
              Bool.and(Parity.bit0(32n, Word.shl(32n, C0)), Parity.bit0(32n, m31)),
              Bool.and(Parity.bit0(32n, Word.shl(32n, C0)), True{}),
              bit0_and(32n, Word.shl(32n, C0), m31),
              Equal.cong(Bool, Bool, t => Bool.and(Parity.bit0(32n, Word.shl(32n, C0)), t), Parity.bit0(32n, m31), True{}, bit0_mask31())),
            Bits.b_and_true(Parity.bit0(32n, Word.shl(32n, C0)))),
          e3))
      +e_bc = Equal.trans(Bool, rB, L5, L6,
        Equal.cong(Word(32n), Bool, t => Parity.bit0(32n, t), sB, tB, e_b),
        Equal.trans(Bool, L5, Bool.and(L6, True{}), L6,
          Equal.trans(Bool, L5, Bool.and(L6, Parity.bit0(32n, m31)), Bool.and(L6, True{}),
            bit0_and(32n, B0, m31),
            Equal.cong(Bool, Bool, t => Bool.and(L6, t), Parity.bit0(32n, m31), True{}, bit0_mask31())),
          Bits.b_and_true(L6)))
      +e_L6 = Equal.trans(Bool, L6, Bool.and(bw12, True{}), bw12,
        Equal.trans(Bool, L6, Bool.and(bw12, Parity.bit0(32n, m1)), Bool.and(bw12, True{}),
          bit0_and(32n, Word.and(32n, Bits.shr_n(32n, 12n, w), m6), m1),
          Equal.cong(Bool, Bool, t => Bool.and(bw12, t), Parity.bit0(32n, m1), True{}, bit0_mask1())),
        Bits.b_and_true(bw12))
      +c_d = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(t, rB), rC), rA, False{}, e_ba)
      +c_c = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(False{}, rB), t), rC, False{}, e_sc)
      Equal.trans(Bool, L0, L4, bw12,
        Equal.trans(Bool, L0, L2, L4,
          Equal.trans(Bool, L0, L1, L2,
            Equal.cong(Word(32n), Bool, t => Parity.bit0(32n, t),
              Word.shr(32n, Word.or(32n, Word.or(32n, A, B), C)),
              Word.or(32n, Word.or(32n, sA, sB), sC), e_shr),
            Equal.trans(Bool, L1, Bool.or(Parity.bit0(32n, Word.or(32n, sA, sB)), rC), L2,
              e1,
              Equal.cong(Bool, Bool, t => Bool.or(t, rC), Parity.bit0(32n, Word.or(32n, sA, sB)), Bool.or(rA, rB), e2))),
          Equal.trans(Bool, L2, L3, L4,
            Equal.trans(Bool, L2, Bool.or(Bool.or(False{}, rB), rC), L3, c_d, c_c),
            Equal.trans(Bool, L3, Bool.or(False{}, rB), L4,
              Bits.b_or_false(Bool.or(False{}, rB)),
              {==}))),
        Equal.trans(Bool, L4, L6, bw12, e_bc, e_L6))

# color_bit2: bit 2 of the packed colour is the z parity.
def color_bit2(+i: U32) -> {Parity.par32(U32.shrn(Rules.color_of(i), 2n)) == Parity.par32(Grid.iz(i)) : Bool}:
  match i:
    case U32{w}:
      +m1 = Bits.mask(32n, 1n)
      +m6 = Bits.mask(32n, 6n)
      +m31 = Bits.mask(32n, 31n)
      +A = Word.and(32n, Word.and(32n, w, m6), m1)
      +B0 = Word.and(32n, Word.and(32n, Bits.shr_n(32n, 12n, w), m6), m1)
      +B = Word.shl(32n, B0)
      +C0 = Word.and(32n, Word.and(32n, Bits.shr_n(32n, 6n, w), m6), m1)
      +C = Word.shl(32n, Word.shl(32n, C0))
      +E = Word.or(32n, Word.or(32n, A, B), C)
      +sA2 = Bits.shr_n(32n, 2n, A)
      +sB2 = Bits.shr_n(32n, 2n, B)
      +sC2 = Bits.shr_n(32n, 2n, C)
      +bA2 = Parity.bit0(32n, sA2)
      +bB2 = Parity.bit0(32n, sB2)
      +bC2 = Parity.bit0(32n, sC2)
      +bw6 = Parity.bit0(32n, Word.and(32n, Bits.shr_n(32n, 6n, w), m6))
      +L0 = Parity.bit0(32n, Bits.shr_n(32n, 2n, E))
      +L1 = Parity.bit0(32n, Word.or(32n, Word.or(32n, sA2, sB2), sC2))
      +L2 = Bool.or(Bool.or(bA2, bB2), bC2)
      +zA = Equal.trans(Word(32n), sA2, Word.shr(32n, Word.shr(32n, A)), Word.zero(32n),
        {==},
        Equal.trans(Word(32n), Word.shr(32n, Word.shr(32n, A)), Word.shr(32n, Word.zero(32n)), Word.zero(32n),
          Equal.cong(Word(32n), Word(32n), t => Word.shr(32n, t), Word.shr(32n, A), Word.zero(32n), shr_and_mask1_zero(32n, Word.and(32n, w, m6))),
          Bits.shr_zero(32n)))
      +zB1 = Bits.shr_shl_one(31n, B0)
      +zB0 = shr_and_mask1_zero(32n, Word.and(32n, Bits.shr_n(32n, 12n, w), m6))
      +zB2 = Bits.shr_and(32n, B0, m31)
      +zB = Equal.trans(Word(32n), sB2, Word.shr(32n, Word.shr(32n, B)), Word.zero(32n),
        {==},
        Equal.trans(Word(32n), Word.shr(32n, Word.shr(32n, B)), Word.shr(32n, Word.and(32n, B0, m31)), Word.zero(32n),
          Equal.cong(Word(32n), Word(32n), t => Word.shr(32n, t), Word.shr(32n, B), Word.and(32n, B0, m31), zB1),
          Equal.trans(Word(32n), Word.shr(32n, Word.and(32n, B0, m31)),
            Word.and(32n, Word.shr(32n, B0), Word.shr(32n, m31)), Word.zero(32n),
            zB2,
            Equal.trans(Word(32n), Word.and(32n, Word.shr(32n, B0), Word.shr(32n, m31)),
              Word.and(32n, Word.zero(32n), Word.shr(32n, m31)), Word.zero(32n),
              Equal.cong(Word(32n), Word(32n), t => Word.and(32n, t, Word.shr(32n, m31)),
                Word.shr(32n, B0), Word.zero(32n), zB0),
              Bits.w_and_zero(32n, Word.shr(32n, m31))))))
      +e_zA = Equal.trans(Bool, bA2, Parity.bit0(32n, Word.zero(32n)), False{},
        Equal.cong(Word(32n), Bool, t => Parity.bit0(32n, t), sA2, Word.zero(32n), zA),
        {==})
      +e_zB = Equal.trans(Bool, bB2, Parity.bit0(32n, Word.zero(32n)), False{},
        Equal.cong(Word(32n), Bool, t => Parity.bit0(32n, t), sB2, Word.zero(32n), zB),
        {==})
      +e_hC = Parity.shr_shl_kmask(2n, C0)
      +e_C0 = Equal.trans(Bool, bC2, Parity.bit0(32n, C0), bw6,
        Equal.trans(Bool, bC2, Parity.bit0(32n, Word.and(32n, C0, Parity.kmask(2n))), Parity.bit0(32n, C0),
          Equal.cong(Word(32n), Bool, t => Parity.bit0(32n, t), sC2, Word.and(32n, C0, Parity.kmask(2n)), e_hC),
          Equal.trans(Bool, Parity.bit0(32n, Word.and(32n, C0, Parity.kmask(2n))),
            Bool.and(Parity.bit0(32n, C0), True{}), Parity.bit0(32n, C0),
            Equal.trans(Bool, Parity.bit0(32n, Word.and(32n, C0, Parity.kmask(2n))),
              Bool.and(Parity.bit0(32n, C0), Parity.bit0(32n, Parity.kmask(2n))),
              Bool.and(Parity.bit0(32n, C0), True{}),
              bit0_and(32n, C0, Parity.kmask(2n)),
              Equal.cong(Bool, Bool, t => Bool.and(Parity.bit0(32n, C0), t),
                Parity.bit0(32n, Parity.kmask(2n)), True{}, {==})),
            Bits.b_and_true(Parity.bit0(32n, C0)))),
        Equal.trans(Bool, Parity.bit0(32n, C0),
          Bool.and(Parity.bit0(32n, Word.and(32n, Bits.shr_n(32n, 6n, w), m6)), True{}),
          Parity.bit0(32n, Word.and(32n, Bits.shr_n(32n, 6n, w), m6)),
          Equal.trans(Bool, Parity.bit0(32n, C0),
            Bool.and(Parity.bit0(32n, Word.and(32n, Bits.shr_n(32n, 6n, w), m6)), Parity.bit0(32n, m1)),
            Bool.and(Parity.bit0(32n, Word.and(32n, Bits.shr_n(32n, 6n, w), m6)), True{}),
            bit0_and(32n, Word.and(32n, Bits.shr_n(32n, 6n, w), m6), m1),
            Equal.cong(Bool, Bool, t => Bool.and(Parity.bit0(32n, Word.and(32n, Bits.shr_n(32n, 6n, w), m6)), t),
              Parity.bit0(32n, m1), True{}, bit0_mask1())),
          Bits.b_and_true(bw6)))
      +e_shr2 = Equal.trans(Word(32n), Bits.shr_n(32n, 2n, E),
        Word.or(32n, Bits.shr_n(32n, 2n, Word.or(32n, A, B)), sC2),
        Word.or(32n, Word.or(32n, sA2, sB2), sC2),
        Bits.shr_n_or(32n, 2n, Word.or(32n, A, B), C),
        Equal.cong(Word(32n), Word(32n), t => Word.or(32n, t, sC2),
          Bits.shr_n(32n, 2n, Word.or(32n, A, B)), Word.or(32n, sA2, sB2), Bits.shr_n_or(32n, 2n, A, B)))
      +e1 = bit0_or(32n, Word.or(32n, sA2, sB2), sC2)
      +e2 = bit0_or(32n, sA2, sB2)
      +c_d = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(t, bB2), bC2), bA2, False{}, e_zA)
      +c_b = Equal.cong(Bool, Bool, t => Bool.or(Bool.or(False{}, t), bC2), bB2, False{}, e_zB)
      Equal.trans(Bool, L0, bC2, bw6,
        Equal.trans(Bool, L0, L2, bC2,
          Equal.trans(Bool, L0, L1, L2,
            Equal.cong(Word(32n), Bool, t => Parity.bit0(32n, t),
              Bits.shr_n(32n, 2n, E), Word.or(32n, Word.or(32n, sA2, sB2), sC2), e_shr2),
            Equal.trans(Bool, L1, Bool.or(Parity.bit0(32n, Word.or(32n, sA2, sB2)), bC2), L2,
              e1,
              Equal.cong(Bool, Bool, t => Bool.or(t, bC2), Parity.bit0(32n, Word.or(32n, sA2, sB2)), Bool.or(bA2, bB2), e2))),
          Equal.trans(Bool, L2, Bool.or(Bool.or(False{}, bB2), bC2), bC2,
            c_d,
            Equal.trans(Bool, Bool.or(Bool.or(False{}, bB2), bC2), Bool.or(Bool.or(False{}, False{}), bC2), bC2,
              c_b, {==}))),
        e_C0)

# ------------------------------------------------------------------ parity target maps
# The x/z phase of a `dy = -1` target: a slide `(dx, -1, dz)` shifts the source's
# x and z parities by `par(dx)` and `par(dz)` respectively.
def target_x_par(+i: U32, +dx: U32, +dz: U32)
  -> {Parity.par32(Grid.ix(Grid.neighbor(i, dx, 4294967295, dz))) == Bool.xor(Parity.par32(Grid.ix(i)), Parity.par32(dx)) : Bool}:
  +addv = U32.add(Grid.ix(i), dx)
  Equal.trans(Bool,
    Parity.par32(Grid.ix(Grid.neighbor(i, dx, 4294967295, dz))),
    Parity.par32(U32.and(addv, 63)),
    Bool.xor(Parity.par32(Grid.ix(i)), Parity.par32(dx)),
    Equal.cong(U32, Bool, v => Parity.par32(v),
      Grid.ix(Grid.neighbor(i, dx, 4294967295, dz)), U32.and(addv, 63),
      Parity.u32_ix_neighbor(i, dx, 4294967295, dz)),
    Equal.trans(Bool,
      Parity.par32(U32.and(addv, 63)),
      Parity.par32(addv),
      Bool.xor(Parity.par32(Grid.ix(i)), Parity.par32(dx)),
      Parity.par32_mask6(addv),
      Parity.par32_add(Grid.ix(i), dx)))

def target_z_par(+i: U32, +dx: U32, +dz: U32)
  -> {Parity.par32(Grid.iz(Grid.neighbor(i, dx, 4294967295, dz))) == Bool.xor(Parity.par32(Grid.iz(i)), Parity.par32(dz)) : Bool}:
  +addv = U32.add(Grid.iz(i), dz)
  Equal.trans(Bool,
    Parity.par32(Grid.iz(Grid.neighbor(i, dx, 4294967295, dz))),
    Parity.par32(U32.and(addv, 63)),
    Bool.xor(Parity.par32(Grid.iz(i)), Parity.par32(dz)),
    Equal.cong(U32, Bool, v => Parity.par32(v),
      Grid.iz(Grid.neighbor(i, dx, 4294967295, dz)), U32.and(addv, 63),
      Priority.u32_iz_neighbor_full(i, dx, 4294967295, dz)),
    Equal.trans(Bool,
      Parity.par32(U32.and(addv, 63)),
      Parity.par32(addv),
      Bool.xor(Parity.par32(Grid.iz(i)), Parity.par32(dz)),
      Parity.par32_mask6(addv),
      Parity.par32_add(Grid.iz(i), dz)))

def not_eq_inv(+a: Bool, +b: Bool, +h: {Bool.not(a) == Bool.not(b) : Bool}) -> {a == b : Bool}:
  Equal.trans(Bool, a, Bool.not(Bool.not(a)), b,
    Equal.sym(Bool, Bool.not(Bool.not(a)), a, Bits.b_not_not(a)),
    Equal.trans(Bool, Bool.not(Bool.not(a)), Bool.not(Bool.not(b)), b,
      Equal.cong(Bool, Bool, t => Bool.not(t), Bool.not(a), Bool.not(b), h),
      Bits.b_not_not(b)))

def xor_cancel_left(+p: Bool, +a: Bool, +b: Bool, +h: {Bool.xor(p, a) == Bool.xor(p, b) : Bool}) -> {a == b : Bool}:
  match p:
    case False{}:
      h
    case True{}:
      not_eq_inv(a, b, h)

# Same colour => the three coordinate parities agree (the inverse of the packing).
def same_color_x(+i: U32, +j: U32, +hc: {U32.is_eq(Rules.color_of(i), Rules.color_of(j)) == True{} : Bool})
  -> {Parity.par32(Grid.ix(i)) == Parity.par32(Grid.ix(j)) : Bool}:
  +e = Word.u32_cmp_eq(Rules.color_of(i), Rules.color_of(j), hc)
  +ec = Equal.cong(U32, Bool, x => Parity.par32(x), Rules.color_of(i), Rules.color_of(j), e)
  Equal.trans(Bool,
    Parity.par32(Grid.ix(i)), Parity.par32(Rules.color_of(i)), Parity.par32(Grid.ix(j)),
    Equal.sym(Bool, Parity.par32(Rules.color_of(i)), Parity.par32(Grid.ix(i)), color_bit0(i)),
    Equal.trans(Bool, Parity.par32(Rules.color_of(i)), Parity.par32(Rules.color_of(j)), Parity.par32(Grid.ix(j)), ec, color_bit0(j)))

def same_color_y(+i: U32, +j: U32, +hc: {U32.is_eq(Rules.color_of(i), Rules.color_of(j)) == True{} : Bool})
  -> {Parity.par32(Grid.iy(i)) == Parity.par32(Grid.iy(j)) : Bool}:
  +e = Word.u32_cmp_eq(Rules.color_of(i), Rules.color_of(j), hc)
  +ec = Equal.cong(U32, Bool, x => Parity.par32(U32.shrn(x, 1n)), Rules.color_of(i), Rules.color_of(j), e)
  Equal.trans(Bool,
    Parity.par32(Grid.iy(i)), Parity.par32(U32.shrn(Rules.color_of(i), 1n)), Parity.par32(Grid.iy(j)),
    Equal.sym(Bool, Parity.par32(U32.shrn(Rules.color_of(i), 1n)), Parity.par32(Grid.iy(i)), color_bit1(i)),
    Equal.trans(Bool, Parity.par32(U32.shrn(Rules.color_of(i), 1n)), Parity.par32(U32.shrn(Rules.color_of(j), 1n)), Parity.par32(Grid.iy(j)), ec, color_bit1(j)))

def same_color_z(+i: U32, +j: U32, +hc: {U32.is_eq(Rules.color_of(i), Rules.color_of(j)) == True{} : Bool})
  -> {Parity.par32(Grid.iz(i)) == Parity.par32(Grid.iz(j)) : Bool}:
  +e = Word.u32_cmp_eq(Rules.color_of(i), Rules.color_of(j), hc)
  +ec = Equal.cong(U32, Bool, x => Parity.par32(U32.shrn(x, 2n)), Rules.color_of(i), Rules.color_of(j), e)
  Equal.trans(Bool,
    Parity.par32(Grid.iz(i)), Parity.par32(U32.shrn(Rules.color_of(i), 2n)), Parity.par32(Grid.iz(j)),
    Equal.sym(Bool, Parity.par32(U32.shrn(Rules.color_of(i), 2n)), Parity.par32(Grid.iz(i)), color_bit2(i)),
    Equal.trans(Bool, Parity.par32(U32.shrn(Rules.color_of(i), 2n)), Parity.par32(U32.shrn(Rules.color_of(j), 2n)), Parity.par32(Grid.iz(j)), ec, color_bit2(j)))

# The classification: a same-colour target collision forces equal displacement
# parities. Cross-direction collisions are therefore either same-direction (and
# injective, V0-3a) or the two opposite-diagonal parity classes (resolved by the
# V0-1 tie-break). The drop `(0, 0)` has parity `(False, False)`.
def same_color_target_x_par(
  +i: U32, +j: U32, +dxi: U32, +dzi: U32, +dxj: U32, +dzj: U32,
  +hc: {U32.is_eq(Rules.color_of(i), Rules.color_of(j)) == True{} : Bool},
  +ht: {Grid.neighbor(i, dxi, 4294967295, dzi) == Grid.neighbor(j, dxj, 4294967295, dzj) : U32}
) -> {Parity.par32(dxi) == Parity.par32(dxj) : Bool}:
  +ti = Grid.neighbor(i, dxi, 4294967295, dzi)
  +tj = Grid.neighbor(j, dxj, 4294967295, dzj)
  +pxi = Parity.par32(Grid.ix(i))
  +pxj = Parity.par32(Grid.ix(j))
  +pdxi = Parity.par32(dxi)
  +pdxj = Parity.par32(dxj)
  +epix = Equal.cong(U32, Bool, t => Parity.par32(t), Grid.ix(ti), Grid.ix(tj),
    Equal.cong(U32, U32, t => Grid.ix(t), ti, tj, ht))
  +ecross = Equal.trans(Bool,
    Bool.xor(pxi, pdxi), Parity.par32(Grid.ix(ti)), Bool.xor(pxj, pdxj),
    Equal.sym(Bool, Parity.par32(Grid.ix(ti)), Bool.xor(pxi, pdxi), target_x_par(i, dxi, dzi)),
    Equal.trans(Bool, Parity.par32(Grid.ix(ti)), Parity.par32(Grid.ix(tj)), Bool.xor(pxj, pdxj),
      epix, target_x_par(j, dxj, dzj)))
  +hcx = same_color_x(i, j, hc)
  +econg = Equal.sym(Bool, Bool.xor(pxi, pdxj), Bool.xor(pxj, pdxj),
    Equal.cong(Bool, Bool, t => Bool.xor(t, pdxj), pxi, pxj, hcx))
  xor_cancel_left(pxi, pdxi, pdxj, Equal.trans(Bool, Bool.xor(pxi, pdxi), Bool.xor(pxj, pdxj), Bool.xor(pxi, pdxj), ecross, econg))

def same_color_target_z_par(
  +i: U32, +j: U32, +dxi: U32, +dzi: U32, +dxj: U32, +dzj: U32,
  +hc: {U32.is_eq(Rules.color_of(i), Rules.color_of(j)) == True{} : Bool},
  +ht: {Grid.neighbor(i, dxi, 4294967295, dzi) == Grid.neighbor(j, dxj, 4294967295, dzj) : U32}
) -> {Parity.par32(dzi) == Parity.par32(dzj) : Bool}:
  +ti = Grid.neighbor(i, dxi, 4294967295, dzi)
  +tj = Grid.neighbor(j, dxj, 4294967295, dzj)
  +pzi = Parity.par32(Grid.iz(i))
  +pzj = Parity.par32(Grid.iz(j))
  +pdzi = Parity.par32(dzi)
  +pdzj = Parity.par32(dzj)
  +epiz = Equal.cong(U32, Bool, t => Parity.par32(t), Grid.iz(ti), Grid.iz(tj),
    Equal.cong(U32, U32, t => Grid.iz(t), ti, tj, ht))
  +ecross = Equal.trans(Bool,
    Bool.xor(pzi, pdzi), Parity.par32(Grid.iz(ti)), Bool.xor(pzj, pdzj),
    Equal.sym(Bool, Parity.par32(Grid.iz(ti)), Bool.xor(pzi, pdzi), target_z_par(i, dxi, dzi)),
    Equal.trans(Bool, Parity.par32(Grid.iz(ti)), Parity.par32(Grid.iz(tj)), Bool.xor(pzj, pdzj),
      epiz, target_z_par(j, dxj, dzj)))
  +hcz = same_color_z(i, j, hc)
  +econg = Equal.sym(Bool, Bool.xor(pzi, pdzj), Bool.xor(pzj, pdzj),
    Equal.cong(Bool, Bool, t => Bool.xor(t, pdzj), pzi, pzj, hcz))
  xor_cancel_left(pzi, pdzi, pdzj, Equal.trans(Bool, Bool.xor(pzi, pdzi), Bool.xor(pzj, pdzj), Bool.xor(pzi, pdzj), ecross, econg))
