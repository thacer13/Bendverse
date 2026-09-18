import Base
import ./bits.bend as Bits
import ./grid.bend as Grid
import ./nat.bend as NatL

def bit0(n: Nat, w: Word(n)) -> Bool:
  match n:
    case 0n:
      match w:
        case WNil{}:
          False{}
    case 1n+p:
      match w:
        case WCon{h, t}:
          h

def fst_b(p: Bool & Bool) -> Bool:
  match p:
    case (a, b):
      a

def full_add_fst_true(a: Bool) -> {fst_b(Bool.full_add(a, True{}, False{})) == Bool.not(a) : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def adc_con_head(p: Nat, at: Word(p), bt: Word(p), f: Bool, sk: Bool & Bool) -> {bit0(1n+p, Word.adc.con(p, at, bt, f, sk)) == fst_b(sk) : Bool}:
  match sk:
    case (s, k):
      {==}

def one(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, Word.zero(p)}

def ones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, ones(p)}

def add_one_flips(+p: Nat, a: Word(1n+p)) -> {bit0(1n+p, Word.add(1n+p, a, one(1n+p))) == Bool.not(bit0(1n+p, a)) : Bool}:
  match a:
    case WCon{+ah, at}:
      Equal.trans(Bool,
        bit0(1n+p, Word.add(1n+p, WCon{ah, at}, one(1n+p))),
        fst_b(Bool.full_add(ah, True{}, False{})),
        Bool.not(ah),
        adc_con_head(p, at, Word.zero(p), False{}, Bool.full_add(ah, True{}, False{})),
        full_add_fst_true(ah))

def add_ones_flips(+p: Nat, a: Word(1n+p)) -> {bit0(1n+p, Word.add(1n+p, a, ones(1n+p))) == Bool.not(bit0(1n+p, a)) : Bool}:
  match a:
    case WCon{+ah, at}:
      Equal.trans(Bool,
        bit0(1n+p, Word.add(1n+p, WCon{ah, at}, ones(1n+p))),
        fst_b(Bool.full_add(ah, True{}, False{})),
        Bool.not(ah),
        adc_con_head(p, at, ones(p), False{}, Bool.full_add(ah, True{}, False{})),
        full_add_fst_true(ah))

def par32(w: U32) -> Bool:
  match w:
    case U32{x}:
      bit0(32n, x)

def u32_add_one_flips(x: U32) -> {par32(U32.add(x, 1)) == Bool.not(par32(x)) : Bool}:
  match x:
    case U32{w}:
      add_one_flips(31n, w)

def u32_add_ones_flips(x: U32) -> {par32(U32.add(x, 4294967295)) == Bool.not(par32(x)) : Bool}:
  match x:
    case U32{w}:
      add_ones_flips(31n, w)

def shr6_m6() -> {Bits.shr_n(32n, 6n, Bits.mask(32n, 6n)) == Word.zero(32n) : Word(32n)}:
  {==}

def shr12_m6() -> {Bits.shr_n(32n, 12n, Bits.mask(32n, 6n)) == Word.zero(32n) : Word(32n)}:
  {==}

def shl_put_false_zero(+n: Nat) -> {Word.shl.put(n, False{}, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p), shl_put_false_zero(p))

def shl_zero_base(+n: Nat) -> {Word.shl(n, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p), shl_put_false_zero(p))

def shl_zero(+n: Nat, k: Nat) -> {Bits.shl_n(n, Word.zero(n), k) == Word.zero(n) : Word(n)}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      Equal.trans(Word(n),
        Bits.shl_n(n, Word.zero(n), 1n+q),
        Word.shl(n, Bits.shl_n(n, Word.zero(n), q)),
        Word.zero(n),
        {==},
        Equal.trans(Word(n),
          Word.shl(n, Bits.shl_n(n, Word.zero(n), q)),
          Word.shl(n, Word.zero(n)),
          Word.zero(n),
          Equal.cong(Word(n), Word(n), x => Word.shl(n, x), Bits.shl_n(n, Word.zero(n), q), Word.zero(n), shl_zero(n, q)),
          shl_zero_base(n)))

def shl6_zero() -> {Bits.shl_n(32n, Word.zero(32n), 6n) == Word.zero(32n) : Word(32n)}:
  shl_zero(32n, 6n)

def shl12_zero() -> {Bits.shl_n(32n, Word.zero(32n), 12n) == Word.zero(32n) : Word(32n)}:
  shl_zero(32n, 12n)

def and_zero_l(+n: Nat, +a: Word(n)) -> {Word.and(n, Word.zero(n), a) == Word.zero(n) : Word(n)}:
  Equal.trans(Word(n),
    Word.and(n, Word.zero(n), a),
    Word.and(n, a, Word.zero(n)),
    Word.zero(n),
    Bits.w_and_comm(n, Word.zero(n), a),
    Bits.w_and_zero(n, a))

def and_shift_zero6(+x: Word(32n)) -> {Word.and(32n, Bits.shl_n(32n, x, 6n), Bits.mask(32n, 6n)) == Word.zero(32n) : Word(32n)}:
  +sx = Bits.shl_n(32n, x, 6n)
  +m6 = Bits.mask(32n, 6n)
  +r = Bits.shr_n(32n, 6n, m6)
  +t2 = Bits.shl_n(32n, Word.and(32n, r, x), 6n)
  +t3 = Bits.shl_n(32n, Word.and(32n, Word.zero(32n), x), 6n)
  +t4 = Bits.shl_n(32n, Word.zero(32n), 6n)
  +e1 = Bits.w_and_comm(32n, sx, m6)
  +e2 = Bits.and_shl_n(32n, 6n, m6, x)
  +e3 = Equal.cong(Word(32n), Word(32n), s => Word.and(32n, s, x), r, Word.zero(32n), shr6_m6())
  +e4 = Equal.cong(Word(32n), Word(32n), m => Bits.shl_n(32n, m, 6n), Word.and(32n, r, x), Word.and(32n, Word.zero(32n), x), e3)
  +e5 = and_zero_l(32n, x)
  +e6 = Equal.cong(Word(32n), Word(32n), m => Bits.shl_n(32n, m, 6n), Word.and(32n, Word.zero(32n), x), Word.zero(32n), e5)
  +e7 = shl6_zero()
  Equal.trans(Word(32n),
    Word.and(32n, sx, m6),
    Word.and(32n, m6, sx),
    Word.zero(32n),
    e1,
    Equal.trans(Word(32n),
      Word.and(32n, m6, sx),
      t2,
      Word.zero(32n),
      e2,
      Equal.trans(Word(32n), t2, t3, Word.zero(32n), e4,
        Equal.trans(Word(32n), t3, t4, Word.zero(32n), e6, e7))))

def and_shift_zero12(+x: Word(32n)) -> {Word.and(32n, Bits.shl_n(32n, x, 12n), Bits.mask(32n, 6n)) == Word.zero(32n) : Word(32n)}:
  +sx = Bits.shl_n(32n, x, 12n)
  +m6 = Bits.mask(32n, 6n)
  +r = Bits.shr_n(32n, 12n, m6)
  +t2 = Bits.shl_n(32n, Word.and(32n, r, x), 12n)
  +t3 = Bits.shl_n(32n, Word.and(32n, Word.zero(32n), x), 12n)
  +t4 = Bits.shl_n(32n, Word.zero(32n), 12n)
  +e1 = Bits.w_and_comm(32n, sx, m6)
  +e2 = Bits.and_shl_n(32n, 12n, m6, x)
  +e3 = Equal.cong(Word(32n), Word(32n), s => Word.and(32n, s, x), r, Word.zero(32n), shr12_m6())
  +e4 = Equal.cong(Word(32n), Word(32n), m => Bits.shl_n(32n, m, 12n), Word.and(32n, r, x), Word.and(32n, Word.zero(32n), x), e3)
  +e5 = and_zero_l(32n, x)
  +e6 = Equal.cong(Word(32n), Word(32n), m => Bits.shl_n(32n, m, 12n), Word.and(32n, Word.zero(32n), x), Word.zero(32n), e5)
  +e7 = shl12_zero()
  Equal.trans(Word(32n),
    Word.and(32n, sx, m6),
    Word.and(32n, m6, sx),
    Word.zero(32n),
    e1,
    Equal.trans(Word(32n),
      Word.and(32n, m6, sx),
      t2,
      Word.zero(32n),
      e2,
      Equal.trans(Word(32n), t2, t3, Word.zero(32n), e4,
        Equal.trans(Word(32n), t3, t4, Word.zero(32n), e6, e7))))

def and_m6_absorb(+x: Word(32n)) -> {Word.and(32n, Bits.mask(32n, 6n), Word.and(32n, x, Bits.mask(32n, 6n))) == Word.and(32n, x, Bits.mask(32n, 6n)) : Word(32n)}:
  +m6 = Bits.mask(32n, 6n)
  Equal.trans(Word(32n),
    Word.and(32n, m6, Word.and(32n, x, m6)),
    Word.and(32n, Word.and(32n, m6, x), m6),
    Word.and(32n, x, m6),
    Equal.sym(Word(32n), Word.and(32n, Word.and(32n, m6, x), m6), Word.and(32n, m6, Word.and(32n, x, m6)), Bits.w_and_assoc(32n, m6, x, m6)),
    Equal.trans(Word(32n),
      Word.and(32n, Word.and(32n, m6, x), m6),
      Word.and(32n, Word.and(32n, x, m6), m6),
      Word.and(32n, x, m6),
      Equal.cong(Word(32n), Word(32n), r => Word.and(32n, r, m6), Word.and(32n, m6, x), Word.and(32n, x, m6), Bits.w_and_comm(32n, m6, x)),
      Bits.w_and_absorb(32n, x, m6)))

def and_m6_shift6_zero(+z: Word(32n)) -> {Word.and(32n, Bits.mask(32n, 6n), Bits.shl_n(32n, Word.and(32n, z, Bits.mask(32n, 6n)), 6n)) == Word.zero(32n) : Word(32n)}:
  Equal.trans(Word(32n),
    Word.and(32n, Bits.mask(32n, 6n), Bits.shl_n(32n, Word.and(32n, z, Bits.mask(32n, 6n)), 6n)),
    Word.and(32n, Bits.shl_n(32n, Word.and(32n, z, Bits.mask(32n, 6n)), 6n), Bits.mask(32n, 6n)),
    Word.zero(32n),
    Bits.w_and_comm(32n, Bits.mask(32n, 6n), Bits.shl_n(32n, Word.and(32n, z, Bits.mask(32n, 6n)), 6n)),
    and_shift_zero6(Word.and(32n, z, Bits.mask(32n, 6n))))

def and_m6_shift12_zero(+y: Word(32n)) -> {Word.and(32n, Bits.mask(32n, 6n), Bits.shl_n(32n, Word.and(32n, y, Bits.mask(32n, 6n)), 12n)) == Word.zero(32n) : Word(32n)}:
  Equal.trans(Word(32n),
    Word.and(32n, Bits.mask(32n, 6n), Bits.shl_n(32n, Word.and(32n, y, Bits.mask(32n, 6n)), 12n)),
    Word.and(32n, Bits.shl_n(32n, Word.and(32n, y, Bits.mask(32n, 6n)), 12n), Bits.mask(32n, 6n)),
    Word.zero(32n),
    Bits.w_and_comm(32n, Bits.mask(32n, 6n), Bits.shl_n(32n, Word.and(32n, y, Bits.mask(32n, 6n)), 12n)),
    and_shift_zero12(Word.and(32n, y, Bits.mask(32n, 6n))))

def or_zero_zero(+a: Word(32n)) -> {Word.or(32n, Word.or(32n, a, Word.zero(32n)), Word.zero(32n)) == a : Word(32n)}:
  Equal.trans(Word(32n),
    Word.or(32n, Word.or(32n, a, Word.zero(32n)), Word.zero(32n)),
    Word.or(32n, a, Word.zero(32n)),
    a,
    Bits.w_or_zero(32n, Word.or(32n, a, Word.zero(32n))),
    Bits.w_or_zero(32n, a))

def low6_pack(+x: Word(32n), +y: Word(32n), +z: Word(32n)) -> {Word.and(32n, Word.or(32n, Word.or(32n, Word.and(32n, x, Bits.mask(32n, 6n)), Bits.shl_n(32n, Word.and(32n, z, Bits.mask(32n, 6n)), 6n)), Bits.shl_n(32n, Word.and(32n, y, Bits.mask(32n, 6n)), 12n)), Bits.mask(32n, 6n)) == Word.and(32n, x, Bits.mask(32n, 6n)) : Word(32n)}:
  +m6 = Bits.mask(32n, 6n)
  +A = Word.and(32n, x, m6)
  +B = Bits.shl_n(32n, Word.and(32n, z, m6), 6n)
  +C = Bits.shl_n(32n, Word.and(32n, y, m6), 12n)
  +P = Word.or(32n, Word.or(32n, A, B), C)
  +g1 = Bits.w_and_comm(32n, P, m6)
  +g2 = Bits.w_and_or(32n, m6, Word.or(32n, A, B), C)
  +h1 = Bits.w_and_or(32n, m6, A, B)
  +h2 = and_m6_absorb(x)
  +h3 = and_m6_shift6_zero(z)
  +h4 = Equal.cong(Word(32n), Word(32n), v => Word.or(32n, v, Word.and(32n, m6, B)), Word.and(32n, m6, A), A, h2)
  +h5 = Equal.cong(Word(32n), Word(32n), v => Word.or(32n, A, v), Word.and(32n, m6, B), Word.zero(32n), h3)
  +h7 = Equal.trans(Word(32n),
    Word.and(32n, m6, Word.or(32n, A, B)),
    Word.or(32n, Word.and(32n, m6, A), Word.and(32n, m6, B)),
    Word.or(32n, A, Word.zero(32n)),
    h1,
    Equal.trans(Word(32n),
      Word.or(32n, Word.and(32n, m6, A), Word.and(32n, m6, B)),
      Word.or(32n, A, Word.and(32n, m6, B)),
      Word.or(32n, A, Word.zero(32n)),
      h4, h5))
  +k1 = and_m6_shift12_zero(y)
  +g2b = Equal.trans(Word(32n),
    Word.and(32n, m6, P),
    Word.or(32n, Word.and(32n, m6, Word.or(32n, A, B)), Word.and(32n, m6, C)),
    Word.or(32n, Word.or(32n, A, Word.zero(32n)), Word.zero(32n)),
    g2,
    Equal.trans(Word(32n),
      Word.or(32n, Word.and(32n, m6, Word.or(32n, A, B)), Word.and(32n, m6, C)),
      Word.or(32n, Word.or(32n, A, Word.zero(32n)), Word.and(32n, m6, C)),
      Word.or(32n, Word.or(32n, A, Word.zero(32n)), Word.zero(32n)),
      Equal.cong(Word(32n), Word(32n), v => Word.or(32n, v, Word.and(32n, m6, C)), Word.and(32n, m6, Word.or(32n, A, B)), Word.or(32n, A, Word.zero(32n)), h7),
      Equal.cong(Word(32n), Word(32n), v => Word.or(32n, Word.or(32n, A, Word.zero(32n)), v), Word.and(32n, m6, C), Word.zero(32n), k1)))
  Equal.trans(Word(32n),
    Word.and(32n, P, m6),
    Word.and(32n, m6, P),
    A,
    g1,
    Equal.trans(Word(32n),
      Word.and(32n, m6, P),
      Word.or(32n, Word.or(32n, A, Word.zero(32n)), Word.zero(32n)),
      A,
      g2b,
      or_zero_zero(A)))

def bit0_and_mask6(+n: Nat, w: Word(n)) -> {bit0(n, Word.and(n, w, Bits.mask(n, 6n))) == bit0(n, w) : Bool}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{+wh, wt}:
          Bits.b_and_true(wh)

def full_add_fst_xor(a: Bool, b: Bool) -> {fst_b(Bool.full_add(a, b, False{})) == Bool.xor(a, b) : Bool}:
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

def lsb_add(n: Nat, a: Word(n), b: Word(n)) -> {bit0(n, Word.add(n, a, b)) == Bool.xor(bit0(n, a), bit0(n, b)) : Bool}:
  match n:
    case 0n:
      match a b: case WNil{} WNil{}: {==}
    case 1n+p:
      match a b:
        case WCon{+ah, at} WCon{+bh, bt}:
          Equal.trans(Bool,
            bit0(1n+p, Word.add(1n+p, WCon{ah, at}, WCon{bh, bt})),
            fst_b(Bool.full_add(ah, bh, False{})),
            Bool.xor(ah, bh),
            adc_con_head(p, at, bt, False{}, Bool.full_add(ah, bh, False{})),
            full_add_fst_xor(ah, bh))

def par32_add(a: U32, b: U32) -> {par32(U32.add(a, b)) == Bool.xor(par32(a), par32(b)) : Bool}:
  match a:
    case U32{x}:
      match b:
        case U32{y}:
          lsb_add(32n, x, y)

def par32_mask6(w: U32) -> {par32(U32.and(w, 63)) == par32(w) : Bool}:
  match w:
    case U32{x}:
      bit0_and_mask6(32n, x)

def and63_absorb(+v: U32) -> {U32.and(U32.and(v, 63), 63) == U32.and(v, 63) : U32}:
  match v:
    case U32{x}:
      Equal.cong(Word(32n), U32, t => U32{t},
        Word.and(32n, Word.and(32n, x, Bits.mask(32n, 6n)), Bits.mask(32n, 6n)),
        Word.and(32n, x, Bits.mask(32n, 6n)),
        Bits.w_and_absorb(32n, x, Bits.mask(32n, 6n)))

def u32_index_ix(+x: U32, +y: U32, +z: U32) -> {U32.and(Grid.index(x, y, z), 63) == U32.and(x, 63) : U32}:
  match x:
    case U32{wx}:
      match y:
        case U32{wy}:
          match z:
            case U32{wz}:
              Equal.cong(Word(32n), U32, t => U32{t},
                Word.and(32n,
                  Word.or(32n,
                    Word.or(32n,
                      Word.and(32n, wx, Bits.mask(32n, 6n)),
                      Bits.shl_n(32n, Word.and(32n, wz, Bits.mask(32n, 6n)), 6n)),
                    Bits.shl_n(32n, Word.and(32n, wy, Bits.mask(32n, 6n)), 12n)),
                  Bits.mask(32n, 6n)),
                Word.and(32n, wx, Bits.mask(32n, 6n)),
                low6_pack(wx, wy, wz))

def u32_ix_neighbor(+i: U32, +dx: U32, +dy: U32, +dz: U32) -> {Grid.ix(Grid.neighbor(i, dx, dy, dz)) == U32.and(U32.add(Grid.ix(i), dx), 63) : U32}:
  +x = U32.and(U32.add(Grid.ix(i), dx), 63)
  +y = U32.and(U32.add(Grid.iy(i), dy), 63)
  +z = U32.and(U32.add(Grid.iz(i), dz), 63)
  +e1 = u32_index_ix(x, y, z)
  +e2 = and63_absorb(U32.add(Grid.ix(i), dx))
  Equal.trans(U32,
    U32.and(Grid.index(x, y, z), 63),
    U32.and(x, 63),
    U32.and(U32.add(Grid.ix(i), dx), 63),
    e1, e2)

def neighbor_x_par(+i: U32, +dx: U32) -> {par32(Grid.ix(Grid.neighbor(i, dx, 0, 0))) == Bool.xor(par32(Grid.ix(i)), par32(dx)) : Bool}:
  +ixn = Grid.ix(Grid.neighbor(i, dx, 0, 0))
  +addv = U32.add(Grid.ix(i), dx)
  +e1 = u32_ix_neighbor(i, dx, 0, 0)
  +e2 = par32_mask6(addv)
  +e3 = par32_add(Grid.ix(i), dx)
  Equal.trans(Bool,
    par32(ixn),
    par32(U32.and(addv, 63)),
    Bool.xor(par32(Grid.ix(i)), par32(dx)),
    Equal.cong(U32, Bool, v => par32(v), ixn, U32.and(addv, 63), e1),
    Equal.trans(Bool,
      par32(U32.and(addv, 63)),
      par32(addv),
      Bool.xor(par32(Grid.ix(i)), par32(dx)),
      e2, e3))

def shr6_and_m6_zero(+u: Word(32n)) -> {Bits.shr_n(32n, 6n, Word.and(32n, u, Bits.mask(32n, 6n))) == Word.zero(32n) : Word(32n)}:
  +a = Bits.shr_n(32n, 6n, u)
  +mid = Word.and(32n, a, Bits.shr_n(32n, 6n, Bits.mask(32n, 6n)))
  Equal.trans(Word(32n),
    Bits.shr_n(32n, 6n, Word.and(32n, u, Bits.mask(32n, 6n))),
    mid,
    Word.zero(32n),
    Bits.shr_n_and(32n, 6n, u, Bits.mask(32n, 6n)),
    Equal.trans(Word(32n),
      mid,
      Word.and(32n, a, Word.zero(32n)),
      Word.zero(32n),
      Equal.cong(Word(32n), Word(32n), v => Word.and(32n, a, v),
        Bits.shr_n(32n, 6n, Bits.mask(32n, 6n)), Word.zero(32n), shr6_m6()),
      Bits.w_and_zero(32n, a)))

def shr12_and_m6_zero(+u: Word(32n)) -> {Bits.shr_n(32n, 12n, Word.and(32n, u, Bits.mask(32n, 6n))) == Word.zero(32n) : Word(32n)}:
  +a = Bits.shr_n(32n, 12n, u)
  +mid = Word.and(32n, a, Bits.shr_n(32n, 12n, Bits.mask(32n, 6n)))
  Equal.trans(Word(32n),
    Bits.shr_n(32n, 12n, Word.and(32n, u, Bits.mask(32n, 6n))),
    mid,
    Word.zero(32n),
    Bits.shr_n_and(32n, 12n, u, Bits.mask(32n, 6n)),
    Equal.trans(Word(32n),
      mid,
      Word.and(32n, a, Word.zero(32n)),
      Word.zero(32n),
      Equal.cong(Word(32n), Word(32n), v => Word.and(32n, a, v),
        Bits.shr_n(32n, 12n, Bits.mask(32n, 6n)), Word.zero(32n), shr12_m6()),
      Bits.w_and_zero(32n, a)))

def m6() -> Word(32n):
  Bits.mask(32n, 6n)

def kmask(k: Nat) -> Word(32n):
  match k:
    case 0n:
      Bits.mask(32n, 32n)
    case 1n+q:
      Word.shr(32n, kmask(q))

def mask31_eq_kmask1() -> {Bits.mask(32n, 31n) == kmask(1n) : Word(32n)}:
  {==}

def shr_kmask(+k: Nat, +j: Nat) -> {Bits.shr_n(32n, k, kmask(j)) == kmask(Nat.add(j, k)) : Word(32n)}:
  match k:
    case 0n:
      Equal.cong(Nat, Word(32n), x => kmask(x), j, Nat.add(j, 0n),
        Equal.sym(Nat, Nat.add(j, 0n), j, NatL.n_add_zero_right(j)))
    case 1n+q:
      match j:
        case 0n:
          +ih = shr_kmask(q, 1n)
          Equal.trans(Word(32n),
            Bits.shr_n(32n, 1n+q, kmask(0n)),
            Bits.shr_n(32n, q, kmask(1n)),
            kmask(Nat.add(0n, 1n+q)),
            Equal.cong(Word(32n), Word(32n), x => Bits.shr_n(32n, q, x),
              Word.shr(32n, kmask(0n)), kmask(1n), mask31_eq_kmask1()),
            ih)
        case 1n+i:
          +ih = shr_kmask(q, 2n+i)
          +arg = NatL.n_add_succ_right(1n+i, q)
          +c = kmask(Nat.add(1n+i, 1n+q))
          +p1 = Equal.cong(Word(32n), Word(32n), x => Bits.shr_n(32n, q, x),
            Word.shr(32n, kmask(1n+i)), kmask(2n+i), {==})
          +p2 = Equal.trans(Word(32n),
            Bits.shr_n(32n, q, kmask(2n+i)),
            kmask(Nat.add(2n+i, q)),
            c,
            ih,
            Equal.cong(Nat, Word(32n), x => kmask(x),
              Nat.add(2n+i, q), Nat.add(1n+i, 1n+q),
              Equal.sym(Nat, Nat.add(1n+i, 1n+q), Nat.add(2n+i, q), arg)))
          Equal.trans(Word(32n),
            Bits.shr_n(32n, 1n+q, kmask(1n+i)),
            Bits.shr_n(32n, q, kmask(2n+i)),
            c, p1, p2)

def shr_kmask1(+k: Nat) -> {Bits.shr_n(32n, k, Bits.mask(32n, 31n)) == kmask(1n+k) : Word(32n)}:
  Equal.trans(Word(32n),
    Bits.shr_n(32n, k, Bits.mask(32n, 31n)),
    Bits.shr_n(32n, k, kmask(1n)),
    kmask(1n+k),
    Equal.cong(Word(32n), Word(32n), x => Bits.shr_n(32n, k, x), Bits.mask(32n, 31n), kmask(1n), mask31_eq_kmask1()),
    shr_kmask(k, 1n))

def kmask_nest(k: Nat) -> {Word.and(32n, kmask(k), kmask(1n+k)) == kmask(1n+k) : Word(32n)}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      +qq = q
      Equal.trans(Word(32n),
        Word.and(32n, kmask(1n+qq), kmask(1n+(1n+qq))),
        Word.shr(32n, Word.and(32n, kmask(qq), kmask(1n+qq))),
        kmask(1n+(1n+qq)),
        Equal.sym(Word(32n), Word.shr(32n, Word.and(32n, kmask(qq), kmask(1n+qq))),
          Word.and(32n, kmask(1n+qq), kmask(1n+(1n+qq))), Bits.shr_and(32n, kmask(qq), kmask(1n+qq))),
        Equal.cong(Word(32n), Word(32n), x => Word.shr(32n, x),
          Word.and(32n, kmask(qq), kmask(1n+qq)), kmask(1n+qq), kmask_nest(qq)))

def shr_shl_kmask(+k: Nat, +X: Word(32n)) -> {Bits.shr_n(32n, k, Bits.shl_n(32n, X, k)) == Word.and(32n, X, kmask(k)) : Word(32n)}:
  match k:
    case 0n:
      Equal.sym(Word(32n), Word.and(32n, X, kmask(0n)), X, Bits.and_ones(32n, X))
    case 1n+q:
      +ih = shr_shl_kmask(q, X)
      +p1 = Bits.shr_n_and(32n, q, Bits.shl_n(32n, X, q), Bits.mask(32n, 31n))
      +sm = shr_kmask1(q)
      +e1 = Equal.cong(Word(32n), Word(32n), v => Word.and(32n, v, Bits.shr_n(32n, q, Bits.mask(32n, 31n))),
        Bits.shr_n(32n, q, Bits.shl_n(32n, X, q)), Word.and(32n, X, kmask(q)), ih)
      +e2 = Equal.cong(Word(32n), Word(32n), v => Word.and(32n, Word.and(32n, X, kmask(q)), v),
        Bits.shr_n(32n, q, Bits.mask(32n, 31n)), kmask(1n+q), sm)
      +mid = Word.and(32n, Word.and(32n, X, kmask(q)), Bits.shr_n(32n, q, Bits.mask(32n, 31n)))
      +p2 = Equal.trans(Word(32n),
        Word.and(32n, Bits.shr_n(32n, q, Bits.shl_n(32n, X, q)), Bits.shr_n(32n, q, Bits.mask(32n, 31n))),
        mid,
        Word.and(32n, Word.and(32n, X, kmask(q)), kmask(1n+q)),
        e1, e2)
      +p3 = Equal.trans(Word(32n),
        Word.and(32n, Word.and(32n, X, kmask(q)), kmask(1n+q)),
        Word.and(32n, X, Word.and(32n, kmask(q), kmask(1n+q))),
        Word.and(32n, X, kmask(1n+q)),
        Bits.w_and_assoc(32n, X, kmask(q), kmask(1n+q)),
        Equal.cong(Word(32n), Word(32n), v => Word.and(32n, X, v),
          Word.and(32n, kmask(q), kmask(1n+q)), kmask(1n+q), kmask_nest(q)))
      +a3 = Bits.shr_n(32n, q, Word.and(32n, Bits.shl_n(32n, X, q), Bits.mask(32n, 31n)))
      +b = Word.and(32n, Bits.shr_n(32n, q, Bits.shl_n(32n, X, q)), Bits.shr_n(32n, q, Bits.mask(32n, 31n)))
      +p0 = Equal.cong(Word(32n), Word(32n), x => Bits.shr_n(32n, q, x),
        Word.shr(32n, Word.shl(32n, Bits.shl_n(32n, X, q))),
        Word.and(32n, Bits.shl_n(32n, X, q), Bits.mask(32n, 31n)),
        Bits.shr_shl_one(31n, Bits.shl_n(32n, X, q)))
      Equal.trans(Word(32n),
        Bits.shr_n(32n, 1n+q, Bits.shl_n(32n, X, 1n+q)),
        a3,
        Word.and(32n, X, kmask(1n+q)),
        p0,
        Equal.trans(Word(32n),
          a3,
          b,
          Word.and(32n, X, kmask(1n+q)),
          p1,
          Equal.trans(Word(32n),
            b,
            Word.and(32n, Word.and(32n, X, kmask(q)), kmask(1n+q)),
            Word.and(32n, X, kmask(1n+q)),
            p2, p3)))

def kmask6_eq() -> {kmask(6n) == Bits.mask(32n, 26n) : Word(32n)}:
  {==}

def kmask12_eq() -> {kmask(12n) == Bits.mask(32n, 20n) : Word(32n)}:
  {==}

def m6_kmask6() -> {Word.and(32n, m6(), kmask(6n)) == m6() : Word(32n)}:
  {==}

def m6_kmask12() -> {Word.and(32n, m6(), kmask(12n)) == m6() : Word(32n)}:
  {==}

def and_m6_kmask6(+u: Word(32n)) -> {Word.and(32n, Word.and(32n, u, m6()), kmask(6n)) == Word.and(32n, u, m6()) : Word(32n)}:
  Equal.trans(Word(32n),
    Word.and(32n, Word.and(32n, u, m6()), kmask(6n)),
    Word.and(32n, u, Word.and(32n, m6(), kmask(6n))),
    Word.and(32n, u, m6()),
    Bits.w_and_assoc(32n, u, m6(), kmask(6n)),
    Equal.cong(Word(32n), Word(32n), v => Word.and(32n, u, v),
      Word.and(32n, m6(), kmask(6n)), m6(), m6_kmask6()))

def and_m6_kmask12(+u: Word(32n)) -> {Word.and(32n, Word.and(32n, u, m6()), kmask(12n)) == Word.and(32n, u, m6()) : Word(32n)}:
  Equal.trans(Word(32n),
    Word.and(32n, Word.and(32n, u, m6()), kmask(12n)),
    Word.and(32n, u, Word.and(32n, m6(), kmask(12n))),
    Word.and(32n, u, m6()),
    Bits.w_and_assoc(32n, u, m6(), kmask(12n)),
    Equal.cong(Word(32n), Word(32n), v => Word.and(32n, u, v),
      Word.and(32n, m6(), kmask(12n)), m6(), m6_kmask12()))

def shr_shl66(+u: Word(32n)) -> {Bits.shr_n(32n, 6n, Bits.shl_n(32n, Word.and(32n, u, m6()), 6n)) == Word.and(32n, u, m6()) : Word(32n)}:
  Equal.trans(Word(32n),
    Bits.shr_n(32n, 6n, Bits.shl_n(32n, Word.and(32n, u, m6()), 6n)),
    Word.and(32n, Word.and(32n, u, m6()), kmask(6n)),
    Word.and(32n, u, m6()),
    shr_shl_kmask(6n, Word.and(32n, u, m6())),
    and_m6_kmask6(u))

def shr_shl1212(+u: Word(32n)) -> {Bits.shr_n(32n, 12n, Bits.shl_n(32n, Word.and(32n, u, m6()), 12n)) == Word.and(32n, u, m6()) : Word(32n)}:
  Equal.trans(Word(32n),
    Bits.shr_n(32n, 12n, Bits.shl_n(32n, Word.and(32n, u, m6()), 12n)),
    Word.and(32n, Word.and(32n, u, m6()), kmask(12n)),
    Word.and(32n, u, m6()),
    shr_shl_kmask(12n, Word.and(32n, u, m6())),
    and_m6_kmask12(u))
