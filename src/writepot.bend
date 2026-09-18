import Base
import ./cell.bend as Cell
import ./bits.bend as Bits
import ./ops.bend as Ops
import ./rules.bend as Rules
import ./settle.bend as S
import ./grid.bend as Grid
import ./potential.bend as Pot

def enc_w(
  mw: Word(32n), cw: Word(32n), aw: Word(32n), sw: Word(32n), fw: Word(32n)
) -> Word(32n):
  Word.or(32n,
    Word.or(32n,
      Word.or(32n,
        Word.or(32n,
          Word.and(32n, mw, Bits.mask(32n, 5n)),
          Bits.shl_n(32n, Word.and(32n, cw, Bits.mask(32n, 6n)), 5n)),
        Bits.shl_n(32n, Word.and(32n, aw, Bits.mask(32n, 1n)), 11n)),
      Bits.shl_n(32n, Word.and(32n, sw, Bits.mask(32n, 5n)), 12n)),
    Bits.shl_n(32n, Word.and(32n, fw, Bits.mask(32n, 6n)), 17n))

def w_and_zero_l(+n: Nat, +a: Word(n))
  -> {Word.and(n, Word.zero(n), a) == Word.zero(n) : Word(n)}:
  Equal.trans(Word(n),
    Word.and(n, Word.zero(n), a),
    Word.and(n, a, Word.zero(n)),
    Word.zero(n),
    Bits.w_and_comm(n, Word.zero(n), a),
    Bits.w_and_zero(n, a))

def shl_zero() -> {Word.shl(32n, Word.zero(32n)) == Word.zero(32n) : Word(32n)}:
  {==}

def shl_n_zero(k: Nat)
  -> {Bits.shl_n(32n, Word.zero(32n), k) == Word.zero(32n) : Word(32n)}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.trans(Word(32n),
        Bits.shl_n(32n, Word.zero(32n), 1n + p),
        Word.zero(32n),
        Word.zero(32n),
        Equal.trans(Word(32n),
          Bits.shl_n(32n, Word.zero(32n), 1n + p),
          Word.shl(32n, Bits.shl_n(32n, Word.zero(32n), p)),
          Word.zero(32n),
          {==},
          Equal.trans(Word(32n),
            Word.shl(32n, Bits.shl_n(32n, Word.zero(32n), p)),
            Word.shl(32n, Word.zero(32n)),
            Word.zero(32n),
            Equal.cong(Word(32n), Word(32n), x => Word.shl(32n, x),
              Bits.shl_n(32n, Word.zero(32n), p), Word.zero(32n), shl_n_zero(p)),
            shl_zero())),
        {==})

def shr5() -> {Bits.shr_n(32n, 5n, Bits.mask(32n, 5n)) == Word.zero(32n) : Word(32n)}:
  {==}

def shr11() -> {Bits.shr_n(32n, 11n, Bits.mask(32n, 5n)) == Word.zero(32n) : Word(32n)}:
  {==}

def shr12() -> {Bits.shr_n(32n, 12n, Bits.mask(32n, 5n)) == Word.zero(32n) : Word(32n)}:
  {==}

def shr17() -> {Bits.shr_n(32n, 17n, Bits.mask(32n, 5n)) == Word.zero(32n) : Word(32n)}:
  {==}

# h : shr_n(32, k, mask5) == zero, so and(mask5, shl_n(X,k)) == zero.
def shift5(+k: Nat, h: {Bits.shr_n(32n, k, Bits.mask(32n, 5n)) == Word.zero(32n) : Word(32n)}, +X: Word(32n))
  -> {Word.and(32n, Bits.mask(32n, 5n), Bits.shl_n(32n, X, k)) == Word.zero(32n) : Word(32n)}:
  Equal.trans(Word(32n),
    Word.and(32n, Bits.mask(32n, 5n), Bits.shl_n(32n, X, k)),
    Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, k, Bits.mask(32n, 5n)), X), k),
    Word.zero(32n),
    Bits.and_shl_n(32n, k, Bits.mask(32n, 5n), X),
    Equal.trans(Word(32n),
      Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, k, Bits.mask(32n, 5n)), X), k),
      Bits.shl_n(32n, Word.and(32n, Word.zero(32n), X), k),
      Word.zero(32n),
      Equal.cong(Word(32n), Word(32n), y => Bits.shl_n(32n, y, k),
        Word.and(32n, Bits.shr_n(32n, k, Bits.mask(32n, 5n)), X),
        Word.and(32n, Word.zero(32n), X),
        Equal.cong(Word(32n), Word(32n), z => Word.and(32n, z, X),
          Bits.shr_n(32n, k, Bits.mask(32n, 5n)), Word.zero(32n), h)),
      Equal.trans(Word(32n),
        Bits.shl_n(32n, Word.and(32n, Word.zero(32n), X), k),
        Bits.shl_n(32n, Word.zero(32n), k),
        Word.zero(32n),
        Equal.cong(Word(32n), Word(32n), y => Bits.shl_n(32n, y, k),
          Word.and(32n, Word.zero(32n), X), Word.zero(32n), w_and_zero_l(32n, X)),
        shl_n_zero(k))))

# and(mask5, or(A, shl_n(X,k))) == and(A, mask5), given the shift clears mask5.
def peel(+A: Word(32n), +X: Word(32n), +k: Nat, h: {Bits.shr_n(32n, k, Bits.mask(32n, 5n)) == Word.zero(32n) : Word(32n)})
  -> {Word.and(32n, Bits.mask(32n, 5n), Word.or(32n, A, Bits.shl_n(32n, X, k))) == Word.and(32n, Bits.mask(32n, 5n), A) : Word(32n)}:
  Equal.trans(Word(32n),
    Word.and(32n, Bits.mask(32n, 5n), Word.or(32n, A, Bits.shl_n(32n, X, k))),
    Word.or(32n, Word.and(32n, Bits.mask(32n, 5n), A), Word.zero(32n)),
    Word.and(32n, Bits.mask(32n, 5n), A),
    Equal.trans(Word(32n),
      Word.and(32n, Bits.mask(32n, 5n), Word.or(32n, A, Bits.shl_n(32n, X, k))),
      Word.or(32n, Word.and(32n, Bits.mask(32n, 5n), A), Word.and(32n, Bits.mask(32n, 5n), Bits.shl_n(32n, X, k))),
      Word.or(32n, Word.and(32n, Bits.mask(32n, 5n), A), Word.zero(32n)),
      Bits.w_and_or(32n, Bits.mask(32n, 5n), A, Bits.shl_n(32n, X, k)),
      Equal.cong(Word(32n), Word(32n), y => Word.or(32n, Word.and(32n, Bits.mask(32n, 5n), A), y),
        Word.and(32n, Bits.mask(32n, 5n), Bits.shl_n(32n, X, k)), Word.zero(32n), shift5(k, h, X))),
    Equal.trans(Word(32n),
      Word.or(32n, Word.and(32n, Bits.mask(32n, 5n), A), Word.zero(32n)),
      Word.and(32n, Bits.mask(32n, 5n), A),
      Word.and(32n, Bits.mask(32n, 5n), A),
      Bits.w_or_zero(32n, Word.and(32n, Bits.mask(32n, 5n), A)),
      {==}))

def absorb_mat(+mw: Word(32n))
  -> {Word.and(32n, Bits.mask(32n, 5n), Word.and(32n, mw, Bits.mask(32n, 5n))) == Word.and(32n, mw, Bits.mask(32n, 5n)) : Word(32n)}:
  Equal.trans(Word(32n),
    Word.and(32n, Bits.mask(32n, 5n), Word.and(32n, mw, Bits.mask(32n, 5n))),
    Word.and(32n, Word.and(32n, mw, Bits.mask(32n, 5n)), Bits.mask(32n, 5n)),
    Word.and(32n, mw, Bits.mask(32n, 5n)),
    Bits.w_and_comm(32n, Bits.mask(32n, 5n), Word.and(32n, mw, Bits.mask(32n, 5n))),
    Bits.w_and_absorb(32n, mw, Bits.mask(32n, 5n)))

def mat_enc_w(+mw: Word(32n), +cw: Word(32n), +aw: Word(32n), +sw: Word(32n), +fw: Word(32n))
  -> {Word.and(32n, enc_w(mw, cw, aw, sw, fw), Bits.mask(32n, 5n)) == Word.and(32n, mw, Bits.mask(32n, 5n)) : Word(32n)}:
  +M5 = Bits.mask(32n, 5n)
  +T1 = Word.and(32n, mw, M5)
  +S2 = Bits.shl_n(32n, Word.and(32n, cw, Bits.mask(32n, 6n)), 5n)
  +S3 = Bits.shl_n(32n, Word.and(32n, aw, Bits.mask(32n, 1n)), 11n)
  +S4 = Bits.shl_n(32n, Word.and(32n, sw, M5), 12n)
  +S5 = Bits.shl_n(32n, Word.and(32n, fw, Bits.mask(32n, 6n)), 17n)
  +P4 = Word.or(32n, Word.or(32n, Word.or(32n, T1, S2), S3), S4)
  +P3 = Word.or(32n, Word.or(32n, T1, S2), S3)
  +P2 = Word.or(32n, T1, S2)
  +X2 = Word.and(32n, cw, Bits.mask(32n, 6n))
  +X3 = Word.and(32n, aw, Bits.mask(32n, 1n))
  +X4 = Word.and(32n, sw, M5)
  +X5 = Word.and(32n, fw, Bits.mask(32n, 6n))
  +e0 = Bits.w_and_comm(32n, enc_w(mw, cw, aw, sw, fw), M5)
  +p5 = peel(P4, X5, 17n, shr17())
  +p4 = peel(P3, X4, 12n, shr12())
  +p3 = peel(P2, X3, 11n, shr11())
  +p2 = peel(T1, X2, 5n, shr5())
  Equal.trans(Word(32n),
    Word.and(32n, enc_w(mw, cw, aw, sw, fw), M5),
    Word.and(32n, M5, P4),
    Word.and(32n, mw, M5),
    Equal.trans(Word(32n),
      Word.and(32n, enc_w(mw, cw, aw, sw, fw), M5),
      Word.and(32n, M5, Word.or(32n, P4, S5)),
      Word.and(32n, M5, P4),
      e0, p5),
    Equal.trans(Word(32n),
      Word.and(32n, M5, P4),
      Word.and(32n, M5, P2),
      Word.and(32n, mw, M5),
      Equal.trans(Word(32n),
        Word.and(32n, M5, P4),
        Word.and(32n, M5, P3),
        Word.and(32n, M5, P2),
        p4, p3),
      Equal.trans(Word(32n),
        Word.and(32n, M5, P2),
        Word.and(32n, M5, T1),
        Word.and(32n, mw, M5),
        p2,
        absorb_mat(mw))))

def and31_absorb(+w: U32) -> {U32.and(U32.and(w, 31), 31) == U32.and(w, 31) : U32}:
  match w:
    case U32{x}:
      Equal.cong(Word(32n), U32, y => U32{y},
        Word.and(32n, Word.and(32n, x, Bits.mask(32n, 5n)), Bits.mask(32n, 5n)),
        Word.and(32n, x, Bits.mask(32n, 5n)),
        Bits.w_and_absorb(32n, x, Bits.mask(32n, 5n)))

# The material field of any Cell.encode is the material argument (5 bits).
def mat_encode(m: U32, c: U32, a: U32, s: U32, f: U32)
  -> {Cell.material(Cell.encode(m, c, a, s, f)) == U32.and(m, 31) : U32}:
  match m c a s f:
    case U32{mw} U32{cw} U32{aw} U32{sw} U32{fw}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Word.and(32n, enc_w(mw, cw, aw, sw, fw), Bits.mask(32n, 5n)),
        Word.and(32n, mw, Bits.mask(32n, 5n)),
        mat_enc_w(mw, cw, aw, sw, fw))

def pot_set_support(+w: U32, +s: U32, +i: U32)
  -> {S.pot_at(Ops.set_support(w, s), i) == S.pot_at(w, i) : Nat}:
  Equal.cong(U32, Nat, m => Nat.mul(Pot.dens(m), U32.to_nat(Grid.iy(i))),
    Cell.material(Ops.set_support(w, s)), Cell.material(w),
    Equal.trans(U32,
      Cell.material(Ops.set_support(w, s)),
      U32.and(Cell.material(w), 31),
      Cell.material(w),
      mat_encode(Cell.material(w), Cell.cohesion(w), Cell.active(w), s, Cell.fall(w)),
      and31_absorb(w)))

def pot_set_fall0(+w: U32, +i: U32)
  -> {S.pot_at(Ops.set_fall0(w), i) == S.pot_at(w, i) : Nat}:
  Equal.cong(U32, Nat, m => Nat.mul(Pot.dens(m), U32.to_nat(Grid.iy(i))),
    Cell.material(Ops.set_fall0(w)), Cell.material(w),
    Equal.trans(U32,
      Cell.material(Ops.set_fall0(w)),
      U32.and(Cell.material(w), 31),
      Cell.material(w),
      mat_encode(Cell.material(w), Cell.cohesion(w), 0, Cell.support(w), 0),
      and31_absorb(w)))

def pot_mov(+w: U32, +i: U32)
  -> {S.pot_at(Rules.mov(w), i) == S.pot_at(w, i) : Nat}:
  +nf = U32.min(U32.add(Cell.fall(w), 1), 63)
  Equal.cong(U32, Nat, m => Nat.mul(Pot.dens(m), U32.to_nat(Grid.iy(i))),
    Cell.material(Rules.mov(w)), Cell.material(w),
    Equal.trans(U32,
      Cell.material(Rules.mov(w)),
      U32.and(Cell.material(w), 31),
      Cell.material(w),
      mat_encode(Cell.material(w), Cell.cohesion(w), Cell.active(w), Cell.support(w), nf),
      and31_absorb(w)))

def pot_crush_rock(+w: U32, +i: U32, +h: {Cell.material(w) == 3 : U32})
  -> {Nat.add(S.pot_at(Ops.crush_word(w), i), Nat.mul(50n, U32.to_nat(Grid.iy(i)))) == S.pot_at(w, i) : Nat}:
  +L = U32.to_nat(Grid.iy(i))
  +e1 = mat_encode(Ops.crush_material(Cell.material(w)), 0, 0, 0, 0)
  +e2 = Equal.cong(U32, U32, m => U32.and(Ops.crush_material(m), 31), Cell.material(w), 3, h)
  +e3 = Equal.trans(U32,
    Cell.material(Ops.crush_word(w)),
    U32.and(Ops.crush_material(Cell.material(w)), 31),
    4,
    e1,
    Equal.trans(U32,
      U32.and(Ops.crush_material(Cell.material(w)), 31),
      U32.and(Ops.crush_material(3), 31),
      4,
      e2,
      {==}))
  +d1 = Equal.trans(Nat,
    Pot.dens(Cell.material(Ops.crush_word(w))),
    Pot.dens(4),
    150n,
    Equal.cong(U32, Nat, m => Pot.dens(m), Cell.material(Ops.crush_word(w)), 4, e3),
    Pot.dens_rubble())
  +d2 = Equal.trans(Nat,
    Pot.dens(Cell.material(w)),
    Pot.dens(3),
    200n,
    Equal.cong(U32, Nat, m => Pot.dens(m), Cell.material(w), 3, h),
    Pot.dens_rock())
  Equal.trans(Nat,
    Nat.add(Nat.mul(Pot.dens(Cell.material(Ops.crush_word(w))), L), Nat.mul(50n, L)),
    Nat.add(Nat.mul(150n, L), Nat.mul(50n, L)),
    Nat.mul(Pot.dens(Cell.material(w)), L),
    Equal.cong(Nat, Nat, x => Nat.add(Nat.mul(x, L), Nat.mul(50n, L)),
      Pot.dens(Cell.material(Ops.crush_word(w))), 150n, d1),
    Equal.trans(Nat,
      Nat.add(Nat.mul(150n, L), Nat.mul(50n, L)),
      Nat.mul(200n, L),
      Nat.mul(Pot.dens(Cell.material(w)), L),
      Pot.crumble_decreases(150n, 50n, L),
      Equal.sym(Nat, Nat.mul(Pot.dens(Cell.material(w)), L), Nat.mul(200n, L),
        Equal.cong(Nat, Nat, x => Nat.mul(x, L), Pot.dens(Cell.material(w)), 200n, d2))))

# A whole-world point write that replaces a pot (v + g) by v lowers Phi by g.
# This is the "composition of replace_decreases" building block: the list-level
# theorem in V2b-i (`list_set_sum`) instantiated at an arbitrary segment split.
def point_write_lowers(+l: +List<Nat>, +v: Nat, +g: Nat, +r: +List<Nat>)
  -> {Nat.add(S.suml(S.app(l, S.app([v], r))), g) == S.suml(S.app(l, S.app([v + g], r))) : Nat}:
  +h = Equal.trans(Nat,
    Nat.add(S.suml([v]), g),
    Nat.add(v, g),
    S.suml([v + g]),
    Equal.cong(Nat, Nat, x => Nat.add(x, g), S.suml([v]), v, S.suml1(v)),
    Equal.sym(Nat, S.suml([v + g]), Nat.add(v, g), S.suml1(Nat.add(v, g))))
  S.replace_decreases(l, r, [v + g], [v], g, h)

# Active-bit writes: set (wake) and clear (deactivate) touch bit 11 only.
# 2048 == shln(1, 11) and ~2048 == not(2048) are definitional.

def mat_or_hi(+w: U32) -> {Cell.material(U32.or(w, U32.shln(1, 11n))) == Cell.material(w) : U32}:
  match w:
    case U32{+x}:
      +M5 = Bits.mask(32n, 5n)
      +K = Bits.shl_n(32n, Bits.mask(32n, 1n), 11n)
      +e1 = Bits.w_and_comm(32n, Word.or(32n, x, K), M5)
      +e2 = Bits.w_and_or(32n, M5, x, K)
      +e3 = shift5(11n, shr11(), Bits.mask(32n, 1n))
      +e4 = Bits.w_or_zero(32n, Word.and(32n, M5, x))
      +e5 = Bits.w_and_comm(32n, M5, x)
      Equal.cong(Word(32n), U32, z => U32{z},
        Word.and(32n, Word.or(32n, x, K), M5),
        Word.and(32n, x, M5),
        Equal.trans(Word(32n),
          Word.and(32n, Word.or(32n, x, K), M5),
          Word.or(32n, Word.and(32n, M5, x), Word.zero(32n)),
          Word.and(32n, x, M5),
          Equal.trans(Word(32n),
            Word.and(32n, Word.or(32n, x, K), M5),
            Word.and(32n, M5, Word.or(32n, x, K)),
            Word.or(32n, Word.and(32n, M5, x), Word.zero(32n)),
            e1,
            Equal.trans(Word(32n),
              Word.and(32n, M5, Word.or(32n, x, K)),
              Word.or(32n, Word.and(32n, M5, x), Word.and(32n, M5, K)),
              Word.or(32n, Word.and(32n, M5, x), Word.zero(32n)),
              e2,
              Equal.cong(Word(32n), Word(32n), y => Word.or(32n, Word.and(32n, M5, x), y),
                Word.and(32n, M5, K), Word.zero(32n), e3))),
          Equal.trans(Word(32n),
            Word.or(32n, Word.and(32n, M5, x), Word.zero(32n)),
            Word.and(32n, M5, x),
            Word.and(32n, x, M5),
            e4, e5)))

def mat_and_hi(+w: U32) -> {Cell.material(U32.and(w, U32.not(U32.shln(1, 11n)))) == Cell.material(w) : U32}:
  match w:
    case U32{+x}:
      +M5 = Bits.mask(32n, 5n)
      +NOTK = Word.not(32n, Bits.shl_n(32n, Bits.mask(32n, 1n), 11n))
      Equal.cong(Word(32n), U32, z => U32{z},
        Word.and(32n, Word.and(32n, x, NOTK), M5),
        Word.and(32n, x, M5),
        Equal.trans(Word(32n),
          Word.and(32n, Word.and(32n, x, NOTK), M5),
          Word.and(32n, x, Word.and(32n, NOTK, M5)),
          Word.and(32n, x, M5),
          Bits.w_and_assoc(32n, x, NOTK, M5),
          Equal.cong(Word(32n), Word(32n), y => Word.and(32n, x, y), Word.and(32n, NOTK, M5), M5, {==})))

def pot_or_hi(+w: U32, +i: U32) -> {S.pot_at(U32.or(w, 2048), i) == S.pot_at(w, i) : Nat}:
  Equal.cong(U32, Nat, m => Nat.mul(Pot.dens(m), U32.to_nat(Grid.iy(i))),
    Cell.material(U32.or(w, 2048)), Cell.material(w), mat_or_hi(w))

def pot_and_hi(+w: U32, +i: U32) -> {S.pot_at(U32.and(w, 4294965247), i) == S.pot_at(w, i) : Nat}:
  Equal.cong(U32, Nat, m => Nat.mul(Pot.dens(m), U32.to_nat(Grid.iy(i))),
    Cell.material(U32.and(w, 4294965247)), Cell.material(w), mat_and_hi(w))
