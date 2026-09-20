import Base
import ./bits.bend as Bits
import ./cw.bend as Cw
import ./parity.bend as Parity

# ============================================================================
# gscale (P3 / G-scale-3) -- the bit-level proof of `cw`'s split/rejoin.
#
# `src/cw.bend` splits a global coordinate into a chunk key plus a local offset
# and rejoins it with no torus mask; T57-T60 witness it, but the identity was
# unproven (PLAN.md §5.3 `G-scale-3`). This module proves it in the `Bits`/`Word`
# model, analogous to `Bits.model_index_rt`:
#
#   * `gscale_global_rt`  : `(x >> 4) << 4 + (x & 15) == x & 16383`, the masked
#                           split/rejoin identity (the `cw_global_x/y/z` core);
#   * `gscale_key_x_ext` / `gscale_local_x_ext` : the field extraction the global
#                           identity needs (`cw_key_x` of a key is its `x` field);
#   * `gscale_kmodel_rt` / `gscale_lmodel_rt` : the key/local roundtrips, i.e.
#                           the 10-bit (resp. 4-bit) field reconstruction, again
#                           mirroring `Bits.model_index_rt`;
#   * `gscale_cw_{x,y,z,key,local}_split` : the composed `U32` statements that
#                           `LAWS.bend` states as laws.
#
# The two arithmetic bricks that make `add` honest are `gscale_add_and_or`
# (adding two disjoint masked fields is their `or`, so the carry never fires)
# and `gscale_and_shl_zero` (a left-shifted field misses the low mask).
# ============================================================================

def gscale_m10() -> Word(32n):
  Bits.mask(32n, 10n)

def gscale_m4() -> Word(32n):
  Bits.mask(32n, 4n)

def gscale_absurd(T: Type, X: T, Y: T, +h: {False{} == True{} : Bool}) -> {X == Y : T}:
  Equal.cong(Bool, T, x => Bool.pick(T, x, Y, X), False{}, True{}, h)

def gscale_whead(+p: Nat, +w: Word(1n+p)) -> Bool:
  match w:
    case WCon{h, t}: h

def gscale_wtail(+p: Nat, +w: Word(1n+p)) -> Word(p):
  match w:
    case WCon{h, t}: t

# `and (w && A) (w && B) = false` when `and A B = false`: the carry side
# condition of the `add = or` lemma below, pushed under the shared mask `w`.
def gscale_b_and_word(+w: Bool, +A: Bool, +B: Bool, +h: {Bool.and(A, B) == False{} : Bool})
  -> {Bool.and(Bool.and(w, A), Bool.and(w, B)) == False{} : Bool}:
  match A:
    case False{}:
      Equal.trans(Bool,
        Bool.and(Bool.and(w, False{}), Bool.and(w, B)),
        Bool.and(False{}, Bool.and(w, B)),
        False{},
        Equal.cong(Bool, Bool, x => Bool.and(x, Bool.and(w, B)), Bool.and(w, False{}), False{}, Bits.b_and_false(w)),
        {==})
    case True{}:
      match B:
        case False{}:
          Equal.trans(Bool,
            Bool.and(Bool.and(w, True{}), Bool.and(w, False{})),
            Bool.and(w, Bool.and(w, False{})),
            False{},
            Equal.cong(Bool, Bool, x => Bool.and(x, Bool.and(w, False{})), Bool.and(w, True{}), w, Bits.b_and_true(w)),
            Equal.trans(Bool,
              Bool.and(w, Bool.and(w, False{})),
              Bool.and(w, False{}),
              False{},
              Equal.cong(Bool, Bool, x => Bool.and(w, x), Bool.and(w, False{}), False{}, Bits.b_and_false(w)),
              Bits.b_and_false(w)))
        case True{}:
          gscale_absurd(Bool,
            Bool.and(Bool.and(w, True{}), Bool.and(w, True{})),
            False{},
            Equal.sym(Bool, True{}, False{}, h))

# With no carry in, `full_add a b false = (or a b, false)` whenever `a && b =
# false`. This is what turns `adc` into `or` at a bit where the two addends do
# not collide.
def gscale_full_add_and(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == False{} : Bool})
  -> {Bool.full_add(a, b, False{}) == (Bool.or(a, b), False{}) : Bool & Bool}:
  match a:
    case False{}:
      match b:
        case False{}: {==}
        case True{}: {==}
    case True{}:
      match b:
        case False{}: {==}
        case True{}:
          gscale_absurd(Bool & Bool,
            Bool.full_add(True{}, True{}, False{}),
            (Bool.or(True{}, True{}), False{}),
            Equal.sym(Bool, True{}, False{}, h))

# The field-addition brick: masked fields of the same word that are disjoint add
# as they or. Induction on the width; the head carries no carry because the two
# head bits cannot both be set.
def gscale_add_and_or(+n: Nat, +w: Word(n), +A: Word(n), +B: Word(n),
    +h: {Word.and(n, A, B) == Word.zero(n) : Word(n)})
  -> {Word.add(n, Word.and(n, w, A), Word.and(n, w, B)) == Word.and(n, w, Word.or(n, A, B)) : Word(n)}:
  match n:
    case 0n:
      match w A B:
        case WNil{} WNil{} WNil{}: {==}
    case 1n+p:
      match w A B:
        case WCon{wh, wt} WCon{Ah, At} WCon{Bh, Bt}:
          +hA = Equal.cong(Word(1n+p), Bool, W => gscale_whead(p, W),
            WCon{Bool.and(Ah, Bh), Word.and(p, At, Bt)},
            WCon{False{}, Word.zero(p)}, h)
          +hT = Equal.cong(Word(1n+p), Word(p), W => gscale_wtail(p, W),
            WCon{Bool.and(Ah, Bh), Word.and(p, At, Bt)},
            WCon{False{}, Word.zero(p)}, h)
          +hh = gscale_b_and_word(wh, Ah, Bh, hA)
          +fa = gscale_full_add_and(Bool.and(wh, Ah), Bool.and(wh, Bh), hh)
          +ih = gscale_add_and_or(p, wt, At, Bt, hT)
          +step1 = Equal.cong(Bool & Bool, Word(1n+p),
            pr => Word.adc.con(p, Word.and(p, wt, At), Word.and(p, wt, Bt), False{}, pr),
            Bool.full_add(Bool.and(wh, Ah), Bool.and(wh, Bh), False{}),
            (Bool.or(Bool.and(wh, Ah), Bool.and(wh, Bh)), False{}),
            fa)
          +step2 = Equal.trans(Word(1n+p),
            WCon{Bool.or(Bool.and(wh, Ah), Bool.and(wh, Bh)), Word.add(p, Word.and(p, wt, At), Word.and(p, wt, Bt))},
            WCon{Bool.or(Bool.and(wh, Ah), Bool.and(wh, Bh)), Word.and(p, wt, Word.or(p, At, Bt))},
            WCon{Bool.and(wh, Bool.or(Ah, Bh)), Word.and(p, wt, Word.or(p, At, Bt))},
            Equal.cong(Word(p), Word(1n+p),
              t => WCon{Bool.or(Bool.and(wh, Ah), Bool.and(wh, Bh)), t},
              Word.add(p, Word.and(p, wt, At), Word.and(p, wt, Bt)),
              Word.and(p, wt, Word.or(p, At, Bt)), ih),
            Equal.cong(Bool, Word(1n+p),
              x => WCon{x, Word.and(p, wt, Word.or(p, At, Bt))},
              Bool.or(Bool.and(wh, Ah), Bool.and(wh, Bh)),
              Bool.and(wh, Bool.or(Ah, Bh)),
              Equal.sym(Bool, Bool.and(wh, Bool.or(Ah, Bh)), Bool.or(Bool.and(wh, Ah), Bool.and(wh, Bh)), Bits.b_and_or(wh, Ah, Bh))))
          Equal.trans(Word(1n+p),
            Word.add(1n+p, Word.and(1n+p, WCon{wh, wt}, WCon{Ah, At}), Word.and(1n+p, WCon{wh, wt}, WCon{Bh, Bt})),
            WCon{Bool.or(Bool.and(wh, Ah), Bool.and(wh, Bh)), Word.add(p, Word.and(p, wt, At), Word.and(p, wt, Bt))},
            Word.and(1n+p, WCon{wh, wt}, Word.or(1n+p, WCon{Ah, At}, WCon{Bh, Bt})),
            step1, step2)

def gscale_shlput_false_zero(n: Nat) -> {Word.shl.put(n, False{}, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p), gscale_shlput_false_zero(p))

def gscale_shl_zero(n: Nat) -> {Word.shl(n, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p), gscale_shlput_false_zero(p))

def gscale_shl_n_zero(+n: Nat, k: Nat) -> {Bits.shl_n(n, Word.zero(n), k) == Word.zero(n) : Word(n)}:
  match k:
    case 0n: {==}
    case 1n+q:
      Equal.trans(Word(n),
        Bits.shl_n(n, Word.zero(n), 1n+q),
        Word.shl(n, Word.zero(n)),
        Word.zero(n),
        Equal.cong(Word(n), Word(n), x => Word.shl(n, x), Bits.shl_n(n, Word.zero(n), q), Word.zero(n), gscale_shl_n_zero(n, q)),
        gscale_shl_zero(n))

# A left-shifted field misses the low `k` bits: `M && (X << k) = 0` once `M >> k
# = 0`. This is `Bits.and_shl_n` plus the concrete mask facts `mask k >> k = 0`.
def gscale_and_shl_zero(+n: Nat, +k: Nat, +X: Word(n), +M: Word(n),
    +h: {Bits.shr_n(n, k, M) == Word.zero(n) : Word(n)})
  -> {Word.and(n, M, Bits.shl_n(n, X, k)) == Word.zero(n) : Word(n)}:
  +ezx = Equal.trans(Word(n),
    Word.and(n, Word.zero(n), X),
    Word.and(n, X, Word.zero(n)),
    Word.zero(n),
    Bits.w_and_comm(n, Word.zero(n), X),
    Bits.w_and_zero(n, X))
  Equal.trans(Word(n),
    Word.and(n, M, Bits.shl_n(n, X, k)),
    Bits.shl_n(n, Word.and(n, Bits.shr_n(n, k, M), X), k),
    Word.zero(n),
    Bits.and_shl_n(n, k, M, X),
    Equal.trans(Word(n),
      Bits.shl_n(n, Word.and(n, Bits.shr_n(n, k, M), X), k),
      Bits.shl_n(n, Word.and(n, Word.zero(n), X), k),
      Word.zero(n),
      Equal.cong(Word(n), Word(n), x => Bits.shl_n(n, x, k),
        Word.and(n, Bits.shr_n(n, k, M), X), Word.and(n, Word.zero(n), X),
        Equal.cong(Word(n), Word(n), x => Word.and(n, x, X), Bits.shr_n(n, k, M), Word.zero(n), h)),
      Equal.trans(Word(n),
        Bits.shl_n(n, Word.and(n, Word.zero(n), X), k),
        Bits.shl_n(n, Word.zero(n), k),
        Word.zero(n),
        Equal.cong(Word(n), Word(n), x => Bits.shl_n(n, x, k),
          Word.and(n, Word.zero(n), X), Word.zero(n), ezx),
        gscale_shl_n_zero(n, k))))

def gscale_shr10_m10() -> {Bits.shr_n(32n, 10n, Bits.mask(32n, 10n)) == Word.zero(32n) : Word(32n)}:
  {==}

def gscale_shr20_m10() -> {Bits.shr_n(32n, 20n, Bits.mask(32n, 10n)) == Word.zero(32n) : Word(32n)}:
  {==}

def gscale_shr4_m4() -> {Bits.shr_n(32n, 4n, Bits.mask(32n, 4n)) == Word.zero(32n) : Word(32n)}:
  {==}

def gscale_shr8_m4() -> {Bits.shr_n(32n, 8n, Bits.mask(32n, 4n)) == Word.zero(32n) : Word(32n)}:
  {==}

def gscale_mask_hi_and() -> {Word.and(32n, Bits.shl_n(32n, gscale_m10(), 4n), gscale_m4()) == Word.zero(32n) : Word(32n)}:
  {==}

def gscale_mask_hi_or() -> {Word.or(32n, Bits.shl_n(32n, gscale_m10(), 4n), gscale_m4()) == Bits.mask(32n, 14n) : Word(32n)}:
  {==}

# The masked split/rejoin: `(w >> 4) << 4 + (w & 15) = w & 16383`. The two
# addends are disjoint masked fields of `w`, so `gscale_add_and_or` replaces the
# addition by an `or`, and the two field masks cover exactly the low 14 bits.
def gscale_global_rt(+w: Word(32n)) ->
  {Word.add(32n, Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, 4n, w), gscale_m10()), 4n), Word.and(32n, w, gscale_m4())) == Word.and(32n, w, Bits.mask(32n, 14n)) : Word(32n)}:
  +Mhi = Bits.shl_n(32n, gscale_m10(), 4n)
  +B4 = Word.and(32n, w, gscale_m4())
  +eA = Equal.sym(Word(32n),
    Word.and(32n, w, Mhi),
    Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, 4n, w), gscale_m10()), 4n),
    Bits.and_shl_n(32n, 4n, w, gscale_m10()))
  +step = gscale_add_and_or(32n, w, Mhi, gscale_m4(), gscale_mask_hi_and())
  Equal.trans(Word(32n),
    Word.add(32n, Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, 4n, w), gscale_m10()), 4n), B4),
    Word.add(32n, Word.and(32n, w, Mhi), B4),
    Word.and(32n, w, Bits.mask(32n, 14n)),
    Equal.cong(Word(32n), Word(32n), x => Word.add(32n, x, B4),
      Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, 4n, w), gscale_m10()), 4n),
      Word.and(32n, w, Mhi), eA),
    Equal.trans(Word(32n),
      Word.add(32n, Word.and(32n, w, Mhi), B4),
      Word.and(32n, w, Word.or(32n, Mhi, gscale_m4())),
      Word.and(32n, w, Bits.mask(32n, 14n)),
      step,
      Equal.cong(Word(32n), Word(32n), x => Word.and(32n, w, x),
        Word.or(32n, Mhi, gscale_m4()), Bits.mask(32n, 14n), gscale_mask_hi_or())))

# ---------------------------------------------------------------------------
# Word-level mirrors of the `cw` fields, and the definitional bridges back to
# `cw` itself. The mirrors make the roundtrip statements readable; the bridges
# (`gscale_cw_*_word`) are `refl` because `cw` is a transparent wrapper.
# ---------------------------------------------------------------------------

def gscale_key_word(cx: Word(32n), cy: Word(32n), cz: Word(32n)) -> Word(32n):
  Word.or(32n, Word.or(32n, Word.and(32n, cx, gscale_m10()), Bits.shl_n(32n, Word.and(32n, cz, gscale_m10()), 10n)), Bits.shl_n(32n, Word.and(32n, cy, gscale_m10()), 20n))

def gscale_local_word(lx: Word(32n), ly: Word(32n), lz: Word(32n)) -> Word(32n):
  Word.or(32n, Word.or(32n, Word.and(32n, lx, gscale_m4()), Bits.shl_n(32n, Word.and(32n, lz, gscale_m4()), 4n)), Bits.shl_n(32n, Word.and(32n, ly, gscale_m4()), 8n))

def gscale_global_x_word(k: Word(32n), l: Word(32n)) -> Word(32n):
  Word.add(32n, Bits.shl_n(32n, Word.and(32n, k, gscale_m10()), 4n), Word.and(32n, l, gscale_m4()))

def gscale_global_y_word(k: Word(32n), l: Word(32n)) -> Word(32n):
  Word.add(32n, Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, 20n, k), gscale_m10()), 4n), Word.and(32n, Bits.shr_n(32n, 8n, l), gscale_m4()))

def gscale_global_z_word(k: Word(32n), l: Word(32n)) -> Word(32n):
  Word.add(32n, Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, 10n, k), gscale_m10()), 4n), Word.and(32n, Bits.shr_n(32n, 4n, l), gscale_m4()))

def gscale_cw_key_word(cxw: Word(32n), cyw: Word(32n), czw: Word(32n)) ->
  {Cw.cw_key(U32{cxw}, U32{cyw}, U32{czw}) == U32{gscale_key_word(cxw, cyw, czw)} : U32}:
  {==}

def gscale_cw_local_word(lxw: Word(32n), lyw: Word(32n), lzw: Word(32n)) ->
  {Cw.cw_local(U32{lxw}, U32{lyw}, U32{lzw}) == U32{gscale_local_word(lxw, lyw, lzw)} : U32}:
  {==}

def gscale_cw_global_x_word(kw: Word(32n), lw: Word(32n)) ->
  {Cw.cw_global_x(U32{kw}, U32{lw}) == U32{gscale_global_x_word(kw, lw)} : U32}:
  {==}

def gscale_cw_global_y_word(kw: Word(32n), lw: Word(32n)) ->
  {Cw.cw_global_y(U32{kw}, U32{lw}) == U32{gscale_global_y_word(kw, lw)} : U32}:
  {==}

def gscale_cw_global_z_word(kw: Word(32n), lw: Word(32n)) ->
  {Cw.cw_global_z(U32{kw}, U32{lw}) == U32{gscale_global_z_word(kw, lw)} : U32}:
  {==}

def gscale_cw_chunk_word(xw: Word(32n)) -> {Cw.cw_chunk_of(U32{xw}) == U32{Bits.shr_n(32n, 4n, xw)} : U32}:
  {==}

def gscale_cw_localof_word(xw: Word(32n)) -> {Cw.cw_local_of(U32{xw}) == U32{Word.and(32n, xw, gscale_m4())} : U32}:
  {==}

def gscale_cw_keyx_word(kw: Word(32n)) -> {Cw.cw_key_x(U32{kw}) == U32{Word.and(32n, kw, gscale_m10())} : U32}:
  {==}

def gscale_cw_keyy_word(kw: Word(32n)) -> {Cw.cw_key_y(U32{kw}) == U32{Word.and(32n, Bits.shr_n(32n, 20n, kw), gscale_m10())} : U32}:
  {==}

def gscale_cw_keyz_word(kw: Word(32n)) -> {Cw.cw_key_z(U32{kw}) == U32{Word.and(32n, Bits.shr_n(32n, 10n, kw), gscale_m10())} : U32}:
  {==}

def gscale_cw_localx_word(lw: Word(32n)) -> {Cw.cw_local_x(U32{lw}) == U32{Word.and(32n, lw, gscale_m4())} : U32}:
  {==}

def gscale_cw_localy_word(lw: Word(32n)) -> {Cw.cw_local_y(U32{lw}) == U32{Word.and(32n, Bits.shr_n(32n, 8n, lw), gscale_m4())} : U32}:
  {==}

def gscale_cw_localz_word(lw: Word(32n)) -> {Cw.cw_local_z(U32{lw}) == U32{Word.and(32n, Bits.shr_n(32n, 4n, lw), gscale_m4())} : U32}:
  {==}

def gscale_kx(k: Word(32n)) -> Word(32n):
  Word.and(32n, k, gscale_m10())

def gscale_kz(k: Word(32n)) -> Word(32n):
  Word.and(32n, Bits.shr_n(32n, 10n, k), gscale_m10())

def gscale_ky(k: Word(32n)) -> Word(32n):
  Word.and(32n, Bits.shr_n(32n, 20n, k), gscale_m10())

def gscale_lx(l: Word(32n)) -> Word(32n):
  Word.and(32n, l, gscale_m4())

def gscale_lz(l: Word(32n)) -> Word(32n):
  Word.and(32n, Bits.shr_n(32n, 4n, l), gscale_m4())

def gscale_ly(l: Word(32n)) -> Word(32n):
  Word.and(32n, Bits.shr_n(32n, 8n, l), gscale_m4())

# `(A or B) && M = (A && M) or (B && M)`.
def gscale_and_or_z(+A: Word(32n), +B: Word(32n), +M: Word(32n))
  -> {Word.and(32n, Word.or(32n, A, B), M) == Word.or(32n, Word.and(32n, A, M), Word.and(32n, B, M)) : Word(32n)}:
  Equal.trans(Word(32n),
    Word.and(32n, Word.or(32n, A, B), M),
    Word.and(32n, M, Word.or(32n, A, B)),
    Word.or(32n, Word.and(32n, A, M), Word.and(32n, B, M)),
    Bits.w_and_comm(32n, Word.or(32n, A, B), M),
    Equal.trans(Word(32n),
      Word.and(32n, M, Word.or(32n, A, B)),
      Word.or(32n, Word.and(32n, M, A), Word.and(32n, M, B)),
      Word.or(32n, Word.and(32n, A, M), Word.and(32n, B, M)),
      Bits.w_and_or(32n, M, A, B),
      Equal.trans(Word(32n),
        Word.or(32n, Word.and(32n, M, A), Word.and(32n, M, B)),
        Word.or(32n, Word.and(32n, A, M), Word.and(32n, M, B)),
        Word.or(32n, Word.and(32n, A, M), Word.and(32n, B, M)),
        Equal.cong(Word(32n), Word(32n), x => Word.or(32n, x, Word.and(32n, M, B)), Word.and(32n, M, A), Word.and(32n, A, M), Bits.w_and_comm(32n, M, A)),
        Equal.cong(Word(32n), Word(32n), x => Word.or(32n, Word.and(32n, A, M), x), Word.and(32n, M, B), Word.and(32n, B, M), Bits.w_and_comm(32n, M, B)))))

# `and (shl X k) M = 0` when `shl X k` is a lower field and `M` the next mask.
def gscale_shl_and_zero(+Y: Word(32n), +M: Word(32n), +k: Nat,
    +h: {Bits.shr_n(32n, k, Y) == Word.zero(32n) : Word(32n)})
  -> {Word.and(32n, Y, Bits.shl_n(32n, M, k)) == Word.zero(32n) : Word(32n)}:
  Equal.trans(Word(32n),
    Word.and(32n, Y, Bits.shl_n(32n, M, k)),
    Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, k, Y), M), k),
    Word.zero(32n),
    Bits.and_shl_n(32n, k, Y, M),
    Equal.trans(Word(32n),
      Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, k, Y), M), k),
      Bits.shl_n(32n, Word.and(32n, Word.zero(32n), M), k),
      Word.zero(32n),
      Equal.cong(Word(32n), Word(32n), x => Bits.shl_n(32n, x, k),
        Word.and(32n, Bits.shr_n(32n, k, Y), M), Word.and(32n, Word.zero(32n), M),
        Equal.cong(Word(32n), Word(32n), x => Word.and(32n, x, M), Bits.shr_n(32n, k, Y), Word.zero(32n), h)),
      Equal.trans(Word(32n),
        Bits.shl_n(32n, Word.and(32n, Word.zero(32n), M), k),
        Bits.shl_n(32n, Word.zero(32n), k),
        Word.zero(32n),
        Equal.cong(Word(32n), Word(32n), x => Bits.shl_n(32n, x, k),
          Word.and(32n, Word.zero(32n), M), Word.zero(32n),
          Equal.trans(Word(32n), Word.and(32n, Word.zero(32n), M), Word.and(32n, M, Word.zero(32n)), Word.zero(32n),
            Bits.w_and_comm(32n, Word.zero(32n), M), Bits.w_and_zero(32n, M))),
        gscale_shl_n_zero(32n, k))))

# `shift right by k then mask` clears a masked low field: `M >> k = 0` plus
# `Bits.shr_n_and` gives `(X && M) >> k = 0`.
def gscale_shr_and_zero(+X: Word(32n), +M: Word(32n), +k: Nat,
    +h: {Bits.shr_n(32n, k, M) == Word.zero(32n) : Word(32n)})
  -> {Bits.shr_n(32n, k, Word.and(32n, X, M)) == Word.zero(32n) : Word(32n)}:
  Equal.trans(Word(32n),
    Bits.shr_n(32n, k, Word.and(32n, X, M)),
    Word.and(32n, Bits.shr_n(32n, k, X), Bits.shr_n(32n, k, M)),
    Word.zero(32n),
    Bits.shr_n_and(32n, k, X, M),
    Equal.trans(Word(32n),
      Word.and(32n, Bits.shr_n(32n, k, X), Bits.shr_n(32n, k, M)),
      Word.and(32n, Bits.shr_n(32n, k, X), Word.zero(32n)),
      Word.zero(32n),
      Equal.cong(Word(32n), Word(32n), x => Word.and(32n, Bits.shr_n(32n, k, X), x),
        Bits.shr_n(32n, k, M), Word.zero(32n), h),
      Bits.w_and_zero(32n, Bits.shr_n(32n, k, X))))

# The low field of the packed key: `key && M = cx && M`.
def gscale_key_x_ext(+cx: Word(32n), +cy: Word(32n), +cz: Word(32n))
  -> {Word.and(32n, gscale_key_word(cx, cy, cz), gscale_m10()) == Word.and(32n, cx, gscale_m10()) : Word(32n)}:
  +A = Word.and(32n, cx, gscale_m10())
  +shB = Bits.shl_n(32n, Word.and(32n, cz, gscale_m10()), 10n)
  +shC = Bits.shl_n(32n, Word.and(32n, cy, gscale_m10()), 20n)
  +zB = gscale_and_shl_zero(32n, 10n, Word.and(32n, cz, gscale_m10()), gscale_m10(), gscale_shr10_m10())
  +zC = gscale_and_shl_zero(32n, 20n, Word.and(32n, cy, gscale_m10()), gscale_m10(), gscale_shr20_m10())
  +eAB = gscale_and_or_z(A, shB, gscale_m10())
  +eAll = gscale_and_or_z(Word.or(32n, A, shB), shC, gscale_m10())
  +eB = Equal.trans(Word(32n),
    Word.and(32n, shB, gscale_m10()),
    Word.and(32n, gscale_m10(), shB),
    Word.zero(32n),
    Bits.w_and_comm(32n, shB, gscale_m10()),
    zB)
  +eC = Equal.trans(Word(32n),
    Word.and(32n, shC, gscale_m10()),
    Word.and(32n, gscale_m10(), shC),
    Word.zero(32n),
    Bits.w_and_comm(32n, shC, gscale_m10()),
    zC)
  +eAz = Bits.w_and_absorb(32n, cx, gscale_m10())
  +inner = Equal.trans(Word(32n),
    Word.and(32n, Word.or(32n, A, shB), gscale_m10()),
    Word.or(32n, Word.and(32n, A, gscale_m10()), Word.and(32n, shB, gscale_m10())),
    A,
    eAB,
    Equal.trans(Word(32n),
      Word.or(32n, Word.and(32n, A, gscale_m10()), Word.and(32n, shB, gscale_m10())),
      Word.or(32n, A, Word.and(32n, shB, gscale_m10())),
      A,
      Equal.cong(Word(32n), Word(32n), x => Word.or(32n, x, Word.and(32n, shB, gscale_m10())), Word.and(32n, A, gscale_m10()), A, eAz),
      Equal.trans(Word(32n),
        Word.or(32n, A, Word.and(32n, shB, gscale_m10())),
        Word.or(32n, A, Word.zero(32n)),
        A,
        Equal.cong(Word(32n), Word(32n), x => Word.or(32n, A, x), Word.and(32n, shB, gscale_m10()), Word.zero(32n), eB),
        Bits.w_or_zero(32n, A))))
  Equal.trans(Word(32n),
    Word.and(32n, gscale_key_word(cx, cy, cz), gscale_m10()),
    Word.or(32n, Word.and(32n, Word.or(32n, A, shB), gscale_m10()), Word.and(32n, shC, gscale_m10())),
    A,
    eAll,
    Equal.trans(Word(32n),
      Word.or(32n, Word.and(32n, Word.or(32n, A, shB), gscale_m10()), Word.and(32n, shC, gscale_m10())),
      Word.or(32n, A, Word.and(32n, shC, gscale_m10())),
      A,
      Equal.cong(Word(32n), Word(32n), x => Word.or(32n, x, Word.and(32n, shC, gscale_m10())), Word.and(32n, Word.or(32n, A, shB), gscale_m10()), A, inner),
      Equal.trans(Word(32n),
        Word.or(32n, A, Word.and(32n, shC, gscale_m10())),
        Word.or(32n, A, Word.zero(32n)),
        A,
        Equal.cong(Word(32n), Word(32n), x => Word.or(32n, A, x), Word.and(32n, shC, gscale_m10()), Word.zero(32n), eC),
        Bits.w_or_zero(32n, A))))

# The low field of the packed local index: `local && M4 = lx && M4`.
def gscale_local_x_ext(+lx: Word(32n), +ly: Word(32n), +lz: Word(32n))
  -> {Word.and(32n, gscale_local_word(lx, ly, lz), gscale_m4()) == Word.and(32n, lx, gscale_m4()) : Word(32n)}:
  +A = Word.and(32n, lx, gscale_m4())
  +shB = Bits.shl_n(32n, Word.and(32n, lz, gscale_m4()), 4n)
  +shC = Bits.shl_n(32n, Word.and(32n, ly, gscale_m4()), 8n)
  +zB = gscale_and_shl_zero(32n, 4n, Word.and(32n, lz, gscale_m4()), gscale_m4(), gscale_shr4_m4())
  +zC = gscale_and_shl_zero(32n, 8n, Word.and(32n, ly, gscale_m4()), gscale_m4(), gscale_shr8_m4())
  +eAB = gscale_and_or_z(A, shB, gscale_m4())
  +eAll = gscale_and_or_z(Word.or(32n, A, shB), shC, gscale_m4())
  +eB = Equal.trans(Word(32n),
    Word.and(32n, shB, gscale_m4()),
    Word.and(32n, gscale_m4(), shB),
    Word.zero(32n),
    Bits.w_and_comm(32n, shB, gscale_m4()),
    zB)
  +eC = Equal.trans(Word(32n),
    Word.and(32n, shC, gscale_m4()),
    Word.and(32n, gscale_m4(), shC),
    Word.zero(32n),
    Bits.w_and_comm(32n, shC, gscale_m4()),
    zC)
  +eAz = Bits.w_and_absorb(32n, lx, gscale_m4())
  +inner = Equal.trans(Word(32n),
    Word.and(32n, Word.or(32n, A, shB), gscale_m4()),
    Word.or(32n, Word.and(32n, A, gscale_m4()), Word.and(32n, shB, gscale_m4())),
    A,
    eAB,
    Equal.trans(Word(32n),
      Word.or(32n, Word.and(32n, A, gscale_m4()), Word.and(32n, shB, gscale_m4())),
      Word.or(32n, A, Word.and(32n, shB, gscale_m4())),
      A,
      Equal.cong(Word(32n), Word(32n), x => Word.or(32n, x, Word.and(32n, shB, gscale_m4())), Word.and(32n, A, gscale_m4()), A, eAz),
      Equal.trans(Word(32n),
        Word.or(32n, A, Word.and(32n, shB, gscale_m4())),
        Word.or(32n, A, Word.zero(32n)),
        A,
        Equal.cong(Word(32n), Word(32n), x => Word.or(32n, A, x), Word.and(32n, shB, gscale_m4()), Word.zero(32n), eB),
        Bits.w_or_zero(32n, A))))
  Equal.trans(Word(32n),
    Word.and(32n, gscale_local_word(lx, ly, lz), gscale_m4()),
    Word.or(32n, Word.and(32n, Word.or(32n, A, shB), gscale_m4()), Word.and(32n, shC, gscale_m4())),
    A,
    eAll,
    Equal.trans(Word(32n),
      Word.or(32n, Word.and(32n, Word.or(32n, A, shB), gscale_m4()), Word.and(32n, shC, gscale_m4())),
      Word.or(32n, A, Word.and(32n, shC, gscale_m4())),
      A,
      Equal.cong(Word(32n), Word(32n), x => Word.or(32n, x, Word.and(32n, shC, gscale_m4())), Word.and(32n, Word.or(32n, A, shB), gscale_m4()), A, inner),
      Equal.trans(Word(32n),
        Word.or(32n, A, Word.and(32n, shC, gscale_m4())),
        Word.or(32n, A, Word.zero(32n)),
        A,
        Equal.cong(Word(32n), Word(32n), x => Word.or(32n, A, x), Word.and(32n, shC, gscale_m4()), Word.zero(32n), eC),
        Bits.w_or_zero(32n, A))))

def gscale_mask30_or() -> {Word.or(32n, Word.or(32n, gscale_m10(), Bits.shl_n(32n, gscale_m10(), 10n)), Bits.shl_n(32n, gscale_m10(), 20n)) == Bits.mask(32n, 30n) : Word(32n)}:
  {==}

def gscale_mask12_or() -> {Word.or(32n, Word.or(32n, gscale_m4(), Bits.shl_n(32n, gscale_m4(), 4n)), Bits.shl_n(32n, gscale_m4(), 8n)) == Bits.mask(32n, 12n) : Word(32n)}:
  {==}

# The key roundtrip, `Bits.model_index_rt` style: the three 10-bit fields at
# offsets 0/10/20 rebuild `k` masked to its 30 used bits. The nested masks from
# `cw_key` are absorbed, the shifted fields are pulled back with `and_shl_n`,
# and the field masks are recombined by `and_factor_l` + `mask30_or`.
def gscale_kmodel_rt(+k: Word(32n)) ->
  {gscale_key_word(gscale_kx(k), gscale_ky(k), gscale_kz(k)) == Word.and(32n, k, Bits.mask(32n, 30n)) : Word(32n)}:
  +A1 = Bits.shl_n(32n, gscale_m10(), 10n)
  +A2 = Bits.shl_n(32n, gscale_m10(), 20n)
  +sx = Bits.w_and_absorb(32n, k, gscale_m10())
  +sz = Bits.w_and_absorb(32n, Bits.shr_n(32n, 10n, k), gscale_m10())
  +sy = Bits.w_and_absorb(32n, Bits.shr_n(32n, 20n, k), gscale_m10())
  +e1 = Equal.sym(Word(32n), Word.and(32n, k, A1), Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, 10n, k), gscale_m10()), 10n), Bits.and_shl_n(32n, 10n, k, gscale_m10()))
  +e2 = Equal.sym(Word(32n), Word.and(32n, k, A2), Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, 20n, k), gscale_m10()), 20n), Bits.and_shl_n(32n, 20n, k, gscale_m10()))
  +p0 = Word.or(32n, Word.or(32n, gscale_kx(k), Bits.shl_n(32n, gscale_kz(k), 10n)), Bits.shl_n(32n, gscale_ky(k), 20n))
  +p1 = Word.or(32n, Word.or(32n, gscale_kx(k), Word.and(32n, k, A1)), Word.and(32n, k, A2))
  +sA = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, x, Bits.shl_n(32n, Word.and(32n, gscale_kz(k), gscale_m10()), 10n)), Bits.shl_n(32n, Word.and(32n, gscale_ky(k), gscale_m10()), 20n)),
    Word.and(32n, gscale_kx(k), gscale_m10()), gscale_kx(k), sx)
  +sB = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, gscale_kx(k), Bits.shl_n(32n, x, 10n)), Bits.shl_n(32n, Word.and(32n, gscale_ky(k), gscale_m10()), 20n)),
    Word.and(32n, gscale_kz(k), gscale_m10()), gscale_kz(k), sz)
  +sFirst = Equal.trans(Word(32n),
    gscale_key_word(gscale_kx(k), gscale_ky(k), gscale_kz(k)),
    Word.or(32n, Word.or(32n, gscale_kx(k), Bits.shl_n(32n, Word.and(32n, gscale_kz(k), gscale_m10()), 10n)), Bits.shl_n(32n, Word.and(32n, gscale_ky(k), gscale_m10()), 20n)),
    Word.or(32n, Word.or(32n, gscale_kx(k), Bits.shl_n(32n, gscale_kz(k), 10n)), Bits.shl_n(32n, Word.and(32n, gscale_ky(k), gscale_m10()), 20n)),
    sA, sB)
  +sSecond = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, gscale_kx(k), Bits.shl_n(32n, gscale_kz(k), 10n)), Bits.shl_n(32n, x, 20n)),
    Word.and(32n, gscale_ky(k), gscale_m10()), gscale_ky(k), sy)
  +p0a = Equal.trans(Word(32n),
    gscale_key_word(gscale_kx(k), gscale_ky(k), gscale_kz(k)),
    Word.or(32n, Word.or(32n, gscale_kx(k), Bits.shl_n(32n, gscale_kz(k), 10n)), Bits.shl_n(32n, Word.and(32n, gscale_ky(k), gscale_m10()), 20n)),
    p0,
    sFirst, sSecond)
  +tC = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, gscale_kx(k), x), Bits.shl_n(32n, gscale_ky(k), 20n)),
    Bits.shl_n(32n, gscale_kz(k), 10n), Word.and(32n, k, A1), e1)
  +tD = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, gscale_kx(k), Word.and(32n, k, A1)), x),
    Bits.shl_n(32n, gscale_ky(k), 20n), Word.and(32n, k, A2), e2)
  Equal.trans(Word(32n),
    gscale_key_word(gscale_kx(k), gscale_ky(k), gscale_kz(k)),
    p1,
    Word.and(32n, k, Bits.mask(32n, 30n)),
    Equal.trans(Word(32n), gscale_key_word(gscale_kx(k), gscale_ky(k), gscale_kz(k)), p0, p1, p0a, Equal.trans(Word(32n), p0, Word.or(32n, Word.or(32n, gscale_kx(k), Word.and(32n, k, A1)), Bits.shl_n(32n, gscale_ky(k), 20n)), p1, tC, tD)),
    Equal.trans(Word(32n),
      p1,
      Word.and(32n, k, Word.or(32n, Word.or(32n, gscale_m10(), A1), A2)),
      Word.and(32n, k, Bits.mask(32n, 30n)),
      Bits.and_factor_l(32n, k, gscale_m10(), A1, A2),
      Equal.cong(Word(32n), Word(32n), x => Word.and(32n, k, x),
        Word.or(32n, Word.or(32n, gscale_m10(), A1), A2), Bits.mask(32n, 30n), gscale_mask30_or())))

def gscale_lmodel_rt(+l: Word(32n)) ->
  {gscale_local_word(gscale_lx(l), gscale_ly(l), gscale_lz(l)) == Word.and(32n, l, Bits.mask(32n, 12n)) : Word(32n)}:
  +A1 = Bits.shl_n(32n, gscale_m4(), 4n)
  +A2 = Bits.shl_n(32n, gscale_m4(), 8n)
  +sx = Bits.w_and_absorb(32n, l, gscale_m4())
  +sz = Bits.w_and_absorb(32n, Bits.shr_n(32n, 4n, l), gscale_m4())
  +sy = Bits.w_and_absorb(32n, Bits.shr_n(32n, 8n, l), gscale_m4())
  +e1 = Equal.sym(Word(32n), Word.and(32n, l, A1), Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, 4n, l), gscale_m4()), 4n), Bits.and_shl_n(32n, 4n, l, gscale_m4()))
  +e2 = Equal.sym(Word(32n), Word.and(32n, l, A2), Bits.shl_n(32n, Word.and(32n, Bits.shr_n(32n, 8n, l), gscale_m4()), 8n), Bits.and_shl_n(32n, 8n, l, gscale_m4()))
  +p0 = Word.or(32n, Word.or(32n, gscale_lx(l), Bits.shl_n(32n, gscale_lz(l), 4n)), Bits.shl_n(32n, gscale_ly(l), 8n))
  +p1 = Word.or(32n, Word.or(32n, gscale_lx(l), Word.and(32n, l, A1)), Word.and(32n, l, A2))
  +sA = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, x, Bits.shl_n(32n, Word.and(32n, gscale_lz(l), gscale_m4()), 4n)), Bits.shl_n(32n, Word.and(32n, gscale_ly(l), gscale_m4()), 8n)),
    Word.and(32n, gscale_lx(l), gscale_m4()), gscale_lx(l), sx)
  +sB = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, gscale_lx(l), Bits.shl_n(32n, x, 4n)), Bits.shl_n(32n, Word.and(32n, gscale_ly(l), gscale_m4()), 8n)),
    Word.and(32n, gscale_lz(l), gscale_m4()), gscale_lz(l), sz)
  +sFirst = Equal.trans(Word(32n),
    gscale_local_word(gscale_lx(l), gscale_ly(l), gscale_lz(l)),
    Word.or(32n, Word.or(32n, gscale_lx(l), Bits.shl_n(32n, Word.and(32n, gscale_lz(l), gscale_m4()), 4n)), Bits.shl_n(32n, Word.and(32n, gscale_ly(l), gscale_m4()), 8n)),
    Word.or(32n, Word.or(32n, gscale_lx(l), Bits.shl_n(32n, gscale_lz(l), 4n)), Bits.shl_n(32n, Word.and(32n, gscale_ly(l), gscale_m4()), 8n)),
    sA, sB)
  +sSecond = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, gscale_lx(l), Bits.shl_n(32n, gscale_lz(l), 4n)), Bits.shl_n(32n, x, 8n)),
    Word.and(32n, gscale_ly(l), gscale_m4()), gscale_ly(l), sy)
  +p0a = Equal.trans(Word(32n),
    gscale_local_word(gscale_lx(l), gscale_ly(l), gscale_lz(l)),
    Word.or(32n, Word.or(32n, gscale_lx(l), Bits.shl_n(32n, gscale_lz(l), 4n)), Bits.shl_n(32n, Word.and(32n, gscale_ly(l), gscale_m4()), 8n)),
    p0,
    sFirst, sSecond)
  +tC = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, gscale_lx(l), x), Bits.shl_n(32n, gscale_ly(l), 8n)),
    Bits.shl_n(32n, gscale_lz(l), 4n), Word.and(32n, l, A1), e1)
  +tD = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, gscale_lx(l), Word.and(32n, l, A1)), x),
    Bits.shl_n(32n, gscale_ly(l), 8n), Word.and(32n, l, A2), e2)
  Equal.trans(Word(32n),
    gscale_local_word(gscale_lx(l), gscale_ly(l), gscale_lz(l)),
    p1,
    Word.and(32n, l, Bits.mask(32n, 12n)),
    Equal.trans(Word(32n), gscale_local_word(gscale_lx(l), gscale_ly(l), gscale_lz(l)), p0, p1, p0a, Equal.trans(Word(32n), p0, Word.or(32n, Word.or(32n, gscale_lx(l), Word.and(32n, l, A1)), Bits.shl_n(32n, gscale_ly(l), 8n)), p1, tC, tD)),
    Equal.trans(Word(32n),
      p1,
      Word.and(32n, l, Word.or(32n, Word.or(32n, gscale_m4(), A1), A2)),
      Word.and(32n, l, Bits.mask(32n, 12n)),
      Bits.and_factor_l(32n, l, gscale_m4(), A1, A2),
      Equal.cong(Word(32n), Word(32n), x => Word.and(32n, l, x),
        Word.or(32n, Word.or(32n, gscale_m4(), A1), A2), Bits.mask(32n, 12n), gscale_mask12_or())))

# ---------------------------------------------------------------------------
# Field extraction for the shifted (y/z) axes.
#
# `Parity.shr_shl_kmask` gives `(X << k) >> k = X && kmask k`; when `X` is
# already masked the `kmask` factor is absorbed, so `(X << k) >> k = X`. That is
# the fact that lets `cw_key_y`/`cw_key_z` (resp. `cw_local_y`/`cw_local_z`)
# recover their field after the packing shift.
# ---------------------------------------------------------------------------
def gscale_kmask_eq10() -> {Parity.kmask(10n) == Bits.mask(32n, 22n) : Word(32n)}: {==}
def gscale_kmask_eq20() -> {Parity.kmask(20n) == Bits.mask(32n, 12n) : Word(32n)}: {==}
def gscale_kmask_eq4() -> {Parity.kmask(4n) == Bits.mask(32n, 28n) : Word(32n)}: {==}
def gscale_kmask_eq8() -> {Parity.kmask(8n) == Bits.mask(32n, 24n) : Word(32n)}: {==}
def gscale_kabs10() -> {Word.and(32n, gscale_m10(), Bits.mask(32n, 22n)) == gscale_m10() : Word(32n)}: {==}
def gscale_kabs20() -> {Word.and(32n, gscale_m10(), Bits.mask(32n, 12n)) == gscale_m10() : Word(32n)}: {==}
def gscale_kabs4() -> {Word.and(32n, gscale_m4(), Bits.mask(32n, 28n)) == gscale_m4() : Word(32n)}: {==}
def gscale_kabs8() -> {Word.and(32n, gscale_m4(), Bits.mask(32n, 24n)) == gscale_m4() : Word(32n)}: {==}

def gscale_shr_shl_masked(+k: Nat, +X: Word(32n), +M: Word(32n), +K: Word(32n),
    +hk: {Parity.kmask(k) == K : Word(32n)},
    +ha: {Word.and(32n, M, K) == M : Word(32n)})
  -> {Bits.shr_n(32n, k, Bits.shl_n(32n, Word.and(32n, X, M), k)) == Word.and(32n, X, M) : Word(32n)}:
  +Xm = Word.and(32n, X, M)
  Equal.trans(Word(32n),
    Bits.shr_n(32n, k, Bits.shl_n(32n, Xm, k)),
    Word.and(32n, Xm, Parity.kmask(k)),
    Xm,
    Parity.shr_shl_kmask(k, Xm),
    Equal.trans(Word(32n),
      Word.and(32n, Xm, Parity.kmask(k)),
      Word.and(32n, Xm, K),
      Xm,
      Equal.cong(Word(32n), Word(32n), x => Word.and(32n, Xm, x), Parity.kmask(k), K, hk),
      Equal.trans(Word(32n),
        Word.and(32n, Xm, K),
        Word.and(32n, X, Word.and(32n, M, K)),
        Xm,
        Bits.w_and_assoc(32n, X, M, K),
        Equal.trans(Word(32n),
          Word.and(32n, X, Word.and(32n, M, K)),
          Word.and(32n, X, M),
          Xm,
          Equal.cong(Word(32n), Word(32n), x => Word.and(32n, X, x), Word.and(32n, M, K), M, ha),
          {==}))))

def gscale_shr20_shl20_m10(+X: Word(32n)) -> {Bits.shr_n(32n, 20n, Bits.shl_n(32n, Word.and(32n, X, gscale_m10()), 20n)) == Word.and(32n, X, gscale_m10()) : Word(32n)}:
  gscale_shr_shl_masked(20n, X, gscale_m10(), Bits.mask(32n, 12n), gscale_kmask_eq20(), gscale_kabs20())

def gscale_shr10_shl10_m10(+X: Word(32n)) -> {Bits.shr_n(32n, 10n, Bits.shl_n(32n, Word.and(32n, X, gscale_m10()), 10n)) == Word.and(32n, X, gscale_m10()) : Word(32n)}:
  gscale_shr_shl_masked(10n, X, gscale_m10(), Bits.mask(32n, 22n), gscale_kmask_eq10(), gscale_kabs10())

def gscale_shr8_shl8_m4(+X: Word(32n)) -> {Bits.shr_n(32n, 8n, Bits.shl_n(32n, Word.and(32n, X, gscale_m4()), 8n)) == Word.and(32n, X, gscale_m4()) : Word(32n)}:
  gscale_shr_shl_masked(8n, X, gscale_m4(), Bits.mask(32n, 24n), gscale_kmask_eq8(), gscale_kabs8())

def gscale_shr4_shl4_m4(+X: Word(32n)) -> {Bits.shr_n(32n, 4n, Bits.shl_n(32n, Word.and(32n, X, gscale_m4()), 4n)) == Word.and(32n, X, gscale_m4()) : Word(32n)}:
  gscale_shr_shl_masked(4n, X, gscale_m4(), Bits.mask(32n, 28n), gscale_kmask_eq4(), gscale_kabs4())

def gscale_and_lzero(+X: Word(32n)) -> {Word.and(32n, Word.zero(32n), X) == Word.zero(32n) : Word(32n)}:
  Equal.trans(Word(32n), Word.and(32n, Word.zero(32n), X), Word.and(32n, X, Word.zero(32n)), Word.zero(32n),
    Bits.w_and_comm(32n, Word.zero(32n), X), Bits.w_and_zero(32n, X))

def gscale_or_rzero(+X: Word(32n)) -> {Word.or(32n, Word.zero(32n), X) == X : Word(32n)}:
  Equal.trans(Word(32n), Word.or(32n, Word.zero(32n), X), Word.or(32n, X, Word.zero(32n)), X,
    Bits.w_or_comm(32n, Word.zero(32n), X), Bits.w_or_zero(32n, X))

# `or (or (and 0 M) (and 0 M << k)) HIGH = HIGH` -- the zero low two fields of
# `cw_key(0, cy, 0)` (resp. `cw_local(0, ly, 0)`).
def gscale_or_low_high(+HIGH: Word(32n), +M: Word(32n), +k: Nat)
  -> {Word.or(32n, Word.or(32n, Word.and(32n, Word.zero(32n), M), Bits.shl_n(32n, Word.and(32n, Word.zero(32n), M), k)), HIGH) == HIGH : Word(32n)}:
  +Z = Word.and(32n, Word.zero(32n), M)
  +ez = gscale_and_lzero(M)
  +ek = Equal.trans(Word(32n), Bits.shl_n(32n, Z, k), Bits.shl_n(32n, Word.zero(32n), k), Word.zero(32n),
    Equal.cong(Word(32n), Word(32n), x => Bits.shl_n(32n, x, k), Z, Word.zero(32n), ez),
    gscale_shl_n_zero(32n, k))
  +einner = Equal.trans(Word(32n), Word.or(32n, Z, Bits.shl_n(32n, Z, k)), Word.or(32n, Word.zero(32n), Word.zero(32n)), Word.zero(32n),
    Equal.trans(Word(32n),
      Word.or(32n, Z, Bits.shl_n(32n, Z, k)),
      Word.or(32n, Word.zero(32n), Bits.shl_n(32n, Z, k)),
      Word.or(32n, Word.zero(32n), Word.zero(32n)),
      Equal.cong(Word(32n), Word(32n), x => Word.or(32n, x, Bits.shl_n(32n, Z, k)), Z, Word.zero(32n), ez),
      Equal.cong(Word(32n), Word(32n), x => Word.or(32n, Word.zero(32n), x), Bits.shl_n(32n, Z, k), Word.zero(32n), ek)),
    Bits.w_or_zero(32n, Word.zero(32n)))
  Equal.trans(Word(32n),
    Word.or(32n, Word.or(32n, Z, Bits.shl_n(32n, Z, k)), HIGH),
    Word.or(32n, Word.zero(32n), HIGH),
    HIGH,
    Equal.cong(Word(32n), Word(32n), x => Word.or(32n, x, HIGH), Word.or(32n, Z, Bits.shl_n(32n, Z, k)), Word.zero(32n), einner),
    gscale_or_rzero(HIGH))

# `or (or (and 0 M) MID) (and 0 M << k) = MID` -- the zero low/high fields of
# `cw_key(0, 0, cz)` (resp. `cw_local(0, 0, lz)`).
def gscale_or_mid_high(+MID: Word(32n), +M: Word(32n), +k: Nat)
  -> {Word.or(32n, Word.or(32n, Word.and(32n, Word.zero(32n), M), MID), Bits.shl_n(32n, Word.and(32n, Word.zero(32n), M), k)) == MID : Word(32n)}:
  +Z = Word.and(32n, Word.zero(32n), M)
  +ez = gscale_and_lzero(M)
  +ek = Equal.trans(Word(32n), Bits.shl_n(32n, Z, k), Bits.shl_n(32n, Word.zero(32n), k), Word.zero(32n),
    Equal.cong(Word(32n), Word(32n), x => Bits.shl_n(32n, x, k), Z, Word.zero(32n), ez),
    gscale_shl_n_zero(32n, k))
  +einner = Equal.trans(Word(32n), Word.or(32n, Z, MID), Word.or(32n, Word.zero(32n), MID), MID,
    Equal.cong(Word(32n), Word(32n), x => Word.or(32n, x, MID), Z, Word.zero(32n), ez),
    gscale_or_rzero(MID))
  Equal.trans(Word(32n),
    Word.or(32n, Word.or(32n, Z, MID), Bits.shl_n(32n, Z, k)),
    Word.or(32n, MID, Word.zero(32n)),
    MID,
    Equal.trans(Word(32n),
      Word.or(32n, Word.or(32n, Z, MID), Bits.shl_n(32n, Z, k)),
      Word.or(32n, MID, Bits.shl_n(32n, Z, k)),
      Word.or(32n, MID, Word.zero(32n)),
      Equal.cong(Word(32n), Word(32n), x => Word.or(32n, x, Bits.shl_n(32n, Z, k)), Word.or(32n, Z, MID), MID, einner),
      Equal.cong(Word(32n), Word(32n), x => Word.or(32n, MID, x), Bits.shl_n(32n, Z, k), Word.zero(32n), ek)),
    Bits.w_or_zero(32n, MID))

def gscale_key_y_red(+cyw: Word(32n)) -> {gscale_key_word(Word.zero(32n), cyw, Word.zero(32n)) == Bits.shl_n(32n, Word.and(32n, cyw, gscale_m10()), 20n) : Word(32n)}:
  gscale_or_low_high(Bits.shl_n(32n, Word.and(32n, cyw, gscale_m10()), 20n), gscale_m10(), 10n)

def gscale_key_z_red(+czw: Word(32n)) -> {gscale_key_word(Word.zero(32n), Word.zero(32n), czw) == Bits.shl_n(32n, Word.and(32n, czw, gscale_m10()), 10n) : Word(32n)}:
  gscale_or_mid_high(Bits.shl_n(32n, Word.and(32n, czw, gscale_m10()), 10n), gscale_m10(), 20n)

def gscale_local_y_red(+lyw: Word(32n)) -> {gscale_local_word(Word.zero(32n), lyw, Word.zero(32n)) == Bits.shl_n(32n, Word.and(32n, lyw, gscale_m4()), 8n) : Word(32n)}:
  gscale_or_low_high(Bits.shl_n(32n, Word.and(32n, lyw, gscale_m4()), 8n), gscale_m4(), 4n)

def gscale_local_z_red(+lzw: Word(32n)) -> {gscale_local_word(Word.zero(32n), Word.zero(32n), lzw) == Bits.shl_n(32n, Word.and(32n, lzw, gscale_m4()), 4n) : Word(32n)}:
  gscale_or_mid_high(Bits.shl_n(32n, Word.and(32n, lzw, gscale_m4()), 4n), gscale_m4(), 8n)

# ---------------------------------------------------------------------------
# The composed `U32` statements. Each destructures the coordinates and pushes
# the field extraction and `gscale_global_rt` through `Equal.cong` under the
# `U32` wrapper. The `cw` wrappers are transparent, so the bridges are `refl`.
# ---------------------------------------------------------------------------

def gscale_cw_x_word(+xw: Word(32n), +yw: Word(32n), +zw: Word(32n)) ->
  {gscale_global_x_word(gscale_key_word(Bits.shr_n(32n, 4n, xw), Bits.shr_n(32n, 4n, yw), Bits.shr_n(32n, 4n, zw)), gscale_local_word(Word.and(32n, xw, gscale_m4()), Word.and(32n, yw, gscale_m4()), Word.and(32n, zw, gscale_m4()))) == Word.and(32n, xw, Bits.mask(32n, 14n)) : Word(32n)}:
  +cxw = Bits.shr_n(32n, 4n, xw)
  +cyw = Bits.shr_n(32n, 4n, yw)
  +czw = Bits.shr_n(32n, 4n, zw)
  +lxw = Word.and(32n, xw, gscale_m4())
  +lyw = Word.and(32n, yw, gscale_m4())
  +lzw = Word.and(32n, zw, gscale_m4())
  +kw = gscale_key_word(cxw, cyw, czw)
  +lw = gscale_local_word(lxw, lyw, lzw)
  +eKey = gscale_key_x_ext(cxw, cyw, czw)
  +eLoc = gscale_local_x_ext(lxw, lyw, lzw)
  +eAbs = Bits.w_and_absorb(32n, xw, gscale_m4())
  +eA = Equal.cong(Word(32n), Word(32n),
    x => Word.add(32n, Bits.shl_n(32n, x, 4n), Word.and(32n, lw, gscale_m4())),
    Word.and(32n, kw, gscale_m10()), Word.and(32n, cxw, gscale_m10()), eKey)
  +eB = Equal.cong(Word(32n), Word(32n),
    x => Word.add(32n, Bits.shl_n(32n, Word.and(32n, cxw, gscale_m10()), 4n), x),
    Word.and(32n, lw, gscale_m4()), Word.and(32n, lxw, gscale_m4()), eLoc)
  +eC = Equal.cong(Word(32n), Word(32n),
    x => Word.add(32n, Bits.shl_n(32n, Word.and(32n, cxw, gscale_m10()), 4n), x),
    Word.and(32n, lxw, gscale_m4()), Word.and(32n, xw, gscale_m4()), eAbs)
  +inner = Equal.trans(Word(32n),
    Word.add(32n, Bits.shl_n(32n, Word.and(32n, kw, gscale_m10()), 4n), Word.and(32n, lw, gscale_m4())),
    Word.add(32n, Bits.shl_n(32n, Word.and(32n, cxw, gscale_m10()), 4n), Word.and(32n, lw, gscale_m4())),
    Word.add(32n, Bits.shl_n(32n, Word.and(32n, cxw, gscale_m10()), 4n), Word.and(32n, xw, gscale_m4())),
    eA,
    Equal.trans(Word(32n),
      Word.add(32n, Bits.shl_n(32n, Word.and(32n, cxw, gscale_m10()), 4n), Word.and(32n, lw, gscale_m4())),
      Word.add(32n, Bits.shl_n(32n, Word.and(32n, cxw, gscale_m10()), 4n), Word.and(32n, lxw, gscale_m4())),
      Word.add(32n, Bits.shl_n(32n, Word.and(32n, cxw, gscale_m10()), 4n), Word.and(32n, xw, gscale_m4())),
      eB, eC))
  Equal.trans(Word(32n),
    gscale_global_x_word(kw, lw),
    Word.add(32n, Bits.shl_n(32n, Word.and(32n, cxw, gscale_m10()), 4n), Word.and(32n, xw, gscale_m4())),
    Word.and(32n, xw, Bits.mask(32n, 14n)),
    inner, gscale_global_rt(xw))

def gscale_cw_y_word(+yw: Word(32n)) ->
  {gscale_global_y_word(gscale_key_word(Word.zero(32n), Bits.shr_n(32n, 4n, yw), Word.zero(32n)), gscale_local_word(Word.zero(32n), Word.and(32n, yw, gscale_m4()), Word.zero(32n))) == Word.and(32n, yw, Bits.mask(32n, 14n)) : Word(32n)}:
  +cyw = Bits.shr_n(32n, 4n, yw)
  +lyw = Word.and(32n, yw, gscale_m4())
  +kw = gscale_key_word(Word.zero(32n), cyw, Word.zero(32n))
  +lw = gscale_local_word(Word.zero(32n), lyw, Word.zero(32n))
  +rKw = gscale_key_y_red(cyw)
  +rLw = gscale_local_y_red(lyw)
  +eKey = gscale_shr20_shl20_m10(cyw)
  +eLoc = gscale_shr8_shl8_m4(lyw)
  +eAbsK = Bits.w_and_absorb(32n, cyw, gscale_m10())
  +eAbsLy = Bits.w_and_absorb(32n, lyw, gscale_m4())
  +eAbsY = Bits.w_and_absorb(32n, yw, gscale_m4())
  +eA = Equal.trans(Word(32n),
    Word.and(32n, Bits.shr_n(32n, 20n, kw), gscale_m10()),
    Word.and(32n, Bits.shr_n(32n, 20n, Bits.shl_n(32n, Word.and(32n, cyw, gscale_m10()), 20n)), gscale_m10()),
    Word.and(32n, cyw, gscale_m10()),
    Equal.cong(Word(32n), Word(32n), x => Word.and(32n, Bits.shr_n(32n, 20n, x), gscale_m10()), kw, Bits.shl_n(32n, Word.and(32n, cyw, gscale_m10()), 20n), rKw),
    Equal.trans(Word(32n),
      Word.and(32n, Bits.shr_n(32n, 20n, Bits.shl_n(32n, Word.and(32n, cyw, gscale_m10()), 20n)), gscale_m10()),
      Word.and(32n, Word.and(32n, cyw, gscale_m10()), gscale_m10()),
      Word.and(32n, cyw, gscale_m10()),
      Equal.cong(Word(32n), Word(32n), x => Word.and(32n, x, gscale_m10()),
        Bits.shr_n(32n, 20n, Bits.shl_n(32n, Word.and(32n, cyw, gscale_m10()), 20n)), Word.and(32n, cyw, gscale_m10()), eKey),
      eAbsK))
  +eB = Equal.trans(Word(32n),
    Word.and(32n, Bits.shr_n(32n, 8n, lw), gscale_m4()),
    Word.and(32n, Bits.shr_n(32n, 8n, Bits.shl_n(32n, Word.and(32n, lyw, gscale_m4()), 8n)), gscale_m4()),
    Word.and(32n, yw, gscale_m4()),
    Equal.cong(Word(32n), Word(32n), x => Word.and(32n, Bits.shr_n(32n, 8n, x), gscale_m4()), lw, Bits.shl_n(32n, Word.and(32n, lyw, gscale_m4()), 8n), rLw),
    Equal.trans(Word(32n),
      Word.and(32n, Bits.shr_n(32n, 8n, Bits.shl_n(32n, Word.and(32n, lyw, gscale_m4()), 8n)), gscale_m4()),
      Word.and(32n, Word.and(32n, lyw, gscale_m4()), gscale_m4()),
      Word.and(32n, yw, gscale_m4()),
      Equal.cong(Word(32n), Word(32n), x => Word.and(32n, x, gscale_m4()),
        Bits.shr_n(32n, 8n, Bits.shl_n(32n, Word.and(32n, lyw, gscale_m4()), 8n)), Word.and(32n, lyw, gscale_m4()), eLoc),
      Equal.trans(Word(32n),
        Word.and(32n, Word.and(32n, lyw, gscale_m4()), gscale_m4()),
        Word.and(32n, lyw, gscale_m4()),
        Word.and(32n, yw, gscale_m4()),
        eAbsLy, eAbsY)))
  +eAstep = Equal.cong(Word(32n), Word(32n),
    x => Word.add(32n, Bits.shl_n(32n, x, 4n), Word.and(32n, Bits.shr_n(32n, 8n, lw), gscale_m4())),
    Word.and(32n, Bits.shr_n(32n, 20n, kw), gscale_m10()), Word.and(32n, cyw, gscale_m10()), eA)
  +eBstep = Equal.cong(Word(32n), Word(32n),
    x => Word.add(32n, Bits.shl_n(32n, Word.and(32n, cyw, gscale_m10()), 4n), x),
    Word.and(32n, Bits.shr_n(32n, 8n, lw), gscale_m4()), Word.and(32n, yw, gscale_m4()), eB)
  Equal.trans(Word(32n),
    gscale_global_y_word(kw, lw),
    Word.add(32n, Bits.shl_n(32n, Word.and(32n, cyw, gscale_m10()), 4n), Word.and(32n, yw, gscale_m4())),
    Word.and(32n, yw, Bits.mask(32n, 14n)),
    Equal.trans(Word(32n),
      gscale_global_y_word(kw, lw),
      Word.add(32n, Bits.shl_n(32n, Word.and(32n, cyw, gscale_m10()), 4n), Word.and(32n, Bits.shr_n(32n, 8n, lw), gscale_m4())),
      Word.add(32n, Bits.shl_n(32n, Word.and(32n, cyw, gscale_m10()), 4n), Word.and(32n, yw, gscale_m4())),
      eAstep, eBstep),
    gscale_global_rt(yw))

def gscale_cw_z_word(+zw: Word(32n)) ->
  {gscale_global_z_word(gscale_key_word(Word.zero(32n), Word.zero(32n), Bits.shr_n(32n, 4n, zw)), gscale_local_word(Word.zero(32n), Word.zero(32n), Word.and(32n, zw, gscale_m4()))) == Word.and(32n, zw, Bits.mask(32n, 14n)) : Word(32n)}:
  +czw = Bits.shr_n(32n, 4n, zw)
  +lzw = Word.and(32n, zw, gscale_m4())
  +kw = gscale_key_word(Word.zero(32n), Word.zero(32n), czw)
  +lw = gscale_local_word(Word.zero(32n), Word.zero(32n), lzw)
  +rKw = gscale_key_z_red(czw)
  +rLw = gscale_local_z_red(lzw)
  +eKey = gscale_shr10_shl10_m10(czw)
  +eLoc = gscale_shr4_shl4_m4(lzw)
  +eAbsK = Bits.w_and_absorb(32n, czw, gscale_m10())
  +eAbsLz = Bits.w_and_absorb(32n, lzw, gscale_m4())
  +eAbsZ = Bits.w_and_absorb(32n, zw, gscale_m4())
  +eA = Equal.trans(Word(32n),
    Word.and(32n, Bits.shr_n(32n, 10n, kw), gscale_m10()),
    Word.and(32n, Bits.shr_n(32n, 10n, Bits.shl_n(32n, Word.and(32n, czw, gscale_m10()), 10n)), gscale_m10()),
    Word.and(32n, czw, gscale_m10()),
    Equal.cong(Word(32n), Word(32n), x => Word.and(32n, Bits.shr_n(32n, 10n, x), gscale_m10()), kw, Bits.shl_n(32n, Word.and(32n, czw, gscale_m10()), 10n), rKw),
    Equal.trans(Word(32n),
      Word.and(32n, Bits.shr_n(32n, 10n, Bits.shl_n(32n, Word.and(32n, czw, gscale_m10()), 10n)), gscale_m10()),
      Word.and(32n, Word.and(32n, czw, gscale_m10()), gscale_m10()),
      Word.and(32n, czw, gscale_m10()),
      Equal.cong(Word(32n), Word(32n), x => Word.and(32n, x, gscale_m10()),
        Bits.shr_n(32n, 10n, Bits.shl_n(32n, Word.and(32n, czw, gscale_m10()), 10n)), Word.and(32n, czw, gscale_m10()), eKey),
      eAbsK))
  +eB = Equal.trans(Word(32n),
    Word.and(32n, Bits.shr_n(32n, 4n, lw), gscale_m4()),
    Word.and(32n, Bits.shr_n(32n, 4n, Bits.shl_n(32n, Word.and(32n, lzw, gscale_m4()), 4n)), gscale_m4()),
    Word.and(32n, zw, gscale_m4()),
    Equal.cong(Word(32n), Word(32n), x => Word.and(32n, Bits.shr_n(32n, 4n, x), gscale_m4()), lw, Bits.shl_n(32n, Word.and(32n, lzw, gscale_m4()), 4n), rLw),
    Equal.trans(Word(32n),
      Word.and(32n, Bits.shr_n(32n, 4n, Bits.shl_n(32n, Word.and(32n, lzw, gscale_m4()), 4n)), gscale_m4()),
      Word.and(32n, Word.and(32n, lzw, gscale_m4()), gscale_m4()),
      Word.and(32n, zw, gscale_m4()),
      Equal.cong(Word(32n), Word(32n), x => Word.and(32n, x, gscale_m4()),
        Bits.shr_n(32n, 4n, Bits.shl_n(32n, Word.and(32n, lzw, gscale_m4()), 4n)), Word.and(32n, lzw, gscale_m4()), eLoc),
      Equal.trans(Word(32n),
        Word.and(32n, Word.and(32n, lzw, gscale_m4()), gscale_m4()),
        Word.and(32n, lzw, gscale_m4()),
        Word.and(32n, zw, gscale_m4()),
        eAbsLz, eAbsZ)))
  +eAstep = Equal.cong(Word(32n), Word(32n),
    x => Word.add(32n, Bits.shl_n(32n, x, 4n), Word.and(32n, Bits.shr_n(32n, 4n, lw), gscale_m4())),
    Word.and(32n, Bits.shr_n(32n, 10n, kw), gscale_m10()), Word.and(32n, czw, gscale_m10()), eA)
  +eBstep = Equal.cong(Word(32n), Word(32n),
    x => Word.add(32n, Bits.shl_n(32n, Word.and(32n, czw, gscale_m10()), 4n), x),
    Word.and(32n, Bits.shr_n(32n, 4n, lw), gscale_m4()), Word.and(32n, zw, gscale_m4()), eB)
  Equal.trans(Word(32n),
    gscale_global_z_word(kw, lw),
    Word.add(32n, Bits.shl_n(32n, Word.and(32n, czw, gscale_m10()), 4n), Word.and(32n, zw, gscale_m4())),
    Word.and(32n, zw, Bits.mask(32n, 14n)),
    Equal.trans(Word(32n),
      gscale_global_z_word(kw, lw),
      Word.add(32n, Bits.shl_n(32n, Word.and(32n, czw, gscale_m10()), 4n), Word.and(32n, Bits.shr_n(32n, 4n, lw), gscale_m4())),
      Word.add(32n, Bits.shl_n(32n, Word.and(32n, czw, gscale_m10()), 4n), Word.and(32n, zw, gscale_m4())),
      eAstep, eBstep),
    gscale_global_rt(zw))

def gscale_cw_x_split(+x: U32, +y: U32, +z: U32) ->
  {Cw.cw_global_x(Cw.cw_key(Cw.cw_chunk_of(x), Cw.cw_chunk_of(y), Cw.cw_chunk_of(z)), Cw.cw_local(Cw.cw_local_of(x), Cw.cw_local_of(y), Cw.cw_local_of(z))) == U32.and(x, 16383) : U32}:
  match x:
    case U32{xw}:
      match y:
        case U32{yw}:
          match z:
            case U32{zw}:
              Equal.cong(Word(32n), U32, w => U32{w},
                gscale_global_x_word(gscale_key_word(Bits.shr_n(32n, 4n, xw), Bits.shr_n(32n, 4n, yw), Bits.shr_n(32n, 4n, zw)), gscale_local_word(Word.and(32n, xw, gscale_m4()), Word.and(32n, yw, gscale_m4()), Word.and(32n, zw, gscale_m4()))),
                Word.and(32n, xw, Bits.mask(32n, 14n)),
                gscale_cw_x_word(xw, yw, zw))

def gscale_cw_y_split(+y: U32) ->
  {Cw.cw_global_y(Cw.cw_key(0, Cw.cw_chunk_of(y), 0), Cw.cw_local(0, Cw.cw_local_of(y), 0)) == U32.and(y, 16383) : U32}:
  match y:
    case U32{yw}:
      Equal.cong(Word(32n), U32, w => U32{w},
        gscale_global_y_word(gscale_key_word(Word.zero(32n), Bits.shr_n(32n, 4n, yw), Word.zero(32n)), gscale_local_word(Word.zero(32n), Word.and(32n, yw, gscale_m4()), Word.zero(32n))),
        Word.and(32n, yw, Bits.mask(32n, 14n)),
        gscale_cw_y_word(yw))

def gscale_cw_z_split(+z: U32) ->
  {Cw.cw_global_z(Cw.cw_key(0, 0, Cw.cw_chunk_of(z)), Cw.cw_local(0, 0, Cw.cw_local_of(z))) == U32.and(z, 16383) : U32}:
  match z:
    case U32{zw}:
      Equal.cong(Word(32n), U32, w => U32{w},
        gscale_global_z_word(gscale_key_word(Word.zero(32n), Word.zero(32n), Bits.shr_n(32n, 4n, zw)), gscale_local_word(Word.zero(32n), Word.zero(32n), Word.and(32n, zw, gscale_m4()))),
        Word.and(32n, zw, Bits.mask(32n, 14n)),
        gscale_cw_z_word(zw))

def gscale_cw_key_split(+k: U32) ->
  {Cw.cw_key(Cw.cw_key_x(k), Cw.cw_key_y(k), Cw.cw_key_z(k)) == U32.and(k, 1073741823) : U32}:
  match k:
    case U32{kw}:
      Equal.cong(Word(32n), U32, w => U32{w},
        gscale_key_word(gscale_kx(kw), gscale_ky(kw), gscale_kz(kw)),
        Word.and(32n, kw, Bits.mask(32n, 30n)),
        gscale_kmodel_rt(kw))

def gscale_cw_local_split(+l: U32) ->
  {Cw.cw_local(Cw.cw_local_x(l), Cw.cw_local_y(l), Cw.cw_local_z(l)) == U32.and(l, 4095) : U32}:
  match l:
    case U32{lw}:
      Equal.cong(Word(32n), U32, w => U32{w},
        gscale_local_word(gscale_lx(lw), gscale_ly(lw), gscale_lz(lw)),
        Word.and(32n, lw, Bits.mask(32n, 12n)),
        gscale_lmodel_rt(lw))
