import Base
import ./nat.bend as NatL

# ============================================================================
# Dirtyn (SCALE.md step 5 / PLAN gap G-scale-2) -- a size-parameterised row mask.
#
# `Dirty.Mask` (src/dirty.bend) is exactly 64 `y` rows: two `U32` words, bit
# `y & 31` of `lo`/`hi`. A moving window (SCALE.md step 5, PLAN `G-scale-2`)
# needs a mask over `2^n` rows, not 64. This module is that mask, additively:
#
#   * the mask is a `Word(w)` bit vector, one bit per `y` row, `w = 2^n`
#     (`dwin_width`); the current 64-row world is the `n = 6`, `w = 64` instance;
#   * `dwin_zero`, `dwin_is_dirty`, `dwin_or_y`, `dwin_mark_if`, `dwin_mark_wake`
#     are `Dirty`'s operations re-expressed for the wider word;
#   * the `mark_wake` `y-1` / `y` / `y+1` reach invariant is stated and proven
#     (`dwin_mark_wake_self` / `_up` / `_down`).
#
# Nothing here touches `src/dirty.bend` or the live 64-row path: the module is a
# model. `w` is an arbitrary `Nat` here (the proofs are structural in the width),
# and `2^n` is the width we instantiate; `dwin_width_n6` pins `n = 6` to 64 and
# T90-T94 witness the operations plus the agreement with `Dirty` on 64 rows.
#
# Row indices are `Nat`; the in-range hypothesis is `{Nat.is_lt(y, w) == True}`,
# which reduces definitionally with the width (so the recursive proofs below can
# pass it straight through) -- no `Bool` reflection is needed.
# ============================================================================

# The mask is a `Word(w)`, one bit per row (LSB = row 0).

def dwin_width(n: Nat) -> Nat:
  match n:
    case 0n:
      1n
    case 1n+p:
      Nat.double(dwin_width(p))

# The zero mask: no dirty rows.
def dwin_zero(w: Nat) -> Word(w):
  Word.zero(w)

# The single-row mask `{y}`: bit `y` set, all others clear.
def dwin_bit(w: Nat, y: Nat) -> Word(w):
  match w:
    case 0n:
      WNil{}
    case 1n+p:
      match y:
        case 0n:
          WCon{True{}, Word.zero(p)}
        case 1n+q:
          WCon{False{}, dwin_bit(p, q)}

# Is row `y` dirty? (the bit test)
def dwin_get(w: Nat, m: Word(w), y: Nat) -> Bool:
  match w:
    case 0n:
      False{}
    case 1n+p:
      match m:
        case WCon{h, t}:
          match y:
            case 0n:
              h
            case 1n+q:
              dwin_get(p, t, q)

def dwin_is_dirty(+w: Nat, +m: Word(w), +y: Nat) -> Bool:
  dwin_get(w, m, y)

# `or_y`: mark row `y` (the set union with `{y}`).
def dwin_or_y(+w: Nat, m: Word(w), y: Nat) -> Word(w):
  Word.or(w, m, dwin_bit(w, y))

# `mark_if`: mark row `y` only when `b` holds (the one-time prime).
def dwin_mark_if(+w: Nat, +m: Word(w), y: Nat, b: Bool) -> Word(w):
  Bool.pick(Word(w), b, dwin_or_y(w, m, y), m)

# The two wrap neighbours of row `y` in a `w`-row window. `up`/`down` are passed
# explicitly to `dwin_mark_wake` so the reach law does not depend on the wrap
# convention; these are the `mod w` neighbours the live path would use.
def dwin_up(w: Nat, y: Nat) -> Nat:
  Nat.mod(Nat.add(y, 1n), w)

def dwin_down(+w: Nat, y: Nat) -> Nat:
  Nat.mod(Nat.add(y, Nat.sub(w, 1n)), w)

# `mark_wake`: the three rows a wake source at row `y` can reach (`y`, `y+1`,
# `y-1`). `Dirty.mark_wake` uses `U32.and(..., 63)` to wrap; here the caller
# supplies `up`/`down` (the wrap neighbours), so the reach invariant is stated
# for the three rows themselves.
def dwin_mark_wake(+w: Nat, +m: Word(w), y: Nat, up: Nat, down: Nat) -> Word(w):
  dwin_or_y(w, dwin_or_y(w, dwin_or_y(w, m, y), up), down)

def dwin_mark_wake_auto(+w: Nat, m: Word(w), +y: Nat) -> Word(w):
  dwin_mark_wake(w, m, y, dwin_up(w, y), dwin_down(w, y))

# ------------------------------------------------------------------ lemmas
# `Bool.or` with a `True` on either side.
def dwin_or_true_r(a: Bool) -> {Bool.or(a, True{}) == True{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

def dwin_or_true_l(a: Bool) -> {Bool.or(True{}, a) == True{} : Bool}:
  match a:
    case False{}:
      {==}
    case True{}:
      {==}

# The bit test distributes over `or` (row membership is a disjunction).
def dwin_get_or(+w: Nat, +a: Word(w), +b: Word(w), +y: Nat)
  -> {dwin_get(w, Word.or(w, a, b), y) == Bool.or(dwin_get(w, a, y), dwin_get(w, b, y)) : Bool}:
  match w:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          match y:
            case 0n:
              {==}
            case 1n+q:
              dwin_get_or(p, at, bt, q)

# A single-row mask contains its own row. The in-range hypothesis is needed
# because a bit shifted past the width is lost; `Nat.is_lt(y, w)` reduces with
# the width, so the recursive call consumes `h` unchanged.
def dwin_get_bit_self(w: Nat, +y: Nat, h: {Nat.is_lt(y, w) == True{} : Bool})
  -> {dwin_get(w, dwin_bit(w, y), y) == True{} : Bool}:
  match w:
    case 0n:
      Equal.trans(Bool,
        False{}, Nat.is_lt(y, 0n), True{},
        Equal.sym(Bool, Nat.is_lt(y, 0n), False{}, NatL.n_not_lt_zero(y)),
        h)
    case 1n+p:
      match y:
        case 0n:
          {==}
        case 1n+q:
          dwin_get_bit_self(p, q, h)

# Zero has no dirty row.
def dwin_zero_get(w: Nat, +y: Nat)
  -> {dwin_get(w, dwin_zero(w), y) == False{} : Bool}:
  match w:
    case 0n:
      {==}
    case 1n+p:
      match y:
        case 0n:
          {==}
        case 1n+q:
          dwin_zero_get(p, q)

# `or_y` marks its own row.
def dwin_get_or_y_self(+w: Nat, +m: Word(w), +y: Nat, h: {Nat.is_lt(y, w) == True{} : Bool})
  -> {dwin_get(w, dwin_or_y(w, m, y), y) == True{} : Bool}:
  Equal.trans(Bool,
    dwin_get(w, dwin_or_y(w, m, y), y),
    Bool.or(dwin_get(w, m, y), dwin_get(w, dwin_bit(w, y), y)),
    True{},
    dwin_get_or(w, m, dwin_bit(w, y), y),
    Equal.trans(Bool,
      Bool.or(dwin_get(w, m, y), dwin_get(w, dwin_bit(w, y), y)),
      Bool.or(dwin_get(w, m, y), True{}),
      True{},
      Equal.cong(Bool, Bool, b => Bool.or(dwin_get(w, m, y), b),
        dwin_get(w, dwin_bit(w, y), y), True{}, dwin_get_bit_self(w, y, h)),
      dwin_or_true_r(dwin_get(w, m, y))))

# `or_y` is monotone: a dirty row stays dirty (the set only grows).
def dwin_get_or_y_mono(+w: Nat, +m: Word(w), +y: Nat, +k: Nat,
    h: {dwin_get(w, m, k) == True{} : Bool})
  -> {dwin_get(w, dwin_or_y(w, m, y), k) == True{} : Bool}:
  Equal.trans(Bool,
    dwin_get(w, dwin_or_y(w, m, y), k),
    Bool.or(dwin_get(w, m, k), dwin_get(w, dwin_bit(w, y), k)),
    True{},
    dwin_get_or(w, m, dwin_bit(w, y), k),
    Equal.trans(Bool,
      Bool.or(dwin_get(w, m, k), dwin_get(w, dwin_bit(w, y), k)),
      Bool.or(True{}, dwin_get(w, dwin_bit(w, y), k)),
      True{},
      Equal.cong(Bool, Bool, b => Bool.or(b, dwin_get(w, dwin_bit(w, y), k)),
        dwin_get(w, m, k), True{}, h),
      dwin_or_true_l(dwin_get(w, dwin_bit(w, y), k))))
# ------------------------------------------------------------------ mark_wake reach
# `mark_wake` dirties the three rows a wake source at `y` can reach: `y` itself,
# and the wrap neighbours `up` / `down` (supplied by the caller; `dwin_up` /
# `dwin_down` are the `mod w` ones). Each proof only needs the single-bit law:
# later `or_y`s add bits on top, and `or(True, _) = True`, so an earlier-marked
# row stays dirty.

def dwin_mark_wake_self(+w: Nat, +m: Word(w), +y: Nat, +up: Nat, +down: Nat,
    h: {Nat.is_lt(y, w) == True{} : Bool})
  -> {dwin_get(w, dwin_mark_wake(w, m, y, up, down), y) == True{} : Bool}:
  +m1 = dwin_or_y(w, m, y)
  +m2 = dwin_or_y(w, m1, up)
  +m3 = dwin_or_y(w, m2, down)
  +inner = Equal.trans(Bool,
    dwin_get(w, m2, y),
    Bool.or(dwin_get(w, m1, y), dwin_get(w, dwin_bit(w, up), y)),
    True{},
    dwin_get_or(w, m1, dwin_bit(w, up), y),
    Equal.trans(Bool,
      Bool.or(dwin_get(w, m1, y), dwin_get(w, dwin_bit(w, up), y)),
      Bool.or(True{}, dwin_get(w, dwin_bit(w, up), y)),
      True{},
      Equal.cong(Bool, Bool, b => Bool.or(b, dwin_get(w, dwin_bit(w, up), y)),
        dwin_get(w, m1, y), True{}, dwin_get_or_y_self(w, m, y, h)),
      dwin_or_true_l(dwin_get(w, dwin_bit(w, up), y))))
  Equal.trans(Bool,
    dwin_get(w, m3, y),
    Bool.or(dwin_get(w, m2, y), dwin_get(w, dwin_bit(w, down), y)),
    True{},
    dwin_get_or(w, m2, dwin_bit(w, down), y),
    Equal.trans(Bool,
      Bool.or(dwin_get(w, m2, y), dwin_get(w, dwin_bit(w, down), y)),
      Bool.or(True{}, dwin_get(w, dwin_bit(w, down), y)),
      True{},
      Equal.cong(Bool, Bool, b => Bool.or(b, dwin_get(w, dwin_bit(w, down), y)),
        dwin_get(w, m2, y), True{}, inner),
      dwin_or_true_l(dwin_get(w, dwin_bit(w, down), y))))

def dwin_mark_wake_up(+w: Nat, +m: Word(w), +y: Nat, +up: Nat, +down: Nat,
    h: {Nat.is_lt(up, w) == True{} : Bool})
  -> {dwin_get(w, dwin_mark_wake(w, m, y, up, down), up) == True{} : Bool}:
  +m1 = dwin_or_y(w, m, y)
  +m2 = dwin_or_y(w, m1, up)
  +m3 = dwin_or_y(w, m2, down)
  +inner = Equal.trans(Bool,
    dwin_get(w, m2, up),
    Bool.or(dwin_get(w, m1, up), dwin_get(w, dwin_bit(w, up), up)),
    True{},
    dwin_get_or(w, m1, dwin_bit(w, up), up),
    Equal.trans(Bool,
      Bool.or(dwin_get(w, m1, up), dwin_get(w, dwin_bit(w, up), up)),
      Bool.or(dwin_get(w, m1, up), True{}),
      True{},
      Equal.cong(Bool, Bool, b => Bool.or(dwin_get(w, m1, up), b),
        dwin_get(w, dwin_bit(w, up), up), True{}, dwin_get_bit_self(w, up, h)),
      dwin_or_true_r(dwin_get(w, m1, up))))
  Equal.trans(Bool,
    dwin_get(w, m3, up),
    Bool.or(dwin_get(w, m2, up), dwin_get(w, dwin_bit(w, down), up)),
    True{},
    dwin_get_or(w, m2, dwin_bit(w, down), up),
    Equal.trans(Bool,
      Bool.or(dwin_get(w, m2, up), dwin_get(w, dwin_bit(w, down), up)),
      Bool.or(True{}, dwin_get(w, dwin_bit(w, down), up)),
      True{},
      Equal.cong(Bool, Bool, b => Bool.or(b, dwin_get(w, dwin_bit(w, down), up)),
        dwin_get(w, m2, up), True{}, inner),
      dwin_or_true_l(dwin_get(w, dwin_bit(w, down), up))))

def dwin_mark_wake_down(+w: Nat, +m: Word(w), +y: Nat, +up: Nat, +down: Nat,
    h: {Nat.is_lt(down, w) == True{} : Bool})
  -> {dwin_get(w, dwin_mark_wake(w, m, y, up, down), down) == True{} : Bool}:
  +m1 = dwin_or_y(w, m, y)
  +m2 = dwin_or_y(w, m1, up)
  +m3 = dwin_or_y(w, m2, down)
  Equal.trans(Bool,
    dwin_get(w, m3, down),
    Bool.or(dwin_get(w, m2, down), dwin_get(w, dwin_bit(w, down), down)),
    True{},
    dwin_get_or(w, m2, dwin_bit(w, down), down),
    Equal.trans(Bool,
      Bool.or(dwin_get(w, m2, down), dwin_get(w, dwin_bit(w, down), down)),
      Bool.or(dwin_get(w, m2, down), True{}),
      True{},
      Equal.cong(Bool, Bool, b => Bool.or(dwin_get(w, m2, down), b),
        dwin_get(w, dwin_bit(w, down), down), True{}, dwin_get_bit_self(w, down, h)),
      dwin_or_true_r(dwin_get(w, m2, down))))

# ------------------------------------------------------------------ wrap range
# SCALE.md step 5 / PLAN `G-scale-2` (the open wrap-range lemma). The `mark_wake`
# reach laws above take `{Nat.is_lt(up, w) == True}` / `{Nat.is_lt(down, w) ==
# True}` as hypotheses; these two lemmas discharge them for the `mod`-based wrap
# `dwin_up` / `dwin_down`, so `dwin_mark_wake_auto` is usable without a caller
# side condition. The bound is `NatL.n_mod_lt` (developed in `src/nat.bend`).
def dwin_up_lt(w: Nat, +y: Nat, h: {Nat.is_lt(0n, w) == True{} : Bool})
  -> {Nat.is_lt(dwin_up(w, y), w) == True{} : Bool}:
  match w:
    case 0n:
      Equal.cong(Bool, Bool,
        z => Bool.pick(Bool, z, True{}, Nat.is_lt(dwin_up(0n, y), 0n)), False{}, True{}, h)
    case 1n+b:
      NatL.n_mod_lt(Nat.add(y, 1n), b)

def dwin_down_lt(w: Nat, +y: Nat, h: {Nat.is_lt(0n, w) == True{} : Bool})
  -> {Nat.is_lt(dwin_down(w, y), w) == True{} : Bool}:
  match w:
    case 0n:
      Equal.cong(Bool, Bool,
        z => Bool.pick(Bool, z, True{}, Nat.is_lt(dwin_down(0n, y), 0n)), False{}, True{}, h)
    case 1n+b:
      +bb = b
      NatL.n_mod_lt(Nat.add(y, Nat.sub(Nat.add(1n, bb), 1n)), bb)
