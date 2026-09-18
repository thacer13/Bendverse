import Base

# Word.cmp reflection.
#
# Base exposes no way to turn a `Cmp`-valued test back into a proposition: a
# `match` on an abstract `U32`/`Word` gets stuck in the wildcard branch and
# refines the scrutinee only to a partial constructor, so a `Bool` result cannot
# be reflected. These lemmas recover exactly that, and are the unlock recorded in
# HISTORY.md A.37 for guarding the crush sites (`G9`) and enumerating write sites
# (`G10`).
#
# `b_cmp_eq` is the `Bool` base case; the two `Word.cmp.fin` lemmas split on the
# tail comparison (LT/GT are impossible and are discharged by transporting a
# contradiction along `Equal.cong` with a `Bool.pick` motive); `w_cmp_eq` is the
# structural induction over the bit prefix. Only then does `u32_cmp_eq` follow.

def b_cmp_eq(a: Bool, b: Bool, h: {Cmp.is_eq(Bool.cmp(a, b)) == True{} : Bool}) -> {a == b : Bool}:
  match a b:
    case False{} False{}:
      {==}
    case False{} True{}:
      h
    case True{} False{}:
      Equal.sym(Bool, False{}, True{}, h)
    case True{} True{}:
      {==}

def w_cmp_fin_eq_bits(+t: Cmp, +ab: Bool, +bb: Bool, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) -> {ab == bb : Bool}:
  match t:
    case LT{}:
      Equal.cong(Bool, Bool, x => Bool.pick(Bool, x, bb, ab), False{}, True{}, h)
    case EQ{}:
      b_cmp_eq(ab, bb, h)
    case GT{}:
      Equal.cong(Bool, Bool, x => Bool.pick(Bool, x, bb, ab), False{}, True{}, h)

def w_cmp_fin_eq_t(+t: Cmp, +ab: Bool, +bb: Bool, h: {Cmp.is_eq(Word.cmp.fin(ab, bb, t)) == True{} : Bool}) -> {Cmp.is_eq(t) == True{} : Bool}:
  match t:
    case LT{}:
      h
    case EQ{}:
      {==}
    case GT{}:
      h

def w_cmp_eq(n: Nat, a: Word(n), b: Word(n), +h: {Cmp.is_eq(Word.cmp(n, a, b)) == True{} : Bool}) -> {a == b : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+ +p:
      match a b:
        case WCon{+ab, +at} WCon{+bb, +bt}:
          +eab = w_cmp_fin_eq_bits(Word.cmp(p, at, bt), ab, bb, h)
          +et = w_cmp_fin_eq_t(Word.cmp(p, at, bt), ab, bb, h)
          +etl = w_cmp_eq(p, at, bt, et)
          Equal.trans(Word(1n+p),
            WCon{ab, at},
            WCon{bb, at},
            WCon{bb, bt},
            Equal.cong(Bool, Word(1n+p), x => WCon{x, at}, ab, bb, eab),
            Equal.cong(Word(p), Word(1n+p), y => WCon{bb, y}, at, bt, etl))

def u32_cmp_eq(a: U32, b: U32, h: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  match a:
    case U32{x}:
      match b:
        case U32{y}:
          +e = w_cmp_eq(32n, x, y, h)
          Equal.cong(Word(32n), U32, z => U32{z}, x, y, e)
