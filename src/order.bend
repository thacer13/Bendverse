import Base

def cmp_fin_total(+t: Cmp, +ab: Bool, +bb: Bool) -> {Bool.or(Bool.or(Cmp.is_lt(Word.cmp.fin(ab, bb, t)), Cmp.is_gt(Word.cmp.fin(ab, bb, t))), Cmp.is_eq(Word.cmp.fin(ab, bb, t))) == True{} : Bool}:
  match t:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      match ab bb:
        case False{} False{}: {==}
        case False{} True{}: {==}
        case True{} False{}: {==}
        case True{} True{}: {==}

def cmp32_total(+x: Word(32n), +y: Word(32n)) -> {Bool.or(Bool.or(Cmp.is_lt(Word.cmp(32n, x, y)), Cmp.is_gt(Word.cmp(32n, x, y))), Cmp.is_eq(Word.cmp(32n, x, y))) == True{} : Bool}:
  match x y:
    case WCon{+ah, +at} WCon{+bh, +bt}:
      cmp_fin_total(Word.cmp(31n, at, bt), ah, bh)

def u32_cmp_total(+a: U32, +b: U32) -> {Bool.or(Bool.or(U32.is_lt(a, b), U32.is_gt(a, b)), U32.is_eq(a, b)) == True{} : Bool}:
  match a:
    case U32{x}:
      match b:
        case U32{y}:
          cmp32_total(x, y)
