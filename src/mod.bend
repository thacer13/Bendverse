import Base
import ./bits.bend as Bits

def and_mask0(n: Nat, w: Word(n)) -> {Word.and(n, w, Bits.mask(n, 0n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n++p:
      Equal.trans(Word(1n+p),
        Word.and(1n+p, w, Bits.mask(1n+p, 0n)),
        Word.and(1n+p, w, Word.zero(1n+p)),
        Word.zero(1n+p),
        Equal.cong(Word(1n+p), Word(1n+p), m => Word.and(1n+p, w, m),
          Bits.mask(1n+p, 0n), Word.zero(1n+p), {==}),
        Bits.w_and_zero(1n+p, w))

def lowadc(+n: Nat, +k: Nat, +a: Word(n), +b: Word(n), +c: Bool) -> {Word.and(n, Word.adc(n, a, b, False{}, c), Bits.mask(n, k)) == Word.and(n, Word.adc(n, Word.and(n, a, Bits.mask(n, k)), Word.and(n, b, Bits.mask(n, k)), False{}, c), Bits.mask(n, k)) : Word(n)}:
  match n:
    case 0n:
      match k:
        case 0n:
          match a b:
            case WNil{} WNil{}:
              {==}
        case 1n++q:
          match a b:
            case WNil{} WNil{}:
              {==}
    case 1n++p:
      match k:
        case 0n:
          Equal.trans(Word(1n+p),
            Word.and(1n+p, Word.adc(1n+p, a, b, False{}, c), Bits.mask(1n+p, 0n)),
            Word.zero(1n+p),
            Word.and(1n+p, Word.adc(1n+p, Word.and(1n+p, a, Bits.mask(1n+p, 0n)), Word.and(1n+p, b, Bits.mask(1n+p, 0n)), False{}, c), Bits.mask(1n+p, 0n)),
            and_mask0(1n+p, Word.adc(1n+p, a, b, False{}, c)),
            Equal.sym(Word(1n+p),
              Word.and(1n+p, Word.adc(1n+p, Word.and(1n+p, a, Bits.mask(1n+p, 0n)), Word.and(1n+p, b, Bits.mask(1n+p, 0n)), False{}, c), Bits.mask(1n+p, 0n)),
              Word.zero(1n+p),
              and_mask0(1n+p, Word.adc(1n+p, Word.and(1n+p, a, Bits.mask(1n+p, 0n)), Word.and(1n+p, b, Bits.mask(1n+p, 0n)), False{}, c))))
        case 1n++q:
          match a b c:
            case WCon{False{}, at} WCon{False{}, bt} False{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
                Word.and(p, Word.adc(p, at, bt, False{}, False{}), Bits.mask(p, q)),
                Word.and(p, Word.adc(p, Word.and(p, at, Bits.mask(p, q)), Word.and(p, bt, Bits.mask(p, q)), False{}, False{}), Bits.mask(p, q)),
                lowadc(p, q, at, bt, False{}))
            case WCon{False{}, at} WCon{False{}, bt} True{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
                Word.and(p, Word.adc(p, at, bt, False{}, False{}), Bits.mask(p, q)),
                Word.and(p, Word.adc(p, Word.and(p, at, Bits.mask(p, q)), Word.and(p, bt, Bits.mask(p, q)), False{}, False{}), Bits.mask(p, q)),
                lowadc(p, q, at, bt, False{}))
            case WCon{False{}, at} WCon{True{}, bt} False{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
                Word.and(p, Word.adc(p, at, bt, False{}, False{}), Bits.mask(p, q)),
                Word.and(p, Word.adc(p, Word.and(p, at, Bits.mask(p, q)), Word.and(p, bt, Bits.mask(p, q)), False{}, False{}), Bits.mask(p, q)),
                lowadc(p, q, at, bt, False{}))
            case WCon{False{}, at} WCon{True{}, bt} True{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
                Word.and(p, Word.adc(p, at, bt, False{}, True{}), Bits.mask(p, q)),
                Word.and(p, Word.adc(p, Word.and(p, at, Bits.mask(p, q)), Word.and(p, bt, Bits.mask(p, q)), False{}, True{}), Bits.mask(p, q)),
                lowadc(p, q, at, bt, True{}))
            case WCon{True{}, at} WCon{False{}, bt} False{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
                Word.and(p, Word.adc(p, at, bt, False{}, False{}), Bits.mask(p, q)),
                Word.and(p, Word.adc(p, Word.and(p, at, Bits.mask(p, q)), Word.and(p, bt, Bits.mask(p, q)), False{}, False{}), Bits.mask(p, q)),
                lowadc(p, q, at, bt, False{}))
            case WCon{True{}, at} WCon{False{}, bt} True{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
                Word.and(p, Word.adc(p, at, bt, False{}, True{}), Bits.mask(p, q)),
                Word.and(p, Word.adc(p, Word.and(p, at, Bits.mask(p, q)), Word.and(p, bt, Bits.mask(p, q)), False{}, True{}), Bits.mask(p, q)),
                lowadc(p, q, at, bt, True{}))
            case WCon{True{}, at} WCon{True{}, bt} False{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
                Word.and(p, Word.adc(p, at, bt, False{}, True{}), Bits.mask(p, q)),
                Word.and(p, Word.adc(p, Word.and(p, at, Bits.mask(p, q)), Word.and(p, bt, Bits.mask(p, q)), False{}, True{}), Bits.mask(p, q)),
                lowadc(p, q, at, bt, True{}))
            case WCon{True{}, at} WCon{True{}, bt} True{}:
              Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
                Word.and(p, Word.adc(p, at, bt, False{}, True{}), Bits.mask(p, q)),
                Word.and(p, Word.adc(p, Word.and(p, at, Bits.mask(p, q)), Word.and(p, bt, Bits.mask(p, q)), False{}, True{}), Bits.mask(p, q)),
                lowadc(p, q, at, bt, True{}))

def ones(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n++p:
      WCon{True{}, ones(p)}

def one(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n++p:
      WCon{True{}, Word.zero(p)}

def add_zero(n: Nat, a: Word(n)) -> {Word.add(n, a, Word.zero(n)) == a : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n++p:
      match a:
        case WCon{False{}, +at}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.adc(p, at, Word.zero(p), False{}, False{}),
            at,
            add_zero(p, at))
        case WCon{True{}, +at}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
            Word.adc(p, at, Word.zero(p), False{}, False{}),
            at,
            add_zero(p, at))

def addc_ones_true(n: Nat, a: Word(n)) -> {Word.adc(n, a, ones(n), False{}, True{}) == a : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n++p:
      match a:
        case WCon{False{}, +at}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
            Word.adc(p, at, ones(p), False{}, True{}),
            at,
            addc_ones_true(p, at))
        case WCon{True{}, +at}:
          Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
            Word.adc(p, at, ones(p), False{}, True{}),
            at,
            addc_ones_true(p, at))

def add_one_eq(n: Nat, a: Word(n)) -> {Word.add(n, a, one(n)) == Word.adc(n, a, Word.zero(n), False{}, True{}) : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n++p:
      match a:
        case WCon{False{}, +at}: {==}
        case WCon{True{}, +at}: {==}

def add_one_ones(n: Nat, a: Word(n)) -> {Word.add(n, Word.add(n, a, one(n)), ones(n)) == a : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n++p:
      match a:
        case WCon{False{}, +at}:
          +e1 = add_zero(p, at)
          +outer0 = Word.adc(p, Word.add(p, at, Word.zero(p)), ones(p), False{}, True{})
          +outer1 = Word.adc(p, at, ones(p), False{}, True{})
          +e2 = Equal.cong(Word(p), Word(p), x => Word.adc(p, x, ones(p), False{}, True{}), Word.add(p, at, Word.zero(p)), at, e1)
          +e3 = addc_ones_true(p, at)
          Equal.trans(Word(1n+p),
            Word.add(1n+p, Word.add(1n+p, WCon{False{}, at}, one(1n+p)), ones(1n+p)),
            WCon{False{}, outer0},
            WCon{False{}, at},
            {==},
            Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
              outer0, at,
              Equal.trans(Word(p), outer0, outer1, at, e2, e3)))
        case WCon{True{}, +at}:
          +inner0 = Word.adc(p, at, Word.zero(p), False{}, True{})
          +inner1 = Word.add(p, at, one(p))
          +e1 = Equal.sym(Word(p), inner1, inner0, add_one_eq(p, at))
          +tail0 = Word.add(p, inner0, ones(p))
          +tail1 = Word.add(p, inner1, ones(p))
          +e2 = Equal.cong(Word(p), Word(p), x => Word.add(p, x, ones(p)), inner0, inner1, e1)
          +e3 = add_one_ones(p, at)
          Equal.trans(Word(1n+p),
            Word.add(1n+p, Word.add(1n+p, WCon{True{}, at}, one(1n+p)), ones(1n+p)),
            WCon{True{}, tail0},
            WCon{True{}, at},
            {==},
            Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
              tail0, at,
              Equal.trans(Word(p), tail0, tail1, at, e2, e3)))

def add_ones_one(n: Nat, a: Word(n)) -> {Word.add(n, Word.add(n, a, ones(n)), one(n)) == a : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n++p:
      match a:
        case WCon{False{}, +at}:
          +dec = Word.add(p, at, ones(p))
          +inner0 = Word.adc(p, dec, Word.zero(p), False{}, True{})
          +inner1 = Word.add(p, dec, one(p))
          +e1 = Equal.sym(Word(p), inner1, inner0, add_one_eq(p, dec))
          +e2 = add_ones_one(p, at)
          Equal.trans(Word(1n+p),
            Word.add(1n+p, Word.add(1n+p, WCon{False{}, at}, ones(1n+p)), one(1n+p)),
            WCon{False{}, inner0},
            WCon{False{}, at},
            {==},
            Equal.cong(Word(p), Word(1n+p), t => WCon{False{}, t},
              inner0, at,
              Equal.trans(Word(p), inner0, inner1, at, e1, e2)))
        case WCon{True{}, +at}:
          +inner = Word.adc(p, at, ones(p), False{}, True{})
          +e1 = addc_ones_true(p, at)
          +tail0 = Word.add(p, inner, Word.zero(p))
          +tail1 = Word.add(p, at, Word.zero(p))
          +e2 = Equal.cong(Word(p), Word(p), x => Word.add(p, x, Word.zero(p)), inner, at, e1)
          +e3 = add_zero(p, at)
          Equal.trans(Word(1n+p),
            Word.add(1n+p, Word.add(1n+p, WCon{True{}, at}, ones(1n+p)), one(1n+p)),
            WCon{True{}, tail0},
            WCon{True{}, at},
            {==},
            Equal.cong(Word(p), Word(1n+p), t => WCon{True{}, t},
              tail0, at,
              Equal.trans(Word(p), tail0, tail1, at, e2, e3)))

def m6() -> Word(32n):
  Bits.mask(32n, 6n)

def low_mask_absorb_w(+x: Word(32n), +y: Word(32n)) -> {Word.and(32n, Word.adc(32n, Word.and(32n, x, m6()), y, False{}, False{}), m6()) == Word.and(32n, Word.adc(32n, x, y, False{}, False{}), m6()) : Word(32n)}:
  +mx = Word.and(32n, x, m6())
  +my = Word.and(32n, y, m6())
  +e1 = lowadc(32n, 6n, x, y, False{})
  +e2 = lowadc(32n, 6n, mx, y, False{})
  +e3 = Equal.cong(Word(32n), Word(32n),
    t => Word.and(32n, Word.adc(32n, t, my, False{}, False{}), m6()),
    Word.and(32n, mx, m6()), mx,
    Bits.w_and_absorb(32n, x, m6()))
  +e4 = Equal.sym(Word(32n),
    Word.and(32n, Word.adc(32n, x, y, False{}, False{}), m6()),
    Word.and(32n, Word.adc(32n, mx, my, False{}, False{}), m6()),
    e1)
  Equal.trans(Word(32n),
    Word.and(32n, Word.adc(32n, mx, y, False{}, False{}), m6()),
    Word.and(32n, Word.adc(32n, mx, my, False{}, False{}), m6()),
    Word.and(32n, Word.adc(32n, x, y, False{}, False{}), m6()),
    Equal.trans(Word(32n),
      Word.and(32n, Word.adc(32n, mx, y, False{}, False{}), m6()),
      Word.and(32n, Word.adc(32n, Word.and(32n, mx, m6()), my, False{}, False{}), m6()),
      Word.and(32n, Word.adc(32n, mx, my, False{}, False{}), m6()),
      e2, e3),
    e4)

def low_mask_absorb(+a: U32, +w: U32) -> {U32.and(U32.add(U32.and(a, 63), w), 63) == U32.and(U32.add(a, w), 63) : U32}:
  match a:
    case U32{x}:
      match w:
        case U32{y}:
          Equal.cong(Word(32n), U32, t => U32{t},
            Word.and(32n, Word.adc(32n, Word.and(32n, x, Bits.mask(32n, 6n)), y, False{}, False{}), Bits.mask(32n, 6n)),
            Word.and(32n, Word.adc(32n, x, y, False{}, False{}), Bits.mask(32n, 6n)),
            low_mask_absorb_w(x, y))

def low6_add_indep(+a: U32, +b: U32) -> {U32.and(U32.add(a, b), 63) == U32.and(U32.add(U32.and(a, 63), U32.and(b, 63)), 63) : U32}:
  match a:
    case U32{x}:
      match b:
        case U32{y}:
          Equal.cong(Word(32n), U32, t => U32{t},
            Word.and(32n, Word.adc(32n, x, y, False{}, False{}), Bits.mask(32n, 6n)),
            Word.and(32n, Word.adc(32n, Word.and(32n, x, Bits.mask(32n, 6n)), Word.and(32n, y, Bits.mask(32n, 6n)), False{}, False{}), Bits.mask(32n, 6n)),
            lowadc(32n, 6n, x, y, False{}))
