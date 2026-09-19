import Base

def b_and_idem(a: Bool) -> {Bool.and(a, a) == a : Bool}:
  match a:
    case False{}: {==}
    case True{}: {==}

def b_and_true(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case False{}: {==}
    case True{}: {==}

def b_and_false(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case False{}: {==}
    case True{}: {==}

def b_and_comm(a: Bool, b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

def b_or_idem(a: Bool) -> {Bool.or(a, a) == a : Bool}:
  match a:
    case False{}: {==}
    case True{}: {==}

def b_or_comm(a: Bool, b: Bool) -> {Bool.or(a, b) == Bool.or(b, a) : Bool}:
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

def b_or_false(a: Bool) -> {Bool.or(a, False{}) == a : Bool}:
  match a:
    case False{}: {==}
    case True{}: {==}

def b_not_not(a: Bool) -> {Bool.not(Bool.not(a)) == a : Bool}:
  match a:
    case False{}: {==}
    case True{}: {==}

def w_and_zero(n: Nat, a: Word(n)) -> {Word.and(n, a, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n+p:
      match a:
        case WCon{h, t}:
          %b_and_false(h) : {WCon{Bool.and(h, False{}), Word.and(p, t, Word.zero(p))} == WCon{_, Word.zero(p)} : Word.Con<p>}
          %w_and_zero(p, t) : {WCon{Bool.and(h, False{}), Word.and(p, t, Word.zero(p))} == WCon{Bool.and(h, False{}), _} : Word.Con<p>}
          {==}

def w_or_zero(n: Nat, a: Word(n)) -> {Word.or(n, a, Word.zero(n)) == a : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n+p:
      match a:
        case WCon{h, t}:
          %b_or_false(h) : {WCon{Bool.or(h, False{}), Word.or(p, t, Word.zero(p))} == WCon{_, t} : Word.Con<p>}
          %w_or_zero(p, t) : {WCon{Bool.or(h, False{}), Word.or(p, t, Word.zero(p))} == WCon{Bool.or(h, False{}), _} : Word.Con<p>}
          {==}

def w_and_comm(n: Nat, a: Word(n), b: Word(n)) -> {Word.and(n, a, b) == Word.and(n, b, a) : Word(n)}:
  match n:
    case 0n:
      match a b: case WNil{} WNil{}: {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          %w_and_comm(p, at, bt) : {WCon{Bool.and(ah, bh), Word.and(p, at, bt)} == WCon{Bool.and(bh, ah), _} : Word.Con<p>}
          %b_and_comm(ah, bh) : {WCon{Bool.and(ah, bh), Word.and(p, at, bt)} == WCon{_, Word.and(p, at, bt)} : Word.Con<p>}
          {==}

def w_or_comm(n: Nat, a: Word(n), b: Word(n)) -> {Word.or(n, a, b) == Word.or(n, b, a) : Word(n)}:
  match n:
    case 0n:
      match a b: case WNil{} WNil{}: {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          %w_or_comm(p, at, bt) : {WCon{Bool.or(ah, bh), Word.or(p, at, bt)} == WCon{Bool.or(bh, ah), _} : Word.Con<p>}
          %b_or_comm(ah, bh) : {WCon{Bool.or(ah, bh), Word.or(p, at, bt)} == WCon{_, Word.or(p, at, bt)} : Word.Con<p>}
          {==}

def w_and_idem(n: Nat, a: Word(n)) -> {Word.and(n, a, a) == a : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n+p:
      match a:
        case WCon{h, t}:
          %w_and_idem(p, t) : {WCon{Bool.and(h, h), Word.and(p, t, t)} == WCon{h, _} : Word.Con<p>}
          %b_and_idem(h) : {WCon{Bool.and(h, h), Word.and(p, t, t)} == WCon{_, Word.and(p, t, t)} : Word.Con<p>}
          {==}

def w_or_idem(n: Nat, a: Word(n)) -> {Word.or(n, a, a) == a : Word(n)}:
  match n:
    case 0n:
      match a: case WNil{}: {==}
    case 1n+p:
      match a:
        case WCon{h, t}:
          %w_or_idem(p, t) : {WCon{Bool.or(h, h), Word.or(p, t, t)} == WCon{h, _} : Word.Con<p>}
          %b_or_idem(h) : {WCon{Bool.or(h, h), Word.or(p, t, t)} == WCon{_, Word.or(p, t, t)} : Word.Con<p>}
          {==}

def shl_put_shrpad(q: Nat, th: Bool, tt: Word(q)) -> {Word.shl.put(1n+q, th, Word.shr.pad(q, tt)) == WCon{th, tt} : Word(1n+q)}:
  match q:
    case 0n:
      match tt: case WNil{}: {==}
    case 1n+r:
      match tt:
        case WCon{tth, ttt}:
          %shl_put_shrpad(r, tth, ttt) : {WCon{th, Word.shl.put(1n+r, tth, Word.shr.pad(r, ttt))} == WCon{th, _} : Word.Con<1n+r>}
          {==}

def shl_after_shr(p: Nat, h: Bool, t: Word(p)) -> {Word.shl(1n+p, Word.shr(1n+p, WCon{h, t})) == WCon{False{}, t} : Word(1n+p)}:
  match p:
    case 0n:
      match t: case WNil{}: {==}
    case 1n+q:
      match t:
        case WCon{t0, t1}:
          %shl_put_shrpad(q, t0, t1) : {WCon{False{}, Word.shl.put(1n+q, t0, Word.shr.pad(q, t1))} == WCon{False{}, _} : Word.Con<1n+q>}
          {==}

def shl_put_or(n: Nat, ah: Bool, bh: Bool, at: Word(n), bt: Word(n)) -> {Word.shl.put(n, Bool.or(ah, bh), Word.or(n, at, bt)) == Word.or(n, Word.shl.put(n, ah, at), Word.shl.put(n, bh, bt)) : Word(n)}:
  match n:
    case 0n:
      match at bt: case WNil{} WNil{}: {==}
    case 1n+p:
      match at bt:
        case WCon{ath, att} WCon{bth, btt}:
          %shl_put_or(p, ath, bth, att, btt) : {WCon{Bool.or(ah, bh), Word.shl.put(p, Bool.or(ath, bth), Word.or(p, att, btt))} == WCon{Bool.or(ah, bh), _} : Word.Con<p>}
          {==}

def shl_put_and(n: Nat, ah: Bool, bh: Bool, at: Word(n), bt: Word(n)) -> {Word.shl.put(n, Bool.and(ah, bh), Word.and(n, at, bt)) == Word.and(n, Word.shl.put(n, ah, at), Word.shl.put(n, bh, bt)) : Word(n)}:
  match n:
    case 0n:
      match at bt: case WNil{} WNil{}: {==}
    case 1n+p:
      match at bt:
        case WCon{ath, att} WCon{bth, btt}:
          %shl_put_and(p, ath, bth, att, btt) : {WCon{Bool.and(ah, bh), Word.shl.put(p, Bool.and(ath, bth), Word.and(p, att, btt))} == WCon{Bool.and(ah, bh), _} : Word.Con<p>}
          {==}

def shr_pad_or(n: Nat, at: Word(n), bt: Word(n)) -> {Word.shr.pad(n, Word.or(n, at, bt)) == Word.or(1n+n, Word.shr.pad(n, at), Word.shr.pad(n, bt)) : Word(1n+n)}:
  match n:
    case 0n:
      match at bt: case WNil{} WNil{}: {==}
    case 1n+p:
      match at bt:
        case WCon{ath, att} WCon{bth, btt}:
          %shr_pad_or(p, att, btt) : {WCon{Bool.or(ath, bth), Word.shr.pad(p, Word.or(p, att, btt))} == WCon{Bool.or(ath, bth), _} : Word.Con<1n+p>}
          {==}

def shl_or(n: Nat, a: Word(n), b: Word(n)) -> {Word.shl(n, Word.or(n, a, b)) == Word.or(n, Word.shl(n, a), Word.shl(n, b)) : Word(n)}:
  match n:
    case 0n:
      match a b: case WNil{} WNil{}: {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          %shl_put_or(p, ah, bh, at, bt) : {WCon{False{}, Word.shl.put(p, Bool.or(ah, bh), Word.or(p, at, bt))} == WCon{False{}, _} : Word.Con<p>}
          {==}

def shr_or(n: Nat, a: Word(n), b: Word(n)) -> {Word.shr(n, Word.or(n, a, b)) == Word.or(n, Word.shr(n, a), Word.shr(n, b)) : Word(n)}:
  match n:
    case 0n:
      match a b: case WNil{} WNil{}: {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          %shr_pad_or(p, at, bt) : {Word.shr.pad(p, Word.or(p, at, bt)) == _ : Word(1n+p)}
          {==}

def shl_and(n: Nat, a: Word(n), b: Word(n)) -> {Word.shl(n, Word.and(n, a, b)) == Word.and(n, Word.shl(n, a), Word.shl(n, b)) : Word(n)}:
  match n:
    case 0n:
      match a b: case WNil{} WNil{}: {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          %shl_put_and(p, ah, bh, at, bt) : {WCon{False{}, Word.shl.put(p, Bool.and(ah, bh), Word.and(p, at, bt))} == WCon{False{}, _} : Word.Con<p>}
          {==}

def shl_put_shrpad_alt(q: Nat, th: Bool, tt: Word(q)) -> {WCon{th, tt} == Word.shl.put(1n+q, th, Word.shr.pad(q, tt)) : Word(1n+q)}:
  match q:
    case 0n:
      match tt: case WNil{}: {==}
    case 1n+r:
      match tt:
        case WCon{tth, ttt}:
          %shl_put_shrpad_alt(r, tth, ttt) : {WCon{th, WCon{tth, ttt}} == WCon{th, _} : Word.Con<1n+r>}
          {==}

def shl_shrpad_alt(p: Nat, X: Word(p)) -> {WCon{False{}, X} == Word.shl(1n+p, Word.shr.pad(p, X)) : Word(1n+p)}:
  match p:
    case 0n:
      match X: case WNil{}: {==}
    case 1n+q:
      match X:
        case WCon{x0, x1}:
          %shl_put_shrpad_alt(q, x0, x1) : {WCon{False{}, WCon{x0, x1}} == WCon{False{}, _} : Word.Con<1n+q>}
          {==}

def and_shrpad_alt(n: Nat, wt: Word(n), mh: Bool, mt: Word(n)) -> {Word.shr.pad(n, Word.and(n, wt, Word.shl.put(n, mh, mt))) == Word.and(1n+n, Word.shr.pad(n, wt), WCon{mh, mt}) : Word(1n+n)}:
  match n:
    case 0n:
      match wt mt: case WNil{} WNil{}: {==}
    case 1n+q:
      match wt mt:
        case WCon{wth, wtt} WCon{mth, mtt}:
          %and_shrpad_alt(q, wtt, mth, mtt) : {WCon{Bool.and(wth, mh), Word.shr.pad(q, Word.and(q, wtt, Word.shl.put(q, mth, mtt)))} == WCon{Bool.and(wth, mh), _} : Word.Con<1n+q>}
          {==}

def and_shl(n: Nat, w: Word(n), m: Word(n)) -> {Word.and(n, w, Word.shl(n, m)) == Word.shl(n, Word.and(n, Word.shr(n, w), m)) : Word(n)}:
  match n:
    case 0n:
      match w m: case WNil{} WNil{}: {==}
    case 1n+p:
      match w m:
        case WCon{+wh, +wt} WCon{+mh, +mt}:
          +p2 = p
          %and_shrpad_alt(p2, wt, mh, mt) : {WCon{Bool.and(wh, False{}), Word.and(p2, wt, Word.shl.put(p2, mh, mt))} == Word.shl(1n+p2, _) : Word.Con<p2>}
          %shl_shrpad_alt(p2, Word.and(p2, wt, Word.shl.put(p2, mh, mt))) : {WCon{Bool.and(wh, False{}), Word.and(p2, wt, Word.shl.put(p2, mh, mt))} == _ : Word.Con<p2>}
          %b_and_false(wh) : {WCon{Bool.and(wh, False{}), Word.and(p2, wt, Word.shl.put(p2, mh, mt))} == WCon{_, Word.and(p2, wt, Word.shl.put(p2, mh, mt))} : Word.Con<p2>}
          {==}

def b_and_assoc(a: Bool, b: Bool, c: Bool) -> {Bool.and(Bool.and(a, b), c) == Bool.and(a, Bool.and(b, c)) : Bool}:
  match a b c:
    case False{} False{} False{}: {==}
    case False{} False{} True{}: {==}
    case False{} True{} False{}: {==}
    case False{} True{} True{}: {==}
    case True{} False{} False{}: {==}
    case True{} False{} True{}: {==}
    case True{} True{} False{}: {==}
    case True{} True{} True{}: {==}

def w_and_assoc(+n: Nat, +a: Word(n), +b: Word(n), +c: Word(n)) -> {Word.and(n, Word.and(n, a, b), c) == Word.and(n, a, Word.and(n, b, c)) : Word(n)}:
  match n:
    case 0n:
      match a b c: case WNil{} WNil{} WNil{}: {==}
    case 1n+p:
      match a b c:
        case WCon{+ah, +at} WCon{+bh, +bt} WCon{+ch, +ct}:
          +T1 = Word.and(p, Word.and(p, at, bt), ct)
          +T2 = Word.and(p, at, Word.and(p, bt, ct))
          +ba = b_and_assoc(ah, bh, ch)
          +ih = w_and_assoc(p, at, bt, ct)
          Equal.trans(Word(1n+p),
            WCon{Bool.and(Bool.and(ah, bh), ch), T1},
            WCon{Bool.and(Bool.and(ah, bh), ch), T2},
            WCon{Bool.and(ah, Bool.and(bh, ch)), T2},
            Equal.cong(Word(p), Word(1n+p), t => WCon{Bool.and(Bool.and(ah, bh), ch), t}, T1, T2, ih),
            Equal.cong(Bool, Word(1n+p), h => WCon{h, T2}, Bool.and(Bool.and(ah, bh), ch), Bool.and(ah, Bool.and(bh, ch)), ba))

def b_and_or(a: Bool, b: Bool, c: Bool) -> {Bool.and(a, Bool.or(b, c)) == Bool.or(Bool.and(a, b), Bool.and(a, c)) : Bool}:
  match a b c:
    case False{} False{} False{}: {==}
    case False{} False{} True{}: {==}
    case False{} True{} False{}: {==}
    case False{} True{} True{}: {==}
    case True{} False{} False{}: {==}
    case True{} False{} True{}: {==}
    case True{} True{} False{}: {==}
    case True{} True{} True{}: {==}

def b_and_absorb(a: Bool, b: Bool) -> {Bool.and(Bool.and(a, b), b) == Bool.and(a, b) : Bool}:
  match a b:
    case False{} False{}: {==}
    case False{} True{}: {==}
    case True{} False{}: {==}
    case True{} True{}: {==}

def mask(n: Nat, k: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      match k:
        case 0n:
          WCon{False{}, Word.zero(p)}
        case 1n+kp:
          WCon{True{}, mask(p, kp)}

def shl_n(+n: Nat, X: Word(n), k: Nat) -> Word(n):
  match k:
    case 0n:
      X
    case 1n+q:
      Word.shl(n, shl_n(n, X, q))

def shr_n(+n: Nat, k: Nat, X: Word(n)) -> Word(n):
  match k:
    case 0n:
      X
    case 1n+q:
      shr_n(n, q, Word.shr(n, X))

def w_and_absorb(n: Nat, w: Word(n), m: Word(n)) -> {Word.and(n, Word.and(n, w, m), m) == Word.and(n, w, m) : Word(n)}:
  match n:
    case 0n:
      match w m: case WNil{} WNil{}: {==}
    case 1n+p:
      match w m:
        case WCon{wh, wt} WCon{mh, mt}:
          %w_and_absorb(p, wt, mt) : {WCon{Bool.and(Bool.and(wh, mh), mh), Word.and(p, Word.and(p, wt, mt), mt)} == WCon{Bool.and(wh, mh), _} : Word.Con<p>}
          %b_and_absorb(wh, mh) : {WCon{Bool.and(Bool.and(wh, mh), mh), Word.and(p, Word.and(p, wt, mt), mt)} == WCon{_, Word.and(p, Word.and(p, wt, mt), mt)} : Word.Con<p>}
          {==}

def w_and_or(n: Nat, a: Word(n), b: Word(n), c: Word(n)) -> {Word.and(n, a, Word.or(n, b, c)) == Word.or(n, Word.and(n, a, b), Word.and(n, a, c)) : Word(n)}:
  match n:
    case 0n:
      match a b c: case WNil{} WNil{} WNil{}: {==}
    case 1n+p:
      match a b c:
        case WCon{ah, at} WCon{bh, bt} WCon{ch, ct}:
          %w_and_or(p, at, bt, ct) : {WCon{Bool.and(ah, Bool.or(bh, ch)), Word.and(p, at, Word.or(p, bt, ct))} == WCon{Bool.or(Bool.and(ah, bh), Bool.and(ah, ch)), _} : Word.Con<p>}
          %b_and_or(ah, bh, ch) : {WCon{Bool.and(ah, Bool.or(bh, ch)), Word.and(p, at, Word.or(p, bt, ct))} == WCon{_, Word.and(p, at, Word.or(p, bt, ct))} : Word.Con<p>}
          {==}

def w_or_and(n: Nat, a: Word(n), b: Word(n), c: Word(n)) -> {Word.or(n, Word.and(n, a, b), Word.and(n, a, c)) == Word.and(n, a, Word.or(n, b, c)) : Word(n)}:
  %w_and_or(n, a, b, c) : {_ == Word.and(n, a, Word.or(n, b, c)) : Word(n)}
  {==}

def and_shl_n(+n: Nat, k: Nat, +w: Word(n), +m: Word(n)) -> {Word.and(n, w, shl_n(n, m, k)) == shl_n(n, Word.and(n, shr_n(n, k, w), m), k) : Word(n)}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      +qq = q
      Equal.trans(Word(n),
        Word.and(n, w, Word.shl(n, shl_n(n, m, qq))),
        Word.shl(n, Word.and(n, Word.shr(n, w), shl_n(n, m, qq))),
        Word.shl(n, shl_n(n, Word.and(n, shr_n(n, qq, Word.shr(n, w)), m), qq)),
        and_shl(n, w, shl_n(n, m, qq)),
        Equal.cong(Word(n), Word(n), x => Word.shl(n, x),
          Word.and(n, Word.shr(n, w), shl_n(n, m, qq)),
          shl_n(n, Word.and(n, shr_n(n, qq, Word.shr(n, w)), m), qq),
          and_shl_n(n, qq, Word.shr(n, w), m)))

def ixm(+n: Nat, w: Word(n)) -> Word(n):
  Word.and(n, w, mask(n, 6n))

def izm(+n: Nat, w: Word(n)) -> Word(n):
  Word.and(n, shr_n(n, 6n, w), mask(n, 6n))

def iym(+n: Nat, w: Word(n)) -> Word(n):
  Word.and(n, shr_n(n, 12n, w), mask(n, 6n))

def model_index(+n: Nat, +w: Word(n)) -> Word(n):
  Word.or(n,
    Word.or(n, Word.and(n, ixm(n, w), mask(n, 6n)),
              shl_n(n, Word.and(n, izm(n, w), mask(n, 6n)), 6n)),
    shl_n(n, Word.and(n, iym(n, w), mask(n, 6n)), 12n))

def t0(w: Word(32n)) -> {Word.and(32n, ixm(32n, w), mask(32n, 6n)) == ixm(32n, w) : Word(32n)}:
  w_and_absorb(32n, w, mask(32n, 6n))

def t1_inner(w: Word(32n)) -> {Word.and(32n, izm(32n, w), mask(32n, 6n)) == izm(32n, w) : Word(32n)}:
  w_and_absorb(32n, shr_n(32n, 6n, w), mask(32n, 6n))

def t1(w: Word(32n)) -> {shl_n(32n, Word.and(32n, izm(32n, w), mask(32n, 6n)), 6n) == Word.and(32n, w, shl_n(32n, mask(32n, 6n), 6n)) : Word(32n)}:
  +w2 = w
  Equal.trans(Word(32n),
    shl_n(32n, Word.and(32n, izm(32n, w), mask(32n, 6n)), 6n),
    shl_n(32n, izm(32n, w), 6n),
    Word.and(32n, w, shl_n(32n, mask(32n, 6n), 6n)),
    Equal.cong(Word(32n), Word(32n), x => shl_n(32n, x, 6n),
      Word.and(32n, izm(32n, w2), mask(32n, 6n)), izm(32n, w2), t1_inner(w2)),
    Equal.sym(Word(32n),
      Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 6n)),
      shl_n(32n, Word.and(32n, shr_n(32n, 6n, w2), mask(32n, 6n)), 6n),
      and_shl_n(32n, 6n, w2, mask(32n, 6n))))

def t2_inner(w: Word(32n)) -> {Word.and(32n, iym(32n, w), mask(32n, 6n)) == iym(32n, w) : Word(32n)}:
  w_and_absorb(32n, shr_n(32n, 12n, w), mask(32n, 6n))

def t2(w: Word(32n)) -> {shl_n(32n, Word.and(32n, iym(32n, w), mask(32n, 6n)), 12n) == Word.and(32n, w, shl_n(32n, mask(32n, 6n), 12n)) : Word(32n)}:
  +w2 = w
  Equal.trans(Word(32n),
    shl_n(32n, Word.and(32n, iym(32n, w), mask(32n, 6n)), 12n),
    shl_n(32n, iym(32n, w), 12n),
    Word.and(32n, w, shl_n(32n, mask(32n, 6n), 12n)),
    Equal.cong(Word(32n), Word(32n), x => shl_n(32n, x, 12n),
      Word.and(32n, iym(32n, w2), mask(32n, 6n)), iym(32n, w2), t2_inner(w2)),
    Equal.sym(Word(32n),
      Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 12n)),
      shl_n(32n, Word.and(32n, shr_n(32n, 12n, w2), mask(32n, 6n)), 12n),
      and_shl_n(32n, 12n, w2, mask(32n, 6n))))

def mask_index() -> {Word.or(32n, mask(32n, 6n), Word.or(32n, shl_n(32n, mask(32n, 6n), 6n), shl_n(32n, mask(32n, 6n), 12n))) == mask(32n, 18n) : Word(32n)}:
  {==}

def and_factor(+n: Nat, +w: Word(n), +A: Word(n), +B: Word(n), +C: Word(n)) -> {Word.or(n, Word.and(n, w, A), Word.or(n, Word.and(n, w, B), Word.and(n, w, C))) == Word.and(n, w, Word.or(n, A, Word.or(n, B, C))) : Word(n)}:
  Equal.trans(Word(n),
    Word.or(n, Word.and(n, w, A), Word.or(n, Word.and(n, w, B), Word.and(n, w, C))),
    Word.or(n, Word.and(n, w, A), Word.and(n, w, Word.or(n, B, C))),
    Word.and(n, w, Word.or(n, A, Word.or(n, B, C))),
    Equal.cong(Word(n), Word(n), x => Word.or(n, Word.and(n, w, A), x),
      Word.or(n, Word.and(n, w, B), Word.and(n, w, C)), Word.and(n, w, Word.or(n, B, C)),
      Equal.sym(Word(n), Word.and(n, w, Word.or(n, B, C)), Word.or(n, Word.and(n, w, B), Word.and(n, w, C)), w_and_or(n, w, B, C))),
    w_or_and(n, w, A, Word.or(n, B, C)))

def mask_index_l() -> {Word.or(32n, Word.or(32n, mask(32n, 6n), shl_n(32n, mask(32n, 6n), 6n)), shl_n(32n, mask(32n, 6n), 12n)) == mask(32n, 18n) : Word(32n)}:
  {==}

def and_factor_l(+n: Nat, +w: Word(n), +A: Word(n), +B: Word(n), +C: Word(n)) -> {Word.or(n, Word.or(n, Word.and(n, w, A), Word.and(n, w, B)), Word.and(n, w, C)) == Word.and(n, w, Word.or(n, Word.or(n, A, B), C)) : Word(n)}:
  Equal.trans(Word(n),
    Word.or(n, Word.or(n, Word.and(n, w, A), Word.and(n, w, B)), Word.and(n, w, C)),
    Word.or(n, Word.and(n, w, Word.or(n, A, B)), Word.and(n, w, C)),
    Word.and(n, w, Word.or(n, Word.or(n, A, B), C)),
    Equal.cong(Word(n), Word(n), x => Word.or(n, x, Word.and(n, w, C)),
      Word.or(n, Word.and(n, w, A), Word.and(n, w, B)), Word.and(n, w, Word.or(n, A, B)),
      Equal.sym(Word(n), Word.and(n, w, Word.or(n, A, B)), Word.or(n, Word.and(n, w, A), Word.and(n, w, B)), w_and_or(n, w, A, B))),
    w_or_and(n, w, Word.or(n, A, B), C))

def stepA(w: Word(32n)) -> {model_index(32n, w) == Word.or(32n, Word.or(32n, Word.and(32n, w, mask(32n, 6n)), Word.and(32n, w, shl_n(32n, mask(32n, 6n), 6n))), Word.and(32n, w, shl_n(32n, mask(32n, 6n), 12n))) : Word(32n)}:
  +w2 = w
  e02 = Equal.trans(Word(32n),
    Word.or(32n, Word.or(32n, Word.and(32n, ixm(32n, w2), mask(32n, 6n)),
        shl_n(32n, Word.and(32n, izm(32n, w2), mask(32n, 6n)), 6n)),
      shl_n(32n, Word.and(32n, iym(32n, w2), mask(32n, 6n)), 12n)),
    Word.or(32n, Word.or(32n, Word.and(32n, ixm(32n, w2), mask(32n, 6n)),
        shl_n(32n, Word.and(32n, izm(32n, w2), mask(32n, 6n)), 6n)),
      Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 12n))),
    Word.or(32n, Word.or(32n, Word.and(32n, ixm(32n, w2), mask(32n, 6n)),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 6n))),
      Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 12n))),
    Equal.cong(Word(32n), Word(32n),
      x => Word.or(32n, Word.or(32n, Word.and(32n, ixm(32n, w2), mask(32n, 6n)),
        shl_n(32n, Word.and(32n, izm(32n, w2), mask(32n, 6n)), 6n)), x),
      shl_n(32n, Word.and(32n, iym(32n, w2), mask(32n, 6n)), 12n),
      Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 12n)), t2(w2)),
    Equal.cong(Word(32n), Word(32n),
      x => Word.or(32n, Word.or(32n, Word.and(32n, ixm(32n, w2), mask(32n, 6n)), x),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 12n))),
      shl_n(32n, Word.and(32n, izm(32n, w2), mask(32n, 6n)), 6n),
      Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 6n)), t1(w2)))
  Equal.trans(Word(32n),
    Word.or(32n, Word.or(32n, Word.and(32n, ixm(32n, w2), mask(32n, 6n)),
        shl_n(32n, Word.and(32n, izm(32n, w2), mask(32n, 6n)), 6n)),
      shl_n(32n, Word.and(32n, iym(32n, w2), mask(32n, 6n)), 12n)),
    Word.or(32n, Word.or(32n, Word.and(32n, ixm(32n, w2), mask(32n, 6n)),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 6n))),
      Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 12n))),
    Word.or(32n, Word.or(32n, Word.and(32n, w2, mask(32n, 6n)),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 6n))),
      Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 12n))),
    e02,
    Equal.cong(Word(32n), Word(32n),
      x => Word.or(32n, Word.or(32n, x,
          Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 6n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 12n))),
      Word.and(32n, ixm(32n, w2), mask(32n, 6n)),
      Word.and(32n, w2, mask(32n, 6n)), t0(w2)))

def stepBC(w: Word(32n)) -> {Word.or(32n, Word.or(32n, Word.and(32n, w, mask(32n, 6n)), Word.and(32n, w, shl_n(32n, mask(32n, 6n), 6n))), Word.and(32n, w, shl_n(32n, mask(32n, 6n), 12n))) == Word.and(32n, w, mask(32n, 18n)) : Word(32n)}:
  +w2 = w
  Equal.trans(Word(32n),
    Word.or(32n, Word.or(32n, Word.and(32n, w2, mask(32n, 6n)),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 6n))),
      Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 12n))),
    Word.and(32n, w2, Word.or(32n, Word.or(32n, mask(32n, 6n), shl_n(32n, mask(32n, 6n), 6n)), shl_n(32n, mask(32n, 6n), 12n))),
    Word.and(32n, w2, mask(32n, 18n)),
    and_factor_l(32n, w2, mask(32n, 6n), shl_n(32n, mask(32n, 6n), 6n), shl_n(32n, mask(32n, 6n), 12n)),
    Equal.cong(Word(32n), Word(32n), x => Word.and(32n, w2, x),
      Word.or(32n, Word.or(32n, mask(32n, 6n), shl_n(32n, mask(32n, 6n), 6n)), shl_n(32n, mask(32n, 6n), 12n)),
      mask(32n, 18n), mask_index_l()))

def model_index_rt(+w: Word(32n)) -> {model_index(32n, w) == Word.and(32n, w, mask(32n, 18n)) : Word(32n)}:
  Equal.trans(Word(32n), model_index(32n, w),
    Word.or(32n, Word.or(32n, Word.and(32n, w, mask(32n, 6n)),
        Word.and(32n, w, shl_n(32n, mask(32n, 6n), 6n))),
      Word.and(32n, w, shl_n(32n, mask(32n, 6n), 12n))),
    Word.and(32n, w, mask(32n, 18n)), stepA(w), stepBC(w))

def cmat(+n: Nat, w: Word(n)) -> Word(n):
  Word.and(n, w, mask(n, 5n))

def ccoh(+n: Nat, w: Word(n)) -> Word(n):
  Word.and(n, shr_n(n, 5n, w), mask(n, 6n))

def cact(+n: Nat, w: Word(n)) -> Word(n):
  Word.and(n, shr_n(n, 11n, w), mask(n, 1n))

def csup(+n: Nat, w: Word(n)) -> Word(n):
  Word.and(n, shr_n(n, 12n, w), mask(n, 5n))

def cfl(+n: Nat, w: Word(n)) -> Word(n):
  Word.and(n, shr_n(n, 17n, w), mask(n, 6n))

def model_cell(+n: Nat, +w: Word(n)) -> Word(n):
  Word.or(n,
    Word.or(n,
      Word.or(n,
        Word.or(n, Word.and(n, cmat(n, w), mask(n, 5n)),
                    shl_n(n, Word.and(n, ccoh(n, w), mask(n, 6n)), 5n)),
        shl_n(n, Word.and(n, cact(n, w), mask(n, 1n)), 11n)),
      shl_n(n, Word.and(n, csup(n, w), mask(n, 5n)), 12n)),
    shl_n(n, Word.and(n, cfl(n, w), mask(n, 6n)), 17n))

def tcmat(w: Word(32n)) -> {Word.and(32n, cmat(32n, w), mask(32n, 5n)) == Word.and(32n, w, mask(32n, 5n)) : Word(32n)}:
  w_and_absorb(32n, w, mask(32n, 5n))

def tccoh(w: Word(32n)) -> {shl_n(32n, Word.and(32n, ccoh(32n, w), mask(32n, 6n)), 5n) == Word.and(32n, w, shl_n(32n, mask(32n, 6n), 5n)) : Word(32n)}:
  +w2 = w
  Equal.trans(Word(32n),
    shl_n(32n, Word.and(32n, ccoh(32n, w2), mask(32n, 6n)), 5n),
    shl_n(32n, ccoh(32n, w2), 5n),
    Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 5n)),
    Equal.cong(Word(32n), Word(32n), x => shl_n(32n, x, 5n),
      Word.and(32n, ccoh(32n, w2), mask(32n, 6n)), ccoh(32n, w2),
      w_and_absorb(32n, shr_n(32n, 5n, w2), mask(32n, 6n))),
    Equal.sym(Word(32n),
      Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 5n)),
      shl_n(32n, Word.and(32n, shr_n(32n, 5n, w2), mask(32n, 6n)), 5n),
      and_shl_n(32n, 5n, w2, mask(32n, 6n))))

def tcact(w: Word(32n)) -> {shl_n(32n, Word.and(32n, cact(32n, w), mask(32n, 1n)), 11n) == Word.and(32n, w, shl_n(32n, mask(32n, 1n), 11n)) : Word(32n)}:
  +w2 = w
  Equal.trans(Word(32n),
    shl_n(32n, Word.and(32n, cact(32n, w2), mask(32n, 1n)), 11n),
    shl_n(32n, cact(32n, w2), 11n),
    Word.and(32n, w2, shl_n(32n, mask(32n, 1n), 11n)),
    Equal.cong(Word(32n), Word(32n), x => shl_n(32n, x, 11n),
      Word.and(32n, cact(32n, w2), mask(32n, 1n)), cact(32n, w2),
      w_and_absorb(32n, shr_n(32n, 11n, w2), mask(32n, 1n))),
    Equal.sym(Word(32n),
      Word.and(32n, w2, shl_n(32n, mask(32n, 1n), 11n)),
      shl_n(32n, Word.and(32n, shr_n(32n, 11n, w2), mask(32n, 1n)), 11n),
      and_shl_n(32n, 11n, w2, mask(32n, 1n))))

def tcsup(w: Word(32n)) -> {shl_n(32n, Word.and(32n, csup(32n, w), mask(32n, 5n)), 12n) == Word.and(32n, w, shl_n(32n, mask(32n, 5n), 12n)) : Word(32n)}:
  +w2 = w
  Equal.trans(Word(32n),
    shl_n(32n, Word.and(32n, csup(32n, w2), mask(32n, 5n)), 12n),
    shl_n(32n, csup(32n, w2), 12n),
    Word.and(32n, w2, shl_n(32n, mask(32n, 5n), 12n)),
    Equal.cong(Word(32n), Word(32n), x => shl_n(32n, x, 12n),
      Word.and(32n, csup(32n, w2), mask(32n, 5n)), csup(32n, w2),
      w_and_absorb(32n, shr_n(32n, 12n, w2), mask(32n, 5n))),
    Equal.sym(Word(32n),
      Word.and(32n, w2, shl_n(32n, mask(32n, 5n), 12n)),
      shl_n(32n, Word.and(32n, shr_n(32n, 12n, w2), mask(32n, 5n)), 12n),
      and_shl_n(32n, 12n, w2, mask(32n, 5n))))

def tcfl(w: Word(32n)) -> {shl_n(32n, Word.and(32n, cfl(32n, w), mask(32n, 6n)), 17n) == Word.and(32n, w, shl_n(32n, mask(32n, 6n), 17n)) : Word(32n)}:
  +w2 = w
  Equal.trans(Word(32n),
    shl_n(32n, Word.and(32n, cfl(32n, w2), mask(32n, 6n)), 17n),
    shl_n(32n, cfl(32n, w2), 17n),
    Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n)),
    Equal.cong(Word(32n), Word(32n), x => shl_n(32n, x, 17n),
      Word.and(32n, cfl(32n, w2), mask(32n, 6n)), cfl(32n, w2),
      w_and_absorb(32n, shr_n(32n, 17n, w2), mask(32n, 6n))),
    Equal.sym(Word(32n),
      Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n)),
      shl_n(32n, Word.and(32n, shr_n(32n, 17n, w2), mask(32n, 6n)), 17n),
      and_shl_n(32n, 17n, w2, mask(32n, 6n))))

def factor5(+n: Nat, +w: Word(n), +A: Word(n), +B: Word(n), +C: Word(n), +D: Word(n), +E: Word(n)) -> {Word.or(n, Word.or(n, Word.or(n, Word.or(n, Word.and(n, w, A), Word.and(n, w, B)), Word.and(n, w, C)), Word.and(n, w, D)), Word.and(n, w, E)) == Word.and(n, w, Word.or(n, Word.or(n, Word.or(n, Word.or(n, A, B), C), D), E)) : Word(n)}:
  g1 = Equal.trans(Word(n),
     Word.or(n, Word.or(n, Word.and(n, w, A), Word.and(n, w, B)), Word.and(n, w, C)),
     Word.or(n, Word.and(n, w, Word.or(n, A, B)), Word.and(n, w, C)),
     Word.and(n, w, Word.or(n, Word.or(n, A, B), C)),
     Equal.cong(Word(n), Word(n), x => Word.or(n, x, Word.and(n, w, C)),
        Word.or(n, Word.and(n, w, A), Word.and(n, w, B)), Word.and(n, w, Word.or(n, A, B)),
        w_or_and(n, w, A, B)),
     w_or_and(n, w, Word.or(n, A, B), C))
  g2 = Equal.trans(Word(n),
     Word.or(n, Word.or(n, Word.or(n, Word.and(n, w, A), Word.and(n, w, B)), Word.and(n, w, C)), Word.and(n, w, D)),
     Word.or(n, Word.and(n, w, Word.or(n, Word.or(n, A, B), C)), Word.and(n, w, D)),
     Word.and(n, w, Word.or(n, Word.or(n, Word.or(n, A, B), C), D)),
     Equal.cong(Word(n), Word(n), x => Word.or(n, x, Word.and(n, w, D)),
        Word.or(n, Word.or(n, Word.and(n, w, A), Word.and(n, w, B)), Word.and(n, w, C)),
        Word.and(n, w, Word.or(n, Word.or(n, A, B), C)), g1),
     w_or_and(n, w, Word.or(n, Word.or(n, A, B), C), D))
  Equal.trans(Word(n),
     Word.or(n, Word.or(n, Word.or(n, Word.or(n, Word.and(n, w, A), Word.and(n, w, B)), Word.and(n, w, C)), Word.and(n, w, D)), Word.and(n, w, E)),
     Word.or(n, Word.and(n, w, Word.or(n, Word.or(n, Word.or(n, A, B), C), D)), Word.and(n, w, E)),
     Word.and(n, w, Word.or(n, Word.or(n, Word.or(n, Word.or(n, A, B), C), D), E)),
     Equal.cong(Word(n), Word(n), x => Word.or(n, x, Word.and(n, w, E)),
        Word.or(n, Word.or(n, Word.or(n, Word.and(n, w, A), Word.and(n, w, B)), Word.and(n, w, C)), Word.and(n, w, D)),
        Word.and(n, w, Word.or(n, Word.or(n, Word.or(n, A, B), C), D)), g2),
     w_or_and(n, w, Word.or(n, Word.or(n, Word.or(n, A, B), C), D), E))

def mask_cell() -> {Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n, mask(32n, 5n), shl_n(32n, mask(32n, 6n), 5n)), shl_n(32n, mask(32n, 1n), 11n)), shl_n(32n, mask(32n, 5n), 12n)), shl_n(32n, mask(32n, 6n), 17n)) == mask(32n, 23n) : Word(32n)}:
  {==}

def model_cell_rt(+w: Word(32n)) -> {model_cell(32n, w) == Word.and(32n, w, mask(32n, 23n)) : Word(32n)}:
  +w2 = w
  p1 = Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n,
        Word.and(32n, cmat(32n, w2), mask(32n, 5n)),
        shl_n(32n, Word.and(32n, ccoh(32n, w2), mask(32n, 6n)), 5n)),
        shl_n(32n, Word.and(32n, cact(32n, w2), mask(32n, 1n)), 11n)),
        shl_n(32n, Word.and(32n, csup(32n, w2), mask(32n, 5n)), 12n)),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n)))
  p2 = Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n,
        Word.and(32n, cmat(32n, w2), mask(32n, 5n)),
        shl_n(32n, Word.and(32n, ccoh(32n, w2), mask(32n, 6n)), 5n)),
        shl_n(32n, Word.and(32n, cact(32n, w2), mask(32n, 1n)), 11n)),
        Word.and(32n, w2, shl_n(32n, mask(32n, 5n), 12n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n)))
  p3 = Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n,
        Word.and(32n, cmat(32n, w2), mask(32n, 5n)),
        shl_n(32n, Word.and(32n, ccoh(32n, w2), mask(32n, 6n)), 5n)),
        Word.and(32n, w2, shl_n(32n, mask(32n, 1n), 11n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 5n), 12n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n)))
  p4 = Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n,
        Word.and(32n, cmat(32n, w2), mask(32n, 5n)),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 5n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 1n), 11n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 5n), 12n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n)))
  p5 = Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n,
        Word.and(32n, w2, mask(32n, 5n)),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 5n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 1n), 11n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 5n), 12n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n)))
  e1 = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n,
        Word.and(32n, cmat(32n, w2), mask(32n, 5n)),
        shl_n(32n, Word.and(32n, ccoh(32n, w2), mask(32n, 6n)), 5n)),
        shl_n(32n, Word.and(32n, cact(32n, w2), mask(32n, 1n)), 11n)),
        shl_n(32n, Word.and(32n, csup(32n, w2), mask(32n, 5n)), 12n)), x),
    shl_n(32n, Word.and(32n, cfl(32n, w2), mask(32n, 6n)), 17n),
    Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n)), tcfl(w2))
  e2 = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n,
        Word.and(32n, cmat(32n, w2), mask(32n, 5n)),
        shl_n(32n, Word.and(32n, ccoh(32n, w2), mask(32n, 6n)), 5n)),
        shl_n(32n, Word.and(32n, cact(32n, w2), mask(32n, 1n)), 11n)), x),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n))),
    shl_n(32n, Word.and(32n, csup(32n, w2), mask(32n, 5n)), 12n),
    Word.and(32n, w2, shl_n(32n, mask(32n, 5n), 12n)), tcsup(w2))
  e3 = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n,
        Word.and(32n, cmat(32n, w2), mask(32n, 5n)),
        shl_n(32n, Word.and(32n, ccoh(32n, w2), mask(32n, 6n)), 5n)), x),
        Word.and(32n, w2, shl_n(32n, mask(32n, 5n), 12n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n))),
    shl_n(32n, Word.and(32n, cact(32n, w2), mask(32n, 1n)), 11n),
    Word.and(32n, w2, shl_n(32n, mask(32n, 1n), 11n)), tcact(w2))
  e4 = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n,
        Word.and(32n, cmat(32n, w2), mask(32n, 5n)), x),
        Word.and(32n, w2, shl_n(32n, mask(32n, 1n), 11n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 5n), 12n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n))),
    shl_n(32n, Word.and(32n, ccoh(32n, w2), mask(32n, 6n)), 5n),
    Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 5n)), tccoh(w2))
  e5 = Equal.cong(Word(32n), Word(32n),
    x => Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n, x,
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 5n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 1n), 11n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 5n), 12n))),
        Word.and(32n, w2, shl_n(32n, mask(32n, 6n), 17n))),
    Word.and(32n, cmat(32n, w2), mask(32n, 5n)),
    Word.and(32n, w2, mask(32n, 5n)), tcmat(w2))
  t12 = Equal.trans(Word(32n), model_cell(32n, w2), p1, p2, e1, e2)
  t34 = Equal.trans(Word(32n), p2, p3, p4, e3, e4)
  t15 = Equal.trans(Word(32n), model_cell(32n, w2), p2, p4, t12, t34)
  t5 = Equal.trans(Word(32n), model_cell(32n, w2), p4, p5, t15, e5)
  Equal.trans(Word(32n), model_cell(32n, w2),
    Word.and(32n, w2, Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n, mask(32n, 5n), shl_n(32n, mask(32n, 6n), 5n)), shl_n(32n, mask(32n, 1n), 11n)), shl_n(32n, mask(32n, 5n), 12n)), shl_n(32n, mask(32n, 6n), 17n))),
    Word.and(32n, w2, mask(32n, 23n)),
    Equal.trans(Word(32n), model_cell(32n, w2), p5,
      Word.and(32n, w2, Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n, mask(32n, 5n), shl_n(32n, mask(32n, 6n), 5n)), shl_n(32n, mask(32n, 1n), 11n)), shl_n(32n, mask(32n, 5n), 12n)), shl_n(32n, mask(32n, 6n), 17n))),
      t5,
      factor5(32n, w2, mask(32n, 5n), shl_n(32n, mask(32n, 6n), 5n), shl_n(32n, mask(32n, 1n), 11n), shl_n(32n, mask(32n, 5n), 12n), shl_n(32n, mask(32n, 6n), 17n))),
    Equal.cong(Word(32n), Word(32n), x => Word.and(32n, w2, x),
        Word.or(32n, Word.or(32n, Word.or(32n, Word.or(32n, mask(32n, 5n), shl_n(32n, mask(32n, 6n), 5n)), shl_n(32n, mask(32n, 1n), 11n)), shl_n(32n, mask(32n, 5n), 12n)), shl_n(32n, mask(32n, 6n), 17n)),
        mask(32n, 23n), mask_cell()))

def shr_pad_and(+p: Nat, +at: Word(p), +bt: Word(p)) -> {Word.shr.pad(p, Word.and(p, at, bt)) == Word.and(1n+p, Word.shr.pad(p, at), Word.shr.pad(p, bt)) : Word(1n+p)}:
  match p:
    case 0n:
      match at bt:
        case WNil{} WNil{}:
          {==}
    case 1n+q:
      match at bt:
        case WCon{ath, att} WCon{bth, btt}:
          Equal.cong(Word(1n+q), Word(1n+(1n+q)), t => WCon{Bool.and(ath, bth), t},
            Word.shr.pad(q, Word.and(q, att, btt)),
            Word.and(1n+q, Word.shr.pad(q, att), Word.shr.pad(q, btt)),
            shr_pad_and(q, att, btt))

def shr_and(+n: Nat, +a: Word(n), +b: Word(n)) -> {Word.shr(n, Word.and(n, a, b)) == Word.and(n, Word.shr(n, a), Word.shr(n, b)) : Word(n)}:
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{ah, at} WCon{bh, bt}:
          shr_pad_and(p, at, bt)

def shr_n_and(+n: Nat, k: Nat, +a: Word(n), +b: Word(n)) -> {shr_n(n, k, Word.and(n, a, b)) == Word.and(n, shr_n(n, k, a), shr_n(n, k, b)) : Word(n)}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      Equal.trans(Word(n),
        shr_n(n, 1n+q, Word.and(n, a, b)),
        shr_n(n, q, Word.and(n, Word.shr(n, a), Word.shr(n, b))),
        Word.and(n, shr_n(n, 1n+q, a), shr_n(n, 1n+q, b)),
        Equal.cong(Word(n), Word(n), x => shr_n(n, q, x),
          Word.shr(n, Word.and(n, a, b)),
          Word.and(n, Word.shr(n, a), Word.shr(n, b)),
          shr_and(n, a, b)),
        shr_n_and(n, q, Word.shr(n, a), Word.shr(n, b)))

def shr_n_or(+n: Nat, k: Nat, +a: Word(n), +b: Word(n)) -> {shr_n(n, k, Word.or(n, a, b)) == Word.or(n, shr_n(n, k, a), shr_n(n, k, b)) : Word(n)}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      Equal.trans(Word(n),
        shr_n(n, 1n+q, Word.or(n, a, b)),
        shr_n(n, q, Word.or(n, Word.shr(n, a), Word.shr(n, b))),
        Word.or(n, shr_n(n, 1n+q, a), shr_n(n, 1n+q, b)),
        Equal.cong(Word(n), Word(n), x => shr_n(n, q, x),
          Word.shr(n, Word.or(n, a, b)),
          Word.or(n, Word.shr(n, a), Word.shr(n, b)),
          shr_or(n, a, b)),
        shr_n_or(n, q, Word.shr(n, a), Word.shr(n, b)))

def shr_pad_zero(+p: Nat) -> {Word.shr.pad(p, Word.zero(p)) == Word.zero(1n+p) : Word(1n+p)}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      Equal.cong(Word(1n+q), Word(1n+(1n+q)), t => WCon{False{}, t},
        Word.shr.pad(q, Word.zero(q)),
        Word.zero(1n+q),
        shr_pad_zero(q))

def shr_zero(+n: Nat) -> {Word.shr(n, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      shr_pad_zero(p)

def shr_n_zero(+n: Nat, k: Nat) -> {shr_n(n, k, Word.zero(n)) == Word.zero(n) : Word(n)}:
  match k:
    case 0n:
      {==}
    case 1n+q:
      Equal.trans(Word(n),
        shr_n(n, 1n+q, Word.zero(n)),
        shr_n(n, q, Word.zero(n)),
        Word.zero(n),
        Equal.cong(Word(n), Word(n), x => shr_n(n, q, x),
          Word.shr(n, Word.zero(n)),
          Word.zero(n),
          shr_zero(n)),
        shr_n_zero(n, q))

def shr_pad_shl_put(q: Nat, b: Bool, t: Word(q)) -> {Word.shr.pad(q, Word.shl.put(q, b, t)) == Word.and(1n+q, WCon{b, t}, mask(1n+q, q)) : Word(1n+q)}:
  match q:
    case 0n:
      Equal.sym(Word(1n+0n), WCon{Bool.and(b, False{}), WNil{}}, WCon{False{}, WNil{}},
        Equal.cong(Bool, Word(1n+0n), h => WCon{h, WNil{}}, Bool.and(b, False{}), False{}, b_and_false(b)))
    case 1n+r:
      match t:
        case WCon{v0, v1}:
          Equal.trans(Word(1n+(1n+r)),
            WCon{b, Word.shr.pad(r, Word.shl.put(r, v0, v1))},
            WCon{b, Word.and(1n+r, WCon{v0, v1}, mask(1n+r, r))},
            WCon{Bool.and(b, True{}), Word.and(1n+r, WCon{v0, v1}, mask(1n+r, r))},
            Equal.cong(Word(1n+r), Word(1n+(1n+r)), s => WCon{b, s},
              Word.shr.pad(r, Word.shl.put(r, v0, v1)),
              Word.and(1n+r, WCon{v0, v1}, mask(1n+r, r)),
              shr_pad_shl_put(r, v0, v1)),
            Equal.cong(Bool, Word(1n+(1n+r)), h => WCon{h, Word.and(1n+r, WCon{v0, v1}, mask(1n+r, r))},
              b, Bool.and(b, True{}), Equal.sym(Bool, Bool.and(b, True{}), b, b_and_true(b))))

def shr_shl_one(+p: Nat, +u: Word(1n+p)) -> {Word.shr(1n+p, Word.shl(1n+p, u)) == Word.and(1n+p, u, mask(1n+p, p)) : Word(1n+p)}:
  match p:
    case 0n:
      match u:
        case WCon{uh, ut}:
          match ut:
            case WNil{}:
              Equal.sym(Word(1n+0n), WCon{Bool.and(uh, False{}), WNil{}}, WCon{False{}, WNil{}},
                Equal.cong(Bool, Word(1n+0n), h => WCon{h, WNil{}}, Bool.and(uh, False{}), False{}, b_and_false(uh)))
    case 1n+q:
      match u:
        case WCon{uh, ut}:
          match ut:
            case WCon{ut0, utt}:
              Equal.trans(Word(1n+(1n+q)),
                WCon{uh, Word.shr.pad(q, Word.shl.put(q, ut0, utt))},
                WCon{uh, Word.and(1n+q, WCon{ut0, utt}, mask(1n+q, q))},
                WCon{Bool.and(uh, True{}), Word.and(1n+q, WCon{ut0, utt}, mask(1n+q, q))},
                Equal.cong(Word(1n+q), Word(1n+(1n+q)), s => WCon{uh, s},
                  Word.shr.pad(q, Word.shl.put(q, ut0, utt)),
                  Word.and(1n+q, WCon{ut0, utt}, mask(1n+q, q)),
                  shr_pad_shl_put(q, ut0, utt)),
                Equal.cong(Bool, Word(1n+(1n+q)), h => WCon{h, Word.and(1n+q, WCon{ut0, utt}, mask(1n+q, q))},
                  uh, Bool.and(uh, True{}), Equal.sym(Bool, Bool.and(uh, True{}), uh, b_and_true(uh))))

def and_ones(n: Nat, w: Word(n)) -> {Word.and(n, w, mask(n, n)) == w : Word(n)}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{wh, wt}:
          Equal.trans(Word(1n+p),
            WCon{Bool.and(wh, True{}), Word.and(p, wt, mask(p, p))},
            WCon{wh, Word.and(p, wt, mask(p, p))},
            WCon{wh, wt},
            Equal.cong(Bool, Word(1n+p), h => WCon{h, Word.and(p, wt, mask(p, p))},
              Bool.and(wh, True{}), wh, b_and_true(wh)),
            Equal.cong(Word(p), Word(1n+p), t => WCon{wh, t},
              Word.and(p, wt, mask(p, p)), wt, and_ones(p, wt)))


def mask_zero(n: Nat) -> {mask(n, 0n) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def not_eq_inv(+a: Bool, +b: Bool, +h: {Bool.not(a) == Bool.not(b) : Bool}) -> {a == b : Bool}:
  Equal.trans(Bool, a, Bool.not(Bool.not(a)), b,
    Equal.sym(Bool, Bool.not(Bool.not(a)), a, b_not_not(a)),
    Equal.trans(Bool, Bool.not(Bool.not(a)), Bool.not(Bool.not(b)), b,
      Equal.cong(Bool, Bool, t => Bool.not(t), Bool.not(a), Bool.not(b), h),
      b_not_not(b)))

def xor_cancel_left(+p: Bool, +a: Bool, +b: Bool, +h: {Bool.xor(p, a) == Bool.xor(p, b) : Bool}) -> {a == b : Bool}:
  match p:
    case False{}:
      h
    case True{}:
      not_eq_inv(a, b, h)

def shr_and_mask1_zero(+n: Nat, +X: Word(n))
  -> {Word.shr(n, Word.and(n, X, mask(n, 1n))) == Word.zero(n) : Word(n)}:
  match n:
    case 0n:
      match X:
        case WNil{}:
          {==}
    case 1n+p:
      match X:
        case WCon{h, t}:
          +e_m = Equal.cong(Word(p), Word(p), s => Word.and(p, t, s), mask(p, 0n), Word.zero(p), mask_zero(p))
          +e_and = Equal.trans(Word(p), Word.and(p, t, mask(p, 0n)), Word.and(p, t, Word.zero(p)), Word.zero(p),
            e_m, w_and_zero(p, t))
          +e = Equal.cong(Word(p), Word(1n+p), s => Word.shr.pad(p, s),
            Word.and(p, t, mask(p, 0n)), Word.zero(p), e_and)
          Equal.trans(Word(1n+p),
            Word.shr(1n+p, Word.and(1n+p, WCon{h, t}, mask(1n+p, 1n))),
            Word.shr.pad(p, Word.and(p, t, mask(p, 0n))),
            Word.zero(1n+p),
            {==},
            Equal.trans(Word(1n+p),
              Word.shr.pad(p, Word.and(p, t, mask(p, 0n))),
              Word.shr.pad(p, Word.zero(p)),
              Word.zero(1n+p),
              e,
              shr_pad_zero(p)))
