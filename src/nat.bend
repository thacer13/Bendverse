import Base

def n_add_zero_right(a: Nat) -> {a + 0n == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %n_add_zero_right(p) : {1n + Nat.add(p, 0n) == 1n + _ : Nat}
      {==}

def n_add_succ_right(a: Nat, b: Nat) -> {a + (1n + b) == 1n + (a + b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      %n_add_succ_right(q, b) : {1n + (q + (1n + b)) == 1n + _ : Nat}
      {==}

def n_add_assoc(a: Nat, b: Nat, c: Nat) -> {(a + b) + c == a + (b + c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %n_add_assoc(p, b, c) : {1n + ((p + b) + c) == 1n + _ : Nat}
      {==}

def n_add_comm(a: Nat, +b: Nat) -> {a + b == b + a : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, n_add_zero_right(b))
    case 1n+p:
      +q = p
      %Equal.sym(Nat, Nat.add(q, b), Nat.add(b, q), n_add_comm(q, b)) : {1n + _ == b + (1n + q) : Nat}
      %n_add_succ_right(b, q) : {_ == b + (1n + q) : Nat}
      {==}

def n_mul_zero_right(a: Nat) -> {a * 0n == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %n_mul_zero_right(p) : {Nat.mul(p, 0n) == _ : Nat}
      {==}

def n_mul_distrib_left(a: Nat, +b: Nat, +c: Nat) -> {(a + b) * c == (a * c) + (b * c) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +q = p
      Equal.trans(Nat,
        Nat.add(c, Nat.mul(Nat.add(q, b), c)),
        Nat.add(c, Nat.add(Nat.mul(q, c), Nat.mul(b, c))),
        Nat.add(Nat.add(c, Nat.mul(q, c)), Nat.mul(b, c)),
        Equal.cong(Nat, Nat, x => Nat.add(c, x),
          Nat.mul(Nat.add(q, b), c), Nat.add(Nat.mul(q, c), Nat.mul(b, c)),
          n_mul_distrib_left(q, b, c)),
        Equal.sym(Nat,
          Nat.add(Nat.add(c, Nat.mul(q, c)), Nat.mul(b, c)),
          Nat.add(c, Nat.add(Nat.mul(q, c), Nat.mul(b, c))),
          n_add_assoc(c, Nat.mul(q, c), Nat.mul(b, c))))

def n_mul_succ_right(a: Nat, +b: Nat) -> {a * (1n + b) == (a * b) + a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      +q = p
      Equal.trans(Nat,
        Nat.add(Nat.add(1n, b), Nat.mul(q, Nat.add(1n, b))),
        Nat.add(Nat.add(1n, b), Nat.add(Nat.mul(q, b), q)),
        Nat.add(Nat.add(b, Nat.mul(q, b)), Nat.add(1n, q)),
        Equal.cong(Nat, Nat, x => Nat.add(Nat.add(1n, b), x),
          Nat.mul(q, Nat.add(1n, b)), Nat.add(Nat.mul(q, b), q),
          n_mul_succ_right(q, b)),
        Equal.trans(Nat,
          Nat.add(Nat.add(1n, b), Nat.add(Nat.mul(q, b), q)),
          Nat.add(1n, Nat.add(b, Nat.add(Nat.mul(q, b), q))),
          Nat.add(Nat.add(b, Nat.mul(q, b)), Nat.add(1n, q)),
          n_add_assoc(1n, b, Nat.add(Nat.mul(q, b), q)),
          Equal.trans(Nat,
            Nat.add(1n, Nat.add(b, Nat.add(Nat.mul(q, b), q))),
            Nat.add(1n, Nat.add(Nat.add(b, Nat.mul(q, b)), q)),
            Nat.add(Nat.add(b, Nat.mul(q, b)), Nat.add(1n, q)),
            Equal.cong(Nat, Nat, x => Nat.add(1n, x),
              Nat.add(b, Nat.add(Nat.mul(q, b), q)), Nat.add(Nat.add(b, Nat.mul(q, b)), q),
              Equal.sym(Nat, Nat.add(Nat.add(b, Nat.mul(q, b)), q), Nat.add(b, Nat.add(Nat.mul(q, b), q)), n_add_assoc(b, Nat.mul(q, b), q))),
            Equal.sym(Nat,
              Nat.add(Nat.add(b, Nat.mul(q, b)), Nat.add(1n, q)),
              Nat.add(1n, Nat.add(Nat.add(b, Nat.mul(q, b)), q)),
              n_add_succ_right(Nat.add(b, Nat.mul(q, b)), q)))))

def n_add_mid_swap(+L: Nat, +x: Nat, +v: Nat, +R: Nat) -> {Nat.add(Nat.add(L, Nat.add(v, R)), x) == Nat.add(Nat.add(L, Nat.add(x, R)), v) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(L, Nat.add(v, R)), x),
    Nat.add(L, Nat.add(Nat.add(v, R), x)),
    Nat.add(Nat.add(L, Nat.add(x, R)), v),
    n_add_assoc(L, Nat.add(v, R), x),
    Equal.trans(Nat,
      Nat.add(L, Nat.add(Nat.add(v, R), x)),
      Nat.add(L, Nat.add(v, Nat.add(x, R))),
      Nat.add(Nat.add(L, Nat.add(x, R)), v),
      Equal.cong(Nat, Nat, y => Nat.add(L, y),
        Nat.add(Nat.add(v, R), x),
        Nat.add(v, Nat.add(x, R)),
        Equal.trans(Nat,
          Nat.add(Nat.add(v, R), x),
          Nat.add(v, Nat.add(R, x)),
          Nat.add(v, Nat.add(x, R)),
          n_add_assoc(v, R, x),
          Equal.cong(Nat, Nat, y => Nat.add(v, y), Nat.add(R, x), Nat.add(x, R), n_add_comm(R, x)))),
      Equal.trans(Nat,
        Nat.add(L, Nat.add(v, Nat.add(x, R))),
        Nat.add(L, Nat.add(Nat.add(x, R), v)),
        Nat.add(Nat.add(L, Nat.add(x, R)), v),
        Equal.cong(Nat, Nat, y => Nat.add(L, y),
          Nat.add(v, Nat.add(x, R)),
          Nat.add(Nat.add(x, R), v),
          n_add_comm(v, Nat.add(x, R))),
        Equal.sym(Nat,
          Nat.add(Nat.add(L, Nat.add(x, R)), v),
          Nat.add(L, Nat.add(Nat.add(x, R), v)),
          n_add_assoc(L, Nat.add(x, R), v)))))

def n_sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def n_not_lt_zero(a: Nat) -> {Nat.is_lt(a, 0n) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}
