import Base

def n_add_zero_right(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %n_add_zero_right(p) : {Nat.add(1n, Nat.add(p, 0n)) == Nat.add(1n, _) : Nat}
      {==}

def n_add_succ_right(a: Nat, b: Nat) -> {Nat.add(a, Nat.add(1n, b)) == Nat.add(1n, Nat.add(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+q:
      %n_add_succ_right(q, b) : {Nat.add(1n, Nat.add(q, Nat.add(1n, b))) == Nat.add(1n, _) : Nat}
      {==}

def n_add_assoc(a: Nat, b: Nat, c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %n_add_assoc(p, b, c) : {Nat.add(1n, Nat.add(Nat.add(p, b), c)) == Nat.add(1n, _) : Nat}
      {==}

def n_add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, n_add_zero_right(b))
    case 1n+p:
      +q = p
      %Equal.sym(Nat, Nat.add(q, b), Nat.add(b, q), n_add_comm(q, b)) : {Nat.add(1n, _) == Nat.add(b, Nat.add(1n, q)) : Nat}
      %n_add_succ_right(b, q) : {_ == Nat.add(b, Nat.add(1n, q)) : Nat}
      {==}

def n_mul_zero_right(a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %n_mul_zero_right(p) : {Nat.mul(p, 0n) == _ : Nat}
      {==}

def n_mul_distrib_left(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
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

def n_mul_succ_right(a: Nat, +b: Nat) -> {Nat.mul(a, Nat.add(1n, b)) == Nat.add(Nat.mul(a, b), a) : Nat}:
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

def n_sub_add(+a: Nat, c: Nat) -> {Nat.sub(Nat.add(a, c), c) == a : Nat}:
  match c:
    case 0n:
      Equal.trans(Nat, Nat.sub(Nat.add(a, 0n), 0n), Nat.add(a, 0n), a,
        n_sub_zero(Nat.add(a, 0n)),
        n_add_zero_right(a))
    case 1n+ +p:
      Equal.trans(Nat,
        Nat.sub(Nat.add(a, Nat.add(1n, p)), Nat.add(1n, p)),
        Nat.sub(Nat.add(1n, Nat.add(a, p)), Nat.add(1n, p)),
        a,
        Equal.cong(Nat, Nat, x => Nat.sub(x, Nat.add(1n, p)), Nat.add(a, Nat.add(1n, p)), Nat.add(1n, Nat.add(a, p)), n_add_succ_right(a, p)),
        n_sub_add(a, p))

def n_add_cancel_right(a: Nat, +b: Nat, +c: Nat, +h: {Nat.add(a, c) == Nat.add(b, c) : Nat}) -> {a == b : Nat}:
  Equal.trans(Nat, a, Nat.sub(Nat.add(a, c), c), b,
    Equal.sym(Nat, Nat.sub(Nat.add(a, c), c), a, n_sub_add(a, c)),
    Equal.trans(Nat, Nat.sub(Nat.add(a, c), c), Nat.sub(Nat.add(b, c), c), b,
      Equal.cong(Nat, Nat, x => Nat.sub(x, c), Nat.add(a, c), Nat.add(b, c), h),
      n_sub_add(b, c)))

# Truncated subtraction recovers the difference under an order hypothesis:
# `b + (a - b) = a` when `a >= b`. The `0n / 1n+p` case is unreachable (its
# hypothesis is `{False == True}`), but Base has no false-elimination primitive;
# `Equal.cong` with a `Bool.pick` motive transports the contradiction to the goal
# (`f(False)` is the left side, `f(True)` the right). This is the same trick
# `Word.cmp` reflection uses for its impossible `LT`/`GT` branches (A.37, A.54).
def n_add_sub_le(a: Nat, b: Nat, h: {Nat.is_ge(a, b) == True{} : Bool})
  -> {Nat.add(b, Nat.sub(a, b)) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      Equal.cong(Bool, Nat,
        z => Bool.pick(Nat, z, 0n, Nat.add(Nat.add(1n, p), Nat.sub(0n, Nat.add(1n, p)))),
        False{}, True{}, h)
    case 1n+q 0n:
      {==}
    case 1n+q 1n+p:
      Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.add(p, Nat.sub(q, p)), q, n_add_sub_le(q, p, h))

# ------------------------------------------------------------------ mod range
# SCALE.md step 5 / PLAN `G-scale-2`. `Dirtyn.dwin_up`/`dwin_down` wrap a row
# index with `Nat.mod`, and the `mark_wake` reach laws need the wrap result to be
# in range (`Nat.is_lt(_, w)`). Base exposes no `Nat.mod` range lemma, so the
# bound is developed here from `Nat.divmod.go`'s loop invariant.
#
# `divmod.go(n, m, d, r)` counts `r` up from 0 while `m` counts down; when `m`
# hits 0 it resets to `(m := r, r := 0)` and bumps the quotient `d`. So `m + r`
# is the invariant (it is `b - 1` when started at `m = b - 1`, `d = r = 0`), and
# the returned remainder is at most `m + r`.

# `a < a + (1 + b)`: the successor bound, structural in `a`.
def n_lt_add_succ(a: Nat, +b: Nat)
  -> {Nat.is_lt(a, Nat.add(a, Nat.add(1n, b))) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      n_lt_add_succ(p, b)

# `divmod.go`'s remainder is `< 1 + (m + r)`, by induction on `n`.
def go_rem_le(n: Nat, +m: Nat, +d: Nat, +r: Nat)
  -> {Nat.is_lt(Nat.mod.fin(Nat.divmod.go(n, m, d, r)), Nat.add(1n, Nat.add(m, r))) == True{} : Bool}:
  match n:
    case 0n:
      +hb = Equal.trans(Nat,
        Nat.add(1n, Nat.add(m, r)),
        Nat.add(1n, Nat.add(r, m)),
        Nat.add(r, Nat.add(1n, m)),
        Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.add(m, r), Nat.add(r, m), n_add_comm(m, r)),
        Equal.sym(Nat, Nat.add(r, Nat.add(1n, m)), Nat.add(1n, Nat.add(r, m)), n_add_succ_right(r, m)))
      Equal.trans(Bool,
        Nat.is_lt(r, Nat.add(1n, Nat.add(m, r))),
        Nat.is_lt(r, Nat.add(r, Nat.add(1n, m))),
        True{},
        Equal.cong(Nat, Bool, z => Nat.is_lt(r, z), Nat.add(1n, Nat.add(m, r)), Nat.add(r, Nat.add(1n, m)), hb),
        n_lt_add_succ(r, m))
    case 1n+np:
      match m:
        case 0n:
          +hb = Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.add(0n, r), Nat.add(r, 0n),
            Equal.sym(Nat, Nat.add(r, 0n), Nat.add(0n, r), n_add_zero_right(r)))
          Equal.trans(Bool,
            Nat.is_lt(Nat.mod.fin(Nat.divmod.go(np, r, Nat.add(1n, d), 0n)), Nat.add(1n, Nat.add(0n, r))),
            Nat.is_lt(Nat.mod.fin(Nat.divmod.go(np, r, Nat.add(1n, d), 0n)), Nat.add(1n, Nat.add(r, 0n))),
            True{},
            Equal.cong(Nat, Bool, z => Nat.is_lt(Nat.mod.fin(Nat.divmod.go(np, r, Nat.add(1n, d), 0n)), z), Nat.add(1n, Nat.add(0n, r)), Nat.add(1n, Nat.add(r, 0n)), hb),
            go_rem_le(np, r, Nat.add(1n, d), 0n))
        case 1n+mp:
          +hb = Equal.sym(Nat,
            Nat.add(1n, Nat.add(mp, Nat.add(1n, r))),
            Nat.add(1n, Nat.add(Nat.add(1n, mp), r)),
            Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.add(mp, Nat.add(1n, r)), Nat.add(Nat.add(1n, mp), r), n_add_succ_right(mp, r)))
          Equal.trans(Bool,
            Nat.is_lt(Nat.mod.fin(Nat.divmod.go(np, mp, d, Nat.add(1n, r))), Nat.add(1n, Nat.add(Nat.add(1n, mp), r))),
            Nat.is_lt(Nat.mod.fin(Nat.divmod.go(np, mp, d, Nat.add(1n, r))), Nat.add(1n, Nat.add(mp, Nat.add(1n, r)))),
            True{},
            Equal.cong(Nat, Bool, z => Nat.is_lt(Nat.mod.fin(Nat.divmod.go(np, mp, d, Nat.add(1n, r))), z), Nat.add(1n, Nat.add(Nat.add(1n, mp), r)), Nat.add(1n, Nat.add(mp, Nat.add(1n, r))), hb),
            go_rem_le(np, mp, d, Nat.add(1n, r)))

# `Nat.mod(a, 1 + b) < 1 + b` (the divisor is positive).
def n_mod_lt(a: Nat, +b: Nat)
  -> {Nat.is_lt(Nat.mod(a, Nat.add(1n, b)), Nat.add(1n, b)) == True{} : Bool}:
  +hb = Equal.sym(Nat, Nat.add(1n, Nat.add(b, 0n)), Nat.add(1n, b),
    Equal.cong(Nat, Nat, x => Nat.add(1n, x), Nat.add(b, 0n), b, n_add_zero_right(b)))
  Equal.trans(Bool,
    Nat.is_lt(Nat.mod(a, Nat.add(1n, b)), Nat.add(1n, b)),
    Nat.is_lt(Nat.mod(a, Nat.add(1n, b)), Nat.add(1n, Nat.add(b, 0n))),
    True{},
    Equal.cong(Nat, Bool, z => Nat.is_lt(Nat.mod(a, Nat.add(1n, b)), z), Nat.add(1n, b), Nat.add(1n, Nat.add(b, 0n)), hb),
    go_rem_le(a, b, 0n, 0n))
