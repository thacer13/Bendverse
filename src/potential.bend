import Base
import ./cell.bend as Cell
import ./nat.bend as NatL

def dens(m: U32) -> Nat:
  U32.to_nat(Cell.density(m))

def dens_empty() -> {dens(Cell.empty()) == 0n : Nat}:
  {==}

def dens_water() -> {dens(Cell.water()) == 80n : Nat}:
  {==}

def dens_sand() -> {dens(Cell.sand()) == 100n : Nat}:
  {==}

def dens_rubble() -> {dens(Cell.rubble()) == 150n : Nat}:
  {==}

def dens_rock() -> {dens(Cell.rock()) == 200n : Nat}:
  {==}

def phi(d: Nat, L: Nat) -> Nat:
  Nat.mul(d, L)

def phi_up(+d: Nat, L: Nat) -> Nat:
  Nat.add(Nat.mul(d, L), d)

def phi_up_eq(+d: Nat, +L: Nat) -> {phi_up(d, L) == Nat.mul(d, 1n + L) : Nat}:
  Equal.sym(Nat, Nat.mul(d, 1n + L), phi_up(d, L), NatL.n_mul_succ_right(d, L))

def rotate2(+D: Nat, +G: Nat, +Y: Nat) -> {(Y + D) + G == (D + G) + Y : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(Y, D), G),
    Nat.add(Nat.add(D, Y), G),
    Nat.add(Nat.add(D, G), Y),
    Equal.cong(Nat, Nat, x => Nat.add(x, G), Nat.add(Y, D), Nat.add(D, Y), NatL.n_add_comm(Y, D)),
    Equal.trans(Nat,
      Nat.add(Nat.add(D, Y), G),
      Nat.add(D, Nat.add(Y, G)),
      Nat.add(Nat.add(D, G), Y),
      NatL.n_add_assoc(D, Y, G),
      Equal.trans(Nat,
        Nat.add(D, Nat.add(Y, G)),
        Nat.add(D, Nat.add(G, Y)),
        Nat.add(Nat.add(D, G), Y),
        Equal.cong(Nat, Nat, x => Nat.add(D, x), Nat.add(Y, G), Nat.add(G, Y), NatL.n_add_comm(Y, G)),
        Equal.sym(Nat, Nat.add(Nat.add(D, G), Y), Nat.add(D, Nat.add(G, Y)), NatL.n_add_assoc(D, G, Y)))))

def fall_decreases(+D: Nat, +G: Nat, +L: Nat) -> {Nat.add(Nat.add(phi(Nat.add(D, G), L), phi_up(D, L)), G) == Nat.add(phi_up(Nat.add(D, G), L), phi(D, L)) : Nat}:
  +X = Nat.mul(Nat.add(D, G), L)
  +Y = Nat.mul(D, L)
  Equal.trans(Nat,
    Nat.add(Nat.add(X, Nat.add(Y, D)), G),
    Nat.add(X, Nat.add(Nat.add(D, G), Y)),
    Nat.add(Nat.add(X, Nat.add(D, G)), Y),
    Equal.trans(Nat,
      Nat.add(Nat.add(X, Nat.add(Y, D)), G),
      Nat.add(X, Nat.add(Nat.add(Y, D), G)),
      Nat.add(X, Nat.add(Nat.add(D, G), Y)),
      NatL.n_add_assoc(X, Nat.add(Y, D), G),
      Equal.cong(Nat, Nat, x => Nat.add(X, x), Nat.add(Nat.add(Y, D), G), Nat.add(Nat.add(D, G), Y), rotate2(D, G, Y))),
    Equal.sym(Nat, Nat.add(Nat.add(X, Nat.add(D, G)), Y), Nat.add(X, Nat.add(Nat.add(D, G), Y)), NatL.n_add_assoc(X, Nat.add(D, G), Y)))

def crumble_decreases(+d: Nat, +G: Nat, +L: Nat) -> {Nat.add(Nat.mul(d, L), Nat.mul(G, L)) == Nat.mul(Nat.add(d, G), L) : Nat}:
  Equal.sym(Nat, Nat.mul(Nat.add(d, G), L), Nat.add(Nat.mul(d, L), Nat.mul(G, L)), NatL.n_mul_distrib_left(d, G, L))

def spend(k: Nat, +m: Nat) -> Nat:
  match k:
    case 0n:
      m
    case 1n+p:
      spend(p, Nat.sub(m, 1n))

def spend_exhausts(m: Nat) -> {spend(m, m) == 0n : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      +q = p
      Equal.trans(Nat,
        spend(q, Nat.sub(q, 0n)),
        spend(q, q),
        0n,
        Equal.cong(Nat, Nat, x => spend(q, x), Nat.sub(q, 0n), q, NatL.n_sub_zero(q)),
        spend_exhausts(q))
