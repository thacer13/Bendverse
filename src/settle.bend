import Base
import ./nat.bend as NatL
import ./potential.bend as Pot
import ./grid.bend as Grid
import ./cell.bend as Cell

def app(xs: +List<Nat>, ys: +List<Nat>) -> +List<Nat>:
  List.append(&2, Nat, xs, ys)

def suml(xs: +List<Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(h, suml(t))

def suml_append(+xs: +List<Nat>, +ys: +List<Nat>) -> {suml(app(xs, ys)) == Nat.add(suml(xs), suml(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.trans(Nat,
        suml(app(h <> t, ys)),
        Nat.add(h, suml(app(t, ys))),
        Nat.add(Nat.add(h, suml(t)), suml(ys)),
        {==},
        Equal.trans(Nat,
          Nat.add(h, suml(app(t, ys))),
          Nat.add(h, Nat.add(suml(t), suml(ys))),
          Nat.add(Nat.add(h, suml(t)), suml(ys)),
          Equal.cong(Nat, Nat, x => Nat.add(h, x),
            suml(app(t, ys)),
            Nat.add(suml(t), suml(ys)),
            suml_append(t, ys)),
          Equal.sym(Nat,
            Nat.add(Nat.add(h, suml(t)), suml(ys)),
            Nat.add(h, Nat.add(suml(t), suml(ys))),
            NatL.n_add_assoc(h, suml(t), suml(ys)))))

def suml_mid(+l: +List<Nat>, +m: +List<Nat>, +r: +List<Nat>) -> {suml(app(l, app(m, r))) == Nat.add(suml(l), Nat.add(suml(m), suml(r))) : Nat}:
  Equal.trans(Nat,
    suml(app(l, app(m, r))),
    Nat.add(suml(l), suml(app(m, r))),
    Nat.add(suml(l), Nat.add(suml(m), suml(r))),
    suml_append(l, app(m, r)),
    Equal.cong(Nat, Nat, x => Nat.add(suml(l), x),
      suml(app(m, r)),
      Nat.add(suml(m), suml(r)),
      suml_append(m, r)))

def swap_add(+A: Nat, +R: Nat, +G: Nat) -> {Nat.add(Nat.add(A, R), G) == Nat.add(Nat.add(A, G), R) : Nat}:
  Equal.trans(Nat,
    Nat.add(Nat.add(A, R), G),
    Nat.add(A, Nat.add(R, G)),
    Nat.add(Nat.add(A, G), R),
    NatL.n_add_assoc(A, R, G),
    Equal.trans(Nat,
      Nat.add(A, Nat.add(R, G)),
      Nat.add(A, Nat.add(G, R)),
      Nat.add(Nat.add(A, G), R),
      Equal.cong(Nat, Nat, x => Nat.add(A, x), Nat.add(R, G), Nat.add(G, R), NatL.n_add_comm(R, G)),
      Equal.sym(Nat,
        Nat.add(Nat.add(A, G), R),
        Nat.add(A, Nat.add(G, R)),
        NatL.n_add_assoc(A, G, R))))

def replace_decreases(
  +l: +List<Nat>, +r: +List<Nat>, +before: +List<Nat>, +after: +List<Nat>, +G: Nat,
  +h: {Nat.add(suml(after), G) == suml(before) : Nat}
) -> {Nat.add(suml(app(l, app(after, r))), G) == suml(app(l, app(before, r))) : Nat}:
  +L = suml(l)
  +A = suml(after)
  +B = suml(before)
  +R = suml(r)
  +e1 = suml_mid(l, after, r)
  +e2 = suml_mid(l, before, r)
  +i1 = NatL.n_add_assoc(L, Nat.add(A, R), G)
  +i2 = swap_add(A, R, G)
  +i3 = Equal.cong(Nat, Nat, x => Nat.add(x, R), Nat.add(A, G), B, h)
  Equal.trans(Nat,
    Nat.add(suml(app(l, app(after, r))), G),
    Nat.add(Nat.add(L, Nat.add(A, R)), G),
    suml(app(l, app(before, r))),
    Equal.cong(Nat, Nat, x => Nat.add(x, G),
      suml(app(l, app(after, r))),
      Nat.add(L, Nat.add(A, R)),
      e1),
    Equal.trans(Nat,
      Nat.add(Nat.add(L, Nat.add(A, R)), G),
      Nat.add(L, Nat.add(B, R)),
      suml(app(l, app(before, r))),
      Equal.trans(Nat,
        Nat.add(Nat.add(L, Nat.add(A, R)), G),
        Nat.add(L, Nat.add(Nat.add(A, R), G)),
        Nat.add(L, Nat.add(B, R)),
        i1,
        Equal.cong(Nat, Nat, x => Nat.add(L, x),
          Nat.add(Nat.add(A, R), G),
          Nat.add(B, R),
          Equal.trans(Nat,
            Nat.add(Nat.add(A, R), G),
            Nat.add(Nat.add(A, G), R),
            Nat.add(B, R),
            i2,
            i3))),
      Equal.sym(Nat,
        suml(app(l, app(before, r))),
        Nat.add(L, Nat.add(B, R)),
        e2)))

def incs(xs: +List<Nat>) -> +List<Nat>:
  match xs:
    case Nil{}:
      Nil{}
    case h <> t:
      Nat.add(1n, h) <> incs(t)

def len(xs: +List<Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(1n, len(t))

def reorder_counts(+h: Nat, +lt: Nat, +st: Nat) -> {Nat.add(Nat.add(1n, h), Nat.add(lt, st)) == Nat.add(Nat.add(1n, lt), Nat.add(h, st)) : Nat}:
  +t1 = Nat.add(1n, Nat.add(h, Nat.add(lt, st)))
  +t2 = Nat.add(1n, Nat.add(Nat.add(h, lt), st))
  +t3 = Nat.add(1n, Nat.add(Nat.add(lt, h), st))
  +t4 = Nat.add(1n, Nat.add(lt, Nat.add(h, st)))
  +t5 = Nat.add(Nat.add(1n, lt), Nat.add(h, st))
  Equal.trans(Nat,
    Nat.add(Nat.add(1n, h), Nat.add(lt, st)),
    t1,
    t5,
    NatL.n_add_assoc(1n, h, Nat.add(lt, st)),
    Equal.trans(Nat, t1, t2, t5,
      Equal.cong(Nat, Nat, x => Nat.add(1n, x),
        Nat.add(h, Nat.add(lt, st)),
        Nat.add(Nat.add(h, lt), st),
        Equal.sym(Nat, Nat.add(Nat.add(h, lt), st), Nat.add(h, Nat.add(lt, st)), NatL.n_add_assoc(h, lt, st))),
      Equal.trans(Nat, t2, t3, t5,
        Equal.cong(Nat, Nat, x => Nat.add(1n, x),
          Nat.add(Nat.add(h, lt), st),
          Nat.add(Nat.add(lt, h), st),
          Equal.cong(Nat, Nat, x => Nat.add(x, st), Nat.add(h, lt), Nat.add(lt, h), NatL.n_add_comm(h, lt))),
        Equal.trans(Nat, t3, t4, t5,
          Equal.cong(Nat, Nat, x => Nat.add(1n, x),
            Nat.add(Nat.add(lt, h), st),
            Nat.add(lt, Nat.add(h, st)),
            NatL.n_add_assoc(lt, h, st)),
          Equal.sym(Nat, t5, t4, NatL.n_add_assoc(1n, lt, Nat.add(h, st)))))))

def suml_incs(+xs: +List<Nat>) -> {suml(incs(xs)) == Nat.add(len(xs), suml(xs)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      Equal.trans(Nat,
        suml(incs(h <> t)),
        Nat.add(Nat.add(1n, h), Nat.add(len(t), suml(t))),
        Nat.add(Nat.add(1n, len(t)), Nat.add(h, suml(t))),
        Equal.cong(Nat, Nat, x => Nat.add(Nat.add(1n, h), x),
          suml(incs(t)),
          Nat.add(len(t), suml(t)),
          suml_incs(t)),
        reorder_counts(h, len(t), suml(t)))

def burn(fuel: Nat, p: Nat) -> Nat:
  match fuel:
    case 0n:
      p
    case 1n+f:
      match p:
        case 0n:
          0n
        case 1n+q:
          burn(f, q)

def burn_exhausts(p: Nat) -> {burn(p, p) == 0n : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      burn_exhausts(q)

def suml1(+a: Nat) -> {suml([a]) == a : Nat}:
  NatL.n_add_zero_right(a)

def suml2(+a: Nat, +b: Nat) -> {suml([a, b]) == Nat.add(a, b) : Nat}:
  Equal.cong(Nat, Nat, x => Nat.add(a, x), Nat.add(b, 0n), b, NatL.n_add_zero_right(b))

def pick_cons(+h: Nat, +a: +List<Nat>, +b: +List<Nat>, +c: Bool) -> {Bool.pick(List<&2, Nat>, c, h <> a, h <> b) == h <> Bool.pick(List<&2, Nat>, c, a, b) : List<&2, Nat>}:
  match c:
    case False{}:
      {==}
    case True{}:
      {==}

def set_append(+l: +List<Nat>, +r: +List<Nat>, +n: Nat, +v: Nat) -> {List.set(&2, Nat, app(l, r), n, v) == Bool.pick(List<&2, Nat>, Nat.is_lt(n, len(l)), app(List.set(&2, Nat, l, n, v), r), app(l, List.set(&2, Nat, r, Nat.sub(n, len(l)), v))) : List<&2, Nat>}:
  match l n:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+p:
      {==}
    case h <> t 0n:
      {==}
    case +h <> +t 1n+ +p:
      +c = Nat.is_lt(p, len(t))
      +a = app(List.set(&2, Nat, t, p, v), r)
      +b = app(t, List.set(&2, Nat, r, Nat.sub(p, len(t)), v))
      Equal.trans(List<&2, Nat>,
        h <> List.set(&2, Nat, app(t, r), p, v),
        h <> Bool.pick(List<&2, Nat>, c, a, b),
        Bool.pick(List<&2, Nat>, c, h <> a, h <> b),
        Equal.cong(List<&2, Nat>, List<&2, Nat>, (x => h <> x),
          List.set(&2, Nat, app(t, r), p, v),
          Bool.pick(List<&2, Nat>, c, a, b),
          set_append(t, r, p, v)),
        Equal.sym(List<&2, Nat>,
          Bool.pick(List<&2, Nat>, c, h <> a, h <> b),
          h <> Bool.pick(List<&2, Nat>, c, a, b),
          pick_cons(h, a, b, c)))

def suml_cons_mid(+l: +List<Nat>, +x: Nat, +r: +List<Nat>) -> {suml(app(l, x <> r)) == Nat.add(suml(l), Nat.add(x, suml(r))) : Nat}:
  Equal.trans(Nat,
    suml(app(l, x <> r)),
    Nat.add(suml(l), Nat.add(Nat.add(x, 0n), suml(r))),
    Nat.add(suml(l), Nat.add(x, suml(r))),
    suml_mid(l, [x], r),
    Equal.cong(Nat, Nat, y => Nat.add(suml(l), y),
      Nat.add(Nat.add(x, 0n), suml(r)),
      Nat.add(x, suml(r)),
      Equal.cong(Nat, Nat, y => Nat.add(y, suml(r)), Nat.add(x, 0n), x, NatL.n_add_zero_right(x))))

def set_sum(+l: +List<Nat>, +x: Nat, +r: +List<Nat>, +v: Nat) -> {Nat.add(suml(app(l, v <> r)), x) == Nat.add(suml(app(l, x <> r)), v) : Nat}:
  +L = suml(l)
  +R = suml(r)
  +after = suml(app(l, v <> r))
  +before = suml(app(l, x <> r))
  +ea = suml_cons_mid(l, v, r)
  +eb = suml_cons_mid(l, x, r)
  Equal.trans(Nat,
    Nat.add(after, x),
    Nat.add(Nat.add(L, Nat.add(v, R)), x),
    Nat.add(before, v),
    Equal.cong(Nat, Nat, y => Nat.add(y, x), after, Nat.add(L, Nat.add(v, R)), ea),
    Equal.trans(Nat,
      Nat.add(Nat.add(L, Nat.add(v, R)), x),
      Nat.add(Nat.add(L, Nat.add(x, R)), v),
      Nat.add(before, v),
      NatL.n_add_mid_swap(L, x, v, R),
      Equal.cong(Nat, Nat, y => Nat.add(y, v),
        Nat.add(L, Nat.add(x, R)),
        before,
        Equal.sym(Nat, before, Nat.add(L, Nat.add(x, R)), eb))))

def fall_before(+D: Nat, +G: Nat, +L: Nat) -> +List<Nat>:
  [Pot.phi_up(Nat.add(D, G), L), Pot.phi(D, L)]

def fall_after(+D: Nat, +G: Nat, +L: Nat) -> +List<Nat>:
  [Pot.phi(Nat.add(D, G), L), Pot.phi_up(D, L)]

def swap_segment_decreases(+D: Nat, +G: Nat, +L: Nat) -> {Nat.add(suml(fall_after(D, G, L)), G) == suml(fall_before(D, G, L)) : Nat}:
  +Av = Pot.phi(Nat.add(D, G), L)
  +Bv = Pot.phi_up(D, L)
  +Cv = Pot.phi_up(Nat.add(D, G), L)
  +Dv = Pot.phi(D, L)
  Equal.trans(Nat,
    Nat.add(suml(fall_after(D, G, L)), G),
    Nat.add(Nat.add(Av, Bv), G),
    suml(fall_before(D, G, L)),
    Equal.cong(Nat, Nat, x => Nat.add(x, G), suml(fall_after(D, G, L)), Nat.add(Av, Bv), suml2(Av, Bv)),
    Equal.trans(Nat,
      Nat.add(Nat.add(Av, Bv), G),
      Nat.add(Cv, Dv),
      suml(fall_before(D, G, L)),
      Pot.fall_decreases(D, G, L),
      Equal.sym(Nat, suml(fall_before(D, G, L)), Nat.add(Cv, Dv), suml2(Cv, Dv))))

def fall_lowers_world(+l: +List<Nat>, +r: +List<Nat>, +D: Nat, +G: Nat, +L: Nat) -> {Nat.add(suml(app(l, app(fall_after(D, G, L), r))), G) == suml(app(l, app(fall_before(D, G, L), r))) : Nat}:
  replace_decreases(l, r, fall_before(D, G, L), fall_after(D, G, L), G, swap_segment_decreases(D, G, L))

def crumble_segment_decreases(+d: Nat, +G: Nat, +L: Nat) -> {Nat.add(suml([Pot.phi(d, L)]), Pot.phi(G, L)) == suml([Pot.phi(Nat.add(d, G), L)]) : Nat}:
  +p1 = Pot.phi(d, L)
  +pg = Pot.phi(G, L)
  +p2 = Pot.phi(Nat.add(d, G), L)
  Equal.trans(Nat,
    Nat.add(suml([p1]), pg),
    Nat.add(p1, pg),
    suml([p2]),
    Equal.cong(Nat, Nat, x => Nat.add(x, pg), suml([p1]), p1, suml1(p1)),
    Equal.trans(Nat,
      Nat.add(p1, pg),
      p2,
      suml([p2]),
      Pot.crumble_decreases(d, G, L),
      Equal.sym(Nat, suml([p2]), p2, suml1(p2))))

def crumble_lowers_world(+l: +List<Nat>, +r: +List<Nat>, +d: Nat, +G: Nat, +L: Nat) -> {Nat.add(suml(app(l, app([Pot.phi(d, L)], r))), Pot.phi(G, L)) == suml(app(l, app([Pot.phi(Nat.add(d, G), L)], r))) : Nat}:
  replace_decreases(l, r, [Pot.phi(Nat.add(d, G), L)], [Pot.phi(d, L)], Pot.phi(G, L), crumble_segment_decreases(d, G, L))


def pot_at(+w: U32, +i: U32) -> Nat:
  Nat.mul(Pot.dens(Cell.material(w)), U32.to_nat(Grid.iy(i)))

def to_pots(a: Array<U32>, +base: U32, n: U32) -> +List<Nat>:
  match a:
    case ALeaf{x}:
      [pot_at(x, base)]
    case ANode{xs, ys}:
      +h = U32.shr(n)
      app(to_pots(xs, base, h), to_pots(ys, U32.add(base, h), h))

def size_got(p: Array<U32> & U32) -> U32:
  match p:
    case (_, n):
      n

def phi_got(p: Array<U32> & U32) -> Nat:
  match p:
    case (a, n):
      suml(to_pots(a, 0, n))

def array_phi(a: Array<U32>) -> Nat:
  phi_got(Array.size(U32, a))

def to_pots_node(xs: Array<U32>, ys: Array<U32>, +base: U32, +n: U32) -> {suml(to_pots(ANode{xs, ys}, base, n)) == Nat.add(suml(to_pots(xs, base, U32.shr(n))), suml(to_pots(ys, U32.add(base, U32.shr(n)), U32.shr(n)))) : Nat}:
  suml_append(to_pots(xs, base, U32.shr(n)), to_pots(ys, U32.add(base, U32.shr(n)), U32.shr(n)))

