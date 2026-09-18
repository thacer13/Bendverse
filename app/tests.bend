import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/worldgen.bend as Worldgen
import ../src/parity.bend as Parity
import ../src/priority.bend as Priority
import ../src/settle.bend as Settle

def is_bad(z: Bool) -> U32:
  match z:
    case True{}:
      0
    case False{}:
      1

def inc_if_false(z: Bool, bad: U32) -> U32:
  match z:
    case True{}:
      bad
    case False{}:
      U32.add(bad, 1)

def report(+name: String, +bad: U32) -> IO(Unit):
  do IO<Unit>:
    z : Bool = U32.is_eq(bad, 0)
    IO.print(Bool.pick(String, z, "PASS " ++ name, "FAIL " ++ name ++ " (" ++ U32.show(bad) ++ ")"))

def index_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      j = Grid.index(Grid.ix(i), Grid.iy(i), Grid.iz(i))
      ok = U32.is_eq(j, i)
      bad2 = inc_if_false(ok, bad)
      index_go(p, U32.add(i, 1), bad2)

def index_bad() -> U32:
  index_go(U32.to_nat(262144), 0, 0)

def cell_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +mat = U32.mod(i, 6)
      +coh = U32.mod(i, 64)
      +act = U32.mod(i, 2)
      +sup = U32.mod(i, 32)
      +fl = U32.mod(i, 64)
      +w = Cell.encode(mat, coh, act, sup, fl)
      okm = U32.is_eq(Cell.material(w), mat)
      okc = U32.is_eq(Cell.cohesion(w), coh)
      oka = U32.is_eq(Cell.active(w), act)
      oks = U32.is_eq(Cell.support(w), sup)
      okf = U32.is_eq(Cell.fall(w), fl)
      okr = U32.is_eq(Cell.reencode(w), w)
      all = Bool.and(Bool.and(Bool.and(Bool.and(okm, okc), Bool.and(oka, oks)), okf), okr)
      bad2 = inc_if_false(all, bad)
      cell_go(p, U32.add(i, 1), bad2)

def cell_bad() -> U32:
  cell_go(U32.to_nat(4096), 0, 0)

def gen_det_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +x = Grid.ix(i)
      +y = Grid.iy(i)
      +z = Grid.iz(i)
      a = Worldgen.gen(x, y, z, 42)
      b = Worldgen.gen(x, y, z, 42)
      bad2 = inc_if_false(U32.is_eq(a, b), bad)
      gen_det_go(p, U32.add(i, 1), bad2)

def gen_det_bad() -> U32:
  gen_det_go(U32.to_nat(4096), 0, 0)

def terrain_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +x = U32.add(U32.mod(Grid.ix(i), 62), 1)
      +z = U32.add(U32.mod(Grid.iz(i), 62), 1)
      +gy = Worldgen.height(x, z, 42)
      m1 = Cell.material(Worldgen.gen(x, gy, z, 42))
      m2 = Cell.material(Worldgen.gen(x, U32.add(gy, 1), z, 42))
      m3 = Cell.material(Worldgen.gen(x, 3, z, 42))
      mb = Cell.material(Worldgen.gen(0, gy, z, 42))
      o1 = U32.is_eq(m1, 2)
      o2 = U32.is_eq(m2, 0)
      o3 = U32.is_eq(m3, 3)
      o4 = U32.is_eq(mb, 1)
      all = Bool.and(Bool.and(o1, o2), Bool.and(o3, o4))
      bad2 = inc_if_false(all, bad)
      terrain_go(p, U32.add(i, 1), bad2)

def terrain_bad() -> U32:
  terrain_go(U32.to_nat(4096), 0, 0)

def build_go(fuel: Nat, +i: U32, cells: List<U32>, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      match cells:
        case Nil{}:
          bad
        case Con{h, t}:
          g = Worldgen.gen(Grid.ix(i), Grid.iy(i), Grid.iz(i), 42)
          build_go(p, U32.add(i, 1), t, inc_if_false(U32.is_eq(h, g), bad))

def build_bad() -> U32:
  build_go(U32.to_nat(262144), 0, Grid.to_list(Worldgen.build()), 0)

def bool_eq(a: Bool, b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

def parity_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      o1 = bool_eq(Parity.par32(U32.add(i, 1)), Bool.not(Parity.par32(i)))
      o2 = bool_eq(Parity.par32(U32.add(i, 4294967295)), Bool.not(Parity.par32(i)))
      o3 = bool_eq(Parity.par32(Grid.ix(Grid.neighbor(i, i, 0, 0))), Bool.xor(Parity.par32(Grid.ix(i)), Parity.par32(i)))
      o4 = bool_eq(Parity.par32(Grid.iy(Grid.neighbor(i, 0, i, 0))), Bool.xor(Parity.par32(Grid.iy(i)), Parity.par32(i)))
      o5 = bool_eq(Parity.par32(Grid.iz(Grid.neighbor(i, 0, 0, i))), Bool.xor(Parity.par32(Grid.iz(i)), Parity.par32(i)))
      all = Bool.and(Bool.and(Bool.and(Bool.and(o1, o2), o3), o4), o5)
      parity_go(p, U32.add(i, 1), inc_if_false(all, bad))

def parity_bad() -> U32:
  parity_go(U32.to_nat(4096), 0, 0)

def mod_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +a = i
      +b = U32.mul(i, 2654435761)
      o1 = U32.is_eq(U32.and(U32.add(a, b), 63), U32.and(U32.add(U32.and(a, 63), U32.and(b, 63)), 63))
      o2 = U32.is_eq(U32.add(U32.add(a, 1), 4294967295), a)
      o3 = U32.is_eq(U32.add(U32.add(a, 4294967295), 1), a)
      all = Bool.and(o1, Bool.and(o2, o3))
      mod_go(p, U32.add(i, 1), inc_if_false(all, bad))

def mod_bad() -> U32:
  mod_go(U32.to_nat(4096), 0, 0)

def phi_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +x = U32.mul(i, 2654435761)
      o0 = U32.is_eq(Priority.phi(Priority.dir_neg(Priority.Dno{}), Priority.phi(Priority.Dno{}, x)), U32.and(x, 63))
      o1 = U32.is_eq(Priority.phi(Priority.dir_neg(Priority.Dup{}), Priority.phi(Priority.Dup{}, x)), U32.and(x, 63))
      o2 = U32.is_eq(Priority.phi(Priority.dir_neg(Priority.Ddn{}), Priority.phi(Priority.Ddn{}, x)), U32.and(x, 63))
      all = Bool.and(o0, Bool.and(o1, o2))
      phi_go(p, U32.add(i, 1), inc_if_false(all, bad))

def phi_bad() -> U32:
  phi_go(U32.to_nat(4096), 0, 0)

def nc_check(+i: U32, +a: Priority.Dir, +b: Priority.Dir, +c: Priority.Dir) -> Bool:
  U32.is_eq(
    Grid.neighbor(Grid.neighbor(i, Priority.dir_val(a), Priority.dir_val(b), Priority.dir_val(c)),
      Priority.dir_val(Priority.dir_neg(a)), Priority.dir_val(Priority.dir_neg(b)), Priority.dir_val(Priority.dir_neg(c))),
    U32.and(i, 262143))

def nc_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      o0 = nc_check(i, Priority.Dno{}, Priority.Dup{}, Priority.Ddn{})
      o1 = nc_check(i, Priority.Dup{}, Priority.Ddn{}, Priority.Dno{})
      o2 = nc_check(i, Priority.Ddn{}, Priority.Dno{}, Priority.Dup{})
      o3 = nc_check(i, Priority.Dup{}, Priority.Dup{}, Priority.Dup{})
      o4 = nc_check(i, Priority.Ddn{}, Priority.Ddn{}, Priority.Ddn{})
      o5 = nc_check(i, Priority.Dno{}, Priority.Dno{}, Priority.Dno{})
      all = Bool.and(Bool.and(Bool.and(o0, o1), Bool.and(o2, o3)), Bool.and(o4, o5))
      nc_go(p, U32.add(i, 1), inc_if_false(all, bad))

def nc_bad() -> U32:
  nc_go(U32.to_nat(4096), 0, 0)

def total_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +b = U32.mul(i, 2654435761)
      all = Bool.or(Bool.or(U32.is_lt(i, b), U32.is_gt(i, b)), U32.is_eq(i, b))
      total_go(p, U32.add(i, 1), inc_if_false(all, bad))

def total_bad() -> U32:
  total_go(U32.to_nat(4096), 0, 0)

def nlist_eq(+xs: +List<Nat>, +ys: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case Con{hy, ty}:
          False{}
    case Con{hx, tx}:
      match ys:
        case Nil{}:
          False{}
        case Con{hy, ty}:
          Bool.and(Nat.is_eq(hx, hy), nlist_eq(tx, ty))

def sample_xs() -> +List<Nat>:
  [10n, 20n, 30n, 40n]

def sample_ys() -> +List<Nat>:
  [50n, 60n]

def set_split_case(+n: Nat, bad: U32) -> U32:
  +xs = sample_xs()
  +ys = sample_ys()
  +v = {99n : Nat}
  +lhs = List.set(&2, Nat, Settle.app(xs, ys), n, v)
  +rhs = Bool.pick(List<&2, Nat>, Nat.is_lt(n, Settle.len(xs)),
    Settle.app(List.set(&2, Nat, xs, n, v), ys),
    Settle.app(xs, List.set(&2, Nat, ys, Nat.sub(n, Settle.len(xs)), v)))
  inc_if_false(nlist_eq(lhs, rhs), bad)

def set_split_go(fuel: Nat, +n: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      set_split_go(p, 1n + n, set_split_case(n, bad))

def sample_xs2() -> +List<Nat>:
  [1n, 2n, 3n]

def sample_ys2() -> +List<Nat>:
  [5n, 6n]

def set_sum_case(bad: U32) -> U32:
  +xs = sample_xs2()
  +ys = sample_ys2()
  +x = {7n : Nat}
  +v = {8n : Nat}
  +lhs = Nat.add(Settle.suml(Settle.app(xs, v <> ys)), x)
  +rhs = Nat.add(Settle.suml(Settle.app(xs, x <> ys)), v)
  inc_if_false(Nat.is_eq(lhs, rhs), bad)

def set_laws_bad() -> U32:
  set_sum_case(set_split_go(U32.to_nat(7), 0n, 0))

def main() -> IO(Unit):
  do IO<Unit>:
    report("T5 index roundtrip (2^18)", index_bad())
    report("T5 cell field roundtrip", cell_bad())
    report("spike bit31", is_bad(U32.is_eq(U32.shln(1, 31n), 2147483648)))
    report("spike mul wrap", is_bad(U32.is_eq(U32.mul(4294967295, 2), 4294967294)))
    report("T6 gen determinism", gen_det_bad())
    report("T7 terrain structure", terrain_bad())
    report("T8 build matches gen (all cells)", build_bad())
    report("T10 parity flip + neighbor x", parity_bad())
    report("T11 low6 add independence + pm1 cancel", mod_bad())
    report("T12 dir phi cancellation", phi_bad())
    report("T13 neighbor index cancellation", nc_bad())
    report("T14 scan order totality", total_bad())
    report("T15 list set split + sum", set_laws_bad())
