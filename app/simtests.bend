import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/worldgen.bend as Worldgen
import ../src/sim.bend as Sim

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

def list_eq(xs: List<U32>, ys: List<U32>) -> Bool:
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
          Bool.and(U32.is_eq(hx, hy), list_eq(tx, ty))

def t1() -> U32:
  a = Worldgen.build()
  a2 = Sim.ticks(U32.to_nat(10), a)
  b = Worldgen.build()
  b2 = Sim.ticks(U32.to_nat(10), b)
  is_bad(list_eq(Grid.to_list(a2), Grid.to_list(b2)))

def count_nonempty_list(xs: List<U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      ne = U32.is_ne(Cell.material(h), 0)
      count_nonempty_list(t, Bool.pick(U32, ne, U32.add(acc, 1), acc))

def count_gen(fuel: Nat, +i: U32, +acc: U32) -> U32:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      x = Grid.ix(i)
      y = Grid.iy(i)
      z = Grid.iz(i)
      g = Worldgen.gen(x, y, z, 42)
      ne = U32.is_ne(Cell.material(g), 0)
      count_gen(p, U32.add(i, 1), Bool.pick(U32, ne, U32.add(acc, 1), acc))

def t2() -> U32:
  before = count_gen(U32.to_nat(262144), 0, 0)
  w = Worldgen.build()
  w2 = Sim.ticks(U32.to_nat(10), w)
  after = count_nonempty_list(Grid.to_list(w2), 0)
  is_bad(U32.is_eq(before, after))

def t3_go(fuel: Nat, +i: U32, cells: List<U32>, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      match cells:
        case Nil{}:
          bad
        case Con{h, t}:
          x = Grid.ix(i)
          y = Grid.iy(i)
          z = Grid.iz(i)
          +g = Worldgen.gen(x, y, z, 42)
          is_bed = U32.is_eq(Cell.material(g), 1)
          ok = Bool.or(Bool.not(is_bed), U32.is_eq(h, g))
          t3_go(p, U32.add(i, 1), t, inc_if_false(ok, bad))

def t3() -> U32:
  w = Worldgen.build()
  w2 = Sim.ticks(U32.to_nat(10), w)
  t3_go(U32.to_nat(262144), 0, Grid.to_list(w2), 0)

def main() -> IO(Unit):
  do IO<Unit>:
    report("T1 tick determinism (10 ticks)", t1())
    report("T2 conservation of non-Empty", t2())
    report("T3 bedrock static", t3())
