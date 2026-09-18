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
  a = Sim.build()
  a2 = Sim.ticks(U32.to_nat(10), a)
  b = Sim.build()
  b2 = Sim.ticks(U32.to_nat(10), b)
  is_bad(list_eq(Grid.to_list(a2), Grid.to_list(b2)))

def count_nonempty_list(xs: List<U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      ne = U32.is_ne(Cell.material(h), 0)
      count_nonempty_list(t, Bool.pick(U32, ne, U32.add(acc, 1), acc))

def t2() -> U32:
  w0 = Sim.spawn(Sim.build())
  before = count_nonempty_list(Grid.to_list(w0), 0)
  w1 = Sim.spawn(Sim.build())
  w2 = Sim.ticks(U32.to_nat(10), w1)
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
  w = Sim.build()
  w2 = Sim.ticks(U32.to_nat(10), w)
  t3_go(U32.to_nat(262144), 0, Grid.to_list(w2), 0)

def same_fields(+h: U32, +g: U32) -> Bool:
  Bool.and(
    U32.is_eq(Cell.material(h), Cell.material(g)),
    Bool.and(U32.is_eq(Cell.cohesion(h), Cell.cohesion(g)), U32.is_eq(Cell.fall(h), Cell.fall(g))))

def near(+x: U32, +z: U32) -> Bool:
  Bool.and(
    Bool.and(U32.is_ge(x, 27), U32.is_le(x, 37)),
    Bool.and(U32.is_ge(z, 27), U32.is_le(z, 37))
  )

def t4_go(fuel: Nat, +i: U32, cells: List<U32>, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      match cells:
        case Nil{}:
          bad
        case Con{h, t}:
          +hh = h
          +x = Grid.ix(i)
          +z = Grid.iz(i)
          +g = Worldgen.gen(x, Grid.iy(i), z, 42)
          act = U32.is_ne(Cell.active(hh), 0)
          fr = Bool.not(near(x, z))
          eq = same_fields(hh, g)
          ok = Bool.and(Bool.not(act), Bool.or(Bool.not(fr), eq))
          t4_go(p, U32.add(i, 1), t, inc_if_false(ok, bad))

def settle(fuel: Nat, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      settle(p, Sim.tick(world))

def t4() -> U32:
  w = Sim.build()
  w1 = Sim.spawn(w)
  w2 = settle(U32.to_nat(50), w1)
  t4_go(U32.to_nat(262144), 0, Grid.to_list(w2), 0)

def maybe_tick(z: Bool, world: Array<U32>) -> Array<U32>:
  match z:
    case True{}:
      Sim.tick(world)
    case False{}:
      world

def list_hash(xs: List<U32>, +h: U32) -> U32:
  match xs:
    case Nil{}:
      h
    case Con{x, t}:
      list_hash(t, U32.add(U32.mul(h, 16777619), x))

def settled_hash(z: Bool) -> U32:
  w = Sim.build()
  w1 = Sim.spawn(w)
  w2 = settle(U32.to_nat(50), w1)
  w3 = maybe_tick(z, w2)
  list_hash(Grid.to_list(w3), 5381)

def t4b() -> U32:
  is_bad(U32.is_eq(settled_hash(False{}), settled_hash(True{})))

def count_rock_gen(fuel: Nat, +i: U32, +acc: U32) -> U32:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      x = Grid.ix(i)
      y = Grid.iy(i)
      z = Grid.iz(i)
      g = Worldgen.gen(x, y, z, 42)
      r = U32.is_eq(Cell.material(g), 3)
      count_rock_gen(p, U32.add(i, 1), Bool.pick(U32, r, U32.add(acc, 1), acc))

def count_rock_list(xs: List<U32>, +acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      r = U32.is_eq(Cell.material(h), 3)
      count_rock_list(t, Bool.pick(U32, r, U32.add(acc, 1), acc))

def t9() -> U32:
  before = count_rock_gen(U32.to_nat(262144), 0, 0)
  w = Sim.pull(Sim.build())
  w2 = Sim.ticks(U32.to_nat(5), w)
  after = count_rock_list(Grid.to_list(w2), 0)
  is_bad(U32.is_lt(after, before))

def main() -> IO(Unit):
  do IO<Unit>:
    report("T1 tick determinism (10 ticks)", t1())
    report("T2 conservation of non-Empty", t2())
    report("T3 bedrock static", t3())
    report("T4 settles + far cells unchanged", t4())
    report("T4b settled world is a fixed point", t4b())
    report("T9 pull-base collapses rock", t9())
