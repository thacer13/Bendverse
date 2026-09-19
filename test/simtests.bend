import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/worldgen.bend as Worldgen
import ../src/sim.bend as Sim
import ../src/support.bend as Support
import ../src/store.bend as Store
import ../scenarios/fixtures.bend as Fixtures

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
  w0 = Fixtures.spawn(Sim.build())
  before = count_nonempty_list(Grid.to_list(w0), 0)
  w1 = Fixtures.spawn(Sim.build())
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
  w1 = Fixtures.spawn(w)
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
  w1 = Fixtures.spawn(w)
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
  w = Fixtures.pull(Sim.build())
  w2 = Sim.ticks(U32.to_nat(5), w)
  after = count_rock_list(Grid.to_list(w2), 0)
  is_bad(U32.is_lt(after, before))

def t18() -> U32:
  a0 = Support.pass_all(Store.assemble(Store.build_all()))
  b0 = Sim.build()
  init_bad = is_bad(list_eq(Grid.to_list(a0), Grid.to_list(b0)))
  a = Sim.ticks(U32.to_nat(10), Fixtures.spawn(Support.pass_all(Store.assemble(Store.build_all()))))
  b = Sim.ticks(U32.to_nat(10), Fixtures.spawn(Sim.build()))
  U32.add(init_bad, is_bad(list_eq(Grid.to_list(a), Grid.to_list(b))))

def t20() -> U32:
  # Every chunk of a fresh store is sleeping and gen-equal, so eviction drops
  # them all and `assemble` regenerates the world; the tick pipeline from that
  # evicted-then-regenerated world matches the fixed world bit-for-bit.
  a0 = Support.pass_all(Store.assemble(Store.evict(Store.build_all())))
  b0 = Sim.build()
  init_bad = is_bad(list_eq(Grid.to_list(a0), Grid.to_list(b0)))
  a = Sim.ticks(U32.to_nat(10), Fixtures.spawn(Support.pass_all(Store.assemble(Store.evict(Store.build_all())))))
  b = Sim.ticks(U32.to_nat(10), Fixtures.spawn(Sim.build()))
  U32.add(init_bad, is_bad(list_eq(Grid.to_list(a), Grid.to_list(b))))

def t23() -> U32:
  # V0-1 conformance: two same-colour diagonal movers still claim the SAME target
  # (`sand` at (4,40,4) and `rubble` at (6,40,4) both reach (5,39,4)), but the
  # phase resolves the contention from the *pre-phase* state: the smaller flat
  # index (sand, 4 < 6) owns the target and the later mover forfeits. So the
  # target ends as SAND (2) -- the ordered cascade that re-read the just-written
  # cell is gone.
  w0 = Sim.build()
  w1 = w0[Grid.index(4, 40, 4)] <- Cell.encode(Cell.sand(), 0, 1, 0, 0)
  w2 = w1[Grid.index(6, 40, 4)] <- Cell.encode(Cell.rubble(), 0, 1, 0, 0)
  w3 = w2[Grid.index(5, 39, 4)] <- Cell.encode(Cell.empty(), 0, 0, 0, 0)
  w4 = w3[Grid.index(3, 40, 4)] <- Cell.encode(Cell.rock(), 48, 0, 31, 0)
  w5 = w4[Grid.index(4, 39, 4)] <- Cell.encode(Cell.rock(), 48, 0, 31, 0)
  w6 = w5[Grid.index(6, 39, 4)] <- Cell.encode(Cell.rock(), 48, 0, 31, 0)
  w7 = Sim.phase(w6, 0)
  is_bad(U32.is_eq(Cell.material(Grid.value_at(w7, Grid.index(5, 39, 4))), Cell.sand()))

def t24() -> U32:
  # V0-1 conformance: wake does not pull a cell into the phase it is woken by.
  # `Sim.phase` is the tick-composable transform (writes applied, wakes pending),
  # so the inactive `sand` at (6,40,4) that the mover at (4,40,4) wakes is not in
  # this phase's evaluated set: it does not fall and (6,39,4) stays EMPTY (0).
  # Intra-phase activation is gone; the wake is applied at tick end (T33).
  w0 = Sim.build()
  w1 = w0[Grid.index(4, 40, 4)] <- Cell.encode(Cell.sand(), 0, 1, 0, 0)
  w2 = w1[Grid.index(6, 40, 4)] <- Cell.encode(Cell.sand(), 0, 0, 0, 0)
  w3 = w2[Grid.index(5, 39, 4)] <- Cell.encode(Cell.empty(), 0, 0, 0, 0)
  w4 = w3[Grid.index(6, 39, 4)] <- Cell.encode(Cell.empty(), 0, 0, 0, 0)
  w5 = w4[Grid.index(3, 40, 4)] <- Cell.encode(Cell.rock(), 48, 0, 31, 0)
  w6 = w5[Grid.index(4, 39, 4)] <- Cell.encode(Cell.rock(), 48, 0, 31, 0)
  w7 = Sim.phase(w6, 0)
  is_bad(U32.is_eq(Cell.material(Grid.value_at(w7, Grid.index(6, 39, 4))), Cell.empty()))

def clear_column(fuel: Nat, +y: U32, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      +i = Grid.index(4, y, 4)
      clear_column(p, U32.add(y, 1), world[i] <- 0)

# T26 V0-1 settling witness: a lone grain in an empty column falls straight down
# (drop has priority over sliding), and once the bedrock floor blocks the drop
# the diagonal cells are bedrock too, so it settles at y=1.
def t26() -> U32:
  w0 = clear_column(U32.to_nat(62), 1, Sim.build())
  w1 = w0[Grid.index(4, 40, 4)] <- Cell.encode(Cell.sand(), 0, 1, 0, 0)
  w2 = settle(U32.to_nat(50), w1)
  landed = U32.is_eq(Cell.material(Grid.value_at(w2, Grid.index(4, 1, 4))), Cell.sand())
  is_bad(landed)

# T27/T28 V0-2 closure witnesses: with the shell painted away, a boundary step is
# inert at the grid level instead of wrapping to the opposite face.
def t27() -> U32:
  # Floor open: sand at (4,0,4), (4,63,4) cleared. Without the guard the drop
  # target `below` wraps to (4,63,4) and the grain escapes to the top face.
  w0 = Sim.build()
  w1 = w0[Grid.index(4, 0, 4)] <- Cell.encode(Cell.sand(), 0, 1, 0, 0)
  w2 = w1[Grid.index(4, 63, 4)] <- Cell.encode(Cell.empty(), 0, 0, 0, 0)
  w3 = Sim.phase(w2, 0)
  is_bad(U32.is_eq(Cell.material(Grid.value_at(w3, Grid.index(4, 0, 4))), Cell.sand()))

def t28() -> U32:
  # West wall open, down and every in-box diagonal blocked: the only candidate is
  # the wrap to (63,39,4). Without the guard the grain slides across the box.
  w0 = Sim.build()
  w1 = w0[Grid.index(0, 40, 4)] <- Cell.encode(Cell.sand(), 0, 1, 0, 0)
  w2 = w1[Grid.index(0, 39, 4)] <- Cell.encode(Cell.rock(), 48, 0, 31, 0)
  w3 = w2[Grid.index(63, 40, 4)] <- Cell.encode(Cell.empty(), 0, 0, 0, 0)
  w4 = w3[Grid.index(63, 39, 4)] <- Cell.encode(Cell.empty(), 0, 0, 0, 0)
  w5 = w4[Grid.index(1, 40, 4)] <- Cell.encode(Cell.rock(), 48, 0, 31, 0)
  w6 = w5[Grid.index(0, 40, 3)] <- Cell.encode(Cell.rock(), 48, 0, 31, 0)
  w7 = w6[Grid.index(0, 40, 5)] <- Cell.encode(Cell.rock(), 48, 0, 31, 0)
  w8 = Sim.phase(w7, 0)
  is_bad(U32.is_eq(Cell.material(Grid.value_at(w8, Grid.index(0, 40, 4))), Cell.sand()))

# T33 V0-4a/G12 conformance: a phase's wake is *pending* until tick end, so a cell
# woken by an earlier phase is not evaluated by a later phase of the same tick.
# `t33_mk(bact)` builds the site: A (color 0, active) drops into (4,39,4) in phase
# 0 and wakes its neighbours; B at (5,39,4) (color 3, so a later phase) is one of
# them. With B inactive at tick start it stays put, but is active afterwards;
# with B active at tick start (control) phase 3 evaluates it and it falls.
def t33_mk(+bact: U32) -> Array<U32>:
  w0 = Sim.build()
  w1 = w0[Grid.index(4, 40, 4)] <- Cell.encode(Cell.sand(), 0, 1, 0, 0)
  w2 = w1[Grid.index(4, 39, 4)] <- 0
  w3 = w2[Grid.index(5, 39, 4)] <- Cell.encode(Cell.sand(), 0, bact, 0, 0)
  w3[Grid.index(5, 38, 4)] <- 0

def t33_stayed() -> Bool:
  w = Sim.tick(t33_mk(0))
  U32.is_eq(Cell.material(Grid.value_at(w, Grid.index(5, 39, 4))), Cell.sand())

def t33_woken() -> Bool:
  w = Sim.tick(t33_mk(0))
  U32.is_ne(Cell.active(Grid.value_at(w, Grid.index(5, 39, 4))), 0)

def t33_control() -> Bool:
  w = Sim.tick(t33_mk(1))
  U32.is_eq(Cell.material(Grid.value_at(w, Grid.index(5, 38, 4))), Cell.sand())

def t33() -> U32:
  is_bad(Bool.and(Bool.and(t33_stayed(), t33_woken()), t33_control()))

def main() -> IO(Unit):
  do IO<Unit>:
    report("T1 tick determinism (10 ticks)", t1())
    report("T2 conservation of non-Empty", t2())
    report("T3 bedrock static", t3())
    report("T4 settles + far cells unchanged", t4())
    report("T4b settled world is a fixed point", t4b())
    report("T9 pull-base collapses rock", t9())
    report("T18 chunk store tick equivalence", t18())
    report("T20 evict -> assemble -> tick equivalence", t20())
    report("T23 phase contention resolved from pre-phase state", t23())
    report("T24 wake does not propagate within a phase", t24())
    report("T26 grain in an empty column settles", t26())
    report("T27 floor painted away: no wrap at y=0", t27())
    report("T28 wall painted away: no wrap at x=0", t28())
    report("T33 wake is pending until tick end (G12)", t33())
