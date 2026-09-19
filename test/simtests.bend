import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/worldgen.bend as Worldgen
import ../src/sim.bend as Sim
import ../src/support.bend as Support
import ../src/store.bend as Store
import ../src/settle.bend as Settle
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
  w1 = Array.set(U32, w0, Grid.index(4, 40, 4), Cell.encode(Cell.sand(), 0, 1, 0, 0))
  w2 = Array.set(U32, w1, Grid.index(6, 40, 4), Cell.encode(Cell.rubble(), 0, 1, 0, 0))
  w3 = Array.set(U32, w2, Grid.index(5, 39, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w4 = Array.set(U32, w3, Grid.index(3, 40, 4), Cell.encode(Cell.rock(), 48, 0, 31, 0))
  w5 = Array.set(U32, w4, Grid.index(4, 39, 4), Cell.encode(Cell.rock(), 48, 0, 31, 0))
  w6 = Array.set(U32, w5, Grid.index(6, 39, 4), Cell.encode(Cell.rock(), 48, 0, 31, 0))
  w7 = Sim.phase(w6, 0)
  is_bad(U32.is_eq(Cell.material(Grid.value_at(w7, Grid.index(5, 39, 4))), Cell.sand()))

def t24() -> U32:
  # V0-1 conformance: wake does not pull a cell into the phase it is woken by.
  # `Sim.phase` is the tick-composable transform (writes applied, wakes pending),
  # so the inactive `sand` at (6,40,4) that the mover at (4,40,4) wakes is not in
  # this phase's evaluated set: it does not fall and (6,39,4) stays EMPTY (0).
  # Intra-phase activation is gone; the wake is applied at tick end (T33).
  w0 = Sim.build()
  w1 = Array.set(U32, w0, Grid.index(4, 40, 4), Cell.encode(Cell.sand(), 0, 1, 0, 0))
  w2 = Array.set(U32, w1, Grid.index(6, 40, 4), Cell.encode(Cell.sand(), 0, 0, 0, 0))
  w3 = Array.set(U32, w2, Grid.index(5, 39, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w4 = Array.set(U32, w3, Grid.index(6, 39, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w5 = Array.set(U32, w4, Grid.index(3, 40, 4), Cell.encode(Cell.rock(), 48, 0, 31, 0))
  w6 = Array.set(U32, w5, Grid.index(4, 39, 4), Cell.encode(Cell.rock(), 48, 0, 31, 0))
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
  w1 = Array.set(U32, w0, Grid.index(4, 40, 4), Cell.encode(Cell.sand(), 0, 1, 0, 0))
  w2 = settle(U32.to_nat(50), w1)
  landed = U32.is_eq(Cell.material(Grid.value_at(w2, Grid.index(4, 1, 4))), Cell.sand())
  is_bad(landed)

# T27/T28 V0-2 closure witnesses: with the shell painted away, a boundary step is
# inert at the grid level instead of wrapping to the opposite face.
def t27() -> U32:
  # Floor open: sand at (4,0,4), (4,63,4) cleared. Without the guard the drop
  # target `below` wraps to (4,63,4) and the grain escapes to the top face.
  w0 = Sim.build()
  w1 = Array.set(U32, w0, Grid.index(4, 0, 4), Cell.encode(Cell.sand(), 0, 1, 0, 0))
  w2 = Array.set(U32, w1, Grid.index(4, 63, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w3 = Sim.phase(w2, 0)
  is_bad(U32.is_eq(Cell.material(Grid.value_at(w3, Grid.index(4, 0, 4))), Cell.sand()))

def t28() -> U32:
  # West wall open, down and every in-box diagonal blocked: the only candidate is
  # the wrap to (63,39,4). Without the guard the grain slides across the box.
  w0 = Sim.build()
  w1 = Array.set(U32, w0, Grid.index(0, 40, 4), Cell.encode(Cell.sand(), 0, 1, 0, 0))
  w2 = Array.set(U32, w1, Grid.index(0, 39, 4), Cell.encode(Cell.rock(), 48, 0, 31, 0))
  w3 = Array.set(U32, w2, Grid.index(63, 40, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w4 = Array.set(U32, w3, Grid.index(63, 39, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w5 = Array.set(U32, w4, Grid.index(1, 40, 4), Cell.encode(Cell.rock(), 48, 0, 31, 0))
  w6 = Array.set(U32, w5, Grid.index(0, 40, 3), Cell.encode(Cell.rock(), 48, 0, 31, 0))
  w7 = Array.set(U32, w6, Grid.index(0, 40, 5), Cell.encode(Cell.rock(), 48, 0, 31, 0))
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
  w1 = Array.set(U32, w0, Grid.index(4, 40, 4), Cell.encode(Cell.sand(), 0, 1, 0, 0))
  w2 = Array.set(U32, w1, Grid.index(4, 39, 4), 0)
  w3 = Array.set(U32, w2, Grid.index(5, 39, 4), Cell.encode(Cell.sand(), 0, bact, 0, 0))
  Array.set(U32, w3, Grid.index(5, 38, 4), 0)

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

# T34 rule-9 conformance: a move clears the mover's active bit and the deferred
# wake re-activates it, so a grain falls at most one cell per tick. (Before the
# V0-4b fix, `mov` kept the bit set, so the target's later colour phase
# re-evaluated the mover and it fell two cells in one tick.)
def t34_world() -> Array<U32>:
  w0 = clear_column(U32.to_nat(62), 1, Sim.build())
  Array.set(U32, w0, Grid.index(4, 40, 4), Cell.encode(Cell.sand(), 0, 1, 0, 0))

def t34_one_drop() -> Bool:
  w = Sim.tick(t34_world())
  U32.is_eq(Cell.material(Grid.value_at(w, Grid.index(4, 39, 4))), Cell.sand())

def t34_reactivated() -> Bool:
  w = Sim.tick(t34_world())
  U32.is_ne(Cell.active(Grid.value_at(w, Grid.index(4, 39, 4))), 0)

def t34() -> U32:
  is_bad(Bool.and(t34_one_drop(), t34_reactivated()))

# T35 V0-4b conformance: the phase fold is driven by the active-cell work list,
# so it processes exactly the phase's colour. A grain of colour 3 at (5,39,4)
# moves in phase 3 but is untouched by phase 0.
def t35_world() -> Array<U32>:
  w0 = Sim.build()
  w1 = Array.set(U32, w0, Grid.index(5, 39, 4), Cell.encode(Cell.sand(), 0, 1, 0, 0))
  Array.set(U32, w1, Grid.index(5, 38, 4), 0)

def t35_color3() -> Bool:
  w = Sim.phase(t35_world(), 3)
  U32.is_eq(Cell.material(Grid.value_at(w, Grid.index(5, 38, 4))), Cell.sand())

def t35_color0() -> Bool:
  w = Sim.phase(t35_world(), 0)
  U32.is_eq(Cell.material(Grid.value_at(w, Grid.index(5, 39, 4))), Cell.sand())

def t35() -> U32:
  is_bad(Bool.and(t35_color3(), t35_color0()))

# T36 V0-4b-2/G16 conformance: the support pass's crush wake is deferred too. An
# active rock R at (4,40,4) with an empty below is crushed in the support pass,
# which wakes its neighbour B at (5,40,4) — but B is not evaluated by the same
# tick's phases (it stays put), and is active afterwards (so it falls next tick).
def t36_world() -> Array<U32>:
  w0 = Sim.build()
  w1 = Array.set(U32, w0, Grid.index(4, 40, 4), Cell.encode(Cell.rock(), 48, 1, 31, 0))
  w2 = Array.set(U32, w1, Grid.index(4, 39, 4), 0)
  w3 = Array.set(U32, w2, Grid.index(5, 40, 4), Cell.encode(Cell.sand(), 0, 0, 0, 0))
  Array.set(U32, w3, Grid.index(5, 39, 4), 0)

def t36_crushed() -> Bool:
  w = Sim.tick(t36_world())
  U32.is_eq(Cell.material(Grid.value_at(w, Grid.index(4, 40, 4))), Cell.rubble())

def t36_stayed() -> Bool:
  w = Sim.tick(t36_world())
  U32.is_eq(Cell.material(Grid.value_at(w, Grid.index(5, 40, 4))), Cell.sand())

def t36_woken() -> Bool:
  w = Sim.tick(t36_world())
  U32.is_ne(Cell.active(Grid.value_at(w, Grid.index(5, 40, 4))), 0)

def t36() -> U32:
  is_bad(Bool.and(Bool.and(t36_crushed(), t36_stayed()), t36_woken()))

# T37 V0-4b-3b conformance: the dirty-row mask carries the work set across ticks.
# A grain at y=16 (a row boundary) falls one cell per tick; the mask must mark the
# rows the deferred wake reaches, or the grain freezes after the first move.
def t37_world() -> Array<U32>:
  w0 = clear_column(U32.to_nat(62), 1, Sim.build())
  Array.set(U32, w0, Grid.index(4, 16, 4), Cell.encode(Cell.sand(), 0, 1, 0, 0))

def t37() -> U32:
  w = Sim.ticks(U32.to_nat(2), t37_world())
  is_bad(U32.is_eq(Cell.material(Grid.value_at(w, Grid.index(4, 14, 4))), Cell.sand()))

# ============================================================================
# T38/T39 — the flagship property, end to end, on the real engine (A.78)
#
# Until now Φ was only ever a *symbolic* object: `Settle.array_phi` is a
# proof-side definition and `Settle.suml` is not tail-recursive, so it overflows
# the stack on a 2^18-cell world. The engine was therefore never checked against
# the property the whole verification pyramid is built to establish. These two
# tests close that: T39 pins the runtime oracle to the model, T38 runs it.
#
# Run natively (`bend test/simtests.bend -o bin && ./bin`): the JS backend
# overflows on this shape, which is why the property went untested.
# ============================================================================

# Φ = Σ dens(material) * y, over the world read in ascending flat-index order
# (the order `Grid.to_list` yields, which is the order `Settle.to_pots` walks).
# Tail-recursive, so it survives a full 262144-cell world.
def phi_acc(xs: List<&1, U32>, +i: U32, acc: Nat) -> Nat:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      phi_acc(t, U32.add(i, 1), Nat.add(acc, Settle.pot_at(h, i)))

def phi_run(world: Array<U32>) -> Nat:
  phi_acc(Grid.to_list(world), 0, 0n)

# Φ consumes an array, so keep the original and measure a copy.
def phi_dup(a: Array<U32>) -> Array<U32> & Array<U32>:
  Array.clone(U32, a)

def phi_keep(p: Array<U32> & Array<U32>) -> Nat & Array<U32>:
  match p:
    case (a, b): (phi_run(a), b)

# Tick `fuel` times; `bad` counts ticks where Φ strictly increased.
def phi_span(fuel: Nat, pr: Nat & Array<U32>, prev: Nat, bad: U32) -> Nat & U32:
  match fuel:
    case 0n:
      match pr:
        case (ph, w): (ph, bad)
    case 1n+p:
      match pr:
        case (+ph, w):
          up = Nat.is_gt(ph, prev)
          phi_span(p, phi_keep(phi_dup(Sim.tick(w))), ph, U32.add(bad, Bool.pick(U32, up, 1, 0)))

# Non-vacuity: a run that moved nothing would pass a monotonicity check for free,
# so Φ must also have strictly dropped over the whole span.
def t38_fin(pr: Nat & U32, +ph0: Nat) -> U32:
  match pr:
    case (phf, bad):
      dropped = Nat.is_gt(ph0, phf)
      U32.add(bad, Bool.pick(U32, dropped, 0, 1))

def t38_start(pr: Nat & Array<U32>) -> U32:
  match pr:
    case (+ph0, w):
      t38_fin(phi_span(60n, phi_keep(phi_dup(Sim.tick(w))), ph0, 0), ph0)

def t38() -> U32:
  w0 = Fixtures.spawn(Sim.build())
  w1 = Fixtures.pull(w0)
  t38_start(phi_keep(phi_dup(w1)))

# T39 — the oracle must agree with the model. An all-empty world carrying one
# sand grain at height y has Φ = `Settle.pot_at` at its packed index, so the
# expectation is taken from the model rather than from a literal. (Large `Nat`
# literals are expanded unary by the compiler and overflow; deriving the value
# is both necessary and a stronger statement.) This pins the whole read path:
# `Grid.to_list` order, the counter's start value, and the `iy` decode.
def empty_world_at(depth: Nat) -> Array<U32>:
  match depth:
    case 0n:
      ALeaf{0}
    case 1n+ +p:
      ANode{empty_world_at(p), empty_world_at(p)}

def one_sand_phi(+y: U32) -> Nat:
  +idx = Grid.index(32, y, 32)
  w = empty_world_at(18n)
  w2 = w[idx] <- Cell.encode(Cell.sand(), 0, 0, 0, 0)
  phi_run(w2)

def model_one_sand(+y: U32) -> Nat:
  Settle.pot_at(Cell.encode(Cell.sand(), 0, 0, 0, 0), Grid.index(32, y, 32))

def t39() -> U32:
  a = U32.add(is_bad(Nat.is_eq(one_sand_phi(1), model_one_sand(1))),
              is_bad(Nat.is_eq(one_sand_phi(5), model_one_sand(5))))
  U32.add(a, is_bad(Nat.is_eq(one_sand_phi(63), model_one_sand(63))))

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
    report("T34 one move per tick (rule 9)", t34())
    report("T35 work-list phase acts on its colour only", t35())
    report("T36 support crush wake is deferred (G16)", t36())
    report("T37 dirty-row mask carries the work set", t37())
    report("T38 Phi never increases over 60 engine ticks", t38())
    report("T39 runtime Phi oracle agrees with the model", t39())
