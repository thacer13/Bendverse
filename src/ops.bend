import Base
import ./grid.bend as Grid
import ./cell.bend as Cell

def mark_got(p: Array<U32> & U32, i: U32) -> Array<U32>:
  match p:
    case (world, w):
      nw = Cell.activate(w)
      world = world[i] <- nw
      world

def mark(world: Array<U32>, +i: U32) -> Array<U32>:
  p = Array.get(U32, world, i)
  mark_got(p, i)

def wake_x(
  fuel: Nat, +dx: U32, +dy: U32, +dz: U32, +i: U32, world: Array<U32>
) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      j = Grid.neighbor(i, U32.sub(dx, 1), U32.sub(dy, 1), U32.sub(dz, 1))
      world2 = mark(world, j)
      wake_x(p, U32.add(dx, 1), dy, dz, i, world2)

def wake_y(
  fuel: Nat, +dy: U32, +dz: U32, +i: U32, world: Array<U32>
) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      world2 = wake_x(U32.to_nat(3), 0, dy, dz, i, world)
      wake_y(p, U32.add(dy, 1), dz, i, world2)

def wake_z(fuel: Nat, +dz: U32, +i: U32, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      world2 = wake_y(U32.to_nat(3), 0, dz, i, world)
      wake_z(p, U32.add(dz, 1), i, world2)

def wake(world: Array<U32>, i: U32) -> Array<U32>:
  wake_z(U32.to_nat(3), 0, i, world)

def set_support(+w: U32, s: U32) -> U32:
  Cell.encode(Cell.material(w), Cell.cohesion(w), Cell.active(w), s, Cell.fall(w))

def set_fall0(+w: U32) -> U32:
  Cell.encode(Cell.material(w), Cell.cohesion(w), 0, Cell.support(w), 0)

def crush_material(+m: U32) -> U32:
  match m:
    case 3:
      4
    case _:
      m

def crush_word(+w: U32) -> U32:
  Cell.encode(crush_material(Cell.material(w)), 0, 0, 0, 0)

# Site-level crush, guarded to rock. A rule-8 impact event only converts rock
# (→ rubble) and drops cohesion; a target that is not rock has no cohesion
# threshold to cross, so the field reset must not be applied. The `Bool.pick`
# keeps the guard a testable value, so the write site is case-splittable in the
# `PT` mirror (G10). Behaviour-witnessed by A.37 probe 1; proof-friendly form
# landed in A.38.
def crush_if_rock(+w: U32) -> U32:
  Bool.pick(U32, U32.is_eq(Cell.material(w), 3), crush_word(w), w)

# The support seed for rules 6/7: the layer just inside the box shell is
# treated as grounded, so cohesive cells there get support 31 and support then
# propagates up the column.
#
# NOTE (A.62): despite the old name this is *coordinate*-based, not a
# neighbourhood test — it never looks at an adjacent cell. It bakes in the
# 64³ world and a bedrock shell at 0/63 (the literals `1`/`62` are `0+1`/`63-1`).
# That deviates from rule 6/7 ("rigidity from the pre-phase neighbourhood") and
# from C2 ("the shell is generation, not grid"). Recorded in PLAN §4.1; to be
# replaced by a real neighbour test in `V0-2`/`V0-4`.
def shell_adjacent(+i: U32) -> Bool:
  +x = Grid.ix(i)
  +z = Grid.iz(i)
  +y = Grid.iy(i)
  Bool.or(
    Bool.or(Bool.or(U32.is_eq(x, 1), U32.is_eq(x, 62)), Bool.or(U32.is_eq(z, 1), U32.is_eq(z, 62))),
    Bool.or(U32.is_eq(y, 1), U32.is_eq(y, 62))
  )
