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

# The support seed for rules 6/7 (V0-5): grounding is a *neighbourhood* test,
# not a coordinate one. The bedrock shell at 0/63 used to be detected by
# hardcoding `x/z/y ∈ {1,62}` (`shell_adjacent`, A.62), which never read a
# neighbour. Now the ground is read: `Support.sup` grounds a cell if the cell
# *below* it is static material (bedrock) — the support contact — or, failing
# that, if any other face neighbour is static (wall adhesion). No coordinate is
# baked in, so interior bedrock grounds too and R6/R7 hold. The below read is on
# the common propagation path, so the five wall reads are only paid where the
# below cell neither grounds nor supports.
#
# `face` maps a direction code 0..5 to the neighbour index; `seed_go` folds the
# reads. `Array` is linear, so the reads thread the `(world, value)` pair. It
# returns selector 4 (grounded → support 31) if a neighbour is static, else
# `acc` (the caller's fallback selector). The seed value `0` is a non-static
# sentinel: material 0 is not static, so the first iteration only reads `face`.
def face(+h: U32, +i: U32) -> U32:
  match h:
    case 0:
      Grid.below(i)
    case 1:
      Grid.above(i)
    case 2:
      Grid.west(i)
    case 3:
      Grid.east(i)
    case 4:
      Grid.south(i)
    case _:
      Grid.north(i)

def seed_go(
  dirs: List<U32>, +i: U32, +acc: U32, gp: Array<U32> & U32
) -> Array<U32> & U32:
  match dirs:
    case Nil{}:
      match gp:
        case (world, v):
          (world, Bool.pick(U32, Cell.static(Cell.material(v)), 4, acc))
    case Con{+h, t}:
      match gp:
        case (world, v):
          seed_go(t, i, Bool.pick(U32, Cell.static(Cell.material(v)), 4, acc), Array.get(U32, world, face(h, i)))

# The wall-adhesion half of the seed: the five non-below faces, returning
# selector 4 (grounded) or 6 (crush). Used by `Support.sup` only where the below
# cell neither grounds nor supports.
def side_sel(world: Array<U32>, +i: U32) -> Array<U32> & U32:
  seed_go([1, 2, 3, 4, 5], i, 6, (world, 0))
