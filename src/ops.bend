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

def adjacent_static(+i: U32) -> Bool:
  +x = Grid.ix(i)
  +z = Grid.iz(i)
  +y = Grid.iy(i)
  Bool.or(
    Bool.or(Bool.or(U32.is_eq(x, 1), U32.is_eq(x, 62)), Bool.or(U32.is_eq(z, 1), U32.is_eq(z, 62))),
    Bool.or(U32.is_eq(y, 1), U32.is_eq(y, 62))
  )
