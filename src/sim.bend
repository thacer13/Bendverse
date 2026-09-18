import Base
import ./grid.bend as Grid
import ./cell.bend as Cell
import ./rules.bend as Rules

def phase(world: Array<U32>, c: U32) -> Array<U32>:
  q = Array.get(U32, world, 0)
  Rules.step(U32.to_nat(8388608), q, 0, 0, c, 0, 0)

def tick(world: Array<U32>) -> Array<U32>:
  world = phase(world, 0)
  world = phase(world, 1)
  world = phase(world, 2)
  world = phase(world, 3)
  world = phase(world, 4)
  world = phase(world, 5)
  world = phase(world, 6)
  world = phase(world, 7)
  world

def ticks(fuel: Nat, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      world2 = tick(world)
      ticks(p, world2)

def spawn_go(fuel: Nat, +i: U32, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      bx = U32.mod(i, 5)
      bz = U32.mod(U32.div(i, 5), 5)
      by = U32.mod(U32.div(i, 25), 7)
      x = U32.add(bx, 30)
      z = U32.add(bz, 30)
      y = U32.add(by, 46)
      +idx = Grid.index(x, y, z)
      world = world[idx] <- Cell.encode(2, 0, 0, 0, 0)
      world = Rules.wake(world, idx)
      spawn_go(p, U32.add(i, 1), world)

def spawn(world: Array<U32>) -> Array<U32>:
  spawn_go(U32.to_nat(175), 0, world)
