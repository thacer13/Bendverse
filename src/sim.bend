import Base
import ./grid.bend as Grid
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
