import Base
import ./grid.bend as Grid
import ./cell.bend as Cell
import ./ops.bend as Ops
import ./rules.bend as Rules
import ./support.bend as Support
import ./worldgen.bend as Worldgen

def build() -> Array<U32>:
  Support.pass_all(Worldgen.build())

def phase(world: Array<U32>, c: U32) -> Array<U32>:
  q = Array.get(U32, world, 0)
  Rules.step(U32.to_nat(16777216), q, 0, 0, c, 0, 0)

def tick(world: Array<U32>) -> Array<U32>:
  world = Support.pass(world)
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
      world = Ops.wake(world, idx)
      spawn_go(p, U32.add(i, 1), world)

def spawn(world: Array<U32>) -> Array<U32>:
  spawn_go(U32.to_nat(175), 0, world)

def pull(world: Array<U32>) -> Array<U32>:
  +idx = Grid.index(32, 3, 32)
  world = world[idx] <- 0
  Ops.wake(world, idx)
