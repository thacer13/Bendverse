import Base
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
