import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/ops.bend as Ops

# Scenario fixtures: pure world transformers used by the runners and the
# simulation tests. These are setup, not engine — the tick pipeline
# (`src/sim.bend`) is only `build`/`phase`/`tick`/`ticks`.

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
