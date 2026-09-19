import Base
import ./cell.bend as Cell
import ./grid.bend as Grid
import ./rules.bend as Rules
import ./support.bend as Support
import ./worldgen.bend as Worldgen

def build() -> Array<U32>:
  Support.pass_all(Worldgen.build())

# M9 win 2: a settled world (no active cell, rule 9) is a tick fixpoint.
# `Support.pass` is activity-gated and `Rules.step` skips inactive cells, so when
# no cell carries the active bit a whole tick is the identity. Scanning first
# turns the flat ~21 ms settled tick into a single cheap pass.
#
# `any_active_go` walks cells `0..262143`, carrying the pair `(world, value)` and
# an OR accumulator. `fuel` is the number of cells *after* the current one, so
# the last cell is handled by the base case and no out-of-range read happens.
def any_active_go(
  fuel: Nat, +i: U32, acc: Bool, gp: Array<U32> & U32
) -> Array<U32> & Bool:
  match fuel:
    case 0n:
      match gp:
        case (world, v):
          (world, Bool.or(acc, U32.is_ne(Cell.active(v), 0)))
    case 1n+p:
      match gp:
        case (world, v):
          acc2 = Bool.or(acc, U32.is_ne(Cell.active(v), 0))
          +ni = U32.add(i, 1)
          q = Array.get(U32, world, ni)
          any_active_go(p, ni, acc2, q)

def any_active(world: Array<U32>) -> Array<U32> & Bool:
  q = Array.get(U32, world, 0)
  any_active_go(U32.to_nat(U32.sub(Grid.volume(), 1)), 0, False{}, q)

def phase(world: Array<U32>, +c: U32) -> Array<U32>:
  +i0 = Grid.color_base(c)
  q = Array.get(U32, world, i0)
  Rules.step(U32.to_nat(16777216), q, 0, i0, c, 0, 0)

def tick_active(world: Array<U32>) -> Array<U32>:
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

def tick_got(r: Array<U32> & Bool) -> Array<U32>:
  match r:
    case (world2, act):
      match act:
        case False{}:
          world2
        case True{}:
          tick_active(world2)

def tick(world: Array<U32>) -> Array<U32>:
  tick_got(any_active(world))

def ticks(fuel: Nat, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      world2 = tick(world)
      ticks(p, world2)
