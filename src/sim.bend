import Base
import ./cell.bend as Cell
import ./grid.bend as Grid
import ./rules.bend as Rules
import ./support.bend as Support
import ./worldgen.bend as Worldgen

def build() -> Array<U32>:
  Support.pass_all(Worldgen.build())

# M9 win 2: a settled world (no active cell, rule 9) is a tick fixpoint.
# `Support.pass` is activity-gated and each phase is an intent fold that skips
# inactive cells, so when no cell carries the active bit a whole tick is the
# identity. Scanning first turns the flat ~21 ms settled tick into a single
# cheap pass.
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

# V0-1: the phase is `Rules.phase_plan` — a pure `plan` (read-only intent +
# resolve) followed by `commit_sets`. V0-4a (rule 9): the wakes the phase
# produced are *pending*; `Sim.phase` returns the written world, and
# `tick_active` applies all eight phases' wakes once, at tick end, so no phase
# evaluates a cell an earlier phase of the same tick woke (`G12`).
def phase_w(world: Array<U32>, +c: U32) -> Array<U32> & List<Rules.Write>:
  Rules.phase_plan(world, c)

def phase_get(r: Array<U32> & List<Rules.Write>) -> Array<U32>:
  match r:
    case (world2, _):
      world2

def phase(world: Array<U32>, +c: U32) -> Array<U32>:
  phase_get(phase_w(world, c))

# `phases` folds colours `c .. 7` over `pair` (the running world and the wakes
# produced so far), carrying the accumulated wake list in `wakes`. The phase
# *result* is handed as a parameter so the pair can be matched without a local
# binder (Bend matches only parameters/fields).
def phases(
  fuel: Nat, +c: U32, pair: Array<U32> & List<Rules.Write>, wakes: List<Rules.Write>
) -> Array<U32> & List<Rules.Write>:
  match fuel:
    case 0n:
      match pair:
        case (world2, ws):
          (world2, List.append(&1, Rules.Write, ws, wakes))
    case 1n+p:
      match pair:
        case (world2, ws):
          phases(p, U32.add(c, 1), phase_w(world2, c), List.append(&1, Rules.Write, ws, wakes))

def phases_commit(r: Array<U32> & List<Rules.Write>) -> Array<U32>:
  match r:
    case (world2, wakes):
      Rules.commit_wakes(wakes, world2)

def tick_active(world: Array<U32>) -> Array<U32>:
  phases_commit(phases(8n, 0, (Support.pass(world), Nil{}), Nil{}))

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
