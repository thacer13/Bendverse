import Base
import ./cell.bend as Cell
import ./grid.bend as Grid
import ./rules.bend as Rules
import ./support.bend as Support
import ./worldgen.bend as Worldgen

def build() -> Array<U32>:
  Support.pass_all(Worldgen.build())

# V0-4b-2: a settled world (no active cell, rule 9) is a tick fixpoint. `any_active`
# is the cheap check; a settled tick is that one scan and nothing else.
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

# ------------------------------------------------------------------ V0-4b
# The phase fold runs over an *active-cell work list* instead of the colour
# sub-lattice. The tick's list is built by the support scan (`Support.pass_gated`
# returns the active cells it saw); `filter_color` selects a phase's colour.
# Soundness: V0-1 makes a phase's result independent of evaluation order, and
# within a tick the active set only shrinks (a move clears the mover's bit, wake
# is deferred to tick end), so the list is a superset of every cell the phases
# can act on and the phases skip any that were deactivated.
#
# `active_list` is the standalone work list for a single-phase probe (`Sim.phase`).
def active_go(
  fuel: Nat, +i: U32, acc: List<&2, U32>, gp: Array<U32> & U32
) -> Array<U32> & List<&2, U32>:
  match fuel:
    case 0n:
      match gp:
        case (world, v):
          (world, Support.cons_if(i, acc, U32.is_ne(Cell.active(v), 0)))
    case 1n+p:
      match gp:
        case (world, v):
          +acc2 = Support.cons_if(i, acc, U32.is_ne(Cell.active(v), 0))
          +ni = U32.add(i, 1)
          q = Array.get(U32, world, ni)
          active_go(p, ni, acc2, q)

def active_list(world: Array<U32>) -> Array<U32> & List<&2, U32>:
  q = Array.get(U32, world, 0)
  active_go(U32.to_nat(U32.sub(Grid.volume(), 1)), 0, Nil{}, q)

def filter_color(+xs: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      Support.cons_if(h, filter_color(t, c), U32.is_eq(Rules.color_of(h), c))

# V0-1: the phase is `Rules.phase_plan_w` — a pure `plan` (read-only intent +
# resolve) followed by `commit_sets`. V0-4a (rule 9): the wakes the phase
# produced are *pending*; the tick threads them and applies them once, at tick
# end, so no phase evaluates a cell an earlier phase of the same tick woke.
def phase_w(
  world: Array<U32>, +c: U32, +todo: List<&2, U32>
) -> Array<U32> & List<Rules.Write>:
  Rules.phase_plan_w(world, filter_color(todo, c))

def phase_get(r: Array<U32> & List<Rules.Write>) -> Array<U32>:
  match r:
    case (world2, _):
      world2

def phase_todo(r: Array<U32> & List<&2, U32>, +c: U32) -> Array<U32>:
  match r:
    case (world2, todo):
      phase_get(phase_w(world2, c, todo))

def phase(world: Array<U32>, +c: U32) -> Array<U32>:
  phase_todo(active_list(world), c)

# `phases` folds colours `0 .. 7`. `r` is the *previous* phase's result (the
# initial call passes the support-passed world with no writes); `todo` is the
# full work list, reused by each colour (hence `+todo`). The result is handed as
# a parameter so the pair can be matched without a local binder (Bend matches
# only parameters/fields).
def phases(
  fuel: Nat, +c: U32, r: Array<U32> & List<Rules.Write>, +todo: List<&2, U32>, wakes: List<Rules.Write>
) -> Array<U32> & List<Rules.Write>:
  match fuel:
    case 0n:
      match r:
        case (world2, ws):
          (world2, List.append(&1, Rules.Write, ws, wakes))
    case 1n+p:
      match r:
        case (world2, ws):
          phases(p, U32.add(c, 1), phase_w(world2, c, todo), todo, List.append(&1, Rules.Write, ws, wakes))

def phases_commit(r: Array<U32> & List<Rules.Write>) -> Array<U32>:
  match r:
    case (world2, wakes):
      Rules.commit_wakes(wakes, world2)

# V0-4b-2: the tick runs the support pass with its wakes *deferred*; the pass also
# returns the active-cell work list, so the eight phases run over that list and
# the support and phase wakes are applied together at tick end.
def tick_sup(r: Array<U32> & List<U32> & List<&2, U32>) -> Array<U32>:
  match r:
    case (world2, sws, todo):
      phases_commit(phases(8n, 0, (world2, Nil{}), todo, Rules.wake_writes(sws)))

def tick_got(r: Array<U32> & Bool) -> Array<U32>:
  match r:
    case (world2, act):
      match act:
        case False{}:
          world2
        case True{}:
          tick_sup(Support.pass_gated(world2, True{}))

def tick(world: Array<U32>) -> Array<U32>:
  tick_got(any_active(world))

def ticks(fuel: Nat, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      world2 = tick(world)
      ticks(p, world2)
