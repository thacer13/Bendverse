import Base
import ./cell.bend as Cell
import ./grid.bend as Grid
import ./rules.bend as Rules
import ./support.bend as Support
import ./worldgen.bend as Worldgen
import ./ops.bend as Ops
import ./dirty.bend as Dirty

def build() -> Array<U32>:
  Support.pass_all(Worldgen.build())

# ------------------------------------------------------------------ V0-4b
# The phase fold runs over an *active-cell work list* instead of the colour
# sub-lattice. Since V0-4b-3b the tick's list is built by the carried dirty-row
# mask (`Dirty.dirty_todo`); `active_list` below is the full-scan form, kept for
# the single-phase test transform `phase`. `filter_color` selects a phase's
# colour.
# Soundness: V0-1 makes a phase's result independent of evaluation order, and
# within a tick the active set only shrinks (a move clears the mover's bit, wake
# is deferred to tick end), so the list is a superset of every cell the phases
# can act on and the phases skip any that were deactivated.
#
# Both builders -- `active_list` and `Dirty.dirty_todo` -- produce the list in
# ascending index order (scanning down and consing), which is the bottom-up order
# the support pass needs for `below` propagation. The phase fold is
# order-independent.
def active_go(
  fuel: Nat, +i: U32, +acc: List<&2, U32>, gp: Array<U32> & U32
) -> Array<U32> & List<&2, U32>:
  match fuel:
    case 0n:
      match gp:
        case (world, v):
          act = U32.is_ne(Cell.active(v), 0)
          (world, Bool.pick(List<&2, U32>, act, i <> acc, acc))
    case 1n+p:
      match gp:
        case (world, v):
          act = U32.is_ne(Cell.active(v), 0)
          +acc2 = Bool.pick(List<&2, U32>, act, i <> acc, acc)
          +ni = U32.sub(i, 1)
          q = Array.get(U32, world, ni)
          active_go(p, ni, acc2, q)

def active_list(world: Array<U32>) -> Array<U32> & List<&2, U32>:
  +hi = U32.sub(Grid.volume(), 1)
  q = Array.get(U32, world, hi)
  active_go(U32.to_nat(hi), hi, Nil{}, q)

def filter_color(+xs: List<&2, U32>, +c: U32) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      +tail = filter_color(t, c)
      keep = U32.is_eq(Rules.color_of(h), c)
      Bool.pick(List<&2, U32>, keep, h <> tail, tail)

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

# V0-4b-3b: the tick is driven by a dirty-row mask carried across ticks
# (`src/dirty.bend`). The mask says which `y` rows may hold a cell activated since
# the last tick, so the work list is built by scanning only those rows
# (`Dirty.dirty_todo`) instead of the whole world (the full-scan `active_list`
# and the retired `any_active` check).
#
# The mask is threaded only through the *commit*: the support and phase entry
# points stay monomorphic (`Array<U32>`, `List<...>`), so no symbolic work list
# crosses a pair-returning fold (the A.76 checker overflow). A wake is applied
# and its three reachable rows marked together.
def commit_wakes_mask(
  writes: List<Rules.Write>, world: Array<U32>, m: Dirty.Mask
) -> Array<U32> & Dirty.Mask:
  match writes:
    case Nil{}:
      (world, m)
    case Con{h, t}:
      match h:
        case Rules.WSet{idx, op, src}:
          commit_wakes_mask(t, world, m)
        case Rules.WWake{+idx}:
          w2 = Ops.wake(world, idx)
          +m2 = Dirty.mark_wake(m, idx)
          commit_wakes_mask(t, w2, m2)

def tick_commit_phases(r: Array<U32> & List<Rules.Write>) -> Array<U32> & Dirty.Mask:
  match r:
    case (world3, wakes):
      commit_wakes_mask(wakes, world3, Dirty.zermask())

# The support pass over the work list (wakes deferred), then the eight phases
# over the same list; the support and phase wakes are applied together at tick
# end, and the mask accumulates the rows they touch.
def tick_sup(r: Array<U32> & List<U32>, todo: List<&2, U32>) -> Array<U32> & Dirty.Mask:
  match r:
    case (world2, sws):
      tick_commit_phases(phases(8n, 0, (world2, Nil{}), todo, Rules.wake_writes(sws)))

def tick_go(r: Array<U32> & List<&2, U32>) -> Array<U32> & Dirty.Mask:
  match r:
    case (world2, +todo):
      tick_sup(Support.pass_todo(world2, todo), todo)

def tick_m(r: Array<U32> & Dirty.Mask) -> Array<U32> & Dirty.Mask:
  tick_go(Dirty.dirty_todo(r))

def ticks_m(fuel: Nat, r: Array<U32> & Dirty.Mask) -> Array<U32> & Dirty.Mask:
  match fuel:
    case 0n:
      r
    case 1n+p:
      ticks_m(p, tick_m(r))

def ticks_step(r: Array<U32> & Dirty.Mask) -> Array<U32>:
  match r:
    case (w, _):
      w

# `tick` primes the mask from the world (one scan); `ticks` primes once and then
# carries it across the whole run, so only the first tick scans the world.
def tick(world: Array<U32>) -> Array<U32>:
  ticks_step(tick_m(Dirty.active_mask(world)))

def ticks(fuel: Nat, world: Array<U32>) -> Array<U32>:
  ticks_step(ticks_m(fuel, Dirty.active_mask(world)))
