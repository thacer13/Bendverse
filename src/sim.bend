import Base
import ./cell.bend as Cell
import ./grid.bend as Grid
import ./rules.bend as Rules
import ./support.bend as Support
import ./worldgen.bend as Worldgen
import ./ops.bend as Ops
import ./dirty.bend as Dirty
import ./window.bend as Window
import ./wgrid.bend as WGrid

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
  +win: Window.Window, world: Array<U32>, +c: U32, +todo: List<&2, U32>
) -> Array<U32> & List<Rules.Write>:
  Rules.phase_plan_w(win, world, filter_color(todo, c))

def phase_get(r: Array<U32> & List<Rules.Write>) -> Array<U32>:
  match r:
    case (world2, _):
      world2

def phase_todo(win: Window.Window, r: Array<U32> & List<&2, U32>, +c: U32) -> Array<U32>:
  match r:
    case (world2, todo):
      phase_get(phase_w(win, world2, c, todo))

def phase(world: Array<U32>, +c: U32) -> Array<U32>:
  phase_todo(Window.canonical(), active_list(world), c)

# `phases` folds colours `0 .. 7`. `r` is the *previous* phase's result (the
# initial call passes the support-passed world with no writes); `todo` is the
# full work list, reused by each colour (hence `+todo`). The result is handed as
# a parameter so the pair can be matched without a local binder (Bend matches
# only parameters/fields).
def phases(
  +win: Window.Window, fuel: Nat, +c: U32, r: Array<U32> & List<Rules.Write>, +todo: List<&2, U32>, wakes: List<Rules.Write>
) -> Array<U32> & List<Rules.Write>:
  match fuel:
    case 0n:
      match r:
        case (world2, ws):
          (world2, List.append(&1, Rules.Write, ws, wakes))
    case 1n+p:
      match r:
        case (world2, ws):
          phases(win, p, U32.add(c, 1), phase_w(win, world2, c, todo), todo, List.append(&1, Rules.Write, ws, wakes))

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
  +win: Window.Window, writes: List<Rules.Write>, world: Array<U32>, m: Dirty.Mask
) -> Array<U32> & Dirty.Mask:
  match writes:
    case Nil{}:
      (world, m)
    case Con{h, t}:
      match h:
        case Rules.WSet{idx, op, src}:
          commit_wakes_mask(win, t, world, m)
        case Rules.WWake{+idx}:
          w2 = Ops.wake_w(win, world, idx)
          +m2 = Dirty.mark_wake(m, idx)
          commit_wakes_mask(win, t, w2, m2)

def tick_commit_phases(win: Window.Window, r: Array<U32> & List<Rules.Write>) -> Array<U32> & Dirty.Mask:
  match r:
    case (world3, wakes):
      commit_wakes_mask(win, wakes, world3, Dirty.zermask())

# ------------------------------------------------------------------ trace (P1)
# `tick_trace` is the engine's tick plus a *delta list*: one entry per cell the
# tick changed, carrying the cell's coordinate and its NEW word. It is the same
# world computation as `tick` (in fact `tick` is `tick_trace` with the deltas
# dropped), so no behaviour changes.
#
# Coordinate. The live world is the fixed 64^3 torus; a `Rules.Write.idx` is the
# flat `Grid.index` index `x + z*64 + y*4096` with each axis masked `&63`
# (`Grid.index`), so its global coordinate is exactly
#   (Grid.ix(idx), Grid.iy(idx), Grid.iz(idx))
#     = (idx&63, (idx>>12)&63, (idx>>6)&63).
# We carry the global coordinate, not the flat index, so a consumer (Bendview)
# never has to know the flat layout. (`Grid.ix/iy/iz` are the inverse of
# `Grid.index` on the torus; `index_roundtrip` is that law.)
#
# `WWake` is activity, not a render change: it only sets the active bit (bit 11)
# and is applied at tick end (`commit_wakes_mask`). The deltas are therefore the
# `WSet` entries -- the changes a renderer mirrors. `Delta.val` is the *effect*
# `Rules.apply_op(src, op)`, computed here so Bendview does not re-implement
# `Rules.apply_op`.
type Delta is Data:
  Delta{x: U32, y: U32, z: U32, val: U32}

# `commit_trace` is `Rules.commit_sets` plus the delta list: it consumes the same
# `WSet` writes in the same order (so the world is bit-identical), records a
# `Delta` per `WSet`, and ignores `WWake` (applied later by `commit_wakes_mask`).
# The result is matched through a parameter (`commit_trace_cons`) because Bend
# cannot scrutinize a computed value.
def commit_trace_cons(+win: Window.Window, r: Array<U32> & List<Delta> & List<Rules.Write>, +idx: U32, +nv: U32) -> Array<U32> & List<Delta> & List<Rules.Write>:
  match r:
    case (world2, ds, wakes):
      (world2, Delta{WGrid.wgrid_ix(win, idx), WGrid.wgrid_iy(win, idx), WGrid.wgrid_iz(win, idx), nv} <> ds, wakes)

def commit_trace(+win: Window.Window, writes: List<Rules.Write>, world: Array<U32>, wakes: List<Rules.Write>) -> Array<U32> & List<Delta> & List<Rules.Write>:
  match writes:
    case Nil{}:
      (world, Nil{}, wakes)
    case Con{h, t}:
      match h:
        case Rules.WSet{+idx, op, src}:
          +nv = Rules.apply_op(src, op)
          commit_trace_cons(win, commit_trace(win, t, world[idx] <- nv, wakes), idx, nv)
        case Rules.WWake{idx}:
          commit_trace(win, t, world, wakes)

# The trace twin of `phase_pending`: commit the phase's set writes (recording
# their deltas) and carry the pending wakes through unchanged. `commit_trace`
# returns the 3-tuple directly so no 2-tuple is re-packed into a 3-tuple (a Bend
# shape the checker rejects).
def phase_pending_trace(win: Window.Window, r: Array<U32> & List<Rules.Write> & List<Rules.Write>) -> Array<U32> & List<Delta> & List<Rules.Write>:
  match r:
    case (world, sets, wakes):
      commit_trace(win, sets, world, wakes)

def phase_plan_w_trace(+win: Window.Window, world: Array<U32>, todo: List<&2, U32>) -> Array<U32> & List<Delta> & List<Rules.Write>:
  match todo:
    case Nil{}:
      (world, Nil{}, Nil{})
    case Con{+h, t}:
      q = Array.get(U32, world, h)
      phase_pending_trace(win, Rules.plan(win, U32.to_nat(16777216), q, 0, h, 0, Rules.K0{}, 0, 0, 0, Nil{}, Nil{}, t))

def phase_w_trace(+win: Window.Window, world: Array<U32>, +c: U32, +todo: List<&2, U32>) -> Array<U32> & List<Delta> & List<Rules.Write>:
  phase_plan_w_trace(win, world, filter_color(todo, c))

# The trace twin of `phases`: same world/wake fold. `r` is the previous phase's
# `(world, deltas, wakes)`; `acc` collects the deltas in application order
# (older phases first) and `wakes` collects the deferred wakes. Replaying `acc`
# in order reconstructs exactly the world `commit_sets` produced.
def phases_trace(
  +win: Window.Window, fuel: Nat, +c: U32, r: Array<U32> & List<Delta> & List<Rules.Write>,
  +todo: List<&2, U32>, acc: List<Delta>, wakes: List<Rules.Write>
) -> Array<U32> & List<Delta> & List<Rules.Write>:
  match fuel:
    case 0n:
      match r:
        case (world2, ds, w2):
          (world2, List.append(&1, Delta, acc, ds), List.append(&1, Rules.Write, w2, wakes))
    case 1n+p:
      match r:
        case (world2, ds, w2):
          phases_trace(win, p, U32.add(c, 1), phase_w_trace(win, world2, c, todo), todo,
            List.append(&1, Delta, acc, ds), List.append(&1, Rules.Write, w2, wakes))

# The trace twin of `commit_wakes_mask`: applies the deferred wakes exactly as
# the live path does (so the world and mask are bit-identical) and threads the
# delta list through untouched.
def commit_wakes_mask_trace(
  +win: Window.Window, writes: List<Rules.Write>, world: Array<U32>, m: Dirty.Mask, ds: List<Delta>
) -> Array<U32> & Dirty.Mask & List<Delta>:
  match writes:
    case Nil{}:
      (world, m, ds)
    case Con{h, t}:
      match h:
        case Rules.WSet{idx, op, src}:
          commit_wakes_mask_trace(win, t, world, m, ds)
        case Rules.WWake{+idx}:
          w2 = Ops.wake_w(win, world, idx)
          +m2 = Dirty.mark_wake(m, idx)
          commit_wakes_mask_trace(win, t, w2, m2, ds)

def tick_commit_phases_trace(win: Window.Window, r: Array<U32> & List<Delta> & List<Rules.Write>) -> Array<U32> & Dirty.Mask & List<Delta>:
  match r:
    case (world3, ds, wakes):
      commit_wakes_mask_trace(win, wakes, world3, Dirty.zermask(), ds)

def tick_sup_trace(+win: Window.Window, r: Array<U32> & List<U32>, todo: List<&2, U32>) -> Array<U32> & Dirty.Mask & List<Delta>:
  match r:
    case (world2, sws):
      tick_commit_phases_trace(win, phases_trace(win, 8n, 0, (world2, Nil{}, Nil{}), todo, Nil{}, Rules.wake_writes(sws)))

def tick_go_trace(+win: Window.Window, r: Array<U32> & List<&2, U32>) -> Array<U32> & Dirty.Mask & List<Delta>:
  match r:
    case (world2, +todo):
      tick_sup_trace(win, Support.pass_todo_w(win, world2, todo), todo)

def tick_m_trace(+win: Window.Window, r: Array<U32> & Dirty.Mask) -> Array<U32> & Dirty.Mask & List<Delta>:
  tick_go_trace(win, Dirty.dirty_todo(r))

# One tick plus its deltas. `tick` below is the world projection.
def tick_trace_got(r: Array<U32> & Dirty.Mask & List<Delta>) -> Array<U32> & List<Delta>:
  match r:
    case (w, _, ds):
      (w, ds)

def tick_trace_w(win: Window.Window, world: Array<U32>) -> Array<U32> & List<Delta>:
  tick_trace_got(tick_m_trace(win, Dirty.active_mask(world)))

def tick_trace(world: Array<U32>) -> Array<U32> & List<Delta>:
  tick_trace_w(Window.canonical(), world)

def tick_world(r: Array<U32> & List<Delta>) -> Array<U32>:
  match r:
    case (w, _):
      w

# The support pass over the work list (wakes deferred), then the eight phases
# over the same list; the support and phase wakes are applied together at tick
# end, and the mask accumulates the rows they touch.
def tick_sup(+win: Window.Window, r: Array<U32> & List<U32>, todo: List<&2, U32>) -> Array<U32> & Dirty.Mask:
  match r:
    case (world2, sws):
      tick_commit_phases(win, phases(win, 8n, 0, (world2, Nil{}), todo, Rules.wake_writes(sws)))

def tick_go(+win: Window.Window, r: Array<U32> & List<&2, U32>) -> Array<U32> & Dirty.Mask:
  match r:
    case (world2, +todo):
      tick_sup(win, Support.pass_todo_w(win, world2, todo), todo)

def tick_m(+win: Window.Window, r: Array<U32> & Dirty.Mask) -> Array<U32> & Dirty.Mask:
  tick_go(win, Dirty.dirty_todo(r))

def ticks_m(+win: Window.Window, fuel: Nat, r: Array<U32> & Dirty.Mask) -> Array<U32> & Dirty.Mask:
  match fuel:
    case 0n:
      r
    case 1n+p:
      ticks_m(win, p, tick_m(win, r))

def ticks_step(r: Array<U32> & Dirty.Mask) -> Array<U32>:
  match r:
    case (w, _):
      w

# `tick` primes the mask from the world (one scan); `ticks` primes once and then
# carries it across the whole run, so only the first tick scans the world. The
# `_w` entries take the resident window (W1: always `Window.canonical()` from the
# plain wrappers); `W5` drives a moving window through them.
def tick_w(win: Window.Window, world: Array<U32>) -> Array<U32>:
  tick_world(tick_trace_w(win, world))

def tick(world: Array<U32>) -> Array<U32>:
  tick_w(Window.canonical(), world)

def ticks_w(win: Window.Window, fuel: Nat, world: Array<U32>) -> Array<U32>:
  ticks_step(ticks_m(win, fuel, Dirty.active_mask(world)))

def ticks(fuel: Nat, world: Array<U32>) -> Array<U32>:
  ticks_w(Window.canonical(), fuel, world)
