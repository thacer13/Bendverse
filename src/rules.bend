import Base
import ./grid.bend as Grid
import ./cell.bend as Cell
import ./ops.bend as Ops

def color_of(+i: U32) -> U32:
  (U32.and(Grid.ix(i), 1)
   .|. (U32.and(Grid.iy(i), 1) << 1n)
   .|. (U32.and(Grid.iz(i), 1) << 2n) : U32)

def side_index(i: U32, k: U32) -> U32:
  match k:
    case 0:
      Grid.neighbor(i, 4294967295, 0, 0)
    case 1:
      Grid.neighbor(i, 1, 0, 0)
    case 2:
      Grid.neighbor(i, 0, 0, 4294967295)
    case 3:
      Grid.neighbor(i, 0, 0, 1)
    case _:
      i

def diag_index(i: U32, k: U32) -> U32:
  match k:
    case 0:
      Grid.neighbor(i, 4294967295, 4294967295, 0)
    case 1:
      Grid.neighbor(i, 1, 4294967295, 0)
    case 2:
      Grid.neighbor(i, 0, 4294967295, 4294967295)
    case 3:
      Grid.neighbor(i, 0, 4294967295, 1)
    case _:
      i

def mov(+w: U32) -> U32:
  nf = U32.min(U32.add(Cell.fall(w), 1), 63)
  Cell.encode(Cell.material(w), Cell.cohesion(w), Cell.active(w), Cell.support(w), nf)

# ============================================================================
# V0-1 — purity of phases (`C1`/`R1`/`R3`/`R9`)
#
# A phase is a *pure function* of the state it is handed:
#
#   phase(state) = apply(resolve(intent(state)))
#
# `plan` is `intent` plus the (pure) contention resolution: it folds over the
# phase colour's cells and, for each, decides an action from the *pre-phase*
# state only, accumulating the resulting writes in `sets`/`wakes`. It never
# writes the array it reads, so no part of the phase can observe another part's
# output. `commit_sets`/`commit_wakes` then apply the write set.
#
# The retired `Rules.step` did the opposite: it wrote `deactivate` to the cell it
# was inspecting, re-read cells a sibling had just moved into (T23), and woke
# neighbours that the same phase then evaluated (T24). Both are gone here:
#
#   * every read is a read of the pre-phase array (the array is never written by
#     `plan`), so a later mover cannot re-read a target an earlier mover wrote;
#   * wake is applied only after the whole colour's writes are in (`commit_wakes`),
#     so a phase never pulls in a cell it woke — the evaluated set is fixed when
#     the phase begins (rule 9).
#
# Contention (rule 3) is resolved from the pre-phase state. Two cells can only
# share a diagonal target if they are the two opposite-direction claimants on the
# same axis (`(4,40,4)`/`(6,40,4)` → `(5,39,4)`, both colour 0); the smaller flat
# index owns the target and the other forfeits to the impact path. Drop and crush
# targets are already injective within a colour (they sit one `y` below, and
# `below` is injective), so no other tie-break is needed. `V0-3` replaces this
# local check with explicit `(colour × direction)` batching and proves the target
# map injective; the tie-break here is the V0-1 stop-gap (see `PLAN.md` §5.3, `G3`).
#
# `step_m`/`sup_m` (the `PT` mirror layer) mirror the retired `Rules.step` and are
# **not** extended: they are retired, not evidence (`PLAN.md` §3.4, §4.1).
# ----------------------------------------------------------------------------

type Write is Data:
  WSet{idx: U32, val: U32}
  WWake{idx: U32}

def dir_dx(+k: U32) -> U32:
  match k:
    case 0: 4294967295
    case 1: 1
    case _: 0

def dir_dz(+k: U32) -> U32:
  match k:
    case 2: 4294967295
    case 3: 1
    case _: 0

# Would `w` enter a cell holding `t`? (empty, or strictly lighter than `w`.)
def can_enter(+w: U32, +t: U32) -> Bool:
  Bool.or(U32.is_eq(Cell.material(t), 0),
    U32.is_lt(Cell.density(Cell.material(t)), Cell.density(Cell.material(w))))

# The V0-1 contention tie-break predicate: is `wc` the kind of cell that could
# claim a diagonal target at all? Deliberately pre-phase and order-free.
def capable(+wc: U32) -> Bool:
  +m = Cell.material(wc)
  Bool.and(U32.is_ne(Cell.active(wc), 0),
    Bool.and(Bool.not(Bool.or(U32.is_eq(m, 0), Cell.static(m))),
      Bool.and(U32.is_eq(Cell.cohesion(wc), 0), Cell.slides(m))))

def dmg_of(+w: U32, +b: U32) -> Bool:
  +f = Cell.fall(w)
  Bool.and(U32.is_ne(f, 0),
    Bool.and(Bool.not(Cell.static(Cell.material(b))), U32.is_ge(f, Cell.cohesion(b))))

# The pure fold. `gp` threads the array through reads and is never written, so
# every read sees the pre-phase state. Selectors mirror the retired `step` state
# machine; the terminal states cons their writes onto `sets`/`wakes`.
#   sel 0..4   start / activity / cohesion skip (4 deactivates an idle cell)
#   sel 5..7   drop: read below, swap
#   sel 8..13  diagonal search over the four horizontal-below directions
#   sel 21..23 impact: crush rock or clear fall
#   sel 30..32 contention resolve: read the opposite claimant, then move or forfeit
#   sel 14..16 end of cell / next cell of the colour
def plan(
  fuel: Nat,
  gp: Array<U32> & U32,
  +sel: U32,
  +i: U32,
  +c: U32,
  +w: U32,
  +k: U32,
  +b: U32,
  +d: U32,
  +ic: U32,
  sets: List<Write>,
  wakes: List<Write>
) -> Array<U32> & List<Write> & List<Write>:
  match fuel:
    case 0n:
      match gp:
        case (world, _):
          (world, sets, wakes)
    case 1n+p:
      match gp:
        case (world, +gv):
          match sel:
            case 0:
              +ab = U32.is_ne(Cell.active(gv), 0)
              plan(p, (world, gv), Bool.pick(U32, ab, 1, 2), i, c, gv, k, b, d, ic, sets, wakes)
            case 1:
              +m = Cell.material(w)
              +skip = Bool.or(Bool.or(U32.is_eq(m, 0), Cell.static(m)), U32.is_ne(Cell.cohesion(w), 0))
              plan(p, (world, gv), Bool.pick(U32, skip, 4, 5), i, c, w, k, b, d, ic, sets, wakes)
            case 2:
              plan(p, (world, gv), 14, i, c, w, k, b, d, ic, sets, wakes)
            case 4:
              plan(p, (world, gv), 14, i, c, w, k, b, d, ic,
                WSet{i, Cell.deactivate(w)} <> sets, wakes)
            case 5:
              q = Array.get(U32, world, Grid.below(i))
              plan(p, q, 6, i, c, w, k, b, d, ic, sets, wakes)
            case 6:
              +can = can_enter(w, gv)
              plan(p, (world, gv), Bool.pick(U32, can, 7, 8), i, c, w, k, gv, d, ic, sets, wakes)
            case 7:
              +nb = Grid.below(i)
              plan(p, (world, gv), 14, i, c, w, k, b, d, ic,
                WSet{nb, mov(w)} <> (WSet{i, gv} <> sets),
                WWake{nb} <> (WWake{i} <> wakes))
            case 8:
              +sl = Cell.slides(Cell.material(w))
              plan(p, (world, gv), Bool.pick(U32, sl, 9, 21), i, c, w, 0, b, d, ic, sets, wakes)
            case 9:
              q = Array.get(U32, world, side_index(i, k))
              plan(p, q, 10, i, c, w, k, b, d, ic, sets, wakes)
            case 10:
              +ce = can_enter(w, gv)
              plan(p, (world, gv), Bool.pick(U32, ce, 11, 12), i, c, w, k, b, d, ic, sets, wakes)
            case 11:
              q = Array.get(U32, world, diag_index(i, k))
              plan(p, q, 13, i, c, w, k, b, d, ic, sets, wakes)
            case 12:
              +nk = U32.add(k, 1)
              +fin = U32.is_eq(nk, 4)
              plan(p, (world, gv), Bool.pick(U32, fin, 21, 9), i, c, w, nk, b, d, ic, sets, wakes)
            case 13:
              +ce2 = can_enter(w, gv)
              plan(p, (world, gv), Bool.pick(U32, ce2, 30, 12), i, c, w, k, b, gv, ic, sets, wakes)
            case 30:
              +dx = dir_dx(k)
              +dz = dir_dz(k)
              +ic0 = Grid.neighbor(i, U32.add(dx, dx), 0, U32.add(dz, dz))
              q = Array.get(U32, world, ic0)
              plan(p, q, 31, i, c, w, k, b, d, ic0, sets, wakes)
            case 31:
              +lose = Bool.and(capable(gv), U32.is_lt(ic, i))
              plan(p, (world, gv), Bool.pick(U32, lose, 21, 32), i, c, w, k, b, d, ic, sets, wakes)
            case 32:
              +nd = diag_index(i, k)
              plan(p, (world, gv), 14, i, c, w, k, b, d, ic,
                WSet{nd, w} <> (WSet{i, d} <> sets),
                WWake{nd} <> (WWake{i} <> wakes))
            case 21:
              +dmg = dmg_of(w, b)
              plan(p, (world, gv), Bool.pick(U32, dmg, 22, 23), i, c, w, k, b, d, ic, sets, wakes)
            case 22:
              +nb = Grid.below(i)
              plan(p, (world, gv), 14, i, c, w, k, b, d, ic,
                WSet{nb, Ops.crush_if_rock(b)} <> (WSet{i, Ops.set_fall0(w)} <> sets),
                WWake{nb} <> (WWake{i} <> wakes))
            case 23:
              plan(p, (world, gv), 14, i, c, w, k, b, d, ic,
                WSet{i, Ops.set_fall0(w)} <> sets, wakes)
            case 14:
              +last = U32.is_eq(i, Grid.color_last(c))
              plan(p, (world, gv), Bool.pick(U32, last, 15, 16), i, c, w, k, b, d, ic, sets, wakes)
            case 15:
              (world, sets, wakes)
            case 16:
              +ni = Grid.next_color(i, c)
              q = Array.get(U32, world, ni)
              plan(p, q, 0, ni, c, 0, 0, 0, 0, 0, sets, wakes)
            case _:
              (world, sets, wakes)

# The shrinking list is the first parameter so the recursive call is a
# decreasing self-call (`world[idx] <- val` is not an unchanged argument).
def commit_sets(writes: List<Write>, world: Array<U32>) -> Array<U32>:
  match writes:
    case Nil{}:
      world
    case Con{h, t}:
      match h:
        case WSet{idx, val}:
          commit_sets(t, world[idx] <- val)
        case WWake{idx}:
          commit_sets(t, world)

def commit_wakes(writes: List<Write>, world: Array<U32>) -> Array<U32>:
  match writes:
    case Nil{}:
      world
    case Con{h, t}:
      match h:
        case WWake{idx}:
          commit_wakes(t, Ops.wake(world, idx))
        case WSet{idx, val}:
          commit_wakes(t, world)

def phase_commit(r: Array<U32> & List<Write> & List<Write>) -> Array<U32>:
  match r:
    case (world, sets, wakes):
      commit_wakes(wakes, commit_sets(sets, world))

# One phase: read-only intent fold over colour `c`, then apply the write set.
def phase(world: Array<U32>, +c: U32) -> Array<U32>:
  +i0 = Grid.color_base(c)
  q = Array.get(U32, world, i0)
  phase_commit(plan(U32.to_nat(16777216), q, 0, i0, c, 0, 0, 0, 0, 0, Nil{}, Nil{}))
