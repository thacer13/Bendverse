import Base
import ./grid.bend as Grid
import ./cell.bend as Cell
import ./ops.bend as Ops
import ./window.bend as Window
import ./wgrid.bend as WGrid

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

# A movement write: the mover's material/support, `fall` advanced, and the active
# bit **cleared**. Rule 9 says a write marks the target active for the *next*
# tick; the move already emits `WWake{nb}` (deferred by V0-4a), which re-activates
# it at tick end. Keeping the bit set here would let a later colour phase
# re-evaluate the mover in the same tick (a per-tick fall speed > 1). The impact
# path (`Ops.set_fall0`) already clears active and relies on the same wake.
def mov(+w: U32) -> U32:
  nf = U32.min(U32.add(Cell.fall(w), 1), 63)
  Cell.encode(Cell.material(w), Cell.cohesion(w), 0, Cell.support(w), nf)

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
# output. `commit_sets` applies the set writes; the tick applies the pending wakes
# (mask-aware, `Sim.commit_wakes_mask`).
#
# The retired `Rules.step` did the opposite: it wrote `deactivate` to the cell it
# was inspecting, re-read cells a sibling had just moved into (T23), and woke
# neighbours that the same phase then evaluated (T24). Both are gone here:
#
#   * every read is a read of the pre-phase array (the array is never written by
#     `plan`), so a later mover cannot re-read a target an earlier mover wrote;
#   * wake is applied only after the whole colour's writes are in (`commit_wakes_mask`,
#     `src/sim.bend`), so a phase never pulls in a cell it woke — the evaluated set
#     is fixed when the phase begins (rule 9).
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
# Closure (`C2`, `V0-2`): every target a rule writes is guarded by
# `Grid.step_inside`, so a step off the box is inert instead of wrapping to the
# opposite face. On the generated world this changes nothing (the bedrock shell
# already blocks those steps); it makes the box a property of the grid rather
# than of the shell, so painting the shell away can no longer open it.
#
# `step_m`/`sup_m` (the `PT` mirror layer) mirror the retired `Rules.step` and are
# **not** extended: they are retired, not evidence (`PLAN.md` §3.4, §4.1).
# ----------------------------------------------------------------------------

# ------------------------------------------------------------------ write effects
# A write's *effect* is a value, not a `U32`.
#
# This is what makes the engine's write set closed **by construction**: `plan` can
# only emit an `Op`, so "the write set is exactly the classified effects" is a
# typing fact rather than an inspection of the code (`G14`). Each constructor has
# a proven Φ effect — the `PresOp` family preserves Φ
# (`Selector.array_write_preserves_phi`) and `OCrushIfRock` lowers it by a guarded
# gap (`Tick.array_guarded_crush_lowers`) — so `array_op_phi` below is total.
#
# The split into `PresOp` (material-preserving) and the material-changing crush
# is what lets the preserving laws be total over their own type: material
# preservation is exactly the hypothesis `mat_pres` discharges.
#
type PresOp is Data:
  OId{}
  OSupport{s: U32}
  OFall0{}
  OMov{}
  OAct{}
  ODeact{}

def apply_pres(+w: U32, +op: PresOp) -> U32:
  match op:
    case OId{}:
      w
    case OSupport{+s}:
      Ops.set_support(w, s)
    case OFall0{}:
      Ops.set_fall0(w)
    case OMov{}:
      mov(w)
    case OAct{}:
      Cell.activate(w)
    case ODeact{}:
      Cell.deactivate(w)

type Op is Data:
  OPres{op: PresOp}
  OCrushIfRock{}

def apply_op(+w: U32, +op: Op) -> U32:
  match op:
    case OPres{+p}:
      apply_pres(w, p)
    case OCrushIfRock{}:
      Ops.crush_if_rock(w)

type Write is Data:
  WSet{idx: U32, op: Op, src: U32}
  WWake{idx: U32}

# V0-3: the four slide directions are a *closed set*, not a `U32` loop index.
# The retired `side_index`/`diag_index` (kept below for the frozen `step_m`
# mirror) take a `U32 k` and end with `case _: i`, so a `k` outside `{0,1,2,3}`
# silently becomes a self-target (PLAN §4.2 landmine). The live phase uses
# `Dir4`, where every direction is a constructor and every match is total, so
# the silent default does not exist in the engine that runs.
#
# A `Dir4` is exactly a displacement `(dir_dx, -1, dir_dz)`: the `-1` is the
# move's `y` component (slide-and-fall), so a direction batch is the translation
# `i |-> Grid.neighbor(i, dir_dx(k), 4294967295, dir_dz(k))`. `batch.bend` proves
# that translation injective, which is rule 4's "distinct targets".
type Dir4 is Data:
  K0{}
  K1{}
  K2{}
  K3{}

def dir_dx(+k: Dir4) -> U32:
  match k:
    case K0{}: 4294967295
    case K1{}: 1
    case _: 0

def dir_dz(+k: Dir4) -> U32:
  match k:
    case K2{}: 4294967295
    case K3{}: 1
    case _: 0

def side4_w(+win: Window.Window, i: U32, +k: Dir4) -> U32:
  match k:
    case K0{}: WGrid.wgrid_neighbor(win, i, 4294967295, 0, 0)
    case K1{}: WGrid.wgrid_neighbor(win, i, 1, 0, 0)
    case K2{}: WGrid.wgrid_neighbor(win, i, 0, 0, 4294967295)
    case K3{}: WGrid.wgrid_neighbor(win, i, 0, 0, 1)

def side4(i: U32, +k: Dir4) -> U32:
  side4_w(Window.canonical(), i, k)

def diag4_w(+win: Window.Window, i: U32, +k: Dir4) -> U32:
  match k:
    case K0{}: WGrid.wgrid_neighbor(win, i, 4294967295, 4294967295, 0)
    case K1{}: WGrid.wgrid_neighbor(win, i, 1, 4294967295, 0)
    case K2{}: WGrid.wgrid_neighbor(win, i, 0, 4294967295, 4294967295)
    case K3{}: WGrid.wgrid_neighbor(win, i, 0, 4294967295, 1)

def diag4(i: U32, +k: Dir4) -> U32:
  diag4_w(Window.canonical(), i, k)

def dir_last(+k: Dir4) -> Bool:
  match k:
    case K3{}: True{}
    case _: False{}

def dir_next(+k: Dir4) -> Dir4:
  match k:
    case K0{}: K1{}
    case K1{}: K2{}
    case K2{}: K3{}
    case K3{}: K0{}

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
#   sel 14     end of cell: advance to the next `todo` index, or stop
#
# V0-4b: the scan domain is the work list `todo` (the active cells of this phase)
# instead of the colour sub-lattice. `c` was only ever used for the advance
# (`color_last`/`next_color`); the per-cell decisions never read it, and V0-1
# makes a phase's result independent of evaluation order, so any order of `todo`
# gives the same write set. The evaluated set is exact because a move now clears
# the mover's active bit and wake is deferred (V0-4a), so the active set only
# shrinks within a tick.
def plan(
  +win: Window.Window,
  fuel: Nat,
  gp: Array<U32> & U32,
  +sel: U32,
  +i: U32,
  +w: U32,
  +k: Dir4,
  +b: U32,
  +d: U32,
  +ic: U32,
  sets: List<Write>,
  wakes: List<Write>,
  todo: List<&2, U32>
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
              plan(win, p, (world, gv), Bool.pick(U32, ab, 1, 2), i, gv, k, b, d, ic, sets, wakes, todo)
            case 1:
              +m = Cell.material(w)
              +skip = Bool.or(Bool.or(U32.is_eq(m, 0), Cell.static(m)), U32.is_ne(Cell.cohesion(w), 0))
              plan(win, p, (world, gv), Bool.pick(U32, skip, 4, 5), i, w, k, b, d, ic, sets, wakes, todo)
            case 2:
              plan(win, p, (world, gv), 14, i, w, k, b, d, ic, sets, wakes, todo)
            case 4:
              plan(win, p, (world, gv), 14, i, w, k, b, d, ic,
                WSet{i, OPres{ODeact{}}, w} <> sets, wakes, todo)
            case 5:
              q = Array.get(U32, world, WGrid.wgrid_below(win, i))
              plan(win, p, q, 6, i, w, k, b, d, ic, sets, wakes, todo)
            case 6:
              +can = Bool.and(can_enter(w, gv), WGrid.wgrid_step_inside(win, i, 0, 4294967295, 0))
              plan(win, p, (world, gv), Bool.pick(U32, can, 7, 8), i, w, k, gv, d, ic, sets, wakes, todo)
            case 7:
              +nb = WGrid.wgrid_below(win, i)
              plan(win, p, (world, gv), 14, i, w, k, b, d, ic,
                WSet{nb, OPres{OMov{}}, w} <> (WSet{i, OPres{OId{}}, gv} <> sets),
                WWake{nb} <> (WWake{i} <> wakes), todo)
            case 8:
              +sl = Cell.slides(Cell.material(w))
              plan(win, p, (world, gv), Bool.pick(U32, sl, 9, 21), i, w, K0{}, b, d, ic, sets, wakes, todo)
            case 9:
              q = Array.get(U32, world, side4_w(win, i, k))
              plan(win, p, q, 10, i, w, k, b, d, ic, sets, wakes, todo)
            case 10:
              +ce = can_enter(w, gv)
              plan(win, p, (world, gv), Bool.pick(U32, ce, 11, 12), i, w, k, b, d, ic, sets, wakes, todo)
            case 11:
              q = Array.get(U32, world, diag4_w(win, i, k))
              plan(win, p, q, 13, i, w, k, b, d, ic, sets, wakes, todo)
            case 12:
              +fin = dir_last(k)
              plan(win, p, (world, gv), Bool.pick(U32, fin, 21, 9), i, w, dir_next(k), b, d, ic, sets, wakes, todo)
            case 13:
              +ce2 = Bool.and(can_enter(w, gv), WGrid.wgrid_step_inside(win, i, dir_dx(k), 4294967295, dir_dz(k)))
              plan(win, p, (world, gv), Bool.pick(U32, ce2, 30, 12), i, w, k, b, gv, ic, sets, wakes, todo)
            case 30:
              +dx = dir_dx(k)
              +dz = dir_dz(k)
              +ic0 = WGrid.wgrid_neighbor(win, i, U32.add(dx, dx), 0, U32.add(dz, dz))
              q = Array.get(U32, world, ic0)
              plan(win, p, q, 31, i, w, k, b, d, ic0, sets, wakes, todo)
            case 31:
              # The opposite claimant only counts if it is inside the box: a
              # wrapped neighbour cannot reach the shared target (boundary moves
              # are inert), so it must not steal the target from `i`.
              +two_dx = U32.add(dir_dx(k), dir_dx(k))
              +two_dz = U32.add(dir_dz(k), dir_dz(k))
              +lose = Bool.and(WGrid.wgrid_step_inside(win, i, two_dx, 0, two_dz),
                        Bool.and(capable(gv), U32.is_lt(ic, i)))
              plan(win, p, (world, gv), Bool.pick(U32, lose, 21, 32), i, w, k, b, d, ic, sets, wakes, todo)
            case 32:
              +nd = diag4_w(win, i, k)
              plan(win, p, (world, gv), 14, i, w, k, b, d, ic,
                WSet{nd, OPres{ODeact{}}, w} <> (WSet{i, OPres{OId{}}, d} <> sets),
                WWake{nd} <> (WWake{i} <> wakes), todo)
            case 21:
              +dmg = Bool.and(dmg_of(w, b), WGrid.wgrid_step_inside(win, i, 0, 4294967295, 0))
              plan(win, p, (world, gv), Bool.pick(U32, dmg, 22, 23), i, w, k, b, d, ic, sets, wakes, todo)
            case 22:
              +nb = WGrid.wgrid_below(win, i)
              plan(win, p, (world, gv), 14, i, w, k, b, d, ic,
                WSet{nb, OCrushIfRock{}, b} <> (WSet{i, OPres{OFall0{}}, w} <> sets),
                WWake{nb} <> (WWake{i} <> wakes), todo)
            case 23:
              plan(win, p, (world, gv), 14, i, w, k, b, d, ic,
                WSet{i, OPres{OFall0{}}, w} <> sets, wakes, todo)
            case 14:
              match todo:
                case Nil{}:
                  (world, sets, wakes)
                case Con{+h, t}:
                  q = Array.get(U32, world, h)
                  plan(win, p, q, 0, h, 0, K0{}, 0, 0, 0, sets, wakes, t)
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
        case WSet{idx, op, src}:
          commit_sets(t, world[idx] <- apply_op(src, op))
        case WWake{idx}:
          commit_sets(t, world)

# V0-4b-2: the support pass returns its crushed-cell wake indices as a
# `List<U32>`; convert them to `WWake` writes so the tick can apply the support
# and phase wakes together at tick end.
def wake_writes(xs: List<U32>) -> List<Write>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      WWake{h} <> wake_writes(t)

# One phase, writes applied and wakes pending.
def phase_pending(r: Array<U32> & List<Write> & List<Write>) -> Array<U32> & List<Write>:
  match r:
    case (world, sets, wakes):
      (commit_sets(sets, world), wakes)

# V0-4a (rule 9): the phase's *writes* land now, its *wakes* are returned
# pending. The tick threads the returned wake lists through all eight phases and
# applies them once at the end, so a later phase of the same tick cannot evaluate
# a cell an earlier phase woke (the `G12` deviation).
#
# V0-4b: the phase runs over its work list `todo` (the active cells of the phase
# colour, in any order) instead of the colour sub-lattice.
def phase_plan_w(win: Window.Window, world: Array<U32>, todo: List<&2, U32>) -> Array<U32> & List<Write>:
  match todo:
    case Nil{}:
      (world, Nil{})
    case Con{+h, t}:
      q = Array.get(U32, world, h)
      phase_pending(plan(win, U32.to_nat(16777216), q, 0, h, 0, K0{}, 0, 0, 0, Nil{}, Nil{}, t))
