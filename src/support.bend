import Base
import ./grid.bend as Grid
import ./cell.bend as Cell
import ./ops.bend as Ops

# V0-4b-2/3 (rule 9): the support pass no longer applies its wake inline; a crush
# conses the crushed cell onto `wakes`, and the tick applies the accumulated
# wakes at tick end. So within a tick the support pass only ever *clears* active
# bits (a crush).
#
# V0-4b-3: the machine is *driven* either by a full scan (`scan = True`, used by
# the setup `pass_all`) or by a work list of active cells (`scan = False`, used
# by the tick), so the tick no longer scans the world for support. The per-cell
# writes are identical; only the advance differs, and the advance writes nothing
# (the `sup_m` mirror tracks the per-cell writes, so its Φ claim is unaffected).

def sup(
  fuel: Nat,
  gp: Array<U32> & U32,
  +sel: U32,
  +i: U32,
  +w: U32,
  +gated: Bool,
  wakes: List<U32>,
  todo: List<&2, U32>,
  +scan: Bool
) -> Array<U32> & List<U32>:
  match fuel:
    case 0n:
      match gp:
        case (world, _):
          (world, wakes)
    case 1n+p:
      match gp:
        case (world, gv):
          match sel:
            case 0:
              +v = gv
              act = U32.is_ne(Cell.active(v), 0)
              okg = Bool.or(Bool.not(gated), act)
              coh = U32.is_ne(Cell.cohesion(v), 0)
              st = Cell.static(Cell.material(v))
              want = Bool.and(okg, Bool.and(coh, Bool.not(st)))
              sup(p, (world, v), Bool.pick(U32, want, 1, 9), i, v, gated, wakes, todo, scan)
            case 1:
              +v = gv
              adj = Ops.shell_adjacent(i)
              sup(p, (world, v), Bool.pick(U32, adj, 4, 5), i, w, gated, wakes, todo, scan)
            case 5:
              q = Array.get(U32, world, Grid.below(i))
              sup(p, q, 2, i, w, gated, wakes, todo, scan)
            case 2:
              +b = gv
              bcoh = U32.is_ne(Cell.cohesion(b), 0)
              bsup = U32.is_ne(Cell.support(b), 0)
              sup(p, (world, b), Bool.pick(U32, Bool.and(bcoh, bsup), 3, 6), i, w, gated, wakes, todo, scan)
            case 3:
              sv = Cell.support(gv)
              world = world[i] <- Ops.set_support(w, sv)
              q = Array.get(U32, world, i)
              sup(p, q, 9, i, 0, gated, wakes, todo, scan)
            case 4:
              world = world[i] <- Ops.set_support(w, 31)
              q = Array.get(U32, world, i)
              sup(p, q, 9, i, 0, gated, wakes, todo, scan)
            case 6:
              crushed = Ops.crush_if_rock(w)
              world = world[i] <- crushed
              q = Array.get(U32, world, i)
              sup(p, q, 9, i, 0, gated, i <> wakes, todo, scan)
            case 9:
              match todo:
                case Nil{}:
                  match scan:
                    case True{}:
                      +ni = U32.add(i, 1)
                      sup(p, (world, gv), Bool.pick(U32, U32.is_eq(ni, Grid.volume()), 10, 11), i, 0, gated, wakes, Nil{}, scan)
                    case False{}:
                      (world, wakes)
                case Con{+h, t}:
                  q = Array.get(U32, world, h)
                  sup(p, q, 0, h, 0, gated, wakes, t, scan)
            case 10:
              (world, wakes)
            case 11:
              +ni = U32.add(i, 1)
              q = Array.get(U32, world, ni)
              sup(p, q, 0, ni, 0, gated, wakes, todo, scan)
            case _:
              (world, wakes)

def wake_all(wakes: List<U32>, world: Array<U32>) -> Array<U32>:
  match wakes:
    case Nil{}:
      world
    case Con{h, t}:
      wake_all(t, Ops.wake(world, h))

def pass_gated(world: Array<U32>, +gated: Bool) -> Array<U32> & List<U32>:
  q = Array.get(U32, world, 0)
  sup(U32.to_nat(16777216), q, 0, 0, 0, gated, Nil{}, Nil{}, True{})

# The tick's entry: run support over the work list `todo` (ascending, so the
# bottom-up `below` propagation matches the scan).
def pass_todo(world: Array<U32>, todo: List<&2, U32>) -> Array<U32> & List<U32>:
  match todo:
    case Nil{}:
      (world, Nil{})
    case Con{+h, t}:
      q = Array.get(U32, world, h)
      sup(U32.to_nat(16777216), q, 0, h, 0, True{}, Nil{}, t, False{})

def pass_commit(r: Array<U32> & List<U32>) -> Array<U32>:
  match r:
    case (world, wakes):
      wake_all(wakes, world)

# Setup passes apply the wakes immediately (they are not a tick).
def pass(world: Array<U32>) -> Array<U32>:
  pass_commit(pass_gated(world, True{}))

def pass_all(world: Array<U32>) -> Array<U32>:
  pass_commit(pass_gated(world, False{}))
