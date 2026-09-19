import Base
import ./grid.bend as Grid
import ./cell.bend as Cell
import ./ops.bend as Ops

# V0-4b-2 (rule 9): the support pass no longer applies its wake inline; a crush
# conses the crushed cell onto `wakes`, and the tick applies the accumulated
# wakes at tick end. So within a tick the support pass only ever *clears* active
# bits (a crush). It also collects the active cells it sees into `todo` — the
# tick's phase work list — so no separate active-list scan is needed.

def cons_if(h: U32, xs: List<&2, U32>, b: Bool) -> List<&2, U32>:
  match b:
    case True{}:
      h <> xs
    case False{}:
      xs

def sup(
  fuel: Nat,
  gp: Array<U32> & U32,
  +sel: U32,
  +i: U32,
  +w: U32,
  +gated: Bool,
  wakes: List<U32>,
  todo: List<&2, U32>
) -> Array<U32> & List<U32> & List<&2, U32>:
  match fuel:
    case 0n:
      match gp:
        case (world, _):
          (world, wakes, todo)
    case 1n+p:
      match gp:
        case (world, gv):
          match sel:
            case 0:
              +v = gv
              +act = U32.is_ne(Cell.active(v), 0)
              okg = Bool.or(Bool.not(gated), act)
              coh = U32.is_ne(Cell.cohesion(v), 0)
              st = Cell.static(Cell.material(v))
              want = Bool.and(okg, Bool.and(coh, Bool.not(st)))
              +todo2 = cons_if(i, todo, act)
              sup(p, (world, v), Bool.pick(U32, want, 1, 9), i, v, gated, wakes, todo2)
            case 1:
              +v = gv
              adj = Ops.shell_adjacent(i)
              sup(p, (world, v), Bool.pick(U32, adj, 4, 5), i, w, gated, wakes, todo)
            case 5:
              q = Array.get(U32, world, Grid.below(i))
              sup(p, q, 2, i, w, gated, wakes, todo)
            case 2:
              +b = gv
              bcoh = U32.is_ne(Cell.cohesion(b), 0)
              bsup = U32.is_ne(Cell.support(b), 0)
              sup(p, (world, b), Bool.pick(U32, Bool.and(bcoh, bsup), 3, 6), i, w, gated, wakes, todo)
            case 3:
              sv = Cell.support(gv)
              world = world[i] <- Ops.set_support(w, sv)
              q = Array.get(U32, world, i)
              sup(p, q, 9, i, 0, gated, wakes, todo)
            case 4:
              world = world[i] <- Ops.set_support(w, 31)
              q = Array.get(U32, world, i)
              sup(p, q, 9, i, 0, gated, wakes, todo)
            case 6:
              crushed = Ops.crush_if_rock(w)
              world = world[i] <- crushed
              q = Array.get(U32, world, i)
              sup(p, q, 9, i, 0, gated, i <> wakes, todo)
            case 9:
              +ni = U32.add(i, 1)
              sup(p, (world, gv), Bool.pick(U32, U32.is_eq(ni, Grid.volume()), 10, 11), i, 0, gated, wakes, todo)
            case 10:
              (world, wakes, todo)
            case 11:
              +ni = U32.add(i, 1)
              q = Array.get(U32, world, ni)
              sup(p, q, 0, ni, 0, gated, wakes, todo)
            case _:
              (world, wakes, todo)

def wake_all(wakes: List<U32>, world: Array<U32>) -> Array<U32>:
  match wakes:
    case Nil{}:
      world
    case Con{h, t}:
      wake_all(t, Ops.wake(world, h))

def pass_gated(
  world: Array<U32>, +gated: Bool
) -> Array<U32> & List<U32> & List<&2, U32>:
  q = Array.get(U32, world, 0)
  sup(U32.to_nat(16777216), q, 0, 0, 0, gated, Nil{}, Nil{})

def pass_commit(r: Array<U32> & List<U32> & List<&2, U32>) -> Array<U32>:
  match r:
    case (world, wakes, _):
      wake_all(wakes, world)

# Setup passes apply the wakes immediately (they are not a tick).
def pass(world: Array<U32>) -> Array<U32>:
  pass_commit(pass_gated(world, True{}))

def pass_all(world: Array<U32>) -> Array<U32>:
  pass_commit(pass_gated(world, False{}))
