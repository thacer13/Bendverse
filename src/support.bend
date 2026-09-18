import Base
import ./grid.bend as Grid
import ./cell.bend as Cell
import ./ops.bend as Ops

def sup(
  fuel: Nat,
  gp: Array<U32> & U32,
  +sel: U32,
  +i: U32,
  +w: U32,
  +gated: Bool
) -> Array<U32>:
  match fuel:
    case 0n:
      match gp:
        case (world, _):
          world
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
              sup(p, (world, v), Bool.pick(U32, want, 1, 9), i, v, gated)
            case 1:
              +v = gv
              adj = Ops.adjacent_static(i)
              sup(p, (world, v), Bool.pick(U32, adj, 4, 5), i, w, gated)
            case 5:
              q = Array.get(U32, world, Grid.below(i))
              sup(p, q, 2, i, w, gated)
            case 2:
              +b = gv
              bcoh = U32.is_ne(Cell.cohesion(b), 0)
              bsup = U32.is_ne(Cell.support(b), 0)
              sup(p, (world, b), Bool.pick(U32, Bool.and(bcoh, bsup), 3, 6), i, w, gated)
            case 3:
              sv = Cell.support(gv)
              world = world[i] <- Ops.set_support(w, sv)
              q = Array.get(U32, world, i)
              sup(p, q, 9, i, 0, gated)
            case 4:
              world = world[i] <- Ops.set_support(w, 31)
              q = Array.get(U32, world, i)
              sup(p, q, 9, i, 0, gated)
            case 6:
              world = world[i] <- Ops.crush_word(w)
              world = Ops.wake(world, i)
              q = Array.get(U32, world, i)
              sup(p, q, 9, i, 0, gated)
            case 9:
              +ni = U32.add(i, 1)
              sup(p, (world, gv), Bool.pick(U32, U32.is_eq(ni, 262144), 10, 11), i, 0, gated)
            case 10:
              world
            case 11:
              +ni = U32.add(i, 1)
              q = Array.get(U32, world, ni)
              sup(p, q, 0, ni, 0, gated)
            case _:
              world

def pass_gated(world: Array<U32>, +gated: Bool) -> Array<U32>:
  q = Array.get(U32, world, 0)
  sup(U32.to_nat(16777216), q, 0, 0, 0, gated)

def pass(world: Array<U32>) -> Array<U32>:
  pass_gated(world, True{})

def pass_all(world: Array<U32>) -> Array<U32>:
  pass_gated(world, False{})
