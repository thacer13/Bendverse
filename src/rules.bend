import Base
import ./grid.bend as Grid
import ./cell.bend as Cell

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

def mark_got(p: Array<U32> & U32, i: U32) -> Array<U32>:
  match p:
    case (world, w):
      nw = U32.or(w, 2048)
      world = world[i] <- nw
      world

def mark(world: Array<U32>, +i: U32) -> Array<U32>:
  p = Array.get(U32, world, i)
  mark_got(p, i)

def wake_x(
  fuel: Nat, +dx: U32, +dy: U32, +dz: U32, +i: U32, world: Array<U32>
) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      j = Grid.neighbor(i, U32.sub(dx, 1), U32.sub(dy, 1), U32.sub(dz, 1))
      world2 = mark(world, j)
      wake_x(p, U32.add(dx, 1), dy, dz, i, world2)

def wake_y(
  fuel: Nat, +dy: U32, +dz: U32, +i: U32, world: Array<U32>
) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      world2 = wake_x(U32.to_nat(3), 0, dy, dz, i, world)
      wake_y(p, U32.add(dy, 1), dz, i, world2)

def wake_z(fuel: Nat, +dz: U32, +i: U32, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      world2 = wake_y(U32.to_nat(3), 0, dz, i, world)
      wake_z(p, U32.add(dz, 1), i, world2)

def wake(world: Array<U32>, i: U32) -> Array<U32>:
  wake_z(U32.to_nat(3), 0, i, world)

def mov(+w: U32) -> U32:
  nf = U32.min(U32.add(Cell.fall(w), 1), 63)
  Cell.encode(Cell.material(w), Cell.cohesion(w), Cell.active(w), Cell.support(w), nf)

def clear_fall_if(z: Bool, world: Array<U32>, +w: U32, +i: U32) -> Array<U32>:
  match z:
    case True{}:
      nw = Cell.encode(Cell.material(w), Cell.cohesion(w), Cell.active(w), Cell.support(w), 0)
      world = world[i] <- nw
      wake(world, i)
    case False{}:
      world

def clear_fall(world: Array<U32>, +w: U32, i: U32) -> Array<U32>:
  clear_fall_if(U32.is_ne(Cell.fall(w), 0), world, w, i)

def step(
  fuel: Nat,
  gp: Array<U32> & U32,
  +sel: U32,
  +i: U32,
  +c: U32,
  +w: U32,
  +k: U32
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
              step(p, (world, v), Bool.pick(U32, act, 20, 19), i, c, 0, 0)
            case 20:
              +v = gv
              bad = U32.is_ne(color_of(i), c)
              step(p, (world, v), Bool.pick(U32, bad, 19, 18), i, c, 0, 0)
            case 19:
              step(p, (world, gv), 14, i, c, 0, 0)
            case 18:
              +v = gv
              nw = U32.and(v, 4294965247)
              world = world[i] <- nw
              +m = Cell.material(v)
              skip = Bool.or(Bool.or(U32.is_eq(m, 0), Cell.static(m)), U32.is_ne(Cell.cohesion(v), 0))
              step(p, (world, v), Bool.pick(U32, skip, 4, 5), i, c, v, 0)
            case 4:
              step(p, (world, gv), 14, i, c, 0, 0)
            case 5:
              q = Array.get(U32, world, Grid.below(i))
              step(p, q, 1, i, c, w, 0)
            case 1:
              +v = gv
              +mb = Cell.material(v)
              can = Bool.or(U32.is_eq(mb, 0), U32.is_lt(Cell.density(mb), Cell.density(Cell.material(w))))
              step(p, (world, v), Bool.pick(U32, can, 6, 7), i, c, w, 0)
            case 6:
              world = world[Grid.below(i)] <- mov(w)
              world = world[i] <- gv
              world = wake(world, i)
              world = wake(world, Grid.below(i))
              q = Array.get(U32, world, i)
              step(p, q, 14, i, c, 0, 0)
            case 7:
              +sl = Cell.slides(Cell.material(w))
              step(p, (world, gv), Bool.pick(U32, sl, 9, 8), i, c, w, 0)
            case 8:
              w2 = clear_fall(world, w, i)
              q = Array.get(U32, w2, i)
              step(p, q, 14, i, c, 0, 0)
            case 9:
              q = Array.get(U32, world, side_index(i, k))
              step(p, q, 2, i, c, w, k)
            case 2:
              +v = gv
              +ms = Cell.material(v)
              sok = Bool.or(U32.is_eq(ms, 0), U32.is_lt(Cell.density(ms), Cell.density(Cell.material(w))))
              step(p, (world, v), Bool.pick(U32, sok, 10, 11), i, c, w, k)
            case 10:
              q = Array.get(U32, world, diag_index(i, k))
              step(p, q, 3, i, c, w, k)
            case 3:
              +v = gv
              +md = Cell.material(v)
              dok = Bool.or(U32.is_eq(md, 0), U32.is_lt(Cell.density(md), Cell.density(Cell.material(w))))
              step(p, (world, v), Bool.pick(U32, dok, 12, 13), i, c, w, k)
            case 11:
              +nk = U32.add(k, 1)
              step(p, (world, gv), Bool.pick(U32, U32.is_eq(nk, 4), 8, 9), i, c, w, nk)
            case 12:
              world = world[diag_index(i, k)] <- w
              world = world[i] <- gv
              world = wake(world, i)
              world = wake(world, diag_index(i, k))
              q = Array.get(U32, world, i)
              step(p, q, 14, i, c, 0, 0)
            case 13:
              +nk = U32.add(k, 1)
              step(p, (world, gv), Bool.pick(U32, U32.is_eq(nk, 4), 8, 9), i, c, w, nk)
            case 14:
              step(p, (world, gv), Bool.pick(U32, U32.is_eq(U32.add(i, 1), 262144), 15, 16), i, c, 0, 0)
            case 15:
              world
            case 16:
              +ni = U32.add(i, 1)
              q = Array.get(U32, world, ni)
              step(p, q, 0, ni, c, 0, 0)
            case _:
              world
