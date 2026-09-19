import Base

def size() -> U32:
  64

def volume() -> U32:
  262144

def index(x: U32, y: U32, z: U32) -> U32:
  (U32.and(x, 63) .|. (U32.and(z, 63) << 6n) .|. (U32.and(y, 63) << 12n) : U32)

def ix(i: U32) -> U32:
  (i .&. 63 : U32)

def iz(i: U32) -> U32:
  ((i >> 6n) .&. 63 : U32)

def iy(i: U32) -> U32:
  ((i >> 12n) .&. 63 : U32)

def to_list_go(a: Array<U32>, acc: List<U32>) -> List<U32>:
  match a:
    case ALeaf{x}:
      x <> acc
    case ANode{xs, ys}:
      to_list_go(xs, to_list_go(ys, acc))

def to_list(a: Array<U32>) -> List<U32>:
  to_list_go(a, Nil{})

def pack(p: Array<U32> & U32) -> U32:
  match p:
    case (a, v):
      v

def value_at(world: Array<U32>, i: U32) -> U32:
  p = Array.get(U32, world, i)
  pack(p)

def neighbor(+i: U32, dx: U32, dy: U32, dz: U32) -> U32:
  x = U32.and(U32.add(ix(i), dx), 63)
  z = U32.and(U32.add(iz(i), dz), 63)
  y = U32.and(U32.add(iy(i), dy), 63)
  index(x, y, z)

# C2 (V0-2): closure at the grid level. `neighbor` wraps mod `size` on every axis,
# so a step off the box would land on the opposite face. `step_inside` is the
# guard: it adds the *raw* offset to the coordinate and tests the bits above the
# axis mask, which are non-zero exactly when the coordinate wrapped. The shell is
# then generation, not what keeps the world closed.
def step_inside(+i: U32, +dx: U32, +dy: U32, +dz: U32) -> Bool:
  +high = U32.not(U32.sub(size(), 1))
  okx = U32.is_eq(U32.and(U32.add(ix(i), dx), high), 0)
  oky = U32.is_eq(U32.and(U32.add(iy(i), dy), high), 0)
  okz = U32.is_eq(U32.and(U32.add(iz(i), dz), high), 0)
  Bool.and(okx, Bool.and(oky, okz))

def below(i: U32) -> U32:
  neighbor(i, 0, 4294967295, 0)

def above(i: U32) -> U32:
  neighbor(i, 0, 1, 0)

def west(i: U32) -> U32:
  neighbor(i, 4294967295, 0, 0)

def east(i: U32) -> U32:
  neighbor(i, 1, 0, 0)

def south(i: U32) -> U32:
  neighbor(i, 0, 0, 4294967295)

def north(i: U32) -> U32:
  neighbor(i, 0, 0, 1)

# The M9 colour sub-lattice (`color_base`/`color_at`/`color_last`/`color_s`/
# `next_color`) was retired by V0-4b-1 (A.72): the phase fold no longer scans a
# colour's 32768-cell sub-lattice, it runs over the active-cell work list
# (`Sim.active_list` + `Rules.plan`'s `todo`). `Rules.color_of` is still the live
# colour function (`Sim.filter_color` uses it).
