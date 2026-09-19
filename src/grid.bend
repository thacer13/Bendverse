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

# ---------------------------------------------------------- color sub-lattice
# `Rules.color_of(i) = (ix&1) | ((iy&1)<<1) | ((iz&1)<<2)` partitions the flat
# index space into 8 phase colors. The cells of color `c`, in increasing flat
# index order, are exactly `color_at(0 .. 32767, c)` (M9: a phase scan need only
# visit its own color instead of all 262144 cells and skipping 7/8 of them).
#
# With `cx = c&1`, `cy = (c>>1)&1`, `cz = (c>>2)&1` and the packed-index strides
# (x: 1, z: 64, y: 4096), the color-`c` sub-lattice is `base(c) + 2*(s&31) +
# 128*((s>>5)&31) + 8192*(s>>10)`, where `base(c) = cx | (cz<<6) | (cy<<12)`.
def color_base(+c: U32) -> U32:
  cx = U32.and(c, 1)
  cy = U32.and(U32.shrn(c, 1n), 1)
  cz = U32.and(U32.shrn(c, 2n), 1)
  U32.or(U32.or(cx, U32.shln(cz, 6n)), U32.shln(cy, 12n))

def color_at(+s: U32, +c: U32) -> U32:
  U32.add(
    color_base(c),
    U32.add(
      U32.add(U32.shln(U32.and(s, 31), 1n), U32.shln(U32.and(U32.shrn(s, 5n), 31), 7n)),
      U32.shln(U32.shrn(s, 10n), 13n)
    )
  )

def color_last(+c: U32) -> U32:
  color_at(32767, c)

# color_s is the inverse of color_at on a color-c index.
def color_s(+i: U32, +c: U32) -> U32:
  cx = U32.and(c, 1)
  cy = U32.and(U32.shrn(c, 1n), 1)
  cz = U32.and(U32.shrn(c, 2n), 1)
  a = U32.shrn(U32.sub(ix(i), cx), 1n)
  b = U32.shrn(U32.sub(iz(i), cz), 1n)
  d = U32.shrn(U32.sub(iy(i), cy), 1n)
  U32.add(U32.add(a, U32.shln(b, 5n)), U32.shln(d, 10n))

def next_color(+i: U32, +c: U32) -> U32:
  color_at(U32.add(color_s(i, c), 1), c)
