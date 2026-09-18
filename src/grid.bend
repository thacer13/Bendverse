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
