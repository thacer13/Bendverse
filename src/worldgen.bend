import Base
import ./grid.bend as Grid
import ./cell.bend as Cell

def seed() -> U32:
  42

def hash(x: U32, y: U32, z: U32, s: U32) -> U32:
  a = U32.mul(x, 2654435761)
  b = U32.mul(y, 40503)
  c = U32.mul(z, 2246822519)
  +d = U32.xor(a, U32.xor(b, U32.xor(c, s)))
  e = U32.xor(d, U32.shrn(d, 15n))
  +f = U32.mul(e, 2246822519)
  U32.xor(f, U32.shrn(f, 16n))

def corner(ix: U32, iy: U32, iz: U32, s: U32) -> U32:
  U32.shrn(hash(ix, iy, iz, s), 24n)

def noise2(+x: U32, +z: U32, +s: U32) -> U32:
  +ix = U32.div(x, 16)
  +iz = U32.div(z, 16)
  +fx = F32.div(U32.to_f32(U32.mod(x, 16)), 16.0)
  fz = F32.div(U32.to_f32(U32.mod(z, 16)), 16.0)
  v00 = U32.to_f32(corner(ix, 0, iz, s))
  v10 = U32.to_f32(corner(U32.add(ix, 1), 0, iz, s))
  v01 = U32.to_f32(corner(ix, 0, U32.add(iz, 1), s))
  v11 = U32.to_f32(corner(U32.add(ix, 1), 0, U32.add(iz, 1), s))
  a = F32.lerp(v00, v10, fx)
  b = F32.lerp(v01, v11, fx)
  c = F32.lerp(a, b, fz)
  F32.to_u32(c)

def height(x: U32, z: U32, s: U32) -> U32:
  n = U32.to_f32(noise2(x, z, s))
  norm = F32.div(n, 255.0)
  U32.add(8, F32.to_u32(F32.floor(F32.mul(norm, 24.0))))

def classify2(above: Bool, near: Bool) -> U32:
  match above:
    case True{}:
      0
    case False{}:
      match near:
        case True{}:
          2
        case False{}:
          3

def classify(+y: U32, +gy: U32) -> U32:
  above = U32.is_gt(y, gy)
  near = U32.is_ge(y, U32.sub(gy, 3))
  classify2(above, near)

def gen_terrain(x: U32, y: U32, z: U32, s: U32) -> U32:
  gy = height(x, z, s)
  +mat = classify(y, gy)
  Cell.encode(mat, Cell.default_cohesion(mat), 0, 0, 0)

def gen_if(border: Bool, x: U32, y: U32, z: U32, s: U32) -> U32:
  match border:
    case True{}:
      Cell.encode(Cell.bedrock(), 63, 0, 0, 0)
    case False{}:
      gen_terrain(x, y, z, s)

def gen(+x: U32, +y: U32, +z: U32, s: U32) -> U32:
  b0 = U32.is_eq(x, 0)
  b1 = U32.is_eq(x, 63)
  b2 = U32.is_eq(y, 0)
  b3 = U32.is_eq(y, 63)
  b4 = U32.is_eq(z, 0)
  b5 = U32.is_eq(z, 63)
  border = Bool.or(Bool.or(b0, b1), Bool.or(Bool.or(b2, b3), Bool.or(b4, b5)))
  gen_if(border, x, y, z, s)

def build_at(depth: Nat, +base: U32) -> Array<U32>:
  match depth:
    case 0n:
      ALeaf{gen(Grid.ix(base), Grid.iy(base), Grid.iz(base), 42)}
    case 1n+ +p:
      +h = U32.shln(1, p)
      xs ys = build_at(p, base) build_at(p, U32.add(base, h))
      ANode{xs, ys}

def build() -> Array<U32>:
  build_at(18n, 0)
