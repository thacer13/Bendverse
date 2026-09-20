import Base
import ./worldgen.bend as Worldgen

def size() -> U32:
  16

def bits() -> Nat:
  4n

def cells() -> U32:
  4096

def local(x: U32, y: U32, z: U32) -> U32:
  (U32.and(x, 15) .|. (U32.and(z, 15) << 4n) .|. (U32.and(y, 15) << 8n) : U32)

def local_x(i: U32) -> U32:
  (i .&. 15 : U32)

def local_z(i: U32) -> U32:
  ((i >> 4n) .&. 15 : U32)

def local_y(i: U32) -> U32:
  ((i >> 8n) .&. 15 : U32)

def key(x: U32, y: U32, z: U32) -> U32:
  (U32.and(x, 1023) .|. (U32.and(z, 1023) << 10n) .|. (U32.and(y, 1023) << 20n) : U32)

def key_x(k: U32) -> U32:
  (k .&. 1023 : U32)

def key_z(k: U32) -> U32:
  ((k >> 10n) .&. 1023 : U32)

def key_y(k: U32) -> U32:
  ((k >> 20n) .&. 1023 : U32)

def global_x(k: U32, i: U32) -> U32:
  U32.add(U32.shln(key_x(k), 4n), local_x(i))

def global_y(k: U32, i: U32) -> U32:
  U32.add(U32.shln(key_y(k), 4n), local_y(i))

def global_z(k: U32, i: U32) -> U32:
  U32.add(U32.shln(key_z(k), 4n), local_z(i))

def gen_local(+k: U32, +i: U32) -> U32:
  Worldgen.gen(global_x(k, i), global_y(k, i), global_z(k, i), 42)

def gen_local_sel(sel: Bool, +k: U32, +i: U32) -> U32:
  Worldgen.at(sel, global_x(k, i), global_y(k, i), global_z(k, i), 42)

def build_at_sel(+sel: Bool, depth: Nat, +base: U32, +k: U32) -> Array<U32>:
  match depth:
    case 0n:
      ALeaf{gen_local_sel(sel, k, base)}
    case 1n+ +p:
      +h = U32.shln(1, p)
      xs ys = build_at_sel(sel, p, base, k) build_at_sel(sel, p, U32.add(base, h), k)
      ANode{xs, ys}

def build_at(depth: Nat, +base: U32, +k: U32) -> Array<U32>:
  build_at_sel(Worldgen.box(), depth, base, k)

def build(k: U32) -> Array<U32>:
  build_at(12n, 0, k)

def build_sel(+sel: Bool, +k: U32) -> Array<U32>:
  build_at_sel(sel, 12n, 0, k)
