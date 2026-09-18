import Base
import ./grid.bend as Grid
import ./mod.bend as Mod
import ./bits.bend as Bits

type Dir is Data:
  Dno{}
  Dup{}
  Ddn{}

def dir_val(d: Dir) -> U32:
  match d:
    case Dno{}: 0
    case Dup{}: 1
    case Ddn{}: 4294967295

def dir_neg(d: Dir) -> Dir:
  match d:
    case Dno{}: Dno{}
    case Dup{}: Ddn{}
    case Ddn{}: Dup{}

def phi(d: Dir, x: U32) -> U32:
  U32.and(U32.add(x, dir_val(d)), 63)

def u32_add_zero_twice(+x: U32) -> {U32.add(U32.add(x, 0), 0) == x : U32}:
  Equal.trans(U32,
    U32.add(U32.add(x, 0), 0),
    U32.add(x, 0),
    x,
    Mod.u32_add_zero_r(U32.add(x, 0)),
    Mod.u32_add_zero_r(x))

def phi_cancel(+d: Dir, +x: U32) -> {phi(dir_neg(d), phi(d, x)) == U32.and(x, 63) : U32}:
  match d:
    case Dno{}:
      Equal.trans(U32,
        phi(Dno{}, phi(Dno{}, x)),
        U32.and(U32.add(U32.add(x, 0), 0), 63),
        U32.and(x, 63),
        Mod.low_mask_absorb(U32.add(x, 0), 0),
        Equal.cong(U32, U32, t => U32.and(t, 63), U32.add(U32.add(x, 0), 0), x, u32_add_zero_twice(x)))
    case Dup{}:
      Equal.trans(U32,
        phi(Ddn{}, phi(Dup{}, x)),
        U32.and(U32.add(U32.add(x, 1), 4294967295), 63),
        U32.and(x, 63),
        Mod.low_mask_absorb(U32.add(x, 1), 4294967295),
        Equal.cong(U32, U32, t => U32.and(t, 63), U32.add(U32.add(x, 1), 4294967295), x, Mod.u32_add_one_ones(x)))
    case Ddn{}:
      Equal.trans(U32,
        phi(Dup{}, phi(Ddn{}, x)),
        U32.and(U32.add(U32.add(x, 4294967295), 1), 63),
        U32.and(x, 63),
        Mod.low_mask_absorb(U32.add(x, 4294967295), 1),
        Equal.cong(U32, U32, t => U32.and(t, 63), U32.add(U32.add(x, 4294967295), 1), x, Mod.u32_add_ones_one(x)))
