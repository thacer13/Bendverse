import Base
import ./grid.bend as Grid
import ./mod.bend as Mod
import ./bits.bend as Bits
import ./parity.bend as Parity

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

def u32_iy_neighbor_full(+i: U32, +dx: U32, +dy: U32, +dz: U32) -> {Grid.iy(Grid.neighbor(i, dx, dy, dz)) == U32.and(U32.add(Grid.iy(i), dy), 63) : U32}:
  +x = U32.and(U32.add(Grid.ix(i), dx), 63)
  +y = U32.and(U32.add(Grid.iy(i), dy), 63)
  +z = U32.and(U32.add(Grid.iz(i), dz), 63)
  +e1 = Parity.u32_index_iy(x, y, z)
  +e2 = Parity.and63_absorb(U32.add(Grid.iy(i), dy))
  Equal.trans(U32,
    Grid.iy(Grid.index(x, y, z)),
    U32.and(y, 63),
    U32.and(U32.add(Grid.iy(i), dy), 63),
    e1, e2)

def u32_iz_neighbor_full(+i: U32, +dx: U32, +dy: U32, +dz: U32) -> {Grid.iz(Grid.neighbor(i, dx, dy, dz)) == U32.and(U32.add(Grid.iz(i), dz), 63) : U32}:
  +x = U32.and(U32.add(Grid.ix(i), dx), 63)
  +y = U32.and(U32.add(Grid.iy(i), dy), 63)
  +z = U32.and(U32.add(Grid.iz(i), dz), 63)
  +e1 = Parity.u32_index_iz(x, y, z)
  +e2 = Parity.and63_absorb(U32.add(Grid.iz(i), dz))
  Equal.trans(U32,
    Grid.iz(Grid.index(x, y, z)),
    U32.and(z, 63),
    U32.and(U32.add(Grid.iz(i), dz), 63),
    e1, e2)

def index_rebuild(+i: U32) -> {Grid.index(Grid.ix(i), Grid.iy(i), Grid.iz(i)) == U32.and(i, 262143) : U32}:
  match i:
    case U32{iw}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Bits.model_index(32n, iw),
        Word.and(32n, iw, Bits.mask(32n, 18n)),
        Bits.model_index_rt(iw))

def ix_cancel(+i: U32, +a: Dir) -> {U32.and(U32.add(U32.and(U32.add(Grid.ix(i), dir_val(a)), 63), dir_val(dir_neg(a))), 63) == Grid.ix(i) : U32}:
  Equal.trans(U32,
    U32.and(U32.add(U32.and(U32.add(Grid.ix(i), dir_val(a)), 63), dir_val(dir_neg(a))), 63),
    U32.and(Grid.ix(i), 63),
    Grid.ix(i),
    phi_cancel(a, Grid.ix(i)),
    Parity.and63_absorb(i))

def iy_cancel(+i: U32, +a: Dir) -> {U32.and(U32.add(U32.and(U32.add(Grid.iy(i), dir_val(a)), 63), dir_val(dir_neg(a))), 63) == Grid.iy(i) : U32}:
  Equal.trans(U32,
    U32.and(U32.add(U32.and(U32.add(Grid.iy(i), dir_val(a)), 63), dir_val(dir_neg(a))), 63),
    U32.and(Grid.iy(i), 63),
    Grid.iy(i),
    phi_cancel(a, Grid.iy(i)),
    Parity.and63_absorb(U32.shrn(i, 12n)))

def iz_cancel(+i: U32, +a: Dir) -> {U32.and(U32.add(U32.and(U32.add(Grid.iz(i), dir_val(a)), 63), dir_val(dir_neg(a))), 63) == Grid.iz(i) : U32}:
  Equal.trans(U32,
    U32.and(U32.add(U32.and(U32.add(Grid.iz(i), dir_val(a)), 63), dir_val(dir_neg(a))), 63),
    U32.and(Grid.iz(i), 63),
    Grid.iz(i),
    phi_cancel(a, Grid.iz(i)),
    Parity.and63_absorb(U32.shrn(i, 6n)))

def neighbor_cancel(+i: U32, +a: Dir, +b: Dir, +c: Dir) -> {Grid.neighbor(Grid.neighbor(i, dir_val(a), dir_val(b), dir_val(c)), dir_val(dir_neg(a)), dir_val(dir_neg(b)), dir_val(dir_neg(c))) == U32.and(i, 262143) : U32}:
  +inner = Grid.neighbor(i, dir_val(a), dir_val(b), dir_val(c))
  +Xi = U32.and(U32.add(Grid.ix(inner), dir_val(dir_neg(a))), 63)
  +Yi = U32.and(U32.add(Grid.iy(inner), dir_val(dir_neg(b))), 63)
  +Zi = U32.and(U32.add(Grid.iz(inner), dir_val(dir_neg(c))), 63)
  +eix = Parity.u32_ix_neighbor(i, dir_val(a), dir_val(b), dir_val(c))
  +xi0 = Equal.cong(U32, U32, t => U32.and(U32.add(t, dir_val(dir_neg(a))), 63), Grid.ix(inner), U32.and(U32.add(Grid.ix(i), dir_val(a)), 63), eix)
  +xi1 = ix_cancel(i, a)
  +xi_eq = Equal.trans(U32, Xi, U32.and(U32.add(U32.and(U32.add(Grid.ix(i), dir_val(a)), 63), dir_val(dir_neg(a))), 63), Grid.ix(i), xi0, xi1)
  +eiy = u32_iy_neighbor_full(i, dir_val(a), dir_val(b), dir_val(c))
  +yi0 = Equal.cong(U32, U32, t => U32.and(U32.add(t, dir_val(dir_neg(b))), 63), Grid.iy(inner), U32.and(U32.add(Grid.iy(i), dir_val(b)), 63), eiy)
  +yi1 = iy_cancel(i, b)
  +yi_eq = Equal.trans(U32, Yi, U32.and(U32.add(U32.and(U32.add(Grid.iy(i), dir_val(b)), 63), dir_val(dir_neg(b))), 63), Grid.iy(i), yi0, yi1)
  +eiz = u32_iz_neighbor_full(i, dir_val(a), dir_val(b), dir_val(c))
  +zi0 = Equal.cong(U32, U32, t => U32.and(U32.add(t, dir_val(dir_neg(c))), 63), Grid.iz(inner), U32.and(U32.add(Grid.iz(i), dir_val(c)), 63), eiz)
  +zi1 = iz_cancel(i, c)
  +zi_eq = Equal.trans(U32, Zi, U32.and(U32.add(U32.and(U32.add(Grid.iz(i), dir_val(c)), 63), dir_val(dir_neg(c))), 63), Grid.iz(i), zi0, zi1)
  +c1 = Equal.cong(U32, U32, t => Grid.index(t, Yi, Zi), Xi, Grid.ix(i), xi_eq)
  +c2 = Equal.cong(U32, U32, t => Grid.index(Grid.ix(i), t, Zi), Yi, Grid.iy(i), yi_eq)
  +c3 = Equal.cong(U32, U32, t => Grid.index(Grid.ix(i), Grid.iy(i), t), Zi, Grid.iz(i), zi_eq)
  +reb = index_rebuild(i)
  Equal.trans(U32,
    Grid.index(Xi, Yi, Zi),
    Grid.index(Grid.ix(i), Yi, Zi),
    U32.and(i, 262143),
    c1,
    Equal.trans(U32,
      Grid.index(Grid.ix(i), Yi, Zi),
      Grid.index(Grid.ix(i), Grid.iy(i), Zi),
      U32.and(i, 262143),
      c2,
      Equal.trans(U32,
        Grid.index(Grid.ix(i), Grid.iy(i), Zi),
        Grid.index(Grid.ix(i), Grid.iy(i), Grid.iz(i)),
        U32.and(i, 262143),
        c3, reb)))
