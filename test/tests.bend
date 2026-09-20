import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/worldgen.bend as Worldgen
import ../src/parity.bend as Parity
import ../src/priority.bend as Priority
import ../src/settle.bend as Settle
import ../src/potential.bend as Pot
import ../src/chunk.bend as Chunk
import ../src/store.bend as Store
import ../src/ops.bend as Ops
import ../src/rules.bend as Rules
import ../src/count.bend as Count
import ../src/refine.bend as Refine
import ../src/commit.bend as Commit
import ../src/v3cw.bend as V3cw
import ../src/tick.bend as Tick
import ../src/g5.bend as G5
import ../src/sim.bend as Sim
import ../scenarios/fixtures.bend as Fixtures
import ../view/voxel.bend as Vox
import ../runners/view3d.bend as View3d

def is_bad(z: Bool) -> U32:
  match z:
    case True{}:
      0
    case False{}:
      1

def inc_if_false(z: Bool, bad: U32) -> U32:
  match z:
    case True{}:
      bad
    case False{}:
      U32.add(bad, 1)

def report(+name: String, +bad: U32) -> IO(Unit):
  do IO<Unit>:
    z : Bool = U32.is_eq(bad, 0)
    IO.print(Bool.pick(String, z, "PASS " ++ name, "FAIL " ++ name ++ " (" ++ U32.show(bad) ++ ")"))

def index_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      j = Grid.index(Grid.ix(i), Grid.iy(i), Grid.iz(i))
      ok = U32.is_eq(j, i)
      bad2 = inc_if_false(ok, bad)
      index_go(p, U32.add(i, 1), bad2)

def index_bad() -> U32:
  index_go(U32.to_nat(262144), 0, 0)

def cell_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +mat = U32.mod(i, 6)
      +coh = U32.mod(i, 64)
      +act = U32.mod(i, 2)
      +sup = U32.mod(i, 32)
      +fl = U32.mod(i, 64)
      +w = Cell.encode(mat, coh, act, sup, fl)
      okm = U32.is_eq(Cell.material(w), mat)
      okc = U32.is_eq(Cell.cohesion(w), coh)
      oka = U32.is_eq(Cell.active(w), act)
      oks = U32.is_eq(Cell.support(w), sup)
      okf = U32.is_eq(Cell.fall(w), fl)
      okr = U32.is_eq(Cell.reencode(w), w)
      all = Bool.and(Bool.and(Bool.and(Bool.and(okm, okc), Bool.and(oka, oks)), okf), okr)
      bad2 = inc_if_false(all, bad)
      cell_go(p, U32.add(i, 1), bad2)

def cell_bad() -> U32:
  cell_go(U32.to_nat(4096), 0, 0)

def gen_det_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +x = Grid.ix(i)
      +y = Grid.iy(i)
      +z = Grid.iz(i)
      a = Worldgen.gen(x, y, z, 42)
      b = Worldgen.gen(x, y, z, 42)
      bad2 = inc_if_false(U32.is_eq(a, b), bad)
      gen_det_go(p, U32.add(i, 1), bad2)

def gen_det_bad() -> U32:
  gen_det_go(U32.to_nat(4096), 0, 0)

def terrain_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +x = U32.add(U32.mod(Grid.ix(i), 62), 1)
      +z = U32.add(U32.mod(Grid.iz(i), 62), 1)
      +gy = Worldgen.height(x, z, 42)
      m1 = Cell.material(Worldgen.gen(x, gy, z, 42))
      m2 = Cell.material(Worldgen.gen(x, U32.add(gy, 1), z, 42))
      m3 = Cell.material(Worldgen.gen(x, 3, z, 42))
      mb = Cell.material(Worldgen.gen(0, gy, z, 42))
      o1 = U32.is_eq(m1, 2)
      o2 = U32.is_eq(m2, 0)
      o3 = U32.is_eq(m3, 3)
      o4 = U32.is_eq(mb, 1)
      all = Bool.and(Bool.and(o1, o2), Bool.and(o3, o4))
      bad2 = inc_if_false(all, bad)
      terrain_go(p, U32.add(i, 1), bad2)

def terrain_bad() -> U32:
  terrain_go(U32.to_nat(4096), 0, 0)

def build_go(fuel: Nat, +i: U32, cells: List<U32>, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      match cells:
        case Nil{}:
          bad
        case Con{h, t}:
          g = Worldgen.gen(Grid.ix(i), Grid.iy(i), Grid.iz(i), 42)
          build_go(p, U32.add(i, 1), t, inc_if_false(U32.is_eq(h, g), bad))

def build_bad() -> U32:
  build_go(U32.to_nat(262144), 0, Grid.to_list(Worldgen.build()), 0)

def bool_eq(a: Bool, b: Bool) -> Bool:
  Bool.not(Bool.xor(a, b))

def parity_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      o1 = bool_eq(Parity.par32(U32.add(i, 1)), Bool.not(Parity.par32(i)))
      o2 = bool_eq(Parity.par32(U32.add(i, 4294967295)), Bool.not(Parity.par32(i)))
      o3 = bool_eq(Parity.par32(Grid.ix(Grid.neighbor(i, i, 0, 0))), Bool.xor(Parity.par32(Grid.ix(i)), Parity.par32(i)))
      o4 = bool_eq(Parity.par32(Grid.iy(Grid.neighbor(i, 0, i, 0))), Bool.xor(Parity.par32(Grid.iy(i)), Parity.par32(i)))
      o5 = bool_eq(Parity.par32(Grid.iz(Grid.neighbor(i, 0, 0, i))), Bool.xor(Parity.par32(Grid.iz(i)), Parity.par32(i)))
      all = Bool.and(Bool.and(Bool.and(Bool.and(o1, o2), o3), o4), o5)
      parity_go(p, U32.add(i, 1), inc_if_false(all, bad))

def parity_bad() -> U32:
  parity_go(U32.to_nat(4096), 0, 0)

def mod_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +a = i
      +b = U32.mul(i, 2654435761)
      o1 = U32.is_eq(U32.and(U32.add(a, b), 63), U32.and(U32.add(U32.and(a, 63), U32.and(b, 63)), 63))
      o2 = U32.is_eq(U32.add(U32.add(a, 1), 4294967295), a)
      o3 = U32.is_eq(U32.add(U32.add(a, 4294967295), 1), a)
      all = Bool.and(o1, Bool.and(o2, o3))
      mod_go(p, U32.add(i, 1), inc_if_false(all, bad))

def mod_bad() -> U32:
  mod_go(U32.to_nat(4096), 0, 0)

def phi_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +x = U32.mul(i, 2654435761)
      o0 = U32.is_eq(Priority.phi(Priority.dir_neg(Priority.Dno{}), Priority.phi(Priority.Dno{}, x)), U32.and(x, 63))
      o1 = U32.is_eq(Priority.phi(Priority.dir_neg(Priority.Dup{}), Priority.phi(Priority.Dup{}, x)), U32.and(x, 63))
      o2 = U32.is_eq(Priority.phi(Priority.dir_neg(Priority.Ddn{}), Priority.phi(Priority.Ddn{}, x)), U32.and(x, 63))
      all = Bool.and(o0, Bool.and(o1, o2))
      phi_go(p, U32.add(i, 1), inc_if_false(all, bad))

def phi_bad() -> U32:
  phi_go(U32.to_nat(4096), 0, 0)

def nc_check(+i: U32, +a: Priority.Dir, +b: Priority.Dir, +c: Priority.Dir) -> Bool:
  U32.is_eq(
    Grid.neighbor(Grid.neighbor(i, Priority.dir_val(a), Priority.dir_val(b), Priority.dir_val(c)),
      Priority.dir_val(Priority.dir_neg(a)), Priority.dir_val(Priority.dir_neg(b)), Priority.dir_val(Priority.dir_neg(c))),
    U32.and(i, 262143))

def nc_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      o0 = nc_check(i, Priority.Dno{}, Priority.Dup{}, Priority.Ddn{})
      o1 = nc_check(i, Priority.Dup{}, Priority.Ddn{}, Priority.Dno{})
      o2 = nc_check(i, Priority.Ddn{}, Priority.Dno{}, Priority.Dup{})
      o3 = nc_check(i, Priority.Dup{}, Priority.Dup{}, Priority.Dup{})
      o4 = nc_check(i, Priority.Ddn{}, Priority.Ddn{}, Priority.Ddn{})
      o5 = nc_check(i, Priority.Dno{}, Priority.Dno{}, Priority.Dno{})
      all = Bool.and(Bool.and(Bool.and(o0, o1), Bool.and(o2, o3)), Bool.and(o4, o5))
      nc_go(p, U32.add(i, 1), inc_if_false(all, bad))

def nc_bad() -> U32:
  nc_go(U32.to_nat(4096), 0, 0)

def total_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +b = U32.mul(i, 2654435761)
      all = Bool.or(Bool.or(U32.is_lt(i, b), U32.is_gt(i, b)), U32.is_eq(i, b))
      total_go(p, U32.add(i, 1), inc_if_false(all, bad))

def total_bad() -> U32:
  total_go(U32.to_nat(4096), 0, 0)

def nlist_eq(+xs: +List<Nat>, +ys: +List<Nat>) -> Bool:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          True{}
        case Con{hy, ty}:
          False{}
    case Con{hx, tx}:
      match ys:
        case Nil{}:
          False{}
        case Con{hy, ty}:
          Bool.and(Nat.is_eq(hx, hy), nlist_eq(tx, ty))

def sample_xs() -> +List<Nat>:
  [10n, 20n, 30n, 40n]

def sample_ys() -> +List<Nat>:
  [50n, 60n]

def set_split_case(+n: Nat, bad: U32) -> U32:
  +xs = sample_xs()
  +ys = sample_ys()
  +v = {99n : Nat}
  +lhs = List.set(&2, Nat, Settle.app(xs, ys), n, v)
  +rhs = Bool.pick(List<&2, Nat>, Nat.is_lt(n, Settle.len(xs)),
    Settle.app(List.set(&2, Nat, xs, n, v), ys),
    Settle.app(xs, List.set(&2, Nat, ys, Nat.sub(n, Settle.len(xs)), v)))
  inc_if_false(nlist_eq(lhs, rhs), bad)

def set_split_go(fuel: Nat, +n: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      set_split_go(p, Nat.add(1n, n), set_split_case(n, bad))

def sample_xs2() -> +List<Nat>:
  [1n, 2n, 3n]

def sample_ys2() -> +List<Nat>:
  [5n, 6n]

def set_sum_case(bad: U32) -> U32:
  +xs = sample_xs2()
  +ys = sample_ys2()
  +x = {7n : Nat}
  +v = {8n : Nat}
  +lhs = Nat.add(Settle.suml(Settle.app(xs, v <> ys)), x)
  +rhs = Nat.add(Settle.suml(Settle.app(xs, x <> ys)), v)
  inc_if_false(Nat.is_eq(lhs, rhs), bad)

def set_laws_bad() -> U32:
  set_sum_case(set_split_go(U32.to_nat(7), 0n, 0))

def ck_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +k = U32.and(U32.mul(i, 2654435761), 1073741823)
      ok = U32.is_eq(Chunk.key(Chunk.key_x(k), Chunk.key_y(k), Chunk.key_z(k)), k)
      ck_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def cl_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +j = U32.and(i, 4095)
      ok = U32.is_eq(Chunk.local(Chunk.local_x(j), Chunk.local_y(j), Chunk.local_z(j)), j)
      cl_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def chunk_gen_go(fuel: Nat, +i: U32, +k: U32, cells: List<U32>, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      match cells:
        case Nil{}:
          bad
        case Con{h, t}:
          +g = Worldgen.gen(Chunk.global_x(k, i), Chunk.global_y(k, i), Chunk.global_z(k, i), 42)
          chunk_gen_go(p, U32.add(i, 1), k, t, inc_if_false(U32.is_eq(h, g), bad))

def chunk_gen_case(+k: U32, bad: U32) -> U32:
  chunk_gen_go(U32.to_nat(4096), 0, k, Grid.to_list(Chunk.build(k)), bad)

def chunk_keys() -> List<U32>:
  [Chunk.key(0, 0, 0), Chunk.key(3, 0, 0), Chunk.key(0, 3, 0), Chunk.key(0, 0, 3), Chunk.key(1, 2, 3), Chunk.key(2, 1, 0), Chunk.key(0, 2, 1), Chunk.key(3, 3, 3)]

def cg_cases(fuel: Nat, keys: List<U32>, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      match keys:
        case Nil{}:
          bad
        case Con{k, t}:
          cg_cases(p, t, chunk_gen_case(k, bad))

def chunk_bad() -> U32:
  U32.add(ck_go(U32.to_nat(4096), 0, 0), U32.add(cl_go(U32.to_nat(4096), 0, 0), cg_cases(U32.to_nat(8), chunk_keys(), 0)))

def dlist_eq(+xs: List<&2, U32>, +ys: List<&2, U32>) -> Bool:
  match xs ys:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{hy, ty}:
      False{}
    case Con{hx, tx} Nil{}:
      False{}
    case Con{hx, tx} Con{hy, ty}:
      Bool.and(U32.is_eq(hx, hy), dlist_eq(tx, ty))

def put_keys(fuel: Nat, keys: List<U32>, store: Store.Store) -> Store.Store:
  match fuel:
    case 0n:
      store
    case 1n+p:
      match keys:
        case Nil{}:
          store
        case Con{+k, t}:
          put_keys(p, t, Store.set(store, k, Store.chunk_list(k)))

def maybe_present(m: Maybe<&2, List<&2, U32>>, +k: U32, bad: U32) -> U32:
  match m:
    case None{}:
      U32.add(bad, 1)
    case Some{val}:
      inc_if_false(dlist_eq(val, Store.chunk_list(k)), bad)

def check_present(+store: Store.Store, +k: U32, bad: U32) -> U32:
  maybe_present(Store.get(store, k), k, bad)

def get_keys(fuel: Nat, keys: List<U32>, +store: Store.Store, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      match keys:
        case Nil{}:
          bad
        case Con{k, t}:
          get_keys(p, t, store, check_present(store, k, bad))

def maybe_absent(m: Maybe<&2, List<&2, U32>>, bad: U32) -> U32:
  match m:
    case None{}:
      bad
    case Some{val}:
      U32.add(bad, 1)

def missing_bad(+store: Store.Store, bad: U32) -> U32:
  maybe_absent(Store.get(store, Chunk.key(2, 2, 2)), bad)

def maybe_overwrite(m: Maybe<&2, List<&2, U32>>, +other: U32, bad: U32) -> U32:
  match m:
    case None{}:
      U32.add(bad, 1)
    case Some{val}:
      inc_if_false(dlist_eq(val, Store.chunk_list(other)), bad)

def overwrite_bad(+store: Store.Store, bad: U32) -> U32:
  +k = Chunk.key(0, 0, 0)
  +other = Chunk.key(0, 0, 1)
  maybe_overwrite(Store.get(Store.set(store, k, Store.chunk_list(other)), k), other, bad)

def list_cmp_go(fuel: Nat, xs: List<U32>, ys: List<U32>, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      match xs:
        case Nil{}:
          bad
        case Con{hx, tx}:
          match ys:
            case Nil{}:
              bad
            case Con{hy, ty}:
              list_cmp_go(p, tx, ty, inc_if_false(U32.is_eq(hx, hy), bad))

def assemble_bad() -> U32:
  store = Store.build_all()
  a = Store.assemble(store)
  b = Worldgen.build()
  list_cmp_go(U32.to_nat(262144), Grid.to_list(a), Grid.to_list(b), 0)

def store_bad() -> U32:
  +base = put_keys(U32.to_nat(8), chunk_keys(), Store.empty())
  U32.add(get_keys(U32.to_nat(8), chunk_keys(), base, 0),
    U32.add(missing_bad(base, 0), overwrite_bad(base, 0)))

# T19 write->pot bridge: support writes preserve pot; crush_lowers for rock and
# is the identity elsewhere (G9 witness; the last fact is not provable in Bend).
def wp_check(+w: U32, +i: U32, bad: U32) -> U32:
  ok0 = U32.is_eq(Cell.material(Ops.set_support(w, 21)), Cell.material(w))
  bad0 = inc_if_false(ok0, bad)
  +z = U32.is_eq(Cell.material(w), 3)
  ok1 = U32.is_eq(Cell.material(Ops.crush_word(w)), Bool.pick(U32, z, 4, Cell.material(w)))
  bad1 = inc_if_false(ok1, bad0)
  +L = U32.to_nat(Grid.iy(i))
  rok = Nat.is_eq(Nat.add(Settle.pot_at(Ops.crush_word(w), i), Nat.mul(50n, L)), Settle.pot_at(w, i))
  non = Nat.is_eq(Settle.pot_at(Ops.crush_word(w), i), Settle.pot_at(w, i))
  bad2 = inc_if_false(Bool.pick(Bool, z, rok, non), bad1)
  bad2

def wp_bad() -> U32:
  wp_check(Cell.encode(0, 5, 1, 7, 3), Grid.index(1, 1, 1),
    wp_check(Cell.encode(1, 63, 0, 31, 63), Grid.index(2, 1, 5),
      wp_check(Cell.encode(2, 0, 1, 0, 0), Grid.index(3, 3, 7),
        wp_check(Cell.encode(3, 48, 1, 15, 9), Grid.index(5, 2, 9),
          wp_check(Cell.encode(4, 0, 0, 4, 2), Grid.index(4, 7, 3),
            wp_check(Cell.encode(5, 10, 1, 2, 17), Grid.index(9, 63, 61),
              wp_check(0, Grid.index(7, 33, 8),
                wp_check(8388607, Grid.index(8, 5, 6), 0))))))))

# T20 chunk sleeping/eviction: a gen-equal chunk is sleeping and regenerable, so
# eviction drops it and `assemble` rebuilds it from worldgen exactly.
def mod_first(+cells: List<&2, U32>) -> List<&2, U32>:
  match cells:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      +m = Cell.encode(Cell.material(h), Cell.cohesion(h), 1, Cell.support(h), Cell.fall(h))
      m <> t

def ev_empty_bad() -> U32:
  a = Store.assemble(Store.empty())
  b = Worldgen.build()
  list_cmp_go(U32.to_nat(262144), Grid.to_list(a), Grid.to_list(b), 0)

def ev_full_bad() -> U32:
  s = Store.build_all()
  a = Store.assemble(Store.evict(s))
  b = Worldgen.build()
  list_cmp_go(U32.to_nat(262144), Grid.to_list(a), Grid.to_list(b), 0)

def ev_mod_bad() -> U32:
  +k = Chunk.key(1, 2, 3)
  +s = Store.set(Store.build_all(), k, mod_first(Store.chunk_list(k)))
  a = Store.assemble(s)
  b = Store.assemble(Store.evict(s))
  list_cmp_go(U32.to_nat(262144), Grid.to_list(a), Grid.to_list(b), 0)

def ev_pred_bad() -> U32:
  +k = Chunk.key(0, 0, 0)
  sl = Store.sleeping_cells(U32.to_nat(4096), Store.chunk_list(k), False{})
  ge = Store.gen_eq_cells(U32.to_nat(4096), Store.chunk_list(k), Store.chunk_list(k), True{})
  bad0 = inc_if_false(sl, 0)
  bad1 = inc_if_false(ge, bad0)
  +k2 = Chunk.key(0, 0, 1)
  sl2 = Store.sleeping_cells(U32.to_nat(4096), mod_first(Store.chunk_list(k2)), False{})
  ge2 = Store.gen_eq_cells(U32.to_nat(4096), mod_first(Store.chunk_list(k2)), Store.chunk_list(k2), True{})
  inc_if_false(Bool.not(sl2), inc_if_false(Bool.not(ge2), bad1))

# T21 conservation witness: every material-preserving write keeps the non-empty
# indicator, and a rock crush keeps it (3 -> 4, both non-empty); non-rock crush
# is the identity (G9 witness).
def cnt_check(+w: U32, bad: U32) -> U32:
  b0 = inc_if_false(Nat.is_eq(Count.nempty(Ops.set_support(w, 21)), Count.nempty(w)), bad)
  b1 = inc_if_false(Nat.is_eq(Count.nempty(Ops.set_fall0(w)), Count.nempty(w)), b0)
  b2 = inc_if_false(Nat.is_eq(Count.nempty(Rules.mov(w)), Count.nempty(w)), b1)
  b3 = inc_if_false(Nat.is_eq(Count.nempty(U32.or(w, 2048)), Count.nempty(w)), b2)
  b4 = inc_if_false(Nat.is_eq(Count.nempty(U32.and(w, 4294965247)), Count.nempty(w)), b3)
  +z = U32.is_eq(Cell.material(w), 3)
  rok = Nat.is_eq(Count.nempty(Ops.crush_word(w)), 1n)
  non = Nat.is_eq(Count.nempty(Ops.crush_word(w)), Count.nempty(w))
  inc_if_false(Bool.pick(Bool, z, rok, non), b4)

def cnt_bad() -> U32:
  cnt_check(Cell.encode(0, 5, 1, 7, 3),
    cnt_check(Cell.encode(1, 63, 0, 31, 63),
      cnt_check(Cell.encode(2, 0, 1, 0, 0),
        cnt_check(Cell.encode(3, 48, 1, 15, 9),
          cnt_check(Cell.encode(4, 0, 0, 4, 2),
            cnt_check(Cell.encode(5, 10, 1, 2, 17),
              cnt_check(0, cnt_check(8388607, 0))))))))

# T22 movement Phi witness: the movement is a two-write swap, and
# its close is the cross equation `after + mov_S == before + mov_T` (A.53). We
# use the size-free `PT` model to place a heavy cell at level 1 (index 4096) and
# an empty cell at level 0 (index 0): the move drops Phi by 100 and the single
# cross terms match the before/after potentials. `fall_gap = mov_S - mov_T` and
# `mov_S >= mov_T` are checked by evaluation.
# T22 movement Phi witness (A.51/A.53): the movement writes `mov(w)` down to
# `below(i)` and the old target `gv` up to `i`, so its concrete Phi account is
# `after + gap == before` with `gap = (dens(w) - dens(gv)) * (iy(i) - iy(j))`.
# Two cases: empty target (gap 100) and lighter-but-nonempty target (gap 20).
def mov_case(+w: U32, +gv: U32, +i: U32, +j: U32, +expect: Nat, bad: U32) -> U32:
  +before = Nat.add(Settle.pot_at(w, i), Settle.pot_at(gv, j))
  +after = Nat.add(Settle.pot_at(Rules.mov(w), j), Settle.pot_at(gv, i))
  +gap = Nat.mul(Nat.sub(Pot.dens(Cell.material(w)), Pot.dens(Cell.material(gv))),
                 Nat.sub(U32.to_nat(Grid.iy(i)), U32.to_nat(Grid.iy(j))))
  b0 = inc_if_false(Nat.is_eq(gap, expect), bad)
  b1 = inc_if_false(Nat.is_eq(Nat.add(after, gap), before), b0)
  b2 = inc_if_false(Nat.is_eq(Settle.pot_at(Rules.mov(w), j), Settle.pot_at(w, j)), b1)
  inc_if_false(Nat.is_ge(before, after), b2)

def mov_bad() -> U32:
  +i = Grid.index(0, 1, 0)
  +j = Grid.index(0, 0, 0)
  mov_case(Cell.encode(2, 0, 1, 0, 0), Cell.encode(0, 0, 0, 0, 0), i, j, 100n,
    mov_case(Cell.encode(2, 0, 1, 0, 0), Cell.encode(5, 0, 0, 0, 0), i, j, 20n, 0))

# T29 (V0-3): the live engine's closed `Rules.Dir4` direction set agrees, for all
# four constructors, with the retired `U32` index table `diag_index`/`side_index`
# — behaviour-preservation witness for the `k < 4` landmine fix (the silent
# `case _: i` default no longer exists on the live path).
def dir4_check(+i: U32, bad: U32) -> U32:
  b0 = inc_if_false(U32.is_eq(Rules.diag4(i, Rules.K0{}), Rules.diag_index(i, 0)), bad)
  b1 = inc_if_false(U32.is_eq(Rules.diag4(i, Rules.K1{}), Rules.diag_index(i, 1)), b0)
  b2 = inc_if_false(U32.is_eq(Rules.diag4(i, Rules.K2{}), Rules.diag_index(i, 2)), b1)
  b3 = inc_if_false(U32.is_eq(Rules.diag4(i, Rules.K3{}), Rules.diag_index(i, 3)), b2)
  b4 = inc_if_false(U32.is_eq(Rules.side4(i, Rules.K0{}), Rules.side_index(i, 0)), b3)
  b5 = inc_if_false(U32.is_eq(Rules.side4(i, Rules.K1{}), Rules.side_index(i, 1)), b4)
  b6 = inc_if_false(U32.is_eq(Rules.side4(i, Rules.K2{}), Rules.side_index(i, 2)), b5)
  b7 = inc_if_false(U32.is_eq(Rules.side4(i, Rules.K3{}), Rules.side_index(i, 3)), b6)
  b7

def dir4_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      dir4_go(p, U32.add(i, 1), dir4_check(i, bad))

def dir4_bad() -> U32:
  dir4_go(U32.to_nat(4096), 0, 0)

# T30 (V0-3b): the (colour x direction) parity classification. By
# `color_collision_x_par`/`_z_par`, a same-colour target collision needs equal
# `(par dx, par dz)`; the engine's four slides fall into exactly two parity
# classes (K0/K1 and K2/K3), and the drop is a third `(False, False)` class.
# Witness the table on the concrete direction values.
def dir_par_check(bad: U32) -> U32:
  +p0x = Parity.par32(Rules.dir_dx(Rules.K0{}))
  +p0z = Parity.par32(Rules.dir_dz(Rules.K0{}))
  +p1x = Parity.par32(Rules.dir_dx(Rules.K1{}))
  +p1z = Parity.par32(Rules.dir_dz(Rules.K1{}))
  +p2x = Parity.par32(Rules.dir_dx(Rules.K2{}))
  +p2z = Parity.par32(Rules.dir_dz(Rules.K2{}))
  +p3x = Parity.par32(Rules.dir_dx(Rules.K3{}))
  +p3z = Parity.par32(Rules.dir_dz(Rules.K3{}))
  b0 = inc_if_false(bool_eq(p0x, p1x), bad)
  b1 = inc_if_false(bool_eq(p0z, p1z), b0)
  b2 = inc_if_false(bool_eq(p2x, p3x), b1)
  b3 = inc_if_false(bool_eq(p2z, p3z), b2)
  b4 = inc_if_false(Bool.not(bool_eq(p0x, p2x)), b3)
  b5 = inc_if_false(Bool.not(bool_eq(p0z, p2z)), b4)
  b6 = inc_if_false(Bool.not(bool_eq(p0x, False{})), b5)
  b7 = inc_if_false(bool_eq(p2z, True{}), b6)
  b7

def dir_par_bad() -> U32:
  dir_par_check(0)

# T31 (V3c-1): point writes at leaves that `Commit.ne_idx` separates commute,
# and the predicate is sharp (`False` exactly when the two writes collide at one
# leaf, where the second write wins). The tree is a 4-leaf `Refine.PT`; leaves are
# read back with the size-free `Tick.tget` walk.
def t31_tree() -> Refine.PT:
  Refine.PN{Refine.PN{Refine.PL{10}, Refine.PL{20}}, Refine.PN{Refine.PL{30}, Refine.PL{40}}}

def t31_check(+x: U32, +y: U32, +v: U32, +w: U32, bad: U32) -> U32:
  +t = t31_tree()
  +lhs = Refine.swap_m(Refine.swap_m(t, 4, x, v), 4, y, w)
  +rhs = Refine.swap_m(Refine.swap_m(t, 4, y, w), 4, x, v)
  b0 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 0), Tick.tget(rhs, 4, 0)), bad)
  b1 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 1), Tick.tget(rhs, 4, 1)), b0)
  b2 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 2), Tick.tget(rhs, 4, 2)), b1)
  b3 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 3), Tick.tget(rhs, 4, 3)), b2)
  b3

def t31_bad() -> U32:
  b0 = inc_if_false(Commit.ne_idx(t31_tree(), 4, 0, 1), 0)
  b1 = t31_check(0, 1, 100, 200, b0)
  b2 = inc_if_false(Commit.ne_idx(t31_tree(), 4, 1, 3), b1)
  b3 = t31_check(1, 3, 100, 200, b2)
  b4 = inc_if_false(Commit.ne_idx(t31_tree(), 4, 2, 0), b3)
  b5 = t31_check(2, 0, 7, 9, b4)
  b6 = inc_if_false(Bool.not(Commit.ne_idx(t31_tree(), 4, 2, 2)), b5)
  b7 = inc_if_false(U32.is_eq(Tick.tget(Refine.swap_m(Refine.swap_m(t31_tree(), 4, 2, 100), 4, 2, 200), 4, 2), 200), b6)
  b7

# T32 (V3c-1b): folding a `List` of point writes is invariant under the
# region-split/append reordering, witnessed on a 4-leaf `Refine.PT`. `xs` and
# `ys` target pairwise distinct leaves, so `xs <> ys` and `ys <> xs` agree, and
# the fold writes the expected values. The distinctness predicates are sharp: a
# colliding pair is rejected (`False`).
def t32_tree() -> Refine.PT:
  Refine.PN{Refine.PN{Refine.PL{10}, Refine.PL{20}}, Refine.PN{Refine.PL{30}, Refine.PL{40}}}

def t32_xs() -> +List<Commit.V3cWrite>:
  Commit.MkWrite{0, 100} <> Commit.MkWrite{2, 200} <> Nil{}

def t32_ys() -> +List<Commit.V3cWrite>:
  Commit.MkWrite{1, 300} <> Commit.MkWrite{3, 400} <> Nil{}

def t32_collide() -> +List<Commit.V3cWrite>:
  Commit.MkWrite{0, 999} <> Nil{}

def t32_check(+lhs: Refine.PT, +rhs: Refine.PT, bad: U32) -> U32:
  b0 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 0), Tick.tget(rhs, 4, 0)), bad)
  b1 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 1), Tick.tget(rhs, 4, 1)), b0)
  b2 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 2), Tick.tget(rhs, 4, 2)), b1)
  b3 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 3), Tick.tget(rhs, 4, 3)), b2)
  b3

def t32_bad() -> U32:
  +t = t32_tree()
  +xs = t32_xs()
  +ys = t32_ys()
  +xc = t32_collide()
  +p1 = Commit.v3c_fold(List.append(&2, Commit.V3cWrite, xs, ys), t, 4)
  +p2 = Commit.v3c_fold(List.append(&2, Commit.V3cWrite, ys, xs), t, 4)
  b0 = t32_check(p1, p2, 0)
  b1 = inc_if_false(U32.is_eq(Tick.tget(p1, 4, 0), 100), b0)
  b2 = inc_if_false(U32.is_eq(Tick.tget(p1, 4, 1), 300), b1)
  b3 = inc_if_false(U32.is_eq(Tick.tget(p1, 4, 2), 200), b2)
  b4 = inc_if_false(U32.is_eq(Tick.tget(p1, 4, 3), 400), b3)
  b5 = inc_if_false(Commit.v3c_pair_ne(xs, ys, t, 4), b4)
  b6 = inc_if_false(Commit.v3c_all_ne(ys, t, 4, 2), b5)
  b7 = inc_if_false(Bool.not(Commit.v3c_pair_ne(xs, xc, t, 4)), b6)
  b8 = inc_if_false(Bool.not(Commit.v3c_pair_ne(xs, xs, t, 4)), b7)
  b8

# T33 (V3c-2 soundness): `ne_idx` never separates equal indices, so it agrees
# with the engine's `U32.is_eq` on the equal case over a 4-leaf tree.
def t33_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +u = U32.add(U32.mul(i, 7), 3)
      b0 = inc_if_false(bool_eq(Commit.ne_idx(t32_tree(), 4, u, u), False{}), bad)
      b1 = inc_if_false(U32.is_eq(u, u), b0)
      t33_go(p, U32.add(i, 1), b1)

def t33_bad() -> U32:
  t33_go(16n, 0, 0)

# T37: a packed world's width is `2^depth` (law `g5_twidth_pow`).
def g5_tree(d: Nat) -> Refine.PT:
  match d:
    case 0n: Refine.PL{0}
    case 1n+ +p: Refine.PN{g5_tree(p), Refine.PL{0}}

def g5_pow_go(fuel: Nat, +d: Nat, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +t = g5_tree(d)
      ok = U32.is_eq(G5.g5_twidth(t), U32{G5.g5_mpow(32n, d)})
      g5_pow_go(p, Nat.add(d, 1n), inc_if_false(ok, bad))

def g5_pow_bad() -> U32:
  g5_pow_go(20n, 0n, 0)

# T38: the mask identity `i & (w - 1) = i` for in-range `i` (law `g5_and_mask_id`).
def g5_mask_i_go(fuel: Nat, +i: U32, +w: U32, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      inr = U32.is_lt(i, w)
      ok = Bool.or(Bool.not(inr), U32.is_eq(U32.and(i, U32.sub(w, 1)), i))
      g5_mask_i_go(p, U32.add(i, 1), w, inc_if_false(ok, bad))

def g5_mask_d_go(fuel: Nat, +d: Nat, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +w = G5.g5_twidth(g5_tree(d))
      g5_mask_d_go(p, Nat.add(d, 1n), g5_mask_i_go(64n, 0, w, bad))

def g5_mask_bad() -> U32:
  g5_mask_d_go(21n, 0n, 0)

# T39: the bare-index read (law `g5_read_get_bare`).
def g5_snd(p: Array<U32> & U32) -> U32:
  match p:
    case (a, b):
      b

def g5_bare_go(fuel: Nat, +i: U32, +t: Refine.PT, +w: U32, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      got = g5_snd(Array.get(U32, Refine.pack(t), i))
      ok = U32.is_eq(got, Tick.tget(t, w, i))
      g5_bare_go(p, U32.add(i, 1), t, w, inc_if_false(ok, bad))

# A balanced tree with distinct leaf values: `pack`+`Array.size` are only sound
# at runtime on full trees, and the values make the read check meaningful.
def g5_full(d: Nat, +base: U32) -> Refine.PT:
  match d:
    case 0n: Refine.PL{base}
    case 1n+ +p: Refine.PN{g5_full(p, base), g5_full(p, U32.add(base, U32.shln(1, p)))}

def g5_bare_bad() -> U32:
  +t = g5_full(3n, 0)
  g5_bare_go(8n, 0, t, G5.g5_twidth(t), 0)
# T34 (V3c-2 completeness witness): on the canonical full 8-leaf tree
# (`Commit.v3c_full(3)`, size 8), `ne_idx` is *exactly* `U32.is_eq(i,j) == False`
# for every in-range pair — the completeness direction that complements T33's
# soundness half. T35 repeats it on the 16-leaf tree to exercise the recursion
# one level deeper.
def t34_inner(fuel: Nat, +i: U32, +j: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      b0 = inc_if_false(bool_eq(Commit.ne_idx(Commit.v3c_full(3n), 8, i, j), Bool.not(U32.is_eq(i, j))), bad)
      t34_inner(p, i, U32.add(j, 1), b0)

def t34_outer(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      b0 = t34_inner(8n, i, 0, bad)
      t34_outer(p, U32.add(i, 1), b0)

def t34_bad() -> U32:
  t34_outer(8n, 0, 0)

def t35_inner(fuel: Nat, +i: U32, +j: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      b0 = inc_if_false(bool_eq(Commit.ne_idx(Commit.v3c_full(4n), 16, i, j), Bool.not(U32.is_eq(i, j))), bad)
      t35_inner(p, i, U32.add(j, 1), b0)

def t35_outer(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      b0 = t35_inner(16n, i, 0, bad)
      t35_outer(p, U32.add(i, 1), b0)

def t35_bad() -> U32:
  t35_outer(16n, 0, 0)

# T43/T44/T45 (C2/G15): `Ops.wake` is bounded by `Grid.step_inside`, so a wrapped
# step is inert. T43 wakes a cell on the x=0 face: the opposite x=63 face must not
# be activated, while the in-box neighbour (1,40,4) must be. T44 repeats it at the
# y=0/z=0 corner (a wrapped (63,63,4)). T45 is the control: an interior wake still
# marks both x neighbours, so the guard does not over-reject.
def t43_empty(depth: Nat) -> Array<U32>:
  match depth:
    case 0n:
      ALeaf{0}
    case 1n+ +p:
      ANode{t43_empty(p), t43_empty(p)}

# Scan the flat cell list once, checking the active bit at each target index.
# `t*`/`w*` are (index, expected-active) pairs; an index that is not one of the
# targets passes vacuously.
def wake_scan(
  fuel: Nat, cells: List<U32>, +k: U32,
  +t1: U32, +t2: U32, +t3: U32, +t4: U32,
  +w1: Bool, +w2: Bool, +w3: Bool, +w4: Bool, bad: U32
) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      match cells:
        case Nil{}:
          bad
        case Con{h, t}:
          +act = U32.is_ne(Cell.active(h), 0)
          +c1 = Bool.or(Bool.not(U32.is_eq(k, t1)), bool_eq(act, w1))
          +c2 = Bool.or(Bool.not(U32.is_eq(k, t2)), bool_eq(act, w2))
          +c3 = Bool.or(Bool.not(U32.is_eq(k, t3)), bool_eq(act, w3))
          +c4 = Bool.or(Bool.not(U32.is_eq(k, t4)), bool_eq(act, w4))
          +b0 = inc_if_false(c1, bad)
          +b1 = inc_if_false(c2, b0)
          +b2 = inc_if_false(c3, b1)
          +b3 = inc_if_false(c4, b2)
          wake_scan(p, t, U32.add(k, 1), t1, t2, t3, t4, w1, w2, w3, w4, b3)

def t43_bad() -> U32:
  w0 = t43_empty(18n)
  w1 = Array.set(U32, w0, Grid.index(0, 40, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w2 = Array.set(U32, w1, Grid.index(63, 40, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w3 = Ops.wake(w2, Grid.index(0, 40, 4))
  +ia = Grid.index(63, 40, 4)
  +ib = Grid.index(1, 40, 4)
  wake_scan(U32.to_nat(Grid.volume()), Grid.to_list(w3), 0,
    ia, ib, ia, ib, False{}, True{}, False{}, True{}, 0)

def t44_bad() -> U32:
  w0 = t43_empty(18n)
  w1 = Array.set(U32, w0, Grid.index(0, 0, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w2 = Array.set(U32, w1, Grid.index(63, 63, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w3 = Array.set(U32, w2, Grid.index(1, 1, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w4 = Ops.wake(w3, Grid.index(0, 0, 4))
  +ia = Grid.index(63, 63, 4)
  +ib = Grid.index(1, 1, 4)
  wake_scan(U32.to_nat(Grid.volume()), Grid.to_list(w4), 0,
    ia, ib, ia, ib, False{}, True{}, False{}, True{}, 0)

def t45_bad() -> U32:
  w0 = t43_empty(18n)
  w1 = Array.set(U32, w0, Grid.index(29, 40, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w2 = Array.set(U32, w1, Grid.index(31, 40, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w3 = Array.set(U32, w2, Grid.index(63, 40, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w4 = Array.set(U32, w3, Grid.index(0, 40, 4), Cell.encode(Cell.empty(), 0, 0, 0, 0))
  w5 = Ops.wake(w4, Grid.index(30, 40, 4))
  wake_scan(U32.to_nat(Grid.volume()), Grid.to_list(w5), 0,
    Grid.index(29, 40, 4), Grid.index(31, 40, 4), Grid.index(63, 40, 4), Grid.index(0, 40, 4),
    True{}, True{}, False{}, False{}, 0)

# T36 (V3c-2 completeness witness, deeper): the exactness `ne_idx = ¬is_eq` on
# the 32-leaf full tree (`Commit.v3c_full(5)`), exercising the new arithmetic
# bricks (subtraction range preservation and the halving size) one level further
# than T34/T35.
def t36_inner(fuel: Nat, +i: U32, +j: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      b0 = inc_if_false(bool_eq(Commit.ne_idx(Commit.v3c_full(5n), 32, i, j), Bool.not(U32.is_eq(i, j))), bad)
      t36_inner(p, i, U32.add(j, 1), b0)

def t36_outer(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      b0 = t36_inner(32n, i, 0, bad)
      t36_outer(p, U32.add(i, 1), b0)

def t36_bad() -> U32:
  t36_outer(32n, 0, 0)

# T40 (brick 2 witness): for `i` with `is_lt(i, 2^(d+1))` and `not is_lt(i, 2^d)`,
# the right child's index `i - 2^d` is still in `[0, 2^d)` — the range
# preservation `Commit.v3c_sub_two_lt` that the completeness recursion needs.
def t40_i_go(fuel: Nat, +i: U32, +w: U32, +w2: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      h1 = U32.is_lt(i, w2)
      h0 = U32.is_lt(i, w)
      concl = U32.is_lt(U32.sub(i, w), w)
      ok = Bool.or(Bool.or(Bool.not(h1), h0), concl)
      t40_i_go(p, U32.add(i, 1), w, w2, inc_if_false(ok, bad))

def t40_d_go(fuel: Nat, +d: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +w = Commit.v3c_two(d)
      +w2 = Commit.v3c_two(Nat.add(1n, d))
      b0 = t40_i_go(1100n, 0, w, w2, bad)
      t40_d_go(p, Nat.add(1n, d), b0)

def t40_bad() -> U32:
  t40_d_go(10n, 0n, 0)

# T41 (brick 3 witness): the canonical size halves, `shr(2^(d+1)) = 2^d`, for
# every non-wrapping `d` (`Commit.v3c_two_shr_of_lt`), i.e. `d` in `[0, 31)`.
def t41_go(fuel: Nat, +d: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +w = Commit.v3c_two(Nat.add(1n, d))
      +w0 = Commit.v3c_two(d)
      ok = U32.is_eq(U32.shr(w), w0)
      t41_go(p, Nat.add(1n, d), inc_if_false(ok, bad))

def t41_bad() -> U32:
  t41_go(31n, 0n, 0)

# T42 (brick 1 witness): `Word.cmp`'s `LT` reflected at the base — `i < 1` forces
# `i = 0` (`Commit.v3c_lt_one_u32`), the leaf case of the completeness induction.
def t42_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      ok = Bool.or(Bool.not(U32.is_lt(i, 1)), U32.is_eq(i, 0))
      t42_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def t42_bad() -> U32:
  t42_go(64n, 0, 0)

# T46 (V3c/G3 engine wire): the engine's sequential commit `Rules.commit_sets`
# equals the abstract fold `Commit.v3c_fold` of the projection `V3cw.v3cw_proj` on
# a 4-leaf `Refine.PT`. `WSet`s use the identity op (`OPres{OId{}}`) so the write
# value is `src`; the `WWake` is state-neutral for the set fold and vanishes in
# the projection. This is the runtime witness for the `v3cw_commit_fold` law.
def t46_tree() -> Refine.PT:
  Refine.PN{Refine.PN{Refine.PL{10}, Refine.PL{20}}, Refine.PN{Refine.PL{30}, Refine.PL{40}}}

def t46_ws() -> +List<Rules.Write>:
  Rules.WSet{0, Rules.OPres{Rules.OId{}}, 100}
    <> Rules.WWake{2}
    <> Rules.WSet{3, Rules.OPres{Rules.OId{}}, 400}
    <> Nil{}

def t46_check(+lhs: Refine.PT, +rhs: Refine.PT, bad: U32) -> U32:
  b0 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 0), Tick.tget(rhs, 4, 0)), bad)
  b1 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 1), Tick.tget(rhs, 4, 1)), b0)
  b2 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 2), Tick.tget(rhs, 4, 2)), b1)
  b3 = inc_if_false(U32.is_eq(Tick.tget(lhs, 4, 3), Tick.tget(rhs, 4, 3)), b2)
  b3

def t46_bad() -> U32:
  +t = t46_tree()
  +ws = t46_ws()
  +committed = Refine.unpack(Rules.commit_sets(V3cw.v3cw_lin(ws), Refine.pack(t)))
  +folded = Commit.v3c_fold(V3cw.v3cw_proj(ws), t, 4)
  b0 = t46_check(committed, folded, 0)
  b1 = inc_if_false(U32.is_eq(Tick.tget(folded, 4, 0), 100), b0)
  b2 = inc_if_false(U32.is_eq(Tick.tget(folded, 4, 1), 20), b1)
  b3 = inc_if_false(U32.is_eq(Tick.tget(folded, 4, 2), 30), b2)
  b4 = inc_if_false(U32.is_eq(Tick.tget(folded, 4, 3), 400), b3)
  b4

# T47 (V3c/G3 projection): the projection applies `Rules.apply_op` (here
# `OPres{OSupport{31}}` writes support `31`), and `WWake` entries do not change
# the tree (a wake+write list commits the same as the writes alone).
def t47_ws() -> +List<Rules.Write>:
  Rules.WSet{1, Rules.OPres{Rules.OSupport{31}}, 20}
    <> Rules.WWake{3}
    <> Nil{}

def t47_bad() -> U32:
  +t = t46_tree()
  +ws = t47_ws()
  +committed = Refine.unpack(Rules.commit_sets(V3cw.v3cw_lin(ws), Refine.pack(t)))
  +folded = Commit.v3c_fold(V3cw.v3cw_proj(ws), t, 4)
  b0 = t46_check(committed, folded, 0)
  b1 = inc_if_false(U32.is_eq(Cell.support(Tick.tget(folded, 4, 1)), 31), b0)
  b2 = inc_if_false(U32.is_eq(Cell.material(Tick.tget(folded, 4, 1)), Cell.material(20)), b1)
  b2

# T48 (V3c/G3 region split): two registers of the engine's write list with
# pairwise-distinct projected targets commit to the same tree in either order.
def t48_xs() -> +List<Rules.Write>:
  Rules.WSet{0, Rules.OPres{Rules.OId{}}, 100}
    <> Rules.WSet{2, Rules.OPres{Rules.OId{}}, 200} <> Nil{}

def t48_ys() -> +List<Rules.Write>:
  Rules.WSet{1, Rules.OPres{Rules.OId{}}, 300}
    <> Rules.WSet{3, Rules.OPres{Rules.OId{}}, 400} <> Nil{}

def t48_bad() -> U32:
  +t = t46_tree()
  +xs = t48_xs()
  +ys = t48_ys()
  xy = V3cw.v3cw_lin(List.append(&2, Rules.Write, xs, ys))
  yx = V3cw.v3cw_lin(List.append(&2, Rules.Write, ys, xs))
  +pxy = Refine.unpack(Rules.commit_sets(xy, Refine.pack(t)))
  +pyx = Refine.unpack(Rules.commit_sets(yx, Refine.pack(t)))
  b0 = t46_check(pxy, pyx, 0)
  b1 = inc_if_false(Commit.v3c_pair_ne(V3cw.v3cw_proj(xs), V3cw.v3cw_proj(ys), t, 4), b0)
  b2 = inc_if_false(U32.is_eq(Tick.tget(pxy, 4, 0), 100), b1)
  b2


# T49 (view3d): the pure voxel raycaster in `view/voxel.bend`. A shell-only
# world (bedrock on all six faces, empty inside) makes each axis ray's first
# hit hand-computable: from the centre (32.5, 32.5, 32.5) the far wall is
# entered after 30.5 cells, the near wall after 31.5, and the entry face normal
# is opposite the march axis. This is a `miss`-free world, so it also witnesses
# that the DDA stops at the *first* non-empty cell (the reported `t`).
def t49_border(+x: U32, +y: U32, +z: U32) -> Bool:
  b0 = U32.is_eq(x, 0)
  b1 = U32.is_eq(x, 63)
  b2 = U32.is_eq(y, 0)
  b3 = U32.is_eq(y, 63)
  b4 = U32.is_eq(z, 0)
  b5 = U32.is_eq(z, 63)
  Bool.or(Bool.or(b0, b1), Bool.or(Bool.or(b2, b3), Bool.or(b4, b5)))

def t49_gen(+x: U32, +y: U32, +z: U32) -> U32:
  Cell.encode(Bool.pick(U32, t49_border(x, y, z), 1, 0), 0, 0, 0, 0)

def t49_build(depth: Nat, +base: U32) -> Array<U32>:
  match depth:
    case 0n:
      ALeaf{t49_gen(Grid.ix(base), Grid.iy(base), Grid.iz(base))}
    case 1n+ +p:
      +h = U32.shln(1, p)
      ANode{t49_build(p, base), t49_build(p, U32.add(base, h))}

def t49_world() -> Array<U32>:
  t49_build(18n, 0)

def t49_hit(q: Array<U32> & Vox.Hit) -> Vox.Hit:
  match q:
    case (w, h):
      h

def t49_check(h: Vox.Hit, +wm: U32, +wx: F32, +wy: F32, +wz: F32, +wt: F32) -> U32:
  match h:
    case Vox.Miss{}:
      1
    case Vox.Hit{mat, nx, ny, nz, t}:
      okm = U32.is_eq(mat, wm)
      okx = F32.is_eq(nx, wx)
      oky = F32.is_eq(ny, wy)
      okz = F32.is_eq(nz, wz)
      okt = F32.is_lt(F32.abs(F32.sub(t, wt)), 0.01)
      all = Bool.and(okm, Bool.and(okx, Bool.and(oky, Bool.and(okz, okt))))
      inc_if_false(all, 0)

def t49_probe(
  +ox: F32, +oy: F32, +oz: F32, +dx: F32, +dy: F32, +dz: F32,
  +wm: U32, +wx: F32, +wy: F32, +wz: F32, +wt: F32
) -> U32:
  t49_check(t49_hit(Vox.trace(t49_world(), ox, oy, oz, dx, dy, dz)), wm, wx, wy, wz, wt)

def t49_bad() -> U32:
  b0 = t49_probe(32.5, 32.5, 32.5, 1.0, 0.0, 0.0, 1, F32.neg(1.0), 0.0, 0.0, 30.5)
  b1 = t49_probe(32.5, 32.5, 32.5, F32.neg(1.0), 0.0, 0.0, 1, 1.0, 0.0, 0.0, 31.5)
  b2 = t49_probe(32.5, 32.5, 32.5, 0.0, 1.0, 0.0, 1, 0.0, F32.neg(1.0), 0.0, 30.5)
  b3 = t49_probe(32.5, 32.5, 32.5, 0.0, F32.neg(1.0), 0.0, 1, 0.0, 1.0, 0.0, 31.5)
  b4 = t49_probe(32.5, 32.5, 32.5, 0.0, 0.0, 1.0, 1, 0.0, 0.0, F32.neg(1.0), 30.5)
  b5 = t49_probe(32.5, 32.5, 32.5, 0.0, 0.0, F32.neg(1.0), 1, 0.0, 0.0, 1.0, 31.5)
  U32.add(b0, U32.add(b1, U32.add(b2, U32.add(b3, U32.add(b4, b5)))))


# T50 (view3d input): both backend key conventions map to the same held bits, and
# the command keys change depth/speed/pause. The X11 backend reports printable
# keys lowercased and the arrows as 63232..63235; the Mac/GLFW convention reports
# uppercase letters and 262..265. `bit_of` accepts both, so the controls work on
# either backend (the T50 witness is the first-version keyboard fix).
def t50_keys(sp: View3d.St) -> U32:
  match sp:
    case View3d.St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
      keys

def t50_depth(sp: View3d.St) -> Nat:
  match sp:
    case View3d.St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
      depth

def t50_run(sp: View3d.St) -> Bool:
  match sp:
    case View3d.St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
      run

def t50_speed(sp: View3d.St) -> U32:
  match sp:
    case View3d.St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
      speed

def t50_bad() -> U32:
  # W (87) and w (119) set bit 0 identically.
  +kw = View3d.held(t50_keys(View3d.handle_key(87, True{}, View3d.init())), 0n)
  +kw2 = View3d.held(t50_keys(View3d.handle_key(119, True{}, View3d.init())), 0n)
  b0 = inc_if_false(Bool.and(kw, kw2), 0)
  # Left: X11 63234 and Mac 263 both set bit 4.
  +kl = View3d.held(t50_keys(View3d.handle_key(63234, True{}, View3d.init())), 4n)
  +kl2 = View3d.held(t50_keys(View3d.handle_key(263, True{}, View3d.init())), 4n)
  b1 = inc_if_false(Bool.and(kl, kl2), b0)
  # Up: X11 63232 and Mac 265 both set bit 6.
  +ku = View3d.held(t50_keys(View3d.handle_key(63232, True{}, View3d.init())), 6n)
  +ku2 = View3d.held(t50_keys(View3d.handle_key(265, True{}, View3d.init())), 6n)
  b2 = inc_if_false(Bool.and(ku, ku2), b1)
  # '.' raises the render depth from 7 to 8; ',' lowers it to 6.
  +d1 = t50_depth(View3d.handle_key(46, True{}, View3d.init()))
  b3 = inc_if_false(U32.is_eq(U32.from_nat(d1), 8), b2)
  +d2 = t50_depth(View3d.handle_key(44, True{}, View3d.init()))
  b4 = inc_if_false(U32.is_eq(U32.from_nat(d2), 6), b3)
  # space pauses; '=' speeds up from 1 to 2.
  b5 = inc_if_false(Bool.not(t50_run(View3d.handle_key(32, True{}, View3d.init()))), b4)
  b6 = inc_if_false(U32.is_eq(t50_speed(View3d.handle_key(61, True{}, View3d.init())), 2), b5)
  b6


# T51 (view3d viewport): the window backend maps a depth-d Image to a w x h
# window by top bits, so the visible sub-image is ceil(w/2^s) x ceil(h/2^s) with
# s = k - d and 2^k >= max(w,h). These are the numbers `view_image` uses.
def t51_bad() -> U32:
  b0 = inc_if_false(U32.is_eq(U32.from_nat(Vox.clog2(1920)), 11), 0)
  b1 = inc_if_false(U32.is_eq(U32.from_nat(Vox.clog2(1024)), 10), b0)
  b2 = inc_if_false(U32.is_eq(U32.from_nat(Vox.clog2(1)), 0), b1)
  # 1920x1080 at depth 7 -> s = 4 -> 120 x 68 cells (16x upscale)
  +s7 = Vox.scale_bits(1920, 1080, 7n)
  b3 = inc_if_false(U32.is_eq(U32.from_nat(s7), 4), b2)
  b4 = inc_if_false(U32.is_eq(Vox.vis_dim(1920, s7), 120), b3)
  b5 = inc_if_false(U32.is_eq(Vox.vis_dim(1080, s7), 68), b4)
  # depth 8 -> s = 3 -> 240 x 135 (8x upscale)
  +s8 = Vox.scale_bits(1920, 1080, 8n)
  b6 = inc_if_false(U32.is_eq(Vox.vis_dim(1920, s8), 240), b5)
  b7 = inc_if_false(U32.is_eq(Vox.vis_dim(1080, s8), 135), b6)
  # a 512x512 window at depth 7 shows the whole 128x128 image (s = 2)
  +s512 = Vox.scale_bits(512, 512, 7n)
  b8 = inc_if_false(U32.is_eq(U32.from_nat(s512), 2), b7)
  b9 = inc_if_false(U32.is_eq(Vox.vis_dim(512, s512), 128), b8)
  b9
# T56 (P1 trace surface): `Sim.tick_trace` is the tick plus a delta list. The
# delta carries a changed cell's *global* coordinate and its NEW word (the
# `Rules.apply_op` effect), so a consumer (Bendview) never re-implements the op.
# The witness checks two things in one pass:
#   (a) the traced world is exactly the non-trace one-tick world `Sim.ticks(1, ..)`
#       (the `tick` path and the carried-mask `ticks` path agree);
#   (b) replaying the deltas onto the PRE-tick world reproduces the tick world up
#       to the activity bit. `WWake` only sets bit 11 (activity) at tick end, and
#       that bit is engine-internal, so a renderer's mirror matches exactly on
#       the render-visible fields (material/cohesion/support/fall).
def replay_deltas_go(ds: List<Sim.Delta>, world: Array<U32>) -> Array<U32>:
  match ds:
    case Nil{}:
      world
    case Con{h, t}:
      match h:
        case Sim.Delta{x, y, z, val}:
          +idx = Grid.index(x, y, z)
          replay_deltas_go(t, world[idx] <- val)

def t56_cmp(lrep: List<U32>, lpost: List<U32>, lticks: List<U32>, +bad: U32) -> U32:
  match lrep:
    case Nil{}:
      bad
    case Con{hr, tr}:
      match lpost:
        case Nil{}:
          bad
        case Con{+hp, tp}:
          match lticks:
            case Nil{}:
              bad
            case Con{ht, tt}:
              b1 = inc_if_false(U32.is_eq(hp, ht), bad)
              b2 = inc_if_false(U32.is_eq(Cell.deactivate(hr), Cell.deactivate(hp)), b1)
              t56_cmp(tr, tp, tt, b2)

def t56_check(r: Array<U32> & List<Sim.Delta>) -> U32:
  match r:
    case (post, ds):
      rep = replay_deltas_go(ds, Fixtures.spawn(Sim.build()))
      t56_cmp(Grid.to_list(rep), Grid.to_list(post),
        Grid.to_list(Sim.ticks(1n, Fixtures.spawn(Sim.build()))), 0)

def t56_bad() -> U32:
  t56_check(Sim.tick_trace(Fixtures.spawn(Sim.build())))


# T52-T55 (track `bridge`, P0b): the golden engine-contract fixture Bendview
# reads. These pin the exact integers of the boundary (cell word, index, chunk
# key, gen vector); a future engine change that breaks the renderer fails here
# instead of silently drifting. See `runners/export.bend` for the byte layout.

def t52_bad() -> U32:
  b0 = inc_if_false(U32.is_eq(Cell.encode(1, 63, 0, 0, 0), 2017), 0)
  b1 = inc_if_false(U32.is_eq(Cell.encode(3, 48, 0, 0, 0), 1539), b0)
  b2 = inc_if_false(U32.is_eq(Cell.encode(2, 0, 0, 0, 0), 2), b1)
  b2

def t53_bad() -> U32:
  b0 = inc_if_false(U32.is_eq(Grid.index(32, 3, 32), 14368), 0)
  b1 = inc_if_false(U32.is_eq(Grid.index(63, 63, 63), 262143), b0)
  b2 = inc_if_false(U32.is_eq(Grid.index(1, 2, 3), 8385), b1)
  b2

def t54_bad() -> U32:
  b0 = inc_if_false(U32.is_eq(Chunk.key(0, 0, 0), 0), 0)
  b1 = inc_if_false(U32.is_eq(Chunk.key(1, 2, 3), 2100225), b0)
  b2 = inc_if_false(U32.is_eq(Chunk.key(3, 3, 3), 3148803), b1)
  b2

def t55_bad() -> U32:
  b0 = inc_if_false(U32.is_eq(Worldgen.gen(0, 63, 0, 42), 2017), 0)
  b1 = inc_if_false(U32.is_eq(Worldgen.gen(32, 3, 32, 42), 1539), b0)
  b2 = inc_if_false(U32.is_eq(Worldgen.gen(21, 20, 21, 42), 2), b1)
  b3 = inc_if_false(U32.is_eq(Worldgen.gen(21, 42, 21, 42), 0), b2)
  b3

def main() -> IO(Unit):
  do IO<Unit>:
    report("T5 index roundtrip (2^18)", index_bad())
    report("T5 cell field roundtrip", cell_bad())
    report("spike bit31", is_bad(U32.is_eq(U32.shln(1, 31n), 2147483648)))
    report("spike mul wrap", is_bad(U32.is_eq(U32.mul(4294967295, 2), 4294967294)))
    report("T6 gen determinism", gen_det_bad())
    report("T7 terrain structure", terrain_bad())
    report("T8 build matches gen (all cells)", build_bad())
    report("T10 parity flip + neighbor x", parity_bad())
    report("T11 low6 add independence + pm1 cancel", mod_bad())
    report("T12 dir phi cancellation", phi_bad())
    report("T13 neighbor index cancellation", nc_bad())
    report("T14 scan order totality", total_bad())
    report("T15 list set split + sum", set_laws_bad())
    report("T16 chunk key/local roundtrip + gen", chunk_bad())
    report("T17 chunk store set/get/overwrite", store_bad())
    report("T18 store assemble == worldgen", assemble_bad())
    report("T19 write->pot bridge", wp_bad())
    report("T20a empty store regenerates worldgen", ev_empty_bad())
    report("T20b all-gen store evicts to worldgen", ev_full_bad())
    report("T20c evict preserves world (one resident chunk)", ev_mod_bad())
    report("T20d sleeping/gen-eq predicates", ev_pred_bad())
    report("T21 conservation of non-Empty writes", cnt_bad())
    report("T22 movement Phi cross + fall account", mov_bad())
    report("T29 Dir4 == U32 direction table (all 4)", dir4_bad())
    report("T30 direction parity classification", dir_par_bad())
    report("T31 point writes commute at distinct leaves", t31_bad())
    report("T32 fold commutes under region split", t32_bad())
    report("T33 ne_idx sound wrt U32 equality", t33_bad())
    report("T37 g5_twidth = 2^depth", g5_pow_bad())
    report("T38 g5 bare-index mask identity", g5_mask_bad())
    report("T39 g5 bare-index read", g5_bare_bad())
    report("T34 ne_idx exact on 8-leaf full tree", t34_bad())
    report("T35 ne_idx exact on 16-leaf full tree", t35_bad())
    report("T43 wake wrap inert at x=0 face (G15)", t43_bad())
    report("T44 wake wrap inert at corner (G15)", t44_bad())
    report("T45 interior wake still marks both sides (G15)", t45_bad())
    report("T36 ne_idx exact on 32-leaf full tree", t36_bad())
    report("T40 V3c-2 sub range preservation", t40_bad())
    report("T41 V3c-2 canonical size halves", t41_bad())
    report("T42 V3c-2 lt-one reflection", t42_bad())
    report("T46 engine commit == projected fold", t46_bad())
    report("T47 projection applies op + wwake neutral", t47_bad())
    report("T48 engine region split commutes", t48_bad())
    report("T49 view3d DDA shell hits", t49_bad())
    report("T50 view3d input both key conventions", t50_bad())
    report("T51 view3d viewport mapping", t51_bad())
    report("T52 golden cell word (encode)", t52_bad())
    report("T53 golden grid index", t53_bad())
    report("T54 golden chunk key", t54_bad())
    report("T55 golden worldgen vector", t55_bad())
    report("T56 tick_trace deltas replay + path agreement", t56_bad())
