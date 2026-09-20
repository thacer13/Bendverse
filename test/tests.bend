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
import ../src/cw.bend as Cw
import ../src/winset.bend as Winset
import ../src/window.bend as Window
import ../src/winshell.bend as Winshell
import ../src/maskword.bend as Maskword
import ../scenarios/fixtures.bend as Fixtures
import ../view/voxel.bend as Vox
import ../runners/view3d.bend as View3d
import ../runners/serve.bend as Serve
import ../runners/export.bend as Export
import ../src/dirty.bend as Dirty
import ../src/dirtyn.bend as Dirtyn
import ../src/wgrid.bend as WGrid

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
# T57-T60 (P3 cw): the global-coordinate module. `cw` splits a global (x,y,z)
# into a chunk key + local index and rejoins it with no torus mask, unlike
# `Grid.index` which folds each axis `&63`. Additive: no live path uses it.
def cw_key_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +k = U32.and(U32.mul(i, 2654435761), 1073741823)
      ok = U32.is_eq(Cw.cw_key(Cw.cw_key_x(k), Cw.cw_key_y(k), Cw.cw_key_z(k)), k)
      cw_key_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def t57_bad() -> U32:
  cw_key_go(U32.to_nat(4096), 0, 0)

def cw_local_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +l = U32.and(i, 4095)
      ok = U32.is_eq(Cw.cw_local(Cw.cw_local_x(l), Cw.cw_local_y(l), Cw.cw_local_z(l)), l)
      cw_local_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def t58_bad() -> U32:
  cw_local_go(U32.to_nat(4096), 0, 0)

def cw_round_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +x = U32.and(U32.mul(i, 7), 16383)
      +y = U32.and(U32.add(U32.mul(i, 13), 1), 16383)
      +z = U32.and(U32.add(U32.mul(i, 29), 2), 16383)
      +k = Cw.cw_key(Cw.cw_chunk_of(x), Cw.cw_chunk_of(y), Cw.cw_chunk_of(z))
      +l = Cw.cw_local(Cw.cw_local_of(x), Cw.cw_local_of(y), Cw.cw_local_of(z))
      okx = U32.is_eq(Cw.cw_global_x(k, l), x)
      oky = U32.is_eq(Cw.cw_global_y(k, l), y)
      okz = U32.is_eq(Cw.cw_global_z(k, l), z)
      all = Bool.and(Bool.and(okx, oky), okz)
      cw_round_go(p, U32.add(i, 1), inc_if_false(all, bad))

def t59_bad() -> U32:
  cw_round_go(U32.to_nat(4096), 0, 0)

# T60: no torus mask. A global x = 200 lives in chunk 12 (200>>4) at local 8,
# and `cw` reconstructs 200; the live `Grid.index` folds it to 8. A coordinate
# above the fixed 64 window is preserved, which is what a moving window needs.
def t60_bad() -> U32:
  +x = {200 : U32}
  +k = Cw.cw_key(Cw.cw_chunk_of(x), 0, 0)
  +l = Cw.cw_local(Cw.cw_local_of(x), 0, 0)
  b0 = inc_if_false(U32.is_eq(Cw.cw_global_x(k, l), x), 0)
  b1 = inc_if_false(U32.is_eq(Cw.cw_key_x(k), 12), b0)
  b2 = inc_if_false(U32.is_eq(Cw.cw_local_x(l), 8), b1)
  b3 = inc_if_false(U32.is_eq(Cw.cw_pack_key(Cw.cw_pack(x, 0, 0)), Cw.cw_key(12, 0, 0)), b2)
  b4 = inc_if_false(U32.is_eq(Cw.cw_pack_local(Cw.cw_pack(x, 0, 0)), Cw.cw_local(8, 0, 0)), b3)
  +idx = Grid.index(x, 0, 0)
  b5 = inc_if_false(U32.is_eq(Grid.ix(idx), 8), b4)
  b5

# T61-T65 (track `bridge2`, B1/B2): the sidecar transport. T61 witnesses the
# length-prefixed little-endian framing (encode then decode); T62 HELLO and the
# inbound control kinds (CREDIT/REQUEST/STOP); T63 the dense first snapshot's
# frame contract against `runners/export.bend`'s body size; T64 the sparse
# snapshot (evicted chunks omitted, `assemble` regenerates them); T65 the B2
# delta contract (render-visible fields only, global `Grid.index` idx).

# Typed byte/word list builders (a local annotation on `List<&2, U32>` is not
# accepted by the parser, so the element type is fixed by the parameters).
def bridge2_w4(a: U32, b: U32, c: U32, d: U32) -> List<&2, U32>:
  a <> (b <> (c <> (d <> Nil{})))

def bridge2_w7(a: U32, b: U32, c: U32, d: U32, e: U32, f: U32, g: U32) -> List<&2, U32>:
  a <> (b <> (c <> (d <> (e <> (f <> (g <> Nil{}))))))

# Compare two `List<&2, U32>` byte buffers (the `&2` kind, unlike `list_cmp_go`).
def bridge2_cmp(+xs: List<&2, U32>, +ys: List<&2, U32>, bad: U32) -> U32:
  inc_if_false(dlist_eq(xs, ys), bad)

# T61: an 8-byte payload (two u32 words) frames as [len=8][kind=2][w0 w1], and
# decoding the bytes recovers exactly those u32 words.
def t61_bad() -> U32:
  payload = Export.bxe_u32_le(10, Export.bxe_u32_le(20, Nil{}))
  frame = Serve.bridge2_frame(2, payload)
  words = Serve.bridge2_dec_words(frame)
  expected = bridge2_w4(8, 2, 10, 20)
  bridge2_cmp(words, expected, 0)

# T62: HELLO carries (version, world_edge, chunk_edge, seed, tick); the three
# inbound control kinds decode back to their fields.
def bridge2_credit_ok(c: Serve.Bridge2Ctrl) -> Bool:
  match c:
    case Serve.BCredit{frames}:
      U32.is_eq(frames, 4)
    case _:
      False{}

def bridge2_request_ok(c: Serve.Bridge2Ctrl) -> Bool:
  match c:
    case Serve.BRequest{tick, flags}:
      Bool.and(U32.is_eq(tick, 9), U32.is_eq(flags, 3))
    case _:
      False{}

def bridge2_stop_ok(c: Serve.Bridge2Ctrl) -> Bool:
  match c:
    case Serve.BStop{}:
      True{}
    case _:
      False{}

def t62_bad() -> U32:
  hello = Serve.bridge2_dec_words(Serve.bridge2_hello(7))
  hexp = bridge2_w7(20, 0, 1, 64, 16, 42, 7)
  b0 = bridge2_cmp(hello, hexp, 0)
  credit = Serve.bridge2_decode_control(Serve.bridge2_frame(5, Export.bxe_u32_le(4, Nil{})))
  b1 = inc_if_false(bridge2_credit_ok(credit), b0)
  request = Serve.bridge2_decode_control(Serve.bridge2_frame(6, Export.bxe_u32_le(9, Export.bxe_u32_le(3, Nil{}))))
  b2 = inc_if_false(bridge2_request_ok(request), b1)
  stop = Serve.bridge2_decode_control(Serve.bridge2_frame(7, Nil{}))
  inc_if_false(bridge2_stop_ok(stop), b2)

# T63: the dense first snapshot is the exporter's body behind a kind-1 header:
# its declared frame size is 8 + the exporter's fixed body size, and the wrapper
# is exactly `bridge2_frame(1, body)`. (The body itself is literally
# `Export.bxe_snapshot_bytes`, so it is byte-identical to `runners/export.bend`;
# the full 1 MiB body is not materialised here, only its size contract.)
def t63_bad() -> U32:
  b0 = inc_if_false(U32.is_eq(Serve.bridge2_dense_frame_size(), 1048872), 0)
  b1 = inc_if_false(U32.is_eq(Export.bxe_snapshot_size(), 1048864), b0)
  body = Export.bxe_u32_le(7, Export.bxe_u32_le(9, Nil{}))
  words = Serve.bridge2_dec_words(Serve.bridge2_frame(1, body))
  bridge2_cmp(words, bridge2_w4(8, 1, 7, 9), b1)

# T64: eviction drops sleeping gen-equal chunks; the sparse snapshot reports the
# reduced resident count, and `assemble` regenerates the world exactly.
def t64_bad() -> U32:
  all = Store.build_all()
  +ev = Store.evict(all)
  sp = Serve.bridge2_snapshot_sparse(ev, 0)
  hdr = List.take(&2, U32, List.drop(&2, U32, sp, 8n), 32n)
  hexp = Serve.bridge2_snap_header(0, 0, Nil{})
  b0 = bridge2_cmp(hdr, hexp, 0)
  a = Store.assemble(ev)
  b = Worldgen.build()
  b1 = list_cmp_go(U32.to_nat(262144), Grid.to_list(a), Grid.to_list(b), b0)
  +k = Chunk.key(1, 2, 3)
  +s2 = Store.set(Store.build_all(), k, mod_first(Store.chunk_list(k)))
  +ev2 = Store.evict(s2)
  sp2 = Serve.bridge2_snapshot_sparse(ev2, 0)
  hexp2 = Serve.bridge2_snap_header(1, 0, Nil{})
  b2 = bridge2_cmp(List.take(&2, U32, List.drop(&2, U32, sp2, 8n), 32n), hexp2, b1)
  a2 = Store.assemble(s2)
  b3 = Store.assemble(ev2)
  list_cmp_go(U32.to_nat(262144), Grid.to_list(a2), Grid.to_list(b3), b2)

# T65: the B2 delta contract, witnessed on a constructed delta so the exact
# bytes are known. The frame is kind 2, tick 1, count 1, and the single record
# is `Grid.index(x, y, z)` (the GLOBAL torus index) followed by
# `Cell.deactivate(new)` -- render-visible fields only, activity bit cleared.
def bridge2_mk_delta(x: U32, y: U32, z: U32, val: U32) -> Sim.Delta:
  Sim.Delta{x, y, z, val}

def bridge2_delta_list(d: Sim.Delta) -> List<Sim.Delta>:
  d <> Nil{}

def t65_bad() -> U32:
  d = bridge2_mk_delta(5, 6, 7, 12345)
  ds = bridge2_delta_list(d)
  +frame = Serve.bridge2_delta_frame(1, ds)
  hdr_exp = Export.bxe_u32_le(16, Export.bxe_u32_le(2, Export.bxe_u32_le(1, Export.bxe_u32_le(1, Nil{}))))
  b0 = bridge2_cmp(List.take(&2, U32, frame, 16n), hdr_exp, 0)
  rec_exp = Export.bxe_u32_le(Grid.index(5, 6, 7), Export.bxe_u32_le(Cell.deactivate(12345), Nil{}))
  +got = List.take(&2, U32, List.drop(&2, U32, frame, 16n), 8n)
  b1 = bridge2_cmp(got, rec_exp, b0)
  inc_if_false(U32.is_eq(Cell.active(Cell.deactivate(12345)), 0), b1)

# T66-T70 (P3/G-scale-3): the five proven `gscale` laws, witnessed over a dense
# range. T66-T68 check the bounded axis roundtrips (`cw_global_x/y/z` of an
# in-range coordinate is the coordinate) exactly as stated; T69/T70 check the
# *unconditional* masked key/local reconstruction that `gscale_kmodel_rt` /
# `gscale_lmodel_rt` prove (`cw_key(kx,ky,kz) = k & (2^30-1)`, likewise local),
# which is stronger than the in-range T57/T58 witnesses.
def gscale_x_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +x = U32.and(U32.mul(i, 7919), 16383)
      +y = U32.and(U32.add(U32.mul(i, 13), 1), 16383)
      +z = U32.and(U32.add(U32.mul(i, 29), 2), 16383)
      +k = Cw.cw_key(Cw.cw_chunk_of(x), Cw.cw_chunk_of(y), Cw.cw_chunk_of(z))
      +l = Cw.cw_local(Cw.cw_local_of(x), Cw.cw_local_of(y), Cw.cw_local_of(z))
      ok = U32.is_eq(Cw.cw_global_x(k, l), x)
      gscale_x_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def t66_bad() -> U32:
  gscale_x_go(U32.to_nat(4096), 0, 0)

def gscale_y_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +y = U32.and(U32.add(U32.mul(i, 7919), 3), 16383)
      +k = Cw.cw_key(0, Cw.cw_chunk_of(y), 0)
      +l = Cw.cw_local(0, Cw.cw_local_of(y), 0)
      ok = U32.is_eq(Cw.cw_global_y(k, l), y)
      gscale_y_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def t67_bad() -> U32:
  gscale_y_go(U32.to_nat(4096), 0, 0)

def gscale_z_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +z = U32.and(U32.add(U32.mul(i, 7919), 5), 16383)
      +k = Cw.cw_key(0, 0, Cw.cw_chunk_of(z))
      +l = Cw.cw_local(0, 0, Cw.cw_local_of(z))
      ok = U32.is_eq(Cw.cw_global_z(k, l), z)
      gscale_z_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def t68_bad() -> U32:
  gscale_z_go(U32.to_nat(4096), 0, 0)

def gscale_key_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +k = U32.and(U32.mul(i, 2654435761), 4294967295)
      ok = U32.is_eq(Cw.cw_key(Cw.cw_key_x(k), Cw.cw_key_y(k), Cw.cw_key_z(k)), U32.and(k, 1073741823))
      gscale_key_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def t69_bad() -> U32:
  gscale_key_go(U32.to_nat(4096), 0, 0)

def gscale_local_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +l = U32.and(U32.mul(i, 2654435761), 4294967295)
      ok = U32.is_eq(Cw.cw_local(Cw.cw_local_x(l), Cw.cw_local_y(l), Cw.cw_local_z(l)), U32.and(l, 4095))
      gscale_local_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def t70_bad() -> U32:
  gscale_local_go(U32.to_nat(4096), 0, 0)

# T71-T72 (track `gscale2`): the full three-coordinate y/z roundtrips
# (`gscale_cw_y_rt_full` / `gscale_cw_z_rt_full`). Unlike T67/T68 these pack all
# three chunk slots, so the axis field has to be recovered from a general key.
def gscale_y_full_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +x = U32.and(U32.add(U32.mul(i, 7919), 1), 16383)
      +y = U32.and(U32.add(U32.mul(i, 13), 3), 16383)
      +z = U32.and(U32.add(U32.mul(i, 29), 2), 16383)
      +k = Cw.cw_key(Cw.cw_chunk_of(x), Cw.cw_chunk_of(y), Cw.cw_chunk_of(z))
      +l = Cw.cw_local(Cw.cw_local_of(x), Cw.cw_local_of(y), Cw.cw_local_of(z))
      ok = U32.is_eq(Cw.cw_global_y(k, l), y)
      gscale_y_full_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def t71_bad() -> U32:
  gscale_y_full_go(U32.to_nat(4096), 0, 0)

def gscale_z_full_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +x = U32.and(U32.add(U32.mul(i, 7919), 5), 16383)
      +y = U32.and(U32.add(U32.mul(i, 13), 7), 16383)
      +z = U32.and(U32.add(U32.mul(i, 29), 11), 16383)
      +k = Cw.cw_key(Cw.cw_chunk_of(x), Cw.cw_chunk_of(y), Cw.cw_chunk_of(z))
      +l = Cw.cw_local(Cw.cw_local_of(x), Cw.cw_local_of(y), Cw.cw_local_of(z))
      ok = U32.is_eq(Cw.cw_global_z(k, l), z)
      gscale_z_full_go(p, U32.add(i, 1), inc_if_false(ok, bad))

def t72_bad() -> U32:
  gscale_z_full_go(U32.to_nat(4096), 0, 0)

# T73-T75 (track `gscale2`, G-scale-4 groundwork): the explicit resident set.
# T73 witnesses membership/insert/remove over `cw_key`s; T74 that
# `winset_evict` drops regenerable residents (pure gen) and keeps modified ones;
# T75 that `winset_gen_cell` is the store's gen list and that
# `assemble(evict)` recovers worldgen.
def winset_ops_bad() -> U32:
  +a = Cw.cw_key(1, 2, 3)
  +b = Cw.cw_key(4, 5, 6)
  +c = Cw.cw_key(7, 7, 7)
  +s2 = Winset.winset_insert(b, Winset.winset_insert(a, Winset.winset_empty()))
  bad0 = inc_if_false(Winset.winset_mem(a, s2), 0)
  bad1 = inc_if_false(Winset.winset_mem(b, s2), bad0)
  bad2 = inc_if_false(Bool.not(Winset.winset_mem(c, s2)), bad1)
  +s3 = Winset.winset_remove(a, s2)
  bad3 = inc_if_false(Bool.not(Winset.winset_mem(a, s3)), bad2)
  bad4 = inc_if_false(Winset.winset_mem(b, s3), bad3)
  +all = Winset.winset_all()
  bad5 = inc_if_false(Winset.winset_mem(Cw.cw_key(3, 3, 3), all), bad4)
  inc_if_false(Bool.not(Winset.winset_mem(Cw.cw_key(4, 0, 0), all)), bad5)

def t73_bad() -> U32:
  winset_ops_bad()

def winset_evict_bad() -> U32:
  +store = Store.build_all()
  +kgen = Cw.cw_key(0, 0, 0)
  +kmod = Cw.cw_key(1, 2, 3)
  +sm = Store.set(store, kmod, mod_first(Store.chunk_list(kmod)))
  +s = Winset.winset_insert(kmod, Winset.winset_insert(kgen, Winset.winset_empty()))
  +ev = Winset.winset_evict(sm, s)
  bad0 = inc_if_false(Bool.not(Winset.winset_mem(kgen, ev)), 0)
  inc_if_false(Winset.winset_mem(kmod, ev), bad0)

def t74_bad() -> U32:
  winset_evict_bad()

def winset_gen_go(fuel: Nat, +k: U32, +i: U32, +gen: List<&2, U32>, +bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      match gen:
        case Nil{}:
          bad
        case Con{h, t}:
          ok = U32.is_eq(Winset.winset_gen_cell(k, i), h)
          winset_gen_go(p, k, U32.add(i, 1), t, inc_if_false(ok, bad))

def winset_roundtrip_bad() -> U32:
  +k = Chunk.key(2, 3, 1)
  bad0 = winset_gen_go(U32.to_nat(4096), k, 0, Store.chunk_list(k), 0)
  +store = Store.build_all()
  bad1 = inc_if_false(Winset.winset_regenerable(store, k), bad0)
  +km = Chunk.key(1, 2, 3)
  +sm = Store.set(store, km, mod_first(Store.chunk_list(km)))
  inc_if_false(Bool.not(Winset.winset_regenerable(sm, km)), bad1)

def t75_bad() -> U32:
  winset_roundtrip_bad()
# T76-T80 (track `bridge3`, G-bridge-1): the flow-control accounting that
# realises SERVE.md §5-§6. T76 the credit window (advance/debit, never overrun);
# T77 the bounded queue; T78 drop-and-keyframe coalescing; T79 the idle PING;
# T80 a deterministic end-to-end scenario over the bridge2 framing. The IO
# reader/writer shell is exercised by hand over a pipe (a law cannot observe IO).

# T76: a zero window cannot emit, and an emit attempt leaves the state at zero
# rather than wrapping (`U32.sub(0, 1) == 2^32-1`); CREDIT advances the window;
# each emit debits exactly one credit and one queue slot.
def t76_bad() -> U32:
  f0 = Serve.bridge3_flow_new(8)
  +f1 = Serve.bridge3_push_go(4n, 1, f0)
  b0 = inc_if_false(U32.is_eq(Serve.bridge3_window(f1), 0), 0)
  +f2 = Serve.bridge3_emit(f1)
  b1 = inc_if_false(U32.is_eq(Serve.bridge3_window(f2), 0), b0)
  b2 = inc_if_false(U32.is_eq(Serve.bridge3_queued(f2), 4), b1)
  +f3 = Serve.bridge3_credit(f2, 4)
  +f4 = Serve.bridge3_emit_go(4n, f3)
  b3 = inc_if_false(U32.is_eq(Serve.bridge3_window(f4), 0), b2)
  b4 = inc_if_false(U32.is_eq(Serve.bridge3_queued(f4), 0), b3)
  f5 = Serve.bridge3_emit(f4)
  b5 = inc_if_false(U32.is_eq(Serve.bridge3_window(f5), 0), b4)
  inc_if_false(U32.is_eq(U32.sub(0, 1), 4294967295), b5)

# T77: the queue is bounded -- 20 deltas into capacity 8 leave 8 resident and
# 12 coalesced, and `has_room` is false at capacity. A capacity-1 queue holds
# one frame and coalesces the rest.
def t77_bad() -> U32:
  f0 = Serve.bridge3_flow_new(8)
  +f1 = Serve.bridge3_push_go(20n, 1, f0)
  b0 = inc_if_false(U32.is_eq(Serve.bridge3_queued(f1), 8), 0)
  b1 = inc_if_false(U32.is_eq(Serve.bridge3_coalesced(f1), 12), b0)
  b2 = inc_if_false(Serve.bridge3_is_keyframe(f1), b1)
  b3 = inc_if_false(Bool.not(Serve.bridge3_has_room(f1)), b2)
  g0 = Serve.bridge3_flow_new(1)
  +g1 = Serve.bridge3_push_go(3n, 1, g0)
  b4 = inc_if_false(U32.is_eq(Serve.bridge3_queued(g1), 1), b3)
  inc_if_false(U32.is_eq(Serve.bridge3_coalesced(g1), 2), b4)

# T78: a delta that arrives at a full queue is dropped and arms a fresh
# SNAPSHOT; the writer policy prefers the keyframe over queued deltas, and
# taking the keyframe supersedes the delta run with exactly one SNAPSHOT.
def t78_bad() -> U32:
  f0 = Serve.bridge3_flow_new(2)
  f1 = Serve.bridge3_push_go(2n, 1, f0)
  +f2 = Serve.bridge3_push_delta(f1, 3)
  b0 = inc_if_false(U32.is_eq(Serve.bridge3_queued(f2), 2), 0)
  b1 = inc_if_false(U32.is_eq(Serve.bridge3_coalesced(f2), 1), b0)
  b2 = inc_if_false(Serve.bridge3_is_keyframe(f2), b1)
  +f3 = Serve.bridge3_credit(f2, 4)
  b3 = inc_if_false(U32.is_eq(Serve.bridge3_next(f3, 2), 1), b2)
  +f4 = Serve.bridge3_take_keyframe(f3)
  b4 = inc_if_false(Bool.not(Serve.bridge3_is_keyframe(f4)), b3)
  b5 = inc_if_false(U32.is_eq(Serve.bridge3_coalesced(f4), 0), b4)
  b6 = inc_if_false(U32.is_eq(Serve.bridge3_queued(f4), 1), b5)
  inc_if_false(U32.is_eq(Serve.bridge3_next(f4, 2), 2), b6)

# T79: an idle stream offers a PING once it passes the threshold -- but only
# with credit held and the queue empty; a queued frame beats the PING, and an
# emit resets the idle timer.
def t79_bad() -> U32:
  +f0 = Serve.bridge3_flow_new(4)
  b0 = inc_if_false(U32.is_eq(Serve.bridge3_next(f0, 3), 0), 0)
  +f1 = Serve.bridge3_credit(f0, 1)
  b1 = inc_if_false(U32.is_eq(Serve.bridge3_next(f1, 3), 0), b0)
  +f2 = Serve.bridge3_idle_go(3n, f1)
  b2 = inc_if_false(U32.is_eq(Serve.bridge3_idle(f2), 3), b1)
  b3 = inc_if_false(U32.is_eq(Serve.bridge3_next(f2, 3), 3), b2)
  +f3 = Serve.bridge3_push_frame(f2, 1)
  b4 = inc_if_false(U32.is_eq(Serve.bridge3_next(f3, 3), 2), b3)
  +f4 = Serve.bridge3_emit(f3)
  b5 = inc_if_false(U32.is_eq(Serve.bridge3_idle(f4), 0), b4)
  inc_if_false(U32.is_eq(Serve.bridge3_window(f4), 0), b5)

# T80: credit exhausted -> the queue overflows and coalesces -> credit returns
# -> the keyframe is taken and emitted as one SNAPSHOT frame. The frame bytes
# are the bridge2 framing: kind 1 for the SNAPSHOT and kind 3 for the idle PING.
def t80_bad() -> U32:
  f0 = Serve.bridge3_flow_new(2)
  f1 = Serve.bridge3_push_go(3n, 1, f0)
  +f2 = Serve.bridge3_credit(f1, 1)
  b0 = inc_if_false(U32.is_eq(Serve.bridge3_next(f2, 2), 1), 0)
  +f3 = Serve.bridge3_take_keyframe(f2)
  +f4 = Serve.bridge3_emit(f3)
  b1 = inc_if_false(U32.is_eq(Serve.bridge3_window(f4), 0), b0)
  b2 = inc_if_false(U32.is_eq(Serve.bridge3_queued(f4), 0), b1)
  +hdr = Serve.bridge2_dec_words(Serve.bridge2_frame(1, Export.bxe_u32_le(0, Nil{})))
  b3 = inc_if_false(U32.is_eq(Serve.bridge2_word0(hdr), 4), b2)
  b4 = inc_if_false(U32.is_eq(Serve.bridge2_word1(hdr), 1), b3)
  +ping = Serve.bridge2_dec_words(Serve.bridge2_ping(9))
  b5 = inc_if_false(U32.is_eq(Serve.bridge2_word1(ping), 3), b4)
  inc_if_false(U32.is_eq(Serve.bridge2_word0(ping), 4), b5)
# T81-T82 (S1 step 2, `src/window.bend`): the window model. T81 witnesses that
# `win_index` on the canonical 64^3 window is exactly `Grid.index` (the relabel)
# and that `win_gx/gy/gz` invert it; T82 witnesses the torus-free property: a
# window based at chunk 1 maps a global coordinate above 63 to a window-local
# coordinate instead of folding to the opposite face (contrast `Grid.ix`).
def win_canon_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +x = U32.and(U32.mul(i, 7), 63)
      +y = U32.and(U32.mul(i, 13), 63)
      +z = U32.and(U32.mul(i, 29), 63)
      +w = Window.canonical()
      +idx = Window.win_index(w, x, y, z)
      b0 = inc_if_false(U32.is_eq(idx, Grid.index(x, y, z)), bad)
      okx = U32.is_eq(Window.win_gx(w, idx), x)
      oky = U32.is_eq(Window.win_gy(w, idx), y)
      okz = U32.is_eq(Window.win_gz(w, idx), z)
      win_canon_go(p, U32.add(i, 1), inc_if_false(Bool.and(okx, Bool.and(oky, okz)), b0))

def t81_bad() -> U32:
  win_canon_go(U32.to_nat(4096), 0, 0)

def t82_bad() -> U32:
  +w = Window.at(1, 1, 1)
  b0 = inc_if_false(U32.is_eq(Window.win_lx(w, 79), 63), 0)
  b1 = inc_if_false(U32.is_eq(Window.win_lx(w, 80), 64), b0)
  +i = Window.win_index(w, 79, 79, 79)
  b2 = inc_if_false(U32.is_eq(Window.win_ix(i), 63), b1)
  b3 = inc_if_false(U32.is_eq(Grid.ix(Grid.index(80, 0, 0)), 16), b2)
  b3

# T83 (G-bridge-2): a snapshot record is a true 16^3 chunk in `Chunk.local`
# order, not a flat `Grid.index` slice. The full dense==sparse body equality is
# the native sim witness `t47` (the fast JS runner cannot hold two 1 MiB
# bodies). Here we pin the *address mapping*: record offset `i` of chunk `k`
# reads `Grid.index(Chunk.global_x/y/z(k,i))` -- and, as a regression guard,
# NOT the flat slice `ci*4096 + i` that was the defect.
def t83_bad() -> U32:
  +k = Chunk.key(0, 0, 0)
  b0 = inc_if_false(U32.is_eq(Export.bxe_cell_index(k, 273), Grid.index(1, 1, 1)), 0)
  b1 = inc_if_false(Bool.not(U32.is_eq(Export.bxe_cell_index(k, 273), 273)), b0)
  +k2 = Chunk.key(1, 2, 3)
  b2 = inc_if_false(U32.is_eq(Export.bxe_cell_index(k2, 1000),
    Grid.index(Chunk.global_x(k2, 1000), Chunk.global_y(k2, 1000), Chunk.global_z(k2, 1000))), b1)
  b2

# T84 (G-bridge-2 section 10): the record *order*. For a chunk `k`, the gathered
# cells must equal `Store.chunk_list(k)` element-by-element -- offset `i` holds
# local index `i` (forward `Chunk.local` order), not the reverse. T47 (dense ==
# sparse) cannot see an order both encoders share; this compares to the store's
# ground truth instead (`chunk_list` is what `assemble_chunk` expects).
def t84_pair(r: Array<U32> & List<&2, U32>) -> U32:
  match r:
    case (world, cells):
      inc_if_false(dlist_eq(cells, Store.chunk_list(Chunk.key(0, 0, 0))), 0)

def t84_bad() -> U32:
  t84_pair(Export.bxe_chunk_cells(Worldgen.build(), Chunk.key(0, 0, 0)))

# T85-T89 (track `genvec`, G-scale-8 / Bendview M3-M4): the shell-free terrain
# reference `bendverse-terrain.bgt`. T85 pins the format size; T86 the golden
# words; T87/T88 the exact split (`gen_terrain != gen` on a shell plane,
# `gen_terrain == gen` off it, out-of-box included); T89 that the sample spans
# every shell plane and an out-of-box coordinate and never emits bedrock.
# `gen` paints the ABSOLUTE planes x/y/z in {0,63}; `gen_terrain` never does.

def genvec_b2u(z: Bool) -> U32:
  Bool.pick(U32, z, 1, 0)

def genvec_shell(+x: U32, +y: U32, +z: U32) -> Bool:
  +b0 = U32.is_eq(x, 0)
  +b1 = U32.is_eq(x, 63)
  +b2 = U32.is_eq(y, 0)
  +b3 = U32.is_eq(y, 63)
  +b4 = U32.is_eq(z, 0)
  +b5 = U32.is_eq(z, 63)
  Bool.or(Bool.or(b0, b1), Bool.or(Bool.or(b2, b3), Bool.or(b4, b5)))

# T85: the terrain file is 16-byte header + 784 records * 20 bytes = 15696.
def t85_bad() -> U32:
  b0 = inc_if_false(U32.is_eq(Export.genvec_terrain_count(), 784), 0)
  b1 = inc_if_false(U32.is_eq(Export.genvec_terrain_size(), 15696), b0)
  b2 = inc_if_false(U32.is_eq(Export.genvec_terrain_size(), U32.add(16, U32.mul(784, 20))), b1)
  b2

# T86: golden `gen_terrain` words -- the three interior materials (Empty 0,
# Sand 2, Rock 1539 = encode(3,48,0,0,0)), a shell plane that `gen` would make
# bedrock (0,63,0 -> 0, not 2017), two out-of-box points, and a seed bump.
def t86_bad() -> U32:
  b0 = inc_if_false(U32.is_eq(Worldgen.gen_terrain(21, 20, 21, 42), 2), 0)
  b1 = inc_if_false(U32.is_eq(Worldgen.gen_terrain(21, 42, 21, 42), 0), b0)
  b2 = inc_if_false(U32.is_eq(Worldgen.gen_terrain(21, 3, 21, 42), 1539), b1)
  b3 = inc_if_false(U32.is_eq(Worldgen.gen_terrain(0, 63, 0, 42), 0), b2)
  b4 = inc_if_false(U32.is_eq(Worldgen.gen_terrain(200, 20, 200, 42), 0), b3)
  b5 = inc_if_false(U32.is_eq(Worldgen.gen_terrain(80, 8, 80, 42), 1539), b4)
  b6 = inc_if_false(U32.is_eq(Worldgen.gen_terrain(21, 20, 21, 43), 0), b5)
  b6

# T87: on every sample coordinate that lies on a shell plane, `gen` must differ
# from `gen_terrain` (the shell is exactly what `gen` adds).
def genvec_shell_ne_go(fuel: Nat, +c: U32, +bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +x = Export.genvec_rec_x(c)
      +y = Export.genvec_rec_y(c)
      +z = Export.genvec_rec_z(c)
      +s = Export.genvec_rec_seed(c)
      +g = Worldgen.gen(x, y, z, s)
      +gt = Worldgen.gen_terrain(x, y, z, s)
      ne = Bool.not(U32.is_eq(g, gt))
      bad2 = Bool.pick(U32, genvec_shell(x, y, z), inc_if_false(ne, bad), bad)
      genvec_shell_ne_go(p, U32.sub(c, 1), bad2)

def t87_bad() -> U32:
  genvec_shell_ne_go(U32.to_nat(Export.genvec_terrain_count()), U32.sub(Export.genvec_terrain_count(), 1), 0)

# T88: off the shell (including the out-of-box coordinates) `gen_terrain` must
# equal `gen` exactly -- the two samplers differ only on the shell planes.
def genvec_free_eq_go(fuel: Nat, +c: U32, +bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +x = Export.genvec_rec_x(c)
      +y = Export.genvec_rec_y(c)
      +z = Export.genvec_rec_z(c)
      +s = Export.genvec_rec_seed(c)
      +g = Worldgen.gen(x, y, z, s)
      +gt = Worldgen.gen_terrain(x, y, z, s)
      eq = U32.is_eq(g, gt)
      free = Bool.not(genvec_shell(x, y, z))
      bad2 = Bool.pick(U32, free, inc_if_false(eq, bad), bad)
      genvec_free_eq_go(p, U32.sub(c, 1), bad2)

def t88_bad() -> U32:
  genvec_free_eq_go(U32.to_nat(Export.genvec_terrain_count()), U32.sub(Export.genvec_terrain_count(), 1), 0)

# T89: sample coverage, accumulated as a bitmask -- low 6 bits: gen_terrain
# materials seen (must be 0,2,3 = 13, never bedrock bit 1); bits 8..13: `gen`
# materials seen (must be all four = 15, via the shell); bit 16: an out-of-box
# axis; bit 17: a shell plane. A port that bakes the shell in or masks to 64
# cannot reproduce this sample.
def genvec_cov_go(fuel: Nat, +c: U32, +acc: U32) -> U32:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      +x = Export.genvec_rec_x(c)
      +y = Export.genvec_rec_y(c)
      +z = Export.genvec_rec_z(c)
      +s = Export.genvec_rec_seed(c)
      +mgt = Cell.material(Worldgen.gen_terrain(x, y, z, s))
      +mg = Cell.material(Worldgen.gen(x, y, z, s))
      +xt = genvec_b2u(U32.is_ge(x, 64))
      +yt = genvec_b2u(U32.is_ge(y, 64))
      +zt = genvec_b2u(U32.is_ge(z, 64))
      +outv = U32.or(xt, U32.or(yt, zt))
      +shv = genvec_b2u(genvec_shell(x, y, z))
      +bt = U32.shln(1, U32.to_nat(mgt))
      +bg = U32.shln(U32.shln(1, U32.to_nat(mg)), 8n)
      +acc2 = U32.or(acc, U32.or(bt, U32.or(bg, U32.or(U32.shln(outv, 16n), U32.shln(shv, 17n)))))
      genvec_cov_go(p, U32.sub(c, 1), acc2)

def t89_bad() -> U32:
  +acc = genvec_cov_go(U32.to_nat(Export.genvec_terrain_count()), U32.sub(Export.genvec_terrain_count(), 1), 0)
  +tmask = U32.and(acc, 63)
  +gmask = U32.and(U32.shrn(acc, 8n), 63)
  +outv = U32.and(U32.shrn(acc, 16n), 1)
  +shv = U32.and(U32.shrn(acc, 17n), 1)
  b0 = inc_if_false(U32.is_eq(tmask, 13), 0)
  b1 = inc_if_false(U32.is_eq(gmask, 15), b0)
  b2 = inc_if_false(U32.is_eq(outv, 1), b1)
  b3 = inc_if_false(U32.is_eq(shv, 1), b2)
  b3
# T90-T94 (SCALE.md step 5 / G-scale-2, `src/dirtyn.bend`): the size-parameterised
# row mask. T90 zero mask; T91 `or_y` marks exactly its row; T92 `mark_if`; T93
# the `mark_wake` y-1/y/y+1 reach over several widths; T94 the n=6 (w=64)
# instance agrees with `Dirty` row-for-row, for both `or_y` and `mark_wake`.
def t90_go(+w: Nat, fuel: Nat, +y: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +d = Dirtyn.dwin_get(w, Dirtyn.dwin_zero(w), y)
      t90_go(w, p, Nat.add(y, 1n), inc_if_false(Bool.not(d), bad))

def t90_wn(n: Nat, bad: U32) -> U32:
  +w = Dirtyn.dwin_width(n)
  t90_go(w, w, 0n, bad)

def t90_ns(fuel: Nat, +n: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      t90_ns(p, Nat.add(n, 1n), t90_wn(n, bad))

def t90_bad() -> U32:
  t90_ns(8n, 1n, 0)

def t91_k(+w: Nat, fuel: Nat, +k: Nat, +y: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +m = Dirtyn.dwin_or_y(w, Dirtyn.dwin_zero(w), y)
      +d = Dirtyn.dwin_get(w, m, k)
      +e = Nat.is_eq(k, y)
      t91_k(w, p, Nat.add(k, 1n), y, inc_if_false(Bool.not(Bool.xor(d, e)), bad))

def t91_y(+w: Nat, fuel: Nat, +y: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      t91_y(w, p, Nat.add(y, 1n), t91_k(w, w, 0n, y, bad))

def t91_wn(n: Nat, bad: U32) -> U32:
  +w = Dirtyn.dwin_width(n)
  t91_y(w, w, 0n, bad)

def t91_ns(fuel: Nat, +n: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      t91_ns(p, Nat.add(n, 1n), t91_wn(n, bad))

def t91_bad() -> U32:
  t91_ns(6n, 1n, 0)

def t92_k(+w: Nat, fuel: Nat, +k: Nat, +y: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +m0 = Dirtyn.dwin_or_y(w, Dirtyn.dwin_zero(w), Nat.mod(Nat.add(y, 1n), w))
      +mt = Dirtyn.dwin_mark_if(w, m0, y, True{})
      +mf = Dirtyn.dwin_mark_if(w, m0, y, False{})
      +dt = Dirtyn.dwin_get(w, mt, k)
      +df = Dirtyn.dwin_get(w, mf, k)
      +d0 = Dirtyn.dwin_get(w, m0, k)
      +e = Nat.is_eq(k, y)
      +b1 = inc_if_false(Bool.or(Bool.not(e), dt), bad)
      t92_k(w, p, Nat.add(k, 1n), y, inc_if_false(Bool.not(Bool.xor(df, d0)), b1))

def t92_y(+w: Nat, fuel: Nat, +y: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      t92_y(w, p, Nat.add(y, 1n), t92_k(w, w, 0n, y, bad))

def t92_wn(n: Nat, bad: U32) -> U32:
  +w = Dirtyn.dwin_width(n)
  t92_y(w, w, 0n, bad)

def t92_ns(fuel: Nat, +n: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      t92_ns(p, Nat.add(n, 1n), t92_wn(n, bad))

def t92_bad() -> U32:
  t92_ns(6n, 1n, 0)

def t93_y(+w: Nat, fuel: Nat, +y: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +up = Dirtyn.dwin_up(w, y)
      +down = Dirtyn.dwin_down(w, y)
      +m = Dirtyn.dwin_mark_wake_auto(w, Dirtyn.dwin_zero(w), y)
      +b0 = inc_if_false(Dirtyn.dwin_get(w, m, y), bad)
      +b1 = inc_if_false(Dirtyn.dwin_get(w, m, up), b0)
      t93_y(w, p, Nat.add(y, 1n), inc_if_false(Dirtyn.dwin_get(w, m, down), b1))

def t93_wn(n: Nat, bad: U32) -> U32:
  +w = Dirtyn.dwin_width(n)
  t93_y(w, w, 0n, bad)

def t93_ns(fuel: Nat, +n: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      t93_ns(p, Nat.add(n, 1n), t93_wn(n, bad))

def t93_bad() -> U32:
  t93_ns(6n, 1n, 0)

def t94_k(fuel: Nat, +k: Nat, +y: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +yu = U32.from_nat(y)
      +ku = U32.from_nat(k)
      +dq = Dirty.or_y(Dirty.zermask(), yu)
      +dw = Dirtyn.dwin_or_y(64n, Dirtyn.dwin_zero(64n), y)
      +a = Dirty.is_dirty_y(dq, ku)
      +b = Dirtyn.dwin_get(64n, dw, k)
      +b1 = inc_if_false(Bool.not(Bool.xor(a, b)), bad)
      +up = Nat.mod(Nat.add(y, 1n), 64n)
      +down = Nat.mod(Nat.add(y, 63n), 64n)
      +i = Grid.index(0, yu, 0)
      +aw = Dirty.is_dirty_y(Dirty.mark_wake(Dirty.zermask(), i), ku)
      +bw = Dirtyn.dwin_get(64n, Dirtyn.dwin_mark_wake(64n, Dirtyn.dwin_zero(64n), y, up, down), k)
      t94_k(p, Nat.add(k, 1n), y, inc_if_false(Bool.not(Bool.xor(aw, bw)), b1))

def t94_y(fuel: Nat, +y: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      t94_y(p, Nat.add(y, 1n), t94_k(64n, 0n, y, bad))

def t94_bad() -> U32:
  t94_y(64n, 0n, 0)

# T105 (SCALE.md step 5 / G-scale-2, wrap range): the n=6 (w=64) instance of
# `dwin_up_lt` / `dwin_down_lt`. Every wrap neighbour of every row is in range,
# and the topology is the mod-64 wrap (`up` = y+1, `down` = y-1: up(0)=1,
# up(63)=0, down(0)=63, down(63)=62). T93 witnessed the reach, this witnesses
# the range the lemma closes.
def t105_go(fuel: Nat, +y: Nat, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +u = Nat.is_lt(Dirtyn.dwin_up(64n, y), 64n)
      +d = Nat.is_lt(Dirtyn.dwin_down(64n, y), 64n)
      t105_go(p, Nat.add(y, 1n), inc_if_false(Bool.and(u, d), bad))

def t105_bad() -> U32:
  +b0 = t105_go(64n, 0n, 0)
  +b1 = inc_if_false(Nat.is_eq(Dirtyn.dwin_up(64n, 0n), 1n), b0)
  +b2 = inc_if_false(Nat.is_eq(Dirtyn.dwin_up(64n, 63n), 0n), b1)
  +b3 = inc_if_false(Nat.is_eq(Dirtyn.dwin_down(64n, 0n), 63n), b2)
  inc_if_false(Nat.is_eq(Dirtyn.dwin_down(64n, 63n), 62n), b3)

# T95-T96 (S1 step 3): assembly over an *explicit* resident set. T95: for the
# canonical window, `Store.assemble_keys (Window.resident_keys canonical)` is the
# same world as the implicit `Store.assemble` (the loop-bound set == the key
# list). T96: over the pure-gen store it reconstructs `Worldgen.build()` -- T18's
# property, now via the explicit key set, so the window's residency is exact.
def t95_bad() -> U32:
  +s1 = Store.build_all()
  +s2 = Store.build_all()
  list_cmp_go(U32.to_nat(262144), Grid.to_list(Store.assemble(s1)),
    Grid.to_list(Store.assemble_keys(Window.resident_keys(Window.canonical()), s2)), 0)

def t96_bad() -> U32:
  +s = Store.build_all()
  list_cmp_go(U32.to_nat(262144), Grid.to_list(Worldgen.build()),
    Grid.to_list(Store.assemble_keys(Window.resident_keys(Window.canonical()), s)), 0)

# T97-T98 (S1 step 4a, decision A): the generator selector. T97: the store's
# GTerrain regeneration reconstructs the shell-free reference terrain
# (`Worldgen.build_terrain`). T98: GBox and GTerrain actually differ -- the
# `(0,0,0)` corner is bedrock `2017` only in the reference mode, and an interior
# cell agrees -- so the selector changes what is generated.
def t97_bad() -> U32:
  s = Store.build_all_sel(Worldgen.terrain())
  a = Store.assemble_keys_sel(Worldgen.terrain(), Window.resident_keys(Window.canonical()), s)
  list_cmp_go(U32.to_nat(262144), Grid.to_list(Worldgen.build_terrain()), Grid.to_list(a), 0)

def t98_bad() -> U32:
  wb = Store.assemble(Store.build_all())
  wt = Store.assemble_sel(Worldgen.terrain(), Store.build_all_sel(Worldgen.terrain()))
  diff = list_cmp_go(U32.to_nat(262144), Grid.to_list(wb), Grid.to_list(wt), 0)
  inc_if_false(Bool.not(U32.is_eq(diff, 0)), 0)

# T99-T100 (S1 step 4b): window motion. T99: a one-chunk x-translation of the
# canonical window partitions its 64 resident chunks into 16 entering, 16
# leaving, 48 unchanged, and every entering chunk is in the new window and not
# the old. T100: `shift` is additive (two one-chunk shifts == one two-chunk).
def ulen(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}: 0
    case Con{h, t}: U32.add(1, ulen(t))

def ent_mem(fuel: Nat, keys: List<&2, U32>, +w: Window.Window, +w2: Window.Window, +bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      match keys:
        case Nil{}: bad
        case Con{+h, t}:
          +ok = Bool.and(Window.in_resident(w2, h), Bool.not(Window.in_resident(w, h)))
          ent_mem(p, t, w, w2, inc_if_false(ok, bad))

def t99_bad() -> U32:
  +w = Window.canonical()
  +w2 = Window.shift(w, 1, 0, 0)
  +ent = Window.entering(w, w2)
  +lea = Window.leaving(w, w2)
  b0 = inc_if_false(U32.is_eq(ulen(ent), 16), 0)
  b1 = inc_if_false(U32.is_eq(ulen(lea), 16), b0)
  ent_mem(64n, ent, w, w2, b1)

def t100_bad() -> U32:
  +w = Window.canonical()
  +a = Window.shift(Window.shift(w, 1, 0, 0), 1, 0, 0)
  +b = Window.shift(w, 2, 0, 0)
  b0 = inc_if_false(U32.is_eq(Window.base_x(a), Window.base_x(b)), 0)
  b1 = inc_if_false(U32.is_eq(Window.base_y(a), Window.base_y(b)), b0)
  inc_if_false(U32.is_eq(Window.base_z(a), Window.base_z(b)), b1)

# T101 (S1 step 4c): a *moved* window assembles into its own array. Translate the
# canonical window one chunk in x (base chunk 1, so global x spans 16..79) and
# check every window-local cell against `Worldgen.gen` at the recovered global
# coordinate (`win_gx/gy/gz`). `Grid.index` masks `&63`, which would fold the far
# edge (x>=64) onto the near cells, so this fails without the `win_index`
# addressing migration. `wgen_go` walks `i` descending and conses, so the list
# comes out in `Grid.to_list` order (index-ascending).
def wgen_go(fuel: Nat, +i: U32, +w: Window.Window, acc: List<U32>) -> List<U32>:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      +g = Worldgen.gen(
        Window.win_gx(w, i), Window.win_gy(w, i), Window.win_gz(w, i), 42)
      wgen_go(p, U32.sub(i, 1), w, g <> acc)

def t101_bad() -> U32:
  +w = Window.at(1, 0, 0)
  a = Store.assemble_w(w, Store.build_all())
  list_cmp_go(
    U32.to_nat(262144), wgen_go(U32.to_nat(262144), 262143, w, Nil{}), Grid.to_list(a), 0)

# T102-T104 (G-scale-7, `src/g7.bend`): witnesses around the proven canonical-
# window relabelling `win_canonical_index`. T81 sampled `win_index`==`Grid.index`
# for x,y,z = (i*7, i*13, i*29) & 63; T102 pins it at the box corners and edges,
# T103 exercises the two bit facts the proof rests on (`U32.sub x 0 == x` and
# `x & 63 == x` for x < 64), and T104 shows the range hypothesis is necessary:
# at global x = 64 the mask-free window map keeps 64 while `Grid.index` folds to
# 0, so a bare `forall x y z` statement would be false.
def t102_bad() -> U32:
  +w = Window.canonical()
  b0 = inc_if_false(U32.is_eq(Window.win_index(w, 0, 0, 0), Grid.index(0, 0, 0)), 0)
  b1 = inc_if_false(U32.is_eq(Window.win_index(w, 63, 63, 63), Grid.index(63, 63, 63)), b0)
  b2 = inc_if_false(U32.is_eq(Window.win_index(w, 63, 0, 0), Grid.index(63, 0, 0)), b1)
  b3 = inc_if_false(U32.is_eq(Window.win_index(w, 0, 63, 0), Grid.index(0, 63, 0)), b2)
  b4 = inc_if_false(U32.is_eq(Window.win_index(w, 0, 0, 63), Grid.index(0, 0, 63)), b3)
  b5 = inc_if_false(U32.is_eq(Window.win_index(w, 62, 1, 17), Grid.index(62, 1, 17)), b4)
  inc_if_false(U32.is_eq(Window.win_index(w, 5, 40, 33), Grid.index(5, 40, 33)), b5)

def g7_sub_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +x = U32.mul(i, 2654435761)
      g7_sub_go(p, U32.add(i, 1), inc_if_false(U32.is_eq(U32.sub(x, 0), x), bad))

def g7_mask_go(fuel: Nat, +i: U32, +bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      g7_mask_go(p, U32.add(i, 1), inc_if_false(U32.is_eq(U32.and(i, 63), i), bad))

def t103_bad() -> U32:
  b0 = g7_sub_go(U32.to_nat(256), 0, 0)
  g7_mask_go(U32.to_nat(64), 0, b0)

def t104_bad() -> U32:
  +w = Window.canonical()
  +l = Window.win_index(w, 64, 0, 0)
  +r = Grid.index(64, 0, 0)
  b0 = inc_if_false(U32.is_eq(l, 64), 0)
  b1 = inc_if_false(U32.is_eq(r, 0), b0)
  inc_if_false(U32.is_ne(l, r), b1)

# T106-T107 (S1 / G-scale-8, window-edge shell, `src/winshell.bend`): the *box*
# contributes the shell at the window's own edge. T106: the canonical shelled
# sampler reproduces `Worldgen.gen` at corners, edges, and interior (the
# `win_gen_canonical` law instance). T107: a *moved* window's shell is
# window-local -- cell global `x = 16` is the moved window's own `x = 0` face, so
# it is bedrock even though it is interior to the fixed box (`gen` = terrain).
def t106_bad() -> U32:
  +w = Window.canonical()
  +b0 = inc_if_false(U32.is_eq(Winshell.gen_at(w, 0, 0, 0, 42), Worldgen.gen(0, 0, 0, 42)), 0)
  +b1 = inc_if_false(U32.is_eq(Winshell.gen_at(w, 63, 30, 10, 42), Worldgen.gen(63, 30, 10, 42)), b0)
  +b2 = inc_if_false(U32.is_eq(Winshell.gen_at(w, 20, 63, 20, 42), Worldgen.gen(20, 63, 20, 42)), b1)
  inc_if_false(U32.is_eq(Winshell.gen_at(w, 30, 20, 12, 42), Worldgen.gen(30, 20, 12, 42)), b2)

def t107_bad() -> U32:
  # window at chunk 1 -> cell origin 16; global x = 16 is its local x = 0 face.
  +w = Window.at(1, 0, 0)
  +shell = Winshell.gen_at(w, 16, 30, 30, 42)
  +inside = Winshell.gen_at(w, 17, 30, 30, 42)
  +box = Worldgen.gen(16, 30, 30, 42)
  +terr = Worldgen.gen_terrain(17, 30, 30, 42)
  +bedrock = Cell.encode(Cell.bedrock(), 63, 0, 0, 0)
  +b0 = inc_if_false(U32.is_eq(shell, bedrock), 0)
  +b1 = inc_if_false(Bool.not(U32.is_eq(shell, box)), b0)
  inc_if_false(U32.is_eq(inside, terr), b1)

# T108-T109 (S1 / G-scale-2 item 3, `src/maskword.bend`): the U32 <-> Word
# bit-test core. T108: `u32_word_bit` sampled over 32 shift positions on varied
# U32s -- the live bit test equals `dwin_get` on the word payload. T109: the
# `mask_word` concatenation places `lo` in bits 0..31 and `hi` in 32..63.
def t108_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +a = U32.mul(i, 2654435761)
      +k = U32.to_nat(i)
      +l = U32.is_ne(U32.and(a, U32.shln(1, k)), 0)
      +r = Dirtyn.dwin_get(32n, Maskword.u32_word(a), k)
      t108_go(p, U32.add(i, 1), inc_if_false(Bool.not(Bool.xor(l, r)), bad))

def t108_bad() -> U32:
  t108_go(32n, 0, 0)

def t109_bad() -> U32:
  +lo_bit0 = Dirty.or_y(Dirty.zermask(), 0)
  +hi_bit0 = Dirty.or_y(Dirty.zermask(), 32)
  +b0 = inc_if_false(Dirtyn.dwin_get(64n, Maskword.mask_word(lo_bit0), 0n), 0)
  +b1 = inc_if_false(Bool.not(Dirtyn.dwin_get(64n, Maskword.mask_word(lo_bit0), 32n)), b0)
  +b2 = inc_if_false(Dirtyn.dwin_get(64n, Maskword.mask_word(hi_bit0), 32n), b1)
  inc_if_false(Bool.not(Dirtyn.dwin_get(64n, Maskword.mask_word(hi_bit0), 0n)), b2)

# T120-T121 (S1 / G-scale-8, store load/evict policy): `Store.window_store`
# rebuilds the store onto a window's resident set (keep overlap, load entering
# from `gen`, drop leaving). T120: a one-chunk x-move of the canonical window,
# then `assemble_w` over the windowed store, reconstructs `gen` on all 262144
# cells (the entering chunk was loaded, the overlap kept). T121: the leaving
# chunk (0,0,0) is gone and the entering chunk (4,0,0) is present.
def is_none_m(m: Maybe<&2, List<&2, U32>>) -> U32:
  match m:
    case None{}: 0
    case Some{cells}: 1

def t120_bad() -> U32:
  +w2 = Window.shift(Window.canonical(), 1, 0, 0)
  +s = Store.window_store(w2, Store.build_all())
  a = Store.assemble_w(w2, s)
  list_cmp_go(U32.to_nat(262144), wgen_go(U32.to_nat(262144), 262143, w2, Nil{}), Grid.to_list(a), 0)

def t121_bad() -> U32:
  +w2 = Window.shift(Window.canonical(), 1, 0, 0)
  +s = Store.window_store(w2, Store.build_all())
  b0 = inc_if_false(U32.is_eq(is_none_m(Store.get(s, Chunk.key(0, 0, 0))), 0), 0)
  inc_if_false(U32.is_eq(is_none_m(Store.get(s, Chunk.key(4, 0, 0))), 1), b0)
# T110-T117 (S1 / G-scale-2 item 3, `src/wordnat.bend`): the U32 <-> Nat index
# value theory. T110 `to_nat(from_nat k) = k`; T111 `is_lt(y,32) = to_nat y < 32`;
# T112 `to_nat(and(y,31))` low/high split; T113 the bit-5 decomposition of
# `to_nat y`; T114/T115 the headline `mask_word_get` sampled over all 64 rows for
# two masks (sparse + edge bits); T116 `from_nat(to_nat a) = a`; T117 the 64-bound
# and the `Maskword` mask bounds.
def t110_go(fuel: Nat, +k: Nat, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +l = U32.to_nat(U32.from_nat(k))
      t110_go(p, Nat.add(k, 1n), inc_if_false(Nat.is_eq(l, k), bad))

def t110_bad() -> U32:
  t110_go(64n, 0n, 0)

def t111_go(fuel: Nat, +y: U32, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +l = U32.is_lt(y, 32)
      +r = Nat.is_lt(U32.to_nat(y), 32n)
      t111_go(p, U32.add(y, 1), inc_if_false(Bool.not(Bool.xor(l, r)), bad))

def t111_bad() -> U32:
  t111_go(64n, 0, 0)

def t112_go(fuel: Nat, +y: U32, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +l = U32.to_nat(U32.and(y, 31))
      +r = Bool.pick(Nat, U32.is_lt(y, 32), U32.to_nat(y), Nat.sub(U32.to_nat(y), 32n))
      t112_go(p, U32.add(y, 1), inc_if_false(Nat.is_eq(l, r), bad))

def t112_bad() -> U32:
  t112_go(64n, 0, 0)

def t113_go(fuel: Nat, +y: U32, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +l = U32.to_nat(y)
      +r = Nat.add(U32.to_nat(U32.and(y, 31)), Bool.pick(Nat, U32.is_lt(y, 32), 0n, 32n))
      t113_go(p, U32.add(y, 1), inc_if_false(Nat.is_eq(l, r), bad))

def t113_bad() -> U32:
  t113_go(64n, 0, 0)

def t114_go(fuel: Nat, +y: U32, +m: Dirty.Mask, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +l = Dirty.is_dirty_y(m, y)
      +r = Dirtyn.dwin_get(64n, Maskword.mask_word(m), U32.to_nat(y))
      t114_go(p, U32.add(y, 1), m, inc_if_false(Bool.not(Bool.xor(l, r)), bad))

def t114_bad() -> U32:
  +m = Dirty.or_y(Dirty.or_y(Dirty.or_y(Dirty.zermask(), 3), 20), 45)
  t114_go(64n, 0, m, 0)

def t115_bad() -> U32:
  +m = Dirty.or_y(Dirty.or_y(Dirty.or_y(Dirty.or_y(Dirty.zermask(), 0), 31), 32), 63)
  t114_go(64n, 0, m, 0)

def t116_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +a = U32.mul(i, 2654435761)
      +l = U32.from_nat(U32.to_nat(a))
      t116_go(p, U32.add(i, 1), inc_if_false(U32.is_eq(l, a), bad))

def t116_bad() -> U32:
  t116_go(64n, 0, 0)

def t117_go(fuel: Nat, +y: U32, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +b0 = inc_if_false(Bool.not(Bool.xor(U32.is_lt(y, 64), Nat.is_lt(U32.to_nat(y), 64n))), bad)
      +b1 = inc_if_false(Nat.is_lt(U32.to_nat(U32.and(y, 31)), 32n), b0)
      +b2 = inc_if_false(Nat.is_lt(U32.to_nat(U32.and(y, 63)), 64n), b1)
      t117_go(p, U32.add(y, 1), b2)

def t117_bad() -> U32:
  t117_go(64n, 0, 0)

# T122-T125 (S1 endgame, slice W1, `src/wgrid.bend`): the window-local coordinate
# seam. T122: `wgrid_index` on the canonical window equals `Grid.index` (the seam
# is a canonical relabelling). T123: `wgrid_neighbor` on the canonical window
# equals `Grid.neighbor` over a swept index set and eight directions (including
# the face folds). T124: `wgrid_step_inside` equals `Grid.step_inside`, including
# the inert face steps that keep the box closed. T125: a *moved* window keeps its
# global coordinates -- `wgrid_index`/`wgrid_ix` do not torus-fold, so they
# genuinely differ from `Grid` off the canonical box (this is what W2 builds on).
def t122_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +w = Window.canonical()
      +x = U32.and(i, 63)
      +y = U32.and(U32.mul(i, 7), 63)
      +z = U32.and(U32.mul(i, 13), 63)
      t122_go(p, U32.add(i, 1), inc_if_false(U32.is_eq(WGrid.wgrid_index(w, x, y, z), Grid.index(x, y, z)), bad))

def t122_bad() -> U32:
  t122_go(U32.to_nat(256), 0, 0)

def wgn_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +w = Window.canonical()
      +b0 = inc_if_false(U32.is_eq(WGrid.wgrid_neighbor(w, i, 1, 0, 0), Grid.neighbor(i, 1, 0, 0)), bad)
      +b1 = inc_if_false(U32.is_eq(WGrid.wgrid_neighbor(w, i, 4294967295, 0, 0), Grid.neighbor(i, 4294967295, 0, 0)), b0)
      +b2 = inc_if_false(U32.is_eq(WGrid.wgrid_neighbor(w, i, 0, 1, 0), Grid.neighbor(i, 0, 1, 0)), b1)
      +b3 = inc_if_false(U32.is_eq(WGrid.wgrid_neighbor(w, i, 0, 4294967295, 0), Grid.neighbor(i, 0, 4294967295, 0)), b2)
      +b4 = inc_if_false(U32.is_eq(WGrid.wgrid_neighbor(w, i, 0, 0, 1), Grid.neighbor(i, 0, 0, 1)), b3)
      +b5 = inc_if_false(U32.is_eq(WGrid.wgrid_neighbor(w, i, 0, 0, 4294967295), Grid.neighbor(i, 0, 0, 4294967295)), b4)
      +b6 = inc_if_false(U32.is_eq(WGrid.wgrid_neighbor(w, i, 4294967295, 4294967295, 0), Grid.neighbor(i, 4294967295, 4294967295, 0)), b5)
      +b7 = inc_if_false(U32.is_eq(WGrid.wgrid_neighbor(w, i, 1, 4294967295, 1), Grid.neighbor(i, 1, 4294967295, 1)), b6)
      wgn_go(p, U32.add(i, 1), b7)

def t123_bad() -> U32:
  b0 = wgn_go(U32.to_nat(300), 0, 0)
  wgn_go(U32.to_nat(300), U32.sub(262144, 300), b0)

def wgs_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n: bad
    case 1n+p:
      +w = Window.canonical()
      +b0 = inc_if_false(U32.is_eq(Bool.to_u32(WGrid.wgrid_step_inside(w, i, 0, 4294967295, 0)), Bool.to_u32(Grid.step_inside(i, 0, 4294967295, 0))), bad)
      +b1 = inc_if_false(U32.is_eq(Bool.to_u32(WGrid.wgrid_step_inside(w, i, 0, 1, 0)), Bool.to_u32(Grid.step_inside(i, 0, 1, 0))), b0)
      +b2 = inc_if_false(U32.is_eq(Bool.to_u32(WGrid.wgrid_step_inside(w, i, 4294967295, 0, 0)), Bool.to_u32(Grid.step_inside(i, 4294967295, 0, 0))), b1)
      +b3 = inc_if_false(U32.is_eq(Bool.to_u32(WGrid.wgrid_step_inside(w, i, 0, 0, 1)), Bool.to_u32(Grid.step_inside(i, 0, 0, 1))), b2)
      +b4 = inc_if_false(U32.is_eq(Bool.to_u32(WGrid.wgrid_step_inside(w, i, 0, 0, 4294967295)), Bool.to_u32(Grid.step_inside(i, 0, 0, 4294967295))), b3)
      +b5 = inc_if_false(U32.is_eq(Bool.to_u32(WGrid.wgrid_step_inside(w, i, 1000, 0, 0)), Bool.to_u32(Grid.step_inside(i, 1000, 0, 0))), b4)
      wgs_go(p, U32.add(i, 1), b5)

def t124_bad() -> U32:
  b0 = wgs_go(U32.to_nat(300), 0, 0)
  wgs_go(U32.to_nat(300), U32.sub(262144, 300), b0)

def t125_bad() -> U32:
  # window at chunk x=12 -> cell origin 192; global x=200 is its local x=8.
  +w = Window.at(12, 0, 0)
  +idx = WGrid.wgrid_index(w, 200, 5, 7)
  +exp = (8 .|. (7 << 6n) .|. (5 << 12n) : U32)
  +folded = Grid.index(200, 5, 7)
  +b0 = inc_if_false(U32.is_eq(idx, exp), 0)
  # the window inverse recovers the *global* x = 200; `Grid` would report 8.
  +b1 = inc_if_false(U32.is_eq(WGrid.wgrid_ix(w, idx), 200), b0)
  +b2 = inc_if_false(U32.is_eq(Grid.ix(folded), 8), b1)
  inc_if_false(U32.is_ne(WGrid.wgrid_ix(w, idx), Grid.ix(folded)), b2)


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
    report("T57 cw chunk key roundtrip", t57_bad())
    report("T58 cw local index roundtrip", t58_bad())
    report("T59 cw global split/rejoin roundtrip", t59_bad())
    report("T60 cw no torus mask (global 200 preserved)", t60_bad())
    report("T61 serve framing encode/decode", t61_bad())
    report("T62 serve HELLO + CREDIT/REQUEST/STOP", t62_bad())
    report("T63 serve dense first snapshot == export body", t63_bad())
    report("T64 serve sparse snapshot + assemble recovery", t64_bad())
    report("T65 serve delta B2 (visible fields, global idx)", t65_bad())
    report("T66 gscale cw x roundtrip (in range)", t66_bad())
    report("T67 gscale cw y roundtrip (in range)", t67_bad())
    report("T68 gscale cw z roundtrip (in range)", t68_bad())
    report("T69 gscale cw key masked roundtrip", t69_bad())
    report("T70 gscale cw local masked roundtrip", t70_bad())
    report("T71 gscale cw y roundtrip (full 3-coord)", t71_bad())
    report("T72 gscale cw z roundtrip (full 3-coord)", t72_bad())
    report("T73 winset mem/insert/remove", t73_bad())
    report("T74 winset evict drops regenerable residents", t74_bad())
    report("T75 winset gen cell + assemble/evict roundtrip", t75_bad())
    report("T76 bridge3 credit window (no overrun)", t76_bad())
    report("T77 bridge3 bounded queue + coalesce count", t77_bad())
    report("T78 bridge3 drop-and-keyframe coalescing", t78_bad())
    report("T79 bridge3 idle PING policy", t79_bad())
    report("T80 bridge3 flow scenario + framing", t80_bad())
    report("T81 window canonical index == Grid.index", t81_bad())
    report("T82 window no torus mask (global 80 not folded)", t82_bad())
    report("T83 dense record offset maps to true chunk cell (G-bridge-2)", t83_bad())
    report("T84 dense record order == Store.chunk_list (G-bridge-2 s10)", t84_bad())
    report("T85 terrain .bgt size + count", t85_bad())
    report("T86 golden terrain vectors (interior/shell/out-of-box)", t86_bad())
    report("T87 gen != gen_terrain on shell planes", t87_bad())
    report("T88 gen == gen_terrain shell-free (incl. out-of-box)", t88_bad())
    report("T89 terrain sample coverage (no bedrock, out-of-box, shell)", t89_bad())
    report("T90 dirtyn zero mask has no dirty row", t90_bad())
    report("T91 dirtyn or_y marks exactly its row", t91_bad())
    report("T92 dirtyn mark_if true/false", t92_bad())
    report("T93 dirtyn mark_wake y-1/y/y+1 reach", t93_bad())
    report("T94 dirtyn n=6 agrees with Dirty (or_y + mark_wake)", t94_bad())
    report("T105 dirtyn wrap in range at n=6 (+ wrap topology)", t105_bad())
    report("T95 explicit resident set == implicit assemble (S1 step 3)", t95_bad())
    report("T96 explicit resident set reconstructs worldgen (S1 step 3)", t96_bad())
    report("T97 GTerrain selector reconstructs shell-free terrain (S1 step 4a)", t97_bad())
    report("T98 GBox vs GTerrain differ on the shell (decision A)", t98_bad())
    report("T99 window one-chunk x-move: 16 enter / 16 leave (S1 step 4b)", t99_bad())
    report("T100 window shift is additive (S1 step 4b)", t100_bad())
    report("T101 moved window assembles its own array (S1 step 4c)", t101_bad())
    report("T102 window relabel at box corners/edges (G-scale-7)", t102_bad())
    report("T103 window relabel bit facts: sub0 + mask6 (G-scale-7)", t103_bad())
    report("T104 window relabel range hypothesis necessary (G-scale-7)", t104_bad())
    report("T106 window-edge shell reproduces gen at canonical (G-scale-8)", t106_bad())
    report("T107 moved-window shell is window-local (G-scale-8)", t107_bad())
    report("T108 U32 bit test == word dwin_get (G-scale-2 core)", t108_bad())
    report("T109 mask_word places lo/hi halves (G-scale-2 core)", t109_bad())
    report("T120 window_store->assemble reconstructs gen (G-scale-8 load)", t120_bad())
    report("T121 window_store evicts leaving, loads entering (G-scale-8)", t121_bad())
    report("T110 to_nat(from_nat k) = k (G-scale-2 index bridge)", t110_bad())
    report("T111 is_lt(y,32) = to_nat y < 32 (G-scale-2 index bridge)", t111_bad())
    report("T112 to_nat(and(y,31)) low/high split (G-scale-2)", t112_bad())
    report("T113 bit-5 decomposition of to_nat y (G-scale-2)", t113_bad())
    report("T114 mask_word_get over all 64 rows, sparse mask (G-scale-2)", t114_bad())
    report("T115 mask_word_get over all 64 rows, edge mask (G-scale-2)", t115_bad())
    report("T116 from_nat(to_nat a) = a (G-scale-2 index bridge)", t116_bad())
    report("T117 64-bound + and(31)/and(63) ranges (G-scale-2)", t117_bad())
    report("T122 wgrid canonical index == Grid.index (W1 seam)", t122_bad())
    report("T123 wgrid canonical neighbor == Grid.neighbor (W1 seam)", t123_bad())
    report("T124 wgrid canonical step_inside == Grid.step_inside (W1 seam)", t124_bad())
    report("T125 moved window keeps global coord, no torus fold (W1 seam)", t125_bad())
