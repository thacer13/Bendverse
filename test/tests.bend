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
import ../src/tick.bend as Tick

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
