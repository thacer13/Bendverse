import Base
import ./grid.bend as Grid
import ./cell.bend as Cell
import ./chunk.bend as Chunk
import ./worldgen.bend as Worldgen
import ./window.bend as Window

type Store is Data:
  STip{}
  SLeaf{key: U32, val: List<&2, U32>}
  SNode{lo: Store, hi: Store}

def empty() -> Store:
  STip{}

def relist(xs: List<U32>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      h <> relist(t)

def chunk_list_sel(sel: Bool, k: U32) -> List<&2, U32>:
  relist(Grid.to_list(Chunk.build_sel(sel, k)))

def chunk_list(k: U32) -> List<&2, U32>:
  chunk_list_sel(Worldgen.box(), k)

def maybe_if(b: Bool, val: List<&2, U32>) -> Maybe<&2, List<&2, U32>>:
  match b:
    case False{}:
      None{}
    case True{}:
      Some{val}

def set_w(n: Nat, w: Word(n), s: Store, +k: U32, v: List<&2, U32>) -> Store:
  match n:
    case 0n:
      SLeaf{k, v}
    case 1n+p:
      match w:
        case WCon{head, tail}:
          match head:
            case False{}:
              match s:
                case STip{}:
                  SNode{set_w(p, tail, STip{}, k, v), STip{}}
                case SLeaf{key, val}:
                  SLeaf{k, v}
                case SNode{lo, hi}:
                  SNode{set_w(p, tail, lo, k, v), hi}
            case True{}:
              match s:
                case STip{}:
                  SNode{STip{}, set_w(p, tail, STip{}, k, v)}
                case SLeaf{key, val}:
                  SLeaf{k, v}
                case SNode{lo, hi}:
                  SNode{lo, set_w(p, tail, hi, k, v)}

def set(s: Store, +k: U32, v: List<&2, U32>) -> Store:
  match k:
    case U32{w}:
      set_w(32n, w, s, k, v)

def get_w(n: Nat, w: Word(n), s: Store, +k: U32) -> Maybe<&2, List<&2, U32>>:
  match n:
    case 0n:
      match s:
        case STip{}:
          None{}
        case SLeaf{key, val}:
          maybe_if(U32.is_eq(key, k), val)
        case SNode{lo, hi}:
          None{}
    case 1n+p:
      match w:
        case WCon{head, tail}:
          match head:
            case False{}:
              match s:
                case STip{}:
                  None{}
                case SLeaf{key, val}:
                  None{}
                case SNode{lo, hi}:
                  get_w(p, tail, lo, k)
            case True{}:
              match s:
                case STip{}:
                  None{}
                case SLeaf{key, val}:
                  None{}
                case SNode{lo, hi}:
                  get_w(p, tail, hi, k)

def get(s: Store, +k: U32) -> Maybe<&2, List<&2, U32>>:
  match k:
    case U32{w}:
      get_w(32n, w, s, k)

# S1 step 4c: the assemble chain is window-aware. `assemble_chunk_w` addresses a
# cell by its window-local flat index via `Window.win_index`, which is torus-free
# (no `&63`), so a chunk based away from the origin lands at its own window-local
# slot instead of aliasing the far edge onto the near cells. The originals are
# wrappers over `Window.canonical()`; for the canonical window `win_index` is
# bit-identical to `Grid.index` (T81), so T18/T95/T96 stay green. `assemble_w`
# (below, over `Window.resident_keys`) is what a moved window uses.
def assemble_chunk_w(
  fuel: Nat, +w: Window.Window, +i: U32, +k: U32, cells: List<&2, U32>, world: Array<U32>
) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      match cells:
        case Nil{}:
          world
        case Con{h, t}:
          +idx = Window.win_index(
            w, Chunk.global_x(k, i), Chunk.global_y(k, i), Chunk.global_z(k, i))
          assemble_chunk_w(p, w, U32.add(i, 1), k, t, world[idx] <- h)

def assemble_chunk(fuel: Nat, +i: U32, +k: U32, cells: List<&2, U32>, world: Array<U32>) -> Array<U32>:
  assemble_chunk_w(fuel, Window.canonical(), i, k, cells, world)

def assemble_cells_w_sel(
  +sel: Bool, +w: Window.Window, m: Maybe<&2, List<&2, U32>>, +k: U32, world: Array<U32>
) -> Array<U32>:
  match m:
    case None{}:
      # A missing (evicted) chunk is regenerated from the selected generator
      # (reference shell or shell-free terrain): the store is a sparse overlay
      # on the coordinate-indexed worldgen (rule 11).
      assemble_chunk_w(U32.to_nat(Chunk.cells()), w, 0, k, chunk_list_sel(sel, k), world)
    case Some{cells}:
      assemble_chunk_w(U32.to_nat(Chunk.cells()), w, 0, k, cells, world)

def assemble_cells_sel(+sel: Bool, m: Maybe<&2, List<&2, U32>>, +k: U32, world: Array<U32>) -> Array<U32>:
  assemble_cells_w_sel(sel, Window.canonical(), m, k, world)

def assemble_cells(m: Maybe<&2, List<&2, U32>>, +k: U32, world: Array<U32>) -> Array<U32>:
  assemble_cells_sel(Worldgen.box(), m, k, world)

def assemble_go_sel(+sel: Bool, fuel: Nat, +ci: U32, +s: Store, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      +k = Chunk.key(U32.and(ci, 3), U32.and(U32.shrn(ci, 2n), 3), U32.and(U32.shrn(ci, 4n), 3))
      assemble_go_sel(sel, p, U32.add(ci, 1), s, assemble_cells_sel(sel, get(s, k), k, world))

def assemble_go(fuel: Nat, +ci: U32, +s: Store, world: Array<U32>) -> Array<U32>:
  assemble_go_sel(Worldgen.box(), fuel, ci, s, world)

def assemble_sel(+sel: Bool, s: Store) -> Array<U32>:
  assemble_go_sel(sel, 64n, 0, s, [0 : U32^18n])

def assemble(s: Store) -> Array<U32>:
  assemble_sel(Worldgen.box(), s)

# S1 step 3: assemble over an *explicit* resident key list (a window's set)
# instead of the implicit `assemble_go` loop bounds. Chunks are disjoint, so the
# order of `keys` does not affect the result; `assemble s` is the canonical
# instance (`Window.resident_keys canonical()`), which T95 checks.
def assemble_keys_go_w_sel(
  +sel: Bool, +w: Window.Window, fuel: Nat, keys: List<&2, U32>, +s: Store, world: Array<U32>
) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      match keys:
        case Nil{}:
          world
        case Con{+h, t}:
          assemble_keys_go_w_sel(
            sel, w, p, t, s, assemble_cells_w_sel(sel, w, get(s, h), h, world))

def assemble_keys_go_sel(+sel: Bool, fuel: Nat, keys: List<&2, U32>, +s: Store, world: Array<U32>) -> Array<U32>:
  assemble_keys_go_w_sel(sel, Window.canonical(), fuel, keys, s, world)

def assemble_keys_w_sel(+sel: Bool, +w: Window.Window, keys: List<&2, U32>, s: Store) -> Array<U32>:
  assemble_keys_go_w_sel(sel, w, 64n, keys, s, [0 : U32^18n])

def assemble_keys_sel(+sel: Bool, keys: List<&2, U32>, s: Store) -> Array<U32>:
  assemble_keys_w_sel(sel, Window.canonical(), keys, s)

def assemble_keys_w(w: Window.Window, keys: List<&2, U32>, s: Store) -> Array<U32>:
  assemble_keys_w_sel(Worldgen.box(), w, keys, s)

def assemble_keys(keys: List<&2, U32>, s: Store) -> Array<U32>:
  assemble_keys_w(Window.canonical(), keys, s)

# S1 step 4c: assemble a *moved* window into its own window-local array over its
# explicit resident set. The canonical instance is `assemble` (T18/T95); a moved
# window addresses by `win_index`, so its far-edge chunks do not fold onto the
# near cells. T101 witnesses the moved case against `Worldgen.gen`.
def assemble_w_sel(+sel: Bool, +w: Window.Window, s: Store) -> Array<U32>:
  assemble_keys_w_sel(sel, w, Window.resident_keys(w), s)

def assemble_w(w: Window.Window, s: Store) -> Array<U32>:
  assemble_w_sel(Worldgen.box(), w, s)

def put_all_go_sel(+sel: Bool, fuel: Nat, +ci: U32, store: Store) -> Store:
  match fuel:
    case 0n:
      store
    case 1n+p:
      +k = Chunk.key(U32.and(ci, 3), U32.and(U32.shrn(ci, 2n), 3), U32.and(U32.shrn(ci, 4n), 3))
      put_all_go_sel(sel, p, U32.add(ci, 1), set(store, k, chunk_list_sel(sel, k)))

def build_all_sel(+sel: Bool) -> Store:
  put_all_go_sel(sel, 64n, 0, STip{})

def build_all() -> Store:
  build_all_sel(Worldgen.box())

# ------------------------------------------------------------------ eviction
# Eviction works on the store, where each chunk is a reusable `Data` list, so a
# chunk's cells can be inspected without consuming the store. A chunk is
# *sleeping* when none of its cells is active (rule 9); a sleeping chunk is
# *regenerable* when it is bit-equal to its pure gen. A regenerable chunk is
# dropped, and `assemble` rebuilds it exactly from worldgen — lossless eviction.

# sleeping_cells: no cell in the list carries the active bit.
def sleeping_cells(fuel: Nat, cells: List<&2, U32>, act: Bool) -> Bool:
  match fuel:
    case 0n:
      Bool.not(act)
    case 1n+p:
      match cells:
        case Nil{}:
          Bool.not(act)
        case Con{h, t}:
          +a2 = Bool.or(act, U32.is_ne(Cell.active(h), 0))
          sleeping_cells(p, t, a2)

# gen_eq_cells: the stored list is bit-equal to the pure gen list (both in local
# order, as produced by `chunk_list`).
def gen_eq_cells(fuel: Nat, cells: List<&2, U32>, gen: List<&2, U32>, eq: Bool) -> Bool:
  match fuel:
    case 0n:
      eq
    case 1n+p:
      match cells gen:
        case Nil{} Nil{}:
          eq
        case Nil{} Con{hy, ty}:
          False{}
        case Con{hx, tx} Nil{}:
          False{}
        case Con{hx, tx} Con{hy, ty}:
          +e2 = Bool.and(eq, U32.is_eq(hx, hy))
          gen_eq_cells(p, tx, ty, e2)

# keep_cells: a regenerable chunk is dropped; any other chunk keeps its cells.
def keep_cells(store: Store, +k: U32, cells: List<&2, U32>, +drop: Bool) -> Store:
  match drop:
    case True{}:
      store
    case False{}:
      set(store, k, cells)

# evict_key walks the 64 chunk keys. `m` is the store's entry at key k; `s` is
# the source store (reused for `get`), and `acc` accumulates the residents.
def evict_key_sel(
  +sel: Bool, fuel: Nat, m: Maybe<&2, List<&2, U32>>, +ci: U32, +s: Store, acc: Store, +k: U32
) -> Store:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      match m:
        case None{}:
          +ni = U32.add(ci, 1)
          +nk = Chunk.key(U32.and(ni, 3), U32.and(U32.shrn(ni, 2n), 3), U32.and(U32.shrn(ni, 4n), 3))
          evict_key_sel(sel, p, get(s, nk), ni, s, acc, nk)
        case Some{+cells}:
          +sl = sleeping_cells(U32.to_nat(Chunk.cells()), cells, False{})
          +ge = gen_eq_cells(U32.to_nat(Chunk.cells()), cells, chunk_list_sel(sel, k), True{})
          +drop = Bool.and(sl, ge)
          +ni = U32.add(ci, 1)
          +nk = Chunk.key(U32.and(ni, 3), U32.and(U32.shrn(ni, 2n), 3), U32.and(U32.shrn(ni, 4n), 3))
          evict_key_sel(sel, p, get(s, nk), ni, s, keep_cells(acc, k, cells, drop), nk)

def evict_sel(+sel: Bool, +s: Store) -> Store:
  +k0 = Chunk.key(0, 0, 0)
  evict_key_sel(sel, U32.to_nat(64), get(s, k0), 0, s, STip{}, k0)

# `evict` drops every sleeping, gen-equal chunk; the result assembles to the
# same world as the input because `assemble` regenerates dropped chunks.
def evict(+s: Store) -> Store:
  evict_sel(Worldgen.box(), s)

# ------------------------------------------------------------------ window store
# S1 / G-scale-8: the window **load/evict policy** on the store. `window_store w s`
# rebuilds `s` onto exactly `w`'s resident keys: a chunk present in `s` is kept
# (overlap), a missing one is loaded from the selected generator (entering), and
# every chunk not resident in `w` is dropped (leaving). It is the store the
# window's array is assembled from (`Store.assemble_w`); the leaving chunks are
# evicted implicitly by rebuilding rather than by an in-place remove (the store
# trie has no delete). Reading a resident chunk never touches `gen`.
def cells_or_gen_sel(+sel: Bool, m: Maybe<&2, List<&2, U32>>, +k: U32) -> List<&2, U32>:
  match m:
    case None{}:
      chunk_list_sel(sel, k)
    case Some{+cells}:
      cells

def load_keys_go_sel(+sel: Bool, fuel: Nat, keys: List<&2, U32>, +s: Store, acc: Store) -> Store:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      match keys:
        case Nil{}:
          acc
        case Con{+h, t}:
          load_keys_go_sel(sel, p, t, s, set(acc, h, cells_or_gen_sel(sel, get(s, h), h)))

def window_store_sel(+sel: Bool, w: Window.Window, s: Store) -> Store:
  load_keys_go_sel(sel, 64n, Window.resident_keys(w), s, STip{})

def window_store(w: Window.Window, s: Store) -> Store:
  window_store_sel(Worldgen.box(), w, s)

# ------------------------------------------------------------------ lossless move
# `window_store` rebuilds from `STip{}` over the new resident keys, so it drops
# *every* chunk that is not resident in `w2` — including a MODIFIED
# (non-gen-equal) chunk that is merely leaving the window. That is lossy: a
# settled pile carried by the leaving chunk is erased, so moving the window back
# regenerates bare `gen` instead of restoring the pile. The lossless policy
# instead walks the whole trie (`move_prune_sel`) and drops a chunk only when it
# is
#
#   * *leaving* (`Window.in_resident w1` and not `Window.in_resident w2`), and
#   * *regenerable*: sleeping (`sleeping_cells`) AND bit-equal to its pure gen
#     (`gen_eq_cells`),
#
# exactly the `Store.evict` criterion but restricted to the leaving slab. Every
# other chunk is kept, so a non-gen-equal chunk is never dropped. `move_store`
# then loads/keeps `w2`'s resident keys from the pruned store (`load_keys_go_sel`
# with the survivors as both source and accumulator): the overlap is preserved,
# an entering chunk comes from the selected generator, and the survivors that
# are not resident in `w2` stay in the store (so the world overlay is intact).
# This is the store-level half of the moving-window driver; `assemble_w` only
# reads resident keys, so the extra survivors are transparent to the window.
def leaving_regen_sel(
  +sel: Bool, +w1: Window.Window, +w2: Window.Window, +k: U32, +cells: List<&2, U32>
) -> Bool:
  +leaving = Bool.and(Window.in_resident(w1, k), Bool.not(Window.in_resident(w2, k)))
  +sleeping = sleeping_cells(U32.to_nat(Chunk.cells()), cells, False{})
  +gen_eq = gen_eq_cells(U32.to_nat(Chunk.cells()), cells, chunk_list_sel(sel, k), True{})
  Bool.and(leaving, Bool.and(sleeping, gen_eq))

def move_prune_sel(+sel: Bool, +w1: Window.Window, +w2: Window.Window, s: Store, acc: Store) -> Store:
  match s:
    case STip{}:
      acc
    case SLeaf{+key, +val}:
      keep_cells(acc, key, val, leaving_regen_sel(sel, w1, w2, key, val))
    case SNode{lo, hi}:
      move_prune_sel(sel, w1, w2, hi, move_prune_sel(sel, w1, w2, lo, acc))

def move_store_sel(+sel: Bool, w1: Window.Window, +w2: Window.Window, s: Store) -> Store:
  +survivors = move_prune_sel(sel, w1, w2, s, STip{})
  load_keys_go_sel(sel, 64n, Window.resident_keys(w2), survivors, survivors)

def move_store(w1: Window.Window, w2: Window.Window, s: Store) -> Store:
  move_store_sel(Worldgen.box(), w1, w2, s)
