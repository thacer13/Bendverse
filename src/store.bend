import Base
import ./grid.bend as Grid
import ./cell.bend as Cell
import ./chunk.bend as Chunk

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

def chunk_list(k: U32) -> List<&2, U32>:
  relist(Grid.to_list(Chunk.build(k)))

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

def assemble_chunk(fuel: Nat, +i: U32, +k: U32, cells: List<&2, U32>, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      match cells:
        case Nil{}:
          world
        case Con{h, t}:
          +idx = Grid.index(Chunk.global_x(k, i), Chunk.global_y(k, i), Chunk.global_z(k, i))
          assemble_chunk(p, U32.add(i, 1), k, t, world[idx] <- h)

def assemble_cells(m: Maybe<&2, List<&2, U32>>, +k: U32, world: Array<U32>) -> Array<U32>:
  match m:
    case None{}:
      # A missing (evicted) chunk is regenerated from its pure gen: the store is
      # a sparse overlay on the coordinate-indexed worldgen (rule 11).
      assemble_chunk(U32.to_nat(4096), 0, k, chunk_list(k), world)
    case Some{cells}:
      assemble_chunk(U32.to_nat(4096), 0, k, cells, world)

def assemble_go(fuel: Nat, +ci: U32, +s: Store, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      +k = Chunk.key(U32.and(ci, 3), U32.and(U32.shrn(ci, 2n), 3), U32.and(U32.shrn(ci, 4n), 3))
      assemble_go(p, U32.add(ci, 1), s, assemble_cells(get(s, k), k, world))

def assemble(s: Store) -> Array<U32>:
  assemble_go(64n, 0, s, [0 : U32^18n])

def put_all_go(fuel: Nat, +ci: U32, store: Store) -> Store:
  match fuel:
    case 0n:
      store
    case 1n+p:
      +k = Chunk.key(U32.and(ci, 3), U32.and(U32.shrn(ci, 2n), 3), U32.and(U32.shrn(ci, 4n), 3))
      put_all_go(p, U32.add(ci, 1), set(store, k, chunk_list(k)))

def build_all() -> Store:
  put_all_go(64n, 0, STip{})

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
def evict_key(
  fuel: Nat, m: Maybe<&2, List<&2, U32>>, +ci: U32, +s: Store, acc: Store, +k: U32
) -> Store:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      match m:
        case None{}:
          +ni = U32.add(ci, 1)
          +nk = Chunk.key(U32.and(ni, 3), U32.and(U32.shrn(ni, 2n), 3), U32.and(U32.shrn(ni, 4n), 3))
          evict_key(p, get(s, nk), ni, s, acc, nk)
        case Some{+cells}:
          +sl = sleeping_cells(U32.to_nat(4096), cells, False{})
          +ge = gen_eq_cells(U32.to_nat(4096), cells, chunk_list(k), True{})
          +drop = Bool.and(sl, ge)
          +ni = U32.add(ci, 1)
          +nk = Chunk.key(U32.and(ni, 3), U32.and(U32.shrn(ni, 2n), 3), U32.and(U32.shrn(ni, 4n), 3))
          evict_key(p, get(s, nk), ni, s, keep_cells(acc, k, cells, drop), nk)

# `evict` drops every sleeping, gen-equal chunk; the result assembles to the
# same world as the input because `assemble` regenerates dropped chunks.
def evict(+s: Store) -> Store:
  +k0 = Chunk.key(0, 0, 0)
  evict_key(U32.to_nat(64), get(s, k0), 0, s, STip{}, k0)
