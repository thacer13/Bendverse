import Base
import ./grid.bend as Grid
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
      world
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
