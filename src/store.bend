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
