import Base
import ./cw.bend as Cw
import ./chunk.bend as Chunk
import ./worldgen.bend as Worldgen
import ./store.bend as Store

# ============================================================================
# winset (P3 / G-scale-4 groundwork) -- an explicit resident set of chunk keys.
#
# The live engine keeps its residents *implicitly* in `Store.assemble_go`'s loop
# bounds (all 64 keys) and `Store.evict`'s 64-step walk; the gap registry calls
# this out as `G-scale-4`. A moving window (S1) needs an explicit set plus a
# load/evict policy. This module is that model, purely additive:
#
#   * `Winset` is a finite set of keys in the `cw_key` layout (a list; duplicates
#     are harmless because membership is by `U32.is_eq`);
#   * `winset_mem` / `winset_insert` / `winset_remove` are membership/insert/
#     remove;
#   * `winset_all` is the set of the 64 keys of the current window;
#   * `winset_regen_cells` is the Store regenerability test (sleeping and
#     gen-equal) and `winset_evict` drops exactly the regenerable residents;
#   * `winset_gen_cell` is the pure `Worldgen.gen` fallback a non-resident chunk
#     is assembled from.
#
# Nothing here is wired into `grid`/`sim`/`dirty`/`store`: the live path is
# untouched, the module is a model. The general membership-after-remove and the
# `assemble`/`evict` roundtrip laws are stated over this model but not proven
# (see the track report / PLAN §5.3 `G-scale-4`).
# ============================================================================

type Winset is Data:
  WinsetNil{}
  WinsetCon{key: U32, rest: Winset}

def winset_empty() -> Winset:
  WinsetNil{}

def winset_mem(+k: U32, s: Winset) -> Bool:
  match s:
    case WinsetNil{}:
      False{}
    case WinsetCon{key, rest}:
      Bool.or(U32.is_eq(k, key), winset_mem(k, rest))

def winset_insert(k: U32, s: Winset) -> Winset:
  WinsetCon{k, s}

def winset_remove(+k: U32, s: Winset) -> Winset:
  match s:
    case WinsetNil{}:
      WinsetNil{}
    case WinsetCon{+key, +rest}:
      Bool.pick(Winset, U32.is_eq(k, key), winset_remove(k, rest), WinsetCon{key, winset_remove(k, rest)})

# The window's 64 keys, enumerated the same way `Store.put_all_go`/`evict_key`
# do (`ci` is the 4x2x4 mixed-radix index: x in bits 0-1, y in 2-3, z in 4-5).
def winset_all_go(fuel: Nat, +ci: U32, s: Winset) -> Winset:
  match fuel:
    case 0n:
      s
    case 1n+p:
      +k = Cw.cw_key(U32.and(ci, 3), U32.and(U32.shrn(ci, 2n), 3), U32.and(U32.shrn(ci, 4n), 3))
      winset_all_go(p, U32.add(ci, 1), WinsetCon{k, s})

def winset_all() -> Winset:
  winset_all_go(64n, 0, WinsetNil{})

# ------------------------------------------------------------------ regenerability
# The store's regenerability test, `Store.sleeping_cells` and
# `Store.gen_eq_cells`, against the chunk's pure gen list `Store.chunk_list(k)`
# (which is `Worldgen.gen` at the chunk's global coordinates).

def winset_regen_cells(+k: U32, +cells: List<&2, U32>) -> Bool:
  Bool.and(
    Store.sleeping_cells(U32.to_nat(Chunk.cells()), cells, False{}),
    Store.gen_eq_cells(U32.to_nat(Chunk.cells()), cells, Store.chunk_list(k), True{}))

def winset_regenerable_m(m: Maybe<&2, List<&2, U32>>, +k: U32) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+cells}:
      winset_regen_cells(k, cells)

def winset_regenerable(store: Store.Store, +k: U32) -> Bool:
  winset_regenerable_m(Store.get(store, k), k)

# Drop every resident key whose stored chunk is regenerable; keep the rest. This
# is the explicit-set mirror of `Store.evict`.
def winset_evict(+store: Store.Store, s: Winset) -> Winset:
  match s:
    case WinsetNil{}:
      WinsetNil{}
    case WinsetCon{+key, +rest}:
      Bool.pick(Winset, winset_regenerable(store, key), winset_evict(store, rest), WinsetCon{key, winset_evict(store, rest)})

# The pure gen cell `assemble` falls back to for a non-resident chunk, at the
# chunk's local index `i`. Definitionally the store's `chunk_list` element.
def winset_gen_cell(+k: U32, +i: U32) -> U32:
  Worldgen.gen(Chunk.global_x(k, i), Chunk.global_y(k, i), Chunk.global_z(k, i), Worldgen.seed())
