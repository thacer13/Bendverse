import Base
import ./grid.bend as Grid
import ./cw.bend as Cw

# ============================================================================
# window (S1 step 2) -- a moving chunk window as an explicit, torus-free map.
#
# The live engine is the fixed 64^3 torus (`Grid`): every axis is masked `&63`,
# so the box is closed by construction and there is exactly one world. `SCALE.md`
# migrates the engine to a *window*: a cubic block of resident chunks at a global
# chunk origin, addressed without a torus mask. This module is step 2 -- the
# model and the index map -- and is deliberately *additive*: nothing in the live
# path uses it yet, and the single instance `canonical()` is exactly the 64^3
# box, so `win_index` on it is a relabelling of `Grid.index` (witnessed by T81).
# Step 3 rewires `Store.assemble_go` to an explicit resident set; step 4 adds
# window motion.
#
# Layout. A window is `win_chunks` chunks on a side (`win_edge` cells), matching
# `Cw.cw_chunk_size`; its origin is the base chunk `(bx, by, bz)`. A global
# coordinate's window-local cell coordinate is `global - origin` (the `cw`
# split/rejoin `(x>>4)<<4 + (x&15) == x` says this is the same as the cw
# chunk+local decomposition -- that identity is the proven `gscale_global_rt`),
# and the window-local flat index is `lx + lz*win_edge + ly*win_edge^2`. Unlike
# `Grid.index` there is no `&63` anywhere, so a coordinate above the box keeps its
# chunk index instead of folding to the opposite face (T82).
#
# Why subtraction, not `cw_chunk_of`/`cw_local_of` directly: Bend is affine, so a
# coordinate cannot be consumed twice (`cw_chunk_of(x)` and `cw_local_of(x)` would
# both take `x`). `x - (base_x<<4)` consumes `x` once and is exactly the cw
# decomposition at a chunk-aligned origin. `cw` still supplies the window origin
# as a chunk key (`win_key`).
# ============================================================================

def win_chunks() -> U32:
  4

def win_edge() -> U32:
  64

def win_cells() -> U32:
  262144

type Window is Data:
  Window{bx: U32, by: U32, bz: U32}

# The one live instance: the 64^3 box at global chunk origin (0,0,0).
def canonical() -> Window:
  Window{0, 0, 0}

# a window at an explicit base chunk (the moving-window constructor).
def at(bx: U32, by: U32, bz: U32) -> Window:
  Window{bx, by, bz}

def base_x(w: Window) -> U32:
  match w:
    case Window{bx, by, bz}:
      bx

def base_y(w: Window) -> U32:
  match w:
    case Window{bx, by, bz}:
      by

def base_z(w: Window) -> U32:
  match w:
    case Window{bx, by, bz}:
      bz

# window origin in cells.
def origin_x(w: Window) -> U32:
  U32.shln(base_x(w), 4n)

def origin_y(w: Window) -> U32:
  U32.shln(base_y(w), 4n)

def origin_z(w: Window) -> U32:
  U32.shln(base_z(w), 4n)

# window-local cell coordinate of a global coordinate (never wraps).
def win_lx(w: Window, x: U32) -> U32:
  U32.sub(x, origin_x(w))

def win_ly(w: Window, y: U32) -> U32:
  U32.sub(y, origin_y(w))

def win_lz(w: Window, z: U32) -> U32:
  U32.sub(z, origin_z(w))

# window-local flat index `lx + lz*64 + ly*4096` (the `Grid.index` layout, over
# window-local coordinates). The three fields are each < 64, so `or` and `add`
# agree; `or` matches `Grid.index`'s formula.
def win_index(w: Window, x: U32, y: U32, z: U32) -> U32:
  match w:
    case Window{bx, by, bz}:
      +lx = U32.sub(x, U32.shln(bx, 4n))
      +ly = U32.sub(y, U32.shln(by, 4n))
      +lz = U32.sub(z, U32.shln(bz, 4n))
      (lx .|. (lz << 6n) .|. (ly << 12n) : U32)

# inverses: window-local flat index -> window-local cell coordinate.
def win_ix(i: U32) -> U32:
  (i .&. 63 : U32)

def win_iz(i: U32) -> U32:
  ((i >> 6n) .&. 63 : U32)

def win_iy(i: U32) -> U32:
  ((i >> 12n) .&. 63 : U32)

# window-local flat index -> global coordinate (add the window origin back).
def win_gx(w: Window, i: U32) -> U32:
  U32.add(win_ix(i), origin_x(w))

def win_gy(w: Window, i: U32) -> U32:
  U32.add(win_iy(i), origin_y(w))

def win_gz(w: Window, i: U32) -> U32:
  U32.add(win_iz(i), origin_z(w))

# the window's base chunk as a `cw` key (the resident-set / store key).
def win_key(w: Window) -> U32:
  match w:
    case Window{bx, by, bz}:
      Cw.cw_key(bx, by, bz)
