import Base
import ./window.bend as Window
import ./worldgen.bend as Worldgen
import ./g7.bend as G7

# ============================================================================
# winshell (S1 / G-scale-8) -- the *box* contributes the shell at the window's
# own edge.
#
# `Worldgen.gen` paints bedrock on the ABSOLUTE planes `x/y/z in {0,63}` of the
# fixed reference box; `Worldgen.gen_terrain` is shell-free (decision A, A.99).
# `G-scale-8`'s open piece is that an absolute edge cannot coexist with a moving
# window: a window based away from the origin would carry the stray absolute wall
# inside its resident set and have no shell at its own edge. The fix is to make
# the *box* (a finite closed window) contribute the shell at its **window-local**
# planes `0`/`63`.
#
# This module is that sampler:
#   * `border_of(lx, ly, lz)`  -- the box shell predicate on window-local coords;
#   * `win_border w x y z`     -- its window instance, `border_of` of the
#                                 window-local coordinates (`win_lx/ly/lz`);
#   * `gen_at w x y z s`       -- bedrock on the window border, else shell-free
#                                 `gen_terrain` at the global coordinate.
#
# The canonical window is the reference box, so `win_border canonical` reduces to
# the absolute `border_of` (`win_border_canonical`) and `gen_at canonical`
# reproduces `Worldgen.gen` bit-for-bit (`win_gen_canonical`) -- the fixed-box
# worlds and laws stand. Additive: nothing in the live path calls this yet.
# ============================================================================

# The box shell predicate on window-local coordinates: any axis at `0` or `63`
# (the `Worldgen.gen` box edge). The nesting mirrors `gen`'s inline border so
# `gen_border` below is definitional.
def border_of(+lx: U32, +ly: U32, +lz: U32) -> Bool:
  b0 = U32.is_eq(lx, 0)
  b1 = U32.is_eq(lx, 63)
  b2 = U32.is_eq(ly, 0)
  b3 = U32.is_eq(ly, 63)
  b4 = U32.is_eq(lz, 0)
  b5 = U32.is_eq(lz, 63)
  Bool.or(Bool.or(b0, b1), Bool.or(Bool.or(b2, b3), Bool.or(b4, b5)))

# The window's border: the shell predicate on its window-local coordinates. For a
# global coordinate outside the window `win_l*` is not in `0..63`, so the
# predicate is false -- only the window's own faces get the shell.
def win_border(+w: Window.Window, x: U32, y: U32, z: U32) -> Bool:
  border_of(Window.win_lx(w, x), Window.win_ly(w, y), Window.win_lz(w, z))

# The shelled sampler: bedrock on the window border, shell-free terrain inside.
def gen_at(+w: Window.Window, +x: U32, +y: U32, +z: U32, s: U32) -> U32:
  Worldgen.gen_if(win_border(w, x, y, z), x, y, z, s)

# `gen` folds its inline border through the same predicate, so the reference box
# is the window instance (definitional).
def gen_border(x: U32, y: U32, z: U32, s: U32)
  -> {Worldgen.gen(x, y, z, s) == Worldgen.gen_if(border_of(x, y, z), x, y, z, s) : U32}:
  {==}

# ------------------------------------------------------------------ canonical
# The canonical window has cell origin `(0,0,0)`, so `win_lx/ly/lz` is the
# identity (`U32.sub(x, 0) == x`, `G7.g7_sub_zero`).
def win_lx_canonical(x: U32) -> {Window.win_lx(Window.canonical(), x) == x : U32}:
  G7.g7_sub_zero(x)

def win_ly_canonical(y: U32) -> {Window.win_ly(Window.canonical(), y) == y : U32}:
  G7.g7_sub_zero(y)

def win_lz_canonical(z: U32) -> {Window.win_lz(Window.canonical(), z) == z : U32}:
  G7.g7_sub_zero(z)

def win_border_canonical(+x: U32, +y: U32, +z: U32)
  -> {win_border(Window.canonical(), x, y, z) == border_of(x, y, z) : Bool}:
  +ex = win_lx_canonical(x)
  +ey = win_ly_canonical(y)
  +ez = win_lz_canonical(z)
  +lx = Window.win_lx(Window.canonical(), x)
  +ly = Window.win_ly(Window.canonical(), y)
  +lz = Window.win_lz(Window.canonical(), z)
  +h1 = Equal.cong(U32, Bool, l => border_of(l, ly, lz), lx, x, ex)
  +h2 = Equal.cong(U32, Bool, l => border_of(x, l, lz), ly, y, ey)
  +h3 = Equal.cong(U32, Bool, l => border_of(x, y, l), lz, z, ez)
  Equal.trans(Bool,
    border_of(lx, ly, lz),
    border_of(x, ly, lz),
    border_of(x, y, z),
    h1,
    Equal.trans(Bool, border_of(x, ly, lz), border_of(x, y, lz), border_of(x, y, z), h2, h3))

def win_gen_canonical(+x: U32, +y: U32, +z: U32, s: U32)
  -> {gen_at(Window.canonical(), x, y, z, s) == Worldgen.gen(x, y, z, s) : U32}:
  Equal.trans(U32,
    gen_at(Window.canonical(), x, y, z, s),
    Worldgen.gen_if(border_of(x, y, z), x, y, z, s),
    Worldgen.gen(x, y, z, s),
    Equal.cong(Bool, U32, b => Worldgen.gen_if(b, x, y, z, s),
      win_border(Window.canonical(), x, y, z), border_of(x, y, z),
      win_border_canonical(x, y, z)),
    Equal.sym(U32,
      Worldgen.gen_if(border_of(x, y, z), x, y, z, s), Worldgen.gen(x, y, z, s),
      gen_border(x, y, z, s)))
