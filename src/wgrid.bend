import Base
import ./grid.bend as Grid
import ./window.bend as Window

# ============================================================================
# wgrid (S1 endgame, slice W1) -- the window-local coordinate seam.
#
# `SCALE.md` §8 migrates the live tick pipeline off the fixed 64^3 `Grid` torus
# onto a moving `Window` (a cubic block of resident chunks at a global chunk
# origin). Only three things in the live path assume the box:
#
#   (i)   the coordinate map `Grid.index` / `Grid.ix/iy/iz`;
#   (ii)  the neighbour map `Grid.neighbor` (torus wrap) and the guard
#         `Grid.step_inside` (box edge = universe edge);
#   (iii) fixed sizes (`Grid.volume`, the 64-row `Dirty.Mask`).
#
# The write algebra (`Refine`/`PT`), the phase fold and `Support` work on flat
# `Array<U32>` indices plus this map, so the map is the only thing that changes.
# This module is the seam: every window-relative coordinate / neighbour / guard
# used by the live rules will route through here, so W2 (residency-aware
# neighbour resolution, `G-scale-1`) is a change to *this file*, not to the
# state machines.
#
# W1 is **canonical-only**: the single live instance is `Window.canonical()`,
# whose `win_index` is the proven relabelling of `Grid.index` (`win_canonical_index`,
# A.105) for in-box coordinates. The neighbour / guard bodies below still carry
# the torus frame (`&63` / the `not(size-1)` mask) exactly as `Grid` does, so for
# the canonical window they are bit-identical to `Grid.neighbor`/`Grid.step_inside`
# (witnessed T122-T124). The `Window` parameter is carried from the tick entry
# down to the rule fold even though W1 does not yet let it affect resolution:
# that is the point of the slice -- W2 swaps the two bodies for residency-aware
# versions and every call site is already threaded.
#
# Naming. `Window.win_ix/iy/iz` return *window-local* coordinates; `win_gx/gy/gz`
# add the origin back and return *global* coordinates. Subscripted `wgrid_ix` is
# the global inverse (the analogue of `Grid.ix`), matching the SCALE §8 brief.
# ============================================================================

# window-local flat index of a global coordinate, torus-free (no `&63`).
def wgrid_index(w: Window.Window, x: U32, y: U32, z: U32) -> U32:
  Window.win_index(w, x, y, z)

# window-local flat index -> global coordinate (the `Grid.ix/iy/iz` analogues).
def wgrid_ix(w: Window.Window, i: U32) -> U32:
  Window.win_gx(w, i)

def wgrid_iy(w: Window.Window, i: U32) -> U32:
  Window.win_gy(w, i)

def wgrid_iz(w: Window.Window, i: U32) -> U32:
  Window.win_gz(w, i)

# The window-frame neighbour. W1 is canonical-only: the body *delegates* to
# `Grid.neighbor`, so `wgrid_neighbor(Window.canonical(), i, ...)` and, through the
# `Rules.side4/diag4` wrappers, every existing `Grid.neighbor`-shaped proof
# (`diag4_y_flip`, `batch.bend`, `color.bend`) reduce *syntactically* to the same
# term -- the seam is transparent. W2 replaces this body with residency-aware
# resolution: a target whose global coordinate leaves the resident set is inert
# (the `G-scale-1` margin rule), not wrapped onto the opposite face. That change
# is local to this file; it will revisit the `diag4`/`side4` shape proofs.
def wgrid_neighbor(+w: Window.Window, +i: U32, dx: U32, dy: U32, dz: U32) -> U32:
  Grid.neighbor(i, dx, dy, dz)

def wgrid_below(w: Window.Window, i: U32) -> U32:
  wgrid_neighbor(w, i, 0, 4294967295, 0)

def wgrid_above(w: Window.Window, i: U32) -> U32:
  wgrid_neighbor(w, i, 0, 1, 0)

def wgrid_west(w: Window.Window, i: U32) -> U32:
  wgrid_neighbor(w, i, 4294967295, 0, 0)

def wgrid_east(w: Window.Window, i: U32) -> U32:
  wgrid_neighbor(w, i, 1, 0, 0)

def wgrid_south(w: Window.Window, i: U32) -> U32:
  wgrid_neighbor(w, i, 0, 0, 4294967295)

def wgrid_north(w: Window.Window, i: U32) -> U32:
  wgrid_neighbor(w, i, 0, 0, 1)

# The per-axis window-frame guard: does adding `d` to the window-local coordinate
# `local` keep it in the resident frame `[0, win_edge)`? The high-bit mask test is
# the same one `Grid.step_inside` uses, so encoding it once here makes the
# guard's meaning ("the local coordinate stayed in the window") explicit.
def wgrid_axis_ok(+local: U32, d: U32) -> Bool:
  U32.is_eq(U32.and(U32.add(local, d), U32.not(U32.sub(Window.win_edge(), 1))), 0)

# The window-frame closure guard over the three axes. The body is exactly
# `Grid.step_inside` written in `Window` terms (`win_ix = Grid.ix`, `win_edge =
# Grid.size`), so swapping it in keeps the seam transparent (the `G15` wake
# guard and every `Rules.plan` target guard reduce to the same term).
#
# `G-scale-1` meaning: `wgrid_axis_ok` is the engine's *residency* test. A false
# axis means the step would leave the resident frame (`Window.win_lx` outer
# range); under the `Decision B` margin the active set never touches the frame
# edge, so a valid in-frame target is never silently inert (`wmarg.bend` proves
# the in-frame -> guard direction; the driver keeps the margin, `W5`).
def wgrid_step_inside(+w: Window.Window, +i: U32, dx: U32, dy: U32, dz: U32) -> Bool:
  Bool.and(wgrid_axis_ok(Window.win_ix(i), dx),
    Bool.and(wgrid_axis_ok(Window.win_iy(i), dy), wgrid_axis_ok(Window.win_iz(i), dz)))

# --------------------------------------------------------------- residency model
# Cell-level residency: is a *global* coordinate `(x,y,z)` inside `win`? Its
# window-local coordinate (global minus origin) must lie in `[0, win_edge)`. A
# coordinate below the origin wraps in `U32.sub` to a huge value, so `is_lt` is
# false there too -- the predicate is total and exact.
def wgrid_resident_x(+w: Window.Window, x: U32) -> Bool:
  U32.is_lt(Window.win_lx(w, x), Window.win_edge())

def wgrid_resident_y(+w: Window.Window, y: U32) -> Bool:
  U32.is_lt(Window.win_ly(w, y), Window.win_edge())

def wgrid_resident_z(+w: Window.Window, z: U32) -> Bool:
  U32.is_lt(Window.win_lz(w, z), Window.win_edge())

def wgrid_resident(+w: Window.Window, x: U32, y: U32, z: U32) -> Bool:
  Bool.and(wgrid_resident_x(w, x),
    Bool.and(wgrid_resident_y(w, y), wgrid_resident_z(w, z)))

# Is the *target* of a rule step (from flat index `i`, by `(dx,dy,dz)`) resident?
# This is the model-side form of `wgrid_step_inside`: the guard tests the
# window-local coordinate, residency tests the global coordinate; they agree
# (`wmarg.bend`).
def wgrid_target_resident(+w: Window.Window, +i: U32, dx: U32, dy: U32, dz: U32) -> Bool:
  wgrid_resident(w,
    U32.add(Window.win_gx(w, i), dx),
    U32.add(Window.win_gy(w, i), dy),
    U32.add(Window.win_gz(w, i), dz))
