import Base
import ./bits.bend as Bits
import ./g5.bend as G5
import ./g7.bend as G7
import ./window.bend as Window
import ./wgrid.bend as WGrid
import ./word.bend as WRefl

# ============================================================================
# wmarg (S1 endgame, slice W2) -- the window-margin / residency verification.
#
# `SCALE.md` §8 W2 and gap `G-scale-1`: `Grid.step_inside` guards every rule
# target, but on a *moving* window the guard must mean "the target is resident",
# not "the box wrapped". `src/wgrid.bend` makes that explicit: `wgrid_axis_ok`
# is the per-axis residency test (`Window.win_lx` stays in `[0, win_edge)`), and
# `wgrid_resident` is the model-side predicate on a *global* coordinate. This
# module connects them to the engine:
#
#   * `wgrid_axis_guard`      -- an in-frame target (`is_lt(add(local,d),
#                               win_edge)`) makes the axis guard `True`: the
#                               guard never silently makes a valid step inert.
#   * `wgrid_step_margin`     -- the three-axis form (the handoff's "every
#                               `Rules.plan` target of an in-frame cell is not
#                               inert"). Under `Decision B` the driver keeps the
#                               active set a chunk inside the frame, so every
#                               target is in-frame (the margin is the driver's
#                               invariant, `W5`).
#   * `wgrid_canonical_resident` -- the canonical window's resident set is
#                               exactly the box: residency is `x,y,z < 64`.
#
# The one bit brick is `wmarg_mask6_high_zero`: `y < 2^6 => y & ~(2^6-1) = 0`
# (`G5.g5_wand_mask_lt` gives `y & mask6 = y`; the complement is a closed
# `and`). This is the exact `and(_, not(edge-1)) == 0` test the guard performs.
# ============================================================================

# `and(mask 6, not(mask 6)) = 0` -- a closed computation, the complement half of
# the low-6-bit mask identity.
def wmarg_mask6_and_not() -> {Word.and(32n, Bits.mask(32n, 6n), Word.not(32n, Bits.mask(32n, 6n))) == Word.zero(32n) : Word(32n)}:
  {==}

# `y < 2^6` implies `y & ~(2^6-1) = 0`: `y` has no bit at position >= 6. This is
# the `Word`-level core of "a window-local coordinate in `[0, 64)` passes the
# high-bit guard".
def wmarg_mask6_high_zero(+yw: Word(32n), +h: {Cmp.is_lt(Word.cmp(32n, yw, G5.g5_mpow(32n, 6n))) == True{} : Bool})
  -> {Word.and(32n, yw, Word.not(32n, Bits.mask(32n, 6n))) == Word.zero(32n) : Word(32n)}:
  +e1 = G5.g5_wand_mask_lt(32n, 6n, yw, h)
  +e2 = Bits.w_and_assoc(32n, yw, Bits.mask(32n, 6n), Word.not(32n, Bits.mask(32n, 6n)))
  +e4 = wmarg_mask6_and_not()
  +e5 = Bits.w_and_zero(32n, yw)
  +A = Word.and(32n, yw, Word.not(32n, Bits.mask(32n, 6n)))
  +B = Word.and(32n, Word.and(32n, yw, Bits.mask(32n, 6n)), Word.not(32n, Bits.mask(32n, 6n)))
  +C = Word.and(32n, yw, Word.and(32n, Bits.mask(32n, 6n), Word.not(32n, Bits.mask(32n, 6n))))
  +D = Word.and(32n, yw, Word.zero(32n))
  +eAB = Equal.cong(Word(32n), Word(32n), z => Word.and(32n, z, Word.not(32n, Bits.mask(32n, 6n))), yw, Word.and(32n, yw, Bits.mask(32n, 6n)), Equal.sym(Word(32n), Word.and(32n, yw, Bits.mask(32n, 6n)), yw, e1))
  +eCD = Equal.cong(Word(32n), Word(32n), z => Word.and(32n, yw, z), Word.and(32n, Bits.mask(32n, 6n), Word.not(32n, Bits.mask(32n, 6n))), Word.zero(32n), e4)
  +eB0 = Equal.trans(Word(32n), B, C, Word.zero(32n), e2, Equal.trans(Word(32n), C, D, Word.zero(32n), eCD, e5))
  Equal.trans(Word(32n), A, B, Word.zero(32n), eAB, eB0)

# The per-axis margin: an in-frame target coordinate makes `wgrid_axis_ok` true.
# This is the direction `G-scale-1` needs -- a step whose window-local target is
# inside the frame is *not* made inert by the guard.
def wgrid_axis_guard(+local: U32, +d: U32,
    +h: {U32.is_lt(U32.add(local, d), Window.win_edge()) == True{} : Bool})
  -> {WGrid.wgrid_axis_ok(local, d) == True{} : Bool}:
  match local:
    case U32{lw}:
      match d:
        case U32{dw}:
          +yw = Word.add(32n, lw, dw)
          +ew = wmarg_mask6_high_zero(yw, h)
          +eU = Equal.cong(Word(32n), U32, z => U32{z},
            Word.and(32n, yw, Word.not(32n, Bits.mask(32n, 6n))), Word.zero(32n), ew)
          Equal.trans(Bool,
            U32.is_eq(U32.and(U32{yw}, U32.not(U32.sub(Window.win_edge(), 1))), 0),
            U32.is_eq(0, 0), True{},
            Equal.cong(U32, Bool, z => U32.is_eq(z, 0),
              U32.and(U32{yw}, U32.not(U32.sub(Window.win_edge(), 1))), 0, eU),
            {==})

# The three-axis margin: if each axis's window-local target coordinate is
# in-frame, the engine's closure guard is `True`. This is the handoff's
# `G-scale-1` invariant in the direction the engine needs (in-frame => not
# silently inert); the driver's chunk margin makes "active cell => in-frame
# target" hold (`W5`).
def wgrid_step_margin(+w: Window.Window, +i: U32, +dx: U32, +dy: U32, +dz: U32,
    +hx: {U32.is_lt(U32.add(Window.win_ix(i), dx), Window.win_edge()) == True{} : Bool},
    +hy: {U32.is_lt(U32.add(Window.win_iy(i), dy), Window.win_edge()) == True{} : Bool},
    +hz: {U32.is_lt(U32.add(Window.win_iz(i), dz), Window.win_edge()) == True{} : Bool})
  -> {WGrid.wgrid_step_inside(w, i, dx, dy, dz) == True{} : Bool}:
  +lx = Window.win_ix(i)
  +ly = Window.win_iy(i)
  +lz = Window.win_iz(i)
  +gx = wgrid_axis_guard(lx, dx, hx)
  +gy = wgrid_axis_guard(ly, dy, hy)
  +gz = wgrid_axis_guard(lz, dz, hz)
  +ax = WGrid.wgrid_axis_ok(lx, dx)
  +ay = WGrid.wgrid_axis_ok(ly, dy)
  +az = WGrid.wgrid_axis_ok(lz, dz)
  +e1 = Equal.cong(Bool, Bool, b => Bool.and(b, Bool.and(ay, az)), ax, True{}, gx)
  +e2 = Equal.cong(Bool, Bool, b => Bool.and(b, az), ay, True{}, gy)
  Equal.trans(Bool,
    Bool.and(ax, Bool.and(ay, az)),
    Bool.and(True{}, Bool.and(ay, az)),
    True{},
    e1,
    Equal.trans(Bool,
      Bool.and(True{}, Bool.and(ay, az)),
      Bool.and(True{}, az),
      True{},
      Equal.cong(Bool, Bool, b => Bool.and(True{}, b), Bool.and(ay, az), Bool.and(True{}, az), e2),
      gz))

# The canonical residency law: on the box the resident set is exactly the in-box
# cells. Each axis's `win_lx(canonical, x) = U32.sub(x, 0)` drops to `x`
# (`G7.g7_sub_zero`), so residency is `x,y,z < 64`.
def wmarg_inbox(x: U32, y: U32, z: U32) -> Bool:
  Bool.and(U32.is_lt(x, 64), Bool.and(U32.is_lt(y, 64), U32.is_lt(z, 64)))

def wmarg_cres_x(x: U32) -> {WGrid.wgrid_resident_x(Window.canonical(), x) == U32.is_lt(x, 64) : Bool}:
  Equal.cong(U32, Bool, z => U32.is_lt(z, 64),
    Window.win_lx(Window.canonical(), x), x, G7.g7_sub_zero(x))

def wmarg_cres_y(y: U32) -> {WGrid.wgrid_resident_y(Window.canonical(), y) == U32.is_lt(y, 64) : Bool}:
  Equal.cong(U32, Bool, z => U32.is_lt(z, 64),
    Window.win_ly(Window.canonical(), y), y, G7.g7_sub_zero(y))

def wmarg_cres_z(z: U32) -> {WGrid.wgrid_resident_z(Window.canonical(), z) == U32.is_lt(z, 64) : Bool}:
  Equal.cong(U32, Bool, zz => U32.is_lt(zz, 64),
    Window.win_lz(Window.canonical(), z), z, G7.g7_sub_zero(z))

def wgrid_canonical_resident(+x: U32, +y: U32, +z: U32)
  -> {WGrid.wgrid_resident(Window.canonical(), x, y, z) == wmarg_inbox(x, y, z) : Bool}:
  +rx = WGrid.wgrid_resident_x(Window.canonical(), x)
  +ry = WGrid.wgrid_resident_y(Window.canonical(), y)
  +rz = WGrid.wgrid_resident_z(Window.canonical(), z)
  +ix = U32.is_lt(x, 64)
  +iy = U32.is_lt(y, 64)
  +iz = U32.is_lt(z, 64)
  +ex = wmarg_cres_x(x)
  +ey = wmarg_cres_y(y)
  +ez = wmarg_cres_z(z)
  +eB1 = Equal.cong(Bool, Bool, b => Bool.and(b, rz), ry, iy, ey)
  +eB = Equal.cong(Bool, Bool, b => Bool.and(ix, b), Bool.and(ry, rz), Bool.and(iy, rz), eB1)
  +eC = Equal.cong(Bool, Bool, b => Bool.and(ix, Bool.and(iy, b)), rz, iz, ez)
  +eA = Equal.cong(Bool, Bool, b => Bool.and(b, Bool.and(ry, rz)), rx, ix, ex)
  Equal.trans(Bool,
    Bool.and(rx, Bool.and(ry, rz)),
    Bool.and(ix, Bool.and(ry, rz)),
    Bool.and(ix, Bool.and(iy, iz)),
    eA,
    Equal.trans(Bool,
      Bool.and(ix, Bool.and(ry, rz)),
      Bool.and(ix, Bool.and(iy, rz)),
      Bool.and(ix, Bool.and(iy, iz)),
      eB, eC))

# ---------------------------------------------------- G-scale-1 residual (gsc1)
# The converse of `wgrid_axis_guard`: `wgrid_axis_ok` passing is the engine's
# residency test, and it means the coordinate did not fold. The guard is a
# `U32.is_eq(_, 0)`, reflected to `Word.and(32n, y, Word.not(32n, mask6)) ==
# Word.zero(32n)` by `Word.w_cmp_eq`; the decomposition `gsc1_word_or_and_not`
# (`y == (y & mask6) | (y & ~mask6)`) with `Bits.w_or_zero` then gives the low
# six bits back, i.e. `y & mask6 == y`.
def gsc1_word_no_fold(+yw: Word(32n),
    +h: {Cmp.is_eq(Word.cmp(32n, Word.and(32n, yw, Word.not(32n, Bits.mask(32n, 6n))), Word.zero(32n))) == True{} : Bool})
  -> {Word.and(32n, yw, Bits.mask(32n, 6n)) == yw : Word(32n)}:
  +hz = WRefl.w_cmp_eq(32n, Word.and(32n, yw, Word.not(32n, Bits.mask(32n, 6n))), Word.zero(32n), h)
  +orzero = Bits.w_or_zero(32n, Word.and(32n, yw, Bits.mask(32n, 6n)))
  +decomp = Bits.gsc1_word_or_and_not(32n, yw, Bits.mask(32n, 6n))
  Equal.trans(Word(32n),
    Word.and(32n, yw, Bits.mask(32n, 6n)),
    Word.or(32n, Word.and(32n, yw, Bits.mask(32n, 6n)), Word.zero(32n)),
    yw,
    Equal.sym(Word(32n), Word.or(32n, Word.and(32n, yw, Bits.mask(32n, 6n)), Word.zero(32n)), Word.and(32n, yw, Bits.mask(32n, 6n)), orzero),
    Equal.trans(Word(32n),
      Word.or(32n, Word.and(32n, yw, Bits.mask(32n, 6n)), Word.zero(32n)),
      Word.or(32n, Word.and(32n, yw, Bits.mask(32n, 6n)), Word.and(32n, yw, Word.not(32n, Bits.mask(32n, 6n)))),
      yw,
      Equal.cong(Word(32n), Word(32n), z => Word.or(32n, Word.and(32n, yw, Bits.mask(32n, 6n)), z), Word.zero(32n), Word.and(32n, yw, Word.not(32n, Bits.mask(32n, 6n))), Equal.sym(Word(32n), Word.and(32n, yw, Word.not(32n, Bits.mask(32n, 6n))), Word.zero(32n), hz)),
      decomp))

# `gsc1_axis_no_fold` at the `U32` level: a passing per-axis guard means the
# box mask `&63` is the identity on the target coordinate.
def gsc1_axis_no_fold(+local: U32, +d: U32,
    +h: {WGrid.wgrid_axis_ok(local, d) == True{} : Bool})
  -> {U32.and(U32.add(local, d), 63) == U32.add(local, d) : U32}:
  match local:
    case U32{lw}:
      match d:
        case U32{dw}:
          +yw = Word.add(32n, lw, dw)
          +e = gsc1_word_no_fold(yw, h)
          Equal.cong(Word(32n), U32, z => U32{z}, Word.and(32n, yw, Bits.mask(32n, 6n)), yw, e)
