import Base
import ./grid.bend as Grid
import ./window.bend as Window
import ./g5.bend as G5
import ./commit.bend as Commit

# ============================================================================
# g7 (G-scale-7) -- the canonical window map is a relabelling of `Grid.index`.
#
# `src/window.bend` (S1 step 2) made the window-local flat index mask-free:
# `win_index w x y z = (x - origin_x) .|. ((z - origin_z) << 6) .|. ((y -
# origin_y) << 12)`, with no torus `&63`. `Grid.index` is the fixed-box map and
# *does* fold every axis: `(x&63) .|. ((z&63) << 6) .|. ((y&63) << 12)`. On the
# canonical window (base chunk 0, so origin 0) the two agree exactly for box
# coordinates, which is the relabelling the migration must preserve. T81 sampled
# it; this module proves it (`win_canonical_index`), closing `G-scale-7`.
#
# Two bit facts carry the proof, both over the `Bits`/`Word` model (the operands
# are decomposed to their `Word(32n)` payloads):
#
#   * `g7_sub_zero`  -- `U32.sub x 0 == x` (`Commit.v3c_sub_zero`, the `adc`
#                       ripple identity with a zero borrow/subtrahend), which
#                       removes the window origin subtraction at base 0;
#   * `g7_mask6`     -- `U32.and x 63 == x` for `x < 64` (`G5.g5_and_mask_id` at
#                       width `2^6`, `Commit.v3c_full(6n)`), which drops the
#                       `Grid` torus mask on in-box coordinates.
#
# With both, each side of the claim rewrites to the *same* nested-`or` term, so
# the relabelling is a pure congruence and needs no `or`/field disjointness.
# (The `gscale` field lemmas reason about `cw`'s 10-bit/4-bit split, a different
# decomposition than this 6-bit grid packing, so they are not on this path.)
# ============================================================================

# `U32.sub x 0 == x`. `Commit.v3c_sub_zero` is the `Word`-level fact
# (`Word.sub n a (Word.zero n) == a`); lifting it through the `U32` wrapper is a
# congruence.
def g7_sub_zero(x: U32) -> {U32.sub(x, 0) == x : U32}:
  match x:
    case U32{xw}:
      Equal.cong(Word(32n), U32, w => U32{w},
        Word.sub(32n, xw, Word.zero(32n)), xw, Commit.v3c_sub_zero(32n, xw))

# The 6-bit mask identity `x & 63 == x` for `x < 64`, i.e. `G5.g5_and_mask_id` at
# the full 64-leaf tree (`g5_twidth (v3c_full 6) = 2^6 = 64`).
def g7_mask6(x: U32, +h: {U32.is_lt(x, 64) == True{} : Bool})
  -> {U32.and(x, 63) == x : U32}:
  G5.g5_and_mask_id(Commit.v3c_full(6n), x, h)

# The relabelling. Both `Window.win_index (Window.canonical())` and `Grid.index`
# reduce, after `g7_sub_zero`, to the same `or`-of-shifted-axes term; `g7_mask6`
# then removes `Grid.index`'s three `&63` folds. Stated for in-box coordinates
# (`x, y, z < 64`) -- outside the box `Grid.index` folds while the mask-free
# window map does not, so the claim is genuinely a box relabelling (T81, T104).
def g7_win_canonical_index(
    x: U32, y: U32, z: U32,
    +hx: {U32.is_lt(x, 64) == True{} : Bool},
    +hy: {U32.is_lt(y, 64) == True{} : Bool},
    +hz: {U32.is_lt(z, 64) == True{} : Bool})
  -> {Window.win_index(Window.canonical(), x, y, z) == Grid.index(x, y, z) : U32}:
  match x:
    case U32{xw}:
      match y:
        case U32{yw}:
          match z:
            case U32{zw}:
              +x2 = xw
              +y2 = yw
              +z2 = zw
              +xc = U32.sub(U32{x2}, 0)
              +yc = U32.sub(U32{y2}, 0)
              +zc = U32.sub(U32{z2}, 0)
              +ex = g7_sub_zero(U32{x2})
              +ey = g7_sub_zero(U32{y2})
              +ez = g7_sub_zero(U32{z2})
              +mx = g7_mask6(U32{x2}, hx)
              +my = g7_mask6(U32{y2}, hy)
              +mz = g7_mask6(U32{z2}, hz)
              # window side: drop the origin subtractions, one axis at a time.
              +L = U32.or(U32.or(xc, U32.shln(zc, 6n)), U32.shln(yc, 12n))
              +M1 = U32.or(U32.or(xc, U32.shln(U32{z2}, 6n)), U32.shln(yc, 12n))
              +M2 = U32.or(U32.or(xc, U32.shln(U32{z2}, 6n)), U32.shln(U32{y2}, 12n))
              +C = U32.or(U32.or(U32{x2}, U32.shln(U32{z2}, 6n)), U32.shln(U32{y2}, 12n))
              +e1 = Equal.cong(U32, U32,
                a => U32.or(U32.or(xc, U32.shln(a, 6n)), U32.shln(yc, 12n)),
                zc, U32{z2}, ez)
              +e2 = Equal.cong(U32, U32,
                a => U32.or(U32.or(xc, U32.shln(U32{z2}, 6n)), U32.shln(a, 12n)),
                yc, U32{y2}, ey)
              +e3 = Equal.cong(U32, U32,
                a => U32.or(U32.or(a, U32.shln(U32{z2}, 6n)), U32.shln(U32{y2}, 12n)),
                xc, U32{x2}, ex)
              +eL = Equal.trans(U32, L, M1, C, e1,
                Equal.trans(U32, M1, M2, C, e2, e3))
              # grid side: drop the three torus masks, one axis at a time.
              +R = U32.or(
                U32.or(U32.and(U32{x2}, 63), U32.shln(U32.and(U32{z2}, 63), 6n)),
                U32.shln(U32.and(U32{y2}, 63), 12n))
              +R1 = U32.or(
                U32.or(U32{x2}, U32.shln(U32.and(U32{z2}, 63), 6n)),
                U32.shln(U32.and(U32{y2}, 63), 12n))
              +R2 = U32.or(
                U32.or(U32{x2}, U32.shln(U32{z2}, 6n)),
                U32.shln(U32.and(U32{y2}, 63), 12n))
              +f1 = Equal.cong(U32, U32,
                a => U32.or(U32.or(a, U32.shln(U32.and(U32{z2}, 63), 6n)),
                  U32.shln(U32.and(U32{y2}, 63), 12n)),
                U32.and(U32{x2}, 63), U32{x2}, mx)
              +f2 = Equal.cong(U32, U32,
                a => U32.or(U32.or(U32{x2}, U32.shln(a, 6n)),
                  U32.shln(U32.and(U32{y2}, 63), 12n)),
                U32.and(U32{z2}, 63), U32{z2}, mz)
              +f3 = Equal.cong(U32, U32,
                a => U32.or(U32.or(U32{x2}, U32.shln(U32{z2}, 6n)),
                  U32.shln(a, 12n)),
                U32.and(U32{y2}, 63), U32{y2}, my)
              +eR = Equal.trans(U32, R, R1, C, f1,
                Equal.trans(U32, R1, R2, C, f2, f3))
              Equal.trans(U32, L, C, R, eL, Equal.sym(U32, R, C, eR))
