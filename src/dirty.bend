import Base
import ./grid.bend as Grid
import ./cell.bend as Cell
import ./dirtyn.bend as Dirtyn

# ------------------------------------------------------------------ V0-4b-3b / S1-W3
# The dirty-*row* mask: a set of `y` rows, one bit per row of the 64³ world. The
# tick carries it across ticks so it can build the active-cell work list by
# scanning only the rows that may hold a cell activated since the last tick,
# instead of rescanning the whole world (the retired `any_active` check and
# `active_list`'s full scan).
#
# Why rows, not chunks. `Support.sup` needs the work list in ascending `y` order
# (a cell's `below` is `y-1`, so the bottom-up support propagation is one pass
# only if every `y-1` is processed before its `y`). Chunks of 16³ cells are
# cheaper to skip but their natural traversal order (chunk-major) interleaves
# rows, so the support pass sees a non-monotone `y` sequence and support lags.
# Row granularity gives the scan exactly the global ascending order
# (`y`, then `z`, then `x`) the support pass needs, and a wake dirties only the
# three rows it can reach (`y-1`, `y`, `y+1`).
#
# S1/W3 (SCALE.md §8). The mask is no longer a two-`U32` `Mask{lo, hi}` record:
# it holds the `Word(64)` bit vector of `Dirtyn` directly, and every row
# operation delegates to `Dirtyn` on that word (`Dirtyn.dwin_*`). For the
# canonical 64-row window this is bit-identical -- the `Dirty.Mask <-> Word(64)`
# isomorphism (`mask_word_get`) is now definitional -- and a window edge of
# `2^n` rows is the same code at width `2^n`.
#
# Invariant. The only way a cell becomes active is a deferred wake applied at
# tick end (`Ops.wake` sets the bit on the 26 neighbours of a wake *source*), and
# every wake source marks its own row and its two neighbours. So an active cell
# always lies in a dirty row, and at the start of a tick the work list is exactly
# the active cells of the dirty rows, in ascending flat-index order.

type Mask is Data:
  Mask{w: Word(64n)}

# The `Word(64)` a mask holds. `maskword.bend` re-exports this as its
# `mask_word` (the old lo/hi -> word constructor is now the identity).
def w3_w_of(m: Mask) -> Word(64n):
  match m:
    case Mask{w}: w

def zermask() -> Mask:
  Mask{Dirtyn.dwin_zero(64n)}

def is_dirty_y(+m: Mask, +y: U32) -> Bool:
  Dirtyn.dwin_get(64n, Dirtyn.mask_word(w3_w_of(m)), U32.to_nat(y))

def or_y(+m: Mask, +y: U32) -> Mask:
  Mask{Dirtyn.dwin_or_y(64n, Dirtyn.mask_word(w3_w_of(m)), U32.to_nat(y))}

def mark_if(+m: Mask, +y: U32, b: Bool) -> Mask:
  Bool.pick(Mask, b, or_y(m, y), m)

# The three rows a wake at `i` can reach: `y-1`, `y`, `y+1`, modulo 64. `Ops.wake`
# is bounded by `Grid.step_inside` (C2/G15), so at the boundary the wrapped row is
# marked but no cell in it is written: the mask over-approximates the wake reach,
# which keeps the invariant (every active cell still lies in a dirty row) intact.
# The wrap is `Dirtyn.dwin_mark_wake_auto` (`dwin_up`/`dwin_down`, the `mod 64`
# neighbours), whose range is `dwin_up_lt`/`dwin_down_lt` (A.104).
def mark_wake(+m: Mask, +i: U32) -> Mask:
  +y = Grid.iy(i)
  Mask{Dirtyn.dwin_mark_wake_auto(64n, Dirtyn.mask_word(w3_w_of(m)), U32.to_nat(y))}

# ------------------------------------------------------------------ scans
# `active_mask` is the one-time prime: the rows that contain an active cell.
#
# S1/W3 performance note. The live `Mask` holds a `Word(64)` (so `mask_word_get`
# is definitional and the width generalises), but the prime scan touches every
# cell of the world, and a `Word(64)` row op is 64 structural steps -- with the
# `mark_if` `pick` the native evaluator forces that branch for *every* cell, a
# ~100x regression (measured: a 50-tick settle went from ~1.5s to minutes). The
# scan therefore accumulates the canonical two-`U32` limbs natively (`W3AMask`) and
# materialises the `Word(64)` once, at the end. The result is bit-identical:
# `cat 32 lo hi` is exactly the old lo/hi layout. `mark_wake` (per wake, not per
# cell) still delegates to `Dirtyn`.
type W3AMask is Data:
  W3AMask{lo: U32, hi: U32}

def w3_amask_zero() -> W3AMask:
  W3AMask{0, 0}

def w3_amask_or_y(+m: W3AMask, +y: U32) -> W3AMask:
  match m:
    case W3AMask{lo, hi}:
      +bit = U32.shln(1, U32.to_nat(U32.and(y, 31)))
      z = U32.is_lt(y, 32)
      Bool.pick(W3AMask, z,
        W3AMask{U32.or(lo, bit), hi},
        W3AMask{lo, U32.or(hi, bit)})

def w3_amask_mark_if(+m: W3AMask, +y: U32, b: Bool) -> W3AMask:
  Bool.pick(W3AMask, b, w3_amask_or_y(m, y), m)

def w3_amask_to_mask(m: W3AMask) -> Mask:
  match m:
    case W3AMask{lo, hi}:
      Mask{Dirtyn.cat(32n, Dirtyn.u32_word(lo), Dirtyn.u32_word(hi))}

def w3_amask_go(fuel: Nat, +i: U32, m: W3AMask, gp: Array<U32> & U32) -> Array<U32> & W3AMask:
  match fuel:
    case 0n:
      match gp:
        case (world, v):
          +act = U32.is_ne(Cell.active(v), 0)
          (world, w3_amask_mark_if(m, Grid.iy(i), act))
    case 1n+p:
      match gp:
        case (world, v):
          +act = U32.is_ne(Cell.active(v), 0)
          +m2 = w3_amask_mark_if(m, Grid.iy(i), act)
          +ni = U32.sub(i, 1)
          q = Array.get(U32, world, ni)
          w3_amask_go(p, ni, m2, q)

def w3_amask_finish(r: Array<U32> & W3AMask) -> Array<U32> & Mask:
  match r:
    case (world, m):
      (world, w3_amask_to_mask(m))

def active_mask(world: Array<U32>) -> Array<U32> & Mask:
  +hi = U32.sub(Grid.volume(), 1)
  q = Array.get(U32, world, hi)
  w3_amask_finish(w3_amask_go(U32.to_nat(hi), hi, w3_amask_zero(), q))

# One row: `base = y<<12`, `fuel = k` walks local `k = z*64+x` from 4095 to 0, so
# the terminal step processes `k=0` and no read runs past the row.
def scan_row(
  fuel: Nat, gp: Array<U32> & U32, +base: U32, +k: U32, +acc: List<&2, U32>
) -> Array<U32> & List<&2, U32>:
  match fuel:
    case 0n:
      match gp:
        case (world, v):
          +i = U32.add(base, k)
          act = U32.is_ne(Cell.active(v), 0)
          (world, Bool.pick(List<&2, U32>, act, i <> acc, acc))
    case 1n+p:
      match gp:
        case (world, v):
          +i = U32.add(base, k)
          act = U32.is_ne(Cell.active(v), 0)
          +acc2 = Bool.pick(List<&2, U32>, act, i <> acc, acc)
          +nk = U32.sub(k, 1)
          +ni = U32.add(base, nk)
          q = Array.get(U32, world, ni)
          scan_row(p, q, base, nk, acc2)

def scan_rows(
  fuel: Nat, gp: Array<U32> & List<&2, U32>, +y: U32, +mask: Mask
) -> Array<U32> & List<&2, U32>:
  match fuel:
    case 0n:
      match gp:
        case (world, acc):
          (world, acc)
    case 1n+p:
      match gp:
        case (world, acc):
          d = is_dirty_y(mask, y)
          +cells = U32.mul(Grid.size(), Grid.size())
          +last = U32.sub(cells, 1)
          +cfuel = Bool.pick(Nat, d, U32.to_nat(last), 0n)
          +base = U32.shln(y, 12n)
          +lasti = U32.add(base, last)
          q = Array.get(U32, world, lasti)
          scan_rows(p, scan_row(cfuel, q, base, last, acc), U32.sub(y, 1), mask)

def dirty_todo(r: Array<U32> & Mask) -> Array<U32> & List<&2, U32>:
  match r:
    case (world, mask):
      scan_rows(U32.to_nat(Grid.size()), (world, Nil{}), U32.sub(Grid.size(), 1), mask)
