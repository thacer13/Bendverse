import Base
import ./parity.bend as Parity
import ./priority.bend as Priority
import ./grid.bend as Grid
import ./rules.bend as Rules

# ------------------------------------------------------------------ V3c-0 (partial)
# Engine-level target separation (A.57/A.58): every cell the rule fold *writes* is
# a neighbor with `dy = -1` (the retired `Rules.step` and its V0-1 successor
# `Rules.plan` write the same targets), so the target's `y`-parity is the opposite
# of the evaluated cell's. The phase color is
# `color_of(i) = ix(i)&1 | (iy(i)&1)<<1 | (iz(i)&1)<<2`, so a flipped `iy`
# parity flips the color's `y` bit: a phase's writes never land on a cell whose
# color equals the phase's in the `y` bit. (The side cells `side_index` reads
# have `dy = 0` and keep the parity — they are read, never written.)
#
# This is the provable fragment. The full *color* separation (all three bits, so
# "the target's color differs, not just its `y` bit") additionally needs the
# `color_of` bit extraction — `par32(shr 1 (color_of i)) = par32(iy i)` and the
# `U32.is_ne` reflection to turn "differs in the `y` bit" into "colors differ";
# that is V3c-0's remaining half, recorded in `PLAN.md` §5.3 (`G3`).

# `par32(iy(neighbor(i, dx, dy, dz))) = xor(par32(iy i), par32 dy)`, for any
# offsets — the `y` component of the general neighbor parity (`Priority`'s
# `u32_iy_neighbor_full` lifted through `par32`).
def iy_par(+i: U32, +dx: U32, +dy: U32, +dz: U32)
  -> {Parity.par32(Grid.iy(Grid.neighbor(i, dx, dy, dz))) == Bool.xor(Parity.par32(Grid.iy(i)), Parity.par32(dy)) : Bool}:
  +addv = U32.add(Grid.iy(i), dy)
  +e1 = Priority.u32_iy_neighbor_full(i, dx, dy, dz)
  +e2 = Parity.par32_mask6(addv)
  +e3 = Parity.par32_add(Grid.iy(i), dy)
  Equal.trans(Bool,
    Parity.par32(Grid.iy(Grid.neighbor(i, dx, dy, dz))),
    Parity.par32(U32.and(addv, 63)),
    Bool.xor(Parity.par32(Grid.iy(i)), Parity.par32(dy)),
    Equal.cong(U32, Bool, v => Parity.par32(v),
      Grid.iy(Grid.neighbor(i, dx, dy, dz)), U32.and(addv, 63), e1),
    Equal.trans(Bool,
      Parity.par32(U32.and(addv, 63)),
      Parity.par32(addv),
      Bool.xor(Parity.par32(Grid.iy(i)), Parity.par32(dy)),
      e2, e3))

def xor_true(b: Bool) -> {Bool.xor(b, True{}) == Bool.not(b) : Bool}:
  match b:
    case True{}: {==}
    case False{}: {==}

def xor_false(b: Bool) -> {Bool.xor(b, False{}) == b : Bool}:
  match b:
    case True{}: {==}
    case False{}: {==}

def par_neg1_true() -> {Parity.par32(4294967295) == True{} : Bool}:
  {==}

def par_0_false() -> {Parity.par32(0) == False{} : Bool}:
  {==}

# A `dy = -1` neighbor (every write target: `below`, `diag_index`) flips the
# `y`-parity.
def neighbor_y_flip(+i: U32, +dx: U32, +dz: U32)
  -> {Parity.par32(Grid.iy(Grid.neighbor(i, dx, 4294967295, dz))) == Bool.not(Parity.par32(Grid.iy(i))) : Bool}:
  Equal.trans(Bool,
    Parity.par32(Grid.iy(Grid.neighbor(i, dx, 4294967295, dz))),
    Bool.xor(Parity.par32(Grid.iy(i)), Parity.par32(4294967295)),
    Bool.not(Parity.par32(Grid.iy(i))),
    iy_par(i, dx, 4294967295, dz),
    Equal.trans(Bool,
      Bool.xor(Parity.par32(Grid.iy(i)), Parity.par32(4294967295)),
      Bool.xor(Parity.par32(Grid.iy(i)), True{}),
      Bool.not(Parity.par32(Grid.iy(i))),
      Equal.cong(Bool, Bool, t => Bool.xor(Parity.par32(Grid.iy(i)), t),
        Parity.par32(4294967295), True{}, par_neg1_true()),
      xor_true(Parity.par32(Grid.iy(i)))))

# A `dy = 0` neighbor (the side cell `side_index` reads) keeps the `y`-parity.
def neighbor_y_keep(+i: U32, +dx: U32, +dz: U32)
  -> {Parity.par32(Grid.iy(Grid.neighbor(i, dx, 0, dz))) == Parity.par32(Grid.iy(i)) : Bool}:
  Equal.trans(Bool,
    Parity.par32(Grid.iy(Grid.neighbor(i, dx, 0, dz))),
    Bool.xor(Parity.par32(Grid.iy(i)), Parity.par32(0)),
    Parity.par32(Grid.iy(i)),
    iy_par(i, dx, 0, dz),
    Equal.trans(Bool,
      Bool.xor(Parity.par32(Grid.iy(i)), Parity.par32(0)),
      Bool.xor(Parity.par32(Grid.iy(i)), False{}),
      Parity.par32(Grid.iy(i)),
      Equal.cong(Bool, Bool, t => Bool.xor(Parity.par32(Grid.iy(i)), t),
        Parity.par32(0), False{}, par_0_false()),
      xor_false(Parity.par32(Grid.iy(i)))))

# The `Rules`-level write target `below` (sel 6 and sel 22) flips the `y`-parity.
# The diagonal/side targets are `match`-guarded on `k` (with an `_ -> i` branch),
# so their per-branch statements are V3c-0's remainder (they need the engine's
# `k < 4` bound); `below` has no such match and reduces directly.
def below_y_flip(+i: U32)
  -> {Parity.par32(Grid.iy(Grid.below(i))) == Bool.not(Parity.par32(Grid.iy(i))) : Bool}:
  neighbor_y_flip(i, 0, 0)

