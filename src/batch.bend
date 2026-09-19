import Base
import ./grid.bend as Grid
import ./priority.bend as Priority
import ./rules.bend as Rules

# ------------------------------------------------------------------ V0-3
# Target-map injectivity for a (colour × direction) batch.
#
# Rule 4's direction batch fixes the displacement `(dx, dy, dz)`, so its target
# map is the *translation* `i |-> Grid.neighbor(i, dx, dy, dz)`. On the 64³
# torus a translation is a bijection, and `Priority.neighbor_cancel` already
# proves the two-sided inverse: `neighbor(neighbor(i, d), -d) = i & 262143`.
# Composing an assumed target collision with that inverse collapses it to a
# source collision, i.e. the translation is injective — "distinct cells have
# distinct targets", the half of rule 4 that makes a batch collision-free with
# no coordination (the other half, the colour partition, is `Grid.color_of`'s
# independence property).
#
# Stated over `Priority.Dir` because every engine displacement is `0`, `+1` or
# `-1` (below, and the four slides), which is exactly what `Dir` closes over.
# The live engine's `Rules.Dir4` (V0-3's other landing) instantiates these.

def move_inj(
  +i: U32, +j: U32,
  +a: Priority.Dir, +b: Priority.Dir, +c: Priority.Dir,
  +h: {Grid.neighbor(i, Priority.dir_val(a), Priority.dir_val(b), Priority.dir_val(c)) == Grid.neighbor(j, Priority.dir_val(a), Priority.dir_val(b), Priority.dir_val(c)) : U32}
) -> {U32.and(i, 262143) == U32.and(j, 262143) : U32}:
  +ni = Grid.neighbor(i, Priority.dir_val(a), Priority.dir_val(b), Priority.dir_val(c))
  +nj = Grid.neighbor(j, Priority.dir_val(a), Priority.dir_val(b), Priority.dir_val(c))
  +na = Priority.dir_val(Priority.dir_neg(a))
  +nb = Priority.dir_val(Priority.dir_neg(b))
  +nc = Priority.dir_val(Priority.dir_neg(c))
  +hh = Equal.cong(U32, U32, t => Grid.neighbor(t, na, nb, nc), ni, nj, h)
  +ci = Priority.neighbor_cancel(i, a, b, c)
  +cj = Priority.neighbor_cancel(j, a, b, c)
  Equal.trans(U32,
    U32.and(i, 262143), Grid.neighbor(ni, na, nb, nc),
    U32.and(j, 262143),
    Equal.sym(U32, Grid.neighbor(ni, na, nb, nc), U32.and(i, 262143), ci),
    Equal.trans(U32, Grid.neighbor(ni, na, nb, nc), Grid.neighbor(nj, na, nb, nc), U32.and(j, 262143), hh, cj))

# The drop batch: `below` is the translation `(0, -1, 0)`.
def below_inj(+i: U32, +j: U32, +h: {Grid.below(i) == Grid.below(j) : U32})
  -> {U32.and(i, 262143) == U32.and(j, 262143) : U32}:
  move_inj(i, j, Priority.Dno{}, Priority.Ddn{}, Priority.Dno{}, h)

# The four slide batches: `diag4(., k)` is the translation
# `(dir_dx k, -1, dir_dz k)`. Each `Dir4` constructor selects one and the
# match is total, so the batch map is injective for every engine direction.
def diag4_inj(+i: U32, +j: U32, +k: Rules.Dir4, +h: {Rules.diag4(i, k) == Rules.diag4(j, k) : U32})
  -> {U32.and(i, 262143) == U32.and(j, 262143) : U32}:
  match k:
    case Rules.K0{}: move_inj(i, j, Priority.Ddn{}, Priority.Ddn{}, Priority.Dno{}, h)
    case Rules.K1{}: move_inj(i, j, Priority.Dup{}, Priority.Ddn{}, Priority.Dno{}, h)
    case Rules.K2{}: move_inj(i, j, Priority.Dno{}, Priority.Ddn{}, Priority.Ddn{}, h)
    case Rules.K3{}: move_inj(i, j, Priority.Dno{}, Priority.Ddn{}, Priority.Dup{}, h)
