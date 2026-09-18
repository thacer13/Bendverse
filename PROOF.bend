import Base
import ./LAWS.bend as Laws
import ./src/bits.bend as Bits
import ./src/grid.bend as Grid
import ./src/cell.bend as Cell
import ./src/potential.bend as Pot
import ./src/settle.bend as Settle
import ./src/parity.bend as Parity
import ./src/mod.bend as Mod
import ./src/priority.bend as Priority

def Laws.sanity():
  {==}

def Laws.grid_volume():
  {==}

def Laws.cell_full_mask():
  {==}

def Laws.cell_reserved_bits():
  {==}

def Laws.index_roundtrip(i):
  match i:
    case U32{iw}:
      Equal.cong(Word(32n), U32, x => U32{x},
        Bits.model_index(32n, iw),
        Word.and(32n, iw, Bits.mask(32n, 18n)),
        Bits.model_index_rt(iw))

def Laws.cell_roundtrip(w):
  match w:
    case U32{x}:
      Equal.cong(Word(32n), U32, y => U32{y},
        Bits.model_cell(32n, x),
        Word.and(32n, x, Bits.mask(32n, 23n)),
        Bits.model_cell_rt(x))

def Laws.rock_crumbles_lighter():
  {==}

def Laws.sand_sinks_in_water():
  {==}

def Laws.fall_decreases(L, D, G):
  Pot.fall_decreases(D, 1n + G, L)

def Laws.crumble_decreases(d, G, L):
  Pot.crumble_decreases(d, 1n + G, L)

def Laws.budget_exhausts(m):
  Pot.spend_exhausts(m)

def Laws.potential_additive(xs, ys):
  Settle.suml_append(xs, ys)

def Laws.fall_lowers_potential(l, r, D, G, L):
  Settle.fall_lowers_world(l, r, D, G, L)

def Laws.crumble_lowers_potential(l, r, d, G, L):
  Settle.crumble_lowers_world(l, r, d, G, L)

def Laws.strict_events_bounded(xs):
  Settle.suml_incs(xs)

def Laws.settling_budget(p):
  Settle.burn_exhausts(p)

def Laws.parity_flip_succ(x):
  Parity.u32_add_one_flips(x)

def Laws.parity_flip_pred(x):
  Parity.u32_add_ones_flips(x)

def Laws.neighbor_x_parity(i, dx):
  Parity.neighbor_x_par(i, dx)

def Laws.neighbor_y_parity(i, dy):
  Parity.neighbor_y_par(i, dy)

def Laws.neighbor_z_parity(i, dz):
  Parity.neighbor_z_par(i, dz)

def Laws.low6_add_independent(a, b):
  Mod.low6_add_indep(a, b)

def Laws.dir_phi_cancel(d, x):
  Priority.phi_cancel(d, x)
