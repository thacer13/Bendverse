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
import ./src/order.bend as Order
import ./src/refine.bend as Refine
import ./src/ops.bend as Ops
import ./src/rules.bend as Rules
import ./src/writepot.bend as WP

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

def Laws.list_set_split(l, r, n, v):
  Settle.set_append(l, r, n, v)

def Laws.list_set_sum(l, x, r, v):
  Settle.set_sum(l, x, r, v)

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

def Laws.neighbor_cancel(i, a, b, c):
  Priority.neighbor_cancel(i, a, b, c)

def Laws.scan_order_total(a, b):
  Order.u32_cmp_total(a, b)

def Laws.swap_refines_array(t, n, i, v):
  Refine.swap_ref(t, n, i, v)

def Laws.array_swap_pots(t, base, n, i, v):
  Refine.array_swap_pots(t, base, n, i, v)

def Laws.swap_lowers_phi(t, base, n, i, v):
  Refine.array_swap_decreases(t, base, n, i, v)

def Laws.material_encode(m, c, a, s, f):
  WP.mat_encode(m, c, a, s, f)

def Laws.support_write_preserves_pot(w, s, i):
  WP.pot_set_support(w, s, i)

def Laws.fall_write_preserves_pot(w, i):
  WP.pot_set_fall0(w, i)

def Laws.mov_preserves_pot(w, i):
  WP.pot_mov(w, i)

def Laws.crumble_lowers_pot(w, i, h):
  WP.pot_crush_rock(w, i, h)

def Laws.point_write_lowers(l, v, g, r):
  WP.point_write_lowers(l, v, g, r)
