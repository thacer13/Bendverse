import Base
import ./LAWS.bend as Laws
import ./src/bits.bend as Bits
import ./src/grid.bend as Grid
import ./src/cell.bend as Cell
import ./src/cw.bend as Cw
import ./src/potential.bend as Pot
import ./src/settle.bend as Settle
import ./src/parity.bend as Parity
import ./src/mod.bend as Mod
import ./src/priority.bend as Priority
import ./src/order.bend as Order
import ./src/refine.bend as Refine
import ./src/ops.bend as Ops
import ./src/rules.bend as Rules
import ./src/sim.bend as Sim
import ./src/dirty.bend as Dirty
import ./src/writepot.bend as WP
import ./src/tick.bend as Tick
import ./src/count.bend as Count
import ./src/g5.bend as G5
import ./src/fall.bend as Fall
import ./src/step.bend as Step
import ./src/phase.bend as Phase
import ./src/batch.bend as Batch
import ./src/commit.bend as Commit
import ./src/v3cw.bend as V3cw
import ./src/color.bend as Color
import ./src/word.bend as WR
import ./src/selector.bend as Selector
import ./src/gscale.bend as Gscale
import ./src/winset.bend as Winset

# This import list is the coverage root: `bend PROOF.bend` checks every module
# reachable from here, so an import whose *alias* looks unused may be the only
# reason that module is verified at all. Do not "tidy" these away (A.62).

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
  Pot.fall_decreases(D, Nat.add(1n, G), L)

def Laws.crumble_decreases(d, G, L):
  Pot.crumble_decreases(d, Nat.add(1n, G), L)

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

def Laws.array_support_write_preserves_phi(t, base, n, i, s):
  Tick.array_support_write(t, base, n, i, s)

def Laws.array_crumble_lowers_phi(t, base, n, i, hm):
  Tick.array_crumble_lowers(t, base, n, i, hm)

def Laws.wake_preserves_pot(w, i):
  WP.pot_or_hi(w, i)

def Laws.deactivate_preserves_pot(w, i):
  WP.pot_and_hi(w, i)

def Laws.array_point_write_preserves_count(t, n, i, v, h):
  Count.array_point_write_preserves_count(t, n, i, v, h)

def Laws.array_point_write_count_balance(t, n, i, v):
  Count.array_point_write_count_balance(t, n, i, v)

def Laws.array_mov_swap_preserves_count(t, n, i, j):
  Count.array_mov_swap_preserves_count(t, n, i, j)

def Laws.array_support_write_preserves_count(t, n, i, s):
  Count.array_support_write_preserves_count(t, n, i, s)

def Laws.array_fall_write_preserves_count(t, n, i):
  Count.array_fall_write_preserves_count(t, n, i)

def Laws.array_mov_write_preserves_count(t, n, i):
  Count.array_mov_write_preserves_count(t, n, i)

def Laws.array_wake_write_preserves_count(t, n, i):
  Count.array_wake_write_preserves_count(t, n, i)

def Laws.array_deactivate_write_preserves_count(t, n, i):
  Count.array_deactivate_write_preserves_count(t, n, i)

def Laws.word_cmp_eq_reflect(n, x, y, h):
  WR.w_cmp_eq(n, x, y, h)

def Laws.u32_cmp_eq_reflect(a, b, h):
  WR.u32_cmp_eq(a, b, h)

def Laws.guarded_crush_lowers_pot(w, i):
  WP.pot_crush_guarded(w, i)

def Laws.array_guarded_crush_lowers_phi(t, base, n, i):
  Tick.array_guarded_crush_lowers_auto(t, base, n, i)

def Laws.array_activate_write_preserves_phi(t, base, n, i):
  Tick.array_activate_write(t, base, n, i)

def Laws.sup_mirror_preserves_phi(fuel, t, n, gated):
  Tick.sup_m_preserves(fuel, t, Tick.tget(t, n, 0), Tick.S0{}, 0, gated, n, U32.to_nat(3), 0)

def Laws.array_mov_cross(t, base, n, i, j):
  Fall.array_mov_cross(t, base, n, i, j)

def Laws.array_mov_lowers_phi(t, base, n, i, j, hg):
  Fall.array_mov_lowers_phi(t, base, n, i, j, hg)

def Laws.array_mov_lowers_phi_regime(t, base, n, i, j, hge):
  Fall.array_mov_lowers_phi_regime(t, base, n, i, j, hge)

def Laws.step_mirror_balance(fuel, t, n, c):
  Step.step_preserves(fuel, t, Tick.tget(t, n, 0), Step.E0{}, 0, c, 0, 0, U32.to_nat(3), n, 0)

def Laws.below_write_flips_y_phase(i):
  Phase.below_y_flip(i)

def Laws.batch_target_injective(i, j, a, b, c, h):
  Batch.move_inj(i, j, a, b, c, h)

def Laws.diag_target_injective(i, j, k, h):
  Batch.diag4_inj(i, j, k, h)

def Laws.diag_write_flips_y_phase(i, k):
  Phase.diag4_y_flip(i, k)

def Laws.color_of_bit0(i):
  Color.color_bit0(i)

def Laws.color_of_bit1(i):
  Color.color_bit1(i)

def Laws.color_of_bit2(i):
  Color.color_bit2(i)

def Laws.color_target_x_par(i, dx, dz):
  Color.target_x_par(i, dx, dz)

def Laws.color_target_z_par(i, dx, dz):
  Color.target_z_par(i, dx, dz)

def Laws.color_collision_x_par(i, j, dxi, dzi, dxj, dzj, hc, ht):
  Color.same_color_target_x_par(i, j, dxi, dzi, dxj, dzj, hc, ht)

def Laws.color_collision_z_par(i, j, dxi, dzi, dxj, dzj, hc, ht):
  Color.same_color_target_z_par(i, j, dxi, dzi, dxj, dzj, hc, ht)

def Laws.point_writes_commute(t, n, i, j, v, w, hne):
  Commit.swap_m_comm(t, n, i, j, v, w, hne)

def Laws.write_selector_preserves_phi(op, t, base, n, i):
  Selector.array_write_preserves_phi(op, t, base, n, i)

def Laws.write_selector_preserves_count(op, t, n, i):
  Selector.array_write_preserves_count(op, t, n, i)

def Laws.array_fall_write_preserves_phi(t, base, n, i):
  Selector.array_write_preserves_phi(Rules.OFall0{}, t, base, n, i)

def Laws.array_mov_write_preserves_phi(t, base, n, i):
  Selector.array_write_preserves_phi(Rules.OMov{}, t, base, n, i)

def Laws.array_deactivate_write_preserves_phi(t, base, n, i):
  Selector.array_write_preserves_phi(Rules.ODeact{}, t, base, n, i)

def Laws.write_effect_phi_balance(op, t, base, n, i, src):
  Selector.array_op_phi_balance(op, t, base, n, i, src)

def Laws.write_effect_count_balance(op, t, n, i, src):
  Selector.array_op_count_balance(op, t, n, i, src)

def Laws.g5_read_get_go(t, n, i):
  G5.g5_tget_get_go(t, n, i)

def Laws.g5_size_pack(t):
  G5.g5_size_pack(t)

def Laws.g5_read_get(t, i):
  G5.g5_read_get(t, i)

def Laws.g5_tget_swap(t, n, i, v):
  G5.g5_tget_swap(t, n, i, v)

def Laws.v3c_write_past_fold(ws, t, n, i, v, hne):
  Commit.v3c_write_past_fold(ws, t, n, i, v, hne)

def Laws.v3c_fold_commutes(xs, ys, t, n, hpn):
  Commit.v3c_fold_commutes(xs, ys, t, n, hpn)

def Laws.v3c_ne_idx_sound(t, n, i, j, he):
  Commit.v3c_ne_idx_sound(t, n, i, j, he)

def Laws.g5_twidth_pow(t):
  G5.g5_twidth_pow(t)

def Laws.g5_and_mask_id(t, i, h):
  G5.g5_and_mask_id(t, i, h)

def Laws.g5_read_get_bare(t, i, h):
  +em = G5.g5_read_get(t, i)
  +eid = G5.g5_and_mask_id(t, i, h)
  +eidx = Equal.cong(U32, U32, x => Tick.tget(t, G5.g5_twidth(t), x),
    U32.and(i, U32.sub(G5.g5_twidth(t), 1)), i, eid)
  +epair = Equal.cong(U32, Array<U32> & U32, y => (Refine.pack(t), y),
    Tick.tget(t, G5.g5_twidth(t), U32.and(i, U32.sub(G5.g5_twidth(t), 1))),
    Tick.tget(t, G5.g5_twidth(t), i), eidx)
  Equal.trans(Array<U32> & U32,
    Array.get(U32, Refine.pack(t), i),
    (Refine.pack(t), Tick.tget(t, G5.g5_twidth(t), U32.and(i, U32.sub(G5.g5_twidth(t), 1)))),
    (Refine.pack(t), Tick.tget(t, G5.g5_twidth(t), i)),
    em, epair)
def Laws.v3c_ne_idx_sep(xs, ys, n, i, j, hzi, hzj):
  Commit.v3c_ne_idx_sep(xs, ys, n, i, j, hzi, hzj)

def Laws.v3c_ne_idx_same_l(xs, ys, n, i, j, hzi, hzj):
  Commit.v3c_ne_idx_same_l(xs, ys, n, i, j, hzi, hzj)

def Laws.v3c_ne_idx_same_r(xs, ys, n, i, j, hzi, hzj):
  Commit.v3c_ne_idx_same_r(xs, ys, n, i, j, hzi, hzj)

def Laws.g15_wake_step_inert(t, n, i, dx, dy, dz, h):
  Equal.cong(Bool, Refine.PT,
    b => Tick.wake_write_m(b, t, n, Grid.neighbor(i, dx, dy, dz)),
    Grid.step_inside(i, dx, dy, dz), False{}, h)
def Laws.v3c_ne_idx_complete(k, i, j, hi, hj, hne):
  Commit.v3c_ne_idx_complete_imp(k, i, j, hi, hj, hne)

def Laws.v3c_ne_idx_exact(k, i, j, hi, hj):
  Commit.v3c_ne_idx_exact(k, i, j, hi, hj)

def Laws.v3cw_commit_fold(ws, t, n, hn, hir):
  V3cw.v3cw_commit_fold(ws, t, n, hn, hir)

def Laws.v3cw_commit_commutes(xs, ys, t, n, hn, hxy, hyx, hpn):
  V3cw.v3cw_commit_commutes(xs, ys, t, n, hn, hxy, hyx, hpn)

def Laws.gscale_cw_x_rt(x, y, z, h):
  match x:
    case U32{xw}:
      match y:
        case U32{yw}:
          match z:
            case U32{zw}:
              +x2 = xw
              +y2 = yw
              +z2 = zw
              +s = Gscale.gscale_cw_x_split(U32{x2}, U32{y2}, U32{z2})
              +g = G5.g5_and_mask_id(Commit.v3c_full(14n), U32{x2}, h)
              Equal.trans(U32,
                Cw.cw_global_x(Cw.cw_key(Cw.cw_chunk_of(U32{x2}), Cw.cw_chunk_of(U32{y2}), Cw.cw_chunk_of(U32{z2})), Cw.cw_local(Cw.cw_local_of(U32{x2}), Cw.cw_local_of(U32{y2}), Cw.cw_local_of(U32{z2}))),
                U32.and(U32{x2}, 16383),
                U32{x2},
                s, g)

def Laws.gscale_cw_y_rt(y, h):
  match y:
    case U32{yw}:
      +y2 = yw
      +s = Gscale.gscale_cw_y_split(U32{y2})
      +g = G5.g5_and_mask_id(Commit.v3c_full(14n), U32{y2}, h)
      Equal.trans(U32,
        Cw.cw_global_y(Cw.cw_key(0, Cw.cw_chunk_of(U32{y2}), 0), Cw.cw_local(0, Cw.cw_local_of(U32{y2}), 0)),
        U32.and(U32{y2}, 16383),
        U32{y2},
        s, g)

def Laws.gscale_cw_z_rt(z, h):
  match z:
    case U32{zw}:
      +z2 = zw
      +s = Gscale.gscale_cw_z_split(U32{z2})
      +g = G5.g5_and_mask_id(Commit.v3c_full(14n), U32{z2}, h)
      Equal.trans(U32,
        Cw.cw_global_z(Cw.cw_key(0, 0, Cw.cw_chunk_of(U32{z2})), Cw.cw_local(0, 0, Cw.cw_local_of(U32{z2}))),
        U32.and(U32{z2}, 16383),
        U32{z2},
        s, g)

def Laws.gscale_cw_key_rt(k, h):
  match k:
    case U32{kw}:
      +k2 = kw
      +s = Gscale.gscale_cw_key_split(U32{k2})
      +g = G5.g5_and_mask_id(Commit.v3c_full(30n), U32{k2}, h)
      Equal.trans(U32,
        Cw.cw_key(Cw.cw_key_x(U32{k2}), Cw.cw_key_y(U32{k2}), Cw.cw_key_z(U32{k2})),
        U32.and(U32{k2}, 1073741823),
        U32{k2},
        s, g)

def Laws.gscale_cw_local_rt(l, h):
  match l:
    case U32{lw}:
      +l2 = lw
      +s = Gscale.gscale_cw_local_split(U32{l2})
      +g = G5.g5_and_mask_id(Commit.v3c_full(12n), U32{l2}, h)
      Equal.trans(U32,
        Cw.cw_local(Cw.cw_local_x(U32{l2}), Cw.cw_local_y(U32{l2}), Cw.cw_local_z(U32{l2})),
        U32.and(U32{l2}, 4095),
        U32{l2},
        s, g)

def Laws.gscale_cw_y_rt_full(x, y, z, h):
  match x:
    case U32{xw}:
      match y:
        case U32{yw}:
          match z:
            case U32{zw}:
              +x2 = xw
              +y2 = yw
              +z2 = zw
              +s = Gscale.gscale_cw_y_split_full(U32{x2}, U32{y2}, U32{z2})
              +g = G5.g5_and_mask_id(Commit.v3c_full(14n), U32{y2}, h)
              Equal.trans(U32,
                Cw.cw_global_y(Cw.cw_key(Cw.cw_chunk_of(U32{x2}), Cw.cw_chunk_of(U32{y2}), Cw.cw_chunk_of(U32{z2})), Cw.cw_local(Cw.cw_local_of(U32{x2}), Cw.cw_local_of(U32{y2}), Cw.cw_local_of(U32{z2}))),
                U32.and(U32{y2}, 16383),
                U32{y2},
                s, g)

def Laws.gscale_cw_z_rt_full(x, y, z, h):
  match x:
    case U32{xw}:
      match y:
        case U32{yw}:
          match z:
            case U32{zw}:
              +x2 = xw
              +y2 = yw
              +z2 = zw
              +s = Gscale.gscale_cw_z_split_full(U32{x2}, U32{y2}, U32{z2})
              +g = G5.g5_and_mask_id(Commit.v3c_full(14n), U32{z2}, h)
              Equal.trans(U32,
                Cw.cw_global_z(Cw.cw_key(Cw.cw_chunk_of(U32{x2}), Cw.cw_chunk_of(U32{y2}), Cw.cw_chunk_of(U32{z2})), Cw.cw_local(Cw.cw_local_of(U32{x2}), Cw.cw_local_of(U32{y2}), Cw.cw_local_of(U32{z2}))),
                U32.and(U32{z2}, 16383),
                U32{z2},
                s, g)

def Laws.winset_mem_insert_self(k, s):
  +e = Commit.v3c_is_eq_refl(k)
  +c = Equal.cong(Bool, Bool, b => Bool.or(b, Winset.winset_mem(k, s)), U32.is_eq(k, k), True{}, e)
  Equal.trans(Bool, Bool.or(U32.is_eq(k, k), Winset.winset_mem(k, s)), Bool.or(True{}, Winset.winset_mem(k, s)), True{}, c, {==})

def Laws.winset_mem_insert_other(k2, k, s, h):
  +c = Equal.cong(Bool, Bool, b => Bool.or(b, Winset.winset_mem(k2, s)), U32.is_eq(k2, k), False{}, h)
  Equal.trans(Bool, Bool.or(U32.is_eq(k2, k), Winset.winset_mem(k2, s)), Bool.or(False{}, Winset.winset_mem(k2, s)), Winset.winset_mem(k2, s), c, {==})

def Laws.winset_remove_insert(k, rest):
  +k2 = k
  +rest2 = rest
  +er = Commit.v3c_is_eq_refl(k2)
  +pick = Bool.pick(Winset.Winset, U32.is_eq(k2, k2), Winset.winset_remove(k2, rest2), Winset.WinsetCon{k2, Winset.winset_remove(k2, rest2)})
  Equal.trans(Winset.Winset,
    Winset.winset_remove(k2, Winset.winset_insert(k2, rest2)),
    pick,
    Winset.winset_remove(k2, rest2),
    {==},
    Equal.trans(Winset.Winset,
      pick,
      Bool.pick(Winset.Winset, True{}, Winset.winset_remove(k2, rest2), Winset.WinsetCon{k2, Winset.winset_remove(k2, rest2)}),
      Winset.winset_remove(k2, rest2),
      Equal.cong(Bool, Winset.Winset, b => Bool.pick(Winset.Winset, b, Winset.winset_remove(k2, rest2), Winset.WinsetCon{k2, Winset.winset_remove(k2, rest2)}), U32.is_eq(k2, k2), True{}, er),
      {==}))
