import Base
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
import ./src/tick.bend as Tick
import ./src/count.bend as Count
import ./src/fall.bend as Fall

law sanity:
  {U32.add(2, 3) == 5 : U32}

law grid_volume:
  {U32.mul(Grid.size(), U32.mul(Grid.size(), Grid.size())) == Grid.volume() : U32}

law cell_full_mask:
  {Cell.encode(31, 63, 1, 31, 63) == 8388607 : U32}

law cell_reserved_bits:
  {U32.and(Cell.encode(31, 63, 1, 31, 63), 4286578688) == 0 : U32}

law index_roundtrip:
  for i: U32
  {Grid.index(Grid.ix(i), Grid.iy(i), Grid.iz(i)) == U32.and(i, 262143) : U32}

law cell_roundtrip:
  for w: U32
  {Cell.reencode(w) == U32.and(w, 8388607) : U32}

law rock_crumbles_lighter:
  {Pot.dens(Cell.rock()) == Pot.dens(Cell.rubble()) + 50n : Nat}

law sand_sinks_in_water:
  {Pot.dens(Cell.water()) + 20n == Pot.dens(Cell.sand()) : Nat}

law fall_decreases:
  for L: Nat
  for D: Nat
  for G: Nat
  {(Pot.phi(D + (1n + G), L) + Pot.phi_up(D, L)) + (1n + G) == Pot.phi_up(D + (1n + G), L) + Pot.phi(D, L) : Nat}

law crumble_decreases:
  for d: Nat
  for G: Nat
  for L: Nat
  {Pot.phi(d, L) + Pot.phi(1n + G, L) == Pot.phi(d + (1n + G), L) : Nat}

law budget_exhausts:
  for m: Nat
  {Pot.spend(m, m) == 0n : Nat}

law potential_additive:
  for +xs: +List<Nat>
  for +ys: +List<Nat>
  {Settle.suml(Settle.app(xs, ys)) == Nat.add(Settle.suml(xs), Settle.suml(ys)) : Nat}

law fall_lowers_potential:
  for +l: +List<Nat>
  for +r: +List<Nat>
  for D: Nat
  for G: Nat
  for L: Nat
  {Nat.add(Settle.suml(Settle.app(l, Settle.app(Settle.fall_after(D, G, L), r))), G) == Settle.suml(Settle.app(l, Settle.app(Settle.fall_before(D, G, L), r))) : Nat}

law crumble_lowers_potential:
  for +l: +List<Nat>
  for +r: +List<Nat>
  for d: Nat
  for G: Nat
  for L: Nat
  {Nat.add(Settle.suml(Settle.app(l, Settle.app([Pot.phi(d, L)], r))), Pot.phi(G, L)) == Settle.suml(Settle.app(l, Settle.app([Pot.phi(Nat.add(d, G), L)], r))) : Nat}

law strict_events_bounded:
  for +xs: +List<Nat>
  {Settle.suml(Settle.incs(xs)) == Nat.add(Settle.len(xs), Settle.suml(xs)) : Nat}

law settling_budget:
  for p: Nat
  {Settle.burn(p, p) == 0n : Nat}

law list_set_split:
  for +l: +List<Nat>
  for +r: +List<Nat>
  for n: Nat
  for v: Nat
  {List.set(&2, Nat, Settle.app(l, r), n, v) == Bool.pick(List<&2, Nat>, Nat.is_lt(n, Settle.len(l)), Settle.app(List.set(&2, Nat, l, n, v), r), Settle.app(l, List.set(&2, Nat, r, Nat.sub(n, Settle.len(l)), v))) : List<&2, Nat>}

law list_set_sum:
  for +l: +List<Nat>
  for x: Nat
  for +r: +List<Nat>
  for v: Nat
  {Nat.add(Settle.suml(Settle.app(l, v <> r)), x) == Nat.add(Settle.suml(Settle.app(l, x <> r)), v) : Nat}

law parity_flip_succ:
  for x: U32
  {Parity.par32(U32.add(x, 1)) == Bool.not(Parity.par32(x)) : Bool}

law parity_flip_pred:
  for x: U32
  {Parity.par32(U32.add(x, 4294967295)) == Bool.not(Parity.par32(x)) : Bool}

law neighbor_x_parity:
  for i: U32
  for dx: U32
  {Parity.par32(Grid.ix(Grid.neighbor(i, dx, 0, 0))) == Bool.xor(Parity.par32(Grid.ix(i)), Parity.par32(dx)) : Bool}

law neighbor_y_parity:
  for i: U32
  for dy: U32
  {Parity.par32(Grid.iy(Grid.neighbor(i, 0, dy, 0))) == Bool.xor(Parity.par32(Grid.iy(i)), Parity.par32(dy)) : Bool}

law neighbor_z_parity:
  for i: U32
  for dz: U32
  {Parity.par32(Grid.iz(Grid.neighbor(i, 0, 0, dz))) == Bool.xor(Parity.par32(Grid.iz(i)), Parity.par32(dz)) : Bool}

law low6_add_independent:
  for a: U32
  for b: U32
  {U32.and(U32.add(a, b), 63) == U32.and(U32.add(U32.and(a, 63), U32.and(b, 63)), 63) : U32}

law dir_phi_cancel:
  for d: Priority.Dir
  for x: U32
  {Priority.phi(Priority.dir_neg(d), Priority.phi(d, x)) == U32.and(x, 63) : U32}

law neighbor_cancel:
  for i: U32
  for a: Priority.Dir
  for b: Priority.Dir
  for c: Priority.Dir
  {Grid.neighbor(Grid.neighbor(i, Priority.dir_val(a), Priority.dir_val(b), Priority.dir_val(c)), Priority.dir_val(Priority.dir_neg(a)), Priority.dir_val(Priority.dir_neg(b)), Priority.dir_val(Priority.dir_neg(c))) == U32.and(i, 262143) : U32}

law scan_order_total:
  for a: U32
  for b: U32
  {Bool.or(Bool.or(U32.is_lt(a, b), U32.is_gt(a, b)), U32.is_eq(a, b)) == True{} : Bool}

law swap_refines_array:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  for +v: U32
  {Refine.unpack(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, v))) == Refine.swap_m(t, n, i, v) : Refine.PT}

law array_swap_pots:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  for +v: U32
  {Settle.to_pots(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, v)), base, n) == Refine.pots_swap_m(t, base, n, i, v) : +List<Nat>}

law swap_lowers_phi:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  for +v: U32
  {Nat.add(Settle.suml(Settle.to_pots(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, v)), base, n)), Refine.nfst(Refine.chg_m(t, base, n, i, v))) == Nat.add(Settle.suml(Settle.to_pots(Refine.pack(t), base, n)), Refine.nsnd(Refine.chg_m(t, base, n, i, v))) : Nat}

law material_encode:
  for m: U32
  for c: U32
  for a: U32
  for s: U32
  for f: U32
  {Cell.material(Cell.encode(m, c, a, s, f)) == U32.and(m, 31) : U32}

law support_write_preserves_pot:
  for +w: U32
  for +s: U32
  for +i: U32
  {Settle.pot_at(Ops.set_support(w, s), i) == Settle.pot_at(w, i) : Nat}

law fall_write_preserves_pot:
  for +w: U32
  for +i: U32
  {Settle.pot_at(Ops.set_fall0(w), i) == Settle.pot_at(w, i) : Nat}

law mov_preserves_pot:
  for +w: U32
  for +i: U32
  {Settle.pot_at(Rules.mov(w), i) == Settle.pot_at(w, i) : Nat}

law crumble_lowers_pot:
  for +w: U32
  for +i: U32
  for +h: {Cell.material(w) == 3 : U32}
  {Nat.add(Settle.pot_at(Ops.crush_word(w), i), Nat.mul(50n, U32.to_nat(Grid.iy(i)))) == Settle.pot_at(w, i) : Nat}

law point_write_lowers:
  for +l: +List<Nat>
  for +v: Nat
  for +g: Nat
  for +r: +List<Nat>
  {Nat.add(Settle.suml(Settle.app(l, Settle.app([v], r))), g) == Settle.suml(Settle.app(l, Settle.app([v + g], r))) : Nat}

law array_support_write_preserves_phi:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  for +s: U32
  {Settle.suml(Settle.to_pots(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Ops.set_support(Tick.tget(t, n, i), s))), base, n)) == Settle.suml(Settle.to_pots(Refine.pack(t), base, n)) : Nat}

law array_crumble_lowers_phi:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  for +hm: {Cell.material(Tick.tget(t, n, i)) == 3 : U32}
  {Nat.add(Settle.suml(Settle.to_pots(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Ops.crush_word(Tick.tget(t, n, i)))), base, n)), Tick.crush_gap(t, base, n, i)) == Settle.suml(Settle.to_pots(Refine.pack(t), base, n)) : Nat}

law wake_preserves_pot:
  for +w: U32
  for +i: U32
  {Settle.pot_at(Cell.activate(w), i) == Settle.pot_at(w, i) : Nat}

law deactivate_preserves_pot:
  for +w: U32
  for +i: U32
  {Settle.pot_at(Cell.deactivate(w), i) == Settle.pot_at(w, i) : Nat}

law array_point_write_preserves_count:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  for +v: U32
  for +h: {Count.nempty(v) == Count.nempty(Tick.tget(t, n, i)) : Nat}
  {Settle.suml(Count.to_counts(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, v)))) == Settle.suml(Count.to_counts(Refine.pack(t))) : Nat}

law array_point_write_count_balance:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  for +v: U32
  {Nat.add(Settle.suml(Count.to_counts(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, v)))), Refine.nfst(Count.cnt_chg_m(t, n, i, v))) == Nat.add(Settle.suml(Count.to_counts(Refine.pack(t))), Refine.nsnd(Count.cnt_chg_m(t, n, i, v))) : Nat}

law array_mov_swap_preserves_count:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  for +j: U32
  {Settle.suml(Count.to_counts(Refine.afst(Array.swap.go(U32, Refine.afst(Array.swap.go(U32, Refine.pack(t), n, j, Rules.mov(Tick.tget(t, n, i)))), n, i, Tick.tget(t, n, j))))) == Settle.suml(Count.to_counts(Refine.pack(t))) : Nat}

law array_support_write_preserves_count:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  for +s: U32
  {Settle.suml(Count.to_counts(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Ops.set_support(Tick.tget(t, n, i), s))))) == Settle.suml(Count.to_counts(Refine.pack(t))) : Nat}

law array_fall_write_preserves_count:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  {Settle.suml(Count.to_counts(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Ops.set_fall0(Tick.tget(t, n, i)))))) == Settle.suml(Count.to_counts(Refine.pack(t))) : Nat}

law array_mov_write_preserves_count:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  {Settle.suml(Count.to_counts(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Rules.mov(Tick.tget(t, n, i)))))) == Settle.suml(Count.to_counts(Refine.pack(t))) : Nat}

law array_wake_write_preserves_count:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  {Settle.suml(Count.to_counts(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Cell.activate(Tick.tget(t, n, i)))))) == Settle.suml(Count.to_counts(Refine.pack(t))) : Nat}

law array_deactivate_write_preserves_count:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  {Settle.suml(Count.to_counts(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Cell.deactivate(Tick.tget(t, n, i)))))) == Settle.suml(Count.to_counts(Refine.pack(t))) : Nat}

law word_cmp_eq_reflect:
  for +n: Nat
  for +x: Word(n)
  for +y: Word(n)
  for +h: {Cmp.is_eq(Word.cmp(n, x, y)) == True{} : Bool}
  {x == y : Word(n)}

law u32_cmp_eq_reflect:
  for +a: U32
  for +b: U32
  for +h: {U32.is_eq(a, b) == True{} : Bool}
  {a == b : U32}

law guarded_crush_lowers_pot:
  for +w: U32
  for +i: U32
  {Nat.add(Settle.pot_at(Ops.crush_if_rock(w), i), Bool.pick(Nat, U32.is_eq(Cell.material(w), 3), Nat.mul(50n, U32.to_nat(Grid.iy(i))), 0n)) == Settle.pot_at(w, i) : Nat}

law array_guarded_crush_lowers_phi:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  {Nat.add(Settle.suml(Settle.to_pots(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Ops.crush_if_rock(Tick.tget(t, n, i)))), base, n)), Tick.guard_gap(t, base, n, i)) == Settle.suml(Settle.to_pots(Refine.pack(t), base, n)) : Nat}

law array_activate_write_preserves_phi:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  {Settle.suml(Settle.to_pots(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Cell.activate(Tick.tget(t, n, i)))), base, n)) == Settle.suml(Settle.to_pots(Refine.pack(t), base, n)) : Nat}

law sup_mirror_preserves_phi:
  for fuel: Nat
  for +t: Refine.PT
  for +n: U32
  for +gated: Bool
  {Tick.sup_phi(Tick.sup_pass_m(fuel, t, n, gated), 0, n) == Settle.suml(Settle.to_pots(Refine.pack(t), 0, n)) : Nat}

law array_mov_cross:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  for +j: U32
  {Nat.add(Settle.suml(Settle.to_pots(Fall.mov_array(t, n, i, j), base, n)), Fall.mov_S(t, base, n, i, j)) == Nat.add(Settle.suml(Settle.to_pots(Refine.pack(t), base, n)), Fall.mov_T(t, base, n, i, j)) : Nat}

law array_mov_lowers_phi:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  for +j: U32
  for +hg: {Nat.add(Fall.mov_T(t, base, n, i, j), Fall.fall_gap(t, base, n, i, j)) == Fall.mov_S(t, base, n, i, j) : Nat}
  {Nat.add(Settle.suml(Settle.to_pots(Fall.mov_array(t, n, i, j), base, n)), Fall.fall_gap(t, base, n, i, j)) == Settle.suml(Settle.to_pots(Refine.pack(t), base, n)) : Nat}

law array_mov_lowers_phi_regime:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  for +j: U32
  for +hge: {Nat.is_ge(Fall.mov_S(t, base, n, i, j), Fall.mov_T(t, base, n, i, j)) == True{} : Bool}
  {Nat.add(Settle.suml(Settle.to_pots(Fall.mov_array(t, n, i, j), base, n)), Fall.fall_gap(t, base, n, i, j)) == Settle.suml(Settle.to_pots(Refine.pack(t), base, n)) : Nat}
