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
import ./src/g5.bend as G5
import ./src/fall.bend as Fall
import ./src/step.bend as Step
import ./src/phase.bend as Phase
import ./src/commit.bend as Commit
import ./src/v3cw.bend as V3cw
import ./src/selector.bend as Selector
import ./src/cw.bend as Cw

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
  {Pot.dens(Cell.rock()) == Nat.add(Pot.dens(Cell.rubble()), 50n) : Nat}

law sand_sinks_in_water:
  {Nat.add(Pot.dens(Cell.water()), 20n) == Pot.dens(Cell.sand()) : Nat}

law fall_decreases:
  for L: Nat
  for D: Nat
  for G: Nat
  {Nat.add(Nat.add(Pot.phi(Nat.add(D, Nat.add(1n, G)), L), Pot.phi_up(D, L)), Nat.add(1n, G)) == Nat.add(Pot.phi_up(Nat.add(D, Nat.add(1n, G)), L), Pot.phi(D, L)) : Nat}

law crumble_decreases:
  for d: Nat
  for G: Nat
  for L: Nat
  {Nat.add(Pot.phi(d, L), Pot.phi(Nat.add(1n, G), L)) == Pot.phi(Nat.add(d, Nat.add(1n, G)), L) : Nat}

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
  {Nat.add(Settle.suml(Settle.app(l, Settle.app([v], r))), g) == Settle.suml(Settle.app(l, Settle.app([Nat.add(v, g)], r))) : Nat}

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

# RETIRED (A.78 note; retired by V0-1/A.63). `Step.step_pass_m` mirrors
# `Rules.step`, which A.63 removed. The theorem is still true of that old
# selector machine, but it no longer speaks about the engine, so it is **not
# evidence** (`PLAN.md` §3.4, §4.1; gap `G10`). The live write-site enumeration
# is `Rules.plan` and it is the open gap `G14`. Marked here so the law list
# cannot be read as live coverage: a mirror of a shape that no longer exists is
# worse than no mirror (AGENTS.md). Do not extend `step_m`.
law step_mirror_balance:
  for fuel: Nat
  for +t: Refine.PT
  for +n: U32
  for +c: U32
  {Step.step_phi(Step.step_pass_m(fuel, t, n, c), 0, n) == Nat.add(Settle.suml(Settle.to_pots(Refine.pack(t), 0, n)), Step.step_db(Step.step_pass_m(fuel, t, n, c))) : Nat}

law below_write_flips_y_phase:
  for i: U32
  {Parity.par32(Grid.iy(Grid.below(i))) == Bool.not(Parity.par32(Grid.iy(i))) : Bool}

# V0-3 — (colour × direction) batch injectivity (rule 4).
#
# A direction batch fixes the displacement, so its target map is a translation
# and `neighbor_cancel` is its inverse: equal targets force equal (torus) sources.
# The `Dir`-value form is the general lemma; `diag_target_injective` is the
# engine's `Rules.Dir4` slide instantiation and `below_write_flips_y_phase` /
# `diag_write_flips_y_phase` are the colour half (a write target flips the phase
# `y` bit).
law batch_target_injective:
  for i: U32
  for j: U32
  for +a: Priority.Dir
  for +b: Priority.Dir
  for +c: Priority.Dir
  for +h: {Grid.neighbor(i, Priority.dir_val(a), Priority.dir_val(b), Priority.dir_val(c)) == Grid.neighbor(j, Priority.dir_val(a), Priority.dir_val(b), Priority.dir_val(c)) : U32}
  {U32.and(i, 262143) == U32.and(j, 262143) : U32}

law diag_target_injective:
  for i: U32
  for j: U32
  for +k: Rules.Dir4
  for +h: {Rules.diag4(i, k) == Rules.diag4(j, k) : U32}
  {U32.and(i, 262143) == U32.and(j, 262143) : U32}

law diag_write_flips_y_phase:
  for i: U32
  for +k: Rules.Dir4
  {Parity.par32(Grid.iy(Rules.diag4(i, k))) == Bool.not(Parity.par32(Grid.iy(i))) : Bool}

# V0-3b — `color_of` bit extraction (the inverse of the colour packing).
# `Rules.color_of(i) = (ix(i)&1) | ((iy(i)&1)<<1) | ((iz(i)&1)<<2)` packs the
# three coordinate parities; these laws read bit `k` back as coordinate `k`'s
# parity, so equal colours force equal coordinate parities (the colour half of
# the (colour × direction) separation).
law color_of_bit0:
  for i: U32
  {Parity.par32(Rules.color_of(i)) == Parity.par32(Grid.ix(i)) : Bool}

law color_of_bit1:
  for i: U32
  {Parity.par32(U32.shrn(Rules.color_of(i), 1n)) == Parity.par32(Grid.iy(i)) : Bool}

law color_of_bit2:
  for i: U32
  {Parity.par32(U32.shrn(Rules.color_of(i), 2n)) == Parity.par32(Grid.iz(i)) : Bool}

# V0-3b — cross-direction target classification (rule 4, the second half).
# A same-colour target collision forces the two displacement parities to agree:
# `par dx` and `par dz` of the two movers are equal. The only engine directions
# sharing a `(par dx, par dz)` class are the opposite-diagonal pairs (K0/K1 and
# K2/K3); every other cross-direction pair is disjoint, and same-direction pairs
# are injective (V0-3a). This is `is_ne`-free: the claim is about the parity
# bits, not about the `U32` equality.
law color_target_x_par:
  for i: U32
  for dx: U32
  for dz: U32
  {Parity.par32(Grid.ix(Grid.neighbor(i, dx, 4294967295, dz))) == Bool.xor(Parity.par32(Grid.ix(i)), Parity.par32(dx)) : Bool}

law color_target_z_par:
  for i: U32
  for dx: U32
  for dz: U32
  {Parity.par32(Grid.iz(Grid.neighbor(i, dx, 4294967295, dz))) == Bool.xor(Parity.par32(Grid.iz(i)), Parity.par32(dz)) : Bool}

law color_collision_x_par:
  for i: U32
  for j: U32
  for +dxi: U32
  for +dzi: U32
  for +dxj: U32
  for +dzj: U32
  for +hc: {U32.is_eq(Rules.color_of(i), Rules.color_of(j)) == True{} : Bool}
  for +ht: {Grid.neighbor(i, dxi, 4294967295, dzi) == Grid.neighbor(j, dxj, 4294967295, dzj) : U32}
  {Parity.par32(dxi) == Parity.par32(dxj) : Bool}

law color_collision_z_par:
  for i: U32
  for j: U32
  for +dxi: U32
  for +dzi: U32
  for +dxj: U32
  for +dzj: U32
  for +hc: {U32.is_eq(Rules.color_of(i), Rules.color_of(j)) == True{} : Bool}
  for +ht: {Grid.neighbor(i, dxi, 4294967295, dzi) == Grid.neighbor(j, dxj, 4294967295, dzj) : U32}
  {Parity.par32(dzi) == Parity.par32(dzj) : Bool}

# V3c-1 — the schedule-invariance kernel (rule 10, the composition step).
#
# `Rules.plan` reads only the pre-phase state (V0-1), so each evaluated cell's
# write set is independent of the others; what remains for a region-split fold to
# equal the sequential fold is that *applying* the merged writes is
# order-independent. That is exactly this: two point writes at leaves that
# `Commit.ne_idx` separates commute. `Commit.ne_idx` mirrors `swap_m`'s own walk
# (a split at some level, or `False` at a leaf where every index collides); for a
# full tree with in-range indices it is `i != j`, and refining that to the
# engine's `U32.is_eq(i, j) == False` is the open residual recorded in §5.3 (`G3`).
law point_writes_commute:
  for +t: Refine.PT
  for +n: U32
  for i: U32
  for j: U32
  for +v: U32
  for +w: U32
  for +hne: {Commit.ne_idx(t, n, i, j) == True{} : Bool}
  {Refine.swap_m(Refine.swap_m(t, n, i, v), n, j, w) == Refine.swap_m(Refine.swap_m(t, n, j, w), n, i, v) : Refine.PT}

# V3d — the generic write-selector family (A.78).
#
# Every material-preserving write has the same Φ and count obligation. Instead of
# four hand-written `PT` recursions (`Tick.chg_support`/`chg_fall`/`chg_activate`/
# `chg_deactivate`), the write effect is the engine's own `Rules.PresOp` — a
# `Data`-kinded selector carried by `Rules.Write` — and the traversal is proved
# once. A `Data` selector is required rather than a function parameter because Bend
# closures are affine: `f : U32 -> U32` can be called at most once, and the
# traversal applies the write at every leaf.
#
# The two generic laws are the family's whole content; the site-specific laws
# below them are one-line instances, kept for traceability to §4.
#
# Coverage note: `array_fall_write_preserves_phi`, `array_mov_write_preserves_phi`
# and `array_deactivate_write_preserves_phi` are *new* statements. `set_fall0` and
# `deactivate` are emitted by the live `Rules.plan` on every tick (sel 22/23 and 4)
# and previously had no array-level Φ law — `step_m` covered them, but it mirrors
# the retired `Rules.step` (A.63) and is no longer evidence (`G10`/`G14`).
#
# A.78 (same milestone): the type names below moved from a selector-local `WrSel`
# to the engine's `Rules.PresOp` when the effect was pushed into `Rules.Write`. The
# statements are unchanged — same family, same claim.
law write_selector_preserves_phi:
  for +op: Rules.PresOp
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  {Settle.suml(Settle.to_pots(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Rules.apply_pres(Tick.tget(t, n, i), op))), base, n)) == Settle.suml(Settle.to_pots(Refine.pack(t), base, n)) : Nat}

law write_selector_preserves_count:
  for +op: Rules.PresOp
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  {Settle.suml(Count.to_counts(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Rules.apply_pres(Tick.tget(t, n, i), op))))) == Settle.suml(Count.to_counts(Refine.pack(t))) : Nat}

law array_fall_write_preserves_phi:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  {Settle.suml(Settle.to_pots(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Ops.set_fall0(Tick.tget(t, n, i)))), base, n)) == Settle.suml(Settle.to_pots(Refine.pack(t), base, n)) : Nat}

law array_mov_write_preserves_phi:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  {Settle.suml(Settle.to_pots(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Rules.mov(Tick.tget(t, n, i)))), base, n)) == Settle.suml(Settle.to_pots(Refine.pack(t), base, n)) : Nat}

law array_deactivate_write_preserves_phi:
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  {Settle.suml(Settle.to_pots(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Cell.deactivate(Tick.tget(t, n, i)))), base, n)) == Settle.suml(Settle.to_pots(Refine.pack(t), base, n)) : Nat}

# The `G14` closure: the exact Φ and count balance of *any* write effect, total
# over the engine's closed `Rules.Op` and any source word. `Rules.Write`'s `WSet`
# carries an `Op`, so this covers whatever `plan` emits — the write set is closed by
# construction, not by inspecting `plan`. The *decrease* is the refinement on top
# (`write_selector_preserves_phi` for material-preserving self-writes,
# `array_guarded_crush_lowers_phi` for the crush, `Fall.array_mov_cross` for the
# two-cell movement).
law write_effect_phi_balance:
  for +op: Rules.Op
  for +t: Refine.PT
  for +base: U32
  for +n: U32
  for +i: U32
  for +src: U32
  {Nat.add(Settle.suml(Settle.to_pots(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Rules.apply_op(src, op))), base, n)), Refine.nfst(Refine.chg_m(t, base, n, i, Rules.apply_op(src, op)))) == Nat.add(Settle.suml(Settle.to_pots(Refine.pack(t), base, n)), Refine.nsnd(Refine.chg_m(t, base, n, i, Rules.apply_op(src, op)))) : Nat}

law write_effect_count_balance:
  for +op: Rules.Op
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  for +src: U32
  {Nat.add(Settle.suml(Count.to_counts(Refine.afst(Array.swap.go(U32, Refine.pack(t), n, i, Rules.apply_op(src, op))))), Refine.nfst(Count.cnt_chg_m(t, n, i, Rules.apply_op(src, op)))) == Nat.add(Settle.suml(Count.to_counts(Refine.pack(t))), Refine.nsnd(Count.cnt_chg_m(t, n, i, Rules.apply_op(src, op)))) : Nat}

# ------------------------------------------------------------------ G5 reads
# The read companion of `swap_ref` (G1's write bridge) and of the `G10`/`G14`
# write-site closures. `Tick.tget` is the reader the live support mirror `sup_m`
# uses (the retired `step_m` reads through it too, A.63); `Support.sup`/`Rules.plan`
# read `Array.get(U32, w, i)`.
# Base's `Array.get.go` walks with the same `n/2` / `is_lt(i, h)` recursion, so the
# mirror's reads are the engine's array reads at the selector's index. This is the
# last thread of the `G5` caveat for the support selector machine.

# The engine's `Array.get.go` primitive reads `tget` at the same level-size.
law g5_read_get_go:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  {Array.get.go(U32, Refine.pack(t), n, i) == (Refine.pack(t), Tick.tget(t, n, i)) : Array<U32> & U32}

# The size half of the `Array.get`/`Array.swap` wrapper: `Array.size(pack t)` is
# `(pack t, g5_twidth t)`, so the engine's masking index is `i & (g5_twidth t - 1)`.
law g5_size_pack:
  for +t: Refine.PT
  {Array.size(U32, Refine.pack(t)) == (Refine.pack(t), G5.g5_twidth(t)) : Array<U32> & U32}

# The composed engine read: `Array.get(U32, pack t, i)` reads
# `tget t (g5_twidth t) (i & (g5_twidth t - 1))`. For the in-range indices the
# engine uses, the mask is the identity (the standard array-index fact, recorded
# as the residual of `G5`).
law g5_read_get:
  for +t: Refine.PT
  for +i: U32
  {Array.get(U32, Refine.pack(t), i) == (Refine.pack(t), Tick.tget(t, G5.g5_twidth(t), U32.and(i, U32.sub(G5.g5_twidth(t), 1)))) : Array<U32> & U32}

# Read-after-write at the selector's index: the engine's `q = Array.get(world, i)`
# after `world[i] <- v` (`Support.sup` cases 3/4/6; the post-write read-back) is
# the mirror's `q = tget(swap_m(t, n, i, v), n, i) = v`.
law g5_tget_swap:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  for +v: U32
  {Tick.tget(Refine.swap_m(t, n, i, v), n, i) == v : U32}

# V3c-1b — the schedule-invariance list/region layer (rule 10, the fold step).
#
# `Commit.v3c_fold` applies a `List` of point writes in order through the
# engine-facing `Refine.swap_m`. The first law lifts the V3c-1 kernel to a whole
# fold: a write at a leaf no write of the list touches commutes past the fold.
# The second is the region-split equality the scheduler needs: the writes of two
# regions, pairwise at distinct leaves, may be applied in either order and give
# the same tree as the sequential fold. Distinctness is `Commit.v3c_all_ne` /
# `Commit.v3c_pair_ne`, built from `Commit.ne_idx`.
law v3c_write_past_fold:
  for +ws: +List<Commit.V3cWrite>
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  for +v: U32
  for +hne: {Commit.v3c_all_ne(ws, t, n, i) == True{} : Bool}
  {Commit.v3c_fold(ws, Refine.swap_m(t, n, i, v), n) == Refine.swap_m(Commit.v3c_fold(ws, t, n), n, i, v) : Refine.PT}

law v3c_fold_commutes:
  for +xs: +List<Commit.V3cWrite>
  for +ys: +List<Commit.V3cWrite>
  for +t: Refine.PT
  for +n: U32
  for +hpn: {Commit.v3c_pair_ne(xs, ys, t, n) == True{} : Bool}
  {Commit.v3c_fold(List.append(&2, Commit.V3cWrite, xs, ys), t, n) == Commit.v3c_fold(List.append(&2, Commit.V3cWrite, ys, xs), t, n) : Refine.PT}

# V3c-2 (soundness half) — `Commit.ne_idx` agrees with the engine's equality on
# equal indices: `U32.is_eq(i, j) == True` forces `ne_idx == False`, so a proven
# `ne_idx == True` implies the engine's `U32.is_eq(i, j) == False`. The converse
# (completeness: distinct in-range indices on a full tree are separated) needs the
# `U32` order/subtraction arithmetic and is the remaining V3c-2 residual (`G3`).
law v3c_ne_idx_sound:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  for +j: U32
  for +he: {U32.is_eq(i, j) == True{} : Bool}
  {Commit.ne_idx(t, n, i, j) == False{} : Bool}

# ------------------------------------------------------------------ G5 mask
# The residual after the read-threading laws above: `g5_read_get` states the
# engine read with the masked index `i & (g5_twidth t - 1)`. The bare-index form
# needs the standard array-index fact for an in-range `i` on a power-of-two
# world. `src/g5.bend` carries a small, self-contained `U32`/`Word` bit-arithmetic
# development for it (no Base or project lemma covered `U32.and`/`U32.is_lt`).

# Law 1: a packed world's width is `2^depth`, at the `Word` level (`g5_mpow`).
law g5_twidth_pow:
  for +t: Refine.PT
  {G5.g5_twidth(t) == U32{G5.g5_mpow(32n, G5.g5_depth(t))} : U32}

# Law 2: for an in-range index the engine's range mask is the identity.
law g5_and_mask_id:
  for +t: Refine.PT
  for +i: U32
  for +h: {U32.is_lt(i, G5.g5_twidth(t)) == True{} : Bool}
  {U32.and(i, U32.sub(G5.g5_twidth(t), 1)) == i : U32}

# The bare-index read: combining the mask identity with `g5_read_get` removes the
# mask from the read-threading law, so the engine read is exactly the mirror read.
law g5_read_get_bare:
  for +t: Refine.PT
  for +i: U32
  for +h: {U32.is_lt(i, G5.g5_twidth(t)) == True{} : Bool}
  {Array.get(U32, Refine.pack(t), i) == (Refine.pack(t), Tick.tget(t, G5.g5_twidth(t), i)) : Array<U32> & U32}
# V3c-2 (completeness, structural fragment) — the three cases of `Commit.ne_idx`'s
# node recursion. `v3c_ne_idx_sep` is the top split (the two indices fall into
# opposite children, so `ne_idx` is `True`); `_same_l`/`_same_r` are the
# same-child reductions. Together they reduce full completeness to the arithmetic
# that distinct in-range indices reach a split at some level; see `PLAN.md` §5.3
# (`G3`).
law v3c_ne_idx_sep:
  for +xs: Refine.PT
  for +ys: Refine.PT
  for +n: U32
  for +i: U32
  for +j: U32
  for +hzi: {U32.is_lt(i, U32.shr(n)) == True{} : Bool}
  for +hzj: {U32.is_lt(j, U32.shr(n)) == False{} : Bool}
  {Commit.ne_idx(Refine.PN{xs, ys}, n, i, j) == True{} : Bool}

law v3c_ne_idx_same_l:
  for +xs: Refine.PT
  for +ys: Refine.PT
  for +n: U32
  for +i: U32
  for +j: U32
  for +hzi: {U32.is_lt(i, U32.shr(n)) == True{} : Bool}
  for +hzj: {U32.is_lt(j, U32.shr(n)) == True{} : Bool}
  {Commit.ne_idx(Refine.PN{xs, ys}, n, i, j) == Commit.ne_idx(xs, U32.shr(n), i, j) : Bool}

law v3c_ne_idx_same_r:
  for +xs: Refine.PT
  for +ys: Refine.PT
  for +n: U32
  for +i: U32
  for +j: U32
  for +hzi: {U32.is_lt(i, U32.shr(n)) == False{} : Bool}
  for +hzj: {U32.is_lt(j, U32.shr(n)) == False{} : Bool}
  {Commit.ne_idx(Refine.PN{xs, ys}, n, i, j) == Commit.ne_idx(ys, U32.shr(n), U32.sub(i, U32.shr(n)), U32.sub(j, U32.shr(n))) : Bool}

# C2/G15: the wake step is bounded by `Grid.step_inside`, so a step the guard
# rejects (a wrapped step off the box) writes nothing. `Ops.wake` computes
# `ok = Grid.step_inside(i, ox, oy, oz)` and applies `mark_if ok`; its `PT`
# mirror `Tick.wake_write_m` is the identity on `False`. This is the wake
# counterpart of V0-2's rule-target guard: activity no longer leaks across the box.
law g15_wake_step_inert:
  for +t: Refine.PT
  for +n: U32
  for +i: U32
  for +dx: U32
  for +dy: U32
  for +dz: U32
  for +h: {Grid.step_inside(i, dx, dy, dz) == False{} : Bool}
  {Tick.wake_write_m(Grid.step_inside(i, dx, dy, dz), t, n, Grid.neighbor(i, dx, dy, dz)) == t : Refine.PT}
# V3c-2 (completeness) — the converse of `v3c_ne_idx_sound`, and with it the
# exact refinement of `ne_idx` to the engine's `U32.is_eq`. For a full
# `2^k`-leaf tree and in-range distinct indices, `ne_idx` separates them:
#
#   `U32.is_eq(i, j) == False`  =>  `ne_idx(full k, two k, i, j) == True`.
#
# The proof is the depth induction over the three structural cases
# (`v3c_ne_idx_sep`/`_same_l`/`_same_r`), closed by the arithmetic bricks
# `v3c_lt_one_u32` (`i < 1 ⇒ i = 0`), `v3c_sub_two_lt` (the right child's index
# stays in `[0, 2^k)`) and `v3c_two_shr_of_lt` (`shr (2^(k+1)) = 2^k`). The
# second law is the combined exactness: `ne_idx` equals `Bool.not ∘ U32.is_eq`,
# which is what the schedule-invariance fold needs to key writes by the engine's
# own equality. This closes the V3c-2 residual (`G3`).
law v3c_ne_idx_complete:
  for +k: Nat
  for +i: U32
  for +j: U32
  for +hi: {U32.is_lt(i, Commit.v3c_two(k)) == True{} : Bool}
  for +hj: {U32.is_lt(j, Commit.v3c_two(k)) == True{} : Bool}
  for +hne: {U32.is_eq(i, j) == False{} : Bool}
  {Commit.ne_idx(Commit.v3c_full(k), Commit.v3c_two(k), i, j) == True{} : Bool}

law v3c_ne_idx_exact:
  for +k: Nat
  for +i: U32
  for +j: U32
  for +hi: {U32.is_lt(i, Commit.v3c_two(k)) == True{} : Bool}
  for +hj: {U32.is_lt(j, Commit.v3c_two(k)) == True{} : Bool}
  {Commit.ne_idx(Commit.v3c_full(k), Commit.v3c_two(k), i, j) == Bool.not(U32.is_eq(i, j)) : Bool}

# V3c/G3 — the engine wire: the engine's sequential write-list commit
# (`Rules.commit_sets`) equals the abstract schedule-invariance fold
# (`Commit.v3c_fold`) of the projected write list. The projection `V3cw.v3cw_proj`
# sends a `WSet{idx, op, src}` to the point write `MkWrite{idx, apply_op(src, op)}`
# and drops `WWake` (state-neutral for the set fold). `V3cw.v3cw_lin` is the
# multiplicity-erased copy of the engine's linear write list (see the module
# header); `hn` pins the fold size to the packed tree's own width (`g5_twidth`)
# and `hir` keeps every write index in range. With this, `v3c_fold_commutes`
# applies to the engine's actual write set.
law v3cw_commit_fold:
  for +ws: +List<Rules.Write>
  for +t: Refine.PT
  for +n: U32
  for +hn: {n == G5.g5_twidth(t) : U32}
  for +hir: {V3cw.v3cw_in_range(ws, n) == True{} : Bool}
  {Refine.unpack(Rules.commit_sets(V3cw.v3cw_lin(ws), Refine.pack(t))) == Commit.v3c_fold(V3cw.v3cw_proj(ws), t, n) : Refine.PT}

# The engine-level region-split equality: two regions of the engine's write set,
# with pairwise-distinct projected targets, commit to the same packed tree in
# either order. This is `v3c_fold_commutes` transported through
# `v3cw_commit_fold` by `V3cw.v3cw_proj_append`.
law v3cw_commit_commutes:
  for +xs: +List<Rules.Write>
  for +ys: +List<Rules.Write>
  for +t: Refine.PT
  for +n: U32
  for +hn: {n == G5.g5_twidth(t) : U32}
  for +hxy: {V3cw.v3cw_in_range(List.append(&2, Rules.Write, xs, ys), n) == True{} : Bool}
  for +hyx: {V3cw.v3cw_in_range(List.append(&2, Rules.Write, ys, xs), n) == True{} : Bool}
  for +hpn: {Commit.v3c_pair_ne(V3cw.v3cw_proj(xs), V3cw.v3cw_proj(ys), t, n) == True{} : Bool}
  {Refine.unpack(Rules.commit_sets(V3cw.v3cw_lin(List.append(&2, Rules.Write, xs, ys)), Refine.pack(t))) == Refine.unpack(Rules.commit_sets(V3cw.v3cw_lin(List.append(&2, Rules.Write, ys, xs)), Refine.pack(t))) : Refine.PT}

# P3 / G-scale-3 -- the `cw` global-coordinate split/rejoin, proven.
#
# `src/cw.bend` splits a global coordinate into a chunk key plus a local offset
# and rejoins it with no torus mask; T57-T60 witness it. These laws close the
# `G-scale-3` gap: the bit lemma `(x >> 4) << 4 + (x & 15) == x & 16383` (the
# `cw_global_x/y/z` core, `Gscale.gscale_global_rt`) plus the field extraction
# and the 10-bit / 4-bit key/local reconstruction (`Gscale.gscale_kmodel_rt`,
# `Gscale.gscale_lmodel_rt`). The `x/y/z` axes are stated for `x < 16384` (the
# 10-bit key range); the y/z forms put the axis chunk in its own slot because
# `cw_global_y/z` read only that field. The key and local roundtrips are stated
# for in-range `k < 2^30` and `l < 2^12`.
law gscale_cw_x_rt:
  for x: U32
  for y: U32
  for z: U32
  for h: {U32.is_lt(x, 16384) == True{} : Bool}
  {Cw.cw_global_x(Cw.cw_key(Cw.cw_chunk_of(x), Cw.cw_chunk_of(y), Cw.cw_chunk_of(z)), Cw.cw_local(Cw.cw_local_of(x), Cw.cw_local_of(y), Cw.cw_local_of(z))) == x : U32}

law gscale_cw_y_rt:
  for y: U32
  for h: {U32.is_lt(y, 16384) == True{} : Bool}
  {Cw.cw_global_y(Cw.cw_key(0, Cw.cw_chunk_of(y), 0), Cw.cw_local(0, Cw.cw_local_of(y), 0)) == y : U32}

law gscale_cw_z_rt:
  for z: U32
  for h: {U32.is_lt(z, 16384) == True{} : Bool}
  {Cw.cw_global_z(Cw.cw_key(0, 0, Cw.cw_chunk_of(z)), Cw.cw_local(0, 0, Cw.cw_local_of(z))) == z : U32}

law gscale_cw_key_rt:
  for k: U32
  for h: {U32.is_lt(k, 1073741824) == True{} : Bool}
  {Cw.cw_key(Cw.cw_key_x(k), Cw.cw_key_y(k), Cw.cw_key_z(k)) == k : U32}

law gscale_cw_local_rt:
  for l: U32
  for h: {U32.is_lt(l, 4096) == True{} : Bool}
  {Cw.cw_local(Cw.cw_local_x(l), Cw.cw_local_y(l), Cw.cw_local_z(l)) == l : U32}

# The full three-coordinate forms of the y/z axis roundtrips: the axis field is
# recovered from an arbitrary packed key/local (any (x, y, z)), rather than from
# a key whose other slots are zero (`Gscale.gscale_key_y_ext`/`_z_ext`,
# `Gscale.gscale_local_y_ext`/`_z_ext`). Additive; the bounded laws above stay.
law gscale_cw_y_rt_full:
  for x: U32
  for y: U32
  for z: U32
  for h: {U32.is_lt(y, 16384) == True{} : Bool}
  {Cw.cw_global_y(Cw.cw_key(Cw.cw_chunk_of(x), Cw.cw_chunk_of(y), Cw.cw_chunk_of(z)), Cw.cw_local(Cw.cw_local_of(x), Cw.cw_local_of(y), Cw.cw_local_of(z))) == y : U32}

law gscale_cw_z_rt_full:
  for x: U32
  for y: U32
  for z: U32
  for h: {U32.is_lt(z, 16384) == True{} : Bool}
  {Cw.cw_global_z(Cw.cw_key(Cw.cw_chunk_of(x), Cw.cw_chunk_of(y), Cw.cw_chunk_of(z)), Cw.cw_local(Cw.cw_local_of(x), Cw.cw_local_of(y), Cw.cw_local_of(z))) == z : U32}
