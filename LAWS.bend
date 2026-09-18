import Base
import ./src/grid.bend as Grid
import ./src/cell.bend as Cell
import ./src/potential.bend as Pot
import ./src/settle.bend as Settle
import ./src/parity.bend as Parity
import ./src/mod.bend as Mod

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
