import Base
import ./src/grid.bend as Grid
import ./src/cell.bend as Cell
import ./src/potential.bend as Pot

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
