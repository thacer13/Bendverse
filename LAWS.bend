import Base
import ./src/grid.bend as Grid
import ./src/cell.bend as Cell

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
