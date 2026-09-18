import Base
import ./LAWS.bend as Laws
import ./src/bits.bend as Bits
import ./src/grid.bend as Grid
import ./src/cell.bend as Cell
import ./src/potential.bend as Pot

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
