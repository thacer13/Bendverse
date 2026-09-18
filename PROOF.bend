import Base
import ./LAWS.bend as Laws
import ./src/bits.bend as Bits
import ./src/grid.bend as Grid
import ./src/cell.bend as Cell

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
