import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/worldgen.bend as Worldgen

def char_of(m: U32) -> String:
  match m:
    case 0:
      "."
    case 1:
      "#"
    case 2:
      "s"
    case 3:
      "R"
    case 4:
      "r"
    case 5:
      "~"
    case _:
      "?"

def append_if(z: Bool, row: String, c: String) -> String:
  match z:
    case True{}:
      row ++ c
    case False{}:
      row

def finish_row(flag: Bool, base: String, tail: List<String>) -> List<String>:
  match flag:
    case True{}:
      "" <> ((base ++ "\n") <> tail)
    case False{}:
      base <> tail

def frame(fuel: Nat, +i: U32, cells: List<U32>, rows: List<String>) -> List<String>:
  match fuel:
    case 0n:
      rows
    case 1n+p:
      match cells:
        case Nil{}:
          rows
        case Con{h, t}:
          match rows:
            case Nil{}:
              frame(p, U32.add(i, 1), t, [""])
            case Con{head, tail}:
              z = Grid.iz(i)
              x = Grid.ix(i)
              +is_z = U32.is_eq(z, 32)
              base = append_if(is_z, head, char_of(Cell.material(h)))
              at_end = Bool.and(is_z, U32.is_eq(x, 63))
              frame(p, U32.add(i, 1), t, finish_row(at_end, base, tail))

def join_rows(rows: List<String>) -> String:
  match rows:
    case Nil{}:
      ""
    case Con{head, tail}:
      head ++ join_rows(tail)

def render() -> String:
  world = Worldgen.build()
  cells = Grid.to_list(world)
  rows = frame(U32.to_nat(262144), 0, cells, [""])
  join_rows(rows)

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print(render())
