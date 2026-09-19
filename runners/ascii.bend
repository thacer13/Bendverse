import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/worldgen.bend as Worldgen
import ../src/sim.bend as Sim
import ../scenarios/fixtures.bend as Fixtures

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

def pull_cell(+x: U32, +y: U32, +z: U32) -> U32:
  hit = Bool.and(U32.is_eq(x, 32), Bool.and(U32.is_eq(y, 3), U32.is_eq(z, 32)))
  Bool.pick(U32, hit, 0, Worldgen.gen(x, y, z, 42))

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

def render_world(world: Array<U32>) -> String:
  cells = Grid.to_list(world)
  rows = frame(U32.to_nat(262144), 0, cells, [""])
  join_rows(rows)

def gen_row(fuel: Nat, +x: U32, +y: U32, acc: String) -> String:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      gen_row(p, U32.add(x, 1), y, acc ++ char_of(Cell.material(pull_cell(x, y, 32))))

def gen_rows(fuel: Nat, +y: U32, out: String) -> String:
  match fuel:
    case 0n:
      out
    case 1n+p:
      row = gen_row(U32.to_nat(64), 0, y, "")
      gen_rows(p, U32.sub(y, 1), out ++ row ++ "\n")

def render_gen() -> String:
  gen_rows(U32.to_nat(64), 63, "")

def ticks() -> Nat:
  U32.to_nat(14)

def main() -> IO(Unit):
  do IO<Unit>:
    world : Array<U32> = Sim.build()
    world1 : Array<U32> = Fixtures.pull(world)
    IO.print("BEFORE (x-y at z=32, y=63 top; one base rock cell pulled at x=32,y=3):")
    IO.print(render_gen())
    world2 : Array<U32> = Sim.ticks(ticks(), world1)
    IO.print("AFTER 14 ticks:")
    IO.print(render_world(world2))
