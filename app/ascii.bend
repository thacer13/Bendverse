import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/worldgen.bend as Worldgen
import ../src/sim.bend as Sim

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

def in_box(+x: U32, +y: U32, +z: U32) -> Bool:
  Bool.and(
    Bool.and(U32.is_ge(x, 30), U32.is_le(x, 34)),
    Bool.and(
      Bool.and(U32.is_ge(z, 30), U32.is_le(z, 34)),
      Bool.and(U32.is_ge(y, 46), U32.is_le(y, 52))
    )
  )

def box_word(+x: U32, +y: U32, +z: U32) -> U32:
  Bool.pick(U32, in_box(x, y, z), 2, Worldgen.gen(x, y, z, 42))

def spawn(fuel: Nat, +i: U32, world: Array<U32>) -> Array<U32>:
  match fuel:
    case 0n:
      world
    case 1n+p:
      bx = U32.mod(i, 5)
      bz = U32.mod(U32.div(i, 5), 5)
      by = U32.mod(U32.div(i, 25), 7)
      x = U32.add(bx, 30)
      z = U32.add(bz, 30)
      y = U32.add(by, 46)
      world = world[Grid.index(x, y, z)] <- 2
      spawn(p, U32.add(i, 1), world)

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
      gen_row(p, U32.add(x, 1), y, acc ++ char_of(Cell.material(box_word(x, y, 32))))

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
    world : Array<U32> = Worldgen.build()
    world1 : Array<U32> = spawn(U32.to_nat(175), 0, world)
    IO.print("BEFORE (x-y at z=32, y=63 top; spawned sand block in air):")
    IO.print(render_gen())
    world2 : Array<U32> = Sim.ticks(ticks(), world1)
    IO.print("AFTER 14 ticks:")
    IO.print(render_world(world2))
