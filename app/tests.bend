import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell

def is_bad(z: Bool) -> U32:
  match z:
    case True{}:
      0
    case False{}:
      1

def inc_if_false(z: Bool, bad: U32) -> U32:
  match z:
    case True{}:
      bad
    case False{}:
      U32.add(bad, 1)

def report(+name: String, +bad: U32) -> IO(Unit):
  do IO<Unit>:
    z : Bool = U32.is_eq(bad, 0)
    IO.print(Bool.pick(String, z, "PASS " ++ name, "FAIL " ++ name ++ " (" ++ U32.show(bad) ++ ")"))

def index_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      j = Grid.index(Grid.ix(i), Grid.iy(i), Grid.iz(i))
      ok = U32.is_eq(j, i)
      bad2 = inc_if_false(ok, bad)
      index_go(p, U32.add(i, 1), bad2)

def index_bad() -> U32:
  index_go(U32.to_nat(262144), 0, 0)

def cell_go(fuel: Nat, +i: U32, bad: U32) -> U32:
  match fuel:
    case 0n:
      bad
    case 1n+p:
      +mat = U32.mod(i, 6)
      +coh = U32.mod(i, 64)
      +act = U32.mod(i, 2)
      +sup = U32.mod(i, 32)
      +fl = U32.mod(i, 64)
      +w = Cell.encode(mat, coh, act, sup, fl)
      okm = U32.is_eq(Cell.material(w), mat)
      okc = U32.is_eq(Cell.cohesion(w), coh)
      oka = U32.is_eq(Cell.active(w), act)
      oks = U32.is_eq(Cell.support(w), sup)
      okf = U32.is_eq(Cell.fall(w), fl)
      okr = U32.is_eq(Cell.reencode(w), w)
      all = Bool.and(Bool.and(Bool.and(Bool.and(okm, okc), Bool.and(oka, oks)), okf), okr)
      bad2 = inc_if_false(all, bad)
      cell_go(p, U32.add(i, 1), bad2)

def cell_bad() -> U32:
  cell_go(U32.to_nat(4096), 0, 0)

def main() -> IO(Unit):
  do IO<Unit>:
    report("T5 index roundtrip (2^18)", index_bad())
    report("T5 cell field roundtrip", cell_bad())
    report("spike bit31", is_bad(U32.is_eq(U32.shln(1, 31n), 2147483648)))
    report("spike mul wrap", is_bad(U32.is_eq(U32.mul(4294967295, 2), 4294967294)))
