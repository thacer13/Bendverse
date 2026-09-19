import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/ops.bend as Ops
import ../src/sim.bend as Sim

type St is Type:
  St{w: Array<U32>, run: Bool, mx: U32, my: U32}

def color_of(+m: U32) -> U32:
  match m:
    case 0:
      657938
    case 1:
      5263440
    case 2:
      14729312
    case 3:
      9474192
    case 4:
      10514496
    case 5:
      2121920
    case _:
      16711935

def render_leaf_got(q: Array<U32> & U32, acc: List<Image>) -> Array<U32> & List<Image>:
  match q:
    case (world2, v):
      (world2, Pix{color_of(Cell.material(v))} <> acc)

def render(depth: Nat, size: U32, gp: Array<U32> & List<Image>, +x0: U32, +y0: U32) -> Array<U32> & List<Image>:
  match depth:
    case 0n:
      match gp:
        case (world, acc):
          # Rendered at cell resolution: one quadtree leaf per cell, so the
          # window scales the 64x64 image up (M9 win 1: 16x fewer `Array.get`s).
          +idx = Grid.index(x0, U32.sub(63, y0), 32)
          render_leaf_got(Array.get(U32, world, idx), acc)
    case 1n+dp:
      +d = dp
      +h = U32.shr(size)
      render(d, h,
        render(d, h,
          render(d, h,
            render(d, h, gp, x0, y0),
            U32.add(x0, h), y0),
          x0, U32.add(y0, h)),
        U32.add(x0, h), U32.add(y0, h))

def group4(imgs: List<Image>) -> List<Image>:
  match imgs:
    case Nil{}:
      Nil{}
    case a <> b <> c <> d <> rest:
      Qua{a, b, c, d} <> group4(rest)
    case h <> t:
      h <> t

def levels(fuel: Nat, imgs: List<Image>) -> List<Image>:
  match fuel:
    case 0n:
      imgs
    case 1n+p:
      levels(p, group4(imgs))

def root_img(imgs: List<Image>) -> Image:
  match imgs:
    case Nil{}:
      Pix{0}
    case h <> _:
      h

def view_got(r: Array<U32> & List<Image>, run: Bool, mx: U32, my: U32) -> St & Image:
  match r:
    case (w2, leafs):
      (St{w2, run, mx, my}, root_img(levels(6n, List.reverse(&1, Image, leafs))))

def view(s: St) -> St & Image:
  match s:
    case St{w, run, mx, my}:
      view_got(render(6n, 64, (w, Nil{}), 0, 0), run, mx, my)

def paint_at(world: Array<U32>, +x: U32, +y: U32, +mat: U32) -> Array<U32>:
  +cx = U32.shrn(x, 2n)
  +cy = U32.shrn(y, 2n)
  +idx = Grid.index(cx, U32.sub(63, cy), 32)
  +word = Cell.encode(mat, Cell.default_cohesion(mat), 0, 0, 0)
  world = world[idx] <- word
  Ops.wake(world, idx)

def handle_mouse(button: U32, down: Bool, +x: U32, +y: U32, sp: St & Bool) -> St & Bool:
  match button:
    case 0:
      match down:
        case False{}:
          match sp:
            case (St{w, run, mx, my}, alive):
              (St{w, run, x, y}, alive)
        case True{}:
          match sp:
            case (St{w, run, mx, my}, alive):
              (St{paint_at(w, x, y, 2), run, x, y}, alive)
    case 1:
      match down:
        case False{}:
          match sp:
            case (St{w, run, mx, my}, alive):
              (St{w, run, x, y}, alive)
        case True{}:
          match sp:
            case (St{w, run, mx, my}, alive):
              (St{paint_at(w, x, y, 3), run, x, y}, alive)
    case _:
      match down:
        case False{}:
          match sp:
            case (St{w, run, mx, my}, alive):
              (St{w, run, x, y}, alive)
        case True{}:
          match sp:
            case (St{w, run, mx, my}, alive):
              (St{w, run, x, y}, alive)

def handle_key(code: U32, down: Bool, sp: St & Bool) -> St & Bool:
  match code:
    case 32:
      match down:
        case False{}:
          match sp:
            case (St{w, run, mx, my}, alive):
              (St{w, run, mx, my}, alive)
        case True{}:
          match sp:
            case (St{w, run, mx, my}, alive):
              (St{w, Bool.not(run), mx, my}, alive)
    case 101:
      match down:
        case False{}:
          match sp:
            case (St{w, run, mx, my}, alive):
              (St{w, run, mx, my}, alive)
        case True{}:
          match sp:
            case (St{w, run, +mx, +my}, alive):
              (St{paint_at(w, mx, my, 0), run, mx, my}, alive)
    case _:
      match down:
        case False{}:
          match sp:
            case (St{w, run, mx, my}, alive):
              (St{w, run, mx, my}, alive)
        case True{}:
          match sp:
            case (St{w, run, mx, my}, alive):
              (St{w, run, mx, my}, alive)

def handle(e: Event, sp: St & Bool) -> St & Bool:
  match e:
    case Close{}:
      match sp:
        case (s, alive):
          (s, False{})
    case Move{x, y}:
      match sp:
        case (St{w, run, mx, my}, alive):
          (St{w, run, x, y}, alive)
    case Mouse{x, y, button, down}:
      handle_mouse(button, down, x, y, sp)
    case Key{code, down}:
      handle_key(code, down, sp)

def step_events(events: List<Event>, sp: St & Bool) -> St & Bool:
  match events:
    case Nil{}:
      sp
    case Con{e, rest}:
      step_events(rest, handle(e, sp))

def tick_go(sp: St & Bool) -> IO(Maybe<St>):
  match sp:
    case (St{w, run, mx, my}, alive):
      match run:
        case False{}:
          match alive:
            case False{}:
              IO.pure(Maybe<St>, None{})
            case True{}:
              IO.pure(Maybe<St>, Some{St{w, run, mx, my}})
        case True{}:
          match alive:
            case False{}:
              IO.pure(Maybe<St>, None{})
            case True{}:
              IO.pure(Maybe<St>, Some{St{Sim.tick(w), run, mx, my}})

def tick(events: List<Event>, s: St) -> IO(Maybe<St>):
  tick_go(step_events(events, (s, True{})))

def main() -> IO(Unit):
  App.run(~St, ~App{view, tick}, "Bendverse — M6", 256, 256, St{Sim.build(), True{}, 32, 32})
