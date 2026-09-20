import Base
import ../src/sim.bend as Sim
import ../view/voxel.bend as Vox

# view3d — a windowed 3D voxel view of the engine's 64^3 world. Presentation
# only (AGENTS.md): this runner adds no engine semantics; the camera and the
# raycast are visibility, and the pure raycast lives in `view/voxel.bend`.
#
# Controls
#   W / S          fly forward / backward (horizontal)
#   A / D          strafe left / right
#   Q / E, <- / -> turn left / right (yaw)
#   Up / Down      pitch up / down
#   R / F          rise / sink
#   mouse drag     look
#   space          pause / resume the simulation
#   - / = and [ ]  simulation speed down / up (ticks per rendered frame)
#   , / .          render depth down / up (smaller = faster + chunkier)
#   close          quit
#
# Key codes: the X11 backend reports a printable key's character (lowercase) and
# the arrows as 63232..63235; the Mac/GLFW convention reports uppercase letters
# and 262..265. `bit_of` accepts both so the controls work on either backend.

def win_w() -> U32:
  1920

def win_h() -> U32:
  1080

def depth_min() -> Nat:
  5n

def depth_max() -> Nat:
  8n

type St is Type:
  St{
    w: Array<U32>, run: Bool, speed: U32, depth: Nat,
    ox: F32, oy: F32, oz: F32, yaw: F32, pitch: F32,
    keys: U32, drag: Bool, mx: U32, my: U32
  }

# Held-key bits, one per control. Both backend key-code conventions are listed.
def bit_of(+code: U32) -> U32:
  match code:
    case 87:
      0    # W
    case 119:
      0    # w
    case 83:
      1    # S
    case 115:
      1    # s
    case 65:
      2    # A
    case 97:
      2    # a
    case 68:
      3    # D
    case 100:
      3    # d
    case 81:
      4    # Q
    case 113:
      4    # q
    case 263:
      4    # Left (Mac/GLFW)
    case 63234:
      4    # Left (X11)
    case 69:
      5    # E
    case 101:
      5    # e
    case 262:
      5    # Right (Mac/GLFW)
    case 63235:
      5    # Right (X11)
    case 265:
      6    # Up (Mac/GLFW)
    case 63232:
      6    # Up (X11)
    case 264:
      7    # Down (Mac/GLFW)
    case 63233:
      7    # Down (X11)
    case 82:
      8    # R
    case 114:
      8    # r
    case 70:
      9    # F
    case 102:
      9    # f
    case _:
      99

def set_bit(+keys: U32, +code: U32, down: Bool) -> U32:
  +b = bit_of(code)
  +valid = U32.is_lt(b, 10)
  +mask = U32.shln(1, U32.to_nat(U32.min(b, 31)))
  +next = Bool.pick(U32, down, U32.or(keys, mask), U32.and(keys, U32.not(mask)))
  Bool.pick(U32, valid, next, keys)

def held(keys: U32, +b: Nat) -> Bool:
  U32.is_ne(U32.and(keys, U32.shln(1, b)), 0)

def one(b: Bool) -> F32:
  Bool.pick(F32, b, 1.0, 0.0)

def inc_if(+a: F32, b: Bool, +d: F32) -> F32:
  Bool.pick(F32, b, F32.add(a, d), a)

def clamp_pos(+v: F32) -> F32:
  F32.clamp(v, 0.05, 63.95)

def clamp_pitch(+v: F32) -> F32:
  F32.clamp(v, F32.neg(1.5), 1.5)

def move_speed() -> F32:
  0.6

# `view` folds held keys into the camera and renders one frame. App.run is
# frame-driven, so this is the per-frame motion (no wall-clock timer).
def view_got(
  r: Array<U32> & Image, run: Bool, speed: U32, depth: Nat,
  +ox: F32, +oy: F32, +oz: F32, +yaw: F32, +pitch: F32,
  keys: U32, drag: Bool, mx: U32, my: U32
) -> St & Image:
  match r:
    case (w2, img):
      (St{w2, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}, img)

def view(s: St) -> St & Image:
  match s:
    case St{w, run, speed, +depth, ox, oy, oz, yaw, pitch, +keys, drag, mx, my}:
      +yaw1 = inc_if(yaw, held(keys, 4n), 0.035)
      +yaw2 = inc_if(yaw1, held(keys, 5n), F32.neg(0.035))
      +pitch1 = inc_if(pitch, held(keys, 6n), 0.030)
      +pitch2 = clamp_pitch(inc_if(pitch1, held(keys, 7n), F32.neg(0.030)))
      +sy = F32.sin(yaw2)
      +cy = F32.cos(yaw2)
      +fwd = F32.sub(one(held(keys, 0n)), one(held(keys, 1n)))
      +str = F32.sub(one(held(keys, 3n)), one(held(keys, 2n)))
      +vert = F32.sub(one(held(keys, 8n)), one(held(keys, 9n)))
      +ox2 = clamp_pos(F32.add(ox, F32.mul(move_speed(), F32.add(F32.mul(fwd, sy), F32.mul(str, cy)))))
      +oz2 = clamp_pos(F32.add(oz, F32.mul(move_speed(), F32.add(F32.mul(fwd, cy),
                                                        F32.mul(str, F32.neg(sy))))))
      +oy2 = clamp_pos(F32.add(oy, F32.mul(move_speed(), vert)))
      view_got(Vox.view_image(win_w(), win_h(), depth, w,
                              Vox.cam_of(ox2, oy2, oz2, yaw2, pitch2)),
               run, speed, depth, ox2, oy2, oz2, yaw2, pitch2, keys, drag, mx, my)

def speed_up(speed: U32) -> U32:
  U32.min(U32.add(speed, 1), 8)

def speed_down(+speed: U32) -> U32:
  U32.sub(speed, U32.min(speed, 1))

def depth_up(+d: Nat) -> Nat:
  Nat.min(Nat.add(d, 1n), depth_max())

def depth_down(+d: Nat) -> Nat:
  Nat.max(Nat.sub(d, 1n), depth_min())

# The world-independent controls: pause, speed, and render depth. Each acts on
# key-down only, so holding the key does not run away.
def handle_cmd(code: U32, sp: St) -> St:
  match code:
    case 32:
      match sp:
        case St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
          St{w, Bool.not(run), speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}
    case 45:
      match sp:
        case St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
          St{w, run, speed_down(speed), depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}
    case 91:
      match sp:
        case St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
          St{w, run, speed_down(speed), depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}
    case 61:
      match sp:
        case St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
          St{w, run, speed_up(speed), depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}
    case 93:
      match sp:
        case St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
          St{w, run, speed_up(speed), depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}
    case 44:
      match sp:
        case St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
          St{w, run, speed, depth_down(depth), ox, oy, oz, yaw, pitch, keys, drag, mx, my}
    case 46:
      match sp:
        case St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
          St{w, run, speed, depth_up(depth), ox, oy, oz, yaw, pitch, keys, drag, mx, my}
    case _:
      sp

def handle_key_down(code: U32, sp: St) -> St:
  match code:
    case 32:
      handle_cmd(code, sp)
    case 45:
      handle_cmd(code, sp)
    case 91:
      handle_cmd(code, sp)
    case 61:
      handle_cmd(code, sp)
    case 93:
      handle_cmd(code, sp)
    case 44:
      handle_cmd(code, sp)
    case 46:
      handle_cmd(code, sp)
    case _:
      match sp:
        case St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
          St{w, run, speed, depth, ox, oy, oz, yaw, pitch,
             set_bit(keys, code, True{}), drag, mx, my}

def handle_key(code: U32, down: Bool, sp: St) -> St:
  match down:
    case True{}:
      handle_key_down(code, sp)
    case False{}:
      match sp:
        case St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
          St{w, run, speed, depth, ox, oy, oz, yaw, pitch,
             set_bit(keys, code, False{}), drag, mx, my}

def handle_mouse(button: U32, down: Bool, +x: U32, +y: U32, sp: St) -> St:
  match button:
    case 0:
      match sp:
        case St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
          St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, down, x, y}
    case _:
      sp

def drag_delta(+now: U32, +before: U32) -> F32:
  +d = U32.sub(U32.max(now, before), U32.min(now, before))
  Bool.pick(F32, U32.is_lt(before, now), U32.to_f32(d), F32.neg(U32.to_f32(d)))

def handle_move(+x: U32, +y: U32, sp: St) -> St:
  match sp:
    case St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}:
      match drag:
        case False{}:
          St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, x, y}
        case True{}:
          +yaw2 = F32.add(yaw, F32.mul(drag_delta(x, mx), 0.005))
          +pitch2 = clamp_pitch(F32.sub(pitch, F32.mul(drag_delta(y, my), 0.005)))
          St{w, run, speed, depth, ox, oy, oz, yaw2, pitch2, keys, drag, x, y}

def handle(e: Event, sp: St & Bool) -> St & Bool:
  match e:
    case Close{}:
      match sp:
        case (s, alive):
          (s, False{})
    case Move{x, y}:
      match sp:
        case (s, alive):
          (handle_move(x, y, s), alive)
    case Mouse{x, y, button, down}:
      match sp:
        case (s, alive):
          (handle_mouse(button, down, x, y, s), alive)
    case Key{code, down}:
      match sp:
        case (s, alive):
          (handle_key(code, down, s), alive)

def step_events(events: List<Event>, sp: St & Bool) -> St & Bool:
  match events:
    case Nil{}:
      sp
    case Con{e, rest}:
      step_events(rest, handle(e, sp))

def tick_go(sp: St & Bool) -> IO(Maybe<St>):
  match sp:
    case (St{w, run, +speed, +depth, +ox, +oy, +oz, +yaw, +pitch, +keys, +drag, +mx, +my}, alive):
      match run:
        case False{}:
          match alive:
            case False{}:
              IO.pure(Maybe<St>, None{})
            case True{}:
              IO.pure(Maybe<St>, Some{St{w, run, speed, depth, ox, oy, oz, yaw, pitch, keys, drag, mx, my}})
        case True{}:
          match alive:
            case False{}:
              IO.pure(Maybe<St>, None{})
            case True{}:
              IO.pure(Maybe<St>, Some{St{Sim.ticks(U32.to_nat(speed), w), run, speed, depth,
                                          ox, oy, oz, yaw, pitch, keys, drag, mx, my}})

def tick(events: List<Event>, s: St) -> IO(Maybe<St>):
  tick_go(step_events(events, (s, True{})))

def init() -> St:
  St{Sim.build(), True{}, 1, 7n, 32.0, 45.0, 4.0, 0.0, F32.neg(0.30), 0, False{}, 0, 0}

def main() -> IO(Unit):
  App.run(~St, ~App{view, tick}, "Bendverse — view3d", win_w(), win_h(), init())
