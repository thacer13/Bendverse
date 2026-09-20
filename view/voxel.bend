import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell

# view3d — pure voxel raycast (Amanatides & Woo DDA) over the engine's
# `Array<U32>` world. Presentation only: it lives outside `src/` and touches the
# engine only through `Grid`/`Cell` reads, so the zero-IO engine stays untouched.
#
# The window backend (`Window.frame`) draws an `Image` — a 2^d x 2^d square
# quadtree — into a w x h window by taking the top bits of each coordinate:
# window pixel (x, y) shows image cell `(x >> s, y >> s)` where `s = k - d` and
# `2^k` is the smallest power of two >= max(w, h). So a windowed view is
# aspect-correct and integer-scaled exactly when the top-left
# `ceil(w / 2^s) x ceil(h / 2^s)` sub-image is the content; `view_image` builds
# that view and `render_q` skips the rays outside it. `image` keeps the old
# square (backward-compatible) form used by the T49 witness.
#
# Bend's `match` only scrutinizes a parameter or a field, so the DDA is a
# self-recursive state machine. Each cell costs two tail calls: one to classify
# the cell it was handed (bounds + material) and one to advance. The `gp` pair
# carries `(world, word)`, and the word for the next cell is fetched during the
# step, so a cell is fetched exactly once.

def dda_steps() -> Nat:
  256n

# tan(fov/2) for a ~70 degree vertical field of view.
def tan_half() -> F32:
  0.70

def axis_inf() -> F32:
  F32.div(1.0, 0.0)

# ------------------------------------------------------------------ camera --
# yaw 0 looks toward +z; increasing yaw turns toward +x. pitch 0 is level, +up.
type Cam is Data:
  Cam{
    ox: F32, oy: F32, oz: F32,
    fx: F32, fy: F32, fz: F32,
    rx: F32, ry: F32, rz: F32,
    ux: F32, uy: F32, uz: F32
  }

def cam_of(+ox: F32, +oy: F32, +oz: F32, +yaw: F32, +pitch: F32) -> Cam:
  +cp = F32.cos(pitch)
  +sp = F32.sin(pitch)
  +sy = F32.sin(yaw)
  +cy = F32.cos(yaw)
  Cam{ox, oy, oz,
      F32.mul(cp, sy), sp, F32.mul(cp, cy),
      cy, 0.0, F32.neg(sy),
      F32.neg(F32.mul(sp, sy)), cp, F32.neg(F32.mul(sp, cy))}

# -------------------------------------------------------------------- DDA ---
# One axis of the DDA state: which way the ray runs on it, the t at which it
# leaves the current cell, and the t it takes to cross one cell.
type Axis is Data:
  Axis{neg: Bool, tmax: F32, tdelta: F32}

def axis_init(+o: F32, i: U32, +d: F32) -> Axis:
  +fi = U32.to_f32(i)
  +neg = F32.is_lt(d, 0.0)
  +zero = F32.is_eq(d, 0.0)
  +tp = F32.div(F32.sub(F32.add(fi, 1.0), o), d)
  +tdp = F32.div(1.0, d)
  +nd = F32.neg(d)
  +tn = F32.div(F32.sub(o, fi), nd)
  +tdn = F32.div(1.0, nd)
  Axis{neg,
       Bool.pick(F32, zero, axis_inf(), Bool.pick(F32, neg, tn, tp)),
       Bool.pick(F32, zero, axis_inf(), Bool.pick(F32, neg, tdn, tdp))}

type Hit is Data:
  Miss{}
  Hit{mat: U32, nx: F32, ny: F32, nz: F32, t: F32}

def sign_f(neg: Bool) -> F32:
  Bool.pick(F32, neg, 1.0, F32.neg(1.0))

# The face the ray entered the hit cell through: opposite the axis it stepped on.
def mk_hit(+mat: U32, +last: U32, ax: Axis, ay: Axis, az: Axis, +t: F32) -> Hit:
  match last:
    case 0:
      match ax:
        case Axis{neg, tmax, tdelta}:
          Hit{mat, sign_f(neg), 0.0, 0.0, t}
    case 1:
      match ay:
        case Axis{neg, tmax, tdelta}:
          Hit{mat, 0.0, sign_f(neg), 0.0, t}
    case 2:
      match az:
        case Axis{neg, tmax, tdelta}:
          Hit{mat, 0.0, 0.0, sign_f(neg), t}
    case _:
      Hit{mat, 0.0, 1.0, 0.0, t}

def inside_box(+ix: U32, +iy: U32, +iz: U32) -> Bool:
  Bool.and(
    Bool.and(U32.is_lt(ix, Grid.size()), U32.is_lt(iy, Grid.size())),
    U32.is_lt(iz, Grid.size()))

# Selectors: 0 examine, 1 hit, 2 step, 3 miss. `fuel` counts calls (two per
# cell), so `dda_steps()` is doubled at the entry points. `gp` is the
# `(world, word)` pair for the cell under consideration.
def dda(
  fuel: Nat, gp: Array<U32> & U32, +sel: U32,
  +ix: U32, +iy: U32, +iz: U32, ax: Axis, ay: Axis, az: Axis,
  +t: F32, +last: U32
) -> Array<U32> & Hit:
  match fuel:
    case 0n:
      match gp:
        case (world, gv):
          (world, Miss{})
    case 1n+ +p:
      match gp:
        case (world, +gv):
          match sel:
            case 0:
              +ok = inside_box(ix, iy, iz)
              +solid = U32.is_ne(Cell.material(gv), 0)
              +miss = Bool.not(ok)
              +hit = Bool.and(ok, solid)
              +ns = Bool.pick(U32, miss, 3, Bool.pick(U32, hit, 1, 2))
              dda(p, (world, gv), ns, ix, iy, iz, ax, ay, az, t, last)
            case 1:
              (world, mk_hit(Cell.material(gv), last, ax, ay, az, t))
            case 2:
              match ax:
                case Axis{+nx, +tx, +dtx}:
                  match ay:
                    case Axis{+ny, +ty, +dty}:
                      match az:
                        case Axis{+nz, +tz, +dtz}:
                          +xf = Bool.and(F32.is_le(tx, ty), F32.is_le(tx, tz))
                          +yf = Bool.and(Bool.not(xf), F32.is_le(ty, tz))
                          +zf = Bool.not(Bool.or(xf, yf))
                          +nix = Bool.pick(U32, xf, Bool.pick(U32, nx, U32.sub(ix, 1), U32.add(ix, 1)), ix)
                          +niy = Bool.pick(U32, yf, Bool.pick(U32, ny, U32.sub(iy, 1), U32.add(iy, 1)), iy)
                          +niz = Bool.pick(U32, zf, Bool.pick(U32, nz, U32.sub(iz, 1), U32.add(iz, 1)), iz)
                          +nax = Bool.pick(Axis, xf, Axis{nx, F32.add(tx, dtx), dtx}, ax)
                          +nay = Bool.pick(Axis, yf, Axis{ny, F32.add(ty, dty), dty}, ay)
                          +naz = Bool.pick(Axis, zf, Axis{nz, F32.add(tz, dtz), dtz}, az)
                          +nt = Bool.pick(F32, xf, tx, Bool.pick(F32, yf, ty, tz))
                          +nlast = Bool.pick(U32, xf, 0, Bool.pick(U32, yf, 1, 2))
                          q = Array.get(U32, world, Grid.index(nix, niy, niz))
                          dda(p, q, 0, nix, niy, niz, nax, nay, naz, nt, nlast)
            case _:
              (world, Miss{})

# `trace` marches the first non-empty cell for a ray whose origin is inside the
# box. Direction need not be unit, but `t` is then in units of |d|. The first
# cell's word is fetched here so `dda`'s two-call loop can start.
def trace(
  world: Array<U32>, +ox: F32, +oy: F32, +oz: F32,
  +dx: F32, +dy: F32, +dz: F32
) -> Array<U32> & Hit:
  +ix = F32.to_u32(F32.floor(ox))
  +iy = F32.to_u32(F32.floor(oy))
  +iz = F32.to_u32(F32.floor(oz))
  q = Array.get(U32, world, Grid.index(ix, iy, iz))
  dda(Nat.mul(2n, dda_steps()), q, 0, ix, iy, iz,
      axis_init(ox, ix, dx), axis_init(oy, iy, dy), axis_init(oz, iz, dz), 0.0, 3)

# ---------------------------------------------------------------- shading ---
# Palette copied from runners/window.bend so 2D and 3D agree on materials.
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

def sky() -> U32:
  660512

def lx() -> F32:
  0.45

def ly() -> F32:
  0.80

def lz() -> F32:
  0.40

def byte_of(+f: F32) -> U32:
  U32.min(F32.to_u32(F32.max(f, 0.0)), 255)

def scale(+c: U32, +f: F32) -> U32:
  +r = byte_of(F32.mul(U32.to_f32(U32.shrn(U32.and(c, 16711680), 16n)), f))
  +g = byte_of(F32.mul(U32.to_f32(U32.shrn(U32.and(c, 65280), 8n)), f))
  +b = byte_of(F32.mul(U32.to_f32(U32.and(c, 255)), f))
  U32.or(U32.shln(r, 16n), U32.or(U32.shln(g, 8n), b))

# Face-normal lambert with a 0.25 ambient floor, so back faces stay readable.
def lambert(nx: F32, ny: F32, nz: F32) -> F32:
  +d = F32.add(F32.add(F32.mul(nx, lx()), F32.mul(ny, ly())), F32.mul(nz, lz()))
  F32.max(d, 0.25)

def shade(h: Hit) -> U32:
  match h:
    case Miss{}:
      sky()
    case Hit{mat, nx, ny, nz, t}:
      scale(color_of(mat), lambert(nx, ny, nz))

def shade_pair(q: Array<U32> & Hit) -> Array<U32> & U32:
  match q:
    case (w2, h):
      (w2, shade(h))

# ---------------------------------------------------------------- viewport --
# Smallest k with 2^k >= n (n >= 1). `fuel` bounds the search (n <= 2^32) and
# `done` is threaded so the loop can branch on a parameter, not a computed Bool.
def clog2_go(fuel: Nat, +n: U32, +k: Nat, +p: U32, done: Bool) -> Nat:
  match fuel:
    case 0n:
      k
    case 1n+f:
      match done:
        case True{}:
          k
        case False{}:
          +np = U32.mul(p, 2)
          clog2_go(f, n, Nat.add(k, 1n), np, Bool.not(U32.is_lt(np, n)))

def clog2(+n: U32) -> Nat:
  clog2_go(32n, n, 0n, 1, Bool.not(U32.is_lt(1, n)))

# The backend's power-of-two window exponent.
def window_bits(w: U32, h: U32) -> Nat:
  clog2(U32.max(w, h))

# s = k - d: how many low bits of each window coordinate the image upscales.
def scale_bits(w: U32, h: U32, +depth: Nat) -> Nat:
  Nat.sub(window_bits(w, h), depth)

# ceil(n / 2^s): the number of image cells the window shows on that axis.
def vis_dim(+n: U32, +s: Nat) -> U32:
  +d = U32.shln(1, Nat.min(s, 31n))
  U32.div(U32.add(n, U32.sub(d, 1)), d)

def cast(world: Array<U32>, cam: Cam, +cw: U32, +ch: U32, +px: U32, +py: U32) -> Array<U32> & U32:
  match cam:
    case Cam{ox, oy, oz, fx, fy, fz, rx, ry, rz, ux, uy, uz}:
      +xf = U32.to_f32(cw)
      +yf = U32.to_f32(ch)
      +aspect = F32.div(xf, yf)
      +sx = F32.mul(F32.mul(F32.sub(F32.div(F32.mul(F32.add(U32.to_f32(px), 0.5), 2.0), xf), 1.0),
                            tan_half()), aspect)
      +sy = F32.mul(F32.sub(1.0, F32.div(F32.mul(F32.add(U32.to_f32(py), 0.5), 2.0), yf)),
                    tan_half())
      +dx0 = F32.add(F32.add(fx, F32.mul(rx, sx)), F32.mul(ux, sy))
      +dy0 = F32.add(F32.add(fy, F32.mul(ry, sx)), F32.mul(uy, sy))
      +dz0 = F32.add(F32.add(fz, F32.mul(rz, sx)), F32.mul(uz, sy))
      +len = F32.sqrt(F32.add(F32.add(F32.mul(dx0, dx0), F32.mul(dy0, dy0)),
                              F32.mul(dz0, dz0)))
      shade_pair(trace(world, ox, oy, oz,
                       F32.div(dx0, len), F32.div(dy0, len), F32.div(dz0, len)))

# ------------------------------------------------------------------ image ---
# Depth 0 emits one leaf per pixel in top-left, top-right, bottom-left,
# bottom-right order; the list is reversed and grouped four at a time so
# `levels` rebuilds the quadtree bottom-up.
def leaf_cast(q: Array<U32> & U32, acc: List<Image>) -> Array<U32> & List<Image>:
  match q:
    case (w2, c):
      (w2, Pix{c} <> acc)

# Outside the viewport (the unused bottom-right of the square): sky, no raycast.
def render_leaf(
  vis: Bool, cam: Cam, +cw: U32, +ch: U32, +x0: U32, +y0: U32,
  gp: Array<U32> & List<Image>
) -> Array<U32> & List<Image>:
  match vis:
    case True{}:
      match gp:
        case (world, acc):
          leaf_cast(cast(world, cam, cw, ch, x0, y0), acc)
    case False{}:
      match gp:
        case (world, acc):
          (world, Pix{sky()} <> acc)

def render_q(
  fuel: Nat, +cam: Cam, +cw: U32, +ch: U32, +size: U32, +x0: U32, +y0: U32,
  gp: Array<U32> & List<Image>
) -> Array<U32> & List<Image>:
  match fuel:
    case 0n:
      render_leaf(Bool.and(U32.is_lt(x0, cw), U32.is_lt(y0, ch)),
                  cam, cw, ch, x0, y0, gp)
    case 1n+ +p:
      +h = U32.shr(size)
      render_q(p, cam, cw, ch, h, U32.add(x0, h), U32.add(y0, h),
        render_q(p, cam, cw, ch, h, x0, U32.add(y0, h),
          render_q(p, cam, cw, ch, h, U32.add(x0, h), y0,
            render_q(p, cam, cw, ch, h, x0, y0, gp))))

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
    case 1n+ +p:
      levels(p, group4(imgs))

def root_img(imgs: List<Image>) -> Image:
  match imgs:
    case Nil{}:
      Pix{0}
    case h <> _:
      h

def finish_image(r: Array<U32> & List<Image>, +fuel: Nat) -> Array<U32> & Image:
  match r:
    case (w2, leafs):
      (w2, root_img(levels(fuel, List.reverse(&1, Image, leafs))))

# Square render: `fuel` is the quadtree depth, the image is 2^fuel x 2^fuel.
def image(+fuel: Nat, world: Array<U32>, cam: Cam) -> Array<U32> & Image:
  +size = U32.shln(1, fuel)
  finish_image(render_q(fuel, cam, size, size, size, 0, 0, (world, Nil{})), fuel)

# Windowed render: the aspect-correct, integer-scaled sub-image a w x h window
# shows of a depth-`depth` quadtree (see the header).
def view_image(+w: U32, +h: U32, +depth: Nat, world: Array<U32>, cam: Cam) -> Array<U32> & Image:
  +s = scale_bits(w, h, depth)
  +cw = vis_dim(w, s)
  +vh = vis_dim(h, s)
  +size = U32.shln(1, depth)
  finish_image(render_q(depth, cam, cw, vh, size, 0, 0, (world, Nil{})), depth)
