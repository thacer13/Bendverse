import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/chunk.bend as Chunk
import ../src/worldgen.bend as Worldgen
import ../src/sim.bend as Sim

# ============================================================================
# Bendverse export surface (track `bridge`, P0) — the binary format contract
# that Bendview reads. This file is IO (it is a runner), so it owns no engine
# semantics: it only reads the pure engine's `Array<U32>` and serialises it.
#
# Two files are written:
#   * a chunk-oriented world snapshot (dense over the 64^3 world), and
#   * gen reference vectors sampled from `Worldgen.gen`.
#
# Everything is little-endian. Records are u32 unless stated. The snapshot's
# unit is a *chunk record keyed by `Chunk.key`* — never a flat 64^3 blob.
#
# ----------------------------------------------------------------------------
# SNAPSHOT FILE  (default `bendverse-snapshot.bvs`)
# ----------------------------------------------------------------------------
#   offset  size          field
#   0       4             magic, ASCII "BVS1" = 42 56 53 31
#   4       4             version        = 1
#   8       4             world_edge     = 64   (Grid.size)
#   12      4             chunk_edge     = 16   (Chunk.size)
#   16      4             chunks_per_axis= 4    (world_edge / chunk_edge)
#   20      4             seed           = 42   (Worldgen.seed)
#   24      4             ticks          = N    (Sim ticks applied)
#   28      4             chunk_count    = 64   (= chunks_per_axis^3)
#   32      ...           chunk_count chunk records, key-ascending
#
#   Chunk record (16388 bytes):
#     +0    4             key            (`Chunk.key(kx, ky, kz)`, 10/10/10 bits)
#     +4    16384         cell words     `Chunk.cells` = 4096 x u32
#
#   Cell order inside a record is the chunk-local index order that
#   `Store.chunk_list` uses (ascending `Grid.index` restricted to the chunk):
#     i = 0 .. 4095,  local_x = i & 15, local_z = (i >> 4) & 15,
#     local_y = (i >> 8) & 15,
#   so `Grid.index(Chunk.global_x(k,i), Chunk.global_y(k,i), Chunk.global_z(k,i))`
#   addresses the same word in the engine's flat world. A key absent from the
#   record set is regenerated from `Worldgen.gen` (the store's sparse-overlay
#   rule, coreidea rule 11); this exporter writes all 64 keys (dense).
#
#   Total size: 32 + 64 * 16388 = 1048864 bytes.
#
# ----------------------------------------------------------------------------
# GEN REFERENCE FILE  (default `bendverse-gen.bvg`)
# ----------------------------------------------------------------------------
#   offset  size          field
#   0       4             magic, ASCII "BVG1" = 42 56 71 31
#   4       4             version        = 1
#   8       4             seed (header)  = 42
#   12      4             vector_count   = 128
#   16      ...           vector_count records, each 20 bytes:
#                           +0  u32 x
#                           +4  u32 y
#                           +8  u32 z
#                           +12 u32 seed
#                           +16 u32 word   (Worldgen.gen(x,y,z,seed))
#
#   The sample is the 4x4x4 grid crossed with seeds {42,43}: x,z in
#   {0,21,42,63} (both boundaries and interiors), y in {0,8,20,42} (bedrock
#   border, rock, sand, empty), so every one of `gen`'s four output classes
#   (materials 0/1/2/3) appears and a port must match bit-for-bit at every
#   point. Ordering is x-major over the counters, seed slowest.
#
#   Total size: 16 + 128 * 20 = 2576 bytes.
# ============================================================================

def bxe_seed() -> U32:
  Worldgen.seed()

def bxe_version() -> U32:
  1

def bxe_gen_count() -> U32:
  128

# ---------------------------------------------------------------- LE encoding
# Cons the four little-endian bytes of `w` in front of `tail`.
def bxe_u32_le(+w: U32, tail: List<&2, U32>) -> List<&2, U32>:
  b0 = U32.and(w, 255)
  b1 = U32.and(U32.shrn(w, 8n), 255)
  b2 = U32.and(U32.shrn(w, 16n), 255)
  b3 = U32.and(U32.shrn(w, 24n), 255)
  b0 <> (b1 <> (b2 <> (b3 <> tail)))

def bxe_magic_bvs(tail: List<&2, U32>) -> List<&2, U32>:
  66 <> (86 <> (83 <> (49 <> tail)))

def bxe_magic_bvg(tail: List<&2, U32>) -> List<&2, U32>:
  66 <> (86 <> (71 <> (49 <> tail)))

# ------------------------------------------------------------------ snapshot
# Snapshot header. Written in forward order (magic first), so it is built as
# `magic(version << ... << count << tail)`.
def bxe_snap_header(ticks: U32, tail: List<&2, U32>) -> List<&2, U32>:
  bxe_magic_bvs(
    bxe_u32_le(bxe_version(),
      bxe_u32_le(Grid.size(),
        bxe_u32_le(Chunk.size(),
          bxe_u32_le(4,
            bxe_u32_le(bxe_seed(),
              bxe_u32_le(ticks,
                bxe_u32_le(64, tail))))))))

# Emit the chunk key in front of `acc` when `cond`. Matching on the boolean
# *parameter* is what Bend requires (a computed scrutinee needs its own def).
def bxe_key_if(cond: Bool, +k: U32, acc: List<&2, U32>) -> List<&2, U32>:
  match cond:
    case True{}:
      bxe_u32_le(k, acc)
    case False{}:
      acc

# Walk the flat world *descending* in `Grid.index`, consing each word's four
# little-endian bytes as a group: because the last word processed is index 0,
# the result is the forward byte stream with each word internally forward (no
# whole-list reverse, which would also flip the bytes inside a word). Descending
# order is the chunk store read backwards: `ci = gi / 4096` is the chunk,
# `i = gi % 4096` its local index, and the chunk key is emitted *after* its
# local cell 0 so that, once consed, it lands just before that cell.
#
# `q` is the `(world, value)` pair from `Array.get`, matched as a parameter
# (`Array` is affine and a local let cannot be a scrutinee). `fuel` counts cells.
def bxe_cells(
  fuel: Nat, q: Array<U32> & U32, +gi: U32, acc: List<&2, U32>
) -> List<&2, U32>:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      match q:
        case (world, v):
          +ci = U32.div(gi, Chunk.cells())
          +i = U32.mod(gi, Chunk.cells())
          +k = Chunk.key(U32.and(ci, 3), U32.and(U32.shrn(ci, 2n), 3), U32.and(U32.shrn(ci, 4n), 3))
          acc1 = bxe_u32_le(v, acc)
          acc2 = bxe_key_if(U32.is_zero(i), k, acc1)
          # Clamp so index 0 re-reads itself instead of underflowing; the value
          # is discarded by the fuel-0 call.
          +ngi = U32.min(U32.sub(gi, 1), gi)
          bxe_cells(p, Array.get(U32, world, ngi), ngi, acc2)

def bxe_snapshot_bytes(world: Array<U32>, +ticks: U32) -> List<&2, U32>:
  h = bxe_snap_header(ticks, Nil{})
  +last = U32.sub(Grid.volume(), 1)
  cells = bxe_cells(U32.to_nat(Grid.volume()), Array.get(U32, world, last), last, Nil{})
  List.append(&2, U32, h, cells)

def bxe_snapshot_size() -> U32:
  U32.add(32, U32.mul(64, 16388))

# --------------------------------------------------------------- gen vectors
# x/z axis values {0, 21, 42, 63}: the two borders and two interiors.
def bxe_coord(j: U32) -> U32:
  U32.mul(U32.and(j, 3), 21)

# y axis values {0, 8, 20, 42}: bedrock border, rock, sand, empty. Chosen so
# the 128 vectors cover all four `gen` material classes.
def bxe_coord_y(j: U32) -> U32:
  match j:
    case 0:
      0
    case 1:
      8
    case 2:
      20
    case _:
      42

def bxe_gen_seed(c: U32) -> U32:
  U32.add(bxe_seed(), U32.div(c, 64))

# `fuel` counts vectors (128 down to 0); `c` descends so records come out
# ascending. c = ix*16 + iy*4 + iz + seed_extra*64 (see header comment).
def bxe_gen_records(fuel: Nat, +c: U32, tail: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      tail
    case 1n+p:
      +x = bxe_coord(U32.div(c, 16))
      +y = bxe_coord_y(U32.and(U32.div(c, 4), 3))
      +z = bxe_coord(c)
      +s = bxe_gen_seed(c)
      w = Worldgen.gen(x, y, z, s)
      rec = bxe_u32_le(x, bxe_u32_le(y, bxe_u32_le(z, bxe_u32_le(s, bxe_u32_le(w, tail)))))
      bxe_gen_records(p, U32.sub(c, 1), rec)

def bxe_gen_bytes() -> List<&2, U32>:
  bxe_magic_bvg(
    bxe_u32_le(bxe_version(),
      bxe_u32_le(bxe_seed(),
        bxe_u32_le(bxe_gen_count(),
          bxe_gen_records(U32.to_nat(bxe_gen_count()), U32.sub(bxe_gen_count(), 1), Nil{})))))

def bxe_gen_size() -> U32:
  U32.add(16, U32.mul(bxe_gen_count(), 20))

# ---------------------------------------------------------------------- IO
# `File.write_bytes` hands the affine handle back beside its `Result`; drain it
# (IO.pass exits on failure) and close.
def bxe_finish(q: File & Result<&1, &1, U32 & String, Unit>) -> IO(Unit):
  match q:
    case (f, res):
      do IO<Unit>:
        u : Unit <- IO.pass(Unit, res)
        File.close(f)

def bxe_write(path: String, data: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open(path, "w"))
    q : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, data)
    bxe_finish(q)

# ------------------------------------------------------------- config / args
type BxeCfg is Data:
  BxeCfg{ticks: U32, snap: String, gen: String}

def bxe_default_cfg() -> BxeCfg:
  BxeCfg{0, "bendverse-snapshot.bvs", "bendverse-gen.bvg"}

def bxe_num_m(m: Maybe<&2, U32>, d: U32) -> U32:
  match m:
    case None{}:
      d
    case Some{n}:
      n

def bxe_num(s: String, d: U32) -> U32:
  bxe_num_m(U32.read(s), d)

def bxe_set_ticks(cfg: BxeCfg, +v: U32) -> BxeCfg:
  match cfg:
    case BxeCfg{ticks, snap, gen}:
      BxeCfg{v, snap, gen}

def bxe_set_snap(cfg: BxeCfg, +v: String) -> BxeCfg:
  match cfg:
    case BxeCfg{ticks, snap, gen}:
      BxeCfg{ticks, v, gen}

def bxe_set_gen(cfg: BxeCfg, +v: String) -> BxeCfg:
  match cfg:
    case BxeCfg{ticks, snap, gen}:
      BxeCfg{ticks, snap, v}

# Parse `--ticks N`, `--snapshot PATH`, `--gen PATH`; anything else is ignored.
def bxe_parse(xs: List<&1, String>, cfg: BxeCfg) -> BxeCfg:
  match xs:
    case Nil{}:
      cfg
    case Con{head, tail}:
      match head:
        case "--ticks":
          match tail:
            case Nil{}:
              cfg
            case Con{head2, tail2}:
              bxe_parse(tail2, bxe_set_ticks(cfg, bxe_num(head2, 0)))
        case "--snapshot":
          match tail:
            case Nil{}:
              cfg
            case Con{head2, tail2}:
              bxe_parse(tail2, bxe_set_snap(cfg, head2))
        case "--gen":
          match tail:
            case Nil{}:
              cfg
            case Con{head2, tail2}:
              bxe_parse(tail2, bxe_set_gen(cfg, head2))
        case _:
          bxe_parse(tail, cfg)

def bxe_summary(+ticks: U32, +snap: String, +gen: String) -> String:
  "export: ticks=" ++ U32.show(ticks)
  ++ " snapshot=" ++ snap ++ " (" ++ U32.show(bxe_snapshot_size()) ++ "B)"
  ++ " gen=" ++ gen ++ " (" ++ U32.show(bxe_gen_size()) ++ "B)"

def bxe_run(cfg: BxeCfg) -> IO(Unit):
  match cfg:
    case BxeCfg{+ticks, +snap, +gen}:
      do IO<Unit>:
        base : Array<U32> = Sim.build()
        world : Array<U32> = Sim.ticks(U32.to_nat(ticks), base)
        bxe_write(snap, bxe_snapshot_bytes(world, ticks))
        bxe_write(gen, bxe_gen_bytes())
        IO.print(bxe_summary(ticks, snap, gen))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    bxe_run(bxe_parse(args, bxe_default_cfg()))
