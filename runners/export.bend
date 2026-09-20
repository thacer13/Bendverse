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
# Three files are written:
#   * a chunk-oriented world snapshot (dense over the 64^3 world),
#   * gen reference vectors sampled from `Worldgen.gen`, and
#   * shell-free terrain vectors sampled from `Worldgen.gen_terrain` (the
#     oracle a renderer port needs when the shell is window-relative).
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
#   32      ...           chunk_count chunk records, chunk-ordinal
#
#   Chunk record (16388 bytes):
#     +0    4             key            (`Chunk.key(kx, ky, kz)`, 10/10/10 bits)
#     +4    16384         cell words     `Chunk.cells` = 4096 x u32
#
#   Record order is chunk-ordinal: `ci = 0..63` with `kx` fastest, then `ky`,
#   then `kz` (`Chunk.key(ci&3, (ci>>2)&3, (ci>>4)&3)`). This is NOT monotonic
#   in the packed key value — a key-indexed parser must map by key, not assume
#   sorted records.
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
#
# ----------------------------------------------------------------------------
# TERRAIN REFERENCE FILE  (default `bendverse-terrain.bgt`)
# ----------------------------------------------------------------------------
#   The shell-free companion of the gen vectors: the SAME header/record shape,
#   but each word is `Worldgen.gen_terrain(x,y,z,seed)` -- `gen` with the
#   bedrock shell on the ABSOLUTE planes x/y/z in {0,63} removed. Bendview's
#   WGSL `gen` is bit-exact but has no oracle for the shell-free sampler; this
#   file is it, and it must reject a port that bakes the shell in or masks
#   coordinates to the 64 box.
#
#   offset  size          field
#   0       4             magic, ASCII "BGT1" = 66 71 84 49
#   4       4             version        = 1
#   8       4             seed (header)  = 42
#   12      4             vector_count   = 784
#   16      ...           vector_count records, each 20 bytes:
#                           +0  u32 x
#                           +4  u32 y
#                           +8  u32 z
#                           +12 u32 seed
#                           +16 u32 word   (Worldgen.gen_terrain(x,y,z,seed))
#
#   The sample is the 7x8x7 cross product
#     x,z in {0, 21, 42, 63, 64, 80, 200}   (shell, interior, out-of-box)
#     y   in {0, 8, 20, 42, 63, 64, 80, 200}
#   crossed with seeds {42, 43}, ordered x-major with seed slowest. It holds a
#   coordinate on every shell plane, coordinates OUTSIDE the 64 box on every
#   axis (a `&63`-masking port folds 64->0, 80->16, 200->8 and lands on a
#   shell), and interiors covering the Empty/Sand/Rock words. Together with the
#   shell planes -- where `gen` paints bedrock but `gen_terrain` does not -- the
#   sample spans all four material classes 0/1/2/3, yet no `gen_terrain` word is
#   ever bedrock. That is the shell-free property a port must reproduce.
#
#   Total size: 16 + 784 * 20 = 15696 bytes.
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

# --------------------------------------------------------------- chunk records
# A snapshot record is a 16^3 *chunk* keyed by `Chunk.key`, in `Store.chunk_list`
# local order: local index `i` addresses the world word
# `Grid.index(Chunk.global_x(k,i), Chunk.global_y(k,i), Chunk.global_z(k,i))`.
# This is the mapping `Store.assemble_chunk` writes and `runners/serve.bend`
# reads, and it is the *only* correct record content. Slicing the flat
# `Grid.index` array every 4096 words is NOT a chunk (`Grid.index = x + z*64 +
# y*4096`, so `gi / 4096 = y` is a `y`-plane) — that was the G-bridge-2 defect.
#
# The world word a chunk record's local offset `i` addresses: the inverse of
# `Chunk.local` composed with `Grid.index` (what `Store.assemble_chunk` writes).
# The G-bridge-2 defect read `Grid.index`-slice offset `ci*4096 + i` instead.
def bxe_cell_index(+k: U32, +i: U32) -> U32:
  Grid.index(Chunk.global_x(k, i), Chunk.global_y(k, i), Chunk.global_z(k, i))

# `k` and `i` are `+` so the three axis projections may each consume them; `q`
# is the `(world, value)` pair from `Array.get`, matched as a parameter (`Array`
# is affine and a local let cannot be a scrutinee). The walk is DESCENDING (`i`
# down to 0) and conses, so the head is local index 0 and the record comes out in
# forward `Chunk.local` order — walking ascending and consing reverses it (the
# G-bridge-2 order residual, §10). The fuel-0 read is discarded; its index is
# clamped so it cannot underflow.
def bxe_chunk_cells_go(
  fuel: Nat, +k: U32, +i: U32, q: Array<U32> & U32, acc: List<&2, U32>
) -> Array<U32> & List<&2, U32>:
  match fuel:
    case 0n:
      match q:
        case (world, v):
          (world, acc)
    case 1n+p:
      match q:
        case (world, v):
          +ni = U32.min(U32.sub(i, 1), i)
          bxe_chunk_cells_go(p, k, ni, Array.get(U32, world, bxe_cell_index(k, ni)), v <> acc)

def bxe_chunk_cells(world: Array<U32>, +k: U32) -> Array<U32> & List<&2, U32>:
  +last = U32.sub(Chunk.cells(), 1)
  bxe_chunk_cells_go(U32.to_nat(Chunk.cells()), k, last, Array.get(U32, world, bxe_cell_index(k, last)), Nil{})

# Cons the little-endian bytes of each cell in front of `tail` (forward order).
def bxe_cell_words(cells: List<&2, U32>, tail: List<&2, U32>) -> List<&2, U32>:
  match cells:
    case Nil{}:
      tail
    case Con{h, t}:
      bxe_u32_le(h, bxe_cell_words(t, tail))

# `key <> cells <> acc` for one chunk, matched through a parameter (the
# chunk-cells pair is computed, and a computed pair is not a scrutinee).
def bxe_rec_if(
  r: Array<U32> & List<&2, U32>, +k: U32, acc: List<&2, U32>
) -> Array<U32> & List<&2, U32>:
  match r:
    case (world, cells):
      (world, bxe_u32_le(k, bxe_cell_words(cells, acc)))

# Walk keys DESCENDING so prepending yields a chunk-ordinal record set (`ci`
# ascending = `kx` fastest, then `ky`, then `kz`; not packed-key-monotonic).
# the header comment specifies and the sparse path (`serve.bend`) emits.
def bxe_records_go(
  fuel: Nat, +ci: U32, r: Array<U32> & List<&2, U32>
) -> Array<U32> & List<&2, U32>:
  match fuel:
    case 0n:
      r
    case 1n+p:
      match r:
        case (world, acc):
          +k = Chunk.key(U32.and(ci, 3), U32.and(U32.shrn(ci, 2n), 3), U32.and(U32.shrn(ci, 4n), 3))
          bxe_records_go(p, U32.min(U32.sub(ci, 1), ci), bxe_rec_if(bxe_chunk_cells(world, k), k, acc))

def bxe_body(ticks: U32, r: Array<U32> & List<&2, U32>) -> List<&2, U32>:
  match r:
    case (world, recs):
      List.append(&2, U32, bxe_snap_header(ticks, Nil{}), recs)

def bxe_snapshot_bytes(world: Array<U32>, +ticks: U32) -> List<&2, U32>:
  bxe_body(ticks, bxe_records_go(64n, 63, (world, Nil{})))

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

# ------------------------------------------------------------- terrain vectors
# Coordinate tables: both shell planes ({0,63}), two interiors ({21,42}), and
# three coordinates OUTSIDE the fixed 64 box ({64,80,200}). The out-of-box
# values are the ones a torus/masked port cannot reproduce: `gen_terrain` is a
# pure function of the absolute coordinate and must not fold `x & 63`.
def genvec_xv(j: U32) -> U32:
  match j:
    case 0:
      0
    case 1:
      21
    case 2:
      42
    case 3:
      63
    case 4:
      64
    case 5:
      80
    case _:
      200

def genvec_zv(j: U32) -> U32:
  genvec_xv(j)

# y adds 8 (rock) and 20 (sand) interiors; 0/63 are shell planes.
def genvec_yv(j: U32) -> U32:
  match j:
    case 0:
      0
    case 1:
      8
    case 2:
      20
    case 3:
      42
    case 4:
      63
    case 5:
      64
    case 6:
      80
    case _:
      200

def genvec_nx() -> U32:
  7

def genvec_ny() -> U32:
  8

def genvec_nz() -> U32:
  7

def genvec_seed_levels() -> U32:
  2

# One (seed) plane: nx*ny*nz = 392.
def genvec_plane() -> U32:
  U32.mul(U32.mul(genvec_nx(), genvec_ny()), genvec_nz())

def genvec_terrain_count() -> U32:
  U32.mul(genvec_plane(), genvec_seed_levels())

# Record `c` (ascending) reads x-major: x slowest, then y, then z, seed slowest.
def genvec_rec_x(+c: U32) -> U32:
  genvec_xv(U32.div(U32.mod(c, genvec_plane()), U32.mul(genvec_ny(), genvec_nz())))

def genvec_rec_y(+c: U32) -> U32:
  genvec_yv(U32.mod(U32.div(c, genvec_nz()), genvec_ny()))

def genvec_rec_z(+c: U32) -> U32:
  genvec_zv(U32.mod(c, genvec_nz()))

def genvec_rec_seed(+c: U32) -> U32:
  U32.add(bxe_seed(), U32.div(c, genvec_plane()))

# `fuel` counts vectors (784 down to 0); `c` descends so records come out
# ascending. Each record is (x, y, z, seed, gen_terrain word), little-endian.
def genvec_terrain_records(fuel: Nat, +c: U32, tail: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      tail
    case 1n+p:
      +x = genvec_rec_x(c)
      +y = genvec_rec_y(c)
      +z = genvec_rec_z(c)
      +s = genvec_rec_seed(c)
      w = Worldgen.gen_terrain(x, y, z, s)
      rec = bxe_u32_le(x, bxe_u32_le(y, bxe_u32_le(z, bxe_u32_le(s, bxe_u32_le(w, tail)))))
      genvec_terrain_records(p, U32.sub(c, 1), rec)

def genvec_magic_bgt(tail: List<&2, U32>) -> List<&2, U32>:
  66 <> (71 <> (84 <> (49 <> tail)))

def genvec_terrain_bytes() -> List<&2, U32>:
  genvec_magic_bgt(
    bxe_u32_le(bxe_version(),
      bxe_u32_le(bxe_seed(),
        bxe_u32_le(genvec_terrain_count(),
          genvec_terrain_records(U32.to_nat(genvec_terrain_count()), U32.sub(genvec_terrain_count(), 1), Nil{})))))

def genvec_terrain_size() -> U32:
  U32.add(16, U32.mul(genvec_terrain_count(), 20))

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
  BxeCfg{ticks: U32, snap: String, gen: String, terrain: String}

def bxe_default_cfg() -> BxeCfg:
  BxeCfg{0, "bendverse-snapshot.bvs", "bendverse-gen.bvg", "bendverse-terrain.bgt"}

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
    case BxeCfg{ticks, snap, gen, terrain}:
      BxeCfg{v, snap, gen, terrain}

def bxe_set_snap(cfg: BxeCfg, +v: String) -> BxeCfg:
  match cfg:
    case BxeCfg{ticks, snap, gen, terrain}:
      BxeCfg{ticks, v, gen, terrain}

def bxe_set_gen(cfg: BxeCfg, +v: String) -> BxeCfg:
  match cfg:
    case BxeCfg{ticks, snap, gen, terrain}:
      BxeCfg{ticks, snap, v, terrain}

def genvec_set_terrain(cfg: BxeCfg, +v: String) -> BxeCfg:
  match cfg:
    case BxeCfg{ticks, snap, gen, terrain}:
      BxeCfg{ticks, snap, gen, v}

# Parse `--ticks N`, `--snapshot PATH`, `--gen PATH`, `--terrain PATH`; anything else is ignored.
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
        case "--terrain":
          match tail:
            case Nil{}:
              cfg
            case Con{head2, tail2}:
              bxe_parse(tail2, genvec_set_terrain(cfg, head2))
        case _:
          bxe_parse(tail, cfg)

def bxe_summary(+ticks: U32, +snap: String, +gen: String, +terrain: String) -> String:
  "export: ticks=" ++ U32.show(ticks)
  ++ " snapshot=" ++ snap ++ " (" ++ U32.show(bxe_snapshot_size()) ++ "B)"
  ++ " gen=" ++ gen ++ " (" ++ U32.show(bxe_gen_size()) ++ "B)"
  ++ " terrain=" ++ terrain ++ " (" ++ U32.show(genvec_terrain_size()) ++ "B)"

def bxe_run(cfg: BxeCfg) -> IO(Unit):
  match cfg:
    case BxeCfg{+ticks, +snap, +gen, +terrain}:
      do IO<Unit>:
        base : Array<U32> = Sim.build()
        world : Array<U32> = Sim.ticks(U32.to_nat(ticks), base)
        bxe_write(snap, bxe_snapshot_bytes(world, ticks))
        bxe_write(gen, bxe_gen_bytes())
        bxe_write(terrain, genvec_terrain_bytes())
        IO.print(bxe_summary(ticks, snap, gen, terrain))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    bxe_run(bxe_parse(args, bxe_default_cfg()))
