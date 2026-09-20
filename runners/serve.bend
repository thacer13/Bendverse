import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/chunk.bend as Chunk
import ../src/store.bend as Store
import ../src/sim.bend as Sim
import ../scenarios/fixtures.bend as Fixtures
import ./export.bend as Export

# ============================================================================
# serve -- the writer side of the Bendview sidecar (track `bridge2`, B1/B2).
# Replaces the P2 skeleton with the real transport from `runners/SERVE.md`.
#
# B2 CONTRACT (one line): DELTA carries render-visible cell fields only
# (material/cohesion/support/fall); the activity bit (`Cell.active_mask`) is
# engine-internal, and wake-only activations (`Rules.WWake`) are not transmitted.
# A delta record is `(idx u32, word u32)` with `word = Cell.deactivate(new)` and
# `idx = Grid.index(x, y, z)` -- the GLOBAL 64^3 torus index, NOT window-local.
# (If the S1 window migration renumbers cells, only the payload interpretation
# changes; `idx` becomes whatever the scale track defines, and the framing below
# is unaffected because it names no coordinates.)
#
# Framing (SERVE.md §2), little-endian, coordinate-agnostic:
#   u32 payload_len, u32 kind, payload_len bytes
# kinds out : 0 HELLO, 1 SNAPSHOT, 2 DELTA, 3 PING, 4 BYE
# kinds in  : 5 CREDIT, 6 REQUEST, 7 STOP
#
# Snapshots. The FIRST SNAPSHOT is the dense genesis body and is byte-identical
# to `runners/export.bend` for the same world/tick (it calls
# `Export.bxe_snapshot_bytes`). A later
# checkpoint may be SPARSE: a chunk that is sleeping and bit-equal to pure gen is
# omitted, and `Store.assemble` regenerates it from `Worldgen.gen` (the store's
# sparse-overlay rule, coreidea rule 11). The header still carries `chunk_count`,
# so absent keys are simply not in the record set.
# ============================================================================

# ---------------------------------------------------------------- framing
def bridge2_frame(+kind: U32, +payload: List<&2, U32>) -> List<&2, U32>:
  +n = U32.from_nat(List.length(&2, U32, payload))
  Export.bxe_u32_le(n, Export.bxe_u32_le(kind, payload))

# HELLO: version, world_edge, chunk_edge, seed, tick. Every field is the
# engine's own constant, so the renderer can validate its port before trusting a
# single cell (SERVE.md §4.2).
def bridge2_hello(+tick: U32) -> List<&2, U32>:
  payload = Export.bxe_u32_le(1,
    Export.bxe_u32_le(Grid.size(),
      Export.bxe_u32_le(Chunk.size(),
        Export.bxe_u32_le(Export.bxe_seed(),
          Export.bxe_u32_le(tick, Nil{})))))
  bridge2_frame(0, payload)

def bridge2_ping(+tick: U32) -> List<&2, U32>:
  bridge2_frame(3, Export.bxe_u32_le(tick, Nil{}))

def bridge2_bye() -> List<&2, U32>:
  bridge2_frame(4, Nil{})

# ---------------------------------------------------------------- snapshots
# Dense (genesis / first snapshot): exactly the exporter's chunk-oriented body.
def bridge2_snapshot_dense(world: Array<U32>, +ticks: U32) -> List<&2, U32>:
  bridge2_frame(1, Export.bxe_snapshot_bytes(world, ticks))

# Declared size of that frame (8-byte header + the exporter's fixed body size),
# for the boundary test.
def bridge2_dense_frame_size() -> U32:
  U32.add(8, Export.bxe_snapshot_size())

# Sparse header, identical to `Export.bxe_snap_header` except that `count` is the
# number of resident chunks rather than the constant 64.
def bridge2_snap_header(+count: U32, ticks: U32, tail: List<&2, U32>) -> List<&2, U32>:
  Export.bxe_magic_bvs(
    Export.bxe_u32_le(Export.bxe_version(),
      Export.bxe_u32_le(Grid.size(),
        Export.bxe_u32_le(Chunk.size(),
          Export.bxe_u32_le(4,
            Export.bxe_u32_le(Export.bxe_seed(),
              Export.bxe_u32_le(ticks,
                Export.bxe_u32_le(count, tail))))))))

# Extract one world chunk's 4096 cell words in `Store.chunk_list` local order
# (ascending `Grid.index` within the chunk), threaded so the flat world is
# reusable. `acc` is built descending, which is ascending.
# `q` is the `(world, value)` pair from `Array.get` for local index `i`; it is a
# parameter because a computed `Array.get` may not be a match scrutinee. The
# final (fuel-0) read is discarded; its index is clamped so it cannot underflow.
def bridge2_chunk_cells_go(
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
          +ni = U32.add(i, 1)
          +nidx = Grid.index(Chunk.global_x(k, ni), Chunk.global_y(k, ni), Chunk.global_z(k, ni))
          bridge2_chunk_cells_go(p, k, ni, Array.get(U32, world, nidx), v <> acc)

def bridge2_chunk_cells(world: Array<U32>, +k: U32) -> Array<U32> & List<&2, U32>:
  bridge2_chunk_cells_go(U32.to_nat(Chunk.cells()), k, 0,
    Array.get(U32, world, Grid.index(Chunk.global_x(k, 0), Chunk.global_y(k, 0), Chunk.global_z(k, 0))), Nil{})

def bridge2_set_chunk(
  r: Array<U32> & List<&2, U32>, +k: U32, store: Store.Store
) -> Array<U32> & Store.Store:
  match r:
    case (world, cells):
      (world, Store.set(store, k, cells))

# Build a `Store` whose resident chunks are a world's chunks, so eviction (and
# thus the sparse snapshot) reuses the engine's own regenerability test.
def bridge2_world_store_go(
  fuel: Nat, +ci: U32, r: Array<U32> & Store.Store
) -> Array<U32> & Store.Store:
  match fuel:
    case 0n:
      r
    case 1n+p:
      match r:
        case (world, store):
          +k = Chunk.key(U32.and(ci, 3), U32.and(U32.shrn(ci, 2n), 3), U32.and(U32.shrn(ci, 4n), 3))
          bridge2_world_store_go(p, U32.add(ci, 1), bridge2_set_chunk(bridge2_chunk_cells(world, k), k, store))

def bridge2_world_store(world: Array<U32>) -> Array<U32> & Store.Store:
  bridge2_world_store_go(64n, 0, (world, Store.empty()))

# Presence test on a `Store.get` result (a computed `Maybe` cannot be matched
# directly).
def bridge2_is_some(m: Maybe<&2, List<&2, U32>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{val}:
      True{}

def bridge2_count_present_go(fuel: Nat, +ci: U32, +s: Store.Store, acc: U32) -> U32:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      +k = Chunk.key(U32.and(ci, 3), U32.and(U32.shrn(ci, 2n), 3), U32.and(U32.shrn(ci, 4n), 3))
      +add = Bool.pick(U32, bridge2_is_some(Store.get(s, k)), 1, 0)
      bridge2_count_present_go(p, U32.add(ci, 1), s, U32.add(acc, add))

# Cons the little-endian bytes of each cell in front of `tail` (forward order).
def bridge2_words_le_onto(cells: List<&2, U32>, tail: List<&2, U32>) -> List<&2, U32>:
  match cells:
    case Nil{}:
      tail
    case Con{h, t}:
      Export.bxe_u32_le(h, bridge2_words_le_onto(t, tail))

# Emit `key <> cells` for a present chunk, or nothing for an evicted one.
def bridge2_rec_if(
  m: Maybe<&2, List<&2, U32>>, +k: U32, tail: List<&2, U32>
) -> List<&2, U32>:
  match m:
    case None{}:
      tail
    case Some{cells}:
      Export.bxe_u32_le(k, bridge2_words_le_onto(cells, tail))

# Walk keys DESCENDING so prepending yields an ascending record set.
def bridge2_records_go(fuel: Nat, +ci: U32, +s: Store.Store, acc: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      acc
    case 1n+p:
      +k = Chunk.key(U32.and(ci, 3), U32.and(U32.shrn(ci, 2n), 3), U32.and(U32.shrn(ci, 4n), 3))
      +acc2 = bridge2_rec_if(Store.get(s, k), k, acc)
      bridge2_records_go(p, U32.min(U32.sub(ci, 1), ci), s, acc2)

# A sparse snapshot of an already-evicted store: header counts residents, body
# carries only residents. `Store.assemble` of the same store reproduces the
# world exactly (lossless: dropped chunks regenerate from pure gen).
def bridge2_snapshot_sparse(+store: Store.Store, +ticks: U32) -> List<&2, U32>:
  +count = bridge2_count_present_go(64n, 0, store, 0)
  h = bridge2_snap_header(count, ticks, Nil{})
  recs = bridge2_records_go(64n, 63, store, Nil{})
  bridge2_frame(1, List.append(&2, U32, h, recs))

# ------------------------------------------------------------------ deltas
# One record per `Sim.Delta`: (idx u32, render-visible word u32). See the B2
# contract above; `Sim.tick_trace` already omits `WWake` records.
def bridge2_delta_records(ds: List<Sim.Delta>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      Nil{}
    case Con{h, t}:
      match h:
        case Sim.Delta{x, y, z, val}:
          +idx = Grid.index(x, y, z)
          Export.bxe_u32_le(idx, Export.bxe_u32_le(Cell.deactivate(val), bridge2_delta_records(t)))

def bridge2_delta_frame(+tick: U32, ds: List<Sim.Delta>) -> List<&2, U32>:
  +recs = bridge2_delta_records(ds)
  +cnt = U32.div(U32.from_nat(List.length(&2, U32, recs)), 8)
  payload = Export.bxe_u32_le(tick, Export.bxe_u32_le(cnt, recs))
  bridge2_frame(2, payload)

# --------------------------------------------------------- control decoding
# Inbound frames (CREDIT/REQUEST/STOP, plus the outbound kinds for symmetry).
# The same header decoder serves both directions (SERVE.md §1).
type Bridge2Ctrl is Data:
  BCredit{frames: U32}
  BRequest{tick: U32, flags: U32}
  BStop{}
  BHello{}
  BSnapshot{}
  BDelta{}
  BPing{}
  BBye{}
  BUnknown{kind: U32}

def bridge2_u32_of_le(b0: U32, b1: U32, b2: U32, b3: U32) -> U32:
  (U32.or(b0, U32.or(U32.shln(b1, 8n), U32.or(U32.shln(b2, 16n), U32.shln(b3, 24n)))) : U32)

# Decode a byte list (length a multiple of 4) into little-endian u32 words.
def bridge2_dec_words(buf: List<&2, U32>) -> List<&2, U32>:
  match buf:
    case Nil{}:
      Nil{}
    case Con{b0, r1}:
      match r1:
        case Con{b1, r2}:
          match r2:
            case Con{b2, r3}:
              match r3:
                case Con{b3, r4}:
                  bridge2_u32_of_le(b0, b1, b2, b3) <> bridge2_dec_words(r4)
                case Nil{}:
                  Nil{}
            case Nil{}:
              Nil{}
        case Nil{}:
          Nil{}

def bridge2_word0(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      h

def bridge2_word1(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      bridge2_word0(t)

def bridge2_by_kind(+kind: U32, +payload: List<&2, U32>) -> Bridge2Ctrl:
  match kind:
    case 0:
      BHello{}
    case 1:
      BSnapshot{}
    case 2:
      BDelta{}
    case 3:
      BPing{}
    case 4:
      BBye{}
    case 5:
      BCredit{bridge2_word0(payload)}
    case 6:
      BRequest{bridge2_word0(payload), bridge2_word1(payload)}
    case 7:
      BStop{}
    case _:
      BUnknown{kind}

def bridge2_classify(ws: List<&2, U32>) -> Bridge2Ctrl:
  match ws:
    case Nil{}:
      BUnknown{4294967295}
    case Con{len, r1}:
      match r1:
        case Nil{}:
          BUnknown{4294967295}
        case Con{kind, payload}:
          bridge2_by_kind(kind, payload)

def bridge2_decode_control(frame: List<&2, U32>) -> Bridge2Ctrl:
  bridge2_classify(bridge2_dec_words(frame))

def bridge2_ctrl_show(c: Bridge2Ctrl) -> String:
  match c:
    case BCredit{frames}:
      "credit frames=" ++ U32.show(frames)
    case BRequest{tick, flags}:
      "request tick=" ++ U32.show(tick) ++ " flags=" ++ U32.show(flags)
    case BStop{}:
      "stop"
    case BHello{}:
      "hello"
    case BSnapshot{}:
      "snapshot"
    case BDelta{}:
      "delta"
    case BPing{}:
      "ping"
    case BBye{}:
      "bye"
    case BUnknown{kind}:
      "unknown kind=" ++ U32.show(kind)

# ---------------------------------------------------------------------- IO
# Open `/dev/stdout` in append mode: a redirect from the shell already truncated
# the file, and O_APPEND keeps successive frames ordered instead of truncating.
def bridge2_stdout(data: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("/dev/stdout", "a"))
    q : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, data)
    Export.bxe_finish(q)

def bridge2_read_finish(
  r: File & Result<&1, &1, U32 & String, List<&2, U32>>
) -> IO(Unit):
  match r:
    case (f, res):
      do IO<Unit>:
        bytes : List<&2, U32> <- IO.pass(List<&2, U32>, res)
        File.close(f)
        IO.print_err("serve: control " ++ bridge2_ctrl_show(bridge2_decode_control(bytes)) ++ "\n")

# Read one control frame's worth of bytes from stdin (op-in via `--control`, so a
# terminal run never blocks; a pipe/FIFO renderer supplies CREDIT/REQUEST/STOP).
def bridge2_read_control() -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("/dev/stdin", "r"))
    q : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f, 1048576)
    bridge2_read_finish(q)

def bridge2_control_if(b: Bool) -> IO(Unit):
  match b:
    case True{}:
      bridge2_read_control()
    case False{}:
      IO.pure(Unit, Unit{})

def bridge2_has_control(xs: List<&1, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{h, t}:
      match h:
        case "--control":
          True{}
        case _:
          bridge2_has_control(t)

# Sparse checkpoint: rebuild the chunk store from the ticked world, evict the
# sleeping gen-equal chunks (the regenerability test) and frame what remains.
def bridge2_checkpoint_store(r: Array<U32> & Store.Store, +tick: U32) -> IO(Unit):
  match r:
    case (world, store):
      do IO<Unit>:
        ev : Store.Store = Store.evict(store)
        bridge2_stdout(bridge2_snapshot_sparse(ev, tick))
        bridge2_stdout(bridge2_ping(tick))
        bridge2_stdout(bridge2_bye())
        IO.print_err("serve: checkpoint tick=" ++ U32.show(tick) ++ ", bye\n")

def bridge2_checkpoint(world: Array<U32>, +tick: U32) -> IO(Unit):
  bridge2_checkpoint_store(bridge2_world_store(world), tick)

# After the dense first snapshot, advance one tick and ship its render-visible
# delta, then a sparse checkpoint and a clean BYE.
def bridge2_tick_result(r: Array<U32> & List<Sim.Delta>) -> IO(Unit):
  match r:
    case (world, ds):
      do IO<Unit>:
        bridge2_stdout(bridge2_delta_frame(1, ds))
        bridge2_checkpoint(world, 1)

def bridge2_emit() -> IO(Unit):
  do IO<Unit>:
    IO.print_err("serve: hello\n")
    bridge2_stdout(bridge2_hello(0))
    bridge2_stdout(bridge2_snapshot_dense(Fixtures.spawn(Sim.build()), 0))
    IO.print_err("serve: dense snapshot tick=0\n")
    bridge2_tick_result(Sim.tick_trace(Fixtures.spawn(Sim.build())))

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    bridge2_emit()
    bridge2_control_if(bridge2_has_control(args))
