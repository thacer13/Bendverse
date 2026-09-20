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
# Strict payload byte count for the frame header. `List.length` is NOT
# tail-recursive (`1n+List.length(...)`), so measuring a dense snapshot (262216
# words) or a large sparse body overflows the machine stack. This accumulator
# walk is tail-recursive and constant-stack, so framing survives any payload the
# writer can actually hold. (The frame header needs the byte count; `payload` is
# a `List<&2, U32>` of bytes, so the length IS the count.)
def bridge2_len_go(xs: List<&2, U32>, +acc: Nat) -> Nat:
  match xs:
    case Nil{}: acc
    case Con{h, t}: bridge2_len_go(t, 1n+acc)

def bridge2_len(+xs: List<&2, U32>) -> Nat:
  bridge2_len_go(xs, 0n)

def bridge2_frame(+kind: U32, +payload: List<&2, U32>) -> List<&2, U32>:
  +n = U32.from_nat(bridge2_len(payload))
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

# (the chunk gather moved to `runners/export.bend` as `bxe_chunk_cells`, so the
# dense and sparse snapshot paths share one correct `Chunk.local` gather —
# G-bridge-2. The dense encoder was the one that was wrong.)

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
          bridge2_world_store_go(p, U32.add(ci, 1), bridge2_set_chunk(Export.bxe_chunk_cells(world, k), k, store))

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

# Emit `key <> cells` for a present chunk, or nothing for an evicted one.
def bridge2_rec_if(
  m: Maybe<&2, List<&2, U32>>, +k: U32, tail: List<&2, U32>
) -> List<&2, U32>:
  match m:
    case None{}:
      tail
    case Some{cells}:
      Export.bxe_u32_le(k, Export.bxe_cell_words(cells, tail))

# Walk keys DESCENDING so prepending yields a chunk-ordinal record set (`kx`
# fastest, then `ky`, then `kz`; not packed-key-monotonic).
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
  +cnt = U32.div(U32.from_nat(bridge2_len(recs)), 8)
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

# --------------------------------------------------------- delta decoding
# Decode a served DELTA payload back into `Sim.Delta` records. The payload is
# `tick u32, count u32, (idx u32, word u32)...`; the two header words are dropped
# and each pair becomes a global-coordinate `Sim.Delta`, so the witness replays
# exactly the bytes the link emits. `word` is already `Cell.deactivate`d by
# `bridge2_delta_records`.
def bridge3_delta_ds_go(ws: List<&2, U32>) -> List<&1, Sim.Delta>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{+idx, r1}:
      match r1:
        case Nil{}:
          Nil{}
        case Con{word, r2}:
          Sim.Delta{Grid.ix(idx), Grid.iy(idx), Grid.iz(idx), word} <> bridge3_delta_ds_go(r2)

def bridge3_delta_ds(payload: List<&2, U32>) -> List<&1, Sim.Delta>:
  bridge3_delta_ds_go(List.drop(&2, U32, bridge2_dec_words(payload), 2n))

# Decode a whole DELTA frame (8-byte header + payload).
def bridge3_delta_frame_ds(frame: List<&2, U32>) -> List<&1, Sim.Delta>:
  bridge3_delta_ds(List.drop(&2, U32, frame, 8n))

# The raw `(idx, word)` record words of a served DELTA payload/frame (the tick
# and count header words dropped). A witness replays these directly, so it never
# needs a `List<Sim.Delta>` across the module seam.
def bridge3_delta_words(payload: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, bridge2_dec_words(payload), 2n)

def bridge3_delta_frame_words(frame: List<&2, U32>) -> List<&2, U32>:
  bridge3_delta_words(List.drop(&2, U32, frame, 8n))

# Walk a length-framed stream and return the frame kinds in order. `payload_len`
# is a byte count; every payload here is whole u32 words, so it is `len/4` words
# to skip past the payload.
def bridge3_frame_kinds_go(fuel: Nat, +ws: List<&2, U32>) -> List<&2, U32>:
  match fuel:
    case 0n:
      Nil{}
    case 1n+p:
      match ws:
        case Nil{}:
          Nil{}
        case Con{+len, r1}:
          match r1:
            case Nil{}:
              Nil{}
            case Con{kind, r2}:
              kind <> bridge3_frame_kinds_go(p, List.drop(&2, U32, r2, U32.to_nat(U32.div(len, 4))))

def bridge3_frame_kinds(stream: List<&2, U32>) -> List<&2, U32>:
  bridge3_frame_kinds_go(1048576n, bridge2_dec_words(stream))

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

# ============================================================================
# serve -- flow control (track `bridge3`, closes `G-bridge-1`).
#
# `bridge2` framed the stream and fixed the kinds, but the writer was a bare
# synchronous emit and control was read at most once. This layer realises
# SERVE.md §5-§6 as pure accounting plus a forked reader:
#
#   * a BOUNDED outbound queue (`cap` frames; rendezvous 1, hard cap 8);
#   * a CREDIT window: CREDIT advances it, an emitted frame debits it, and no
#     frame is ever written with a zero window (no overrun, no wrap -- `U32.sub`
#     wraps, so the guard is the whole safety argument);
#   * DROP-AND-KEYFRAME COALESCING: when the queue is full a delta is dropped,
#     counted, and a fresh SNAPSHOT is armed, so the renderer sees either a
#     contiguous delta run or a clean keyframe jump (never a gap);
#   * an idle PING: after `threshold` ticks with nothing emitted, the writer
#     offers a PING heartbeat.
#
# The accounting is pure (`Bridge3Flow`) and witnessed by T76-T80. The IO shell
# drives it, and `bridge3_reader` drains stdin continuously into a `Chan` (so
# control is no longer read at most once). The engine/writer split is still
# co-resident in one IO thread: Bend's `Chan.recv` parks rather than polling, so
# a non-blocking `try_recv` is not expressible; that residual is a gap.
# ============================================================================

type Bridge3Flow is Data:
  B3Flow{
    window: U32,     # send credit remaining (CREDIT advances, emit debits)
    queued: U32,     # frames resident in the bounded outbound queue
    cap: U32,        # queue capacity (>= 1)
    coalesced: U32,  # deltas dropped since the last armed keyframe
    keyframe: Bool,  # a fresh SNAPSHOT is armed
    tick: U32,       # newest tick the engine has produced
    idle: U32,       # ticks since the last emitted frame (PING timer)
    stop: Bool       # control said STOP/EOF: flush the checkpoint, then exit
  }

def bridge3_flow_new(+cap: U32) -> Bridge3Flow:
  B3Flow{0, 0, cap, 0, False{}, 0, 0, False{}}

def bridge3_window(f: Bridge3Flow) -> U32:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}: window

def bridge3_queued(f: Bridge3Flow) -> U32:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}: queued

def bridge3_coalesced(f: Bridge3Flow) -> U32:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}: coalesced

def bridge3_is_keyframe(f: Bridge3Flow) -> Bool:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}: keyframe

def bridge3_idle(f: Bridge3Flow) -> U32:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}: idle

def bridge3_is_stopped(f: Bridge3Flow) -> Bool:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}: stop

def bridge3_can_emit(f: Bridge3Flow) -> Bool:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}:
      Bool.and(U32.is_gt(window, 0), U32.is_gt(queued, 0))

def bridge3_has_room(f: Bridge3Flow) -> Bool:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}:
      U32.is_lt(queued, cap)

def bridge3_has_credit(f: Bridge3Flow) -> Bool:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}:
      U32.is_gt(window, 0)

# A CREDIT frame advances the send window; a REQUEST arms a keyframe.
def bridge3_credit(f: Bridge3Flow, +n: U32) -> Bridge3Flow:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}:
      B3Flow{U32.add(window, n), queued, cap, coalesced, keyframe, tick, idle, stop}

def bridge3_arm_keyframe(f: Bridge3Flow, +tick: U32) -> Bridge3Flow:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick0, idle, stop}:
      B3Flow{window, queued, cap, coalesced, True{}, tick, idle, stop}

# STOP/EOF: sticky, and grants a flush window so the final checkpoint
# (SNAPSHOT + PING) can be written even though the renderer has stopped granting.
def bridge3_stop(f: Bridge3Flow) -> Bridge3Flow:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}:
      B3Flow{U32.add(window, 8), queued, cap, coalesced, keyframe, tick, idle, True{}}

# --- emit: debit one credit and one slot, reset the idle timer ---------------
def bridge3_emit_if(can: Bool, +window: U32, +queued: U32, +cap: U32, +coalesced: U32, +keyframe: Bool, +tick: U32, +idle: U32, +stop: Bool) -> Bridge3Flow:
  match can:
    case True{}:
      B3Flow{U32.sub(window, 1), U32.sub(queued, 1), cap, coalesced, keyframe, tick, 0, stop}
    case False{}:
      B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}

def bridge3_emit(f: Bridge3Flow) -> Bridge3Flow:
  match f:
    case B3Flow{+window, +queued, cap, coalesced, keyframe, tick, idle, +stop}:
      bridge3_emit_if(Bool.and(U32.is_gt(window, 0), U32.is_gt(queued, 0)),
        window, queued, cap, coalesced, keyframe, tick, idle, stop)

# --- bounded queue: push, with coalescing on overflow ------------------------
def bridge3_push_delta_if(room: Bool, +window: U32, +queued: U32, +cap: U32, +coalesced: U32, +keyframe: Bool, +tick: U32, +idle: U32, +stop: Bool) -> Bridge3Flow:
  match room:
    case True{}:
      B3Flow{window, U32.add(queued, 1), cap, coalesced, keyframe, tick, idle, stop}
    case False{}:
      B3Flow{window, queued, cap, U32.add(coalesced, 1), True{}, tick, idle, stop}

def bridge3_push_delta(f: Bridge3Flow, +tick: U32) -> Bridge3Flow:
  match f:
    case B3Flow{window, +queued, +cap, coalesced, keyframe, tick0, idle, stop}:
      bridge3_push_delta_if(U32.is_lt(queued, cap), window, queued, cap, coalesced, keyframe, tick, idle, stop)

def bridge3_push_frame_if(room: Bool, +window: U32, +queued: U32, +cap: U32, +coalesced: U32, +keyframe: Bool, +tick: U32, +idle: U32, +stop: Bool) -> Bridge3Flow:
  match room:
    case True{}:
      B3Flow{window, U32.add(queued, 1), cap, coalesced, keyframe, tick, idle, stop}
    case False{}:
      B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}

def bridge3_push_frame(f: Bridge3Flow, +tick: U32) -> Bridge3Flow:
  match f:
    case B3Flow{window, +queued, +cap, coalesced, keyframe, tick0, idle, stop}:
      bridge3_push_frame_if(U32.is_lt(queued, cap), window, queued, cap, coalesced, keyframe, tick, idle, stop)

# Consume an armed keyframe: replace the queued delta run with one SNAPSHOT.
def bridge3_take_kf_if(ok: Bool, +window: U32, +queued: U32, +cap: U32, +coalesced: U32, +keyframe: Bool, +tick: U32, +idle: U32, +stop: Bool) -> Bridge3Flow:
  match ok:
    case True{}:
      B3Flow{window, 1, cap, 0, False{}, tick, idle, stop}
    case False{}:
      B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}

def bridge3_take_keyframe(f: Bridge3Flow) -> Bridge3Flow:
  match f:
    case B3Flow{+window, +queued, +cap, +coalesced, +keyframe, tick, idle, +stop}:
      bridge3_take_kf_if(Bool.and(keyframe, U32.is_gt(window, 0)),
        window, queued, cap, coalesced, keyframe, tick, idle, stop)

# --- idle PING ---------------------------------------------------------------
def bridge3_idle_tick(f: Bridge3Flow) -> Bridge3Flow:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}:
      B3Flow{window, queued, cap, coalesced, keyframe, tick, U32.add(idle, 1), stop}

# Writer policy: 0 none, 1 SNAPSHOT, 2 DELTA, 3 PING. A keyframe beats queued
# deltas; a PING is offered only when the queue is empty and the stream is idle.
def bridge3_next_k(kf: Bool, q: Bool, w: Bool, idle_ok: Bool) -> U32:
  Bool.pick(U32, w,
    Bool.pick(U32, kf, 1, Bool.pick(U32, q, 2, Bool.pick(U32, idle_ok, 3, 0))),
    0)

def bridge3_next(f: Bridge3Flow, +threshold: U32) -> U32:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop}:
      bridge3_next_k(keyframe, U32.is_gt(queued, 0), U32.is_gt(window, 0), U32.is_ge(idle, threshold))

# --- iteration helpers (tests and the writer) --------------------------------
def bridge3_emit_go(fuel: Nat, f: Bridge3Flow) -> Bridge3Flow:
  match fuel:
    case 0n: f
    case 1n+p: bridge3_emit_go(p, bridge3_emit(f))

def bridge3_push_go(fuel: Nat, +tick: U32, f: Bridge3Flow) -> Bridge3Flow:
  match fuel:
    case 0n: f
    case 1n+p: bridge3_push_go(p, U32.add(tick, 1), bridge3_push_delta(f, tick))

def bridge3_idle_go(fuel: Nat, f: Bridge3Flow) -> Bridge3Flow:
  match fuel:
    case 0n: f
    case 1n+p: bridge3_idle_go(p, bridge3_idle_tick(f))

# ----------------------------------------------------------------- flow IO
# Fold one inbound control into the flow: CREDIT advances the window, REQUEST
# arms a keyframe, STOP is handled by the reader (channel close).
def bridge3_apply_ctrl(f: Bridge3Flow, c: Bridge2Ctrl) -> Bridge3Flow:
  match c:
    case BCredit{frames}:
      bridge3_credit(f, frames)
    case BRequest{tick, flags}:
      bridge3_arm_keyframe(f, tick)
    case BStop{}:
      bridge3_stop(f)
    case _:
      f

def bridge3_recv_fold(f: Bridge3Flow, m: Maybe<&1, Bridge2Ctrl>) -> Bridge3Flow:
  match m:
    case None{}:
      # renderer closed stdin (STOP/EOF): arm a flush window and stop
      bridge3_stop(f)
    case Some{c}:
      bridge3_apply_ctrl(f, c)

# Block the WRITER (never the engine) until the window holds credit, folding
# whatever control arrives meanwhile.
def bridge3_recv_step(chan: Chan(Bridge2Ctrl), f: Bridge3Flow) -> IO(Bridge3Flow):
  do IO<Bridge3Flow>:
    m : Maybe<&1, Bridge2Ctrl> <- Chan.recv(Bridge2Ctrl, chan)
    IO.pure(Bridge3Flow, bridge3_recv_fold(f, m))

def bridge3_grant_go(fuel: Nat, has: Bool, f: Bridge3Flow, +chan: Chan(Bridge2Ctrl)) -> IO(Bridge3Flow):
  match fuel:
    case 0n:
      IO.pure(Bridge3Flow, f)
    case 1n+p:
      match has:
        case True{}:
          IO.pure(Bridge3Flow, f)
        case False{}:
          do IO<Bridge3Flow>:
            +f2 : Bridge3Flow <- bridge3_recv_step(chan, f)
            bridge3_grant_go(p, bridge3_has_credit(f2), f2, chan)

def bridge3_grant_until(+f: Bridge3Flow, chan: Chan(Bridge2Ctrl)) -> IO(Bridge3Flow):
  bridge3_grant_go(1024n, bridge3_has_credit(f), f, chan)

def bridge3_write_if(ok: Bool, frame: List<&2, U32>, f: Bridge3Flow) -> IO(Bridge3Flow):
  match ok:
    case True{}:
      do IO<Bridge3Flow>:
        bridge2_stdout(frame)
        IO.pure(Bridge3Flow, bridge3_emit(f))
    case False{}:
      IO.pure(Bridge3Flow, f)

# Queue one frame, wait for credit, write it, and debit the flow. A frame is
# only written when credit is held, so the window is never overrun even if the
# renderer grants nothing.
def bridge3_write_frame(f: Bridge3Flow, chan: Chan(Bridge2Ctrl), +tick: U32, frame: List<&2, U32>) -> IO(Bridge3Flow):
  do IO<Bridge3Flow>:
    f2 : Bridge3Flow = bridge3_push_frame(f, tick)
    +f3 : Bridge3Flow <- bridge3_grant_until(f2, chan)
    bridge3_write_if(bridge3_has_credit(f3), frame, f3)

def bridge3_bytes_or_nil(res: Result<&1, &1, U32 & String, List<&2, U32>>) -> List<&2, U32>:
  match res:
    case Done{value}:
      value
    case Fail{(code, message)}:
      Nil{}

# Continuous stdin reader: decode each control frame and hand it to the writer
# over a room-1 `Chan`. Closing stdin (EOF) closes the channel, which the writer
# reads as STOP. This replaces the one-shot `bridge2_read_control`.
#
# Bend has no forward references, no mutual recursion, and a `match` may only
# scrutinize a top-level parameter -- so the read/match/send loop is one
# self-recursive `def` with a `Nat` fuel (the guide's server-loop shape) and a
# `phase` selector: 0 reads, 1 unpacks the read result, 2 dispatches the bytes.
# The extra `q`/`bytes` parameters are the same function's "which to run"
# selector, so no helper needs a forward reference.
def bridge3_reader_go(
  fuel: Nat,
  +phase: U32,
  +chan: Chan(Bridge2Ctrl),
  q: File & Result<&1, &1, U32 & String, List<&2, U32>>,
  +bytes: List<&2, U32>
) -> IO(Unit):
  match fuel:
    case 0n:
      Chan.close(Bridge2Ctrl, chan)
    case 1n+p:
      match phase:
        case 0:
          match q:
            case (f0, r0):
              do IO<Unit>:
                q2 : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f0, 1048576)
                bridge3_reader_go(p, 1, chan, q2, Nil{})
        case 1:
          match q:
            case (f2, res):
              do IO<Unit>:
                bytes2 : List<&2, U32> = bridge3_bytes_or_nil(res)
                bridge3_reader_go(p, 2, chan, (f2, Fail{(0, "")}), bytes2)
        case _:
          match bytes:
            case Nil{}:
              do IO<Unit>:
                IO.print_err("serve: control EOF\n")
                Chan.close(Bridge2Ctrl, chan)
            case Con{h, t}:
              do IO<Unit>:
                sent : Bool <- Chan.send(Bridge2Ctrl, chan, bridge2_decode_control(bytes))
                bridge3_reader_go(p, 0, chan, q, Nil{})

def bridge3_reader(chan: Chan(Bridge2Ctrl)) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("/dev/stdin", "r"))
    bridge3_reader_go(1048576n, 0, chan, (f, Fail{(0, "")}), Nil{})

# The flow-based live link: HELLO, a dense SNAPSHOT of the genesis world at tick
# 0, then a continuous DELTA stream (one frame per canonical-window tick, global
# coordinates from `Sim.tick_trace`), gated by the credit window the forked
# reader fills from CREDIT. A STOP frame (or EOF) sets the flow's sticky stop
# flag; the loop then flushes a sparse checkpoint SNAPSHOT, a PING and a BYE.
#
# This is deliberately the FIXED canonical window (`Sim.tick_trace`), not the W5
# motion driver: window motion is a separate, later decision.
def bridge3_link_world() -> Array<U32>:
  Fixtures.spawn(Sim.build())

def bridge3_live_fuel() -> Nat:
  1073741824n

# Sparse checkpoint at the loop's current tick, then PING and BYE.
def bridge3_checkpoint_store(r: Array<U32> & Store.Store, +chan: Chan(Bridge2Ctrl), +tick: U32, f: Bridge3Flow) -> IO(Unit):
  match r:
    case (world, store):
      do IO<Unit>:
        ev : Store.Store = Store.evict(store)
        f1 : Bridge3Flow <- bridge3_write_frame(f, chan, tick, bridge2_snapshot_sparse(ev, tick))
        f2 : Bridge3Flow <- bridge3_write_frame(f1, chan, tick, bridge2_ping(tick))
        bridge2_stdout(bridge2_bye())
        IO.print_err("serve: checkpoint tick=" ++ U32.show(tick) ++ ", bye\n")

def bridge3_checkpoint_flow(world: Array<U32>, chan: Chan(Bridge2Ctrl), +tick: U32, f: Bridge3Flow) -> IO(Unit):
  bridge3_checkpoint_store(bridge2_world_store(world), chan, tick, f)

# The continuous loop body. `r` threads the previous tick's `(world, deltas)` as
# a parameter (Bend cannot scrutinize a computed value). The loop stops when the
# flow is stopped or the fuel is exhausted, then checkpoints.
#
# Flush the terminal checkpoint at the loop's current tick.
def bridge3_live_finish(r: Array<U32> & List<Sim.Delta>, chan: Chan(Bridge2Ctrl), +tick: U32, f: Bridge3Flow) -> IO(Unit):
  match r:
    case (world, ds):
      bridge3_checkpoint_flow(world, chan, tick, f)

# The continuous loop body: one self-recursive `def` with a phase selector (Bend
# has no forward references / mutual recursion). `fuel` is `2 * ticks` because
# every self-call must decrement it: phase 0 checks the stop flag, phase 1 writes
# one tick's DELTA and ticks again. `r` threads the previous tick's
# `(world, deltas)` as a parameter (Bend cannot scrutinize a computed value), and
# `tick` is the tick `ds` belongs to. It checkpoints on STOP/EOF or fuel
# exhaustion; the tick before the stop check means a post-STOP SNAPSHOT may
# supersede one unbroadcast tick -- legal, since a SNAPSHOT supersedes all deltas.
def bridge3_live_go(
  fuel: Nat, +phase: U32, +tick: U32, +chan: Chan(Bridge2Ctrl), f: Bridge3Flow,
  r: Array<U32> & List<Sim.Delta>
) -> IO(Unit):
  match fuel:
    case 0n:
      bridge3_live_finish(r, chan, tick, f)
    case 1n+p:
      match phase:
        case 0:
          match f:
            case B3Flow{window, queued, cap, coalesced, keyframe, tick0, idle, stop}:
              match stop:
                case True{}:
                  bridge3_live_finish(r, chan, tick, f)
                case False{}:
                  bridge3_live_go(p, 1, tick, chan, f, r)
        case _:
          match r:
            case (world, ds):
              do IO<Unit>:
                f2 : Bridge3Flow <- bridge3_write_frame(f, chan, tick, bridge2_delta_frame(tick, ds))
                bridge3_live_go(p, 0, U32.add(tick, 1), chan, f2, Sim.tick_trace(world))

# Control path: a forked reader parses CREDIT/REQUEST/STOP from stdin; the
# writer is fully credit-gated, so the loop runs until STOP/EOF.
def bridge3_serve_control() -> IO(Unit):
  do IO<Unit>:
    +chan : Chan(Bridge2Ctrl) <- Chan.new(Bridge2Ctrl, 1)
    IO.spawn(Unit, bridge3_reader(chan))
    IO.print_err("serve: hello\n")
    bridge2_stdout(bridge2_hello(0))
    f0 : Bridge3Flow = bridge3_flow_new(8)
    f1 : Bridge3Flow <- bridge3_write_frame(f0, chan, 0, bridge2_snapshot_dense(bridge3_link_world(), 0))
    IO.print_err("serve: dense snapshot tick=0\n")
    bridge3_live_go(bridge3_live_fuel(), 0, 1, chan, f1, Sim.tick_trace(bridge3_link_world()))

# No-control path: the same loop, but the window is pre-seeded so no reader is
# needed; it runs a bounded number of ticks and then checkpoints.
def bridge3_serve_bounded(+ticks: Nat) -> IO(Unit):
  do IO<Unit>:
    +chan : Chan(Bridge2Ctrl) <- Chan.new(Bridge2Ctrl, 1)
    IO.print_err("serve: hello\n")
    bridge2_stdout(bridge2_hello(0))
    f0 : Bridge3Flow = bridge3_credit(bridge3_flow_new(8), 64)
    f1 : Bridge3Flow <- bridge3_write_frame(f0, chan, 0, bridge2_snapshot_dense(bridge3_link_world(), 0))
    IO.print_err("serve: dense snapshot tick=0\n")
    bridge3_live_go(Nat.double(ticks), 0, 1, chan, f1, Sim.tick_trace(bridge3_link_world()))

def bridge3_serve_if(control: Bool) -> IO(Unit):
  match control:
    case True{}:
      bridge3_serve_control()
    case False{}:
      bridge3_serve_bounded(8n)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<&1, String> <- IO.args()
    bridge3_serve_if(bridge2_has_control(args))
