import Base
import ../src/grid.bend as Grid
import ../src/cell.bend as Cell
import ../src/chunk.bend as Chunk
import ../src/window.bend as Window
import ../src/store.bend as Store
import ../src/sim.bend as Sim
import ../src/worldgen.bend as Worldgen
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
# kinds out : 0 HELLO, 1 SNAPSHOT, 2 DELTA, 3 PING, 4 BYE, 9 ORIGIN
# kinds in  : 5 CREDIT, 6 REQUEST, 7 STOP, 8 FOCUS
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

# ============================================================================
# focus -- the moving-window live path (track `focus`, Bendview D1).
#
# A renderer FOCUS request (inbound kind 8) names the window's target base chunk
# origin `(cx, cy, cz)`. The engine shifts the resident window to that origin
# (`Window.shift`), runs one moved-window tick (`Sim.w5_trace_step`), and streams
# a fresh SNAPSHOT of the moved window. The renderer re-anchors from the ORIGIN
# reply (outbound kind 9), so the engine emits the window's base chunk origin
# `(bx, by, bz)` immediately after HELLO and again before every moved SNAPSHOT.
#
# Decision: FOCUS carries a CHUNK origin, not a global cell. It is total (no
# centering/clamp ambiguity), exactly the coordinate `Window.shift` consumes, and
# symmetric with the ORIGIN reply. A global cell would force the engine to pick a
# centering policy; the renderer already tracks the window origin and can compute
# the chunk it wants from the camera. The moved DELTA idx is window-local
# (`Window.win_index`, which equals `Grid.index` on the canonical window, so the
# fixed path's bytes are unchanged); a SNAPSHOT supersedes the deltas before a
# move (SERVE.md §4).
# ============================================================================

# FOCUS payload: `cx u32, cy u32, cz u32`. ORIGIN payload: `bx, by, bz`.
def focus_payload(+cx: U32, +cy: U32, +cz: U32) -> List<&2, U32>:
  Export.bxe_u32_le(cx, Export.bxe_u32_le(cy, Export.bxe_u32_le(cz, Nil{})))

# ORIGIN (kind 9): the window's base chunk origin, for the renderer to re-anchor.
def focus_origin_frame(+w: Window.Window) -> List<&2, U32>:
  bridge2_frame(9, focus_payload(Window.base_x(w), Window.base_y(w), Window.base_z(w)))

# The chunk deltas that shift `w`'s base onto the requested origin. `U32.sub`
# wraps, so a backwards move is the two's complement `Window.shift` expects.
def focus_dcx(w: Window.Window, +cx: U32) -> U32:
  U32.sub(cx, Window.base_x(w))

def focus_dcy(w: Window.Window, +cy: U32) -> U32:
  U32.sub(cy, Window.base_y(w))

def focus_dcz(w: Window.Window, +cz: U32) -> U32:
  U32.sub(cz, Window.base_z(w))

# DELTA on the resident window: `idx` is the WINDOW-LOCAL flat index (identical to
# `Grid.index` on `Window.canonical()`, so the fixed-window bytes are unchanged).
# Tail-recursive (constant-stack): the shell-free live first tick carries ~80k
# deltas, and the old `bxe_u32_le(idx, ... focus_delta_records(w, t))` built one
# machine-stack frame per delta. The delta list is reversed first (a tail walk),
# then each delta's bytes are prepended -- little-endian words stay intact, and
# the emitted record order is byte-identical to the old right fold.
def focus_delta_recs_go(ds: List<Sim.Delta>, +w: Window.Window, acc: List<&2, U32>) -> List<&2, U32>:
  match ds:
    case Nil{}:
      acc
    case Con{h, t}:
      match h:
        case Sim.Delta{x, y, z, val}:
          +idx = Window.win_index(w, x, y, z)
          focus_delta_recs_go(t, w, Export.bxe_u32_le(idx, Export.bxe_u32_le(Cell.deactivate(val), acc)))

def focus_delta_records(+w: Window.Window, ds: List<Sim.Delta>) -> List<&2, U32>:
  focus_delta_recs_go(List.reverse(&1, Sim.Delta, ds), w, Nil{})

def focus_delta_frame(+w: Window.Window, +tick: U32, ds: List<Sim.Delta>) -> List<&2, U32>:
  +recs = focus_delta_records(w, ds)
  +cnt = U32.div(U32.from_nat(bridge2_len(recs)), 8)
  bridge2_frame(2, Export.bxe_u32_le(tick, Export.bxe_u32_le(cnt, recs)))

# Sparse SNAPSHOT of a MOVED window: the record set is the window's own resident
# keys (`Window.resident_keys`), not the canonical 64. Reuses the exporter's
# sparse header and record shape, so the renderer's snapshot parser is unchanged;
# eviction omits sleeping gen-equal chunks (they regenerate from `gen`).
def focus_records_go(keys: List<&2, U32>, +s: Store.Store, acc: List<&2, U32>) -> List<&2, U32>:
  match keys:
    case Nil{}:
      acc
    case Con{+k, t}:
      focus_records_go(t, s, bridge2_rec_if(Store.get(s, k), k, acc))

def focus_count_go(keys: List<&2, U32>, +s: Store.Store, acc: U32) -> U32:
  match keys:
    case Nil{}:
      acc
    case Con{+k, t}:
      +add = Bool.pick(U32, bridge2_is_some(Store.get(s, k)), 1, 0)
      focus_count_go(t, s, U32.add(acc, add))

def focus_snapshot_sparse(+sel: Bool, +w: Window.Window, +s: Store.Store, +ticks: U32) -> List<&2, U32>:
  +ev = Store.evict_sel(sel, s)
  +keys = Window.resident_keys(w)
  +count = focus_count_go(keys, ev, 0)
  h = bridge2_snap_header(count, ticks, Nil{})
  recs = focus_records_go(keys, ev, Nil{})
  bridge2_frame(1, List.append(&2, U32, h, recs))

# Advance one tick on the resident window and checkpoint it back into the store
# (the windowed twin of `Sim.tick_trace`; the store carries the ticked state
# across a later move). `r` is the computed `(world, deltas)` pair passed as a
# parameter because a computed value cannot be scrutinized.
def focus_tick_r(+w: Window.Window, +s: Store.Store, r: Array<U32> & List<Sim.Delta>) -> Window.Window & Store.Store & List<Sim.Delta>:
  match r:
    case (world2, ds2):
      (w, Sim.w5_ck_store_on(w, world2, s), ds2)

def focus_next_state(+sel: Bool, +w: Window.Window, +s: Store.Store) -> Window.Window & Store.Store & List<Sim.Delta>:
  focus_tick_r(w, s, Sim.tick_trace_w(w, Store.assemble_w_sel(sel, w, s)))

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
  BFocus{cx: U32, cy: U32, cz: U32}
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

def bridge2_word2(xs: List<&2, U32>) -> U32:
  match xs:
    case Nil{}:
      0
    case Con{h, t}:
      bridge2_word1(t)

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
    case 8:
      BFocus{bridge2_word0(payload), bridge2_word1(payload), bridge2_word2(payload)}
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
    case BFocus{cx, cy, cz}:
      "focus " ++ U32.show(cx) ++ "," ++ U32.show(cy) ++ "," ++ U32.show(cz)
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

# A renderer focus request is engine state, not credit accounting, but it must
# survive the credit wait (where control is folded into the flow). A small
# `Data` holder is used instead of `Maybe` because a `Data` field must itself be
# `Data` (`Maybe` is `Type`), so the one-slot pending request rides on the flow.
type Focus is Data:
  FocusNone{}
  FocusAt{cx: U32, cy: U32, cz: U32}

type Bridge3Flow is Data:
  B3Flow{
    window: U32,     # send credit remaining (CREDIT advances, emit debits)
    queued: U32,     # frames resident in the bounded outbound queue
    cap: U32,        # queue capacity (>= 1)
    coalesced: U32,  # deltas dropped since the last armed keyframe
    keyframe: Bool,  # a fresh SNAPSHOT is armed
    tick: U32,       # newest tick the engine has produced
    idle: U32,       # ticks since the last emitted frame (PING timer)
    stop: Bool,      # control said STOP/EOF: flush the checkpoint, then exit
    focus: Focus     # pending FOCUS request (one slot; newest wins)
  }

def bridge3_flow_new(+cap: U32) -> Bridge3Flow:
  B3Flow{0, 0, cap, 0, False{}, 0, 0, False{}, FocusNone{}}

def bridge3_window(f: Bridge3Flow) -> U32:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}: window

def bridge3_queued(f: Bridge3Flow) -> U32:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}: queued

def bridge3_coalesced(f: Bridge3Flow) -> U32:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}: coalesced

def bridge3_is_keyframe(f: Bridge3Flow) -> Bool:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}: keyframe

def bridge3_idle(f: Bridge3Flow) -> U32:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}: idle

def bridge3_is_stopped(f: Bridge3Flow) -> Bool:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}: stop

def bridge3_can_emit(f: Bridge3Flow) -> Bool:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}:
      Bool.and(U32.is_gt(window, 0), U32.is_gt(queued, 0))

def bridge3_has_room(f: Bridge3Flow) -> Bool:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}:
      U32.is_lt(queued, cap)

def bridge3_has_credit(f: Bridge3Flow) -> Bool:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}:
      U32.is_gt(window, 0)

# The pending focus (the one slot the loop consumes at a frame boundary).
def focus_of_flow(f: Bridge3Flow) -> Focus:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, focus}: focus

# Arm a focus request; the newest request replaces any pending one.
def focus_set(f: Bridge3Flow, +cx: U32, +cy: U32, +cz: U32) -> Bridge3Flow:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}:
      B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, FocusAt{cx, cy, cz}}

# Consume the pending focus (called after the move has been applied).
def focus_clear(f: Bridge3Flow) -> Bridge3Flow:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}:
      B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, FocusNone{}}

# A CREDIT frame advances the send window; a REQUEST arms a keyframe.
def bridge3_credit(f: Bridge3Flow, +n: U32) -> Bridge3Flow:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, focus}:
      B3Flow{U32.add(window, n), queued, cap, coalesced, keyframe, tick, idle, stop, focus}

def bridge3_arm_keyframe(f: Bridge3Flow, +tick: U32) -> Bridge3Flow:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick0, idle, stop, focus}:
      B3Flow{window, queued, cap, coalesced, True{}, tick, idle, stop, focus}

# STOP/EOF: sticky, and grants a flush window so the final checkpoint
# (SNAPSHOT + PING) can be written even though the renderer has stopped granting.
def bridge3_stop(f: Bridge3Flow) -> Bridge3Flow:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, focus}:
      B3Flow{U32.add(window, 8), queued, cap, coalesced, keyframe, tick, idle, True{}, focus}

# --- emit: debit one credit and one slot, reset the idle timer ---------------
def bridge3_emit_if(can: Bool, +window: U32, +queued: U32, +cap: U32, +coalesced: U32, +keyframe: Bool, +tick: U32, +idle: U32, +stop: Bool, +focus: Focus) -> Bridge3Flow:
  match can:
    case True{}:
      B3Flow{U32.sub(window, 1), U32.sub(queued, 1), cap, coalesced, keyframe, tick, 0, stop, focus}
    case False{}:
      B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, focus}

def bridge3_emit(f: Bridge3Flow) -> Bridge3Flow:
  match f:
    case B3Flow{+window, +queued, cap, coalesced, keyframe, tick, idle, +stop, +focus}:
      bridge3_emit_if(Bool.and(U32.is_gt(window, 0), U32.is_gt(queued, 0)),
        window, queued, cap, coalesced, keyframe, tick, idle, stop, focus)

# --- bounded queue: push, with coalescing on overflow ------------------------
def bridge3_push_delta_if(room: Bool, +window: U32, +queued: U32, +cap: U32, +coalesced: U32, +keyframe: Bool, +tick: U32, +idle: U32, +stop: Bool, +focus: Focus) -> Bridge3Flow:
  match room:
    case True{}:
      B3Flow{window, U32.add(queued, 1), cap, coalesced, keyframe, tick, idle, stop, focus}
    case False{}:
      B3Flow{window, queued, cap, U32.add(coalesced, 1), True{}, tick, idle, stop, focus}

def bridge3_push_delta(f: Bridge3Flow, +tick: U32) -> Bridge3Flow:
  match f:
    case B3Flow{window, +queued, +cap, coalesced, keyframe, tick0, idle, stop, +focus}:
      bridge3_push_delta_if(U32.is_lt(queued, cap), window, queued, cap, coalesced, keyframe, tick, idle, stop, focus)

def bridge3_push_frame_if(room: Bool, +window: U32, +queued: U32, +cap: U32, +coalesced: U32, +keyframe: Bool, +tick: U32, +idle: U32, +stop: Bool, +focus: Focus) -> Bridge3Flow:
  match room:
    case True{}:
      B3Flow{window, U32.add(queued, 1), cap, coalesced, keyframe, tick, idle, stop, focus}
    case False{}:
      B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, focus}

def bridge3_push_frame(f: Bridge3Flow, +tick: U32) -> Bridge3Flow:
  match f:
    case B3Flow{window, +queued, +cap, coalesced, keyframe, tick0, idle, stop, +focus}:
      bridge3_push_frame_if(U32.is_lt(queued, cap), window, queued, cap, coalesced, keyframe, tick, idle, stop, focus)

# Consume an armed keyframe: replace the queued delta run with one SNAPSHOT.
def bridge3_take_kf_if(ok: Bool, +window: U32, +queued: U32, +cap: U32, +coalesced: U32, +keyframe: Bool, +tick: U32, +idle: U32, +stop: Bool, +focus: Focus) -> Bridge3Flow:
  match ok:
    case True{}:
      B3Flow{window, 1, cap, 0, False{}, tick, idle, stop, focus}
    case False{}:
      B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, focus}

def bridge3_take_keyframe(f: Bridge3Flow) -> Bridge3Flow:
  match f:
    case B3Flow{+window, +queued, +cap, +coalesced, +keyframe, tick, idle, +stop, +focus}:
      bridge3_take_kf_if(Bool.and(keyframe, U32.is_gt(window, 0)),
        window, queued, cap, coalesced, keyframe, tick, idle, stop, focus)

# --- idle PING ---------------------------------------------------------------
def bridge3_idle_tick(f: Bridge3Flow) -> Bridge3Flow:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, focus}:
      B3Flow{window, queued, cap, coalesced, keyframe, tick, U32.add(idle, 1), stop, focus}

# Writer policy: 0 none, 1 SNAPSHOT, 2 DELTA, 3 PING. A keyframe beats queued
# deltas; a PING is offered only when the queue is empty and the stream is idle.
def bridge3_next_k(kf: Bool, q: Bool, w: Bool, idle_ok: Bool) -> U32:
  Bool.pick(U32, w,
    Bool.pick(U32, kf, 1, Bool.pick(U32, q, 2, Bool.pick(U32, idle_ok, 3, 0))),
    0)

def bridge3_next(f: Bridge3Flow, +threshold: U32) -> U32:
  match f:
    case B3Flow{window, queued, cap, coalesced, keyframe, tick, idle, stop, _}:
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
    case BFocus{cx, cy, cz}:
      focus_set(f, cx, cy, cz)
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

# Continuous stdin reader: assemble `[len][kind][payload]` control frames from an
# accumulating buffer and hand each decoded frame to the writer over a room-1
# `Chan`. Closing stdin (EOF) closes the channel, which the writer reads as STOP.
#
# `File.read_bytes` is a read-*some*: it returns as soon as any bytes are
# available (up to the max), so a renderer that holds stdin open is not a
# problem. The old reader decoded the whole read as one frame and dropped the
# rest, so two frames in one read (or a partial frame) mis-parsed -- `G-bridge-1`'s
# reader half. This version carries the unconsumed bytes across reads and pulls
# complete frames out one at a time.
#
# Bend has no forward references, no mutual recursion, and a `match` may only
# scrutinize a top-level parameter -- so the read/match/send loop is one
# self-recursive `def` with a `Nat` fuel (the guide's server-loop shape) and a
# `phase` selector: 0 reads, 1 folds the read result into `buf`/`eof`, 2 extracts
# and dispatches frames. The extra `q`/`buf`/`eof` parameters are the same
# function's state, so no helper needs a forward reference.

# Bytes in the frame at the head of `buf`: an 8-byte header (`payload_len` u32,
# `kind` u32) + `payload_len` payload bytes, or `0` when fewer than 8 bytes are
# present. `buf` holds *bytes* (as `File.read_bytes` returns them), so the length
# is the little-endian u32 of the first four bytes.
def bridge3_frame_need(+buf: List<&2, U32>) -> Nat:
  match buf:
    case Nil{}:
      0n
    case Con{b0, r1}:
      match r1:
        case Nil{}:
          0n
        case Con{b1, r2}:
          match r2:
            case Nil{}:
              0n
            case Con{b2, r3}:
              match r3:
                case Nil{}:
                  0n
                case Con{b3, r4}:
                  Nat.add(8n, U32.to_nat(bridge2_u32_of_le(b0, b1, b2, b3)))

# Is the head frame fully present?
def bridge3_frame_ready(+buf: List<&2, U32>) -> Bool:
  +need = bridge3_frame_need(buf)
  Bool.and(Nat.is_gt(need, 0n), Nat.is_ge(bridge2_len(buf), need))

# A frame whose declared length exceeds the sane cap (SERVE.md §2, 64 MiB) is a
# protocol error: the reader closes rather than buffering forever.
def bridge3_frame_bad(+buf: List<&2, U32>) -> Bool:
  Nat.is_gt(bridge3_frame_need(buf), 67108864n)

def bridge3_frame_take(+buf: List<&2, U32>) -> List<&2, U32>:
  List.take(&2, U32, buf, bridge3_frame_need(buf))

def bridge3_frame_rest(+buf: List<&2, U32>) -> List<&2, U32>:
  List.drop(&2, U32, buf, bridge3_frame_need(buf))

def bridge3_reader_go(
  fuel: Nat,
  +phase: U32,
  +chan: Chan(Bridge2Ctrl),
  q: File & Result<&1, &1, U32 & String, List<&2, U32>>,
  +buf: List<&2, U32>,
  +ready: Bool,
  +bad: Bool
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
                q2 : File & Result<&1, &1, U32 & String, List<&2, U32>> <- File.read_bytes(f0, 65536)
                bridge3_reader_go(p, 1, chan, q2, buf, False{}, False{})
        case 1:
          match q:
            case (f2, res):
              match res:
                case Done{value}:
                  bridge3_reader_go(p, 2, chan, (f2, Fail{(0, "")}), List.append(&2, U32, buf, value), False{}, False{})
                case Fail{(code, message)}:
                  bridge3_reader_go(p, 6, chan, (f2, Fail{(0, "")}), buf, False{}, False{})
        case 2:
          bridge3_reader_go(p, 3, chan, q, buf, bridge3_frame_ready(buf), bridge3_frame_bad(buf))
        case 3:
          match ready:
            case True{}:
              do IO<Unit>:
                sent : Bool <- Chan.send(Bridge2Ctrl, chan, bridge2_decode_control(bridge3_frame_take(buf)))
                bridge3_reader_go(p, 2, chan, q, bridge3_frame_rest(buf), False{}, False{})
            case False{}:
              match bad:
                case True{}:
                  do IO<Unit>:
                    IO.print_err("serve: control frame too large\n")
                    Chan.close(Bridge2Ctrl, chan)
                case False{}:
                  bridge3_reader_go(p, 0, chan, q, buf, False{}, False{})
        case 6:
          bridge3_reader_go(p, 9, chan, q, buf, bridge3_frame_ready(buf), bridge3_frame_bad(buf))
        case _:
          match ready:
            case True{}:
              do IO<Unit>:
                sent : Bool <- Chan.send(Bridge2Ctrl, chan, bridge2_decode_control(bridge3_frame_take(buf)))
                bridge3_reader_go(p, 6, chan, q, bridge3_frame_rest(buf), False{}, False{})
            case False{}:
              do IO<Unit>:
                IO.print_err("serve: control EOF\n")
                Chan.close(Bridge2Ctrl, chan)

def bridge3_reader(chan: Chan(Bridge2Ctrl)) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("/dev/stdin", "r"))
    bridge3_reader_go(1048576n, 0, chan, (f, Fail{(0, "")}), Nil{}, False{}, False{})

# The flow-based live link: HELLO, an ORIGIN (the canonical window's base chunk),
# a dense SNAPSHOT of the genesis world at tick 0, then a continuous DELTA stream
# (one frame per resident-window tick). A renderer FOCUS request shifts the
# resident window and the engine emits a fresh ORIGIN + SNAPSHOT of the moved
# window. The stream is gated by the credit window the forked reader fills from
# CREDIT. A STOP frame (or EOF) sets the flow's sticky stop flag; the loop then
# flushes a sparse checkpoint SNAPSHOT, a PING and a BYE.
#
# The live world is **shell-free** (decision A, `G-scale-8`): the window / infinite
# mode samples `Worldgen.gen_terrain`, so the link world is `Sim.build_terrain`
# (support-seeded, no absolute `{0,63}` bedrock) and the whole store/focus path is
# threaded with `Worldgen.terrain()`. The shelled `Sim.build` stays the reference
# mode (`Test/tests`/`simtests` build it directly); a moving window must not carry
# the absolute shell, which after a shift can land inside the resident set.
def bridge3_link_world() -> Array<U32>:
  Fixtures.spawn(Sim.shellfree_build_terrain())

def bridge3_live_fuel() -> Nat:
  1073741824n

# The final keyframe (windowed): a sparse SNAPSHOT of the resident window, a
# PING, then BYE.
def focus_checkpoint(+sel: Bool, +w: Window.Window, +s: Store.Store, +chan: Chan(Bridge2Ctrl), +tick: U32, f: Bridge3Flow) -> IO(Unit):
  do IO<Unit>:
    f1 : Bridge3Flow <- bridge3_write_frame(f, chan, tick, focus_snapshot_sparse(sel, w, s, tick))
    f2 : Bridge3Flow <- bridge3_write_frame(f1, chan, tick, bridge2_ping(tick))
    bridge2_stdout(bridge2_bye())
    IO.print_err("serve: checkpoint tick=" ++ U32.show(tick) ++ ", bye\n")

# The genesis `(window, store, deltas)` for tick 1: the canonical window at tick 0,
# checkpointed after one canonical tick.
def focus_initial(+sel: Bool) -> Window.Window & Store.Store & List<Sim.Delta>:
  +w0 = Window.canonical()
  +s0 = Sim.w5_ck_store_sel(sel, w0, bridge3_link_world())
  focus_next_state(sel, w0, s0)

# Flush the terminal checkpoint at the loop's current tick.
def bridge3_live_finish(+sel: Bool, r: Window.Window & Store.Store & List<Sim.Delta>, chan: Chan(Bridge2Ctrl), +tick: U32, f: Bridge3Flow) -> IO(Unit):
  match r:
    case (w, s, ds):
      focus_checkpoint(sel, w, s, chan, tick, f)

# The continuous loop body: one self-recursive `def` with a phase selector (Bend
# has no forward references / mutual recursion). `fuel` is `2 * ticks` because
# every self-call must decrement it.
#
# `r` is the resident `(window, store, deltas)` at `tick`; the store holds the
# ticked state, so a move can carry it across the seam. Phases:
#   0  check the stop flag;
#   1  write `tick`'s DELTA (window-local idx) and drop into 2;
#   2  consume a pending FOCUS: none -> advance one canonical tick; some -> shift
#      the window (`Sim.w5_trace_step`) and drop into 3;
#   3  emit ORIGIN + a fresh moved-window SNAPSHOT (which supersedes the deltas
#      before the move), then continue at the tick after the move's tick.
# A post-STOP SNAPSHOT may supersede one unbroadcast tick -- legal, since a
# SNAPSHOT supersedes all deltas.
def bridge3_live_go(
  +sel: Bool, fuel: Nat, +phase: U32, +tick: U32, +chan: Chan(Bridge2Ctrl), f: Bridge3Flow,
  r: Window.Window & Store.Store & List<Sim.Delta>
) -> IO(Unit):
  match fuel:
    case 0n:
      bridge3_live_finish(sel, r, chan, tick, f)
    case 1n+p:
      match phase:
        case 0:
          match f:
            case B3Flow{window, queued, cap, coalesced, keyframe, tick0, idle, stop, focus}:
              match stop:
                case True{}:
                  bridge3_live_finish(sel, r, chan, tick, f)
                case False{}:
                  bridge3_live_go(sel, p, 1, tick, chan, f, r)
        case 1:
          match r:
            case (+w, +s, ds):
              do IO<Unit>:
                f2 : Bridge3Flow <- bridge3_write_frame(f, chan, tick, focus_delta_frame(w, tick, ds))
                r1 : Window.Window & Store.Store & List<Sim.Delta> = (w, s, Nil{})
                bridge3_live_go(sel, p, 2, tick, chan, f2, r1)
        case 2:
          match f:
            case B3Flow{window, queued, cap, coalesced, keyframe, tick0, idle, stop, focus}:
              match focus:
                case FocusNone{}:
                  match r:
                    case (+w, +s, _):
                      do IO<Unit>:
                        r2 : Window.Window & Store.Store & List<Sim.Delta> = focus_next_state(sel, w, s)
                        bridge3_live_go(sel, p, 0, U32.add(tick, 1), chan, f, r2)
                case FocusAt{cx, cy, cz}:
                  match r:
                    case (+w, +s, _):
                      do IO<Unit>:
                        fnew : Bridge3Flow = B3Flow{window, queued, cap, coalesced, keyframe, tick0, idle, stop, FocusNone{}}
                        r3 : Window.Window & Store.Store & List<Sim.Delta> =
                          Sim.w5_trace_step_sel(sel, w, focus_dcx(w, cx), focus_dcy(w, cy), focus_dcz(w, cz), 1n, s)
                        bridge3_live_go(sel, p, 3, U32.add(tick, 1), chan, fnew, r3)
        case _:
          match r:
            case (+w2, +s2, _):
              do IO<Unit>:
                f2 : Bridge3Flow <- bridge3_write_frame(f, chan, tick, focus_origin_frame(w2))
                f3 : Bridge3Flow <- bridge3_write_frame(f2, chan, tick, focus_snapshot_sparse(sel, w2, s2, tick))
                r4 : Window.Window & Store.Store & List<Sim.Delta> = focus_next_state(sel, w2, s2)
                bridge3_live_go(sel, p, 0, U32.add(tick, 1), chan, f3, r4)

# Control path: a forked reader parses CREDIT/REQUEST/STOP/FOCUS from stdin; the
# writer is fully credit-gated, so the loop runs until STOP/EOF.
def bridge3_serve_control() -> IO(Unit):
  do IO<Unit>:
    +chan : Chan(Bridge2Ctrl) <- Chan.new(Bridge2Ctrl, 1)
    IO.spawn(Unit, bridge3_reader(chan))
    IO.print_err("serve: hello\n")
    bridge2_stdout(bridge2_hello(0))
    bridge2_stdout(focus_origin_frame(Window.canonical()))
    f0 : Bridge3Flow = bridge3_flow_new(8)
    f1 : Bridge3Flow <- bridge3_write_frame(f0, chan, 0, bridge2_snapshot_dense(bridge3_link_world(), 0))
    IO.print_err("serve: dense snapshot tick=0\n")
    bridge3_live_go(Worldgen.terrain(), bridge3_live_fuel(), 0, 1, chan, f1, focus_initial(Worldgen.terrain()))

# No-control path: the same loop, but the window is pre-seeded so no reader is
# needed; it runs a bounded number of ticks and then checkpoints.
def bridge3_serve_bounded(+ticks: Nat) -> IO(Unit):
  do IO<Unit>:
    +chan : Chan(Bridge2Ctrl) <- Chan.new(Bridge2Ctrl, 1)
    IO.print_err("serve: hello\n")
    bridge2_stdout(bridge2_hello(0))
    bridge2_stdout(focus_origin_frame(Window.canonical()))
    f0 : Bridge3Flow = bridge3_credit(bridge3_flow_new(8), 64)
    f1 : Bridge3Flow <- bridge3_write_frame(f0, chan, 0, bridge2_snapshot_dense(bridge3_link_world(), 0))
    IO.print_err("serve: dense snapshot tick=0\n")
    bridge3_live_go(Worldgen.terrain(), Nat.double(Nat.double(ticks)), 0, 1, chan, f1, focus_initial(Worldgen.terrain()))

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
