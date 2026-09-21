# Bendverse sidecar transport (track `bridge`, P2)

**Status.** Design note, not a spec rewrite. The renderer contract is
`../Bendview/SPEC.md`; the engine facts are `../src/`. This document adds the
*transport* between a headless Bendverse process and Bendview: how one or more
frames of world state cross a pipe. It does not change the snapshot format
(`runners/export.bend` owns that), and it does not define deltas — the `scale`
track owns the delta shape and this note only assumes it.

## 1. Transport

- **Channel.** The sidecar writes frames to **stdout** and reads control from
  **stdin**. Either end may be a pipe (`|`), a FIFO (`mkfifo`), or a
  process-substitution file descriptor. No socket is required; a Unix-domain
  socket may be dropped in later behind the same framing.
- **Binary.** stdout/stdin are byte streams; the host must not line-buffer,
  translate newlines, or encode. On Windows set `O_BINARY` once at startup.
- **Direction.** Engine → renderer carries frames (HELLO/SNAPSHOT/DELTA/PING/
  BYE). Renderer → engine carries control (CREDIT/REQUEST/STOP) as described in
  §6. Both directions use the same frame header, so one decoder serves both.
- **One writer per stream.** Frames are emitted by a single writer; the
  simulation never writes directly (see §5).

## 2. Framing

Every message is one frame. The header is fixed-size and little-endian:

    offset  size  field
    0       4     payload_len   bytes after the header (u32)
    4       4     kind          message kind (u32)
    8       ...   payload       payload_len bytes, kind-defined

`payload_len` is the exact payload size, so a reader can skip, buffer, or
resynchronise without understanding the payload. A frame with `payload_len`
larger than a sane cap (default 64 MiB) is a protocol error; the reader closes
the stream. Frames never nest.

Kind values:

| kind | name      | direction | payload |
|---|---|---|---|
| 0 | `HELLO`    | engine → renderer | `version u32, world_edge u32, chunk_edge u32, seed u32, tick u32` |
| 1 | `SNAPSHOT` | engine → renderer | chunk-oriented snapshot body, genesis-format (see below) |
| 2 | `DELTA`    | engine → renderer | tick + write list (shape owned by `scale`; assumed in §3) |
| 3 | `PING`     | both | `tick u32` heartbeats on an idle stream |
| 4 | `BYE`      | engine → renderer | empty; the producer is exiting cleanly |
| 5 | `CREDIT`   | renderer → engine | `frames u32`; advances the send window (°6) |
| 6 | `REQUEST`  | renderer → engine | `tick u32, flags u32`; ask for a fresh SNAPSHOT |
| 7 | `STOP`     | renderer → engine | empty; equivalent to closing stdin |
| 8 | `FOCUS`    | renderer → engine | `cx u32, cy u32, cz u32`; move the window's base chunk origin |
| 9 | `ORIGIN`   | engine → renderer | `bx u32, by u32, bz u32`; the window's current base chunk origin |

All multi-byte integers are little-endian throughout, matching the snapshot and
gen files (`runners/export.bend`).

### 2.1 Focus and the window origin (track `focus`, Bendview D1)

The fixed-window link is canonical; the **focus protocol** makes the resident
window follow the renderer's camera.

- **`FOCUS` (kind 8)** carries the target **base chunk origin** `(cx, cy, cz)` of
the window (a chunk origin, not a global cell: it is total, exactly the
coordinate `Window.shift` consumes, and symmetric with `ORIGIN`). The renderer
derives the chunk it wants from its camera and the last `ORIGIN` it received.
- **`ORIGIN` (kind 9)** replies with the window's base chunk origin, so the
renderer can re-anchor its view frame. It is emitted once right after `HELLO`
(the canonical `(0,0,0)`) and again immediately before every moved-window
`SNAPSHOT`.
- On a focus request the engine shifts the resident window (`Window.shift`),
loads the entering slab / evicts the leaving slab (`Store.move_store`, lossless),
runs one moved-window tick (`Sim.w5_trace_step`), then emits `ORIGIN` + a fresh
`SNAPSHOT` of the moved window. A `SNAPSHOT` supersedes all prior deltas (§4),
so the renderer may discard its delta run at the move. The engine coalesces
requests: the newest pending `FOCUS` wins; requests arriving while a move is in
flight are applied at the next frame boundary.
- **Delta coordinates after a move.** A `DELTA` `idx` is the **window-local**
flat index (`Window.win_index`), so it is relative to the most recent `ORIGIN`.
On the canonical window `Window.win_index == Grid.index`, so the fixed-window
bytes are unchanged. (This is the one payload change a moving-window client
must make: apply `idx` against the window anchored at the last `ORIGIN` rather
than the global 64³ `Grid.index`.)

## 3. Assumed delta payload (owned by `scale`)

This note **assumes**, and does not implement, the delta shape:

    tick       u32
    count      u32
    writes     count records, each:
                 idx  u32          Grid.index of the changed cell
                 op   u32          Rules op tag
                 src  u32          source word / operand
    wake_count u32
    wakes      wake_count u32     Grid.index values woken at tick end

The record fields mirror `Rules.Write` (`WSet{idx, op, src}` / `WWake{idx}`) and
`src/rules.bend`, and `idx` is a `Grid.index`. If the `scale` track changes the
shape, this section changes with it; the framing does not. A delta is only valid
against the state at `tick - 1` (or against the most recent SNAPSHOT at that
tick).

## 4. Lifecycle

1. Renderer spawns `bendverse-serve` (or attaches the FIFO) and starts reading.
2. Engine sends **HELLO** first. All fields come from the engine's own
   constants (`Grid.size`, `Chunk.size`, `Worldgen.seed`), so the renderer can
   validate its own port before trusting a single cell. An **ORIGIN** frame
   follows immediately, carrying the initial window base chunk (`(0,0,0)` for
   the canonical window).
3. Engine sends a **SNAPSHOT** at tick 0 (the initial state), then **DELTA**
   frames as ticks advance. It may send a new SNAPSHOT at any time (checkpoint,
   request, or catch-up); a SNAPSHOT always supersedes all prior deltas.
4. A renderer **FOCUS** request moves the resident window. The engine replies
   with a fresh **ORIGIN** and a **SNAPSHOT** of the moved window (a keyframe),
   then continues the delta stream window-locally.
5. On an idle stream the engine emits **PING** at least every `ping_ms` (default
   1000 ms) so the renderer can distinguish "quiet" from "dead".
6. Engine exits: flush a final **BYE**, then close. Renderer exits: it closes
   stdin / sends **STOP**; the engine stops at the next frame boundary.

A reader that sees EOF without **BYE** treats the stream as truncated and
requests/reconnects; a reader that sees **BYE** may close cleanly.

## 5. Decoupling (presentation may be stale)

`../Bendview/AGENTS.md` and `SPEC.md` §5 require that the *renderer never stalls
the engine*. The sidecar therefore splits the engine thread from the writer
thread:

- The simulation advances at its own rate and pushes deltas into a **bounded**
  queue (rendezvous size 1 frame by default, 8 frames hard cap).
- The writer drains that queue to stdout. A slow renderer blocks the *writer*,
  never the tick loop.
- When the queue is full the engine **coalesces**: intermediate deltas are
  dropped and a marker is set so the writer emits a fresh **SNAPSHOT** instead
  of the lost run. The renderer thus sees either a contiguous delta run or a
  clean keyframe jump — never a gap it must guess through. Dropping presentation
  data is allowed; blocking the engine is not.

## 6. Backpressure

Backpressure is explicit and credit-based, because a blocking `write` on stdout
is the failure mode this design exists to avoid:

- After **HELLO**, the renderer grants an initial window of `W` frames (default
  `W = 4`) with **CREDIT**.
- The writer decrements the window per frame and blocks its own thread when the
  window is empty. The engine never blocks: it keeps ticking and coalescing
  (§5).
- The renderer sends **CREDIT n** after consuming n frames, refilling the
  window. Credit is advisory — stdout itself can still block if the renderer
  never reads — but it bounds how much stale data the writer holds.
- A snapshot is ~1 MiB and the OS pipe buffer is typically 64 KiB, so a
  snapshot write necessarily blocks part-way. The renderer must always read
  concurrently with the engine's write; the sidecar does not try to make
  snapshots atomic with respect to the pipe buffer.
- If credit is exhausted and the window stays empty for longer than
  `stall_ms` (default 2000 ms), the writer discards queued deltas and arms one
  **SNAPSHOT** for when credit returns.

## 7. Ordering and invariants

- Frames on a stream are totally ordered; each carries or implies a `tick`, and
  `tick` is non-decreasing. A SNAPSHOT at tick `T` makes any later delta with
  `tick <= T` redundant.
- A delta applies to exactly the state produced by the preceding frame at
  `tick - 1`. The renderer may apply a delta out of order only by discarding it
  and requesting a SNAPSHOT.
- CRC/checksums are intentionally out of scope for v1: under POSIX pipes and
  FIFOs the transport is reliable and ordered, and a truncated stream is
  detected by a short read against `payload_len`. Add per-frame checksums only
  if a lossy channel is ever used.

## 8. CLI sketch

    bendverse-serve [--ticks-per-frame N] [--snapshot-every M]
                    [--credit-window W] [--ping-ms MS]

Defaults: `N = 1`, `M = 0` (no periodic checkpoint), `W = 4`, `MS = 1000`.
Diagnostics go to **stderr**, never stdout.

`runners/serve.bend` now realises §5-§6 on the writer side (track `bridge3`):
`HELLO`; an `ORIGIN` (window base chunk); a dense genesis `SNAPSHOT`; a tick's
`DELTA`; a sparse checkpoint `SNAPSHOT`; an idle `PING`; and a final `BYE`,
reusing `runners/export.bend`'s encoders so there is exactly one snapshot format.
The outbound side is a bounded queue (`bridge3_flow_new`, default cap 8) under a
credit window (`bridge3_credit`/`bridge3_emit`), with drop-and-keyframe
coalescing (`bridge3_push_delta`/`bridge3_take_keyframe`) and an idle PING
(`bridge3_next`); `bridge3_reader` drains stdin continuously into a `Chan` and
`bridge3_write_frame` blocks the writer, not the engine, on an empty window.
The accounting is pure and witnessed by T76-T80; the engine/writer thread split
remains co-resident because Bend's `Chan.recv` parks rather than polls (no
non-blocking `try_recv`), which is recorded as a gap candidate.

The **moving-window focus path** (track `focus`, §2.1) threads the resident
`Window` through the live loop (`focus_initial`, `focus_next_state`) and consumes
a pending `FOCUS` at a frame boundary: `Sim.w5_trace_step` shifts the window and
runs the moved-window tick, then the engine emits `ORIGIN` + a sparse
moved-window `SNAPSHOT` (`focus_origin_frame`, `focus_snapshot_sparse`). `DELTA`
idx is window-local (`focus_delta_frame`), identical to `Grid.index` on the
canonical window. The wire shapes are witnessed tick-free by T151-T155; the
native end-to-end moved-window stream is left to integration.
