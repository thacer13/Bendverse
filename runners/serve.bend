import Base
import ../src/grid.bend as Grid
import ../src/chunk.bend as Chunk
import ../src/sim.bend as Sim
import ./export.bend as Export

# serve -- the writer side of the Bendview sidecar (track `bridge`, P2).
#
# Skeleton only: it emits HELLO, a few length-framed SNAPSHOTs (ticks 0,1,2),
# then BYE, reusing `runners/export.bend`'s encoders so there is exactly one
# snapshot format. The design (framing, lifecycle, credit/backpressure, and the
# delta stream owned by the `scale` track) is `runners/SERVE.md`; the delta
# stream is deliberately not implemented here.
#
# Frame header (little-endian, see SERVE.md §2):
#   u32 payload_len, u32 kind, payload_len bytes
# kinds: 0 HELLO, 1 SNAPSHOT, 2 DELTA, 3 PING, 4 BYE.
#
# Usage:  serve > stream.bin        (writes the binary stream to stdout)

def bxe_frame(+kind: U32, +payload: List<&2, U32>) -> List<&2, U32>:
  +n = U32.from_nat(List.length(&2, U32, payload))
  Export.bxe_u32_le(n, Export.bxe_u32_le(kind, payload))

# HELLO: version, world_edge, chunk_edge, seed, tick. Every field is the
# engine's own constant, so the renderer can validate its port first.
def bxe_hello(+tick: U32) -> List<&2, U32>:
  payload = Export.bxe_u32_le(1,
    Export.bxe_u32_le(Grid.size(),
      Export.bxe_u32_le(Chunk.size(),
        Export.bxe_u32_le(Export.bxe_seed(),
          Export.bxe_u32_le(tick, Nil{})))))
  bxe_frame(0, payload)

def bxe_snapshot_frame(world: Array<U32>, +ticks: U32) -> List<&2, U32>:
  bxe_frame(1, Export.bxe_snapshot_bytes(world, ticks))

def bxe_bye() -> List<&2, U32>:
  bxe_frame(4, Nil{})

# Open `/dev/stdout` in append mode: a redirect from the shell already
# truncated the file, and O_APPEND keeps successive frames in order instead of
# each open truncating the previous ones (mode "w" would).
def bxe_stdout(data: List<&2, U32>) -> IO(Unit):
  do IO<Unit>:
    f : File <- IO.try(File, File.open("/dev/stdout", "a"))
    q : File & Result<&1, &1, U32 & String, Unit> <- File.write_bytes(f, data)
    Export.bxe_finish(q)

# Rebuild the world fresh per frame so the snapshot encoder can consume it
# linearly (a real sidecar would tick and clone; this is the skeleton).
def bxe_pump(fuel: Nat, +tick: U32) -> IO(Unit):
  match fuel:
    case 0n:
      do IO<Unit>:
        bxe_stdout(bxe_bye())
        IO.print_err("serve: bye\n")
    case 1n+p:
      do IO<Unit>:
        world : Array<U32> = Sim.ticks(U32.to_nat(tick), Sim.build())
        bxe_stdout(bxe_snapshot_frame(world, tick))
        IO.print_err("serve: snapshot tick=" ++ U32.show(tick) ++ "\n")
        bxe_pump(p, U32.add(tick, 1))

def main() -> IO(Unit):
  do IO<Unit>:
    IO.print_err("serve: hello\n")
    bxe_stdout(bxe_hello(0))
    bxe_pump(3n, 0)
