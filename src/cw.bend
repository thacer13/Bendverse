import Base

# ============================================================================
# cw (P3) -- global coordinates for a moving chunk window.
#
# The live engine (`Grid.index`) is a fixed 64^3 torus: every axis is masked
# `&63`, so `Grid.neighbor` wraps and the box is closed by construction (V0-2 /
# `Grid.step_inside`). That is the right model for a fixed window, but a *moving*
# window at arbitrary coordinates needs a coordinate system that does not wrap:
# a chunk key plus a local offset that reconstruct the original global
# coordinate. This module is additive -- nothing in `Grid`/`Sim` uses it yet;
# the migration is scoped in `SCALE.md`.
#
# Layout. A chunk is 16^3 (`cw_chunk_size`), matching `src/chunk.bend`. The chunk
# key packs the three chunk indices into 10 bits each (the `Chunk.key` layout);
# the local index packs the 4-bit in-chunk offsets (the `Chunk.local` layout).
# There is no `&63` anywhere: `cw_global_*` is the identity on the split/rejoin
# pair for every coordinate below the 10-bit key range (16 * 1024 = 16384), and
# coordinates above 63 keep their chunk index instead of folding to the torus.
# ============================================================================

def cw_chunk_size() -> U32:
  16

def cw_chunk_bits() -> Nat:
  4n

def cw_chunk_cells() -> U32:
  4096

def cw_key_mask() -> U32:
  1023

def cw_local_mask() -> U32:
  15

# global coordinate -> chunk index / in-chunk offset (floor division by 16).
def cw_chunk_of(x: U32) -> U32:
  U32.shrn(x, 4n)

def cw_local_of(x: U32) -> U32:
  U32.and(x, 15)

# chunk-index triple <-> key (no torus; the index is masked to the key width).
def cw_key(cx: U32, cy: U32, cz: U32) -> U32:
  (U32.and(cx, 1023) .|. (U32.and(cz, 1023) << 10n) .|. (U32.and(cy, 1023) << 20n) : U32)

def cw_key_x(k: U32) -> U32:
  (k .&. 1023 : U32)

def cw_key_z(k: U32) -> U32:
  ((k >> 10n) .&. 1023 : U32)

def cw_key_y(k: U32) -> U32:
  ((k >> 20n) .&. 1023 : U32)

# local-offset triple <-> local index (4 bits per axis).
def cw_local(x: U32, y: U32, z: U32) -> U32:
  (U32.and(x, 15) .|. (U32.and(z, 15) << 4n) .|. (U32.and(y, 15) << 8n) : U32)

def cw_local_x(l: U32) -> U32:
  (l .&. 15 : U32)

def cw_local_z(l: U32) -> U32:
  ((l >> 4n) .&. 15 : U32)

def cw_local_y(l: U32) -> U32:
  ((l >> 8n) .&. 15 : U32)

# (key, local) -> global coordinate. This is the inverse of `cw_pack`; unlike
# `Grid.index` it never wraps, so it works at any window origin.
def cw_global_x(k: U32, l: U32) -> U32:
  U32.add(U32.shln(cw_key_x(k), 4n), cw_local_x(l))

def cw_global_y(k: U32, l: U32) -> U32:
  U32.add(U32.shln(cw_key_y(k), 4n), cw_local_y(l))

def cw_global_z(k: U32, l: U32) -> U32:
  U32.add(U32.shln(cw_key_z(k), 4n), cw_local_z(l))

# global (x, y, z) -> (chunk_key, local). `cw_global_x/y/z` invert it for every
# coordinate below 16384 on each axis (the 10-bit key range).
def cw_pack(+x: U32, +y: U32, +z: U32) -> U32 & U32:
  (cw_key(cw_chunk_of(x), cw_chunk_of(y), cw_chunk_of(z)),
   cw_local(cw_local_of(x), cw_local_of(y), cw_local_of(z)))

def cw_pack_key(r: U32 & U32) -> U32:
  match r:
    case (k, l):
      k

def cw_pack_local(r: U32 & U32) -> U32:
  match r:
    case (k, l):
      l
