import Base
import ./store.bend as Store
import ./word.bend as WR
import ./nat.bend as NatL
import ./chunk.bend as Chunk
import ./window.bend as Window

# ============================================================================
# g4 (P3 / G-scale-4 residual) -- the assemble/evict roundtrip, at the precision
# the store actually supports.
#
# PLAN.md §5.3 (`G-scale-4`) asks for `assemble(evict s) == assemble s`, and
# records that the law needs an `Array` update-identity under the `G5` boundary,
# plus store-level `get`/`set` refinement lemmas. This module supplies the two
# bricks that were actually missing, both fully proven:
#
#   * `g4_gen_eq_cells_eq` : the proof-relevant reflection the gap named as a
#     blocker. `Store.gen_eq_cells` compares two chunk cell lists elementwise
#     with `U32.is_eq` and folds the result through `Bool.and`; from a `True`
#     result it recovers `cells == gen` as a *propositional* list equality.
#     The `U32.is_eq` eliminator already existed (`WR.u32_cmp_eq`, law
#     `u32_cmp_eq_reflect`); what was missing was (a) `Bool.and` reflection and
#     (b) the fuel/length bookkeeping that rules out the trivially-True
#     over-budget cases (`gen_eq_cells 0 cs gs True == True` for any `cs`,`gs`).
#     The law therefore carries the exact side conditions `fuel == length cells`
#     and `length gen == fuel`; for the store these are the chunk-size facts
#     that the resident lists are 4096 long (T161).
#
#   * `g4_assemble_chunk_regen` : the `Array` update-identity, in its honest
#     form. `Store.assemble_chunk_w` is a pure fold of `Array.set`s, so two
#     pointwise-equal cell lists assemble to the *same* array; combined with the
#     reflection, a stored chunk that is regenerable assembles exactly as its
#     pure-gen replacement. This is the per-chunk `assemble(evict)` step.
#
# What is NOT proven here (and is filed as a gap candidate):
#
#   * The headline `assemble(evict s) == assemble s` cannot even be *stated* as a
#     gate goal: `Store.assemble_cells_w_sel` calls `Store.chunk_list_sel`, whose
#     body eagerly builds a 4096-leaf `Chunk.build_sel` array and converts it
#     with `Grid.to_list`. Normalising that inside the checker costs tens of
#     seconds per occurrence and, nested under `assemble_cells_*`, does not
#     terminate in the gate budget (measured: >45 s for a reflexive goal that
#     mentions the function once). All laws below are therefore stated over the
#     variable-fuel primitive `assemble_chunk_w` (the exact function both the
#     `Some` and the `None` branch of `assemble_cells_w_sel` reduce to), which
#     the checker normalises instantly.
#   * The store-level `get`/`set` refinement ("a dropped key reads back `None`;
#     a kept key reads back its value") is not proven: `Store.get_w`/`set_w` are
#     correct only when every `SLeaf` sits at full depth (32), since a `SLeaf`
#     met by `set_w` at an intermediate level is overwritten and a `SLeaf` read
#     back at intermediate level yields `None`. Proving it needs a well-formed
#     trie invariant over the 32-bit key path. The runtime witnesses T162/T163
#     exercise the actual `evict`/`get` behaviour instead.
# ============================================================================

# False-elimination (Base has no primitive; the same `Bool.pick`-motive trick as
# `NatL`/`Word` use).
def g4_absurd(T: Type, X: T, Y: T, +h: {False{} == True{} : Bool}) -> {X == Y : T}:
  Equal.cong(Bool, T, x => Bool.pick(T, x, Y, X), False{}, True{}, h)

# --------------------------------------------------------------- Nat length
# `1 + p` is never `0` (the over-budget base case of `gen_eq_cells`), and
# `1 + a = 1 + b` cancels. `List.length` of a `Con` reduces to `1 + length tail`,
# so these are what turn the `1n+p` match on the fuel into the induction.

def g4_nat_pred(n: Nat) -> Bool:
  match n:
    case 0n: True{}
    case 1n+_: False{}

def g4_nat_succ_ne_zero(p: Nat, +h: {Nat.add(1n, p) == 0n : Nat}) -> {False{} == True{} : Bool}:
  Equal.cong(Nat, Bool, m => g4_nat_pred(m), Nat.add(1n, p), 0n, h)

def g4_length_zero(xs: List<&2, U32>, +h: {List.length(&2, U32, xs) == 0n : Nat}) -> {xs == Nil{} : List<&2, U32>}:
  match xs:
    case Nil{}: {==}
    case Con{+hd, +tl}:
      g4_absurd(List<&2, U32>, Con{hd, tl}, Nil{},
        g4_nat_succ_ne_zero(List.length(&2, U32, tl), h))

def g4_add1_cancel(+a: Nat, +b: Nat, +h: {Nat.add(1n, a) == Nat.add(1n, b) : Nat}) -> {a == b : Nat}:
  +h1 = Equal.trans(Nat, Nat.add(a, 1n), Nat.add(1n, a), Nat.add(1n, b),
          Equal.sym(Nat, Nat.add(1n, a), Nat.add(a, 1n), NatL.n_add_comm(1n, a)), h)
  +h2 = Equal.trans(Nat, Nat.add(a, 1n), Nat.add(1n, b), Nat.add(b, 1n), h1, NatL.n_add_comm(1n, b))
  NatL.n_add_cancel_right(a, b, 1n, h2)

# ------------------------------------------------------------- Bool.and
# Reflection for the accumulator `gen_eq_cells` folds through `Bool.and`.

def g4_and_false_right(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case False{}: {==}
    case True{}: {==}

def g4_and_true_left(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case False{}:
      g4_absurd(Bool, False{}, True{},
        Equal.trans(Bool, False{}, Bool.and(False{}, b), True{},
          Equal.sym(Bool, Bool.and(False{}, b), False{}, {==}), h))
    case True{}: {==}

def g4_and_true_right(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match b:
    case True{}: {==}
    case False{}:
      g4_absurd(Bool, False{}, True{},
        Equal.trans(Bool, False{}, Bool.and(a, False{}), True{},
          Equal.sym(Bool, Bool.and(a, False{}), False{}, g4_and_false_right(a)), h))

# ------------------------------------------------- `gen_eq_cells` reflection
# `gen_eq_cells` returns its accumulated `eq` once the fuel runs out, so a `True`
# result on an over-budget call says nothing about the lists. `_acc` recovers the
# accumulator (`eq == True`) under the exact-budget hypothesis; `_eq` then peels
# the pairs and uses `WR.u32_cmp_eq` on each reflected `is_eq`.

def g4_gen_eq_cells_acc(fuel: Nat, +cells: List<&2, U32>, +gen: List<&2, U32>, +eq: Bool,
    +hfuel: {fuel == List.length(&2, U32, cells) : Nat},
    +h: {Store.gen_eq_cells(fuel, cells, gen, eq) == True{} : Bool})
  -> {eq == True{} : Bool}:
  match fuel:
    case 0n:
      h
    case 1n+ +p:
      match cells gen:
        case Nil{} Nil{}:
          h
        case Nil{} Con{+hy, +ty}:
          g4_absurd(Bool, eq, True{}, h)
        case Con{+hx, +tx} Nil{}:
          g4_absurd(Bool, eq, True{}, h)
        case Con{+hx, +tx} Con{+hy, +ty}:
          +hf = g4_add1_cancel(p, List.length(&2, U32, tx), hfuel)
          g4_and_true_left(eq, U32.is_eq(hx, hy),
            g4_gen_eq_cells_acc(p, tx, ty, Bool.and(eq, U32.is_eq(hx, hy)), hf, h))

def g4_gen_eq_cells_eq(fuel: Nat, +cells: List<&2, U32>, +gen: List<&2, U32>, +eq: Bool,
    +hfuel: {fuel == List.length(&2, U32, cells) : Nat},
    +hlen: {List.length(&2, U32, gen) == fuel : Nat},
    +h: {Store.gen_eq_cells(fuel, cells, gen, eq) == True{} : Bool})
  -> {cells == gen : List<&2, U32>}:
  match fuel:
    case 0n:
      +hc = g4_length_zero(cells, Equal.sym(Nat, fuel, List.length(&2, U32, cells), hfuel))
      +hg = g4_length_zero(gen, hlen)
      Equal.trans(List<&2, U32>, cells, Nil{}, gen, hc, Equal.sym(List<&2, U32>, gen, Nil{}, hg))
    case 1n+ +p:
      match cells gen:
        case Nil{} Nil{}:
          {==}
        case Nil{} Con{+hy, +ty}:
          g4_absurd(List<&2, U32>, Nil{}, Con{hy, ty}, h)
        case Con{+hx, +tx} Nil{}:
          g4_absurd(List<&2, U32>, Con{hx, tx}, Nil{}, h)
        case Con{+hx, +tx} Con{+hy, +ty}:
          +hf = g4_add1_cancel(p, List.length(&2, U32, tx), hfuel)
          +hg = g4_add1_cancel(List.length(&2, U32, ty), p, hlen)
          +hacc = g4_gen_eq_cells_acc(p, tx, ty, Bool.and(eq, U32.is_eq(hx, hy)), hf, h)
          +heq = g4_and_true_right(eq, U32.is_eq(hx, hy), hacc)
          +hxy = WR.u32_cmp_eq(hx, hy, heq)
          +htx = g4_gen_eq_cells_eq(p, tx, ty, Bool.and(eq, U32.is_eq(hx, hy)), hf, hg, h)
          Equal.trans(List<&2, U32>, Con{hx, tx}, Con{hy, tx}, Con{hy, ty},
            Equal.cong(U32, List<&2, U32>, v => Con{v, tx}, hx, hy, hxy),
            Equal.cong(List<&2, U32>, List<&2, U32>, t => Con{hy, t}, tx, ty, htx))

# ------------------------------------------------------- Array update-identity
# `assemble_chunk_w` is a pure fold of writes, so equal cell lists give equal
# arrays (no commutativity or idempotence of `Array.set` is needed: the two runs
# perform the *same* sequence of writes).

def g4_assemble_chunk_cong(
  fuel: Nat, +w: Window.Window, +i: U32, +k: U32,
  +c1: List<&2, U32>, +c2: List<&2, U32>, world: Array<U32>,
  +h: {c1 == c2 : List<&2, U32>}
) -> {Store.assemble_chunk_w(fuel, w, i, k, c1, world) == Store.assemble_chunk_w(fuel, w, i, k, c2, world) : Array<U32>}:
  Equal.cong(List<&2, U32>, Array<U32>,
    l => Store.assemble_chunk_w(fuel, w, i, k, l, world), c1, c2, h)

# The per-chunk roundtrip: a stored chunk that passes `gen_eq_cells` against its
# pure gen list assembles exactly as the regenerated chunk. This is the
# `assemble(evict)` step at one key; the store-level walk over the 64 keys is the
# residual (see the header).
def g4_assemble_chunk_regen(
  +fuel: Nat, +w: Window.Window, +i: U32, +k: U32,
  +cells: List<&2, U32>, +gen: List<&2, U32>, world: Array<U32>,
  +hfuel: {fuel == List.length(&2, U32, cells) : Nat},
  +hlen: {List.length(&2, U32, gen) == fuel : Nat},
  +h: {Store.gen_eq_cells(fuel, cells, gen, True{}) == True{} : Bool}
) -> {Store.assemble_chunk_w(fuel, w, i, k, cells, world) == Store.assemble_chunk_w(fuel, w, i, k, gen, world) : Array<U32>}:
  +heq = g4_gen_eq_cells_eq(fuel, cells, gen, True{}, hfuel, hlen, h)
  g4_assemble_chunk_cong(fuel, w, i, k, cells, gen, world, heq)

# The chunk-size instance (`fuel = Chunk.cells() = 4096`), the fuel the store's
# own `assemble_cells_w_sel` uses.
def g4_assemble_chunk_regen_chunk(
  +w: Window.Window, +i: U32, +k: U32,
  +cells: List<&2, U32>, +gen: List<&2, U32>, world: Array<U32>,
  +hfuel: {U32.to_nat(Chunk.cells()) == List.length(&2, U32, cells) : Nat},
  +hlen: {List.length(&2, U32, gen) == U32.to_nat(Chunk.cells()) : Nat},
  +h: {Store.gen_eq_cells(U32.to_nat(Chunk.cells()), cells, gen, True{}) == True{} : Bool}
) -> {Store.assemble_chunk_w(U32.to_nat(Chunk.cells()), w, i, k, cells, world) == Store.assemble_chunk_w(U32.to_nat(Chunk.cells()), w, i, k, gen, world) : Array<U32>}:
  g4_assemble_chunk_regen(U32.to_nat(Chunk.cells()), w, i, k, cells, gen, world, hfuel, hlen, h)

# The `Some` (resident/kept) branch of the store's own `assemble_cells_w_sel` is
# definitionally the primitive at `Chunk.cells()`. Bridging it makes the
# per-chunk roundtrip above a statement about the real store function for a
# present chunk. The `None` branch cannot be bridged in the gate: it reduces to
# `chunk_list_sel`, whose 4096-leaf build the checker cannot normalise (the
# barrier recorded in the header, and the residual gap candidate).
def g4_assemble_cells_present(
  +sel: Bool, +w: Window.Window, +k: U32, +cells: List<&2, U32>, world: Array<U32>
) -> {Store.assemble_cells_w_sel(sel, w, Some{cells}, k, world) == Store.assemble_chunk_w(U32.to_nat(Chunk.cells()), w, 0, k, cells, world) : Array<U32>}:
  {==}
