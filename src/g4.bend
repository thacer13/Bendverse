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
#   * The store-level `get`/`set` refinement was the second blocker. `Store.get_w`/
#     `set_w` are correct only when every `SLeaf` sits at full depth (32), since a
#     `SLeaf` met by `set_w` at an intermediate level is overwritten and a `SLeaf`
#     read back at intermediate level yields `None`. This module now proves it:
#     `g4_wf` is the trie well-formedness invariant (a leaf at a partial depth is
#     exactly the malformed shape), `g4_set_w_wf` shows `set_w` preserves it, and
#     `g4_get_set_same` recovers `get(set(s,k,v),k) == Some{v}` for a well-formed
#     store. The companion `g4_get_set_other` shows a write at one key path is
#     invisible to a read at a *diverging* path (`g4_same(n,w,w') == False`),
#     which needs no well-formedness; `g4_get_set_same32`/`g4_get_set_other32`
#     are the full-depth `U32` statements (the latter keyed off
#     `U32.is_eq(k,k') == False` via `g4_same_eq_cmp`).
#
# What remains unproven (and is filed as a gap candidate): the 64-key
# `evict`/`assemble` fold itself. The per-key bricks are landed here:
# `g4_assemble_cells_same` (after a same-key `set` on a well-formed store, the
# key's assembly equals assembling its explicit chunk) and
# `g4_assemble_cells_other` (a `set` at another key is transparent), plus the
# accumulator primitives `g4_keep_cells_drop`/`_keep`. Threading those through
# `Store.evict_key_sel`'s concrete 64-step recursion -- and the dropped
# (regenerable) key's `None`-branch equality, which runs through the
# un-normalisable `chunk_list_sel` -- is the residual.
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

# ============================================================================
# Store-level `get`/`set` trie refinement (the second G-scale-4 blocker).
#
# The trie `Store.set_w`/`get_w` walks a `Word(n)` key prefix from the root and
# is only a map when every leaf sits at the *bottom* of the walk: a `SLeaf` met
# at an intermediate level is overwritten by `set_w` (losing its key) and read
# back as `None` by `get_w`. `g4_wf` makes that shape explicit -- a leaf is legal
# only at depth 0 -- and the four laws below pin the read-after-write behaviour.
# ============================================================================

# `Bool.and` introduction (the dual of the `_true_left`/`_true_right` projections
# already used by the `gen_eq_cells` reflection above).
def g4_and_intro(+a: Bool, +b: Bool, +ha: {a == True{} : Bool}, +hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}: hb
    case False{}: g4_absurd(Bool, False{}, True{}, ha)

# ------------------------------------------------------------ U32.is_eq refl
# `Word.cmp` on a word with itself is `EQ` (structural induction over the bit
# prefix), hence `U32.is_eq(a,a) == True`. Same development as `Commit`'s
# `v3c_w_cmp_refl`, restated here so the trie laws are self-contained.
def g4_w_cmp_refl(n: Nat, w: Word(n)) -> {Word.cmp(n, w, w) == EQ{} : Cmp}:
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+ +p:
      match w:
        case WCon{+wh, +wt}:
          match wh:
            case False{}:
              %Equal.sym(Cmp, Word.cmp(p, wt, wt), EQ{}, g4_w_cmp_refl(p, wt)) : {Word.cmp.fin(False{}, False{}, _) == EQ{} : Cmp}
              {==}
            case True{}:
              %Equal.sym(Cmp, Word.cmp(p, wt, wt), EQ{}, g4_w_cmp_refl(p, wt)) : {Word.cmp.fin(True{}, True{}, _) == EQ{} : Cmp}
              {==}

def g4_is_eq_refl(+a: U32) -> {U32.is_eq(a, a) == True{} : Bool}:
  match a:
    case U32{w}:
      Equal.cong(Cmp, Bool, c => Cmp.is_eq(c), Word.cmp(32n, w, w), EQ{}, g4_w_cmp_refl(32n, w))

# ------------------------------------------------------- well-formedness
# `g4_wf(n, s)`: every `SLeaf` in `s` is at depth 0 of the remaining `n`-bit walk.
# `STip` is legal anywhere (it is the empty subtree); `SNode` is legal when both
# children are well-formed. At `n = 0` the leaf is the whole subtree, so any `s`
# is accepted (`set_w` overwrites it and `get_w` reads the written leaf).
def g4_wf(n: Nat, s: Store.Store) -> Bool:
  match n:
    case 0n: True{}
    case 1n+ +p:
      match s:
        case Store.STip{}: True{}
        case Store.SLeaf{+key, +val}: False{}
        case Store.SNode{+lo, +hi}: Bool.and(g4_wf(p, lo), g4_wf(p, hi))

def g4_wf_tip(n: Nat) -> {g4_wf(n, Store.STip{}) == True{} : Bool}:
  match n:
    case 0n: {==}
    case 1n+ +p: {==}

# `set_w` preserves well-formedness (the malformed intermediate-`SLeaf` case is
# discharged by contradiction).
def g4_set_w_wf(n: Nat, w: Word(n), s: Store.Store, +k: U32, +v: List<&2, U32>,
    +h: {g4_wf(n, s) == True{} : Bool})
  -> {g4_wf(n, Store.set_w(n, w, s, k, v)) == True{} : Bool}:
  match n:
    case 0n: {==}
    case 1n+ +p:
      match w:
        case WCon{+head, +tail}:
          match head:
            case False{}:
              match s:
                case Store.STip{}:
                  g4_and_intro(g4_wf(p, Store.set_w(p, tail, Store.STip{}, k, v)), g4_wf(p, Store.STip{}),
                    g4_set_w_wf(p, tail, Store.STip{}, k, v, g4_wf_tip(p)), g4_wf_tip(p))
                case Store.SLeaf{+key, +val}:
                  h
                case Store.SNode{+lo, +hi}:
                  +hlo = g4_and_true_left(g4_wf(p, lo), g4_wf(p, hi), h)
                  +hhi = g4_and_true_right(g4_wf(p, lo), g4_wf(p, hi), h)
                  g4_and_intro(g4_wf(p, Store.set_w(p, tail, lo, k, v)), g4_wf(p, hi),
                    g4_set_w_wf(p, tail, lo, k, v, hlo), hhi)
            case True{}:
              match s:
                case Store.STip{}:
                  g4_and_intro(g4_wf(p, Store.STip{}), g4_wf(p, Store.set_w(p, tail, Store.STip{}, k, v)),
                    g4_wf_tip(p), g4_set_w_wf(p, tail, Store.STip{}, k, v, g4_wf_tip(p)))
                case Store.SLeaf{+key, +val}:
                  h
                case Store.SNode{+lo, +hi}:
                  +hlo = g4_and_true_left(g4_wf(p, lo), g4_wf(p, hi), h)
                  +hhi = g4_and_true_right(g4_wf(p, lo), g4_wf(p, hi), h)
                  g4_and_intro(g4_wf(p, lo), g4_wf(p, Store.set_w(p, tail, hi, k, v)),
                    hlo, g4_set_w_wf(p, tail, hi, k, v, hhi))

# ------------------------------------------- read-after-write at the same key
# For a well-formed store, writing `k` and reading it back at the same key path
# returns exactly `v`. The well-formedness hypothesis is what rules out the
# intermediate-`SLeaf` overwrite.
def g4_get_set_same(n: Nat, w: Word(n), s: Store.Store, +k: U32, +v: List<&2, U32>,
    +hwf: {g4_wf(n, s) == True{} : Bool})
  -> {Store.get_w(n, w, Store.set_w(n, w, s, k, v), k) == Some{v} : Maybe<&2, List<&2, U32>>}:
  match n:
    case 0n:
      +hr = g4_is_eq_refl(k)
      Equal.cong(Bool, Maybe<&2, List<&2, U32>>, b => Store.maybe_if(b, v), U32.is_eq(k, k), True{}, hr)
    case 1n+ +p:
      match w:
        case WCon{+head, +tail}:
          match head:
            case False{}:
              match s:
                case Store.STip{}:
                  g4_get_set_same(p, tail, Store.STip{}, k, v, g4_wf_tip(p))
                case Store.SLeaf{+key, +val}:
                  g4_absurd(Maybe<&2, List<&2, U32>>, None{}, Some{v}, hwf)
                case Store.SNode{+lo, +hi}:
                  +hlo = g4_and_true_left(g4_wf(p, lo), g4_wf(p, hi), hwf)
                  g4_get_set_same(p, tail, lo, k, v, hlo)
            case True{}:
              match s:
                case Store.STip{}:
                  g4_get_set_same(p, tail, Store.STip{}, k, v, g4_wf_tip(p))
                case Store.SLeaf{+key, +val}:
                  g4_absurd(Maybe<&2, List<&2, U32>>, None{}, Some{v}, hwf)
                case Store.SNode{+lo, +hi}:
                  +hhi = g4_and_true_right(g4_wf(p, lo), g4_wf(p, hi), hwf)
                  g4_get_set_same(p, tail, hi, k, v, hhi)

# Full-depth wrappers: `Store.set`/`get` are `set_w`/`get_w` at `n = 32`.
def g4_get_set_same32(+s: Store.Store, +k: U32, +v: List<&2, U32>,
    +hwf: {g4_wf(32n, s) == True{} : Bool})
  -> {Store.get(Store.set(s, k, v), k) == Some{v} : Maybe<&2, List<&2, U32>>}:
  match k:
    case U32{w}:
      g4_get_set_same(32n, w, s, k, v, hwf)

def g4_set_wf32(+s: Store.Store, +k: U32, +v: List<&2, U32>,
    +h: {g4_wf(32n, s) == True{} : Bool})
  -> {g4_wf(32n, Store.set(s, k, v)) == True{} : Bool}:
  match k:
    case U32{w}:
      g4_set_w_wf(32n, w, s, k, v, h)

# ------------------------------------------ read-after-write at another key
# Structural bit-path agreement. `g4_same(n,a,b)` is `True` exactly when the two
# `n`-bit words agree; `g4_same_eq_cmp` pins it to `Cmp.is_eq(Word.cmp(n,a,b))`,
# so `U32.is_eq(k,k') == False` is the same as "the key paths diverge".
def g4_same(n: Nat, a: Word(n), b: Word(n)) -> Bool:
  match n:
    case 0n: True{}
    case 1n+ +p:
      match a:
        case WCon{ah, +at}:
          match ah:
            case False{}:
              match b:
                case WCon{bh, +bt}:
                  match bh:
                    case False{}: g4_same(p, at, bt)
                    case True{}: False{}
            case True{}:
              match b:
                case WCon{bh, +bt}:
                  match bh:
                    case False{}: False{}
                    case True{}: g4_same(p, at, bt)

def g4_cmp_fin_ff(t: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, False{}, t)) == Cmp.is_eq(t) : Bool}:
  match t:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

def g4_cmp_fin_ft(t: Cmp) -> {Cmp.is_eq(Word.cmp.fin(False{}, True{}, t)) == False{} : Bool}:
  match t:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

def g4_cmp_fin_tf(t: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, False{}, t)) == False{} : Bool}:
  match t:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

def g4_cmp_fin_tt(t: Cmp) -> {Cmp.is_eq(Word.cmp.fin(True{}, True{}, t)) == Cmp.is_eq(t) : Bool}:
  match t:
    case LT{}: {==}
    case EQ{}: {==}
    case GT{}: {==}

def g4_same_eq_cmp(n: Nat, a: Word(n), b: Word(n)) -> {g4_same(n, a, b) == Cmp.is_eq(Word.cmp(n, a, b)) : Bool}:
  match n:
    case 0n:
      match a:
        case WNil{}:
          match b:
            case WNil{}: {==}
    case 1n+ +p:
      match a:
        case WCon{ah, +at}:
          match ah:
            case False{}:
              match b:
                case WCon{bh, +bt}:
                  match bh:
                    case False{}:
                      Equal.trans(Bool, g4_same(p, at, bt), Cmp.is_eq(Word.cmp(p, at, bt)),
                        Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))),
                        g4_same_eq_cmp(p, at, bt),
                        Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, False{}, Word.cmp(p, at, bt))),
                          Cmp.is_eq(Word.cmp(p, at, bt)), g4_cmp_fin_ff(Word.cmp(p, at, bt))))
                    case True{}:
                      Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(False{}, True{}, Word.cmp(p, at, bt))), False{},
                        g4_cmp_fin_ft(Word.cmp(p, at, bt)))
            case True{}:
              match b:
                case WCon{bh, +bt}:
                  match bh:
                    case False{}:
                      Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, False{}, Word.cmp(p, at, bt))), False{},
                        g4_cmp_fin_tf(Word.cmp(p, at, bt)))
                    case True{}:
                      Equal.trans(Bool, g4_same(p, at, bt), Cmp.is_eq(Word.cmp(p, at, bt)),
                        Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
                        g4_same_eq_cmp(p, at, bt),
                        Equal.sym(Bool, Cmp.is_eq(Word.cmp.fin(True{}, True{}, Word.cmp(p, at, bt))),
                          Cmp.is_eq(Word.cmp(p, at, bt)), g4_cmp_fin_tt(Word.cmp(p, at, bt))))

# Reading an empty subtree is always `None` (the diverging-path case needs it
# when the write lands on the *other* child of a freshly split `STip`).
def g4_get_w_tip(n: Nat, w: Word(n), +k: U32) -> {Store.get_w(n, w, Store.STip{}, k) == None{} : Maybe<&2, List<&2, U32>>}:
  match n:
    case 0n:
      match w:
        case WNil{}: {==}
    case 1n+ +p:
      match w:
        case WCon{h, +t}:
          match h:
            case False{}: {==}
            case True{}: {==}

# A write at one path is invisible to a read at a diverging path. No
# well-formedness is needed: the two walks never meet at a leaf.
def g4_get_set_other(n: Nat, w: Word(n), w2: Word(n), +s: Store.Store, +k: U32, +k2: U32,
    +v: List<&2, U32>, +hd: {g4_same(n, w, w2) == False{} : Bool})
  -> {Store.get_w(n, w2, Store.set_w(n, w, s, k, v), k2) == Store.get_w(n, w2, s, k2) : Maybe<&2, List<&2, U32>>}:
  match n:
    case 0n:
      match w:
        case WNil{}:
          match w2:
            case WNil{}:
              g4_absurd(Maybe<&2, List<&2, U32>>, Store.get_w(0n, WNil{}, Store.set_w(0n, WNil{}, s, k, v), k2),
                Store.get_w(0n, WNil{}, s, k2), Equal.sym(Bool, True{}, False{}, hd))
    case 1n+ +p:
      match w:
        case WCon{ah, +at}:
          match ah:
            case False{}:
              match w2:
                case WCon{bh, +bt}:
                  match bh:
                    case False{}:
                      match s:
                        case Store.STip{}:
                          Equal.trans(Maybe<&2, List<&2, U32>>,
                            Store.get_w(p, bt, Store.set_w(p, at, Store.STip{}, k, v), k2),
                            Store.get_w(p, bt, Store.STip{}, k2),
                            None{},
                            g4_get_set_other(p, at, bt, Store.STip{}, k, k2, v, hd),
                            g4_get_w_tip(p, bt, k2))
                        case Store.SLeaf{+key, +val}: {==}
                        case Store.SNode{+lo, +hi}:
                          g4_get_set_other(p, at, bt, lo, k, k2, v, hd)
                    case True{}:
                      match s:
                        case Store.STip{}: g4_get_w_tip(p, bt, k2)
                        case Store.SLeaf{+key, +val}: {==}
                        case Store.SNode{+lo, +hi}: {==}
            case True{}:
              match w2:
                case WCon{bh, +bt}:
                  match bh:
                    case False{}:
                      match s:
                        case Store.STip{}: g4_get_w_tip(p, bt, k2)
                        case Store.SLeaf{+key, +val}: {==}
                        case Store.SNode{+lo, +hi}: {==}
                    case True{}:
                      match s:
                        case Store.STip{}:
                          Equal.trans(Maybe<&2, List<&2, U32>>,
                            Store.get_w(p, bt, Store.set_w(p, at, Store.STip{}, k, v), k2),
                            Store.get_w(p, bt, Store.STip{}, k2),
                            None{},
                            g4_get_set_other(p, at, bt, Store.STip{}, k, k2, v, hd),
                            g4_get_w_tip(p, bt, k2))
                        case Store.SLeaf{+key, +val}: {==}
                        case Store.SNode{+lo, +hi}:
                          g4_get_set_other(p, at, bt, hi, k, k2, v, hd)

# Full-depth wrapper: distinct `U32` keys have diverging `Word(32)` paths (via
# `g4_same_eq_cmp`), so a write is invisible to a read at any other key.
def g4_get_set_other32(+s: Store.Store, +k: U32, +k2: U32, +v: List<&2, U32>,
    +hne: {U32.is_eq(k, k2) == False{} : Bool})
  -> {Store.get(Store.set(s, k, v), k2) == Store.get(s, k2) : Maybe<&2, List<&2, U32>>}:
  match k:
    case U32{w}:
      match k2:
        case U32{w2}:
          +hd = Equal.trans(Bool, g4_same(32n, w, w2), Cmp.is_eq(Word.cmp(32n, w, w2)), False{},
            g4_same_eq_cmp(32n, w, w2), hne)
          g4_get_set_other(32n, w, w2, s, k, k2, v, hd)

# ============================================================================
# Per-key assembly steps toward the 64-key `evict`/`assemble` fold.
#
# `Store.assemble_cells_sel` reads its `Maybe` argument (the store's entry at a
# key) and writes the chunk. The two laws below are the fold's per-key moves:
# a key that was just set assembles from its stored chunk, and a key that was set
# at *another* key is untouched. `g4_keep_cells_drop`/`_keep` are the
# `evict_key_sel` accumulator primitives at the store-entry level.
#
# The full fold (`assemble(evict s) == assemble s` over the 64 keys) still needs
# the invariant thread through `Store.evict_key_sel`'s concrete recursion -- in
# particular the dropped (regenerable) key's `None`-branch equality, which
# normalises `chunk_list_sel` and is the barrier recorded in the header.
# ============================================================================

# Accepted/kept key: after a same-key `set` on a well-formed store the key's
# assembly equals assembling the explicit chunk (the `Some` branch).
def g4_assemble_cells_same(
  +sel: Bool, +k: U32, +s: Store.Store, +v: List<&2, U32>, world: Array<U32>,
  +hwf: {g4_wf(32n, s) == True{} : Bool}
) -> {Store.assemble_cells_sel(sel, Store.get(Store.set(s, k, v), k), k, world) == Store.assemble_cells_sel(sel, Some{v}, k, world) : Array<U32>}:
  Equal.cong(Maybe<&2, List<&2, U32>>, Array<U32>,
    m => Store.assemble_cells_sel(sel, m, k, world),
    Store.get(Store.set(s, k, v), k), Some{v}, g4_get_set_same32(s, k, v, hwf))

# Non-interference: a `set` at another key is invisible to this key's assembly
# (the `assemble_cells_sel` argument is unchanged by `g4_get_set_other32`).
def g4_assemble_cells_other(
  +sel: Bool, +k1: U32, +k2: U32, +s: Store.Store, +v: List<&2, U32>, world: Array<U32>,
  +hne: {U32.is_eq(k2, k1) == False{} : Bool}
) -> {Store.assemble_cells_sel(sel, Store.get(Store.set(s, k2, v), k1), k1, world) == Store.assemble_cells_sel(sel, Store.get(s, k1), k1, world) : Array<U32>}:
  Equal.cong(Maybe<&2, List<&2, U32>>, Array<U32>,
    m => Store.assemble_cells_sel(sel, m, k1, world),
    Store.get(Store.set(s, k2, v), k1), Store.get(s, k1), g4_get_set_other32(s, k2, k1, v, hne))

# `evict_key_sel` accumulator primitives: a dropped key leaves the accumulator
# untouched; a kept key sets it and reads back at that key.
def g4_keep_cells_drop(+store: Store.Store, +k: U32, +cells: List<&2, U32>)
  -> {Store.get(Store.keep_cells(store, k, cells, True{}), k) == Store.get(store, k) : Maybe<&2, List<&2, U32>>}:
  {==}

def g4_keep_cells_keep(+store: Store.Store, +k: U32, +cells: List<&2, U32>,
    +hwf: {g4_wf(32n, store) == True{} : Bool})
  -> {Store.get(Store.keep_cells(store, k, cells, False{}), k) == Some{cells} : Maybe<&2, List<&2, U32>>}:
  g4_get_set_same32(store, k, cells, hwf)
