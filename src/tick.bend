import Base
import ./refine.bend as R
import ./writepot.bend as W
import ./settle.bend as S
import ./nat.bend as NatL
import ./ops.bend as Ops
import ./grid.bend as Grid
import ./cell.bend as Cell
import ./word.bend as WR

# The packed-index word at position i of a PT tree, following the same
# `is_lt(i, shr n)` walk as swap_m / chg_m.
def tget(t: R.PT, n: U32, +i: U32) -> U32:
  match t:
    case R.PL{x}:
      x
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      Bool.pick(U32, U32.is_lt(i, h), tget(xs, h, i), tget(ys, h, U32.sub(i, h)))

# ------------------------------------------------------------------ support
# A support write changes only the support field: the changed leaf's old and
# new potentials coincide, so Phi is preserved.

def chg_support_if(
  +xs: R.PT, +ys: R.PT, +base: U32, +h: U32, +i: U32, +s: U32, +z: Bool,
  ihx: {R.nfst(R.chg_m(xs, base, h, i, Ops.set_support(tget(xs, h, i), s))) == R.nsnd(R.chg_m(xs, base, h, i, Ops.set_support(tget(xs, h, i), s))) : Nat},
  ihy: {R.nfst(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Ops.set_support(tget(ys, h, U32.sub(i, h)), s))) == R.nsnd(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Ops.set_support(tget(ys, h, U32.sub(i, h)), s))) : Nat}
) -> {R.nfst(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, Ops.set_support(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h))), s)),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Ops.set_support(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h))), s))))
      == R.nsnd(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, Ops.set_support(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h))), s)),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Ops.set_support(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h))), s))))
      : Nat}:
  match z:
    case True{}:
      ihx
    case False{}:
      ihy

def chg_support(t: R.PT, +base: U32, +n: U32, +i: U32, +s: U32)
  -> {R.nfst(R.chg_m(t, base, n, i, Ops.set_support(tget(t, n, i), s))) == R.nsnd(R.chg_m(t, base, n, i, Ops.set_support(tget(t, n, i), s))) : Nat}:
  match t:
    case R.PL{x}:
      Equal.sym(Nat,
        S.pot_at(Ops.set_support(x, s), base),
        S.pot_at(x, base),
        W.pot_set_support(x, s, base))
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      chg_support_if(xs, ys, base, h, i, s, z,
        chg_support(xs, base, h, i, s),
        chg_support(ys, U32.add(base, h), h, U32.sub(i, h), s))

# Phi is preserved by a support write at any index of the array.
def array_support_write(+t: R.PT, +base: U32, +n: U32, +i: U32, +s: U32)
  -> {S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, Ops.set_support(tget(t, n, i), s))), base, n)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  +v = Ops.set_support(tget(t, n, i), s)
  +after = S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), base, n))
  +before = S.suml(S.to_pots(R.pack(t), base, n))
  +w1 = R.nfst(R.chg_m(t, base, n, i, v))
  +w2 = R.nsnd(R.chg_m(t, base, n, i, v))
  +eq = chg_support(t, base, n, i, s)
  +dec = R.array_swap_decreases(t, base, n, i, v)
  +e1 = Equal.cong(Nat, Nat, x => Nat.add(after, x), w2, w1, Equal.sym(Nat, w1, w2, eq))
  +e2 = Equal.trans(Nat, Nat.add(after, w2), Nat.add(after, w1), Nat.add(before, w2), e1, dec)
  NatL.n_add_cancel_right(after, before, w2, e2)

# ------------------------------------------------------------------ crumble
# A rock crumble (material 3 -> 4) lowers the leaf's potential by 50 * L where
# L is the leaf's level (the bedrock floor guarantees L >= 1 in the engine).

def crush_gap(t: R.PT, +base: U32, +n: U32, +i: U32) -> Nat:
  match t:
    case R.PL{x}:
      Nat.mul(50n, U32.to_nat(Grid.iy(base)))
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      Bool.pick(Nat, z,
        crush_gap(xs, base, h, i),
        crush_gap(ys, U32.add(base, h), h, U32.sub(i, h)))

# The Φ slack of a guarded crush at index i: the rock gap when the target is
# rock, and 0 otherwise (a non-rock "crush" writes the value back unchanged).
def guard_gap(+t: R.PT, +base: U32, +n: U32, +i: U32) -> Nat:
  Bool.pick(Nat, U32.is_eq(Cell.material(tget(t, n, i)), 3), crush_gap(t, base, n, i), 0n)

def chg_crush_if(
  +xs: R.PT, +ys: R.PT, +base: U32, +h: U32, +i: U32, +z: Bool,
  hm: {Cell.material(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h)))) == 3 : U32},
  ihx: ({Cell.material(tget(xs, h, i)) == 3 : U32} -> {Nat.add(R.nsnd(R.chg_m(xs, base, h, i, Ops.crush_word(tget(xs, h, i)))), crush_gap(xs, base, h, i)) == R.nfst(R.chg_m(xs, base, h, i, Ops.crush_word(tget(xs, h, i)))) : Nat}),
  ihy: ({Cell.material(tget(ys, h, U32.sub(i, h))) == 3 : U32} -> {Nat.add(R.nsnd(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Ops.crush_word(tget(ys, h, U32.sub(i, h))))), crush_gap(ys, U32.add(base, h), h, U32.sub(i, h))) == R.nfst(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Ops.crush_word(tget(ys, h, U32.sub(i, h))))) : Nat})
) -> {Nat.add(R.nsnd(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, Ops.crush_word(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h))))),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Ops.crush_word(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h))))))),
      Bool.pick(Nat, z, crush_gap(xs, base, h, i), crush_gap(ys, U32.add(base, h), h, U32.sub(i, h))))
      == R.nfst(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, Ops.crush_word(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h))))),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Ops.crush_word(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h)))))))
      : Nat}:
  match z:
    case True{}:
      ihx(hm)
    case False{}:
      ihy(hm)

def chg_crush_rock(t: R.PT, +base: U32, +n: U32, +i: U32, hm: {Cell.material(tget(t, n, i)) == 3 : U32})
  -> {Nat.add(R.nsnd(R.chg_m(t, base, n, i, Ops.crush_word(tget(t, n, i)))), crush_gap(t, base, n, i)) == R.nfst(R.chg_m(t, base, n, i, Ops.crush_word(tget(t, n, i)))) : Nat}:
  match t:
    case R.PL{x}:
      W.pot_crush_rock(x, base, hm)
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      chg_crush_if(xs, ys, base, h, i, z, hm,
        hx => chg_crush_rock(xs, base, h, i, hx),
        hy => chg_crush_rock(ys, U32.add(base, h), h, U32.sub(i, h), hy))

def array_crumble_lowers(+t: R.PT, +base: U32, +n: U32, +i: U32, +hm: {Cell.material(tget(t, n, i)) == 3 : U32})
  -> {Nat.add(S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, Ops.crush_word(tget(t, n, i)))), base, n)), crush_gap(t, base, n, i)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  +v = Ops.crush_word(tget(t, n, i))
  +after = S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), base, n))
  +before = S.suml(S.to_pots(R.pack(t), base, n))
  +g = crush_gap(t, base, n, i)
  +w1 = R.nfst(R.chg_m(t, base, n, i, v))
  +w2 = R.nsnd(R.chg_m(t, base, n, i, v))
  +chg = chg_crush_rock(t, base, n, i, hm)
  +dec = R.array_swap_decreases(t, base, n, i, v)
  +e1 = Equal.cong(Nat, Nat, x => Nat.add(after, x), Nat.add(w2, g), w1, chg)
  +e2 = Equal.trans(Nat, Nat.add(after, Nat.add(w2, g)), Nat.add(after, w1), Nat.add(before, w2), e1, dec)
  +mid = Equal.trans(Nat, Nat.add(after, Nat.add(w2, g)), Nat.add(after, Nat.add(g, w2)), Nat.add(Nat.add(after, g), w2),
    Equal.cong(Nat, Nat, x => Nat.add(after, x), Nat.add(w2, g), Nat.add(g, w2), NatL.n_add_comm(w2, g)),
    Equal.sym(Nat, Nat.add(Nat.add(after, g), w2), Nat.add(after, Nat.add(g, w2)), NatL.n_add_assoc(after, g, w2)))
  +e7 = Equal.trans(Nat, Nat.add(Nat.add(after, g), w2), Nat.add(after, Nat.add(w2, g)), Nat.add(before, w2),
    Equal.sym(Nat, Nat.add(after, Nat.add(w2, g)), Nat.add(Nat.add(after, g), w2), mid), e2)
  NatL.n_add_cancel_right(Nat.add(after, g), before, w2, e7)

# ------------------------------------------------------------------ guarded crush
# A guarded crush (`Ops.crush_if_rock`) writes `crush_word(v)` when the target is
# rock and `v` unchanged otherwise. At the array level its Φ slack is exactly
# `guard_gap` (the rock gap, or 0), so it never raises Φ — this is the write-site
# theorem for both machinery crush sites (`Rules.step` sel 22, `Support.sup`
# sel 6) and the array-level closure of `G9`.

# Writing the current value back is the identity at the pot level.
def pots_write_same_if(
  +xs: R.PT, +ys: R.PT, +base: U32, +h: U32, +i: U32, +z: Bool,
  ihx: {R.pots_swap_m(xs, base, h, i, tget(xs, h, i)) == R.pots_m(xs, base, h) : +List<Nat>},
  ihy: {R.pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), tget(ys, h, U32.sub(i, h))) == R.pots_m(ys, U32.add(base, h), h) : +List<Nat>}
) -> {Bool.pick(List<&2, Nat>, z,
        S.app(R.pots_swap_m(xs, base, h, i, Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h)))), R.pots_m(ys, U32.add(base, h), h)),
        S.app(R.pots_m(xs, base, h), R.pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h))))))
     == S.app(R.pots_m(xs, base, h), R.pots_m(ys, U32.add(base, h), h)) : +List<Nat>}:
  match z:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>,
        x => S.app(x, R.pots_m(ys, U32.add(base, h), h)),
        R.pots_swap_m(xs, base, h, i, tget(xs, h, i)), R.pots_m(xs, base, h), ihx)
    case False{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>,
        x => S.app(R.pots_m(xs, base, h), x),
        R.pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), tget(ys, h, U32.sub(i, h))),
        R.pots_m(ys, U32.add(base, h), h), ihy)

def pots_write_same(t: R.PT, +base: U32, +n: U32, +i: U32)
  -> {R.pots_swap_m(t, base, n, i, tget(t, n, i)) == R.pots_m(t, base, n) : +List<Nat>}:
  match t:
    case R.PL{x}:
      {==}
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      pots_write_same_if(xs, ys, base, h, i, z,
        pots_write_same(xs, base, h, i),
        pots_write_same(ys, U32.add(base, h), h, U32.sub(i, h)))

def array_guarded_crush_lowers(
  +t: R.PT, +base: U32, +n: U32, +i: U32, +z: Bool,
  hz: {z == U32.is_eq(Cell.material(tget(t, n, i)), 3) : Bool}
) -> {Nat.add(S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i,
        Bool.pick(U32, z, Ops.crush_word(tget(t, n, i)), tget(t, n, i)))), base, n)),
      Bool.pick(Nat, z, crush_gap(t, base, n, i), 0n)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  match z:
    case True{}:
      array_crumble_lowers(t, base, n, i,
        WR.u32_cmp_eq(Cell.material(tget(t, n, i)), 3,
          Equal.sym(Bool, True{}, U32.is_eq(Cell.material(tget(t, n, i)), 3), hz)))
    case False{}:
      +after = S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, tget(t, n, i))), base, n))
      +before = S.suml(S.to_pots(R.pack(t), base, n))
      +s1 = Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
        S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, tget(t, n, i))), base, n),
        R.pots_swap_m(t, base, n, i, tget(t, n, i)),
        R.array_swap_pots(t, base, n, i, tget(t, n, i)))
      +s2 = Equal.trans(Nat, after, S.suml(R.pots_swap_m(t, base, n, i, tget(t, n, i))), S.suml(R.pots_m(t, base, n)),
        s1,
        Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
          R.pots_swap_m(t, base, n, i, tget(t, n, i)), R.pots_m(t, base, n),
          pots_write_same(t, base, n, i)))
      +s3 = Equal.trans(Nat, after, S.suml(R.pots_m(t, base, n)), before,
        s2,
        Equal.sym(Nat, before, S.suml(R.pots_m(t, base, n)),
          Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
            S.to_pots(R.pack(t), base, n), R.pots_m(t, base, n), R.to_pots_pack(t, base, n))))
      Equal.trans(Nat, Nat.add(after, 0n), after, before, NatL.n_add_zero_right(after), s3)

def array_guarded_crush_lowers_auto(+t: R.PT, +base: U32, +n: U32, +i: U32)
  -> {Nat.add(S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i,
        Ops.crush_if_rock(tget(t, n, i)))), base, n)),
      guard_gap(t, base, n, i)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  array_guarded_crush_lowers(t, base, n, i, U32.is_eq(Cell.material(tget(t, n, i)), 3), {==})

# ------------------------------------------------------------------ wake / activate
# `Ops.wake` only writes `Cell.activate` (bit 11), which preserves the material
# field and therefore `pot_at`. The array-level write law mirrors
# `array_support_write`; the `wake_*_m` mirrors and their preservation lemmas
# compose it along the three nested neighbor loops, for the `Support.sup` mirror.

def chg_activate_if(
  +xs: R.PT, +ys: R.PT, +base: U32, +h: U32, +i: U32, +z: Bool,
  ihx: {R.nfst(R.chg_m(xs, base, h, i, Cell.activate(tget(xs, h, i)))) == R.nsnd(R.chg_m(xs, base, h, i, Cell.activate(tget(xs, h, i)))) : Nat},
  ihy: {R.nfst(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Cell.activate(tget(ys, h, U32.sub(i, h))))) == R.nsnd(R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Cell.activate(tget(ys, h, U32.sub(i, h))))) : Nat}
) -> {R.nfst(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, Cell.activate(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h))))),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Cell.activate(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h)))))))
      == R.nsnd(Bool.pick(Nat & Nat, z,
        R.chg_m(xs, base, h, i, Cell.activate(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h))))),
        R.chg_m(ys, U32.add(base, h), h, U32.sub(i, h), Cell.activate(Bool.pick(U32, z, tget(xs, h, i), tget(ys, h, U32.sub(i, h)))))))
      : Nat}:
  match z:
    case True{}:
      ihx
    case False{}:
      ihy

def chg_activate(t: R.PT, +base: U32, +n: U32, +i: U32)
  -> {R.nfst(R.chg_m(t, base, n, i, Cell.activate(tget(t, n, i)))) == R.nsnd(R.chg_m(t, base, n, i, Cell.activate(tget(t, n, i)))) : Nat}:
  match t:
    case R.PL{x}:
      Equal.sym(Nat, S.pot_at(Cell.activate(x), base), S.pot_at(x, base), W.pot_or_hi(x, base))
    case R.PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      chg_activate_if(xs, ys, base, h, i, z,
        chg_activate(xs, base, h, i),
        chg_activate(ys, U32.add(base, h), h, U32.sub(i, h)))

def array_activate_write(+t: R.PT, +base: U32, +n: U32, +i: U32)
  -> {S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, Cell.activate(tget(t, n, i)))), base, n)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  +v = Cell.activate(tget(t, n, i))
  +after = S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), base, n))
  +before = S.suml(S.to_pots(R.pack(t), base, n))
  +w1 = R.nfst(R.chg_m(t, base, n, i, v))
  +w2 = R.nsnd(R.chg_m(t, base, n, i, v))
  +eq = chg_activate(t, base, n, i)
  +dec = R.array_swap_decreases(t, base, n, i, v)
  +e1 = Equal.cong(Nat, Nat, x => Nat.add(after, x), w2, w1, Equal.sym(Nat, w1, w2, eq))
  +e2 = Equal.trans(Nat, Nat.add(after, w2), Nat.add(after, w1), Nat.add(before, w2), e1, dec)
  NatL.n_add_cancel_right(after, before, w2, e2)

# Bridge `pack(swap_m(..))` to `Array.swap.go(..)`, so the array laws apply to
# the `PT` mirror's writes.
def to_pots_swap_pack(+t: R.PT, +base: U32, +n: U32, +j: U32, +v: U32)
  -> {S.to_pots(R.pack(R.swap_m(t, n, j, v)), base, n) == S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, j, v)), base, n) : +List<Nat>}:
  Equal.cong(Array<U32>, +List<Nat>, y => S.to_pots(y, base, n),
    R.pack(R.swap_m(t, n, j, v)),
    R.afst(Array.swap.go(U32, R.pack(t), n, j, v)),
    Equal.trans(Array<U32>,
      R.pack(R.swap_m(t, n, j, v)),
      R.pack(R.unpack(R.afst(Array.swap.go(U32, R.pack(t), n, j, v)))),
      R.afst(Array.swap.go(U32, R.pack(t), n, j, v)),
      Equal.sym(Array<U32>,
        R.pack(R.unpack(R.afst(Array.swap.go(U32, R.pack(t), n, j, v)))),
        R.pack(R.swap_m(t, n, j, v)),
        Equal.cong(R.PT, Array<U32>, x => R.pack(x),
          R.unpack(R.afst(Array.swap.go(U32, R.pack(t), n, j, v))),
          R.swap_m(t, n, j, v),
          R.swap_ref(t, n, j, v))),
      R.pack_unpack(R.afst(Array.swap.go(U32, R.pack(t), n, j, v)))))

def wake_x_m(fuel: Nat, +dx: U32, +dy: U32, +dz: U32, +i: U32, +t: R.PT, +n: U32) -> R.PT:
  match fuel:
    case 0n:
      t
    case 1n+p:
      +j = Grid.neighbor(i, U32.sub(dx, 1), U32.sub(dy, 1), U32.sub(dz, 1))
      t2 = R.swap_m(t, n, j, Cell.activate(tget(t, n, j)))
      wake_x_m(p, U32.add(dx, 1), dy, dz, i, t2, n)

def wake_x_m_preserves(fuel: Nat, +dx: U32, +dy: U32, +dz: U32, +i: U32, +t: R.PT, +n: U32, +base: U32)
  -> {S.suml(S.to_pots(R.pack(wake_x_m(fuel, dx, dy, dz, i, t, n)), base, n)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      +j = Grid.neighbor(i, U32.sub(dx, 1), U32.sub(dy, 1), U32.sub(dz, 1))
      +v = Cell.activate(tget(t, n, j))
      +t2 = R.swap_m(t, n, j, v)
      +e0 = to_pots_swap_pack(t, base, n, j, v)
      +e1 = Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
        S.to_pots(R.pack(t2), base, n),
        S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, j, v)), base, n), e0)
      +e2 = Equal.trans(Nat, S.suml(S.to_pots(R.pack(t2), base, n)),
        S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, j, Cell.activate(tget(t, n, j)))), base, n)),
        S.suml(S.to_pots(R.pack(t), base, n)),
        e1, array_activate_write(t, base, n, j))
      +ih = wake_x_m_preserves(p, U32.add(dx, 1), dy, dz, i, t2, n, base)
      Equal.trans(Nat,
        S.suml(S.to_pots(R.pack(wake_x_m(p, U32.add(dx, 1), dy, dz, i, t2, n)), base, n)),
        S.suml(S.to_pots(R.pack(t2), base, n)),
        S.suml(S.to_pots(R.pack(t), base, n)),
        ih, e2)

def wake_y_m(fuel: Nat, +dy: U32, +dz: U32, +i: U32, +t: R.PT, +n: U32) -> R.PT:
  match fuel:
    case 0n:
      t
    case 1n+p:
      t2 = wake_x_m(U32.to_nat(3), 0, dy, dz, i, t, n)
      wake_y_m(p, U32.add(dy, 1), dz, i, t2, n)

def wake_y_m_preserves(fuel: Nat, +dy: U32, +dz: U32, +i: U32, +t: R.PT, +n: U32, +base: U32)
  -> {S.suml(S.to_pots(R.pack(wake_y_m(fuel, dy, dz, i, t, n)), base, n)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      +t2 = wake_x_m(U32.to_nat(3), 0, dy, dz, i, t, n)
      +e2 = wake_x_m_preserves(U32.to_nat(3), 0, dy, dz, i, t, n, base)
      +ih = wake_y_m_preserves(p, U32.add(dy, 1), dz, i, t2, n, base)
      Equal.trans(Nat,
        S.suml(S.to_pots(R.pack(wake_y_m(p, U32.add(dy, 1), dz, i, t2, n)), base, n)),
        S.suml(S.to_pots(R.pack(t2), base, n)),
        S.suml(S.to_pots(R.pack(t), base, n)),
        ih, e2)

def wake_z_m(fuel: Nat, +dz: U32, +i: U32, +t: R.PT, +n: U32) -> R.PT:
  match fuel:
    case 0n:
      t
    case 1n+p:
      t2 = wake_y_m(U32.to_nat(3), 0, dz, i, t, n)
      wake_z_m(p, U32.add(dz, 1), i, t2, n)

def wake_z_m_preserves(fuel: Nat, +dz: U32, +i: U32, +t: R.PT, +n: U32, +base: U32)
  -> {S.suml(S.to_pots(R.pack(wake_z_m(fuel, dz, i, t, n)), base, n)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      +t2 = wake_y_m(U32.to_nat(3), 0, dz, i, t, n)
      +e2 = wake_y_m_preserves(U32.to_nat(3), 0, dz, i, t, n, base)
      +ih = wake_z_m_preserves(p, U32.add(dz, 1), i, t2, n, base)
      Equal.trans(Nat,
        S.suml(S.to_pots(R.pack(wake_z_m(p, U32.add(dz, 1), i, t2, n)), base, n)),
        S.suml(S.to_pots(R.pack(t2), base, n)),
        S.suml(S.to_pots(R.pack(t), base, n)),
        ih, e2)

def wake_m(+i: U32, +t: R.PT, +n: U32) -> R.PT:
  wake_z_m(U32.to_nat(3), 0, i, t, n)

# ------------------------------------------------------------------ sup mirror
# `Support.sup` mirrored on `PT` (G10). The engine matches on a numeric selector,
# which is opaque in a proof, so the mirror uses a datatype selector (`SupSel`);
# the `SupSel` -> numeric mapping is the `G5` refinement, by inspection. The
# mirror carries the running Φ gap: `set_support` adds 0, the guarded crush at
# sel 6 adds `guard_gap`. The wake fuel is threaded as an abstract `Nat` (A.45:
# a concrete fuel inside a proposition unrolls into a normalisation cliff); the
# top-level `sup_pass_m` instantiates it at 3.

type SupSel is Data:
  S0{}
  S1{}
  S2{}
  S3{}
  S4{}
  S5{}
  S6{}
  S7{}
  S8{}
  S9{}
  S10{}
  S11{}

def gap_swap_add(+A: Nat, +gr: Nat, +g: Nat) -> {Nat.add(A, Nat.add(g, gr)) == Nat.add(Nat.add(A, gr), g) : Nat}:
  Equal.trans(Nat,
    Nat.add(A, Nat.add(g, gr)),
    Nat.add(Nat.add(A, g), gr),
    Nat.add(Nat.add(A, gr), g),
    Equal.sym(Nat, Nat.add(Nat.add(A, g), gr), Nat.add(A, Nat.add(g, gr)), NatL.n_add_assoc(A, g, gr)),
    Equal.sym(Nat, Nat.add(Nat.add(A, gr), g), Nat.add(Nat.add(A, g), gr), S.swap_add(A, gr, g)))

# Φ of a mirror result: the pot sum of the tree plus the accumulated gap.
def sup_phi(r: R.PT & Nat, +base: U32, +n: U32) -> Nat:
  match r:
    case (t, g): Nat.add(S.suml(S.to_pots(R.pack(t), base, n)), g)

def sup_add_gap(r: R.PT & Nat, gap: Nat) -> R.PT & Nat:
  match r:
    case (t, g): (t, Nat.add(gap, g))

def sup_phi_add_gap(r: R.PT & Nat, +g: Nat, +base: U32, +n: U32)
  -> {sup_phi(sup_add_gap(r, g), base, n) == Nat.add(sup_phi(r, base, n), g) : Nat}:
  match r:
    case (t, gr):
      gap_swap_add(S.suml(S.to_pots(R.pack(t), base, n)), gr, g)

def sup_m(fuel: Nat, +t: R.PT, +gv: U32, +sel: SupSel, +i: U32, +gated: Bool, +n: U32, +wf: Nat, +base: U32) -> R.PT & Nat:
  match fuel:
    case 0n:
      (t, 0n)
    case 1n+p:
      match sel:
        case S0{}:
          +v = gv
          act = U32.is_ne(Cell.active(v), 0)
          okg = Bool.or(Bool.not(gated), act)
          coh = U32.is_ne(Cell.cohesion(v), 0)
          st = Cell.static(Cell.material(v))
          want = Bool.and(okg, Bool.and(coh, Bool.not(st)))
          sup_m(p, t, v, Bool.pick(SupSel, want, S1{}, S9{}), i, gated, n, wf, base)
        case S1{}:
          adj = Ops.adjacent_static(i)
          sup_m(p, t, gv, Bool.pick(SupSel, adj, S4{}, S5{}), i, gated, n, wf, base)
        case S2{}:
          +b = gv
          bcoh = U32.is_ne(Cell.cohesion(b), 0)
          bsup = U32.is_ne(Cell.support(b), 0)
          sup_m(p, t, b, Bool.pick(SupSel, Bool.and(bcoh, bsup), S3{}, S6{}), i, gated, n, wf, base)
        case S3{}:
          +sv = Cell.support(gv)
          +v = Ops.set_support(tget(t, n, i), sv)
          +t2 = R.swap_m(t, n, i, v)
          +q = tget(t2, n, i)
          sup_m(p, t2, q, S9{}, i, gated, n, wf, base)
        case S4{}:
          +v = Ops.set_support(tget(t, n, i), 31)
          +t2 = R.swap_m(t, n, i, v)
          +q = tget(t2, n, i)
          sup_m(p, t2, q, S9{}, i, gated, n, wf, base)
        case S5{}:
          +q = tget(t, n, Grid.below(i))
          sup_m(p, t, q, S2{}, i, gated, n, wf, base)
        case S6{}:
          +v = Ops.crush_if_rock(tget(t, n, i))
          +t2 = R.swap_m(t, n, i, v)
          +t3 = wake_z_m(wf, 0, i, t2, n)
          +q = tget(t3, n, i)
          rr = sup_m(p, t3, q, S9{}, i, gated, n, wf, base)
          sup_add_gap(rr, guard_gap(t, base, n, i))
        case S9{}:
          +ni = U32.add(i, 1)
          sup_m(p, t, gv, Bool.pick(SupSel, U32.is_eq(ni, 262144), S10{}, S11{}), i, gated, n, wf, base)
        case S10{}:
          (t, 0n)
        case S11{}:
          +ni = U32.add(i, 1)
          +q = tget(t, n, ni)
          sup_m(p, t, q, S0{}, ni, gated, n, wf, base)
        case S7{}:
          (t, 0n)
        case S8{}:
          (t, 0n)

# A support write at index `i` preserves Φ (sel 3/4 add no gap).
def sup_support_step(+t: R.PT, +base: U32, +n: U32, +i: U32, +sv: U32)
  -> {S.suml(S.to_pots(R.pack(R.swap_m(t, n, i, Ops.set_support(tget(t, n, i), sv))), base, n)) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  +v = Ops.set_support(tget(t, n, i), sv)
  +after = S.suml(S.to_pots(R.pack(R.swap_m(t, n, i, v)), base, n))
  +before = S.suml(S.to_pots(R.pack(t), base, n))
  +e0 = to_pots_swap_pack(t, base, n, i, v)
  +e1 = Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
    S.to_pots(R.pack(R.swap_m(t, n, i, v)), base, n),
    S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), base, n), e0)
  Equal.trans(Nat, after,
    S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), base, n)),
    before, e1, array_support_write(t, base, n, i, sv))

# A guarded crush + wake at index `i` lowers Φ by exactly `guard_gap` (sel 6).
def sup_crush_step(+t: R.PT, +base: U32, +n: U32, +i: U32, +wf: Nat)
  -> {Nat.add(S.suml(S.to_pots(R.pack(wake_z_m(wf, 0, i, R.swap_m(t, n, i, Ops.crush_if_rock(tget(t, n, i))), n)), base, n)),
           guard_gap(t, base, n, i))
      == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  +v = Ops.crush_if_rock(tget(t, n, i))
  +t2 = R.swap_m(t, n, i, v)
  +t3 = wake_z_m(wf, 0, i, t2, n)
  +g = guard_gap(t, base, n, i)
  +e0 = to_pots_swap_pack(t, base, n, i, v)
  +e1 = Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
    S.to_pots(R.pack(t2), base, n),
    S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), base, n), e0)
  +e3 = wake_z_m_preserves(wf, 0, i, t2, n, base)
  Equal.trans(Nat, Nat.add(S.suml(S.to_pots(R.pack(t3), base, n)), g),
    Nat.add(S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), base, n)), g),
    S.suml(S.to_pots(R.pack(t), base, n)),
    Equal.trans(Nat,
      Nat.add(S.suml(S.to_pots(R.pack(t3), base, n)), g),
      Nat.add(S.suml(S.to_pots(R.pack(t2), base, n)), g),
      Nat.add(S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), base, n)), g),
      Equal.cong(Nat, Nat, x => Nat.add(x, g),
        S.suml(S.to_pots(R.pack(t3), base, n)),
        S.suml(S.to_pots(R.pack(t2), base, n)), e3),
      Equal.cong(Nat, Nat, x => Nat.add(x, g),
        S.suml(S.to_pots(R.pack(t2), base, n)),
        S.suml(S.to_pots(R.afst(Array.swap.go(U32, R.pack(t), n, i, v)), base, n)), e1)),
    array_guarded_crush_lowers_auto(t, base, n, i))

# The fuel-loop mirror: composing the write primitives along `Support.sup`'s
# control flow preserves Φ up to the accumulated crush gap. Stated over an
# abstract fuel (all fuels), hence also the engine's `U32.to_nat(16777216)`.
def sup_m_preserves(+fuel: Nat, +t: R.PT, +gv: U32, +sel: SupSel, +i: U32, +gated: Bool, +n: U32, +wf: Nat, +base: U32)
  -> {sup_phi(sup_m(fuel, t, gv, sel, i, gated, n, wf, base), base, n) == S.suml(S.to_pots(R.pack(t), base, n)) : Nat}:
  match fuel:
    case 0n:
      NatL.n_add_zero_right(S.suml(S.to_pots(R.pack(t), base, n)))
    case 1n+p:
      match sel:
        case S0{}:
          +v = gv
          act = U32.is_ne(Cell.active(v), 0)
          okg = Bool.or(Bool.not(gated), act)
          coh = U32.is_ne(Cell.cohesion(v), 0)
          st = Cell.static(Cell.material(v))
          want = Bool.and(okg, Bool.and(coh, Bool.not(st)))
          sup_m_preserves(p, t, v, Bool.pick(SupSel, want, S1{}, S9{}), i, gated, n, wf, base)
        case S1{}:
          adj = Ops.adjacent_static(i)
          sup_m_preserves(p, t, gv, Bool.pick(SupSel, adj, S4{}, S5{}), i, gated, n, wf, base)
        case S2{}:
          +b = gv
          bcoh = U32.is_ne(Cell.cohesion(b), 0)
          bsup = U32.is_ne(Cell.support(b), 0)
          sup_m_preserves(p, t, b, Bool.pick(SupSel, Bool.and(bcoh, bsup), S3{}, S6{}), i, gated, n, wf, base)
        case S3{}:
          +sv = Cell.support(gv)
          +v = Ops.set_support(tget(t, n, i), sv)
          +t2 = R.swap_m(t, n, i, v)
          +q = tget(t2, n, i)
          +ih = sup_m_preserves(p, t2, q, S9{}, i, gated, n, wf, base)
          +st = sup_support_step(t, base, n, i, sv)
          Equal.trans(Nat,
            sup_phi(sup_m(p, t2, q, S9{}, i, gated, n, wf, base), base, n),
            S.suml(S.to_pots(R.pack(t2), base, n)),
            S.suml(S.to_pots(R.pack(t), base, n)),
            ih, st)
        case S4{}:
          +v = Ops.set_support(tget(t, n, i), 31)
          +t2 = R.swap_m(t, n, i, v)
          +q = tget(t2, n, i)
          +ih = sup_m_preserves(p, t2, q, S9{}, i, gated, n, wf, base)
          +st = sup_support_step(t, base, n, i, 31)
          Equal.trans(Nat,
            sup_phi(sup_m(p, t2, q, S9{}, i, gated, n, wf, base), base, n),
            S.suml(S.to_pots(R.pack(t2), base, n)),
            S.suml(S.to_pots(R.pack(t), base, n)),
            ih, st)
        case S5{}:
          +q = tget(t, n, Grid.below(i))
          sup_m_preserves(p, t, q, S2{}, i, gated, n, wf, base)
        case S6{}:
          +v = Ops.crush_if_rock(tget(t, n, i))
          +t2 = R.swap_m(t, n, i, v)
          +t3 = wake_z_m(wf, 0, i, t2, n)
          +q = tget(t3, n, i)
          +ih = sup_m_preserves(p, t3, q, S9{}, i, gated, n, wf, base)
          +st = sup_crush_step(t, base, n, i, wf)
          +g = guard_gap(t, base, n, i)
          Equal.trans(Nat,
            sup_phi(sup_add_gap(sup_m(p, t3, q, S9{}, i, gated, n, wf, base), g), base, n),
            Nat.add(sup_phi(sup_m(p, t3, q, S9{}, i, gated, n, wf, base), base, n), g),
            S.suml(S.to_pots(R.pack(t), base, n)),
            sup_phi_add_gap(sup_m(p, t3, q, S9{}, i, gated, n, wf, base), g, base, n),
            Equal.trans(Nat,
              Nat.add(sup_phi(sup_m(p, t3, q, S9{}, i, gated, n, wf, base), base, n), g),
              Nat.add(S.suml(S.to_pots(R.pack(t3), base, n)), g),
              S.suml(S.to_pots(R.pack(t), base, n)),
              Equal.cong(Nat, Nat, x => Nat.add(x, g),
                sup_phi(sup_m(p, t3, q, S9{}, i, gated, n, wf, base), base, n),
                S.suml(S.to_pots(R.pack(t3), base, n)), ih),
              st))
        case S9{}:
          +ni = U32.add(i, 1)
          sup_m_preserves(p, t, gv, Bool.pick(SupSel, U32.is_eq(ni, 262144), S10{}, S11{}), i, gated, n, wf, base)
        case S10{}:
          NatL.n_add_zero_right(S.suml(S.to_pots(R.pack(t), base, n)))
        case S11{}:
          +ni = U32.add(i, 1)
          +q = tget(t, n, ni)
          sup_m_preserves(p, t, q, S0{}, ni, gated, n, wf, base)
        case S7{}:
          NatL.n_add_zero_right(S.suml(S.to_pots(R.pack(t), base, n)))
        case S8{}:
          NatL.n_add_zero_right(S.suml(S.to_pots(R.pack(t), base, n)))

# The top-level binding: the mirror run over the engine's entry point
# (`pass_gated`'s `sup(16777216, get(world, 0), 0, 0, 0, gated)`), with the wake
# fuel instantiated at 3. The main fuel stays abstract (all-fuel theorem).
def sup_pass_m(fuel: Nat, +t: R.PT, +n: U32, +gated: Bool) -> R.PT & Nat:
  sup_m(fuel, t, tget(t, n, 0), S0{}, 0, gated, n, U32.to_nat(3), 0)
