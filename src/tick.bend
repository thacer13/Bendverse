import Base
import ./refine.bend as R
import ./writepot.bend as W
import ./settle.bend as S
import ./nat.bend as NatL
import ./ops.bend as Ops
import ./grid.bend as Grid
import ./cell.bend as Cell

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
