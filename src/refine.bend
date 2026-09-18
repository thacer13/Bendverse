import Base
import ./settle.bend as S
import ./nat.bend as NatL

# A non-linear (Data) model of Array<U32>'s ALeaf/ANode shape. Every array is
# definitionally pack(unpack(a)); PT lets the linearity checker see one owner.
type PT is Data:
  PL{value: U32}
  PN{xs: PT, ys: PT}

def pack(t: PT) -> Array<U32>:
  match t:
    case PL{x}: ALeaf{x}
    case PN{xs, ys}: ANode{pack(xs), pack(ys)}

def unpack(a: Array<U32>) -> PT:
  match a:
    case ALeaf{x}: PL{x}
    case ANode{xs, ys}: PN{unpack(xs), unpack(ys)}

def unpack_pack(t: PT) -> {unpack(pack(t)) == t : PT}:
  match t:
    case PL{x}:
      {==}
    case PN{+xs, +ys}:
      Equal.trans(PT,
        PN{unpack(pack(xs)), unpack(pack(ys))},
        PN{xs, unpack(pack(ys))},
        PN{xs, ys},
        Equal.cong(PT, PT, x => PN{x, unpack(pack(ys))}, unpack(pack(xs)), xs, unpack_pack(xs)),
        Equal.cong(PT, PT, y => PN{xs, y}, unpack(pack(ys)), ys, unpack_pack(ys)))

def pack_unpack(a: Array<U32>) -> {pack(unpack(a)) == a : Array<U32>}:
  match a:
    case ALeaf{x}:
      {==}
    case ANode{xs, ys}:
      Equal.trans(Array<U32>,
        ANode{pack(unpack(xs)), pack(unpack(ys))},
        ANode{xs, pack(unpack(ys))},
        ANode{xs, ys},
        Equal.cong(Array<U32>, Array<U32>, x => ANode{x, pack(unpack(ys))},
          pack(unpack(xs)), xs, pack_unpack(xs)),
        Equal.cong(Array<U32>, Array<U32>, y => ANode{xs, y},
          pack(unpack(ys)), ys, pack_unpack(ys)))

def afst(p: Array<U32> & U32) -> Array<U32>:
  match p:
    case (a, _): a

def nfst(p: Nat & Nat) -> Nat:
  match p:
    case (a, _): a

def nsnd(p: Nat & Nat) -> Nat:
  match p:
    case (_, b): b

# Base's Array.swap.lo/hi return pairs built by destructuring their third
# argument; these lemmas expose the first component so the pair reduces.
def lo_fst(ys: Array<U32>, r: Array<U32> & U32)
  -> {afst(Array.swap.lo(U32, ys, r)) == ANode{afst(r), ys} : Array<U32>}:
  match r:
    case (nxs, old): {==}

def hi_fst(xs: Array<U32>, r: Array<U32> & U32)
  -> {afst(Array.swap.hi(U32, xs, r)) == ANode{xs, afst(r)} : Array<U32>}:
  match r:
    case (nxs, old): {==}

# ------------------------- model swap -------------------------

def swap_m(t: PT, n: U32, +i: U32, +v: U32) -> PT:
  match t:
    case PL{x}: PL{v}
    case PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      Bool.pick(PT, z,
        PN{swap_m(xs, h, i, v), ys},
        PN{xs, swap_m(ys, h, U32.sub(i, h), v)})

def swap_ref_if(
  +xs: PT, +ys: PT, +h: U32, +i: U32, +v: U32, +z: Bool,
  ihx: {unpack(afst(Array.swap.go(U32, pack(xs), h, i, v))) == swap_m(xs, h, i, v) : PT},
  ihy: {unpack(afst(Array.swap.go(U32, pack(ys), h, U32.sub(i, h), v))) == swap_m(ys, h, U32.sub(i, h), v) : PT}
) -> {unpack(afst(Array.swap.if(U32, pack(xs), pack(ys), h, i, v, z))) == Bool.pick(PT, z, PN{swap_m(xs, h, i, v), ys}, PN{xs, swap_m(ys, h, U32.sub(i, h), v)}) : PT}:
  match z:
    case True{}:
      Equal.trans(PT,
        unpack(afst(Array.swap.lo(U32, pack(ys), Array.swap.go(U32, pack(xs), h, i, v)))),
        PN{unpack(afst(Array.swap.go(U32, pack(xs), h, i, v))), unpack(pack(ys))},
        PN{swap_m(xs, h, i, v), ys},
        Equal.cong(Array<U32>, PT, a => unpack(a),
          afst(Array.swap.lo(U32, pack(ys), Array.swap.go(U32, pack(xs), h, i, v))),
          ANode{afst(Array.swap.go(U32, pack(xs), h, i, v)), pack(ys)},
          lo_fst(pack(ys), Array.swap.go(U32, pack(xs), h, i, v))),
        Equal.trans(PT,
          PN{unpack(afst(Array.swap.go(U32, pack(xs), h, i, v))), unpack(pack(ys))},
          PN{swap_m(xs, h, i, v), unpack(pack(ys))},
          PN{swap_m(xs, h, i, v), ys},
          Equal.cong(PT, PT, x => PN{x, unpack(pack(ys))},
            unpack(afst(Array.swap.go(U32, pack(xs), h, i, v))), swap_m(xs, h, i, v), ihx),
          Equal.cong(PT, PT, y => PN{swap_m(xs, h, i, v), y}, unpack(pack(ys)), ys, unpack_pack(ys))))
    case False{}:
      Equal.trans(PT,
        unpack(afst(Array.swap.hi(U32, pack(xs), Array.swap.go(U32, pack(ys), h, U32.sub(i, h), v)))),
        PN{unpack(pack(xs)), unpack(afst(Array.swap.go(U32, pack(ys), h, U32.sub(i, h), v)))},
        PN{xs, swap_m(ys, h, U32.sub(i, h), v)},
        Equal.cong(Array<U32>, PT, a => unpack(a),
          afst(Array.swap.hi(U32, pack(xs), Array.swap.go(U32, pack(ys), h, U32.sub(i, h), v))),
          ANode{pack(xs), afst(Array.swap.go(U32, pack(ys), h, U32.sub(i, h), v))},
          hi_fst(pack(xs), Array.swap.go(U32, pack(ys), h, U32.sub(i, h), v))),
        Equal.trans(PT,
          PN{unpack(pack(xs)), unpack(afst(Array.swap.go(U32, pack(ys), h, U32.sub(i, h), v)))},
          PN{xs, unpack(afst(Array.swap.go(U32, pack(ys), h, U32.sub(i, h), v)))},
          PN{xs, swap_m(ys, h, U32.sub(i, h), v)},
          Equal.cong(PT, PT, x => PN{x, unpack(afst(Array.swap.go(U32, pack(ys), h, U32.sub(i, h), v)))},
            unpack(pack(xs)), xs, unpack_pack(xs)),
          Equal.cong(PT, PT, y => PN{xs, y},
            unpack(afst(Array.swap.go(U32, pack(ys), h, U32.sub(i, h), v))),
            swap_m(ys, h, U32.sub(i, h), v), ihy)))

def swap_ref(t: PT, n: U32, +i: U32, +v: U32)
  -> {unpack(afst(Array.swap.go(U32, pack(t), n, i, v))) == swap_m(t, n, i, v) : PT}:
  match t:
    case PL{x}:
      {==}
    case PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      swap_ref_if(xs, ys, h, i, v, z, swap_ref(xs, h, i, v), swap_ref(ys, h, U32.sub(i, h), v))

# ------------------------- potential folds -------------------------

def pots_m(t: PT, +base: U32, +n: U32) -> +List<Nat>:
  match t:
    case PL{x}: [S.pot_at(x, base)]
    case PN{+xs, +ys}:
      +h = U32.shr(n)
      S.app(pots_m(xs, base, h), pots_m(ys, U32.add(base, h), h))

def pots_swap_m(t: PT, +base: U32, +n: U32, +i: U32, +v: U32) -> +List<Nat>:
  match t:
    case PL{x}: [S.pot_at(v, base)]
    case PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      Bool.pick(List<&2, Nat>, z,
        S.app(pots_swap_m(xs, base, h, i, v), pots_m(ys, U32.add(base, h), h)),
        S.app(pots_m(xs, base, h), pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v)))

def chg_m(t: PT, +base: U32, +n: U32, +i: U32, +v: U32) -> Nat & Nat:
  match t:
    case PL{x}: (S.pot_at(x, base), S.pot_at(v, base))
    case PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      Bool.pick(Nat & Nat, z,
        chg_m(xs, base, h, i, v),
        chg_m(ys, U32.add(base, h), h, U32.sub(i, h), v))

def to_pots_pack(t: PT, +base: U32, +n: U32)
  -> {S.to_pots(pack(t), base, n) == pots_m(t, base, n) : +List<Nat>}:
  match t:
    case PL{x}:
      {==}
    case PN{+xs, +ys}:
      +h = U32.shr(n)
      +e1 = Equal.cong(List<&2, Nat>, List<&2, Nat>, x => S.app(x, S.to_pots(pack(ys), U32.add(base, h), h)),
        S.to_pots(pack(xs), base, h), pots_m(xs, base, h), to_pots_pack(xs, base, h))
      +e2 = Equal.cong(List<&2, Nat>, List<&2, Nat>, y => S.app(pots_m(xs, base, h), y),
        S.to_pots(pack(ys), U32.add(base, h), h), pots_m(ys, U32.add(base, h), h),
        to_pots_pack(ys, U32.add(base, h), h))
      Equal.trans(List<&2, Nat>,
        S.to_pots(ANode{pack(xs), pack(ys)}, base, n),
        S.app(pots_m(xs, base, h), S.to_pots(pack(ys), U32.add(base, h), h)),
        S.app(pots_m(xs, base, h), pots_m(ys, U32.add(base, h), h)),
        e1,
        e2)

def pots_corr_if(
  +xs: PT, +ys: PT, +base: U32, +n: U32, +i: U32, +v: U32, +z: Bool,
  ihx: {pots_m(swap_m(xs, U32.shr(n), i, v), base, U32.shr(n)) == pots_swap_m(xs, base, U32.shr(n), i, v) : +List<Nat>},
  ihy: {pots_m(swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v), U32.add(base, U32.shr(n)), U32.shr(n)) == pots_swap_m(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)), v) : +List<Nat>}
) -> {pots_m(Bool.pick(PT, z, PN{swap_m(xs, U32.shr(n), i, v), ys}, PN{xs, swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v)}), base, n)
    == Bool.pick(List<&2, Nat>, z,
        S.app(pots_swap_m(xs, base, U32.shr(n), i, v), pots_m(ys, U32.add(base, U32.shr(n)), U32.shr(n))),
        S.app(pots_m(xs, base, U32.shr(n)), pots_swap_m(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)), v)))
    : +List<Nat>}:
  match z:
    case True{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>,
        x => S.app(x, pots_m(ys, U32.add(base, U32.shr(n)), U32.shr(n))),
        pots_m(swap_m(xs, U32.shr(n), i, v), base, U32.shr(n)),
        pots_swap_m(xs, base, U32.shr(n), i, v), ihx)
    case False{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>,
        x => S.app(pots_m(xs, base, U32.shr(n)), x),
        pots_m(swap_m(ys, U32.shr(n), U32.sub(i, U32.shr(n)), v), U32.add(base, U32.shr(n)), U32.shr(n)),
        pots_swap_m(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)), v), ihy)

def pots_corr(t: PT, +base: U32, +n: U32, +i: U32, +v: U32)
  -> {pots_m(swap_m(t, n, i, v), base, n) == pots_swap_m(t, base, n, i, v) : +List<Nat>}:
  match t:
    case PL{x}:
      {==}
    case PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      pots_corr_if(xs, ys, base, n, i, v, z,
        pots_corr(xs, base, h, i, v),
        pots_corr(ys, U32.add(base, h), h, U32.sub(i, h), v))

# ------------------------- Φ decrease -------------------------

def dec_if(
  +xs: PT, +ys: PT, +base: U32, +n: U32, +i: U32, +v: U32, +z: Bool,
  ihx: {Nat.add(S.suml(pots_swap_m(xs, base, U32.shr(n), i, v)), nfst(chg_m(xs, base, U32.shr(n), i, v))) == Nat.add(S.suml(pots_m(xs, base, U32.shr(n))), nsnd(chg_m(xs, base, U32.shr(n), i, v))) : Nat},
  ihy: {Nat.add(S.suml(pots_swap_m(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)), v)), nfst(chg_m(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)), v))) == Nat.add(S.suml(pots_m(ys, U32.add(base, U32.shr(n)), U32.shr(n))), nsnd(chg_m(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)), v))) : Nat}
) -> {Nat.add(S.suml(Bool.pick(List<&2, Nat>, z,
        S.app(pots_swap_m(xs, base, U32.shr(n), i, v), pots_m(ys, U32.add(base, U32.shr(n)), U32.shr(n))),
        S.app(pots_m(xs, base, U32.shr(n)), pots_swap_m(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)), v)))),
      nfst(Bool.pick(Nat & Nat, z, chg_m(xs, base, U32.shr(n), i, v), chg_m(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)), v))))
    == Nat.add(S.suml(S.app(pots_m(xs, base, U32.shr(n)), pots_m(ys, U32.add(base, U32.shr(n)), U32.shr(n)))),
      nsnd(Bool.pick(Nat & Nat, z, chg_m(xs, base, U32.shr(n), i, v), chg_m(ys, U32.add(base, U32.shr(n)), U32.shr(n), U32.sub(i, U32.shr(n)), v))))
    : Nat}:
  match z:
    case True{}:
      +h = U32.shr(n)
      +BX = S.suml(pots_m(xs, base, h))
      +R = S.suml(pots_m(ys, U32.add(base, h), h))
      +OLD = nfst(chg_m(xs, base, h, i, v))
      +NEW = nsnd(chg_m(xs, base, h, i, v))
      +ea = S.suml_append(pots_swap_m(xs, base, h, i, v), pots_m(ys, U32.add(base, h), h))
      +eb = S.suml_append(pots_m(xs, base, h), pots_m(ys, U32.add(base, h), h))
      +s1 = S.swap_add(S.suml(pots_swap_m(xs, base, h, i, v)), R, OLD)
      +s2 = Equal.cong(Nat, Nat, x => Nat.add(x, R),
        Nat.add(S.suml(pots_swap_m(xs, base, h, i, v)), OLD), Nat.add(BX, NEW), ihx)
      +s3 = Equal.sym(Nat, Nat.add(Nat.add(BX, R), NEW), Nat.add(Nat.add(BX, NEW), R), S.swap_add(BX, R, NEW))
      Equal.trans(Nat,
        Nat.add(S.suml(S.app(pots_swap_m(xs, base, h, i, v), pots_m(ys, U32.add(base, h), h))), OLD),
        Nat.add(Nat.add(BX, R), NEW),
        Nat.add(S.suml(S.app(pots_m(xs, base, h), pots_m(ys, U32.add(base, h), h))), NEW),
        Equal.trans(Nat,
          Nat.add(S.suml(S.app(pots_swap_m(xs, base, h, i, v), pots_m(ys, U32.add(base, h), h))), OLD),
          Nat.add(Nat.add(S.suml(pots_swap_m(xs, base, h, i, v)), R), OLD),
          Nat.add(Nat.add(BX, R), NEW),
          Equal.cong(Nat, Nat, s => Nat.add(s, OLD),
            S.suml(S.app(pots_swap_m(xs, base, h, i, v), pots_m(ys, U32.add(base, h), h))),
            Nat.add(S.suml(pots_swap_m(xs, base, h, i, v)), R), ea),
          Equal.trans(Nat,
            Nat.add(Nat.add(S.suml(pots_swap_m(xs, base, h, i, v)), R), OLD),
            Nat.add(Nat.add(BX, NEW), R),
            Nat.add(Nat.add(BX, R), NEW),
            Equal.trans(Nat,
              Nat.add(Nat.add(S.suml(pots_swap_m(xs, base, h, i, v)), R), OLD),
              Nat.add(Nat.add(S.suml(pots_swap_m(xs, base, h, i, v)), OLD), R),
              Nat.add(Nat.add(BX, NEW), R),
              s1,
              s2),
            s3)),
        Equal.sym(Nat,
          Nat.add(S.suml(S.app(pots_m(xs, base, h), pots_m(ys, U32.add(base, h), h))), NEW),
          Nat.add(Nat.add(BX, R), NEW),
          Equal.cong(Nat, Nat, s => Nat.add(s, NEW),
            S.suml(S.app(pots_m(xs, base, h), pots_m(ys, U32.add(base, h), h))),
            Nat.add(BX, R), eb)))
    case False{}:
      +h = U32.shr(n)
      +AX = S.suml(pots_m(xs, base, h))
      +BY = S.suml(pots_m(ys, U32.add(base, h), h))
      +OLD = nfst(chg_m(ys, U32.add(base, h), h, U32.sub(i, h), v))
      +NEW = nsnd(chg_m(ys, U32.add(base, h), h, U32.sub(i, h), v))
      +ea = S.suml_append(pots_m(xs, base, h), pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v))
      +eb = S.suml_append(pots_m(xs, base, h), pots_m(ys, U32.add(base, h), h))
      +s1 = NatL.n_add_assoc(AX, S.suml(pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v)), OLD)
      +s2 = Equal.cong(Nat, Nat, x => Nat.add(AX, x),
        Nat.add(S.suml(pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v)), OLD), Nat.add(BY, NEW), ihy)
      +s3 = NatL.n_add_assoc(AX, BY, NEW)
      Equal.trans(Nat,
        Nat.add(S.suml(S.app(pots_m(xs, base, h), pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v))), OLD),
        Nat.add(AX, Nat.add(BY, NEW)),
        Nat.add(S.suml(S.app(pots_m(xs, base, h), pots_m(ys, U32.add(base, h), h))), NEW),
        Equal.trans(Nat,
          Nat.add(S.suml(S.app(pots_m(xs, base, h), pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v))), OLD),
          Nat.add(AX, Nat.add(S.suml(pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v)), OLD)),
          Nat.add(AX, Nat.add(BY, NEW)),
          Equal.trans(Nat,
            Nat.add(S.suml(S.app(pots_m(xs, base, h), pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v))), OLD),
            Nat.add(Nat.add(AX, S.suml(pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v))), OLD),
            Nat.add(AX, Nat.add(S.suml(pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v)), OLD)),
            Equal.cong(Nat, Nat, s => Nat.add(s, OLD),
              S.suml(S.app(pots_m(xs, base, h), pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v))),
              Nat.add(AX, S.suml(pots_swap_m(ys, U32.add(base, h), h, U32.sub(i, h), v))), ea),
            s1),
          s2),
        Equal.sym(Nat,
          Nat.add(S.suml(S.app(pots_m(xs, base, h), pots_m(ys, U32.add(base, h), h))), NEW),
          Nat.add(AX, Nat.add(BY, NEW)),
          Equal.trans(Nat,
            Nat.add(S.suml(S.app(pots_m(xs, base, h), pots_m(ys, U32.add(base, h), h))), NEW),
            Nat.add(Nat.add(AX, BY), NEW),
            Nat.add(AX, Nat.add(BY, NEW)),
            Equal.cong(Nat, Nat, s => Nat.add(s, NEW),
              S.suml(S.app(pots_m(xs, base, h), pots_m(ys, U32.add(base, h), h))),
              Nat.add(AX, BY), eb),
            s3)))

def dec(t: PT, +base: U32, +n: U32, +i: U32, +v: U32)
  -> {Nat.add(S.suml(pots_swap_m(t, base, n, i, v)), nfst(chg_m(t, base, n, i, v))) == Nat.add(S.suml(pots_m(t, base, n)), nsnd(chg_m(t, base, n, i, v))) : Nat}:
  match t:
    case PL{+x}:
      Equal.trans(Nat,
        Nat.add(S.suml([S.pot_at(v, base)]), S.pot_at(x, base)),
        Nat.add(S.pot_at(v, base), S.pot_at(x, base)),
        Nat.add(S.suml([S.pot_at(x, base)]), S.pot_at(v, base)),
        Equal.cong(Nat, Nat, s => Nat.add(s, S.pot_at(x, base)),
          S.suml([S.pot_at(v, base)]), S.pot_at(v, base), S.suml1(S.pot_at(v, base))),
        Equal.trans(Nat,
          Nat.add(S.pot_at(v, base), S.pot_at(x, base)),
          Nat.add(S.pot_at(x, base), S.pot_at(v, base)),
          Nat.add(S.suml([S.pot_at(x, base)]), S.pot_at(v, base)),
          NatL.n_add_comm(S.pot_at(v, base), S.pot_at(x, base)),
          Equal.sym(Nat,
            Nat.add(S.suml([S.pot_at(x, base)]), S.pot_at(v, base)),
            Nat.add(S.pot_at(x, base), S.pot_at(v, base)),
            Equal.cong(Nat, Nat, s => Nat.add(s, S.pot_at(v, base)),
              S.suml([S.pot_at(x, base)]), S.pot_at(x, base), S.suml1(S.pot_at(x, base))))))
    case PN{+xs, +ys}:
      +h = U32.shr(n)
      +z = U32.is_lt(i, h)
      dec_if(xs, ys, base, n, i, v, z,
        dec(xs, base, h, i, v),
        dec(ys, U32.add(base, h), h, U32.sub(i, h), v))

# The composed array-level claim: the pot list of Base's Array.swap.go result
# equals the incrementally-updated pot list of the model.
def array_swap_pots(+t: PT, +base: U32, +n: U32, +i: U32, +v: U32)
  -> {S.to_pots(afst(Array.swap.go(U32, pack(t), n, i, v)), base, n) == pots_swap_m(t, base, n, i, v) : +List<Nat>}:
  +ea = Equal.sym(Array<U32>, pack(unpack(afst(Array.swap.go(U32, pack(t), n, i, v)))),
    afst(Array.swap.go(U32, pack(t), n, i, v)),
    pack_unpack(afst(Array.swap.go(U32, pack(t), n, i, v))))
  +eb = Equal.cong(PT, Array<U32>, t2 => pack(t2),
    unpack(afst(Array.swap.go(U32, pack(t), n, i, v))), swap_m(t, n, i, v),
    swap_ref(t, n, i, v))
  +e1 = Equal.cong(Array<U32>, +List<Nat>, a => S.to_pots(a, base, n),
    afst(Array.swap.go(U32, pack(t), n, i, v)), pack(swap_m(t, n, i, v)),
    Equal.trans(Array<U32>,
      afst(Array.swap.go(U32, pack(t), n, i, v)),
      pack(unpack(afst(Array.swap.go(U32, pack(t), n, i, v)))),
      pack(swap_m(t, n, i, v)),
      ea, eb))
  Equal.trans(+List<Nat>,
    S.to_pots(afst(Array.swap.go(U32, pack(t), n, i, v)), base, n),
    S.to_pots(pack(swap_m(t, n, i, v)), base, n),
    pots_swap_m(t, base, n, i, v),
    e1,
    Equal.trans(+List<Nat>,
      S.to_pots(pack(swap_m(t, n, i, v)), base, n),
      pots_m(swap_m(t, n, i, v), base, n),
      pots_swap_m(t, base, n, i, v),
      to_pots_pack(swap_m(t, n, i, v), base, n),
      pots_corr(t, base, n, i, v)))

# The array-level Φ decrease under a point update.
def array_swap_decreases(+t: PT, +base: U32, +n: U32, +i: U32, +v: U32)
  -> {Nat.add(S.suml(S.to_pots(afst(Array.swap.go(U32, pack(t), n, i, v)), base, n)), nfst(chg_m(t, base, n, i, v))) == Nat.add(S.suml(S.to_pots(pack(t), base, n)), nsnd(chg_m(t, base, n, i, v))) : Nat}:
  +e1 = Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
    S.to_pots(afst(Array.swap.go(U32, pack(t), n, i, v)), base, n),
    pots_swap_m(t, base, n, i, v),
    array_swap_pots(t, base, n, i, v))
  +e2 = Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
    S.to_pots(pack(t), base, n), pots_m(t, base, n),
    to_pots_pack(t, base, n))
  Equal.trans(Nat,
    Nat.add(S.suml(S.to_pots(afst(Array.swap.go(U32, pack(t), n, i, v)), base, n)), nfst(chg_m(t, base, n, i, v))),
    Nat.add(S.suml(pots_swap_m(t, base, n, i, v)), nfst(chg_m(t, base, n, i, v))),
    Nat.add(S.suml(S.to_pots(pack(t), base, n)), nsnd(chg_m(t, base, n, i, v))),
    Equal.cong(Nat, Nat, x => Nat.add(x, nfst(chg_m(t, base, n, i, v))),
      S.suml(S.to_pots(afst(Array.swap.go(U32, pack(t), n, i, v)), base, n)),
      S.suml(pots_swap_m(t, base, n, i, v)), e1),
    Equal.trans(Nat,
      Nat.add(S.suml(pots_swap_m(t, base, n, i, v)), nfst(chg_m(t, base, n, i, v))),
      Nat.add(S.suml(pots_m(t, base, n)), nsnd(chg_m(t, base, n, i, v))),
      Nat.add(S.suml(S.to_pots(pack(t), base, n)), nsnd(chg_m(t, base, n, i, v))),
      dec(t, base, n, i, v),
      Equal.cong(Nat, Nat, x => Nat.add(x, nsnd(chg_m(t, base, n, i, v))),
        S.suml(pots_m(t, base, n)), S.suml(S.to_pots(pack(t), base, n)),
        Equal.sym(Nat, S.suml(S.to_pots(pack(t), base, n)), S.suml(pots_m(t, base, n)), e2))))
