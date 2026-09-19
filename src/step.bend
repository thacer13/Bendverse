import Base
import ./tick.bend as T
import ./refine.bend as R
import ./settle.bend as S
import ./nat.bend as NatL
import ./rules.bend as Rules
import ./ops.bend as Ops
import ./cell.bend as Cell
import ./grid.bend as Grid
import ./fall.bend as F

# --------------------------------------------------- RETIRED by V0-1 (A.63)
# This mirrors the **retired** `Rules.step` (removed in A.63 and replaced by
# `Rules.plan`/`Rules.phase_plan`). `step_m` is still a true theorem about that old
# selector machine, but it no longer mirrors the engine, so it is no longer
# evidence (`PLAN.md` §3.4, §4.1). Do not extend it; the live write sites are
# `Rules.plan`'s.
# ------------------------------------------------------------------ G10 closure
# `Rules.step` mirrored on `PT` so every write site's potential effect is
# machine-checked and composed. The selector is a datatype (`StepSel`); the
# `StepSel` -> numeric mapping is the `G5` refinement, by inspection (as with
# `Tick.SupSel`). The mirror does not commit to a single φ gap: a move is only a
# decrease under the fall regime, so `step_m` carries a **pair** of accumulators
# with the invariant `Φ(current) + da == Φ(start) + db`. Every write contributes
# its exact leaf-balance `(old pot, new pot)` (`pt_write_balance`), a wake adds
# nothing, and the identity is unconditional — the engine's `can` check is never
# re-derived. The wake fuel is threaded as an abstract `Nat` (A.45/A.55: a
# concrete `3` inside a proposition unrolls the loop); the top-level
# `step_pass_m` instantiates it at `3`.

type StepSel is Data:
  E0{}
  E1{}
  E2{}
  E3{}
  E4{}
  E5{}
  E6{}
  E7{}
  E8{}
  E9{}
  E10{}
  E11{}
  E12{}
  E13{}
  E14{}
  E15{}
  E16{}
  E17{}
  E18{}
  E19{}
  E20{}
  E21{}
  E22{}
  E23{}

type StepRes is Data:
  SR{t: R.PT, da: Nat, db: Nat}

def step_t(+r: StepRes) -> R.PT:
  match r:
    case SR{t, da, db}: t

def step_da(+r: StepRes) -> Nat:
  match r:
    case SR{t, da, db}: da

def step_db(+r: StepRes) -> Nat:
  match r:
    case SR{t, da, db}: db

# `Φ` of a mirror result: the tree's pot sum plus the running `da`.
def step_phi(+r: StepRes, +base: U32, +n: U32) -> Nat:
  Nat.add(S.suml(S.to_pots(R.pack(step_t(r)), base, n)), step_da(r))

# Extend the running gap by one write's `(ds, dt)` balance.
def sr_add(+r: StepRes, +ds: Nat, +dt: Nat) -> StepRes:
  SR{step_t(r), Nat.add(ds, step_da(r)), Nat.add(dt, step_db(r))}

# The one-write composition: from `Φ(after) + ds == Φ(before) + dt` and an inner
# invariant relative to `after`, the extended result is invariant relative to
# `before` (the `Φ` bookkeeping is pure Nat arithmetic).
def sr_add_phi(+r: StepRes, +t0: R.PT, +t1: R.PT, +ds: Nat, +dt: Nat, +base: U32, +n: U32,
  hw: {Nat.add(S.suml(S.to_pots(R.pack(t1), base, n)), ds) == Nat.add(S.suml(S.to_pots(R.pack(t0), base, n)), dt) : Nat},
  hi: {step_phi(r, base, n) == Nat.add(S.suml(S.to_pots(R.pack(t1), base, n)), step_db(r)) : Nat})
  -> {step_phi(sr_add(r, ds, dt), base, n) == Nat.add(S.suml(S.to_pots(R.pack(t0), base, n)), step_db(sr_add(r, ds, dt))) : Nat}:
  match r:
    case SR{t, da, db}:
      +A = S.suml(S.to_pots(R.pack(t), base, n))
      +B = S.suml(S.to_pots(R.pack(t1), base, n))
      +C = S.suml(S.to_pots(R.pack(t0), base, n))
      Equal.trans(Nat,
        Nat.add(A, Nat.add(ds, da)),
        Nat.add(A, Nat.add(da, ds)),
        Nat.add(C, Nat.add(dt, db)),
        Equal.cong(Nat, Nat, x => Nat.add(A, x), Nat.add(ds, da), Nat.add(da, ds), NatL.n_add_comm(ds, da)),
        Equal.trans(Nat,
          Nat.add(A, Nat.add(da, ds)),
          Nat.add(Nat.add(A, da), ds),
          Nat.add(C, Nat.add(dt, db)),
          Equal.sym(Nat, Nat.add(Nat.add(A, da), ds), Nat.add(A, Nat.add(da, ds)), NatL.n_add_assoc(A, da, ds)),
          Equal.trans(Nat,
            Nat.add(Nat.add(A, da), ds),
            Nat.add(Nat.add(B, db), ds),
            Nat.add(C, Nat.add(dt, db)),
            Equal.cong(Nat, Nat, x => Nat.add(x, ds), Nat.add(A, da), Nat.add(B, db), hi),
            Equal.trans(Nat,
              Nat.add(Nat.add(B, db), ds),
              Nat.add(B, Nat.add(db, ds)),
              Nat.add(C, Nat.add(dt, db)),
              NatL.n_add_assoc(B, db, ds),
              Equal.trans(Nat,
                Nat.add(B, Nat.add(db, ds)),
                Nat.add(B, Nat.add(ds, db)),
                Nat.add(C, Nat.add(dt, db)),
                Equal.cong(Nat, Nat, x => Nat.add(B, x), Nat.add(db, ds), Nat.add(ds, db), NatL.n_add_comm(db, ds)),
                Equal.trans(Nat,
                  Nat.add(B, Nat.add(ds, db)),
                  Nat.add(Nat.add(B, ds), db),
                  Nat.add(C, Nat.add(dt, db)),
                  Equal.sym(Nat, Nat.add(Nat.add(B, ds), db), Nat.add(B, Nat.add(ds, db)), NatL.n_add_assoc(B, ds, db)),
                  Equal.trans(Nat,
                    Nat.add(Nat.add(B, ds), db),
                    Nat.add(Nat.add(C, dt), db),
                    Nat.add(C, Nat.add(dt, db)),
                    Equal.cong(Nat, Nat, x => Nat.add(x, db), Nat.add(B, ds), Nat.add(C, dt), hw),
                    NatL.n_add_assoc(C, dt, db))))))))

# Retarget an inner invariant across an equal-`Φ` change of the pre-tree (the
# wake steps: `wake_z_m` only writes the activity bit).
def sr_phi_cong(+r: StepRes, +t0: R.PT, +t1: R.PT, +base: U32, +n: U32,
  hphi: {S.suml(S.to_pots(R.pack(t1), base, n)) == S.suml(S.to_pots(R.pack(t0), base, n)) : Nat},
  hi: {step_phi(r, base, n) == Nat.add(S.suml(S.to_pots(R.pack(t1), base, n)), step_db(r)) : Nat})
  -> {step_phi(r, base, n) == Nat.add(S.suml(S.to_pots(R.pack(t0), base, n)), step_db(r)) : Nat}:
  Equal.trans(Nat,
    step_phi(r, base, n),
    Nat.add(S.suml(S.to_pots(R.pack(t1), base, n)), step_db(r)),
    Nat.add(S.suml(S.to_pots(R.pack(t0), base, n)), step_db(r)),
    hi,
    Equal.cong(Nat, Nat, x => Nat.add(x, step_db(r)),
      S.suml(S.to_pots(R.pack(t1), base, n)), S.suml(S.to_pots(R.pack(t0), base, n)), hphi))

# The leaf-potentials a write at `i` replaces: `wr_old` is the current pot at the
# leaf, `wr_new` the written value's pot there.
def wr_old(+t: R.PT, +base: U32, +n: U32, +i: U32) -> Nat:
  S.pot_at(T.tget(t, n, i), F.leaf_base(t, base, n, i))

def wr_new(+t: R.PT, +base: U32, +n: U32, +i: U32, +v: U32) -> Nat:
  S.pot_at(v, F.leaf_base(t, base, n, i))

# The exact leaf balance of a single point write, at the array (`to_pots`)
# presentation the mirror uses. This is `Refine.swap_balance` transported across
# `to_pots(pack(swap_m ..)) == pots_m(swap_m ..)`.
def pt_write_balance(+t: R.PT, +base: U32, +n: U32, +i: U32, +v: U32)
  -> {Nat.add(S.suml(S.to_pots(R.pack(R.swap_m(t, n, i, v)), base, n)), wr_old(t, base, n, i))
      == Nat.add(S.suml(S.to_pots(R.pack(t), base, n)), wr_new(t, base, n, i, v)) : Nat}:
  +after = S.suml(S.to_pots(R.pack(R.swap_m(t, n, i, v)), base, n))
  +before = S.suml(S.to_pots(R.pack(t), base, n))
  +A2 = S.suml(R.pots_m(R.swap_m(t, n, i, v), base, n))
  +A0 = S.suml(R.pots_m(t, base, n))
  +pold = wr_old(t, base, n, i)
  +pnew = wr_new(t, base, n, i, v)
  +e2 = Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
    S.to_pots(R.pack(R.swap_m(t, n, i, v)), base, n), R.pots_m(R.swap_m(t, n, i, v), base, n),
    R.to_pots_pack(R.swap_m(t, n, i, v), base, n))
  +e0 = Equal.cong(List<&2, Nat>, Nat, l => S.suml(l),
    S.to_pots(R.pack(t), base, n), R.pots_m(t, base, n), R.to_pots_pack(t, base, n))
  +bal = F.swap_balance(t, base, n, i, v)
  Equal.trans(Nat,
    Nat.add(after, pold),
    Nat.add(A2, pold),
    Nat.add(before, pnew),
    Equal.cong(Nat, Nat, x => Nat.add(x, pold), after, A2, e2),
    Equal.trans(Nat,
      Nat.add(A2, pold),
      Nat.add(A0, pnew),
      Nat.add(before, pnew),
      bal,
      Equal.cong(Nat, Nat, x => Nat.add(x, pnew), A0, before, Equal.sym(Nat, before, A0, e0))))

# ------------------------------------------------------------------ the mirror
def step_m(fuel: Nat, +t: R.PT, +gv: U32, +sel: StepSel, +i: U32, +c: U32, +w: U32, +k: U32, +wf: Nat, +n: U32, +base: U32) -> StepRes:
  match fuel:
    case 0n:
      SR{t, 0n, 0n}
    case 1n+p:
      match sel:
        case E0{}:
          +v = gv
          act = U32.is_ne(Cell.active(v), 0)
          step_m(p, t, v, Bool.pick(StepSel, act, E20{}, E19{}), i, c, 0, 0, wf, n, base)
        case E20{}:
          +v = gv
          bad = U32.is_ne(Rules.color_of(i), c)
          step_m(p, t, v, Bool.pick(StepSel, bad, E19{}, E18{}), i, c, 0, 0, wf, n, base)
        case E19{}:
          step_m(p, t, gv, E14{}, i, c, 0, 0, wf, n, base)
        case E18{}:
          +v = gv
          +nw = Cell.deactivate(v)
          +t1 = R.swap_m(t, n, i, nw)
          +m = Cell.material(v)
          skip = Bool.or(Bool.or(U32.is_eq(m, 0), Cell.static(m)), U32.is_ne(Cell.cohesion(v), 0))
          sr_add(step_m(p, t1, v, Bool.pick(StepSel, skip, E4{}, E5{}), i, c, v, 0, wf, n, base),
                 wr_old(t, base, n, i), wr_new(t, base, n, i, nw))
        case E4{}:
          step_m(p, t, gv, E14{}, i, c, 0, 0, wf, n, base)
        case E5{}:
          +q = T.tget(t, n, Grid.below(i))
          step_m(p, t, q, E1{}, i, c, w, 0, wf, n, base)
        case E1{}:
          +mb = Cell.material(gv)
          can = Bool.or(U32.is_eq(mb, 0), U32.is_lt(Cell.density(mb), Cell.density(Cell.material(w))))
          step_m(p, t, gv, Bool.pick(StepSel, can, E6{}, E7{}), i, c, w, 0, wf, n, base)
        case E6{}:
          +j = Grid.below(i)
          +t1 = R.swap_m(t, n, j, Rules.mov(w))
          +t2 = R.swap_m(t1, n, i, gv)
          +t3 = T.wake_z_m(wf, 0, i, t2, n)
          +t4 = T.wake_z_m(wf, 0, j, t3, n)
          +q = T.tget(t4, n, i)
          sr_add(sr_add(step_m(p, t4, q, E14{}, i, c, 0, 0, wf, n, base),
                        wr_old(t1, base, n, i), wr_new(t1, base, n, i, gv)),
                 wr_old(t, base, n, j), wr_new(t, base, n, j, Rules.mov(w)))
        case E7{}:
          +sl = Cell.slides(Cell.material(w))
          step_m(p, t, gv, Bool.pick(StepSel, sl, E9{}, E8{}), i, c, w, 0, wf, n, base)
        case E8{}:
          +q = T.tget(t, n, Grid.below(i))
          step_m(p, t, q, E21{}, i, c, w, 0, wf, n, base)
        case E9{}:
          +q = T.tget(t, n, Rules.side_index(i, k))
          step_m(p, t, q, E2{}, i, c, w, k, wf, n, base)
        case E2{}:
          +ms = Cell.material(gv)
          sok = Bool.or(U32.is_eq(ms, 0), U32.is_lt(Cell.density(ms), Cell.density(Cell.material(w))))
          step_m(p, t, gv, Bool.pick(StepSel, sok, E10{}, E11{}), i, c, w, k, wf, n, base)
        case E10{}:
          +q = T.tget(t, n, Rules.diag_index(i, k))
          step_m(p, t, q, E3{}, i, c, w, k, wf, n, base)
        case E3{}:
          +md = Cell.material(gv)
          dok = Bool.or(U32.is_eq(md, 0), U32.is_lt(Cell.density(md), Cell.density(Cell.material(w))))
          step_m(p, t, gv, Bool.pick(StepSel, dok, E12{}, E13{}), i, c, w, k, wf, n, base)
        case E11{}:
          +nk = U32.add(k, 1)
          step_m(p, t, gv, Bool.pick(StepSel, U32.is_eq(nk, 4), E8{}, E9{}), i, c, w, nk, wf, n, base)
        case E12{}:
          +j = Rules.diag_index(i, k)
          +t1 = R.swap_m(t, n, j, w)
          +t2 = R.swap_m(t1, n, i, gv)
          +t3 = T.wake_z_m(wf, 0, i, t2, n)
          +t4 = T.wake_z_m(wf, 0, j, t3, n)
          +q = T.tget(t4, n, i)
          sr_add(sr_add(step_m(p, t4, q, E14{}, i, c, 0, 0, wf, n, base),
                        wr_old(t1, base, n, i), wr_new(t1, base, n, i, gv)),
                 wr_old(t, base, n, j), wr_new(t, base, n, j, w))
        case E13{}:
          +nk = U32.add(k, 1)
          step_m(p, t, gv, Bool.pick(StepSel, U32.is_eq(nk, 4), E8{}, E9{}), i, c, w, nk, wf, n, base)
        case E21{}:
          +b = gv
          +f = Cell.fall(w)
          tst = Cell.static(Cell.material(b))
          dmg = Bool.and(U32.is_ne(f, 0), Bool.and(Bool.not(tst), U32.is_ge(f, Cell.cohesion(b))))
          step_m(p, t, b, Bool.pick(StepSel, dmg, E22{}, E23{}), i, c, w, 0, wf, n, base)
        case E22{}:
          +j = Grid.below(i)
          +t1 = R.swap_m(t, n, j, Ops.crush_if_rock(gv))
          +t2 = T.wake_z_m(wf, 0, j, t1, n)
          +t3 = R.swap_m(t2, n, i, Ops.set_fall0(w))
          +t4 = T.wake_z_m(wf, 0, i, t3, n)
          +q = T.tget(t4, n, i)
          sr_add(sr_add(step_m(p, t4, q, E14{}, i, c, 0, 0, wf, n, base),
                        wr_old(t2, base, n, i), wr_new(t2, base, n, i, Ops.set_fall0(w))),
                 wr_old(t, base, n, j), wr_new(t, base, n, j, Ops.crush_if_rock(gv)))
        case E23{}:
          +t1 = R.swap_m(t, n, i, Ops.set_fall0(w))
          +q = T.tget(t1, n, i)
          sr_add(step_m(p, t1, q, E14{}, i, c, 0, 0, wf, n, base),
                 wr_old(t, base, n, i), wr_new(t, base, n, i, Ops.set_fall0(w)))
        case E14{}:
          step_m(p, t, gv, Bool.pick(StepSel, U32.is_eq(U32.add(i, 1), Grid.volume()), E15{}, E16{}), i, c, 0, 0, wf, n, base)
        case E15{}:
          SR{t, 0n, 0n}
        case E16{}:
          +ni = U32.add(i, 1)
          +q = T.tget(t, n, ni)
          step_m(p, t, q, E0{}, ni, c, 0, 0, wf, n, base)
        case E17{}:
          SR{t, 0n, 0n}

# The fuel-loop preservation: composing the write primitives along `Rules.step`'s
# control flow keeps the pair invariant `Φ(current) + da == Φ(start) + db`. Stated
# over an abstract fuel (all fuels), so also over the engine's `to_nat(16777216)`.
def step_preserves(+fuel: Nat, +t: R.PT, +gv: U32, +sel: StepSel, +i: U32, +c: U32, +w: U32, +k: U32, +wf: Nat, +n: U32, +base: U32)
  -> {step_phi(step_m(fuel, t, gv, sel, i, c, w, k, wf, n, base), base, n)
      == Nat.add(S.suml(S.to_pots(R.pack(t), base, n)), step_db(step_m(fuel, t, gv, sel, i, c, w, k, wf, n, base))) : Nat}:
  match fuel:
    case 0n:
      {==}
    case 1n+p:
      match sel:
        case E0{}:
          +v = gv
          act = U32.is_ne(Cell.active(v), 0)
          step_preserves(p, t, v, Bool.pick(StepSel, act, E20{}, E19{}), i, c, 0, 0, wf, n, base)
        case E20{}:
          +v = gv
          bad = U32.is_ne(Rules.color_of(i), c)
          step_preserves(p, t, v, Bool.pick(StepSel, bad, E19{}, E18{}), i, c, 0, 0, wf, n, base)
        case E19{}:
          step_preserves(p, t, gv, E14{}, i, c, 0, 0, wf, n, base)
        case E18{}:
          +v = gv
          +nw = Cell.deactivate(v)
          +t1 = R.swap_m(t, n, i, nw)
          +m = Cell.material(v)
          skip = Bool.or(Bool.or(U32.is_eq(m, 0), Cell.static(m)), U32.is_ne(Cell.cohesion(v), 0))
          +sel2 = Bool.pick(StepSel, skip, E4{}, E5{})
          sr_add_phi(step_m(p, t1, v, sel2, i, c, v, 0, wf, n, base), t, t1,
            wr_old(t, base, n, i), wr_new(t, base, n, i, nw), base, n,
            pt_write_balance(t, base, n, i, nw),
            step_preserves(p, t1, v, sel2, i, c, v, 0, wf, n, base))
        case E4{}:
          step_preserves(p, t, gv, E14{}, i, c, 0, 0, wf, n, base)
        case E5{}:
          +q = T.tget(t, n, Grid.below(i))
          step_preserves(p, t, q, E1{}, i, c, w, 0, wf, n, base)
        case E1{}:
          +mb = Cell.material(gv)
          can = Bool.or(U32.is_eq(mb, 0), U32.is_lt(Cell.density(mb), Cell.density(Cell.material(w))))
          step_preserves(p, t, gv, Bool.pick(StepSel, can, E6{}, E7{}), i, c, w, 0, wf, n, base)
        case E6{}:
          +j = Grid.below(i)
          +t1 = R.swap_m(t, n, j, Rules.mov(w))
          +t2 = R.swap_m(t1, n, i, gv)
          +t3 = T.wake_z_m(wf, 0, i, t2, n)
          +t4 = T.wake_z_m(wf, 0, j, t3, n)
          +q = T.tget(t4, n, i)
          +inner = step_m(p, t4, q, E14{}, i, c, 0, 0, wf, n, base)
          +hwake = Equal.trans(Nat,
            S.suml(S.to_pots(R.pack(t4), base, n)),
            S.suml(S.to_pots(R.pack(t3), base, n)),
            S.suml(S.to_pots(R.pack(t2), base, n)),
            T.wake_z_m_preserves(wf, 0, j, t3, n, base),
            T.wake_z_m_preserves(wf, 0, i, t2, n, base))
          +hi2 = sr_phi_cong(inner, t2, t4, base, n, hwake,
            step_preserves(p, t4, q, E14{}, i, c, 0, 0, wf, n, base))
          +hi1 = sr_add_phi(inner, t1, t2,
            wr_old(t1, base, n, i), wr_new(t1, base, n, i, gv), base, n,
            pt_write_balance(t1, base, n, i, gv), hi2)
          sr_add_phi(sr_add(inner, wr_old(t1, base, n, i), wr_new(t1, base, n, i, gv)), t, t1,
            wr_old(t, base, n, j), wr_new(t, base, n, j, Rules.mov(w)), base, n,
            pt_write_balance(t, base, n, j, Rules.mov(w)), hi1)
        case E7{}:
          +sl = Cell.slides(Cell.material(w))
          step_preserves(p, t, gv, Bool.pick(StepSel, sl, E9{}, E8{}), i, c, w, 0, wf, n, base)
        case E8{}:
          +q = T.tget(t, n, Grid.below(i))
          step_preserves(p, t, q, E21{}, i, c, w, 0, wf, n, base)
        case E9{}:
          +q = T.tget(t, n, Rules.side_index(i, k))
          step_preserves(p, t, q, E2{}, i, c, w, k, wf, n, base)
        case E2{}:
          +ms = Cell.material(gv)
          sok = Bool.or(U32.is_eq(ms, 0), U32.is_lt(Cell.density(ms), Cell.density(Cell.material(w))))
          step_preserves(p, t, gv, Bool.pick(StepSel, sok, E10{}, E11{}), i, c, w, k, wf, n, base)
        case E10{}:
          +q = T.tget(t, n, Rules.diag_index(i, k))
          step_preserves(p, t, q, E3{}, i, c, w, k, wf, n, base)
        case E3{}:
          +md = Cell.material(gv)
          dok = Bool.or(U32.is_eq(md, 0), U32.is_lt(Cell.density(md), Cell.density(Cell.material(w))))
          step_preserves(p, t, gv, Bool.pick(StepSel, dok, E12{}, E13{}), i, c, w, k, wf, n, base)
        case E11{}:
          +nk = U32.add(k, 1)
          step_preserves(p, t, gv, Bool.pick(StepSel, U32.is_eq(nk, 4), E8{}, E9{}), i, c, w, nk, wf, n, base)
        case E12{}:
          +j = Rules.diag_index(i, k)
          +t1 = R.swap_m(t, n, j, w)
          +t2 = R.swap_m(t1, n, i, gv)
          +t3 = T.wake_z_m(wf, 0, i, t2, n)
          +t4 = T.wake_z_m(wf, 0, j, t3, n)
          +q = T.tget(t4, n, i)
          +inner = step_m(p, t4, q, E14{}, i, c, 0, 0, wf, n, base)
          +hwake = Equal.trans(Nat,
            S.suml(S.to_pots(R.pack(t4), base, n)),
            S.suml(S.to_pots(R.pack(t3), base, n)),
            S.suml(S.to_pots(R.pack(t2), base, n)),
            T.wake_z_m_preserves(wf, 0, j, t3, n, base),
            T.wake_z_m_preserves(wf, 0, i, t2, n, base))
          +hi2 = sr_phi_cong(inner, t2, t4, base, n, hwake,
            step_preserves(p, t4, q, E14{}, i, c, 0, 0, wf, n, base))
          +hi1 = sr_add_phi(inner, t1, t2,
            wr_old(t1, base, n, i), wr_new(t1, base, n, i, gv), base, n,
            pt_write_balance(t1, base, n, i, gv), hi2)
          sr_add_phi(sr_add(inner, wr_old(t1, base, n, i), wr_new(t1, base, n, i, gv)), t, t1,
            wr_old(t, base, n, j), wr_new(t, base, n, j, w), base, n,
            pt_write_balance(t, base, n, j, w), hi1)
        case E13{}:
          +nk = U32.add(k, 1)
          step_preserves(p, t, gv, Bool.pick(StepSel, U32.is_eq(nk, 4), E8{}, E9{}), i, c, w, nk, wf, n, base)
        case E21{}:
          +b = gv
          +f = Cell.fall(w)
          tst = Cell.static(Cell.material(b))
          dmg = Bool.and(U32.is_ne(f, 0), Bool.and(Bool.not(tst), U32.is_ge(f, Cell.cohesion(b))))
          step_preserves(p, t, b, Bool.pick(StepSel, dmg, E22{}, E23{}), i, c, w, 0, wf, n, base)
        case E22{}:
          +j = Grid.below(i)
          +t1 = R.swap_m(t, n, j, Ops.crush_if_rock(gv))
          +t2 = T.wake_z_m(wf, 0, j, t1, n)
          +t3 = R.swap_m(t2, n, i, Ops.set_fall0(w))
          +t4 = T.wake_z_m(wf, 0, i, t3, n)
          +q = T.tget(t4, n, i)
          +inner = step_m(p, t4, q, E14{}, i, c, 0, 0, wf, n, base)
          +r_i = sr_add(inner, wr_old(t2, base, n, i), wr_new(t2, base, n, i, Ops.set_fall0(w)))
          +hi3 = sr_phi_cong(inner, t3, t4, base, n,
            T.wake_z_m_preserves(wf, 0, i, t3, n, base),
            step_preserves(p, t4, q, E14{}, i, c, 0, 0, wf, n, base))
          +hi2 = sr_add_phi(inner, t2, t3,
            wr_old(t2, base, n, i), wr_new(t2, base, n, i, Ops.set_fall0(w)), base, n,
            pt_write_balance(t2, base, n, i, Ops.set_fall0(w)), hi3)
          +hi1 = sr_phi_cong(r_i, t1, t2, base, n,
            T.wake_z_m_preserves(wf, 0, j, t1, n, base), hi2)
          sr_add_phi(r_i, t, t1,
            wr_old(t, base, n, j), wr_new(t, base, n, j, Ops.crush_if_rock(gv)), base, n,
            pt_write_balance(t, base, n, j, Ops.crush_if_rock(gv)), hi1)
        case E23{}:
          +t1 = R.swap_m(t, n, i, Ops.set_fall0(w))
          +q = T.tget(t1, n, i)
          sr_add_phi(step_m(p, t1, q, E14{}, i, c, 0, 0, wf, n, base), t, t1,
            wr_old(t, base, n, i), wr_new(t, base, n, i, Ops.set_fall0(w)), base, n,
            pt_write_balance(t, base, n, i, Ops.set_fall0(w)),
            step_preserves(p, t1, q, E14{}, i, c, 0, 0, wf, n, base))
        case E14{}:
          step_preserves(p, t, gv, Bool.pick(StepSel, U32.is_eq(U32.add(i, 1), Grid.volume()), E15{}, E16{}), i, c, 0, 0, wf, n, base)
        case E15{}:
          {==}
        case E16{}:
          +ni = U32.add(i, 1)
          +q = T.tget(t, n, ni)
          step_preserves(p, t, q, E0{}, ni, c, 0, 0, wf, n, base)
        case E17{}:
          {==}

# The top-level binding: the mirror run over `Sim.phase`'s entry point
# (`Rules.step(16777216, get(world,0), 0, 0, c, 0, 0)`), with the wake fuel
# instantiated at `3`. The main fuel stays abstract (all-fuel theorem).
def step_pass_m(fuel: Nat, +t: R.PT, +n: U32, +c: U32) -> StepRes:
  step_m(fuel, t, T.tget(t, n, 0), E0{}, 0, c, 0, 0, U32.to_nat(3), n, 0)
