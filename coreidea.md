Core Model

The world is a closed 3D box of cells. Each cell holds exactly one material
(including "empty"). There are no objects, no entities, no rigid bodies — a
"rock" or "boulder" is just a contiguous region of cells sharing a material and
a cohesion property. Everything that happens, happens through local cell rules
evaluated identically everywhere, every tick.

The Contract

Three sentences carry the design; the rules below are consequences of them, not
independent wishlist items.

1. **Purity of phases.** A tick is the composition of phases. Each phase is a
   *pure function* of the state it is handed: it reads that state, computes a
   write set, and yields a new state. No part of a phase reads a value that
   another part of the same phase produced.
2. **Closure.** The world is a closed box. Rules never move material out of it,
   and the simulation has no periodic wrap: a boundary move is inert.
3. **Cost tracks disturbance.** A tick's work is proportional to the number of
   disturbed cells, not to the size of the world.

These three are the target. Everything else that used to be asserted as a rule
is a *theorem* of them: determinism under any schedule (rule 10), at most one
writer per cell per phase (rule 3), collision-free parallel batches (rule 4),
and a settled world being a tick fixpoint (rule 9). A claim that follows from
the contract should be proved from it, not restated as an axiom.

The Immutable Rules

1. Locality
A cell's next state depends only on the **pre-phase** state within a fixed,
small radius (the 6 or 26 adjacent cells, plus a bounded candidate set for
contention). No rule may read a value written earlier in the same phase. This
is the rule that makes parallelism legal — it is the one constraint everything
else must obey.

2. Conservation
Material is never created or destroyed, only moved or transformed by an
explicit rule (e.g., "rock → rubble on impact"). Every movement is a swap or
transfer between two specific cells, never a copy.

3. Single-writer per cell, per tick
At most one rule application writes a given cell in a given phase. Contention is
resolved by the **schedule**, never by observing a sibling's write: a parallel
batch is constructed so two of its applications cannot target the same cell, and
where two could, a deterministic tie-break computed from the pre-phase state
picks the owner. A phase that resolves contention by re-reading a cell another
part of the phase already wrote is not a phase — it is a sequential fold.

4. Phase separation (the parallelism contract)
A tick is divided into fixed batches: a **colour** (an even/odd parity partition
of the lattice that separates each cell from its neighbours) crossed with a
**direction** (a fixed displacement). A colour batch visits cells no two of
which are neighbours; a direction batch fixes the displacement, so distinct
cells have distinct targets and contention cannot arise at all. Zero-coordination
parallelism is therefore a *property of the schedule*, and it is provable —
injectivity of the target map within a batch. Rules are written once; batching is
a scheduling concern, not a rule-author concern.

5. Falling is universal
Every non-static material obeys the same base rule: if the cell below is
lower-density-or-empty, move down; else if a diagonal-below cell is
lower-density-or-empty, move there. Materials differ only in their density and
angle of repose (how readily they slide diagonally vs. stack vertically), not in
having different fall logic. A cell's *choice* among candidate directions is a
pure function of the pre-phase state — that is what lets rule 4 batch by
direction.

6. Cohesion determines rigidity — as a local property
A cell has a cohesion value. High cohesion = it does not independently obey the
falling rule; what holds it up, and when it gives way, is decided from its own
cohesion and the **pre-phase state of its immediate neighbourhood** (support
contacts, adjacency to static material). Low cohesion = it obeys rule 5
individually every tick. Rigidity is a value on a spectrum, not a separate
object type. There is deliberately no global connected-component analysis:
"a cluster moves as one" is expressed as a local support rule, because cluster
semantics are non-local and cannot be evaluated inside a phase-parallel tick.

7. Support is derived, never carried
Support is always derived from the current neighbourhood, never carried forward
across a structural change. Derivation is scoped to **disturbed cells**: a cell
whose neighbourhood did not change cannot have changed support, so it is not
recomputed. "Recompute honestly" is a statement about staleness, not a licence
to rescan the world.

8. Impact is a threshold event, not a force simulation
No velocities, no momentum accumulation, no continuous collision. A moving cell
(falling or thrown) that would enter an occupied cell instead resolves as a
discrete impact event: if incoming "energy" (derived simply from fall
distance/speed) exceeds the target's cohesion threshold, the target's cohesion
is reduced or it converts material (rock → rubble); otherwise the mover stops.
This keeps the whole system rule-based and local instead of needing a physics
solver.

9. Activity is explicit — and its effects land next tick
A cell is evaluated only if it is marked active (recently changed, or adjacent
to something active). A cell that hasn't changed and has no active neighbour
does no work and costs nothing. A write marks the written cell and its 26
neighbours active **for the next tick**: the set of cells evaluated in a phase
is fixed when the phase begins, and a phase never pulls in a cell it woke. This
is what implements contract 3 — cost is proportional to disturbance, not world
size.

10. Determinism within a tick, not across scheduling
Given the same starting state and the same tie-break rule (#3), the result of a
tick is identical regardless of how work was distributed across processors.
Parallelism may change *when* things are computed, never *what* the answer is.
This is a corollary of contract 1: since every phase is a pure function of its
input, any evaluation order of any granularity yields the same tick. It is not a
constraint imposed on the scheduler; it is a property the phase already has.

11. World generation is a pure seeding function, not a system
For any cell coordinate, there exists a pure function f(x, y, z) → material,
parameters that depends only on the coordinate itself (and a fixed global seed) —
never on generation order, neighbouring chunks' generation status, or simulation
history. A chunk's initial state is produced by sampling this function once per
cell within it, with every cell marked inactive (per rule 9). This function may
internally layer multiple scalar fields (e.g., macro-scale for base terrain
shape, higher-frequency for material selection, sparse fields for isolated
features) — but externally it must behave as a single pure lookup: same
coordinate, same seed, same result, regardless of when or in what order it is
called. The **terrain** function is shell-free: it says what material a coordinate holds,
everywhere, with no absolute world edge, and it is a function of the coordinate
(and seed) alone — never of the window. Two things the old "shell" conflated must
be kept distinct:

- **Boundary (closure, contract 2)** is a property of the **grid or window**: a
  rule target off the resident set is inert. Window-relative is *correct* here.
- **Ground (the support base case of rules 5–7)** is a property of the **world**:
  the world-fixed datum the support recursion bottoms out on. It must *not* be
  window-relative. Ground at the window edge is ground that follows the camera:
  gravity would depend on where the observer stands, `Support` would have no
  stable anchor, and every solid cell would read as unsupported — the shell-free
  live build's ~80k spurious active cells (A.121). The concrete form of the world
  ground (a world-fixed bedrock plane, a fixed-`y` boundary rule, or a void) is a
  design choice, filed as `G-scale-9`; what the contract fixes is that it is a
  property of the *world*, not of the resident set.

The closed reference box adds its historical shell on the absolute planes
`x/y/z ∈ {0,63}`; the canonical window reproduces it bit-for-bit
(`win_gen_canonical`), so the fixed-box worlds and laws stand. Closure holds
because rule targets are guarded (contract 2), not because the grid wraps.

Where the code stands (do not confuse this with the target)

`PLAN.md` §4 is the conformance table and the single source of truth: per
contract clause and per rule, whether the engine conforms, deviates, or holds by
construction. This section states only the *shape* of the current gap, in model
terms; it changes only when a contract clause or a rule's status changes, not per
milestone.

Purity (contract 1), closure (contract 2), and rule 9's "effects land next tick"
all hold: a phase reads only the state it is handed, the boundary is a property of
the grid rather than of a shell, and every wake is applied at tick end. Cost
(`C3`) is carried by the dirty-row work set (`V0-4b-3b`, A.77), and support is
derived from the neighbourhood (`V0-5`, A.81). What is *not* yet closed is the
**ground**: the live window is shell-free, so `Support` has no base case and the
world is born fully awake (`G-scale-9`). No deviation is closed by rewording a
rule to match the code.

Ambition (in the open)

This is not a demo, and it isn't trying to be one. The ASCII and windowed
front-ends exist only to keep the model visible and honest. The ambition is a
small, complete rule system whose determinism, conservation, stability, and
scalability are properties of the design rather than features layered on top —
a reference engine that is free to mature slowly.

"Scalable" means, concretely: world size is a parameter rather than a constant;
a tick's cost is proportional to the disturbed set, so a large world with a
small active core ticks in time set by the core; and phases are parallel by
construction, so the same tick runs on many cores with no coordination and no
change of answer.
