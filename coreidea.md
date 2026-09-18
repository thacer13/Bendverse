Core Model

The world is a 3D grid of cells. Each cell holds exactly one material (including "empty"). There are no objects, no entities, no rigid bodies — a "rock" or "boulder" is just a contiguous region of cells sharing a material and a cohesion property. Everything that happens, happens through local cell rules evaluated identically everywhere, every tick.

The Immutable Rules

1. Locality
A cell's next state depends only on itself and its neighbors within a fixed, small radius (typically the 6 or 26 adjacent cells). No cell may read or write anything outside that neighborhood. This is the rule that makes parallelism legal — it's the one constraint everything else must obey.

2. Conservation
Material is never created or destroyed, only moved or transformed by an explicit rule (e.g., "rock → rubble on impact"). Every movement is a swap or transfer between two specific cells, never a copy.

3. Single-writer per cell, per tick
Exactly one rule application may resolve to writing a given cell in a given tick. If multiple neighbors "want" to move into the same empty cell simultaneously, a deterministic tie-break (priority order, or reject-and-retry) decides — never a silent overwrite. This is the race condition rule; everything else can be sloppy, this one can't.

4. Phase separation (the parallelism contract)
A tick is divided into fixed sub-phases (e.g., an even/odd or 8-cell parity partition in 3D). Within a single phase, no two cells being updated are neighbors of each other. This guarantees every cell update in a phase can run fully in parallel with zero coordination. Rules are written once; the phase-splitting is a scheduling concern, not a rule-author concern.

5. Falling is universal
Every non-static material obeys the same base rule: if the cell below is lower-density-or-empty, move down; else if a diagonal-below cell is lower-density-or-empty, move there. Materials differ only in their density and angle of repose (how readily they slide diagonally vs. stack vertically), not in having different fall logic.

6. Cohesion determines rigidity, not material type
A cell has a cohesion value. High cohesion = it does not independently obey the falling rule; instead it moves only as part of a connected cohesive cluster, and only when that cluster's support (contact with static or sufficiently-supported cells) drops below a threshold. Low cohesion = it obeys rule 5 individually every tick. Rigidity is a value on a spectrum, not a separate object type — this is what unifies "sand" and "boulder" under one system.

7. Support is recomputed, never cached across structural change
Whenever a cell's neighborhood changes (something removed, added, or moved nearby), support/cohesion state must be re-derived from current neighbors, not carried forward. This is what makes collapse "honest" — pull a base cell out and everything depending on it re-evaluates, cascading naturally rather than needing scripted triggers.

8. Impact is a threshold event, not a force simulation
No velocities, no momentum accumulation, no continuous collision. A moving cell (falling or thrown) that would enter an occupied cell instead resolves as a discrete impact event: if incoming "energy" (derived simply from fall distance/speed) exceeds the target's cohesion threshold, the target's cohesion is reduced or it converts material (rock → rubble); otherwise the mover stops. This keeps the whole system rule-based and local instead of needing a physics solver.

9. Activity is explicit, not implicit
A cell is only evaluated if it is marked active (recently changed, or adjacent to something active). A cell that hasn't changed and has no active neighbor does no work and costs nothing. Activity propagates outward by one rule: any write to a cell marks its neighbors active next tick. This is what makes "infinite" viable — cost is proportional to disturbance, not world size.

10. Determinism within a tick, not across scheduling
Given the same starting state and the same tie-break rule (#3), the result of a tick is identical regardless of how work was distributed across processors. Parallelism may change when things are computed, never what the answer is.

11. World generation is a pure seeding function, not a system
For any cell coordinate, there exists a pure function f(x, y, z) → material, parameters that depends only on the coordinate itself (and a fixed global seed) — never on generation order, neighboring chunks' generation status, or simulation history. A chunk's initial state is produced by sampling this function once per cell within it, with every cell marked inactive (per rule 9). This function may internally layer multiple scalar fields (e.g., macro-scale for base terrain shape, higher-frequency for material selection, sparse fields for isolated features) — but externally it must behave as a single pure lookup: same coordinate, same seed, same result, regardless of when or in what order it's called.

Ambition (in the open)

This is not really a demo, and it isn't trying to be one. The ASCII and windowed front-ends exist only to keep the model visible and honest. The ambition is a small, complete rule system whose determinism, conservation, stability, and scalability are properties of the design rather than features layered on top — a reference engine that is free to mature slowly. Parallelism and chunking are sketched, not claimed; the verified kernels are real. The demo can be as plain as it likes.
