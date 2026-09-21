# Bendverse

Bendverse is a machine-checked reference engine for scalable falling-sand
cellular simulation. The engine is `src/` (pure, zero IO); the properties that
make scaling sound — determinism, conservation, settling — are stated in
`LAWS.bend` and checked by `PROOF.bend`.

The render frontend is the sister project **Bendview** (`../Bendview`). It
consumes the engine through `runners/export.bend` (the `.bvs`/`.bvg`/`.bgt`
binary oracles) and the `runners/serve.bend` sidecar link (`runners/SERVE.md`).

## Verify

    bend PROOF.bend          # the gate: must print "All terms check."
    bend test/tests.bend     # fast, tick-free suite

    bend test/simtests.bend -o bin/simtests && ./bin/simtests   # native sim suite

The native sim suite is the one that exercises ticks; run it natively, not in JS.

## Layout

- `src/` — the pure engine (zero IO): `cell`, `grid`, `worldgen`, `rules`,
  `support`, `ops`, `sim`, `dirty`, `chunk`/`store`, plus the verification
  layers (`settle`/`parity`/`mod`/`priority`/`order`/`fall`/`bits`/`nat`/`list`).
- `runners/` — thin front-ends for visibility only, not part of the engine:
  `ascii.bend` (headless cross-section), `window.bend` (2D `App.run` sandbox),
  `view3d.bend` (native voxel viewer), `export.bend` (binary oracles),
  `serve.bend` (the Bendview sidecar).
- `test/` — verification witnesses (`tests.bend` fast, `simtests.bend` native).
- `PROOF.bend` / `LAWS.bend` — the machine-checked claims.
- `coreidea.md` (contract), `PLAN.md` (plan, gaps), `SCALE.md` (window
  migration), `HISTORY.md` (milestones).

The runners are development conveniences; the supported renderer is Bendview.
