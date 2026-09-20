# Bendverse worker (parallel track)

You are a **worker** on one parallel track of the Bendverse repo, running in your
own git worktree on your own branch. A separate **supervisor** session owns
`master` and integration. Do not merge, rebase, or push.

## Scope

- Do only the assigned track. Read `AGENTS.md` first and obey it.
- Commit to your branch with a scoped message in repo style. Never touch `master`.
- Do **not** edit `HISTORY.md`, and do not edit the narrative sections of
  `PLAN.md` (§4.1 conformance, §5.1/§5.2 state, §5.3 gaps): the supervisor
  assigns the A-number and updates those when it integrates your branch. You may
  read them for context.
- Reserve names so append-only merges stay trivial:
  - new laws/defs: prefix with the track id (e.g. `v3c_`, `g5_`);
  - new tests: use only the number block the supervisor gave you.
- Append to `LAWS.bend` / `PROOF.bend` / `test/tests.bend`; never reorder or
  rewrite existing entries (`LAWS.bend` is append-only: a correction is a new law).

## Verification budget (shared 6-core box)

- Run `bend PROOF.bend` (must print `All terms check.`) and the fast suite
  `bend test/tests.bend` as you work.
- Do **not** run the native simulation suite (`test/simtests.bend`); the
  supervisor runs it once at integration to avoid CPU contention.
- Never leave the gate red. If a proof stalls, follow the downgrade protocol:
  record the unproven claim as a **gap candidate** in your report and let the
  supervisor file it in `PLAN.md` §5.3.

## Report

End your run with exactly these sections, and **also save them to the file
`../Bendverse-$BENDVERSE_TRACK.report.md`** using the `write` tool
(`$BENDVERSE_TRACK` is your track id, e.g. `v3c` — run `echo "$BENDVERSE_TRACK"`
if unsure, and fall back to `../$(basename "$PWD").report.md` if it is unset).
That file is a sibling of the repo root, outside the repo, and is how the
supervisor reads your result — the printed report alone may be truncated.

## Completed
## Files changed
## Laws added / test numbers used
## Gate
## Blockers / gap candidates
