#!/usr/bin/env bash
# Parallel tracks for Bendverse: one git worktree + branch per track, driven by a
# single supervisor session that owns master and integration.
#
# Why: wall-clock is the scarce resource, and Bend checks use all 6 cores. Two
# writers in one working tree lose work; separate worktrees isolate edits, the
# per-cwd scratch files (`.bendverse-*.bend`), and the per-basename native cache
# (`$TMPDIR/bendverse/<basename>-simtests`). The supervisor dispatches workers
# here and integrates their branches itself.
#
# Usage:
#   tools/parallel.sh new <track>            # worktree ../Bendverse-<track> on branch <track>
#   tools/parallel.sh dispatch <track> "task" # run a worker (pi -p) in that worktree
#   tools/parallel.sh list                   # worktrees
#   tools/parallel.sh rm <track>             # remove worktree (keeps unmerged branch)
#
# The worker role/protocol lives in tools/worker-prompt.md; the task string is
# only the track-specific part. Worker output is tee'd to
# ../Bendverse-<track>.log so the supervisor can read it back cheaply.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
BASE=$(basename "$ROOT")
PARENT=$(dirname "$ROOT")
WT="$PARENT/$BASE-"      # worktree prefix
LOG="$PARENT/$BASE-"     # log prefix

usage() { sed -n '2,20p' "$0"; }

cmd=${1:-}
shift || true

case "$cmd" in
  new)
    t=${1:?usage: parallel.sh new <track>}
    p="$WT$t"
    if [ -e "$p" ]; then echo "already exists: $p" >&2; exit 1; fi
    git -C "$ROOT" worktree add "$p" -b "$t" master
    echo "$p"
    ;;
  rm)
    t=${1:?usage: parallel.sh rm <track>}
    p="$WT$t"
    git -C "$ROOT" worktree remove "$p"
    git -C "$ROOT" branch -d "$t" 2>/dev/null || echo "branch $t kept (not merged)" >&2
    ;;
  list)
    git -C "$ROOT" worktree list
    ;;
  dispatch)
    t=${1:?usage: parallel.sh dispatch <track> "<task>"}; shift
    task=${1:?usage: parallel.sh dispatch <track> "<task>"}
    p="$WT$t"
    if [ ! -d "$p" ]; then echo "no worktree $p (run: parallel.sh new $t)" >&2; exit 1; fi
    l="$LOG$t.log"
    ( cd "$p" && pi -p --approve \
        --append-system-prompt "$ROOT/tools/worker-prompt.md" \
        "$task" ) 2>&1 | tee "$l"
    ;;
  *)
    usage; exit 2
    ;;
esac
