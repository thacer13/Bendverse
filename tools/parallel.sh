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
# Dispatch backend (chosen automatically):
#   - inside Herdr (HERDR_ENV=1): each worker is an interactive `pi` in its own
#     Herdr pane, so the human can watch it and Herdr tracks its
#     idle/working/blocked/done state; the pane output is captured to the log.
#   - otherwise: a headless `pi -p`, output captured to the log.
# The worktree/branch protocol is identical either way.
#
# Usage:
#   tools/parallel.sh new <track>             # worktree ../Bendverse-<track> on branch <track>
#   tools/parallel.sh dispatch <track> "task" # run a worker in that worktree
#   tools/parallel.sh list                    # worktrees
#   tools/parallel.sh rm <track>              # remove worktree (keeps unmerged branch)
#
# Env knobs:
#   BENDVERSE_SPLIT=right|down   Herdr pane split direction (default right; use
#                                down for the second concurrent worker)
#   BENDVERSE_KEEP_PANES=1       leave finished Herdr panes open (default: close)
#   BENDVERSE_TIMEOUT_MS=...     Herdr worker wait timeout (default 3600000)
#
# Worker output is captured to ../Bendverse-<track>.log; the worker also writes
# ../Bendverse-<track>.report.md (its own final report) so the supervisor has a
# clean result either way.
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
BASE=$(basename "$ROOT")
PARENT=$(dirname "$ROOT")
WT="$PARENT/$BASE-"      # worktree prefix
LOG="$PARENT/$BASE-"     # log/report prefix
SPLIT=${BENDVERSE_SPLIT:-right}
TIMEOUT_MS=${BENDVERSE_TIMEOUT_MS:-3600000}

usage() { sed -n '2,30p' "$0"; }

cmd=${1:-}
shift || true

# Headless worker: `pi -p`, output tee'd to the log.
dispatch_pi() { # track worktree task log
  local t=$1 p=$2 task=$3 l=$4
  ( cd "$p" && BENDVERSE_TRACK="$t" pi -p --approve \
      --append-system-prompt "$ROOT/tools/worker-prompt.md" \
      "$task" ) 2>&1 | tee "$l"
}

# Watchable worker: interactive `pi` in a Herdr pane, then capture the pane.
dispatch_herdr() { # track worktree task log
  local t=$1 p=$2 task=$3 l=$4
  command -v herdr >/dev/null || { echo "HERDR_ENV=1 but herdr not on PATH" >&2; return 1; }
  command -v jq >/dev/null || { echo "HERDR_ENV=1 but jq not on PATH" >&2; return 1; }
  local pane
  pane=$(herdr pane split --current --direction "$SPLIT" --cwd "$p" \
           --env "BENDVERSE_TRACK=$t" --no-focus | jq -r '.result.pane.pane_id')
  if [ -z "$pane" ] || [ "$pane" = "null" ]; then
    echo "herdr pane split returned no pane id" >&2; return 1
  fi
  # Launch interactive pi with the worker role, then submit the task and wait.
  herdr agent start "$t" --kind pi --pane "$pane" --timeout 60000 -- \
    --approve --append-system-prompt "$ROOT/tools/worker-prompt.md" >/dev/null
  herdr agent prompt "$t" "$task" --wait --timeout "$TIMEOUT_MS" >/dev/null \
    || echo "note: worker did not settle cleanly (blocked/stalled?) — captured anyway" >&2
  herdr agent read "$t" --source recent --lines 400 --format text > "$l" 2>&1 || true
  if [ "${BENDVERSE_KEEP_PANES:-}" != 1 ]; then
    herdr pane close "$pane" >/dev/null 2>&1 || true
  fi
  cat "$l"
}

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
    if [ "${HERDR_ENV:-}" = 1 ]; then
      dispatch_herdr "$t" "$p" "$task" "$l"
    else
      dispatch_pi "$t" "$p" "$task" "$l"
    fi
    ;;
  *)
    usage; exit 2
    ;;
esac
