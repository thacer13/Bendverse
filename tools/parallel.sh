#!/usr/bin/env bash
# Parallel tracks: one git worktree + branch per track, driven by a single
# supervisor session that owns master and integration.
#
# Shared plumbing. This file is byte-identical in Bendview and Bendverse and
# derives the repo name at runtime; keep it that way (change one, change the
# other). Project-specific worker rules live in tools/worker-prompt.md, which
# `dispatch` passes as the worker's role.
#
# Why worktrees: wall-clock, not tokens, is the scarce resource, and two writers
# in one working tree lose work. Separate worktrees isolate edits and per-cwd
# scratch files; the supervisor dispatches workers here and integrates their
# branches itself.
#
# Dispatch backend (chosen automatically):
#   - inside Herdr (HERDR_ENV=1): each worker is an interactive `pi` in its own
#     Herdr pane (watchable; Herdr tracks its idle/working/blocked/done state);
#     the pane output is captured to the log.
#   - otherwise: a headless `pi -p`, output captured to the log.
#
# Usage:
#   tools/parallel.sh new <track>             # worktree ../<Repo>-<track> on branch <track>
#   tools/parallel.sh dispatch <track> "task" # run a worker in that worktree
#   tools/parallel.sh list                    # worktrees
#   tools/parallel.sh rm <track>              # remove worktree (keeps unmerged branch)
#   tools/parallel.sh reap [<track>...]       # close leaked worker panes (no args:
#                                             # idle workers whose worktree is gone)
#
# Env knobs (REPO-prefixed names, e.g. BENDVIEW_SPLIT, also work):
#   TRACK_SPLIT=right|down   Herdr pane split direction (default right; use
#                            down for the second concurrent worker)
#   TRACK_KEEP_PANES=1       leave finished Herdr panes open (default: close)
#   TRACK_TIMEOUT_MS=...     Herdr worker wait timeout (default 3600000)
#
# Worker output is captured to ../<Repo>-<track>.log; the worker also writes
# ../<Repo>-<track>.report.md (its own final report).
set -euo pipefail

ROOT=$(cd "$(dirname "$0")/.." && pwd)
BASE=$(basename "$ROOT")
PARENT=$(dirname "$ROOT")
PREFIX=$(printf '%s' "$BASE" | tr '[:lower:]' '[:upper:]')
WT="$PARENT/$BASE-"      # worktree prefix
LOG="$PARENT/$BASE-"     # log/report prefix

# A knob is read as generic TRACK_<name>, then repo-prefixed <PREFIX>_<name>.
knob() { printenv "TRACK_$1" 2>/dev/null || printenv "${PREFIX}_$1" 2>/dev/null || true; }
SPLIT=$(knob SPLIT); SPLIT=${SPLIT:-right}
TIMEOUT_MS=$(knob TIMEOUT_MS); TIMEOUT_MS=${TIMEOUT_MS:-3600000}
KEEP_PANES=$(knob KEEP_PANES)

# A dispatch that is killed (e.g. the supervisor's tool timeout) must not leak
# its Herdr pane: record it here and close it on EXIT/INT/TERM. On the normal
# path the pane is closed and ACTIVE_PANE cleared, so the trap is a no-op.
# TRACK_KEEP_PANES=1 disables both.
ACTIVE_PANE=""
cleanup_pane() {
  if [ -n "$ACTIVE_PANE" ] && [ "$KEEP_PANES" != 1 ]; then
    herdr pane close "$ACTIVE_PANE" >/dev/null 2>&1 || true
  fi
}
trap cleanup_pane EXIT INT TERM

usage() { sed -n '2,40p' "$0"; }

cmd=${1:-}
shift || true

# Headless worker: `pi -p`, output tee'd to the log.
dispatch_pi() { # track worktree task log
  local t=$1 p=$2 task=$3 l=$4
  ( cd "$p" && env "${PREFIX}_TRACK=$t" TRACK="$t" pi -p --approve \
      --append-system-prompt "$ROOT/tools/worker-prompt.md" \
      "$task" ) 2>&1 | tee "$l"
}

# Watchable worker: interactive `pi` in a Herdr pane, then capture the pane.
dispatch_herdr() { # track worktree task log
  local t=$1 p=$2 task=$3 l=$4
  command -v herdr >/dev/null || { echo "HERDR_ENV=1 but herdr not on PATH" >&2; return 1; }
  command -v jq >/dev/null || { echo "HERDR_ENV=1 but jq not on PATH" >&2; return 1; }
  local pane target=(--current)
  if [ -n "${HERDR_PANE_ID:-}" ]; then target=(--pane "$HERDR_PANE_ID"); fi
  pane=$(herdr pane split "${target[@]}" --direction "$SPLIT" --cwd "$p" \
           --env "${PREFIX}_TRACK=$t" --env "TRACK=$t" --no-focus | jq -r '.result.pane.pane_id')
  if [ -z "$pane" ] || [ "$pane" = "null" ]; then
    echo "herdr pane split returned no pane id" >&2; return 1
  fi
  ACTIVE_PANE="$pane"
  # Launch interactive pi with the worker role, then submit the task and wait.
  herdr agent start "$t" --kind pi --pane "$pane" --timeout 60000 -- \
    --approve --append-system-prompt "$ROOT/tools/worker-prompt.md" >/dev/null
  herdr agent prompt "$t" "$task" --wait --timeout "$TIMEOUT_MS" >/dev/null \
    || echo "note: worker did not settle cleanly (blocked/stalled?) — captured anyway" >&2
  herdr agent read "$t" --source recent --lines 400 --format text > "$l" 2>&1 || true
  if [ "$KEEP_PANES" != 1 ]; then
    herdr pane close "$pane" >/dev/null 2>&1 || true
  fi
  ACTIVE_PANE=""
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
  reap)
    command -v herdr >/dev/null || { echo "herdr not on PATH" >&2; exit 1; }
    command -v jq >/dev/null || { echo "jq not on PATH" >&2; exit 1; }
    if [ "$#" -gt 0 ]; then
      for t in "$@"; do
        pane=$(herdr agent list | jq -r --arg n "$t" '.result.agents[] | select(.name==$n) | .pane_id' | head -1)
        if [ -n "$pane" ] && [ "$pane" != null ]; then
          echo "closing $t ($pane)"; herdr pane close "$pane" >/dev/null 2>&1 || true
        else
          echo "no pane for $t" >&2
        fi
      done
    else
      herdr agent list | jq -r '.result.agents[] | select(.name != null) | [.name,.pane_id,.cwd] | @tsv' |
      while IFS=$'\t' read -r name pane cwd; do
        case "$cwd" in
          *"$BASE"-*)
            if [ ! -d "$cwd" ]; then
              echo "closing leaked pane $pane ($name; worktree gone)"
              herdr pane close "$pane" >/dev/null 2>&1 || true
            fi ;;
        esac
      done
    fi
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
