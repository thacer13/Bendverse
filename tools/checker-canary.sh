#!/usr/bin/env bash
# Checker canaries for Bendverse.
#
# Purpose: proof integrity, not performance. Bend's `{==}` discharges
# *definitional* equality, so a change in what the checker reduces can turn into
# a soundness or understanding problem, not just a slow compile:
#   - a POSITIVE canary that stops checking  => missing/stuck normalization;
#   - a NEGATIVE canary that starts checking => over-eager normalization
#     (the checker accepting something it must not) -- a soundness alarm.
#
# Each file in tools/canaries/ is named *.pass.bend or *.fail.bend. Run:
#   tools/checker-canary.sh            # default 45s per canary
#   CANARY_TIMEOUT=90 tools/checker-canary.sh
#
# A timeout on a *pass* canary is reported separately: it is the A.41-A.42
# expansion cliff, not a wrong answer.
set -u
cd "$(dirname "$0")/.."
T=${CANARY_TIMEOUT:-45}
dir=tools/canaries
ok=0 bad=0
printf 'checker canaries (timeout %ss, cwd %s)\n' "$T" "$PWD"
for f in "$dir"/*.bend; do
  base=$(basename "$f")
  case "$base" in
    *.pass.bend) want=pass ;;
    *.fail.bend) want=fail ;;
    *) printf '  skip %-32s (name must contain .pass./.fail.)\n' "$base"; continue ;;
  esac
  out=$(env BEND_NO_TELEMETRY=1 timeout --kill-after=5 "$T" bend "$f" 2>&1)
  rc=$?
  if [ "$rc" -eq 124 ]; then got=timeout
  elif printf '%s' "$out" | grep -q 'All terms check\.'; then got=pass
  else got=fail; fi
  if [ "$got" = "$want" ]; then
    printf '  ok    %-32s %s\n' "$base" "$got"; ok=$((ok + 1))
  elif [ "$got" = timeout ]; then
    printf '  CLIFF %-32s expected %s, TIMED OUT after %ss (see PLAN 7)\n' "$base" "$want" "$T"; bad=$((bad + 1))
  else
    printf '  BAD   %-32s expected %s, got %s\n' "$base" "$want" "$got"; bad=$((bad + 1))
  fi
done
printf 'canaries: %d ok, %d bad\n' "$ok" "$bad"
[ "$bad" -eq 0 ]
