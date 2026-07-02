#!/usr/bin/env bash
# lint-simp-nf.sh — enforce simp normal form (Mathlib's `simpNF` environment linter)
# with a grandfathered baseline.
#
# Why not `lake exe runLinter TauCeti`: the root TauCeti.lean is intentionally empty
# (the lakefile glob is authoritative for what gets built), so runLinter would lint an
# empty environment and pass vacuously. Instead we generate a driver module that
# imports every `TauCeti/**/*.lean` module and runs `#lint only simpNF in TauCeti`,
# elaborate it against the already-built oleans (`lake env lean`), and parse the
# violations out of the linter's report.
#
# Violations that predate this check are grandfathered in scripts/simp-nf-baseline.txt
# (sorted declaration names, one per line):
#   - a violating declaration NOT in the baseline is a NEW violation  -> exit 1;
#   - a baseline entry that no longer violates is printed as a RATCHET reminder
#     (delete it from the baseline in a follow-up PR), without failing.
#
# Run from the repo root (or anywhere; it cd's to the root) AFTER `lake build` — it
# needs the compiled oleans. It does no network I/O and writes only under $TMPDIR, so
# it is safe inside the pr-build landrun sandbox. Usage:
#
#   scripts/lint-simp-nf.sh            # check against the baseline
#   scripts/lint-simp-nf.sh --update   # rewrite the baseline from the current state
set -uo pipefail

cd "$(dirname "$0")/.."
BASELINE="scripts/simp-nf-baseline.txt"
UPDATE=0
[ "${1:-}" = "--update" ] && UPDATE=1

fail() { echo "::error::simp-nf: $*"; echo "SIMP-NF: FAIL — $*"; exit 1; }

TMP="$(mktemp -d)" || fail "mktemp failed"
trap 'rm -rf "$TMP"' EXIT

# --- 1. generate the driver: import every TauCeti module, lint only simpNF ------
# `set_option linter.hashCommand false` because the driver is generated, not committed;
# the style linter would otherwise flag the bare `#lint`.
{
  echo "module"
  find TauCeti -name '*.lean' | LC_ALL=C sort \
    | sed 's/\.lean$//; s|/|.|g; s/^/public import /'
  echo
  echo "set_option linter.hashCommand false in"
  echo "#lint only simpNF in TauCeti"
} > "$TMP/SimpNFDriver.lean"
mods=$(grep -c '^public import ' "$TMP/SimpNFDriver.lean") || true
[ "${mods:-0}" -gt 0 ] || fail "found no TauCeti/*.lean modules — the lint is miswired"

# --- 2. elaborate it (exit 1 from lean just means the linter found violations) --
lake env lean "$TMP/SimpNFDriver.lean" > "$TMP/out.txt" 2>&1
status=$?

# One `#check <decl> /- <reason> -/` block per violation (with or without a leading
# `@`, depending on the declaration's binders).
LC_ALL=C sed -n 's/^#check @\{0,1\}\([^ ]*\) .*/\1/p' "$TMP/out.txt" | LC_ALL=C sort -u \
  > "$TMP/violations.txt"

if [ "$status" -ne 0 ] && ! [ -s "$TMP/violations.txt" ]; then
  # lean failed but not with a parseable linter report: a broken import/driver, not lint.
  cat "$TMP/out.txt"
  fail "driver elaboration failed (lean exit $status) without a simpNF report — see output above"
fi
if [ "$status" -eq 0 ] && [ -s "$TMP/violations.txt" ]; then
  fail "internal inconsistency: lean exited 0 but violations were parsed"
fi

total=$(wc -l < "$TMP/violations.txt")
echo "simp-nf: linted $mods modules; $total declaration(s) not in simp normal form."

# --- 3. --update: rewrite the baseline and stop ---------------------------------
if [ "$UPDATE" = 1 ]; then
  cp "$TMP/violations.txt" "$BASELINE"
  echo "simp-nf: wrote $total grandfathered declaration(s) to $BASELINE."
  exit 0
fi

# --- 4. compare against the grandfathered baseline ------------------------------
[ -f "$BASELINE" ] || fail "baseline $BASELINE not found — run scripts/lint-simp-nf.sh --update to create it"
LC_ALL=C sort -u "$BASELINE" > "$TMP/baseline.txt"

# Baseline entries that no longer violate: a ratchet reminder, never a failure.
LC_ALL=C comm -13 "$TMP/violations.txt" "$TMP/baseline.txt" > "$TMP/fixed.txt"
if [ -s "$TMP/fixed.txt" ]; then
  echo
  echo "simp-nf: RATCHET — $(wc -l < "$TMP/fixed.txt") baseline entr(y/ies) no longer violate simpNF."
  echo "Please delete these lines from $BASELINE (a follow-up PR is fine):"
  sed 's/^/  /' "$TMP/fixed.txt"
fi

# Violations not in the baseline: new debt — fail, and show the linter's reasoning.
LC_ALL=C comm -23 "$TMP/violations.txt" "$TMP/baseline.txt" > "$TMP/new.txt"
if [ -s "$TMP/new.txt" ]; then
  echo
  echo "simp-nf: NEW simpNF violation(s) not in the grandfathered baseline:"
  awk 'NR==FNR { want[$0]=1; next }
       /^#check / { name=$2; sub(/^@/, "", name); p = (name in want) }
       p { print "  " $0 }
       p && /-\/[[:space:]]*$/ { p=0; print "" }' "$TMP/new.txt" "$TMP/out.txt"
  echo "Fix the lemma so its left-hand side is in simp normal form (see the linter's"
  echo "suggestion above), remove the @[simp] attribute, or use @[nolint simpNF] with a"
  echo "comment when the lemma is a deliberate exception."
  fail "$(wc -l < "$TMP/new.txt") new simpNF violation(s); see the list above"
fi

echo "SIMP-NF: PASS — no new violations ($total grandfathered, $(wc -l < "$TMP/fixed.txt") ratchetable)."
