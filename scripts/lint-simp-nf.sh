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
# (LC_ALL=C sorted declaration names, one per line, no duplicates):
#   - a violating declaration NOT in the baseline is a NEW violation  -> exit 1;
#   - a baseline entry that no longer violates is printed as a RATCHET reminder
#     (delete it from the baseline in a follow-up PR), without failing.
#
# `@[nolint simpNF]` ratchet: silencing the linter per-declaration would bypass the
# baseline, so every occurrence of the string `nolint simpNF` under TauCeti/ must be
# accounted for in scripts/simp-nf-nolints-allowlist.txt (lines of `<file>:<count>`,
# LC_ALL=C sorted). Growing that allowlist must go through the same human-reviewed
# path as this script — it is exactly the hole an auto-merged PR would otherwise use.
#
# SECURITY MODEL (this script elaborates the PR's own code, so treat its output as
# partially attacker-controlled):
#   * The linter's report starts with a header line
#       -- Found N error(s) in M declarations (plus ...) in TauCeti with K linters
#     followed (when N > 0) by one `#check <decl> /- ... -/` block per violation.
#     When N > 0 the report is an error diagnostic, so the header carries the
#     `<driver>:<line>:<col>: error: ` prefix of our own driver file (a fresh mktemp
#     path) and lean exits nonzero; when N = 0 it is an info message printed bare.
#     We require EXACTLY ONE header in the output, of the form matching the exit
#     code (anchored error header + N > 0 for a nonzero exit; bare header + N = 0
#     for a zero exit), we count `#check` lines only AFTER the header, and we
#     require that count to equal N.
#   * PR code can print arbitrary text at import time (initializers): a forged header
#     printed alongside the real one yields two headers -> fail, and a forged smaller
#     report cannot suppress the real report's `error:` diagnostic or lean's nonzero
#     exit. Forged `#check` lines make the count disagree with N -> fail.
#   * The remaining forgery needs the process to die before `#lint` runs while having
#     already printed a single self-consistent PASSING report. Commands after a failed
#     command still elaborate, so we append a `#eval` printing a per-run random nonce
#     after the `#lint`, and require that marker AFTER the header: an early exit(0)
#     forgery must also predict the nonce.
#   * Residual risk (accepted): initializer code could read /proc/self/cmdline to
#     learn the driver path AND read the driver file to learn the nonce, then forge a
#     passing report and exit(0) before `#lint`. Any lint that elaborates untrusted
#     code has this ceiling; the pr-build landrun sandbox plus human review of
#     suspicious `initialize`/`@[init]` code are the outer defense. Everything short
#     of that deliberate two-step forgery fails closed.
#
# Run from the repo root (or anywhere; it cd's to the root) AFTER `lake build` — it
# needs the compiled oleans. It does no network I/O and writes only under $TMPDIR, so
# it is safe inside the pr-build landrun sandbox. Usage:
#
#   scripts/lint-simp-nf.sh            # check against the baseline
#   scripts/lint-simp-nf.sh --update   # rewrite the baseline from the current state
set -euo pipefail

cd "$(dirname "$0")/.."
BASELINE="scripts/simp-nf-baseline.txt"
ALLOWLIST="scripts/simp-nf-nolints-allowlist.txt"
UPDATE=0
[ "${1:-}" = "--update" ] && UPDATE=1

fail() { echo "::error::simp-nf: $*"; echo "SIMP-NF: FAIL — $*"; exit 1; }

TMP="$(mktemp -d)" || fail "mktemp failed"
trap 'rm -rf "$TMP"' EXIT
DRIVER="$TMP/SimpNFDriver.lean"

# --- 0. `@[nolint simpNF]` ratchet (cheap, source-only: run before the build) ----
[ -f "$ALLOWLIST" ] || fail "allowlist $ALLOWLIST not found — it must be checked in (empty is fine)"
LC_ALL=C sort -cu "$ALLOWLIST" 2>/dev/null \
  || fail "$ALLOWLIST is not sorted/duplicate-free — fix it with: LC_ALL=C sort -u -o $ALLOWLIST $ALLOWLIST"
{ grep -rc 'nolint simpNF' --include='*.lean' TauCeti || true; } \
  | { grep -v ':0$' || true; } | LC_ALL=C sort > "$TMP/nolints.txt"
LC_ALL=C comm -23 "$TMP/nolints.txt" "$ALLOWLIST" > "$TMP/nolints-new.txt"
if [ -s "$TMP/nolints-new.txt" ]; then
  echo "simp-nf: 'nolint simpNF' occurrence(s) under TauCeti/ not accounted for in $ALLOWLIST:"
  sed 's/^/  /' "$TMP/nolints-new.txt"
  echo "Silencing the simpNF linter bypasses the baseline. If a @[nolint simpNF] is truly"
  echo "warranted, add/adjust the '<file>:<count>' line in $ALLOWLIST in the same PR —"
  echo "that file, like this script, must only change via human-reviewed PRs (never via"
  echo "an auto-merged one)."
  fail "unaccounted 'nolint simpNF' occurrence(s); see the list above"
fi
LC_ALL=C comm -13 "$TMP/nolints.txt" "$ALLOWLIST" > "$TMP/nolints-fixed.txt"
if [ -s "$TMP/nolints-fixed.txt" ]; then
  echo "simp-nf: RATCHET — allowlist entr(y/ies) in $ALLOWLIST no longer match the sources;"
  echo "please update/remove these lines (a follow-up PR is fine):"
  sed 's/^/  /' "$TMP/nolints-fixed.txt"
fi

# --- 0b. validate the baseline before spending minutes on elaboration ------------
if [ "$UPDATE" != 1 ]; then
  [ -f "$BASELINE" ] || fail "baseline $BASELINE not found — run scripts/lint-simp-nf.sh --update to create it"
  LC_ALL=C sort -cu "$BASELINE" 2>/dev/null \
    || fail "$BASELINE is not sorted/duplicate-free — fix it with: LC_ALL=C sort -u -o $BASELINE $BASELINE"
fi

# --- 1. generate the driver: import every TauCeti module, lint only simpNF -------
# `set_option linter.hashCommand false` because the driver is generated, not committed;
# the style linter would otherwise flag the bare `#lint`/`#eval`. The trailing `#eval`
# prints a per-run nonce proving the process survived past `#lint` (see SECURITY MODEL).
NONCE="$(od -An -N16 -tx8 /dev/urandom | tr -d ' \n')" || fail "nonce generation failed"
MARKER="SIMPNF-DRIVER-COMPLETE-$NONCE"
{
  echo "module"
  find TauCeti -name '*.lean' | LC_ALL=C sort \
    | sed 's/\.lean$//; s|/|.|g; s/^/public import /'
  echo
  echo "set_option linter.hashCommand false in"
  echo "#lint only simpNF in TauCeti"
  echo
  echo "set_option linter.hashCommand false in"
  echo "#eval IO.println \"$MARKER\""
} > "$DRIVER"
mods=$(grep -c '^public import ' "$DRIVER" || true)
[ "${mods:-0}" -gt 0 ] || fail "found no TauCeti/*.lean modules — the lint is miswired"

# --- 2. elaborate it (exit 1 from lean is EXPECTED when the linter reports) ------
if lake env lean "$DRIVER" > "$TMP/out.txt" 2>&1; then
  status=0
else
  status=$?
fi

# --- 3. locate the linter's own report and parse it fail-closed ------------------
# Two genuine header shapes (see SECURITY MODEL): N > 0 comes as an error diagnostic
# prefixed with our driver's path; N = 0 comes as a bare info line. Collect both.
awk -v pfx="$DRIVER:" '
  BEGIN { hdr = "-- Found [0-9]+ errors? in [0-9]+ declarations \\(plus [0-9]+ automatically generated ones\\) in TauCeti with [0-9]+ linters$" }
  {
    if (index($0, pfx) == 1) {
      rest = substr($0, length(pfx) + 1)
      if (rest ~ ("^[0-9]+:[0-9]+: error: " hdr)) { print NR " error " rest; next }
    }
    if ($0 ~ ("^" hdr)) print NR " bare " $0
  }' "$TMP/out.txt" > "$TMP/headers.txt"

nheaders=$(wc -l < "$TMP/headers.txt")
if [ "$nheaders" -ne 1 ]; then
  cat "$TMP/out.txt"
  if [ "$nheaders" -eq 0 ]; then
    fail "driver/linter failure: no simpNF report header found (lean exit $status) — see output above"
  fi
  fail "driver/linter failure: $nheaders report headers found (possible forged report) — see output above"
fi

hdr_lineno=$(awk '{print $1}' "$TMP/headers.txt")
hdr_kind=$(awk '{print $2}' "$TMP/headers.txt")
hdr_count=$(sed -n 's/^.*-- Found \([0-9]*\) errors\{0,1\} in .*/\1/p' "$TMP/headers.txt")
[ -n "$hdr_kind" ] && [ -n "$hdr_count" ] || fail "internal error: could not re-parse the report header"

# The report region: everything after the header. The completion marker must appear
# there — it is only printed once elaboration gets PAST the `#lint` command.
tail -n +"$((hdr_lineno + 1))" "$TMP/out.txt" > "$TMP/report.txt"
if ! grep -qF "$MARKER" "$TMP/report.txt"; then
  cat "$TMP/out.txt"
  fail "driver/linter failure: driver did not run to completion (missing nonce marker) — see output above"
fi

# Exit code, header kind, and count must agree: violations mean an anchored error
# header AND a nonzero exit; a clean lint means a bare header with N = 0 AND exit 0.
case "$hdr_kind:$status" in
  error:0) cat "$TMP/out.txt"; fail "driver/linter failure: lint reported errors but lean exited 0" ;;
  bare:0)  if [ "$hdr_count" -ne 0 ]; then
             cat "$TMP/out.txt"
             fail "driver/linter failure: unprefixed report claims $hdr_count violation(s)"
           fi ;;
  error:*) [ "$hdr_count" -gt 0 ] || { cat "$TMP/out.txt"; fail "driver/linter failure: error report with count 0"; } ;;
  bare:*)  cat "$TMP/out.txt"
           fail "driver/linter failure: lean exited $status but the lint itself reported no violations — some other error occurred; see output above" ;;
esac

# One `#check <decl> /- <reason> -/` block per violation (with or without a leading
# `@`, depending on the declaration's binders) — parsed ONLY from the report region,
# and the number of blocks must equal N from the header.
nchecks=$(grep -c '^#check ' "$TMP/report.txt" || true)
if [ "${nchecks:-0}" -ne "$hdr_count" ]; then
  cat "$TMP/out.txt"
  fail "driver/linter failure: header claims $hdr_count violation(s) but $nchecks #check block(s) parsed"
fi
LC_ALL=C sed -n 's/^#check @\{0,1\}\([^ ]*\) .*/\1/p' "$TMP/report.txt" | LC_ALL=C sort -u \
  > "$TMP/violations.txt"

total=$(wc -l < "$TMP/violations.txt")
echo "simp-nf: linted $mods modules; $total declaration(s) not in simp normal form."

# --- 4. --update: rewrite the baseline and stop -----------------------------------
if [ "$UPDATE" = 1 ]; then
  cp "$TMP/violations.txt" "$BASELINE"
  echo "simp-nf: wrote $total grandfathered declaration(s) to $BASELINE."
  exit 0
fi

# --- 5. compare against the grandfathered baseline --------------------------------
# Baseline entries that no longer violate: a ratchet reminder, never a failure.
LC_ALL=C comm -13 "$TMP/violations.txt" "$BASELINE" > "$TMP/fixed.txt"
if [ -s "$TMP/fixed.txt" ]; then
  echo
  echo "simp-nf: RATCHET — $(wc -l < "$TMP/fixed.txt") baseline entr(y/ies) no longer violate simpNF."
  echo "Please delete these lines from $BASELINE (a follow-up PR is fine):"
  sed 's/^/  /' "$TMP/fixed.txt"
fi

# Violations not in the baseline: new debt — fail, and show the linter's reasoning.
LC_ALL=C comm -23 "$TMP/violations.txt" "$BASELINE" > "$TMP/new.txt"
if [ -s "$TMP/new.txt" ]; then
  echo
  echo "simp-nf: NEW simpNF violation(s) not in the grandfathered baseline:"
  awk 'NR==FNR { want[$0]=1; next }
       /^#check / { name=$2; sub(/^@/, "", name); p = (name in want) }
       p { print "  " $0 }
       p && /-\/[[:space:]]*$/ { p=0; print "" }' "$TMP/new.txt" "$TMP/report.txt"
  echo "Fix the lemma so its left-hand side is in simp normal form (see the linter's"
  echo "suggestion above), remove the @[simp] attribute, or — as a deliberate, commented"
  echo "exception — use @[nolint simpNF] plus an entry in $ALLOWLIST."
  fail "$(wc -l < "$TMP/new.txt") new simpNF violation(s); see the list above"
fi

echo "SIMP-NF: PASS — no new violations ($total grandfathered, $(wc -l < "$TMP/fixed.txt") ratchetable)."
