#!/usr/bin/env bash
# lint-env.sh — enforce Mathlib's default environment-linter set (`#lint`) plus a
# reliable docstring check, with a grandfathered baseline. This generalizes the former
# lint-simp-nf.sh from `#lint only simpNF` to all default linters (simpNF, checkType,
# synTaut, structureInType, defsWithUnderscore, simpComm, ...).
#
# Why not `lake exe runLinter TauCeti`: the root TauCeti.lean is intentionally empty
# (the lakefile glob is authoritative for what gets built), so runLinter would lint an
# empty environment and pass vacuously. Instead we generate a driver module that
# imports every `TauCeti/**/*.lean` module and runs `#lint only ... in TauCeti`,
# elaborate it against the already-built oleans (`lake env lean`), and parse the
# violations out of the linter report, attributing each one to the linter whose
# section it appears in.
#
# docBlame IS EXCLUDED from the `#lint` pass and replaced by a direct scan — do NOT
# "simplify" this back to the linter. Under the Lean module system the linter
# framework's introspection is systematically wrong across module boundaries:
#   * docstrings are exported only to the `server`/`private` parts of the `.olean`
#     (see `docStringExt` in Lean's `DocString/Extension.lean`: `exported := #[]`),
#     so in the module-style driver `Lean.findDocString?` sees NO docstring for any
#     imported declaration and docBlame flags thousands of documented declarations;
#   * theorems whose proofs live in non-`@[expose]`d oleans are surfaced to it as
#     `axiom`s (docBlame reported ~4.5k phantom "axiom missing documentation string"
#     hits, and misclassified undocumented defs as axioms, on a library with zero
#     real axioms — CI's `lake exe axioms` audit proves that separately).
# `#lint` has no exclusion syntax, so the driver runs `#lint only $LINTERS`, the
# explicit default-set-minus-docBlame list below. Running docBlame and dropping its
# report section instead would open a forgery channel (a crafted declaration name
# containing a newline could print a fake `docBlame` section opener inside the report
# and swallow subsequent real violations); with `only`, docBlame never runs, so any
# docBlame-attributed line is a forgery and fails closed as an unbaselined violation.
# So that new default linters added upstream are not silently missed, the docstring
# scan driver re-derives the default set from the environment and FAILS if it no
# longer equals $LINTERS + docBlame — a Batteries/Mathlib bump that changes the
# default linter set turns into a loud CI failure asking for a human update here.
# The docstring check itself runs as a
# generated LEGACY (non-module) driver with plain imports: with a non-module root,
# Lean imports the whole closure at the `private` olean level, where both docstrings
# and true declaration kinds are visible. Calibration (2026-07, this file's PR):
# module-style probes (`public import` and `import all`) both returned no docstring
# for known-documented declarations, the legacy probe found 671/677 documented,
# flagged a scratch undocumented `def` by name, and did not flag known-documented
# `TauCeti.GridDiagram.OSet`, `TauCeti.Isotopy`,
# `TauCeti.AlgebraicGeometry.WeilDivisor.coeff`. As a standing fail-closed guard, the
# scan requires at least one visible docstring among the scanned declarations (a
# blind scan sees zero) — if docstring storage moves again, this check FAILS rather
# than reporting hundreds of false violations or silently passing. The scan mirrors
# docBlame's rules (skip auto-generated declarations, instances, `Prop`-valued
# projections; require docstrings on definitions, inductives, opaques, axioms —
# theorems are deliberately exempt, as in Mathlib, where docBlameThm is a separate,
# non-default linter). Its findings are reported under the pseudo-linter name
# `docString`. NOTE: `@[nolint docBlame]` has no effect on the scan (it does not read
# nolint attributes); deliberate exceptions get a `docString <decl>` baseline entry.
#
# Violations that predate this check are grandfathered in scripts/lint-baseline.txt
# (lines of `<linter> <declName>`, LC_ALL=C sorted, no duplicates):
#   - a (linter, declaration) pair NOT in the baseline is a NEW violation  -> exit 1;
#   - a baseline entry that no longer violates is printed as a RATCHET reminder
#     (delete it from the baseline in a follow-up PR), without failing.
# The simpNF entries are the deliberate exception set kept after the 2026-07
# library-wide cleanup (see the wave-2/3 PR bodies, TauCeti #649-#657, #669-#673, for
# per-entry rationale); the rest are grandfathered singletons being fixed in parallel
# PRs.
#
# LINTER FAILED entries: a linter can crash on a declaration instead of judging it
# (its `#check` block then reads `/- LINTER FAILED: ... -/`; e.g. structureInType
# currently crashes on a private structure — another module-system introspection
# artifact). We treat a crash as a violation attributed to that linter, baseline-able
# like any other, so the known artifacts are grandfathered but a linter crashing on
# NEW code fails CI loudly rather than silently skipping the declaration.
#
# `@[nolint <linter>]` ratchet: silencing a linter per-declaration would bypass the
# baseline, so every linter name mentioned after the token `nolint` under TauCeti/
# must be accounted for in scripts/lint-nolints-allowlist.txt (lines of
# `<file>:<linter>:<count>`, LC_ALL=C sorted). The scan is textual and deliberately
# over-broad (a `nolint foo` in a comment counts too — avoid the literal token in
# prose); after `nolint` it takes every identifier in the whitespace-separated run, so
# multi-linter attributes like `@[nolint simpComm simpNF]` are fully counted. Growing
# the allowlist must go through the same human-reviewed path as this script — it is
# exactly the hole an auto-merged PR would otherwise use.
#
# SECURITY MODEL (this script elaborates the PR's own code — both drivers execute
# import-time initializers — so treat all lean output as partially
# attacker-controlled):
#   * The `#lint` report starts with a header line
#       -- Found N error(s) in M declarations (plus ...) in TauCeti with K linters
#     followed (when N > 0) by one section per reporting linter, opened by a line
#       /- The `<linter>` linter reports:
#     and containing one `#check <decl> /- ... -/` block per violation.
#     When N > 0 the report is an error diagnostic, so the header carries the
#     `<driver>:<line>:<col>: error: ` prefix of our own driver file (a fresh mktemp
#     path) and lean exits nonzero; when N = 0 it is an info message printed bare.
#     We require EXACTLY ONE header in the output, of the form matching the exit
#     code (anchored error header + N > 0 for a nonzero exit; bare header + N = 0
#     for a zero exit), we parse `#check` lines only AFTER the header, we require
#     every `#check` to fall inside a linter section, and we require the TOTAL
#     `#check` count to equal N.
#   * PR code can print arbitrary text at import time (initializers): a forged header
#     printed alongside the real one yields two headers -> fail, and a forged smaller
#     report cannot suppress the real report's `error:` diagnostic or lean's nonzero
#     exit. Forged `#check` lines make the count disagree with N -> fail. A forged
#     section-opener line can at worst re-attribute subsequent real violations to a
#     different linter name; whether bogus, `docBlame` (which does not run), or a
#     real one, the resulting (linter, declaration) pair cannot match a baseline
#     entry for the real pair -> those violations count as NEW -> fail.
#   * The docstring scan prints one `DOCSCAN <decl> ...` line per violation and
#     exactly one summary line ending in a per-run random nonce marker, carrying its
#     own counts. We require exit 0, EXACTLY ONE summary line, the undocumented count
#     to equal the number of DOCSCAN lines, at least one scanned declaration, and at
#     least one visible docstring (see the calibration note above). Forged DOCSCAN
#     lines break the count; a forged summary must predict the nonce.
#   * The remaining forgery needs a process to die before the real work runs while
#     having already printed a single self-consistent PASSING report. Commands after
#     a failed command still elaborate, so the `#lint` driver appends a `#eval`
#     printing a per-run random nonce after the `#lint`, and we require that marker
#     AFTER the header; the scan's nonce-carrying summary plays the same role there.
#   * Residual risk (accepted): initializer code could read /proc/self/cmdline to
#     learn the driver path AND read the driver file to learn the nonce, then forge a
#     passing report and exit(0) before the real work. Any lint that elaborates
#     untrusted code has this ceiling; the pr-build landrun sandbox plus human review
#     of suspicious `initialize`/`@[init]` code are the outer defense. Everything
#     short of that deliberate two-step forgery fails closed.
#
# Run from the repo root (or anywhere; it cd's to the root) AFTER `lake build` — it
# needs the compiled oleans. It does no network I/O and writes only under $TMPDIR, so
# it is safe inside the pr-build landrun sandbox. Usage:
#
#   scripts/lint-env.sh            # check against the baseline
#   scripts/lint-env.sh --update   # rewrite the baseline from the current state
set -euo pipefail

cd "$(dirname "$0")/.."
BASELINE="scripts/lint-baseline.txt"
ALLOWLIST="scripts/lint-nolints-allowlist.txt"
UPDATE=0
[ "${1:-}" = "--update" ] && UPDATE=1

fail() { echo "::error::lint-env: $*"; echo "LINT-ENV: FAIL — $*"; exit 1; }

TMP="$(mktemp -d)" || fail "mktemp failed"
trap 'rm -rf "$TMP"' EXIT
DRIVER="$TMP/LintEnvDriver.lean"
DOCDRIVER="$TMP/DocScanDriver.lean"

# --- 0. `@[nolint <linter>]` ratchet (cheap, source-only: run before the build) ---
# Every identifier in the whitespace-separated run after a `nolint` token counts as a
# silenced linter (so `@[nolint simpComm simpNF]` yields one simpComm AND one simpNF
# occurrence); occurrences are tallied into `<file>:<linter>:<count>` lines.
[ -f "$ALLOWLIST" ] || fail "allowlist $ALLOWLIST not found — it must be checked in (empty is fine)"
LC_ALL=C sort -cu "$ALLOWLIST" 2>/dev/null \
  || fail "$ALLOWLIST is not sorted/duplicate-free — fix it with: LC_ALL=C sort -u -o $ALLOWLIST $ALLOWLIST"
find TauCeti -name '*.lean' -print0 | xargs -0 awk '
  {
    s = $0
    while (match(s, /nolint[ \t]+[A-Za-z0-9_][A-Za-z0-9_ \t]*/)) {
      seg = substr(s, RSTART + 7, RLENGTH - 7)
      n = split(seg, ids, /[ \t]+/)
      for (i = 1; i <= n; i++) if (ids[i] != "") print FILENAME ":" ids[i]
      s = substr(s, RSTART + RLENGTH)
    }
  }' | LC_ALL=C sort | uniq -c | awk '{ print $2 ":" $1 }' | LC_ALL=C sort > "$TMP/nolints.txt"
LC_ALL=C comm -23 "$TMP/nolints.txt" "$ALLOWLIST" > "$TMP/nolints-new.txt"
if [ -s "$TMP/nolints-new.txt" ]; then
  echo "lint-env: 'nolint <linter>' occurrence(s) under TauCeti/ not accounted for in $ALLOWLIST:"
  sed 's/^/  /' "$TMP/nolints-new.txt"
  echo "Silencing an environment linter bypasses the baseline. If a @[nolint <linter>] is"
  echo "truly warranted, add/adjust the '<file>:<linter>:<count>' line in $ALLOWLIST in the"
  echo "same PR — that file, like this script, must only change via human-reviewed PRs"
  echo "(never via an auto-merged one)."
  fail "unaccounted 'nolint' occurrence(s); see the list above"
fi
LC_ALL=C comm -13 "$TMP/nolints.txt" "$ALLOWLIST" > "$TMP/nolints-fixed.txt"
if [ -s "$TMP/nolints-fixed.txt" ]; then
  echo "lint-env: RATCHET — allowlist entr(y/ies) in $ALLOWLIST no longer match the sources;"
  echo "please update/remove these lines (a follow-up PR is fine):"
  sed 's/^/  /' "$TMP/nolints-fixed.txt"
fi

# --- 0b. validate the baseline before spending minutes on elaboration ------------
if [ "$UPDATE" != 1 ]; then
  [ -f "$BASELINE" ] || fail "baseline $BASELINE not found — run scripts/lint-env.sh --update to create it"
  LC_ALL=C sort -cu "$BASELINE" 2>/dev/null \
    || fail "$BASELINE is not sorted/duplicate-free — fix it with: LC_ALL=C sort -u -o $BASELINE $BASELINE"
fi

NONCE="$(od -An -N16 -tx8 /dev/urandom | tr -d ' \n')" || fail "nonce generation failed"
MARKER="LINTENV-DRIVER-COMPLETE-$NONCE"
DOCMARKER="DOCSCAN-COMPLETE-$NONCE"

# The default environment-linter set minus docBlame (see the header comment), sorted.
# The docstring-scan driver verifies this against the environment and fails if the
# default set drifts, so a stale list here cannot silently narrow the lint.
LINTERS="checkType defsWithUnderscore deprecatedNoSince dupNamespace impossibleInstance nonClassInstance simpComm simpNF structureInType synTaut tacticDocs unusedArguments unusedHavesSuffices"

# $LINTERS rendered as Lean string literals, for the freshness guard in the driver.
LINTERS_LEAN=$(printf '"%s", ' $LINTERS | sed 's/, $//')

MODULE_IMPORT_LIST="$TMP/modules.txt"
find TauCeti -name '*.lean' | LC_ALL=C sort | sed 's/\.lean$//; s|/|.|g' > "$MODULE_IMPORT_LIST"
mods=$(wc -l < "$MODULE_IMPORT_LIST")
[ "${mods:-0}" -gt 0 ] || fail "found no TauCeti/*.lean modules — the lint is miswired"

# --- 1. docstring scan (fast; see the docBlame exclusion rationale above) ----------
# A LEGACY (non-module) driver with plain imports: the non-module root imports the
# closure at the `private` olean level, where docstrings and true declaration kinds
# are visible (they are NOT in a module-style driver; see the header comment).
{
  sed 's/^/import /' "$MODULE_IMPORT_LIST"
  cat <<EOF

open Lean Meta in
/-- docBlame-parity kind: \`some kindWord\` iff the declaration requires a docstring. -/
def docscanKind? (declName : Name) : MetaM (Option String) := do
  if (← getEnv).isAutoDecl declName then return none
  if ← isInstance declName then return none
  if let .str p _ := declName then
    if ← isInstance p then return none
  if let .str _ s := declName then
    if s == "parenthesizer" || s == "formatter" || s == "delaborator" || s == "quot" then
      return none
  match ← getConstInfo declName with
  | .axiomInfo .. => return some "axiom"
  | .opaqueInfo .. => return some "constant"
  | .defnInfo info =>
    if (← isProjectionFn declName) && (← isProp info.type) then return none
    return some "definition"
  | .inductInfo .. => return some "inductive"
  | _ => return none

open Lean in
run_meta do
  let env ← getEnv
  -- Freshness guard (see the header comment): the explicit \`#lint only\` list in
  -- scripts/lint-env.sh must still equal the default linter set minus docBlame.
  let expected : Array String := #[$LINTERS_LEAN]
  let mut actual : Array String := #[]
  for (name, _, dflt) in Batteries.Tactic.Lint.batteriesLinterExt.getState env do
    if dflt && name != \`docBlame then actual := actual.push s!"{name}"
  actual := actual.qsort (· < ·)
  unless actual == expected do
    throwError "the default env-linter set changed: scripts/lint-env.sh runs {expected} \
      but the environment's defaults minus docBlame are {actual}; update LINTERS in \
      scripts/lint-env.sh (and triage any new linter's findings)"
  let modNames := env.allImportedModuleNames
  let candidates : Array Name := env.constants.fold (init := #[]) fun acc declName _ =>
    match env.getModuleIdxFor? declName with
    | some idx =>
      match modNames[idx.toNat]? with
      | some m => if m == \`TauCeti || (\`TauCeti).isPrefixOf m then acc.push declName else acc
      | none => acc
    | none => acc
  let mut scanned := 0
  let mut documented := 0
  let mut undoc := 0
  for declName in candidates do
    if let some kind ← docscanKind? declName then
      scanned := scanned + 1
      if (← findDocString? env declName).isSome then
        documented := documented + 1
      else
        undoc := undoc + 1
        IO.println s!"DOCSCAN {declName} /- {kind} missing documentation string -/"
  IO.println s!"DOCSCAN-SUMMARY scanned={scanned} documented={documented} undocumented={undoc} $DOCMARKER"
EOF
} > "$DOCDRIVER"

if ! lake env lean "$DOCDRIVER" > "$TMP/docscan.txt" 2>&1; then
  cat "$TMP/docscan.txt"
  fail "driver failure: the docstring-scan driver did not elaborate cleanly — see output above"
fi
nsummaries=$(grep -c "^DOCSCAN-SUMMARY scanned=[0-9]* documented=[0-9]* undocumented=[0-9]* $DOCMARKER\$" "$TMP/docscan.txt" || true)
if [ "${nsummaries:-0}" -ne 1 ]; then
  cat "$TMP/docscan.txt"
  fail "driver failure: expected exactly 1 docstring-scan summary line, found ${nsummaries:-0}"
fi
summary=$(grep "^DOCSCAN-SUMMARY .* $DOCMARKER\$" "$TMP/docscan.txt")
# NB space-anchored keys: a bare `documented=` would greedily match inside `undocumented=`.
scanned=$(echo "$summary" | sed -n 's/.* scanned=\([0-9]*\).*/\1/p')
documented=$(echo "$summary" | sed -n 's/.* documented=\([0-9]*\).*/\1/p')
undocumented=$(echo "$summary" | sed -n 's/.* undocumented=\([0-9]*\).*/\1/p')
ndocviol=$(grep -c '^DOCSCAN ' "$TMP/docscan.txt" || true)
[ "${ndocviol:-0}" -eq "$undocumented" ] \
  || { cat "$TMP/docscan.txt"; fail "driver failure: docstring-scan summary claims $undocumented violation(s) but ${ndocviol:-0} DOCSCAN line(s) parsed"; }
[ "$scanned" -eq $((documented + undocumented)) ] \
  || fail "docstring scan summary is inconsistent: scanned=$scanned != documented=$documented + undocumented=$undocumented"
[ "$scanned" -gt 0 ] || fail "docstring scan scanned 0 declarations — the scan is miswired"
[ "$documented" -gt 0 ] \
  || fail "docstring scan saw NO docstrings at all ($scanned scanned): docstring visibility is broken (olean docstring storage moved?) — fix the scan, do not baseline this"
LC_ALL=C sed -n 's/^DOCSCAN \([^ ]*\).*/docString \1/p' "$TMP/docscan.txt" > "$TMP/violations-docscan.txt"
echo "lint-env: docstring scan: $scanned scanned, $documented documented, $undocumented undocumented."

# --- 2. generate the #lint driver: import every TauCeti module, default linters ---
# `set_option linter.hashCommand false` because the driver is generated, not committed;
# the style linter would otherwise flag the bare `#lint`/`#eval`. The trailing `#eval`
# prints a per-run nonce proving the process survived past `#lint` (see SECURITY MODEL).
{
  echo "module"
  sed 's/^/public import /' "$MODULE_IMPORT_LIST"
  echo
  echo "set_option linter.hashCommand false in"
  echo "#lint only $LINTERS in TauCeti"
  echo
  echo "set_option linter.hashCommand false in"
  echo "#eval IO.println \"$MARKER\""
} > "$DRIVER"

# --- 3. elaborate it (exit 1 from lean is EXPECTED when the linters report) -------
if lake env lean "$DRIVER" > "$TMP/out.txt" 2>&1; then
  status=0
else
  status=$?
fi

# --- 4. locate the linter report and parse it fail-closed -------------------------
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
    fail "driver/linter failure: no lint report header found (lean exit $status) — see output above"
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
# `@`, depending on the declaration's binders), grouped into per-linter sections that
# open with a "/- The `<linter>` linter reports:" line — parsed ONLY from the report
# region. The TOTAL number of `#check` blocks must equal N from the header, and every
# block must fall inside a section. docBlame does not run (see the header comment), so
# a docBlame-attributed line can only be forged output; like any other unexpected
# attribution it cannot match the baseline and fails as a new violation.
nchecks=$(grep -c '^#check ' "$TMP/report.txt" || true)
if [ "${nchecks:-0}" -ne "$hdr_count" ]; then
  cat "$TMP/out.txt"
  fail "driver/linter failure: header claims $hdr_count violation(s) but $nchecks #check block(s) parsed"
fi
LC_ALL=C awk '
  /^\/- The `[A-Za-z0-9_]+` linter reports:/ {
    linter = $0
    sub(/^\/- The `/, "", linter); sub(/` linter reports:.*$/, "", linter)
    next
  }
  /^#check / {
    if (linter == "") exit 3          # a violation before any section opener
    name = $2; sub(/^@/, "", name)
    print linter " " name
  }
' "$TMP/report.txt" > "$TMP/violations-lint.txt" \
  || { cat "$TMP/out.txt"; fail "driver/linter failure: a #check block appeared before any linter section"; }

# --- 5. combine, then --update or compare against the grandfathered baseline ------
LC_ALL=C sort -u "$TMP/violations-lint.txt" "$TMP/violations-docscan.txt" > "$TMP/violations.txt"
total=$(wc -l < "$TMP/violations.txt")
echo "lint-env: linted $mods modules; $total (linter, declaration) violation(s)."

if [ "$UPDATE" = 1 ]; then
  cp "$TMP/violations.txt" "$BASELINE"
  echo "lint-env: wrote $total grandfathered entr(y/ies) to $BASELINE."
  exit 0
fi

# Baseline entries that no longer violate: a ratchet reminder, never a failure.
LC_ALL=C comm -13 "$TMP/violations.txt" "$BASELINE" > "$TMP/fixed.txt"
if [ -s "$TMP/fixed.txt" ]; then
  echo
  echo "lint-env: RATCHET — $(wc -l < "$TMP/fixed.txt") baseline entr(y/ies) no longer violate."
  echo "Please delete these lines from $BASELINE (a follow-up PR is fine):"
  sed 's/^/  /' "$TMP/fixed.txt"
fi

# Violations not in the baseline: new debt — fail, and show each check's reasoning.
LC_ALL=C comm -23 "$TMP/violations.txt" "$BASELINE" > "$TMP/new.txt"
if [ -s "$TMP/new.txt" ]; then
  echo
  echo "lint-env: NEW violation(s) not in the grandfathered baseline (as '<linter> <declaration>'):"
  awk 'NR==FNR { want[$0]=1; next }
       /^\/- The `[A-Za-z0-9_]+` linter reports:/ {
         l = $0; sub(/^\/- The `/, "", l); sub(/` linter reports:.*$/, "", l)
         pending = "  [" l "]"
       }
       /^#check / {
         name = $2; sub(/^@/, "", name)
         p = ((l " " name) in want)
         if (p && pending != "") { print pending; pending = "" }
       }
       p { print "  " $0 }
       p && /-\/[[:space:]]*$/ { p = 0; print "" }' "$TMP/new.txt" "$TMP/report.txt"
  awk 'NR==FNR { want[$0]=1; next }
       /^DOCSCAN / {
         name = $2
         if (("docString " name) in want) {
           if (!h) { print "  [docString]"; h = 1 }
           sub(/^DOCSCAN /, "#check ")
           print "  " $0
         }
       }' "$TMP/new.txt" "$TMP/docscan.txt"
  echo
  echo "Fix the declaration per the explanation above (for docString: add a docstring), or"
  echo "— as a deliberate, commented exception — use @[nolint <linter>] plus an entry in"
  echo "$ALLOWLIST (for docString: a baseline entry, since the scan ignores @[nolint])."
  echo "If a flagged declaration is NOT in your diff, your branch likely carries a stale"
  echo "copy of a file that main has since cleaned up (the CI build overlays your whole"
  echo "TauCeti/ tree onto current main): merge main into your branch and re-push."
  fail "$(wc -l < "$TMP/new.txt") new violation(s); see the list above"
fi

echo "LINT-ENV: PASS — no new violations ($total grandfathered, $(wc -l < "$TMP/fixed.txt") ratchetable)."
