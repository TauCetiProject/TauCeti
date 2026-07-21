#!/usr/bin/env bash
# sandbox-build.sh — the offline, landrun-sandboxed build + audits + environment lint of
# the overlaid TauCeti/ sources, factored out of .github/workflows/pr-build.yml.
#
# pr-build.yml invokes this inside landrun with a fixed, comment-free one-liner
# (`cd base && exec bash scripts/sandbox-build.sh`), so the workflow's `bash -c` payload
# can no longer be broken by an apostrophe or a stray quote in a comment: all the prose
# and its punctuation live here, in a file the shell reads as a script rather than as a
# single-quoted `-c` argument. (A comment reading "Mathlib's default" once closed that
# single-quoted argument early and reddened every PR build; see #694.)
#
# This is a TRUSTED base copy. Only the PR's TauCeti/ is overlaid into the sandbox;
# scripts/ is not, and a PR that edits scripts/ is routed to a human by the scope guard —
# so this script cannot be swapped out to escape the sandbox, even though it elaborates
# the PR's (untrusted) TauCeti/ code, which is the whole reason it runs under landrun.
#
# cwd on entry is the trusted `base` checkout, with the PR's TauCeti/ already overlaid.
set -euxo pipefail

export TMPDIR="$PWD/.lake/tmp"

# Build the overlaid TauCeti/ against the trusted base config. landrun keeps this
# offline and confines writes to base/.lake.
#
# The build must be SILENT, the way Mathlib requires: a clean elaboration prints only Lake's
# progress. Any Lean `info:` or `warning:` diagnostic in the output — a stray `#check`/`#eval`, a
# `simp?`/`ring_nf?`-style "Try this: …" suggestion, or a linter warning — means the overlaid
# TauCeti/ is not clean, so fail on it here. (A compile `error:` already fails `lake build` below via
# pipefail; this catches the non-fatal diagnostics that otherwise slip through green and, worse, can
# masquerade in the log as the failure when some LATER check is the real one.) We capture the build
# output and scan it: `info:`/`warning:` at line start or in the `<file>:<line>:<col>: warning:` form.
# Lake's per-module markers (`✔`/`ℹ`/`⚠ [n/m] …`) are not diagnostics and do not match.
build_log="$TMPDIR/lake-build.log"
lake build 2>&1 | tee "$build_log"
if grep -nE '(^|[[:space:]])(warning|info): ' "$build_log"; then
  echo "::error::build is not silent — the lines above are Lean warning/info diagnostics; a clean build must emit none. Remove the stray #check/#eval, apply or delete the suggested rewrite, or fix the warning."
  exit 1
fi

# Axiom audit: inspect the built environment and reject any axiom outside
# {propext, Classical.choice, Quot.sound} — catching sorry, native_decide, and
# home-rolled axioms, including ones reaching in through imports.
lake exe axioms

# Module-system audit: every TauCeti/ module must opt into the Lean module system
# (read from each compiled module's isModule flag, not a textual grep).
lake exe module-system

# Environment lint: Mathlib's default `#lint` set minus docBlame, plus a
# module-system-reliable docstring scan, compared against the grandfathered baseline in
# scripts/lint-baseline.txt. Script, baseline, and the @[nolint <linter>] allowlist
# (scripts/lint-nolints-allowlist.txt) are trusted base copies, and its report parsing
# is fail-closed (see the SECURITY MODEL in the script). Fails on new violations or
# unaccounted nolints; fixed baseline entries print a ratchet reminder only.
bash scripts/lint-env.sh
