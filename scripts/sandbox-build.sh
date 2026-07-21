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
lake build

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
