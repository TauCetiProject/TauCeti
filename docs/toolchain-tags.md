# Toolchain tags

Tau Ceti tags eligible Lean releases as `vX`, the way Mathlib does, so a project on Lean
v4.34.0 can check out `v4.34.0` here and get a tree that builds.

## The rule

**`vX` is the first commit on `main` whose `lean-toolchain` is `leanprover/lean4:X`.**

Mathlib puts its `vX` tag on the commit that bumps its own `lean-toolchain` to X, and
`scripts/check-bump.sh` requires this repository's toolchain to match Mathlib's at whatever
it pins. The first `main` commit on toolchain X therefore pins Mathlib at or after Mathlib's
`vX` tag. The tag message gives the pin.

Ordinary toolchain tags do not promise Mathlib's matching release pin: that requires a separate
maintenance branch, source build, and cache publication, as described below.

## What a tag promises

The commit is on that Lean toolchain, its post-merge CI passed, and its oleans are in the
Lake artifact cache, so a checkout builds without recompiling the library. The tool checks
the recorded CI result and the published cache; neither needs a rebuild.

New tags also require their commit to lie on main's first-parent history at or behind
the protected [security audit cursor](security-audit.md). The tool reads fresh remote
refs and repeats the coverage check immediately before publishing. This is a bounded
source inspection, with the scope and bootstrap limits described in that policy.
Tag creation is admin-only, and published `v*` tags cannot be changed or deleted.

## What it does not cover

The tool tags only commits on `main`. A release mathlib has tagged but `main` has not
reached yet is reported `ahead`: nothing is wrong, the bump has not got there, and it will
be tagged like any other release when it does. A release `main` went past without stopping
is reported `unreachable`. Two things cause that, and they differ in what can be done about them: the
daily bump stepped over the release's window on Mathlib master, which a later bump could
avoid, or Mathlib cut the release on its `stable` branch, which `check-bump.sh` will not let
this repository pin at all.

Historically, such releases were tagged by hand off a `main` commit. `v4.33.0` is one: a commit
off `afb1aacb` changing only the two pin files, built from source, with its cache uploaded
manually. The report marks it `tagged`, notes that it was constructed, and says whether it
found a cache. These existing tags remain unchanged. Constructing a new side-branch
release with an ordinary `vX` name is no longer an exception: those tags must use audited main
history. Explicitly requested maintenance patch releases use distinct names as described below.

Releases older than `v4.33.0-rc1` are out of scope, because the Lake cache has no older
entries. That bound is `EARLIEST_RELEASE` in the script; raise it if the cache is pruned,
never lower it.

## Maintenance patch releases

`v4.35.0+patch1` is an explicitly requested maintenance release based on `v4.35.0`. It uses
Mathlib's `v4.35.0` tag (`56a005855ea17e0b0958f73ec801ae140b0a1679`) instead of the later
master snapshot in the original Tau Ceti tag. This lets downstream projects share the matching
Mathlib release with libraries such as Stacks. The Lean toolchain stays at `v4.35.0`.

This is a deliberate exception for this maintenance branch, not a change to the ordinary
`vX` tagging rule or main's forward-only Mathlib-master updates. The automatic tag tool does not
construct or publish this patch release. The existing `v4.35.0` tag remains immutable.

To build and publish this maintenance release:

1. Work on `release/v4.35.0-patch1`, starting from the existing `v4.35.0` tag. Pin both the
   lakefile requirement and manifest to Mathlib's release; repair existing proofs against it.
2. Dispatch `ci.yml` on that branch. It runs the full library build, ownership/axiom and module
   audits, environment and source linters, then the existing isolated cache publisher. Cache
   publication is required to succeed. The job checks only the exact revision for cache reuse:
   the old Mathlib snapshot's Tau Ceti artifacts have different input hashes.
3. Wait for that exact commit's CI and cache publication to succeed, and confirm its public
   revision map. Test a fresh consumer with Mathlib's matching release and the patched Tau Ceti
   commit, requiring cache restoration to build without recompiling Tau Ceti.
4. Create the new annotated `v4.35.0+patch1` tag on that verified commit and push it. Include the
   base tag, exact Mathlib pin, and validation evidence in its message. Never move the old tag.

The publisher still runs on a fresh runner separate from the build; upload credentials are
never available to Lean elaboration. This release uses stock Lean/Lake.

## Reporting

`.github/workflows/toolchain-tags.yml` posts to Zulip (Tau Ceti > "Toolchain tags") when a
release becomes taggable or turns out not to be taggable. It runs on a push to `main` that
changes `lean-toolchain`, waits for `ci.yml` to conclude on that commit, and then posts only
if the state has changed since its last message. It reads that state from a marker in the
message, so it stores nothing, and it never creates a tag. Before comparing that marker,
the bot repairs the missing `shell` language on its own newest old-style command fence;
that one-time edit leaves the report body unchanged.

The trusted Worker also dispatches this report after advancing the security cursor.
That dispatch uses the workflow on the default branch, even when the cursor still
points at an older commit. A release ahead of the cursor is reported as
`pending-security-audit`; cursor updates only produce a new message when release
readiness changes.

The wait matters: the push lands 40 to 70 minutes before the release is taggable, because
`ci.yml` coalesces bursts of `main` pushes and then takes 20 to 30 minutes, publishing the
Lake cache at the end. Reporting at push time would always say "not yet".

A release waiting on CI shows as `pending` and is left out of the change comparison. It is
not news, and including it would post one message saying "wait" and another when the
waiting ended.

## Using it

```
python3 scripts/toolchain_tags.py                      # the report
python3 scripts/toolchain_tags.py --create v4.34.0     # one tag
python3 scripts/toolchain_tags.py --create --all       # every ready release
```

Run `--create` after a bump lands on a new toolchain and the security cursor covers
its commit. It needs a `gh` login with repository-admin permission; the report needs
only read access.

If a tag does not match the rule, the tool reports it and changes nothing.
