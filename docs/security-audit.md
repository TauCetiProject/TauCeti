# Security audit cursor

`security-audit` marks the inspected prefix of main's first-parent history. Only
repository admins may create or update it. Separate rulesets prohibit deleting it
or moving it backward, including for admins. GitHub cannot enforce membership in
main's history; the trusted Worker validates that relationship before each update.
Administrators must use that updater rather than directly pushing arbitrary commits.

The bootstrap is `8eecb48e9b51da99ca119f190a64ca43c100795b`, the main snapshot inspected
on 2026-10-12. That was a static source audit; earlier intermediate commits are
grandfathered, not individually audited. No identifiable malicious payload was found.
The benign D4 macro using `hygiene false` was subsequently removed and the cheap
source-option guard strengthened in #15202 and #15203.

TauCetiWorker's explicit `security-audit` phase examines only `TauCeti/` and
`TauCeti.lean` for IO and executable metaprogramming beyond macros and notation.
Macro bodies are inspected for these behaviors too. Scripts, workflows, Lake
configuration, dependency pins and other human-reviewed infrastructure are excluded.
Ordinary mathematical APIs and standard Mathlib tactics/registration commands are
allowed. This is not an additional mathematical review or a dependency/artifact audit.

Each session uses Luna or Haiku, with complete per-commit diffs and changed-file
contents. Batches contain at most 20 commits with a 2 MiB workload target; a single
larger commit may use up to 8 MiB, with a 4 MiB limit per source blob. These limits
bound the workload, rather than the conversation's live context. For larger inputs,
one narrowly scoped reader exposes only numbered pages of the immutable prepared
input. Continuation tokens serialize reads. The same conversation may use native
compaction and re-read pages, then returns one verdict for the entire batch. There
are no independent partial inspections or combined partial approvals. A pass also
requires the reader's receipt to cover every page and the verdict to echo the token
following the last page's contents; delivery alone does not prove understanding.
Findings and unresolved questions must survive compaction, and the
reviewer must return incomplete if it cannot finish the inspection.

Individual commits are inspected in order: a later revert cannot conceal an earlier
dangerous version. Candidate code is never executed. The model has no GitHub
credential, general filesystem access, shell or editing authority; trusted Worker
code verifies its structured verdict and updates the ref. A finding, incomplete
review, client failure or input beyond the workload limits stops the cursor for
human attention. Local input bundles, actual launchers/environments/prompts,
transcripts, read receipts, native Codex
compaction/usage records, verdicts and advancement records are retained by the worker.
A pre-inspection commit-budget block from the old 256 KiB planner can be archived and
replanned when the exact next commit fits the new limits. That does not attest the
commit or retry a model verdict; other blocks still require human attention.
After inspecting every intermediate commit themselves, an admin can use the Worker's
explicit `attest --through SHA --reason ...` command for an oversized range or to
resolve a finding. It records human evidence and repeats the same ancestry and
authority checks. A model re-roll is not a substitute for that review.

An unexplained `incomplete` answer with an empty findings list, or a paged `pass`
whose input digest omits only its final character, may receive bounded output repair
in the same retained Luna conversation. The exact ordered commits and remaining
schema must validate; paged input must have complete receipt coverage and the correct
final token. A repaired answer must echo the exact full digest. The response schema
fixes that digest to prevent copying errors. Earlier source findings and explained
incomplete verdicts remain binding. The repair preserves all notes and uncertainty;
only a new complete passing answer can approve the original batch. Service retries
and repairs share at most three launches per invocation. Each batch permits at most two
explicit admin `repair-output --state DIR --reason ...` invocation. Failed answers,
repair counts and recovery kinds are retained in the evidence and ledger. Exhausted
repairs remain blocked. The original pre-profile incident has a narrowly pinned
compatibility continuation for its exact reader-context failure; it does not permit
other explained incomplete verdicts to be retried.

Local blocks are not a shared authorization service. Administrators must not evade
a finding by changing worker IDs, and should keep admin credentials out of ordinary
authoring/review agents. Recovering an accidental off-main admin push requires a
human to temporarily change the monotone ruleset, restore an inspected main commit,
and re-enable the protection.

## Toolchain tags

New `v*` tags are admin-only; existing tags cannot be changed or deleted. For a new
toolchain release, its commit must occur on main's first-parent history at or before
the cursor, and must meet the existing main CI and published-cache requirements.
`scripts/toolchain_tags.py --create` repeats the cursor check immediately before
publishing and records the cursor SHA in the annotated tag. Missing or invalid
cursor state blocks creation. Admins must use this tool; GitHub's tag restrictions
do not independently enforce cross-branch ancestry.

The readiness report runs when the toolchain changes or the cursor advances. It
reports releases ahead of the cursor as `pending-security-audit`. Historical tags,
including constructed side-branch releases, remain unchanged and show their historical
coverage. Constructing new side-branch release commits is no longer an exception.

This policy trusts repository admins and the installed Worker/tag tooling. A
malicious administrator can edit protections; an AI verdict can miss obfuscated code,
and conversation compaction can lose inspection details.
The cursor records a bounded source inspection, not a certification of safety.
