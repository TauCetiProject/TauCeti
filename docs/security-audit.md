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
contents. Batches contain at most 20 commits with a 2 MiB workload target. A single
larger commit is inspected alone, without an aggregate byte cap, in the same
compacting session. Each source blob remains limited to 4 MiB and each model launch
to 30 minutes. The batching target does not bound the conversation's live context. For larger inputs,
one narrowly scoped reader exposes only numbered pages of the immutable prepared
input. Continuation tokens serialize reads; the reader rejects skipping unread pages
and reports the next unread page and remaining count. The same conversation may use native
compaction and re-read pages, then returns one verdict for the entire batch. There
are no independent partial inspections or combined partial approvals. A pass also
requires the reader's receipt to cover every page and the verdict to echo the token
following the last page's contents; delivery alone does not prove understanding.
Findings and unresolved questions must survive compaction. Remaining unread pages
are work to continue; actual uncertainty about code requires an incomplete verdict
with an explanation.

Individual commits are inspected in order: a later revert cannot conceal an earlier
dangerous version. Candidate code is never executed. The model has no GitHub
credential, general filesystem access, shell or editing authority; trusted Worker
code verifies its structured verdict and updates the ref. In judgment protocol v3,
the model returns only `verdict` and `findings`, plus the final `read_token` for
paged inputs. The Worker attaches the immutable input digest and ordered commit
list from its own launch record. Model output never supplies that identity;
unknown response fields are rejected. Complete coverage and final-token checks
remain required, and host-owned identity does not establish source safety.
A source finding, explained uncertainty or unsupported source blob stops the
cursor for human attention.

Luna's native persistent goal tools are enabled with the objective of inspecting the
whole immutable bundle while preserving findings and unresolved code questions.
Goal state survives Worker restarts separately from temporary provider credentials.
The noninteractive Codex client ends after a turn; the Worker owns continuation.
Goal completion never establishes source safety or authorizes a cursor update.

For Codex Luna, provider service failures, timeouts and eligible mechanical output
failures may resume the same native conversation without human source attestation.
The Worker also continues an `unfinished` answer with empty findings, a premature
empty-finding pass with unread pages, or a cleanly ended turn without a final answer.
Coverage determines remaining reading work, never approval. The exact native UUID,
source bundle, notes and findings are retained; no independent partial approvals
are combined. Haiku supports native compaction within its inspection; retained-session
automatic recovery currently supports Codex only.
Immediate continuations share at most three launches, with 5- and 10-second delays. Afterward,
the ordinary worker loop uses a durable 5/10/20/40/60-minute backoff, capped at
one recovery invocation per hour. Each invocation rechecks hard quota limits,
admin authority, the current cursor, exact next main prefix, unchanged input,
native UUID, reader, catalog, launcher and exact inspection prompt. It preserves
all prior findings and notes. Only a fresh complete passing judgment and confirmed
reference update clear the block. Native history and reader receipts are durable
while the model runs, including if the Worker dies before capturing stdout.
Local input bundles, actual launchers/environments/prompts, transcripts, read
receipts, native Codex compaction/usage records, verdicts, retry budgets and
advancement records are retained by the worker.
A recognized pre-inspection commit-budget block from an older planner can be archived and
replanned when the exact next commit fits the current limits. That does not attest the
commit or retry a model verdict; source findings and explained uncertainty about
code still require human attention.
After inspecting every intermediate commit themselves, an admin can use the Worker's
explicit `attest --through SHA --reason ...` command for an oversized range or to
resolve a finding. It records human evidence and repeats the same ancestry and
authority checks. A model re-roll is not a substitute for that review.

An admin's combined audit/bump/progress worker starts an audit only when at least
20 commits are pending, unless configured otherwise. Each inspection still contains
at most 20 commits, and the workload target can select fewer. Audit-only workers
inspect any nonempty backlog. Audit blocks preserve the cursor and release gate,
while the combined worker can continue bump/progress work.

When private Zulip notifications are configured on the trusted worker, a source
finding or explained code-safety uncertainty sends an immediate direct message
marked **Human review required**, with the affected commit range, recorded diagnostic
and local evidence paths. Routine unfinished turns and provider failures stay in
local logs while automatic recovery handles them. An **Operational stall** DM is
sent only if the same cursor has remained held for at least one hour after the
first observed operational pause. It explains that no source finding is recorded
and eligible automatic recovery continues. The timer is durable across retries,
changed attempts and Worker restarts; cursor advancement starts a fresh delay.
These notification rules never clear a block, waive source review or change recovery
eligibility. Repeated alerts for the same blocked range and kind are suppressed
using durable receipts. Failed delivery backs off and is retried on subsequent audit
rounds. No GitHub issue is created. The bot credential and configuration path are
excluded from the isolated reviewer's environment. Without notification configuration,
reporting remains in the local evidence and worker logs. Failed notification delivery
does not clear an audit block or prevent unrelated maintenance.

Automatic mechanical repair requires an empty-finding pass, complete page
coverage and a final-output validation failure, such as a damaged reader token or
legacy copied commit identity. It never converts that answer into approval. A
reviewed version-1 or version-2 launcher profile can migrate in the same retained
Luna session, preserving the original evidence. A version-2 coverage-only incomplete
is eligible only when its exact diagnostic matches a closed grammar, the actual
unread page range and final reader token. The native final and any ledger record
must agree; additional findings and unknown prose remain blocked. There is no
exception for a particular commit SHA. The response schema requires no SHA or digest
copying. An unexplained empty `incomplete` may receive bounded immediate repair,
but is not scheduled again afterward. Source findings, explained uncertainty about
code, unknown profiles, unauthorized tools and mismatched evidence remain blocked.
Missing coverage always blocks approval, even when it permits continuing the
inspection. Findings in earlier native history or ledger records remain binding after retries, compaction and restarts. Provider recovery may preserve an
earlier mechanical answer, but never rerolls a source finding or explained uncertainty.

Historical administrative `retry-service`, `repair-output` and narrowly pinned
reader continuations remain restricted to their original profiles. They do not
widen ordinary automatic recovery eligibility. Operational recovery needs no
manual command or human source attestation; source findings still require review.
Only a complete passing safety judgment, full delivery coverage when paged, its
final token and a confirmed ref update can advance the cursor.

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
