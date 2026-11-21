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
to 30 minutes. The batching target does not bound the conversation's live context.
Small inputs are supplied inline. For larger inputs, one narrowly scoped reader
exposes only numbered pages of the immutable prepared input: it serves the next
unserved page or an earlier reread, rejects skipping ahead, and reports the next
unserved page and remaining count. The same conversation may use native compaction
and reread pages, then returns one verdict for the entire batch. A pass also
requires the reader to have served every page; delivery alone does not prove
understanding. Findings and unresolved questions must survive compaction.

Individual commits are inspected in order: a later revert cannot conceal an earlier
dangerous version. Candidate code is never executed. The model has no GitHub
credential, general filesystem access, shell or editing authority; trusted Worker
code verifies its structured verdict and updates the ref. The model returns only
`verdict` and `findings`. The Worker attaches the immutable input digest and ordered
commit list from its own launch record. Model output never supplies that identity;
unknown response fields are rejected. Complete coverage remains required, and
host-owned identity does not establish source safety. A source finding, unreadable
evidence or an unsupported source blob stops the cursor for human attention.

Only a human attestation moves the cursor past a finding or an unreadable hold. After
inspecting every intermediate commit themselves, an admin can use the Worker's
explicit `attest --through SHA --reason ...` command for an oversized range or to
resolve a finding. It records human evidence and repeats the same ancestry and
authority checks. A model re-roll is not a substitute for that review. The Worker
retains local input bundles, actual launchers, environments and prompts, transcripts,
native Codex compaction and usage records, read receipts, verdicts and advancement
records.

Worker audit rounds and the parallel pool run the same scheduler; a Worker round
advances passed ranges, inspects at most one range and returns. An admin's combined
audit/bump/progress worker admits new audit work only when at least 20 commits are
pending, unless configured otherwise; admitted ranges, including the halves of a split
range, continue below that threshold. Each inspection still contains at most 20
commits, and the workload target can select fewer. Audit-only workers inspect any
nonempty backlog. Audit blocks preserve the cursor and release gate, while the combined
worker can continue bump/progress work.

With private Zulip notifications configured on the trusted worker, the operator always
either sees the cursor advance or has a direct message. A recorded source concern sends an
immediate DM marked **Human review required**, with the affected commit range, the recorded
diagnostic and local evidence paths. Every other reason for the cursor to stop is reported
by one cursor watchdog. It runs on every audit round, on every pass of a parallel pool and
as a standalone command for a timer. Once audit work is due at a cursor (enough pending
commits to admit work, or work already started there) and that cursor has not moved for an
hour, it sends an **Operational stall** DM, then a new one daily while the cursor stays held.
An unobservable cursor counts as held, and the DM names the error. Off-host monitoring
remains responsible for detecting a dead worker host. Alerts never clear a block, waive
source review or change recovery eligibility. Durable receipts and local locks send each
alert once. Failed delivery backs off for 15 minutes and is retried on later checks, and
the cause of the failure is logged. No GitHub issue is created. The bot credential and
configuration path are excluded from the isolated reviewer's environment. Without
notification configuration, reporting remains in the local evidence and worker logs.

New inspections use judgment protocol 5. The reviewer returns `pass`, `finding` or
`unfinished`; there is no `incomplete`. Genuine uncertainty about whether a construct is
safe is a `finding`: a concern requiring human review, not necessarily a demonstrated
vulnerability. Unread pages or lost context are never findings; the reviewer returns
`unfinished` with no findings and the Worker continues the same session, within one budget
of three charged launches (a launch that served new pages is not charged; a timeout ends
the attempt). Native goal tools are not offered. New inspections never fall back to an
older protocol: until a client's delivery is verified for protocol 5, they wait. Any
concern recorded anywhere in an attempt (its native history, captured output,
continuations or the ledger) binds that range and sends the immediate DM, whatever the
final answer says and even if the attempt later failed. Unreadable or ambiguous evidence
is treated as a possible concern: it holds the range and sends an immediate DM rather than
starting a fresh inspection. A concern or unreadable hold recorded for a range binds every
range that contains any of its commits, however the commits are later planned or split.

An attempt that ends without a judgment and without any recorded concern (an exhausted
continuation budget, malformed output, a timeout or an unexpected tool call) never binds.
If the reviewer engaged with the range (it answered, or was served input), the Worker
bisects it: in one durable update it replaces the range with two consecutive ranges,
splitting its ordered commit list in half, and inspects each in a fresh session with
complete per-commit input. It repeats this down to single commits. A single commit without
a judgment, or a range whose reviewer never engaged (a provider or setup failure), is
inspected again in a fresh session, preferring a different available reviewer, with a
persisted backoff of up to an hour that never gives up. Each replacement range needs its
own complete passing judgment with full served coverage, and ranges advance strictly in
order. These are complete inspections of smaller commit ranges; pages or partial approvals
from different attempts are never combined. Codex exposes built-in MCP resource helpers
whenever an MCP server is configured, and they cannot be disabled. Their descriptions mark
them unavailable, the only configured server is the read-only audit reader, which serves
no resources, and calls to them count as no coverage. Evidence retained from protocols 1
to 4 is classified the same way, so any recorded concern there, including an explained
`incomplete`, remains binding; it is never continued, and only a protocol-5 inspection can
pass.

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
