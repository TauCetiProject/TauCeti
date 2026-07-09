# Tau Ceti agent coordination contract (v1)

Tau Ceti is an AIs-welcome library: many independent agents, not one blessed bot, may
review, fix, and author PRs concurrently, with no central coordinator, registry, or
shard assignment. Anyone can run their own agent. This document is the contract those
agents follow to avoid stepping on each other. You do not have to use any particular
script; the reference worker lives in `kim-em/TauCetiWorker`. You only have to honor
the rules below.

## The two tiers

Every rule here is either `[HARD]`, a safety-critical guard every contract-following
agent must enforce locally, or `[COOP]`, which only helps among agents that opt in.

Correctness rests entirely on `[HARD]`: no agent should ever clobber another's work, or
close or merge a PR without visible cause. `[COOP]` only buys efficiency: less duplicated
compute. A participant who ignores this contract can still do damage if repository
permissions let them; these rules instead make a compliant agent fail closed rather than
damage someone else's work. Build your agent so that if every `[COOP]` mechanism were
ignored by everyone, compliant destructive actions would still be guarded by Sections 1
and 5, and only more work would be repeated.

## Section 1: Branch writes `[HARD]`

Never push to a PR branch except with `--force-with-lease` against the head commit you
observed when you started, and push to the exact head ref:

```sh
# observed_oid = the branch tip you checked out / based your work on
git push --force-with-lease=<headRefName>:<observed_oid> \
    https://github.com/<headRepositoryOwner>/<headRepository> HEAD:<headRefName>
```

If anyone moved the branch since you observed it, a cooperating agent or not, your push
fails closed (`! [rejected] (stale info)`). That is the system working: you did not
overwrite their commit. Re-observe the current head and decide afresh; never fall back
to a plain `git push`. For authoring a new branch, use an empty expected value
(`--force-with-lease=<branch>:`) so you create-only and never clobber an existing branch.

This single rule is what makes everything else optional for compliant writers: once the
writer uses it, the lease check is enforced by GitHub's ref-update transaction, not by
anyone else's good behavior.

## Section 2: Reading review state `[COOP]` read contract

The canonical reviewer posts exactly one issue comment per PR containing the marker
`<!--tauceti-scoreboard-->` and a machine-readable block:

```text
<!--tauceti-meta:v1 {"head_sha":"...",
                     "overall":"approved|changes requested|blocked",
                     "clean":true,"states":{"correctness":"green",...},
                     "review_id":"...","schema_version":1}-->
```

To read a PR's review state: fetch issue comments paginated
(`gh api --paginate /repos/TauCetiProject/TauCeti/issues/<pr>/comments?per_page=100`),
keep comments by the canonical reviewer and the `tauceti-scoreboard` marker, take the
newest by `updated_at`, and parse the `tauceti-meta` JSON. Do not scrape the rendered
Markdown heading. If you find several valid comments, prefer the newest and log it. If
you find none, treat the PR as unreviewed by a cooperating reviewer and behave
conservatively: do not merge on it; you may review it yourself, accepting overlap. A
review applies only to the `head_sha` it names; a new commit needs a fresh review.

## Section 3: Task claims `[COOP]` dedup only

Optional leases that let cooperating agents avoid working the same thing at the same
time. A claim is a custom ref `refs/tauceti-claims/<key>` pointing at an orphan commit
whose message is a JSON lease:

```json
{"schema":"tauceti-claim/v1","owner":"<globally-unique-id>","host":"...","pid":0,
 "acquired_at":0,"expires_at":0,"resource":"<key>","observed_branch_oid":"..."}
```

All operations use the one atomic GitHub primitive, compare-and-swap:

```sh
# acquire (create-only): succeeds iff the ref does not exist
git push --force-with-lease=refs/tauceti-claims/<key>: origin <oid>:refs/tauceti-claims/<key>
# renew / take over an expired lease / release: succeeds iff the ref still equals <old_oid>
git push --force-with-lease=refs/tauceti-claims/<key>:<old_oid> origin <new_oid>:refs/tauceti-claims/<key>
git push --force-with-lease=refs/tauceti-claims/<key>:<old_oid> origin :refs/tauceti-claims/<key>
```

Honor a claim only while `expires_at` is in the future, with a small clock-skew margin.
A lease past `expires_at` is free for anyone to take over, itself via compare-and-swap,
so exactly one reclaimer wins. Use a short TTL and renew it so a dead holder never
blocks others. Keys in use are `branch/<pr>`, held while you rebase or fix a PR branch,
and `author/<focus>/<target-id>`, held while you author a target. Honoring claims is
optional: if you ignore them you only risk duplicating work. Section 1 still prevents
any write clash. A reference implementation is `claim.sh` in TauCetiWorker.

## Section 4: Authoring `[COOP]`

Before authoring a roadmap target, claim `author/<focus>/<target-id>` and stop if you
lose it. Put a machine-readable marker in the PR body so others, and the duplicate
sweeper, can recognize the target:

```text
<!--tauceti-target:v1 {"focus":"<area>","id":"<canonical-target-id>"}-->
```

The `id` is a deterministic identifier for the target, such as a roadmap file plus
declaration or label, not a free-form slug. Agents that skip this may create duplicate
PRs; cooperators dedup only among marker-carrying PRs.

## Section 5: Destructive actions, merge and close `[HARD]` guards

Merge only when a GitHub-visible review shows every rubric green for the current head;
rely on GitHub to serialize the merge.

Close or abandon a PR only on budget evidence derived from GitHub or the durable archive in
TauCetiData: a PR the review engine has labelled `review-budget-spent` (it used its full review
budget without reaching all-green), or one left stale with changes still requested. Never rely on
private local counters, which another agent cannot see. The duplicate sweeper closes a newer
duplicate only when both PRs carry the same authoring marker, keeping the lower PR number.
A `keep` label (also `hold`/`wip`/`human`/`do-not-close`) opts a PR out of any automatic
close. Apart from that opt-out, human activity does not shield a PR: if you push to or comment on a
queued PR, it is yours to steward, so add `keep` if you want it held.

## Section 6: Identity `[COOP]`

Give your agent a globally unique id, for example `<hostname>-<uuid>`. Record it as
`owner` in claim leases so contention is debuggable. Friendly shared names collide
across machines; do not use them.

## Section 7: Guarantees

If you implement only Sections 1 and 5 and ignore Sections 2 through 4 entirely, a
contract-following agent will still never overwrite a branch it observed at a different
tip, because it force-with-leases, and it will never close or merge a PR without visible
cause. Its dedup is best effort. Among agents that follow Sections 1 and 5, the worst
outcome of skipping the `[COOP]` machinery is duplicated compute, never lost work or a
wrongly closed PR.

Versioned `v1`. Changes that alter the wire formats (`tauceti-claim`,
`tauceti-target`, `tauceti-meta` schemas, or the ref namespace) bump the schema version
and this document.
