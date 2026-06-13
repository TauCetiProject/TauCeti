# Tau Ceti agent coordination contract (v1)

Tau Ceti is an AIs-welcome library: many independent agents — not one blessed bot — may review, fix,
and author PRs **concurrently**, with **no central coordinator, registry, or shard assignment**. Anyone
can run their own agent. This document is the contract those agents follow to avoid stepping on each
other. You do not have to use any particular script (the reference worker lives in
[kim-em/TauCetiWorker](https://github.com/kim-em/TauCetiWorker)); you only have to honor the rules below.

## The two tiers

Every rule here is either **[HARD]** — it holds against *everyone*, including agents that ignore this
contract entirely — or **[COOP]** — it only helps among agents that opt in.

> **Correctness rests entirely on [HARD]: no agent should ever clobber another's work, or close/merge a
> PR without visible cause. [COOP] only buys efficiency — less duplicated compute.** A non-cooperating
> participant can therefore *waste effort* but cannot cause damage. Build your agent so that if every
> [COOP] mechanism were ignored by everyone, nothing would break — only more work would be repeated.

---

## §1 — Branch writes  **[HARD]**

**Never push to a PR branch except with `--force-with-lease` against the head commit you observed when
you started**, and push to the exact head ref:

```sh
# observed_oid = the branch tip you checked out / based your work on
git push --force-with-lease=<headRefName>:<observed_oid> \
    https://github.com/<headRepositoryOwner>/<headRepository> HEAD:<headRefName>
```

If anyone moved the branch since you observed it — a cooperating agent or not — your push **fails closed**
(`! [rejected] (stale info)`). That is the system working: you did not overwrite their commit. Re-observe
the current head and decide afresh; never fall back to a plain `git push`. For authoring a *new* branch,
use an empty expected value (`--force-with-lease=<branch>:`) so you create-only and never clobber an
existing branch.

This single rule is what makes everything else optional: it is enforced by GitHub's ref-update
transaction, not by anyone's good behavior.

## §2 — Reading review state  **[COOP] read contract**

The canonical reviewer posts exactly one issue comment per PR containing the marker
`<!--tauceti-scoreboard-->` and a machine-readable block:

```
<!--tauceti-meta:v1 {"head_sha":"…","overall":"approved|changes requested|blocked",
                     "clean":true,"states":{"correctness":"green",…},
                     "review_id":"…","schema_version":1}-->
```

To read a PR's review state: fetch issue comments **paginated**
(`gh api --paginate /repos/FormalFrontier/TauCeti/issues/<pr>/comments?per_page=100`), keep comments by
the canonical reviewer **and** the `tauceti-scoreboard` marker, take the newest by `updated_at`, and parse
the `tauceti-meta` JSON — **do not scrape the rendered Markdown heading**. If you find several valid
comments, prefer the newest and log it; if you find none, treat the PR as *unreviewed by a cooperating
reviewer* and behave conservatively (don't merge on it; you may review it yourself, accepting overlap).
A review applies only to the `head_sha` it names — a new commit needs a fresh review.

## §3 — Task claims  **[COOP] dedup only**

Optional leases that let cooperating agents avoid working the same thing at the same time. A claim is a
custom ref `refs/tauceti-claims/<key>` pointing at an orphan commit whose message is a JSON lease:

```
{"schema":"tauceti-claim/v1","owner":"<globally-unique-id>","host":"…","pid":…,
 "acquired_at":<epoch>,"expires_at":<epoch>,"resource":"<key>","observed_branch_oid":"…"}
```

All operations use the one atomic GitHub primitive (compare-and-swap):

```sh
# acquire (create-only): succeeds iff the ref does not exist
git push --force-with-lease=refs/tauceti-claims/<key>: origin <oid>:refs/tauceti-claims/<key>
# renew / take over an EXPIRED lease / release: succeeds iff the ref still equals <old_oid>
git push --force-with-lease=refs/tauceti-claims/<key>:<old_oid> origin <new_oid>:refs/tauceti-claims/<key>
git push --force-with-lease=refs/tauceti-claims/<key>:<old_oid> origin :refs/tauceti-claims/<key>  # release
```

Rules: honor a claim only while `expires_at` is in the future (with a small clock-skew margin); a lease
past `expires_at` is free for anyone to take over (itself via CAS, so exactly one reclaimer wins). Use a
**short TTL and renew** (heartbeat) so a dead holder never blocks others. Keys in use: `branch/<pr>`
(held while you rebase/fix a PR branch) and `author/<focus>/<target-id>` (held while you author a target).
**Honoring claims is optional**: if you ignore them you only risk duplicating work — §1 still prevents any
write clash. A reference implementation is `claim.sh` in TauCetiWorker.

## §4 — Authoring  **[COOP]**

Before authoring a roadmap target, claim `author/<focus>/<target-id>` (§3) and stop if you lose it. Put a
machine-readable marker in the PR body so others — and the duplicate sweeper — can recognize the target:

```
<!--tauceti-target:v1 {"focus":"<area>","id":"<canonical-target-id>"}-->
```

The `id` is a deterministic identifier for the target (e.g. roadmap file + declaration/label), not a
free-form slug. Agents that skip this may create duplicate PRs; cooperators dedup only among
marker-carrying PRs.

## §5 — Destructive actions (merge / close)  **[HARD] guards**

- **Merge** only when a GitHub-visible review (§2) shows every rubric green for the *current* head; rely on
  GitHub to serialize the merge (a loser simply sees "already merged").
- **Close / abandon** only a PR that is **in your scope** (one you authored or can identify as yours), with
  **no human activity**, and only on budget evidence derived from GitHub or the durable archive
  ([TauCetiData](https://github.com/FormalFrontier/TauCetiData)) — never on your private local counters,
  which another agent cannot see. Never close a foreign or human-touched PR. The duplicate sweeper closes a
  newer duplicate only when both PRs carry the same §4 marker and neither has human activity; otherwise it
  labels for a human.

## §6 — Identity  **[COOP]**

Give your agent a **globally-unique** id (e.g. `<hostname>-<uuid>`); record it as `owner` in claim leases
so contention is debuggable. Friendly shared names (`a`, `b`) collide across machines — don't use them.

## §7 — Guarantees

If you implement only §1 and §5 and ignore §§2–4 entirely, a contract-following agent will still **never
overwrite your branch** (it force-with-leases), **never close or merge your PR without visible cause**, and
its dedup is best-effort. The worst outcome of non-cooperation — yours or anyone's — is duplicated compute,
never lost work or a wrongly-closed PR.

---

*Versioned `v1`. Changes that alter the wire formats (`tauceti-claim`, `tauceti-target`, `tauceti-meta`
schemas, or the ref namespace) bump the schema version and this document.*
