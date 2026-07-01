# Zulip PR status reactions

Mirror each TauCeti PR's lifecycle onto Zulip, so the whole arc of a PR is
visible at a glance in the **Tau Ceti** channel. One bot-owned message per PR
lives in the **PRs** topic, carrying two independent groups of emoji reactions:

| Group | State | Emoji |
| --- | --- | --- |
| **CI (build)** | running | 🟡 `yellow` |
| | passed | 🟢 `green_circle` |
| | failed | 🔴 `red_circle` |
| **Review / lifecycle** | review has begun | 👀 `eyes` |
| | running, green so far | ▶️ `play` |
| | changes requested / blocked | ✍️ `writing` |
| | all review done, all green | ✔️ `check` |
| | merged | `:merge:` |
| | closed, not merged | `:closed-pr:` |

[`zulip_pr_status.py`](zulip_pr_status.py) does a full **reconcile from GitHub
truth** — PR state, the canonical `<!--tauceti-scoreboard-->` comment's meta
JSON, and the `build` commit status — then finds-or-creates the PR's message and
sets both groups. It is idempotent, so the same command drives both the
event-driven workflows and a one-shot backfill. Only the bot's *own* reactions
are authoritative (presence is judged by the bot's user id), so a human reacting
on a status message never confuses reconciliation. Its only dependencies are
python3's standard library and an authenticated `gh` CLI — no PyPI packages.

Three workflows drive it:

- [`zulip-pr.yml`](../../.github/workflows/zulip-pr.yml) — on PR
  `opened`/`reopened`/`closed`. Creates the message and owns the merged/closed
  ending.
- [`zulip-pr-status.yml`](../../.github/workflows/zulip-pr-status.yml) — on
  `workflow_run` of `pr-build` and `Review`. Refreshes the CI and review groups.
- [`zulip-healthcheck.yml`](../../.github/workflows/zulip-healthcheck.yml) — a
  schedule (every 6h) that runs `check` to probe the credentials, so a broken
  key is caught even during quiet periods with no PR activity.

## One-time setup

1. **Create a dedicated Zulip bot** (Zulip → Settings → Bots → Add a new bot,
   type *Generic*). Subscribe it to the **Tau Ceti** channel — a bot can only
   post and react in channels it belongs to.
2. **Add repository secrets** on `TauCetiProject/TauCeti`:
   - `ZULIP_API_KEY` — the bot's API key
   - `ZULIP_EMAIL` — the bot's email (e.g. `tauceti-pr-bot@leanprover.zulipchat.com`)

   The site is hard-coded to `https://leanprover.zulipchat.com` in the workflows.

   > **Set the key without a trailing newline.** A newline (or stray
   > whitespace) rides into the Basic-auth header and Zulip rejects the key as
   > `Malformed API key` (a 401). Use `--body`, which does not append one:
   >
   > ```bash
   > gh secret set ZULIP_API_KEY --repo TauCetiProject/TauCeti --body "$KEY"
   > ```
   >
   > Avoid `echo "$KEY" | gh secret set ...` (echo adds a newline). The script
   > also `.strip()`s both creds defensively, but set them cleanly anyway.

## Failure modes

The integration is built to be quiet about cosmetic problems and loud about real
ones, because the two are easy to confuse from the outside:

- A **transient** hiccup — one Zulip 5xx, a network blip, a PR with no message
  yet — is cosmetic and self-heals on the next reconcile. The script logs it and
  exits 0, so the workflow run stays green.
- A **configuration** break — missing/empty creds, a bad API key (401), a
  forbidden bot (403), or the bot not subscribed to the channel — breaks *every*
  PR and will not fix itself. The script logs it, emits a GitHub Actions
  `::error::` annotation, and exits non-zero, so the workflow run goes **red**.
  None of the three workflows use `continue-on-error`, so this is visible in the
  Actions tab and on the PR's checks. (Before this split, the workflows
  swallowed everything and always showed green, so a dead key could go unnoticed
  for a long time.)

When a run is red, re-set `ZULIP_API_KEY` per the gotcha above, then confirm:

```bash
export ZULIP_API_KEY=... ZULIP_EMAIL=... ZULIP_SITE=https://leanprover.zulipchat.com
python3 scripts/zulip/zulip_pr_status.py check   # exits 0 and prints OK when healthy
```

Re-run the `zulip-healthcheck` workflow (or just wait for the next PR event) to
clear the red. Reactions are reconciled from GitHub truth on every event, so
they catch up on their own once the key works again; a one-shot backfill is only
needed to seed messages for PRs opened while the key was broken (see below).

## Backfill (run locally)

With the bot credentials exported and `gh` authenticated:

```bash
export ZULIP_API_KEY=... ZULIP_EMAIL=... ZULIP_SITE=https://leanprover.zulipchat.com
# ascending PR number == chronological order
for pr in $(gh pr list --repo TauCetiProject/TauCeti --state all --limit 1000 --json number --jq '.[].number' | sort -n); do
  python3 scripts/zulip/zulip_pr_status.py reconcile "$pr" --create
done
```

Re-running is safe: it converges the reactions to current GitHub state and
creates a message only for PRs that don't have one yet.
