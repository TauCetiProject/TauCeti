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
| | running, green so far | ▶️ `arrow_forward` |
| | changes requested / blocked | ✍️ `writing` |
| | all review done, all green | ✅ `white_check_mark` |
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

Two workflows trigger it:

- [`zulip-pr.yml`](../../.github/workflows/zulip-pr.yml) — on PR
  `opened`/`reopened`/`closed`. Creates the message and owns the merged/closed
  ending.
- [`zulip-pr-status.yml`](../../.github/workflows/zulip-pr-status.yml) — on
  `workflow_run` of `pr-build` and `Review`. Refreshes the CI and review groups.

## One-time setup

1. **Create a dedicated Zulip bot** (Zulip → Settings → Bots → Add a new bot,
   type *Generic*). Subscribe it to the **Tau Ceti** channel — a bot can only
   post and react in channels it belongs to.
2. **Add repository secrets** on `FormalFrontier/TauCeti`:
   - `ZULIP_API_KEY` — the bot's API key
   - `ZULIP_EMAIL` — the bot's email (e.g. `tauceti-pr-bot@leanprover.zulipchat.com`)

   The site is hard-coded to `https://leanprover.zulipchat.com` in the workflows.

## Backfill (run locally)

With the bot credentials exported and `gh` authenticated:

```bash
export ZULIP_API_KEY=... ZULIP_EMAIL=... ZULIP_SITE=https://leanprover.zulipchat.com
# ascending PR number == chronological order
for pr in $(gh pr list --repo FormalFrontier/TauCeti --state all --limit 1000 --json number --jq '.[].number' | sort -n); do
  python3 scripts/zulip/zulip_pr_status.py reconcile "$pr" --create
done
```

Re-running is safe: it converges the reactions to current GitHub state and
creates a message only for PRs that don't have one yet.
