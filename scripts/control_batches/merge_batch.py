"""Coalesced wake-ups run the pinned policy, with changed PRs ahead of unchanged work."""

import json
import os
from pathlib import Path
import sys

POLICY = Path(__file__).resolve().parents[2] / ".tauceti-review/runner"
if POLICY.is_dir():
    sys.path.insert(0, str(POLICY))
import sweep


def changed(pr, previous):
    """Scheduling hint only: all authority still comes from the policy's fresh reads."""
    if not isinstance(previous, dict) or previous.get("head") != (pr.get("head") or {}).get("sha"):
        return True
    observed = previous.get("batch_observed_updated_at")
    if not isinstance(observed, str) or not observed:
        return True  # Upgrade/missing checkpoint gets one fresh policy evaluation.
    return (sweep.parse_ts(pr.get("updated_at")) > sweep.parse_ts(observed)
            or pr.get("batch_comments") != previous.get("batch_observed_comments"))


def install():
    """Install discovery/order/checkpoint hooks without changing merge decisions."""
    original_candidates = sweep.candidates
    original_remember = sweep.remember_sweep_attempt
    original_open_prs = sweep.open_prs
    original_begin = sweep.api_budget.begin_pr
    original_run = sweep.api_budget.run
    original_diff = sweep.pr_diff
    attempt = dict(failed=False, failures_before=0)

    def begin_pr():
        attempt.update(failed=False, failures_before=sweep.api_budget.failures)
        return original_begin()

    def run(*args, **kwargs):
        try:
            result = original_run(*args, **kwargs)
        except Exception:
            attempt["failed"] = True
            raise
        if result.returncode:
            attempt["failed"] = True
        return result

    def pr_diff(*args, **kwargs):
        try:
            return original_diff(*args, **kwargs)
        except Exception:
            attempt["failed"] = True
            raise

    def open_prs():
        prs = original_open_prs()
        owner, name = sweep.REPO.split("/", 1)
        query = """query($owner:String!,$name:String!,$endCursor:String){
          rateLimit{cost remaining}
          repository(owner:$owner,name:$name){pullRequests(first:100,after:$endCursor,states:OPEN,baseRefName:"main"){
            pageInfo{hasNextPage endCursor} nodes{number headRefOid comments(first:1,orderBy:{field:UPDATED_AT,direction:DESC}){
              totalCount nodes{id updatedAt}}}}}}
        """
        # Match the policy's REST discovery: gh paginates in one invocation,
        # so repository growth does not consume a fixed per-PR-work call limit.
        pages = sweep.gh_json(["api", "graphql", "--paginate", "--slurp", "-f", "query=" + query,
                               "-f", "owner=" + owner, "-f", "name=" + name])
        if not isinstance(pages, list) or not pages:
            raise RuntimeError("Merge batch comment-version discovery was incomplete")
        stamps = {}
        for data in pages:
            if data.get("errors"):
                raise RuntimeError("Merge batch comment-version discovery failed; no candidates processed")
            connection = data["data"]["repository"]["pullRequests"]
            for pr in connection["nodes"]:
                comments = pr["comments"]
                stamps[pr["number"]] = (pr["headRefOid"], dict(count=comments["totalCount"], latest=comments["nodes"]))
            print(json.dumps(dict(schema="tauceti-merge.comment-discovery/v1", prs=len(stamps),
                                  graphql_cost=data["data"].get("rateLimit", {}).get("cost"))))
        if pages[-1]["data"]["repository"]["pullRequests"]["pageInfo"]["hasNextPage"]:
            raise RuntimeError("Merge batch comment-version discovery ended before the final page")
        for pr in prs:
            observed = stamps.get(pr["number"])
            # Never attach another head's observation to this discovery snapshot.
            pr["batch_comments"] = observed[1] if observed and observed[0] == (pr.get("head") or {}).get("sha") else None
        return prs

    def candidates(prs, queue_prs, bors_prs, *, admit=True):
        ordered = original_candidates(prs, queue_prs, bors_prs, admit=admit)
        # Include changed PRs even without pr-status's readiness hint. Do not
        # lose approvals/revocations when their individual pending runs collapse.
        fresh = [p for p in prs if changed(p, sweep._sweep_progress.get(str(p["number"])))]
        active = set(queue_prs) | set(bors_prs)
        def latest_change(pr):
            comments = (pr.get("batch_comments") or {}).get("latest", [])
            previous = sweep._sweep_progress.get(str(pr["number"]))
            comment_change = isinstance(previous, dict) and pr.get("batch_comments") != previous.get("batch_observed_comments")
            stamp = max([sweep.parse_ts(pr.get("updated_at"))] +
                        [sweep.parse_ts(c.get("updatedAt")) for c in comments])
            return pr["number"] in active, comment_change, stamp
        fresh.sort(key=latest_change, reverse=True)
        numbers = {p["number"] for p in fresh}
        return fresh + [p for p in ordered if p["number"] not in numbers]

    def remember(pr):
        original_remember(pr)
        path = os.environ.get("SWEEP_PROGRESS_FILE")
        if not path or sweep.DRY_RUN:
            return
        if attempt["failed"] or sweep.api_budget.rate_limited or sweep.api_budget.failures > attempt["failures_before"]:
            return  # Attempt ordering advances; input versions remain unacknowledged.
        # Save the metadata version discovered BEFORE the policy ran, not the
        # completion time: a concurrent edit must remain fresh on the next pass.
        entry = sweep._sweep_progress.setdefault(str(pr["number"]), {})
        entry["batch_observed_updated_at"] = pr.get("updated_at")
        entry["batch_observed_comments"] = pr.get("batch_comments")
        try:
            target = Path(path)
            pending = target.with_suffix(".tmp")
            pending.write_text(json.dumps(sweep._sweep_progress))
            pending.replace(target)
        except OSError:
            print("merge-batch: scheduling checkpoint unavailable; current policy checks still apply", file=sys.stderr)

    sweep.candidates, sweep.remember_sweep_attempt, sweep.open_prs = candidates, remember, open_prs
    sweep.api_budget.begin_pr, sweep.api_budget.run, sweep.pr_diff = begin_pr, run, pr_diff


def main():
    """Run the pinned policy under its existing budget and report batch API use."""
    install()
    try:
        sweep.api_budget.configure(sweep.FOCUSED)
        return sweep.main()
    except sweep.api_budget.Exhausted as error:
        return sweep.api_budget.defer(error)
    finally:
        print(json.dumps(dict(schema="tauceti-merge.api-usage/v1", focused=sweep.FOCUSED,
                              gh_invocations=sweep.api_budget.calls, invocation_limit=sweep.api_budget.limit,
                              action_failures=sweep.api_budget.failures, rate_limited=sweep.api_budget.rate_limited)))


if __name__ == "__main__":
    raise SystemExit(main())
