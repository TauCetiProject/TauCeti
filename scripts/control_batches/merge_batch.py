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
    return sweep.parse_ts(pr.get("updated_at")) > sweep.parse_ts(observed)


def install():
    original_candidates = sweep.candidates
    original_remember = sweep.remember_sweep_attempt

    def candidates(prs, queue_prs, bors_prs, *, admit=True):
        ordered = original_candidates(prs, queue_prs, bors_prs, admit=admit)
        # Include changed PRs even without pr-status's readiness hint. Do not
        # lose approvals/revocations when their individual pending runs collapse.
        fresh = [p for p in prs if changed(p, sweep._sweep_progress.get(str(p["number"])))]
        fresh.sort(key=lambda p: sweep.parse_ts(p.get("updated_at")), reverse=True)
        numbers = {p["number"] for p in fresh}
        return fresh + [p for p in ordered if p["number"] not in numbers]

    def remember(pr):
        original_remember(pr)
        path = os.environ.get("SWEEP_PROGRESS_FILE")
        if not path or sweep.DRY_RUN:
            return
        # Save the metadata version discovered BEFORE the policy ran, not the
        # completion time: a concurrent edit must remain fresh on the next pass.
        sweep._sweep_progress.setdefault(str(pr["number"]), {})["batch_observed_updated_at"] = pr.get("updated_at")
        try:
            target = Path(path)
            pending = target.with_suffix(".tmp")
            pending.write_text(json.dumps(sweep._sweep_progress))
            pending.replace(target)
        except OSError:
            print("merge-batch: scheduling checkpoint unavailable; current policy checks still apply", file=sys.stderr)

    sweep.candidates, sweep.remember_sweep_attempt = candidates, remember


def main():
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
