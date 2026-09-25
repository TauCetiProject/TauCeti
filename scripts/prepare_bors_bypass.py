#!/usr/bin/env python3
"""Prepare (and optionally apply) the minimal GitHub protection bypass for bors.

Only the named bors App is added. Existing merge-queue and required-status
rules stay intact. This does not switch MERGE_BACKEND or approve any PR.
"""
import argparse
import copy
import json
import pathlib
import subprocess

REPO = "TauCetiProject/TauCeti"
RULESET = 17824807


def gh(path, *, method="GET", data=None):
    cmd = ["gh", "api", "-X", method, path]
    if data is not None:
        cmd += ["--input", "-"]
    out = subprocess.check_output(cmd, input=json.dumps(data) if data is not None else None,
                                  text=True)
    return json.loads(out) if out.strip() else None


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--app-id", type=int, required=True)
    ap.add_argument("--app-slug", required=True)
    ap.add_argument("--output", type=pathlib.Path, default=pathlib.Path("/tmp/tauceti-bors-bypass"))
    ap.add_argument("--apply", action="store_true")
    args = ap.parse_args()
    if args.app_id <= 0 or not args.app_slug:
        ap.error("an installed GitHub App ID and slug are required")
    app = gh(f"apps/{args.app_slug}")
    if app["id"] != args.app_id:
        raise SystemExit("App ID does not match slug")

    rules_path = f"repos/{REPO}/rulesets/{RULESET}"
    reviews_path = f"repos/{REPO}/branches/main/protection/required_pull_request_reviews"
    current_rules = gh(rules_path)
    current_reviews = gh(reviews_path)
    if current_rules["name"] != "merge-queue-main" or current_rules["target"] != "branch":
        raise SystemExit("unexpected ruleset; refusing to construct a bypass")
    if not {"merge_queue", "required_status_checks"} <= {r["type"] for r in current_rules["rules"]}:
        raise SystemExit("expected merge queue and required status rules are absent")
    if not current_reviews.get("require_code_owner_reviews"):
        raise SystemExit("classic code-owner review protection is absent")

    proposed_rules = {key: copy.deepcopy(current_rules[key]) for key in
                      ("name", "target", "enforcement", "conditions", "rules", "bypass_actors")}
    actor = {"actor_id": args.app_id, "actor_type": "Integration", "bypass_mode": "always"}
    if not any(x.get("actor_type") == "Integration" and x.get("actor_id") == args.app_id
               for x in proposed_rules["bypass_actors"]):
        proposed_rules["bypass_actors"].append(actor)

    proposed_reviews = {key: current_reviews[key] for key in
                        ("dismiss_stale_reviews", "require_code_owner_reviews",
                         "required_approving_review_count", "require_last_push_approval")}
    allowances = current_reviews.get("bypass_pull_request_allowances") or {}
    existing = {key: [item["login"] if isinstance(item, dict) and key == "users" else
                      item["slug"] if isinstance(item, dict) and key in ("teams", "apps") else item
                      for item in allowances.get(key, [])]
                for key in ("users", "teams", "apps")}
    if args.app_slug not in existing["apps"]:
        existing["apps"].append(args.app_slug)
    proposed_reviews["bypass_pull_request_allowances"] = existing
    if current_reviews.get("dismissal_restrictions"):
        restrictions = current_reviews["dismissal_restrictions"]
        proposed_reviews["dismissal_restrictions"] = {
            "users": [x["login"] for x in restrictions.get("users", [])],
            "teams": [x["slug"] for x in restrictions.get("teams", [])],
            "apps": [x["slug"] for x in restrictions.get("apps", [])],
        }

    args.output.mkdir(parents=True, exist_ok=True)
    for name, value in (("ruleset-before", current_rules), ("reviews-before", current_reviews),
                        ("ruleset-proposed", proposed_rules), ("reviews-proposed", proposed_reviews)):
        (args.output / f"{name}.json").write_text(json.dumps(value, indent=2) + "\n")
    print(f"Proposal and backup written to {args.output}")
    if args.apply:
        gh(rules_path, method="PUT", data=proposed_rules)
        gh(reviews_path, method="PATCH", data=proposed_reviews)
        print("Bors App added to both bypass lists. MERGE_BACKEND is unchanged.")
    else:
        print("Read-only plan; pass --apply after reviewing the JSON and completing the pilot.")


if __name__ == "__main__":
    main()
