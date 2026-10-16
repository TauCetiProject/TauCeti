#!/usr/bin/env python3
"""Cancel one withdrawn Bors dispatch; trusted default-branch code only.

No candidate checkout, force cancellation, VM lifecycle calls or status writes.
The durable intent expires; each invocation makes a fixed number of requests.
"""
import json
import os
import re
import urllib.error
import urllib.request
from datetime import datetime, timezone

REPO = "TauCetiProject/TauCeti"
REPO_ID = 1256881326
ACTOR_ID = 337246530
WORKFLOW_ID = 288851159
AUTHORITY = "https://bors.taucetiproject.org/api/candidate-cancellations/"
ACTIVE = {"queued", "in_progress", "waiting", "requested", "pending"}


class Refused(ValueError):
    """A failed trust or identity check that forbids further cancellation I/O."""
    pass


def positive(value):
    """Return whether a JSON value is a positive integer, excluding booleans."""
    return type(value) is int and value > 0


def validate_event(event):
    """Validate a GitHub dispatch and return its three integer binding fields.

    Only the configured repository and authenticated Bors sender can supply an
    intent_id, run_id and first run_attempt. Raise Refused for other envelopes;
    this payload alone grants no cancellation authority.
    """
    actor = event.get("sender", {})
    if (event.get("action") != "tauceti-bors-cancel"
            or event.get("repository", {}).get("id") != REPO_ID
            or event.get("repository", {}).get("full_name") != REPO
            or actor.get("id") != ACTOR_ID
            or actor.get("login") != "tau-ceti-bors[bot]"
            or actor.get("type") != "Bot"):
        raise Refused("untrusted dispatch")
    payload = event.get("client_payload", {})
    if not all(positive(payload.get(k)) for k in ("intent_id", "run_id", "run_attempt")):
        raise Refused("malformed dispatch binding")
    if payload["run_attempt"] != 1:
        raise Refused("rerun is not cancellable")
    return {k: payload[k] for k in ("intent_id", "run_id", "run_attempt")}


def validate_authority(authority, payload, now):
    """Validate fresh Bors authority JSON and return the unchanged mapping.

    Bors binds the intent/run/attempt to repository, batch, immutable candidate
    generation, head, base and branch. dispatch_at is Unix microseconds;
    expires_at and the injected now value are Unix seconds. Refuse missing,
    malformed, expired or payload-mismatched authority. Server-side eligibility
    must be fetched again immediately before sending cancellation.
    """
    if (authority.get("schema") != "tauceti-bors.cancellation/v1"
            or authority.get("repository") != REPO
            or authority.get("repository_id") != REPO_ID
            or any(authority.get(k) != payload[k] for k in payload)
            or not all(positive(authority.get(k)) for k in
                       ("batch_id", "candidate_id", "generation", "dispatch_at", "expires_at"))
            or authority["expires_at"] <= now
            or not all(isinstance(authority.get(k), str)
                       and re.fullmatch(r"[0-9a-f]{40}", authority[k])
                       for k in ("head_sha", "base_sha"))
            or not isinstance(authority.get("branch"), str)
            or not authority["branch"] or re.search(r"\s", authority["branch"])):
        raise Refused("missing, expired or changed durable authority")
    return authority


def validate_run(run, authority, payload):
    """Bind REST run JSON to the authorized staging title and first attempt.

    Return active or already_completed; raise Refused for any identity, actor,
    workflow, creation-window or state mismatch. created_at is an ISO8601 UTC
    time, compared with the authority timestamp units documented above.
    repository_dispatch head_sha identifies workflow code, not candidate code.
    This observation is not an atomic precondition on GitHub cancellation.
    """
    title = (f"bors branch={authority['branch']} batch={authority['batch_id']} "
             f"head={authority['head_sha']} base={authority['base_sha']}")
    if (not positive(run.get("id")) or type(run.get("run_attempt")) is not int
            or run.get("id") != payload["run_id"] or run.get("run_attempt") != 1
            or run.get("event") != "repository_dispatch"
            or run.get("path") != ".github/workflows/pr-build.yml"
            or run.get("workflow_id") != WORKFLOW_ID
            or run.get("display_title") != title
            or run.get("repository", {}).get("id") != REPO_ID
            or run.get("repository", {}).get("full_name") != REPO):
        raise Refused("run does not bind the exact candidate")
    for key in ("actor", "triggering_actor"):
        actor = run.get(key, {})
        if (actor.get("id") != ACTOR_ID or actor.get("type") != "Bot"
                or actor.get("login") != "tau-ceti-bors[bot]"):
            raise Refused("run actor mismatch")
    try:
        created = datetime.fromisoformat(run["created_at"].replace("Z", "+00:00")).timestamp()
    except (KeyError, ValueError, TypeError, AttributeError) as exc:
        raise Refused("invalid run creation time") from exc
    if not authority["dispatch_at"] / 1_000_000 - 60 <= created <= authority["expires_at"]:
        raise Refused("run outside dispatch window")
    # repository_dispatch.head_sha is the workflow SHA, never the candidate SHA.
    if run.get("status") == "completed":
        return "already_completed"
    if run.get("status") not in ACTIVE:
        raise Refused("unknown run state")
    return "active"


def request(url, token=None, method="GET"):
    """Return (HTTP status, decoded JSON or None) for one fixed-origin request.

    Callers supply only the fixed Bors/GitHub origins and positive numeric IDs.
    A supplied token goes only to GitHub. Redirects are refused; responses have
    a 1MB cap and a ten-second socket timeout. HTTP/transport/JSON errors escape
    for explicit outcome reporting, without hidden retries.
    """
    headers = {"Accept": "application/vnd.github+json", "User-Agent": "bors-exact-cancellation"}
    if token:
        headers["Authorization"] = f"Bearer {token}"
    req = urllib.request.Request(url, headers=headers, method=method,
                                 data=b"" if method == "POST" else None)
    # No redirects to a payload-selected host; all origins are fixed above/below.
    opener = urllib.request.build_opener(NoRedirect)
    with opener.open(req, timeout=10) as response:
        raw = response.read(1_000_001)
        if len(raw) > 1_000_000:
            raise Refused("response too large")
        return response.status, json.loads(raw) if raw else None


class NoRedirect(urllib.request.HTTPRedirectHandler):
    """Reject redirects rather than move trust or credentials to another URL."""
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        """Raise Refused for every redirect instead of creating a new request."""
        raise Refused("redirect refused")


def cancel(event, token, http=request, now=lambda: datetime.now(timezone.utc).timestamp()):
    """Request normal cancellation using fresh durable and current-run evidence.

    event is a GitHub dispatch, token is the trusted job token, and injectable
    http/now use the request tuple contract and Unix seconds. Return
    already_completed or normal_cancellation_requested; trust/API failures
    escape to main without force-cancel or status writes. Bors owns bounded
    durable retry. Two run reads reject observed reruns, followed by a final
    authority read. GitHub has no attempt-conditional cancellation: an external
    human rerun between the final GET and POST remains an unavoidable API race.
    """
    payload = validate_event(event)
    authority_url = AUTHORITY + str(payload["intent_id"])
    _, authority = http(authority_url)
    validate_authority(authority, payload, now())
    run_url = f"https://api.github.com/repos/{REPO}/actions/runs/{payload['run_id']}"
    _, run = http(run_url, token)
    state = validate_run(run, authority, payload)
    if state == "already_completed":
        return state
    # Re-fetch both authorities. Never let a queued workflow use its old payload
    # as permission. These reads are outside every Bors Batch/Patch transaction.
    _, run = http(run_url, token)
    if validate_run(run, authority, payload) == "already_completed":
        return "already_completed"
    _, current = http(authority_url)
    validate_authority(current, payload, now())
    if current != authority:
        raise Refused("authority changed during lookup")
    status, _ = http(run_url + "/cancel", token, "POST")
    if status != 202:
        raise Refused(f"unexpected cancellation response {status}")
    return "normal_cancellation_requested"


def main():
    """Read trusted Actions inputs and print one explicit JSON outcome.

    Report permission, missing/revoked, terminal/conflict and API/trust errors
    without granting new authority or reporting a Lean proof failure. Success
    means the normal cancellation API acknowledged the request, not that CI or
    its runner has reached a terminal state.
    """
    try:
        with open(os.environ["GITHUB_EVENT_PATH"], encoding="utf-8") as file:
            event = json.load(file)
        result = cancel(event, os.environ["GH_TOKEN"])
    except urllib.error.HTTPError as exc:
        # These are observations, not proof failures and not permission to force.
        result = {401: "permission_denied", 403: "permission_denied", 404: "missing_or_revoked",
                  409: "already_terminal_or_conflict"}.get(exc.code, f"api_error_{exc.code}")
    except (Refused, KeyError, TypeError, ValueError, OSError) as exc:
        result = f"refused_or_api_error:{type(exc).__name__}:{exc}"
    print(json.dumps({"cancellation_outcome": result}, sort_keys=True))


if __name__ == "__main__":
    main()
