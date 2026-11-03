"""Bound label batch work while retaining the pinned reconciler's progress and policy."""

import argparse
import pathlib
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import roadmap_label as labels
from github_api import Deferred, GitHub

# Discovery scales with repository size. Yield between PRs after this many
# responses; finish the current PR so a large diff cannot livelock at a fixed cutoff.
WORK_RESPONSES = 40
WORKFLOW_RESERVE = 250
APP_CORE_RESERVE = 1000
APP_GRAPHQL_RESERVE = 100


class BatchYield(Deferred):
    """Local scheduling yield, not an exhausted shared credential."""

    def __init__(self, detail):
        self.until = time.time() + 300
        RuntimeError.__init__(self, "Label batch yielding: " + detail + "; saved work resumes in a later batch")


class BatchClient(GitHub):
    """Label client with a between-PR work target and request-level quota reserves.

    Discovery responses count toward quota, but the work target starts after a
    complete open-PR listing. Local BatchYield preserves normal saved progress;
    actual quota exhaustion retains the shared client's outage/retry semantics.
    """

    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.work_start = None
        self.yielded = False

    @property
    def responses(self):
        """Count this client's recorded HTTP responses, including retry responses."""
        return sum(row["requests"] for row in self.stats.values())

    def pause(self, reason):
        """Yield local work without marking the shared credential exhausted."""
        self.yielded = True
        raise BatchYield(reason)

    def request(self, method, path, data=None, *, read=None, **kwargs):
        """Honor observed reserves before delegating transport and mutation policy.

        Reserves apply during discovery and within a PR; only begin_pr applies
        the batch work target, so this method cannot livelock a large PR there.
        """
        is_read = method == "GET" if read is None else read
        credential, _ = self._credential(is_read)
        resource = "graphql" if path == "graphql" else "core"
        quota = self.stats.get(credential, {}).get("buckets", {}).get(resource, {})
        remaining, reset = quota.get("remaining"), quota.get("reset")
        if remaining is not None and (not reset or time.time() < float(reset)):
            reserve = (
                WORKFLOW_RESERVE if is_read else APP_GRAPHQL_RESERVE if resource == "graphql" else APP_CORE_RESERVE
            )
            if int(remaining) <= reserve:
                self.pause(f"{credential}/{resource} quota reserve reached")
        return super().request(method, path, data, read=read, **kwargs)

    def _record(self, credential, method, path, status, headers, read):
        super()._record(credential, method, path, status, headers, read)
        if status == 429 or headers.get("x-ratelimit-remaining") == "0" or (status == 403 and headers.get("retry-after")):
            # Transient transport retries retain a small wait allowance, but an
            # actual exhausted credential must stop before another request.
            reset = headers.get("x-ratelimit-reset")
            until = float(reset) + 5 if str(reset).isdigit() else time.time() + 60
            self.blocked[credential] = until
            raise Deferred(credential, until)

    def begin_pr(self):
        """Defer the next PR once the response target is spent; finish a started PR."""
        if self.work_start is not None and self.responses - self.work_start >= WORK_RESPONSES:
            self.pause("changed-PR response allowance reached")

    def pages(self, path):
        """Yield all pages, then start work accounting after open-PR discovery."""
        yield from super().pages(path)
        if "/pulls?" in path and "state=open" in path:
            self.work_start = self.responses  # Never impose a fixed PR-count discovery cap.


class BatchState(labels.RecoveryState):
    """Keep label input/retry state with fair attempt order and automatic retry dates."""

    def success(self, number, label, key):
        """Remember a completed input and its scheduling timestamp."""
        super().success(number, label, key)
        self.records[number]["batch_attempted_at"] = time.time()

    def failure(self, number, error, key=None, **kwargs):
        """Retain bounded attempts, with a six-hour retry after their exhaustion."""
        super().failure(number, error, key, **kwargs)
        record = self.records[number]
        record["batch_attempted_at"] = time.time()
        # Permissions and API validation can change without a contributor edit.
        # Preserve bounded attempts, but never require an operator to unpark them.
        if record["attempts"] >= labels.MAX_RETRIES:
            record.setdefault("retry_at", time.time() + 6 * 3600)


def main(argv=None):
    """Run the pinned reconciler, restoring module bindings on every exit.

    Corrupt input checkpoints rebuild automatically. The reconciler saves its
    progress before a local allowance yield becomes scheduling success (0).
    Actual API errors retain a nonzero result and their ordinary retry state.
    """
    argv = list(sys.argv[1:] if argv is None else argv)
    parser = argparse.ArgumentParser(add_help=False, allow_abbrev=False)
    parser.add_argument("--state-in")
    parser.add_argument("--retry-exhausted", action="store_true")
    options, _ = parser.parse_known_args(argv)
    if options.state_in and not options.retry_exhausted:
        try:
            labels.RecoveryState(options.state_in)
        except (OSError, ValueError, TypeError, AttributeError, RuntimeError, RecursionError):
            # Input hashes are an optimization, never policy or merge authority.
            # Rebuild a damaged checkpoint instead of restoring and failing forever.
            print("::warning::Unusable label checkpoint; rebuilding progress from current PR inputs")
            argv.append("--retry-exhausted")
    clients = []

    def client(**kwargs):
        value = BatchClient(**kwargs)
        clients.append(value)
        return value

    original_client, original_run_pr = labels.GitHub, labels.run_pr
    original_state, original_candidates = labels.RecoveryState, labels.candidates

    def run_pr(api, *args, **kwargs):
        api.begin_pr()
        return original_run_pr(api, *args, **kwargs)

    def candidates(api, args, areas):
        pending = list(original_candidates(api, args, areas))
        records = args._state.records if args._state else {}
        def attempted(number):
            value = records.get(number, {}).get("batch_attempted_at", 0)
            return value if isinstance(value, (int, float)) else 0
        return iter(sorted(pending, key=attempted))

    labels.GitHub, labels.run_pr = client, run_pr
    labels.RecoveryState, labels.candidates = BatchState, candidates
    try:
        result = labels.main(argv)
    finally:
        labels.GitHub, labels.run_pr = original_client, original_run_pr
        labels.RecoveryState, labels.candidates = original_state, original_candidates
    if result == 1 and clients and clients[0].yielded:
        # The reconciler already fsynced progress in its normal finally path.
        # Yielding our own allowance is successful scheduling, not an API outage.
        print("Label batch yielded with progress retained; no shared quota-exhaustion marker was written")
        return 0
    return result


if __name__ == "__main__":
    raise SystemExit(main())
