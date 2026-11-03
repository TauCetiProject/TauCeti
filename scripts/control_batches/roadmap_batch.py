"""Bound label batch work while retaining the pinned reconciler's progress and policy."""

import pathlib
import sys
import time

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[1]))
import roadmap_label as labels
from github_api import Deferred, GitHub

# Discovery scales with repository size; changed-PR work yields after this many
# actual responses (retries included). A single in-flight request may add two retries.
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
    def __init__(self, **kwargs):
        super().__init__(**kwargs)
        self.work_start = None
        self.yielded = False

    @property
    def responses(self):
        return sum(row["requests"] for row in self.stats.values())

    def pause(self, reason):
        self.yielded = True
        raise BatchYield(reason)

    def request(self, method, path, data=None, *, read=None, **kwargs):
        if self.work_start is not None and self.responses - self.work_start >= WORK_RESPONSES:
            self.pause("changed-PR response allowance reached")
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

    def pages(self, path):
        yield from super().pages(path)
        if "/pulls?" in path and "state=open" in path:
            self.work_start = self.responses  # Never impose a fixed PR-count discovery cap.


def main(argv=None):
    clients = []

    def client(**kwargs):
        value = BatchClient(**kwargs)
        clients.append(value)
        return value

    original = labels.GitHub
    labels.GitHub = client
    try:
        result = labels.main(sys.argv[1:] if argv is None else argv)
    finally:
        labels.GitHub = original
    if result == 1 and clients and clients[0].yielded:
        # The reconciler already fsynced progress in its normal finally path.
        # Yielding our own allowance is successful scheduling, not an API outage.
        print("Label batch yielded with progress retained; no shared quota-exhaustion marker was written")
        return 0
    return result


if __name__ == "__main__":
    raise SystemExit(main())
