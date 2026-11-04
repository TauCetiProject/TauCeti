# Label and merge batches

Both workflows filter irrelevant events before joining a global job concurrency
group. A running job is never cancelled; only the newest pending wake-up remains.
The `control-batch-debounce` environment supplies a five-minute wait timer, with
no secrets or reviewers, and `deployment: false` avoids deployment records.
Waiting occupies no runner. Each kind starts at most about twelve jobs an hour
under continuous load, plus the independent hourly full merge sweep.

`roadmap_batch.py` wraps the pinned label reconciler. It lists open PR metadata,
skips saved unchanged classification inputs, and processes pending attempts least
recently attempted first. The 40-response work target is checked between PRs, so
large diffs can finish; quota reserves are still checked before every request.
Transport errors retain a small retry allowance. Actual rate limits stop requests
immediately, while local yields save progress without marking shared API quota
unavailable. Invalid checkpoints rebuild from current inputs, failed downloads
try older trusted artifacts, and exhausted failures retry after six hours. The
hourly label timer resumes work even after events cease.

`merge_batch.py` invokes the exact policy checked out by the shared pinned action.
The policy supplies all review, head, base, hold, backend, withdrawal and quota
checks. The wrapper only orders candidates and records discovery versions.
Changed PR/head metadata or a changed comment-version snapshot goes ahead of
unchanged queue rechecks, with active queue members first within the changed
set. Failed policy checks retain fresh inputs rather than acknowledging them.
A paginated GraphQL query reads each open PR's comment
count and most recently updated comment ID/timestamp, without bodies, so edits
and deletions are detected even when the PR's own `updated_at` does not change,
including changed PRs without readiness labels. Thus coalescing individual event
runs does not discard their changed inputs. Progress records the metadata version
listed before processing, so an edit during the attempt remains fresh next time.
The bounded pass can stop before covering the queue; the next batch resumes.
The existing hourly full merge sweep remains a backstop after the final event.

Neither a progress checkpoint nor an event payload authorizes a label or merge.
The shared implementations read current trusted policy and current PR data before
mutating. A GitHub outage or insufficient quota delays work; it never relaxes
checks. Other API users can consume quota between observations, so production
request counts and delays must be measured after rollout.
