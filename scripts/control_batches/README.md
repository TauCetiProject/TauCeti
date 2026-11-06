# Label batches

The roadmap-label workflow filters irrelevant events before joining its global job
concurrency group. The `control-batch-debounce` environment waits five minutes without
occupying a runner. A running label job is never cancelled.

`roadmap_batch.py` wraps the pinned label reconciler. It lists open PR metadata,
skips saved unchanged classification inputs, and processes pending attempts least
recently attempted first. The 40-response work target is checked between PRs, so
large diffs can finish; quota reserves are still checked before every request.
Transport errors retain a small retry allowance. Actual rate limits stop requests
immediately, while local yields save progress without marking shared API quota
unavailable. Invalid checkpoints rebuild from current inputs, failed downloads
try older trusted artifacts, and exhausted failures retry after six hours. The
hourly label timer resumes work even after events cease.

Admission belongs to the continuously running queue service. This directory contains
no merge executor, admission checkpoint or scheduled merge sweep. Review publication
and ordinary CI supply evidence to the service; they do not launch admission jobs.
