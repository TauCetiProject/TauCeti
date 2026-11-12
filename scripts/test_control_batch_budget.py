"""Ensure quota yields keep completed labels and never masquerade as shared outages."""

import importlib.util
import json
import os
from pathlib import Path
import tempfile
import time
import unittest
from unittest.mock import patch

import github_api as api
import roadmap_label as labels

path = Path(__file__).parent / "control_batches/roadmap_batch.py"
spec = importlib.util.spec_from_file_location("label_batch", path)
batch = importlib.util.module_from_spec(spec)
spec.loader.exec_module(batch)


class BatchBudget(unittest.TestCase):
    def test_work_allowance_counts_responses_but_never_caps_discovery_by_project_size(self):
        client = batch.BatchClient()
        client.stats = {"workflow-read": dict(requests=900, buckets={})}
        with patch.object(api.GitHub, "pages", return_value=iter([list(range(100))])):
            self.assertEqual(len(list(client.pages("repos/o/r/pulls?state=open"))[0]), 100)
        self.assertEqual(client.work_start, 900)
        client.stats["workflow-read"]["requests"] += 40
        with patch.object(api.GitHub, "request") as request, self.assertRaises(batch.BatchYield):
            client.begin_pr()
        request.assert_not_called()
        self.assertTrue(client.yielded)

    def test_large_pr_finishes_before_the_response_allowance_yields_to_next_batch(self):
        client = batch.BatchClient()
        client.work_start = 0
        def response(*args, **kwargs):
            client.stats.setdefault("workflow-read", dict(requests=0, buckets={}))["requests"] += 1
            return {}
        with patch.object(api.GitHub, "request", side_effect=response):
            client.begin_pr()
            for page in range(80):
                client.request("GET", f"repos/o/r/pulls/1/files?page={page}")
            self.assertEqual(client.responses, 80, "large PRs must not restart at a fixed response cutoff")
            with self.assertRaises(batch.BatchYield):
                client.begin_pr()

    def test_quota_reserves_are_separate_for_resources_and_credentials(self):
        with patch.dict(os.environ, dict(GH_READ_TOKEN="read", GH_TOKEN="write")):
            for read, resource, remaining in ((True, "core", 250), (True, "graphql", 250),
                                               (False, "core", 1000), (False, "graphql", 100)):
                with self.subTest(read=read, resource=resource):
                    client = batch.BatchClient()
                    role, _ = client._credential(read)
                    client.stats = {role: dict(requests=1, buckets={resource: dict(remaining=str(remaining), reset=str(time.time()+60))})}
                    with patch.object(api.GitHub, "request") as request, self.assertRaises(batch.BatchYield):
                        client.request("POST" if resource == "graphql" else "GET", "graphql" if resource == "graphql" else "repos/o/r/pulls", read=read)
                    request.assert_not_called()

    def test_actual_exhaustion_stops_before_shared_client_can_wait_or_retry(self):
        for status, headers in ((429, {}), (403, {"retry-after": "1"}),
                                (200, {"x-ratelimit-remaining": "0", "x-ratelimit-reset": "2000"})):
            with self.subTest(status=status, headers=headers):
                client = batch.BatchClient(max_wait=15)
                with patch.object(api, "mark_quota_unavailable"), self.assertRaises(api.Deferred):
                    client._record("workflow-read", "GET", "repos/o/r/pulls", status, headers, True)
                self.assertFalse(client.yielded, "actual quota exhaustion must not be reported as a local allowance")

    def test_all_exhausted_label_failures_get_an_automatic_retry_deadline(self):
        state = batch.BatchState()
        state.inputs[1] = "1" * 64
        for _ in range(labels.MAX_RETRIES):
            state.failure(1, RuntimeError("permission was temporarily unavailable"))
        self.assertGreater(state.records[1]["retry_at"], time.time())
        self.assertLessEqual(state.records[1]["retry_at"], time.time() + 6 * 3600)
        self.assertIn("batch_attempted_at", state.records[1])

    def test_pending_label_failures_yield_to_least_recently_attempted_work(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            area = root / "PDE"
            area.mkdir()
            (area / "README.md").touch()
            checkpoint = root / "state.json"
            records = {str(n): dict(key=str(n)*64, label="roadmap/PDE", attempts=1, batch_attempted_at=at)
                       for n, at in ((1, 20), (2, 10))}
            checkpoint.write_text(json.dumps(dict(version=1, prs=records)))
            order = []
            def process(_api, args, areas, number):
                order.append(number)
                args._processed_key = str(number)*64
                args._state.seen.add(number)
                return "roadmap/PDE"
            with patch.object(labels, "candidates", return_value=iter([1, 2])), \
                 patch.object(labels, "run_pr", side_effect=process):
                self.assertEqual(batch.main(["--roadmap-dir", directory, "--reconcile-open", "--apply",
                                             "--state-in", str(checkpoint), "--state-out", str(root/'out.json')]), 0)
            self.assertEqual(order, [2, 1])

    def test_corrupt_checkpoint_rebuilds_automatically_without_human_reset(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            area = root / "PDE"
            area.mkdir()
            (area / "README.md").touch()
            checkpoint = root / "broken.json"
            output = root / "new.json"
            client = batch.BatchClient()
            def process(_api, args, areas, number):
                args._processed_key = "1" * 64
                args._state.seen.add(number)
                return "roadmap/PDE"
            for corrupt in ("not valid JSON", "null", "[]", '{"version": 42}',
                            '{"version": 1, "prs": {"1": {"key": null}}}'):
                with self.subTest(checkpoint=corrupt):
                    checkpoint.write_text(corrupt)
                    with patch.object(batch, "BatchClient", return_value=client), \
                         patch.object(labels, "candidates", return_value=iter([1])), \
                         patch.object(labels, "run_pr", side_effect=process):
                        self.assertEqual(batch.main(["--roadmap-dir", directory, "--reconcile-open", "--apply",
                                                     "--state-in", str(checkpoint), "--state-out", str(output)]), 0)
                    self.assertEqual(json.loads(output.read_text())["prs"]["1"]["label"], "roadmap/PDE")

    def test_local_yield_saves_completed_inputs_and_does_not_mark_global_quota_failure(self):
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            area = root / "PDE"
            area.mkdir()
            (area / "README.md").touch()
            state = root / "out.json"
            client = batch.BatchClient()
            def process(_client, args, areas, number):
                args._processed_key = str(number) * 64
                args._state.seen.add(number)
                if number == 2:
                    client.pause("test allowance")
                return "roadmap/PDE"
            with patch.object(batch, "BatchClient", return_value=client), \
                 patch.object(labels, "candidates", return_value=iter([1, 2])), \
                 patch.object(labels, "run_pr", side_effect=process), \
                 patch.object(api, "mark_quota_unavailable") as mark:
                self.assertEqual(batch.main(["--roadmap-dir", directory, "--reconcile-open", "--apply", "--state-out", str(state)]), 0)
            saved = json.loads(state.read_text())
            self.assertEqual(saved["prs"]["1"]["label"], "roadmap/PDE")
            self.assertNotIn("2", saved["prs"])
            mark.assert_not_called()


if __name__ == "__main__":
    unittest.main()
