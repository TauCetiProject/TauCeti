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
            client.request("GET", "repos/o/r/pulls/1")
        request.assert_not_called()
        self.assertTrue(client.yielded)

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
