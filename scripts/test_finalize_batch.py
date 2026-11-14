"""Exercise terminal reporting, bounded acquisition and publisher trust boundaries."""
import contextlib
import copy
import io
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from urllib.error import HTTPError
from unittest.mock import Mock, patch

import yaml
import finalize_batch as finalizer

ROOT = Path(__file__).resolve().parents[1]
PR = yaml.safe_load((ROOT / ".github/workflows/pr-build.yml").read_text())["jobs"]
PUB = yaml.safe_load((ROOT / ".github/workflows/publish-lake-cache.yml").read_text())
ENV = dict(STATUS_SHA="a" * 40, BUILD_JOB_RESULT="success", BUILD_STATE="success",
           BUILD_DESCRIPTION="audited", PUBLICATION_REQUIRED="true",
           GITHUB_RUN_ID="12", GITHUB_RUN_ATTEMPT="2", BORS_STAGING="false")


def job(status="completed", conclusion="success", confirmed=True):
    return dict(id=7, name=finalizer.PUBLISHER, status=status, conclusion=conclusion,
                runner_name="nsc-publisher" if status != "queued" else "",
                labels=[finalizer.MACHINE_LABEL],
                steps=[dict(name=finalizer.CONFIRM, conclusion="success" if confirmed else "skipped")])


def jobs(*items):
    sandbox = dict(name="sandboxed-build", runner_name="nsc-sandbox")
    return dict(total_count=len(items) + 1, jobs=[sandbox, *items])


class Clock:
    now = 0

    def __call__(self):
        return self.now

    def sleep(self, seconds):
        self.now += seconds


class FinalizerTests(unittest.TestCase):
    def wait(self, responses):
        fetch = Mock(side_effect=responses)
        clock = Clock()
        with contextlib.redirect_stdout(io.StringIO()):
            result = finalizer.wait_publication(12, 2, fetch=fetch, clock=clock, sleep=clock.sleep)
        for call in fetch.call_args_list:
            self.assertEqual(call.args, ("/actions/runs/12/attempts/2/jobs?per_page=100",))
        return result, clock.now

    def test_no_early_green_before_completed_exact_map_confirmation(self):
        result, elapsed = self.wait([jobs(job("queued", None)), jobs(job("in_progress", None)), jobs(job())])
        self.assertEqual(result[0], "success")
        self.assertEqual(elapsed, 60)

    def test_failed_canceled_skipped_or_unconfirmed_publisher_cannot_be_green(self):
        for conclusion, confirmed in [("failure", True), ("cancelled", True), ("skipped", True),
                                      ("timed_out", True), ("success", False)]:
            with self.subTest(conclusion=conclusion, confirmed=confirmed):
                result, _ = self.wait([jobs(job(conclusion=conclusion, confirmed=confirmed))])
                self.assertEqual(result[0], "failure")

    def test_unavailable_missing_or_unobservable_publisher_is_bounded(self):
        for response in [jobs(job("queued", None)), jobs(), OSError("API unavailable"),
                         jobs(dict(job(), name="publisher from another job"))]:
            with self.subTest(response=response):
                result, elapsed = self.wait([response] * 11)
                self.assertEqual(result[0], "failure")
                self.assertIn("5m", result[1])
                self.assertEqual(elapsed, 300)

    def test_running_publication_has_a_separate_bounded_completion_budget(self):
        result, elapsed = self.wait([jobs(job("in_progress", None))] * 41)
        self.assertEqual(result[0], "failure")
        self.assertIn("20m", result[1])
        self.assertEqual(elapsed, 1200)

    def test_transient_jobs_api_error_after_acquisition_does_not_reset_queue_deadline(self):
        responses = [jobs(job("in_progress", None))] * 11 + [OSError("transient"), jobs(job())]
        result, elapsed = self.wait(responses)
        self.assertEqual(result[0], "success")
        self.assertGreater(elapsed, 300)

    def test_ambiguous_or_truncated_job_listing_is_not_publication_evidence(self):
        for response in [jobs(job(), job()), dict(total_count=101, jobs=[job()])]:
            with self.subTest(response=response):
                with self.assertRaises(ValueError):
                    finalizer.publication_job(response)

    def test_reused_sandbox_runner_privileged_cached_or_wrong_run_labels_fail_closed(self):
        for changes in [dict(runner_name="nsc-sandbox"),
                        dict(labels=["ubuntu-latest"]),
                        dict(labels=[finalizer.MACHINE_LABEL, "namespace-features:github.run-id=13"]),
                        dict(labels=[finalizer.MACHINE_LABEL, "namespace-features:container.privileged=true"]),
                        dict(labels=[finalizer.MACHINE_LABEL, "namespace-features:github.run-id=12", "nscloud-cache-tag-staging"])]:
            with self.subTest(changes=changes):
                result, _ = self.wait([jobs(dict(job(), **changes))])
                self.assertEqual(result[0], "failure")
                self.assertIn("not isolated", result[1])

    def test_canceled_before_runner_assignment_has_an_actionable_acquisition_failure(self):
        result, elapsed = self.wait([jobs(dict(job(conclusion="cancelled"), runner_name=""))])
        self.assertEqual(result[0], "failure")
        self.assertIn("without acquiring", result[1])
        self.assertEqual(elapsed, 0)

    def test_in_progress_without_runner_name_is_observed_as_not_yet_acquired(self):
        result, elapsed = self.wait([jobs(dict(job("in_progress", None), runner_name="")), jobs(job())])
        self.assertEqual(result[0], "success")
        self.assertEqual(elapsed, 30)

    def test_canceled_missing_or_failed_audits_never_wait_or_post_green(self):
        wait = Mock(side_effect=AssertionError("no publisher wait after failed audit"))
        for result in ["cancelled", "skipped", ""]:
            for state in ["success", "failure", ""]:
                self.assertEqual(finalizer.terminal_state(dict(ENV, BUILD_JOB_RESULT=result,
                    BUILD_STATE=state), wait=wait)[0], "failure")
        for result in ["success", "failure"]:
            for state in ["failure", ""]:
                self.assertEqual(finalizer.terminal_state(dict(ENV, BUILD_JOB_RESULT=result,
                    BUILD_STATE=state), wait=wait)[0], "failure")

    def test_report_failure_after_successful_audits_still_requires_publication(self):
        env = dict(ENV, BUILD_JOB_RESULT="failure", BUILD_STATE="success")
        for published in ["success", "failure"]:
            with self.subTest(published=published):
                wait = Mock(return_value=(published, "publication result"))
                self.assertEqual(finalizer.terminal_state(env, wait=wait)[0], published)
                wait.assert_called_once_with(12, 2)

    def test_unconfigured_publication_preserves_existing_optional_behavior(self):
        wait = Mock(side_effect=AssertionError("publication not configured"))
        self.assertEqual(finalizer.terminal_state(dict(ENV, PUBLICATION_REQUIRED="false"), wait=wait)[0], "success")

    def test_current_generation_revalidated_and_stale_generation_rejected(self):
        env = dict(ENV, BORS_STAGING="true", BORS_BATCH_ID="7", BORS_BASE_REF="main", BORS_BASE_SHA="b" * 40)
        batch = dict(id=7, base="main", state="running", head_sha="a" * 40, base_sha="b" * 40,
                     train=dict(candidate_id=2, generation=3, staging_ref="staging-candidate-2-3"))
        data = dict(schema="tauceti-bors.observation/v1", repo=finalizer.REPO, base="main", requested_batch=batch)
        wait = Mock(return_value=("success", "confirmed"))
        observe = Mock(return_value=data)
        self.assertEqual(finalizer.terminal_state(env, wait=wait, observe=observe)[0], "success")
        observe.assert_called_once_with(7, "main")
        withdrawn = copy.deepcopy(data)
        withdrawn["requested_batch"].update(state="canceled", head_sha=None, train=None)
        self.assertEqual(finalizer.terminal_state(env, wait=wait, observe=lambda *_: withdrawn),
                         ("withdrawn", "batch withdrawn; no verdict posted"))
        for field, value in [("id", 8), ("head_sha", "c" * 40),
                             ("train", dict(candidate_id=2, generation=4, staging_ref="staging-candidate-2-3"))]:
            stale = copy.deepcopy(data)
            stale["requested_batch"][field] = value
            self.assertEqual(finalizer.terminal_state(env, wait=wait, observe=lambda *_: stale)[0], "failure")
        with patch.object(finalizer.time, "sleep"):
            self.assertEqual(finalizer.terminal_state(env, wait=wait, observe=Mock(side_effect=OSError()))[0], "failure")
        observe = Mock(side_effect=[OSError(), OSError(), data])
        with patch.object(finalizer.time, "sleep") as sleep:
            self.assertEqual(finalizer.terminal_state(env, wait=wait, observe=observe)[0], "success")
            self.assertEqual(observe.call_count, 3)
            self.assertEqual([call.args for call in sleep.call_args_list], [(5,), (10,)])

    def test_status_uses_exact_sha_and_retries_boundedly(self):
        for state in ["success", "failure"]:
            with patch.dict(os.environ, ENV, clear=True), patch.object(finalizer, "terminal_state", return_value=(state, "result")), \
                 patch.object(finalizer, "api", side_effect=[dict(run_attempt=2), [], OSError(), dict(run_attempt=2), [], {}]) as post, \
                 patch.object(finalizer.time, "sleep"), \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(finalizer.main(), 0 if state == "success" else 1)
                self.assertEqual(post.call_count, 6)
                path, payload = post.call_args.args
                self.assertEqual(path, "/statuses/" + ENV["STATUS_SHA"])
                self.assertEqual(payload["state"], state)
                self.assertEqual(payload["context"], "build")
                self.assertEqual(payload["target_url"], "https://github.com/TauCetiProject/TauCeti/actions/runs/12")
        with patch.dict(os.environ, dict(ENV, STATUS_SHA="main"), clear=True), patch.object(finalizer, "api") as post, \
             contextlib.redirect_stderr(io.StringIO()):
            self.assertEqual(finalizer.main(), 1)
            post.assert_not_called()

    def test_known_superseded_attempt_skips_status_and_canceled_run_cannot_be_green(self):
        for latest, count, posted_state in [(dict(run_attempt=3), 1, None),
                                            (dict(run_attempt=2, conclusion="cancelled"), 3, "failure")]:
            with patch.dict(os.environ, ENV, clear=True), \
                 patch.object(finalizer, "terminal_state", return_value=("success", "confirmed")), \
                 patch.object(finalizer, "api", side_effect=[latest, [], {}]) as post, \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(finalizer.main(), 1)
                self.assertEqual(post.call_count, count)
                if posted_state:
                    self.assertEqual(post.call_args.args[1]["state"], posted_state)

    def test_observation_api_uses_shared_client_and_conditional_attempt_reads(self):
        client = Mock()
        with patch.object(finalizer, "_client", client):
            finalizer.api("/actions/runs/12/attempts/2/jobs?per_page=100")
        client.request.assert_called_once_with("GET", "repos/TauCetiProject/TauCeti/actions/runs/12/attempts/2/jobs?per_page=100",
                                               None, conditional=True, idempotent=False)

    def test_quota_exhaustion_exits_without_fast_retry_and_preserves_intent(self):
        with tempfile.TemporaryDirectory() as directory:
            target = str(Path(directory) / "intent.json")
            with patch.dict(os.environ, dict(ENV, TAUCETI_STATUS_INTENT=target), clear=True), \
                 patch.object(finalizer, "terminal_state", return_value=("success", "confirmed")), \
                 patch.object(finalizer, "api", side_effect=finalizer.Deferred("ci-status-app", finalizer.time.time() + 4000)) as post, \
                 patch.object(finalizer.time, "sleep") as sleep, \
                 contextlib.redirect_stderr(io.StringIO()):
                self.assertEqual(finalizer.main(), 75)
            post.assert_called_once()
            sleep.assert_not_called()
            intent = json.loads(Path(target).read_text())
            self.assertEqual(intent["payload"]["state"], "success")
            with patch.object(finalizer, "terminal_state", side_effect=AssertionError("must not rebuild")), \
                 patch.object(finalizer, "api", side_effect=[dict(run_attempt=2), [], {}]) as post, \
                 contextlib.redirect_stdout(io.StringIO()):
                self.assertEqual(finalizer.main(["--resume", target]), 0)
            self.assertEqual(post.call_args.args[0], "/statuses/" + ENV["STATUS_SHA"])

    def test_resuming_intent_rejects_tampering_and_fences_successor(self):
        payload = dict(state="success", context="build", description="ok",
                       target_url="https://github.com/TauCetiProject/TauCeti/actions/runs/12")
        original = finalizer.status_intent(ENV, payload)
        for field, value in [("revision", "main"), ("repo", "other/repo"), ("attempt", 0),
                             ("run_id", "12"), ("payload", dict(payload, context="arbitrary")),
                             ("payload", dict(payload, target_url="https://evil.example"))]:
            with self.subTest(field=field, value=value), self.assertRaises(ValueError):
                finalizer.validate_intent(dict(original, **{field: value}))
        with patch.object(finalizer, "api", return_value=dict(run_attempt=3)) as post, \
             contextlib.redirect_stdout(io.StringIO()):
            self.assertEqual(finalizer.publish(original), 1)
        post.assert_called_once()


class WorkflowBoundaryTests(unittest.TestCase):
    def test_retired_namespace_canary_is_not_current_publication_evidence(self):
        fixture = json.loads((ROOT / "scripts/publication_capacity_fixture.json").read_text())
        self.assertEqual(fixture["workflow_sha"], "d596be5aa001a0187cc3a3c7890314d7b0782e4a")
        by_name = {item["name"]: item for item in fixture["jobs"]}
        self.assertEqual(len({item["runner_name"] for item in fixture["jobs"]}), 2)
        for name, shape in [("finalizer-capacity", "2x4"), ("publisher-capacity", "4x8")]:
            item = by_name[name]
            self.assertEqual(item["conclusion"], "success")
            self.assertEqual(set(item["labels"]), {
                f"nscloud-ubuntu-24.04-amd64-{shape}-with-features;job.priority=0",
                f"namespace-features:github.run-id={fixture['run_id']}"})
        # Only the sandbox identity is synthetic; publisher labels/name are verbatim API evidence.
        sandbox = dict(name="sandboxed-build", runner_name="fixture-sandbox")
        self.assertFalse(finalizer.isolated_runner(dict(jobs=[sandbox]), by_name["publisher-capacity"], fixture["run_id"]))

    def test_separate_unprivileged_priority_runner_and_scoped_tokens(self):
        report = PR["finalize-merge-group-build"]
        publisher = PUB["jobs"]["publish"]
        for part, shape in [(report, "2x4"), (publisher, "4x8")]:
            from test_pick_runner import expression
            self.assertEqual(expression(part["runs-on"], event="repository_dispatch", action="tauceti-bors-staging"),
                             ["self-hosted", "linux", "x64", "tauceti-fleet-queue-control",
                              "fleet-74773fc7f54d4877add11d80113fe340"])
            self.assertEqual(expression(part["runs-on"]), "ubuntu-24.04")
        self.assertEqual(report["needs"], "sandboxed-build")
        self.assertEqual(report["permissions"], {"contents": "read", "actions": "read", "statuses": "write"})
        self.assertEqual(report["timeout-minutes"], 30)
        self.assertEqual(PUB["permissions"], {"contents": "read"})
        checkout = report["steps"][0]["with"]
        self.assertEqual(checkout["ref"], "${{ github.workflow_sha }}")
        self.assertIs(checkout["persist-credentials"], False)
        self.assertNotIn("LAKE_CACHE_KEY", str(report))
        self.assertIn("tauceti-bors-staging", report["if"])
        gate = PR["publish-merge-group-cache"]
        self.assertIn("!cancelled()", gate["if"])
        self.assertIn("outputs.build-state == 'success'", gate["if"])
        self.assertIn("publication-required == 'true'", gate["if"])
        self.assertIs(gate["with"]["publication-required"], True)
        self.assertNotIn("LAKE_CACHE_KEY", str(PR["sandboxed-build"]))

    def test_publisher_only_reads_pin_and_trusted_tools_and_secret_is_step_local(self):
        steps = PUB["jobs"]["publish"]["steps"]
        checkouts = [step["with"] for step in steps if step.get("uses", "").startswith("actions/checkout@")]
        self.assertEqual(checkouts[0]["sparse-checkout"], "lean-toolchain")
        self.assertEqual(checkouts[0]["ref"], "${{ inputs.revision }}")
        self.assertEqual(checkouts[1]["ref"], "${{ github.workflow_sha }}")
        self.assertTrue(all(c["persist-credentials"] is False for c in checkouts))
        holders = [step["name"] for step in steps if "secrets.LAKE_CACHE_KEY" in str(step)]
        self.assertEqual(holders, ["Publish the staged Lake cache"])
        self.assertNotIn("actions/cache", str(steps))
        confirm = next(step for step in steps if step.get("name") == finalizer.CONFIRM)
        self.assertIn('--expected "$RUNNER_TEMP/lake-publication-plan/outputs.jsonl"', confirm["run"])

    def test_missing_or_empty_secret_fails_required_publication_without_upload(self):
        upload = next(step for step in PUB["jobs"]["publish"]["steps"] if step.get("id") == "upload")
        with tempfile.TemporaryDirectory() as directory:
            for secret in ["", "  "]:
                env = dict(os.environ, S3_ARTIFACT_ENDPOINT="https://example.org/artifacts",
                           S3_REVISION_ENDPOINT="https://example.org/revisions",
                           PUBLIC_ARTIFACT_ENDPOINT="https://example.org/artifacts",
                           PUBLIC_REVISION_ENDPOINT="https://example.org/revisions",
                           LAKE_CACHE_KEY_RAW=secret, PUBLICATION_REQUIRED="true", REVISION="a" * 40,
                           GITHUB_OUTPUT=directory + "/output")
                result = subprocess.run(["bash", "-c", upload["run"]], env=env, capture_output=True, text=True)
                self.assertEqual(result.returncode, 1)
                self.assertIn("::error::", result.stdout)
                self.assertFalse(Path(env["GITHUB_OUTPUT"]).exists())


if __name__ == "__main__":
    unittest.main()
