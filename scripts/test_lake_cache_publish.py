#!/usr/bin/env python3
"""Incremental publication safety tests, plus stock Lake restore over local TLS."""
import contextlib
import hashlib
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
import io
import json
import os
from pathlib import Path
import shutil
import ssl
import subprocess
import sys
import tempfile
import threading
import unittest
from unittest.mock import patch

import lake_cache_publish as publish
import lake_cache_reuse as reuse

INTEGRATION = "--integration" in sys.argv
if INTEGRATION:
    sys.argv.remove("--integration")
ROOT = Path(__file__).resolve().parents[1]
TOOLCHAIN = (ROOT / "lean-toolchain").read_text().strip()
SHA = "a" * 40
NAME = "0123456789abcdef.ltar"
OTHER = "fedcba9876543210.ltar"
PUBLIC = "https://cache.example/artifacts"
REVISION = "https://cache.example/revisions"


def record(data):
    return publish.hashes(io.BytesIO(data))


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.temporary = tempfile.TemporaryDirectory()
        self.addCleanup(self.temporary.cleanup)
        self.root = Path(self.temporary.name)
        self.project = self.root / "project"
        self.artifacts = self.project / ".lake/cache/artifacts"
        self.artifacts.mkdir(parents=True)
        self.data = b"archive bytes"
        (self.artifacts / NAME).write_bytes(self.data)
        (self.artifacts / OTHER).write_bytes(b"new archive")
        (self.project / "lean-toolchain").write_text(TOOLCHAIN)
        self.raw = ('"2026-03-17"\n' + json.dumps(["1" * 16, NAME]) + '\n'
                    + json.dumps(["2" * 16, OTHER]) + '\n').encode()
        (self.project / ".lake/outputs.jsonl").write_bytes(self.raw)
        self.index = self.root / "trusted.json"
        self.saved = {"version": 1, "toolchain": TOOLCHAIN,
                      "entries": {"1" * 16: [NAME, hashlib.sha256(self.data).hexdigest()]}}
        self.index.write_text(json.dumps(self.saved))
        self.stage = self.root / "stage"
        self.plan = self.root / "plan"

    def stage_outputs(self, available=True, full=False):
        with patch.object(publish, "available", side_effect=lambda _public, records: set(records) if available else set()), contextlib.redirect_stdout(io.StringIO()):
            return publish.stage(self.project, self.index, self.stage, PUBLIC, full)

    def prepare(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return publish.prepare(self.stage, self.plan, TOOLCHAIN, SHA, PUBLIC, PUBLIC, REVISION)

    def test_unchanged_omitted_new_staged_and_full_map_preserved(self):
        stats = self.stage_outputs()
        self.assertEqual(stats["inherited"], 1)
        self.assertEqual(stats["staged_bytes"], len(b"new archive"))
        self.assertEqual((self.stage / "outputs.jsonl").read_bytes(), self.raw)
        self.assertFalse((self.stage / NAME).exists())
        self.assertEqual((self.stage / OTHER).read_bytes(), b"new archive")
        with patch.object(publish, "verify_remote", return_value=len(self.data)) as verify:
            stats = self.prepare()
        verify.assert_called_once_with(PUBLIC, {NAME: record(self.data)})
        self.assertEqual(stats["uploaded_objects"], 1)
        config = (self.plan / "artifacts.curl").read_text()
        self.assertNotIn(NAME, config)
        self.assertIn(OTHER, config)
        self.assertEqual((self.plan / "outputs.jsonl").read_bytes(), self.raw)

    def test_all_inherited_objects_still_publish_the_complete_map(self):
        self.raw = self.raw.splitlines()[0] + b"\n" + self.raw.splitlines()[1] + b"\n"
        (self.project / ".lake/outputs.jsonl").write_bytes(self.raw)
        self.stage_outputs()
        with patch.object(publish, "verify_remote", return_value=len(self.data)):
            stats = self.prepare()
        self.assertEqual(stats["uploaded_objects"], 0)
        self.assertEqual((self.plan / "artifacts.curl").read_text(), "")
        self.assertEqual((self.plan / "outputs.jsonl").read_bytes(), self.raw)

    def test_missing_or_corrupt_remote_falls_back_to_local_archive(self):
        stats = self.stage_outputs(available=False)
        self.assertEqual(stats["inherited"], 0)
        self.assertEqual(stats["fallback_objects"], 1)
        self.assertEqual((self.stage / NAME).read_bytes(), self.data)
        self.assertEqual(self.prepare()["uploaded_objects"], 2)

    def test_widespread_misses_have_a_bounded_full_staging_fallback(self):
        records, lines = {}, ['"2026-03-17"']
        for i in range(300):
            name = f"{i:016x}.ltar"
            (self.artifacts / name).write_bytes(self.data)
            records[f"{i:016x}"] = [name, hashlib.sha256(self.data).hexdigest()]
            lines.append(json.dumps([f"{i:016x}", name]))
        (self.project / ".lake/outputs.jsonl").write_text("\n".join(lines) + "\n")
        self.saved["entries"] = records
        self.index.write_text(json.dumps(self.saved))
        with patch.object(publish, "available", return_value=set()) as probe:
            stats = self.stage_outputs_with_probe()
        self.assertEqual(probe.call_count, 1)
        self.assertLessEqual(len(probe.call_args.args[1]), publish.BATCH_SIZE)
        self.assertEqual(stats["inherited"], 0)
        self.assertEqual(stats["fallback_objects"], 300)
        self.assertEqual(len(list(self.stage.glob("*.ltar"))), 300)

    def stage_outputs_with_probe(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return publish.stage(self.project, self.index, self.stage, PUBLIC)

    def test_full_publication_override_uses_no_availability_requests(self):
        with patch.object(publish, "available", side_effect=AssertionError("no HEAD")):
            with contextlib.redirect_stdout(io.StringIO()):
                publish.stage(self.project, self.index, self.stage, PUBLIC, full=True)
        self.assertEqual(self.prepare()["inherited"], 0)

    def test_snapshot_toolchain_change_or_stale_digest_disables_omission(self):
        for mutation in ("toolchain", "digest", "missing", "malformed"):
            with self.subTest(mutation=mutation):
                saved = json.loads(json.dumps(self.saved))
                if mutation == "toolchain":
                    saved["toolchain"] = "leanprover/lean4:v4.0.0"
                elif mutation == "digest":
                    saved["entries"]["1" * 16][1] = "f" * 64
                elif mutation == "missing":
                    saved = {}
                else:
                    saved = []
                self.index.write_text(json.dumps(saved))
                stats = self.stage_outputs()
                self.assertEqual(stats["inherited"], 0)
                shutil.rmtree(self.stage)

    def test_candidate_hash_sidecars_do_not_decide_omission(self):
        (self.artifacts / (NAME + ".hash")).write_text(self.saved["entries"]["1" * 16][1])
        (self.artifacts / NAME).write_bytes(b"candidate replacement")
        self.assertEqual(self.stage_outputs()["inherited"], 0)

    def test_missing_archive_or_symlinked_candidate_paths_fail_closed(self):
        for path in (self.artifacts / NAME, self.artifacts, self.artifacts.parent,
                     self.project / ".lake/outputs.jsonl", self.project / "lean-toolchain"):
            with self.subTest(path=path):
                original = path.with_name(path.name + ".original")
                path.rename(original)
                path.symlink_to(original)
                with self.assertRaises((OSError, ValueError)):
                    self.stage_outputs()
                self.assertFalse(self.stage.exists())
                path.unlink()
                original.rename(path)

    def test_hostile_staging_names_types_and_parent_symlinks(self):
        self.stage_outputs(available=False)
        for name in ("evil.hash", "../escape", "a/b", "BAD.ltar", "--config"):
            with self.subTest(name=name):
                raw = ('"2026-03-17"\n' + json.dumps(["1" * 16, name]) + '\n').encode()
                (self.stage / "outputs.jsonl").write_bytes(raw)
                with self.assertRaises(ValueError):
                    self.prepare()
                self.assertFalse(self.plan.exists())
        (self.stage / "outputs.jsonl").write_bytes(self.raw)
        for name in (NAME, "publication.json", "outputs.jsonl"):
            path = self.stage / name
            original = self.root / (name + ".original")
            path.rename(original)
            path.symlink_to(original)
            with self.assertRaises(OSError):
                self.prepare()
            path.unlink()
            original.rename(path)
        fifo = self.stage / "aaaaaaaaaaaaaaaa.ltar"
        os.mkfifo(fifo)
        with self.assertRaises(ValueError):
            self.prepare()
        fifo.unlink()
        nested = self.stage / "bbbbbbbbbbbbbbbb.ltar"
        nested.mkdir()
        with self.assertRaises(ValueError):
            self.prepare()
        nested.rmdir()
        alias = self.root / "alias"
        alias.symlink_to(self.stage)
        with self.assertRaises(OSError):
            publish.prepare(alias, self.plan, TOOLCHAIN, SHA, PUBLIC, PUBLIC, REVISION)

    def test_manifest_coverage_scope_digest_and_duplicate_map_validation(self):
        self.stage_outputs(available=False)
        manifest_path = self.stage / "publication.json"
        original = json.loads(manifest_path.read_text())
        mutations = []
        for field, value in (("toolchain", "leanprover/lean4:v4.0.0"),
                             ("inherited", [NAME, NAME]), ("inherited", ["../escape"]),
                             ("objects", {}), ("version", 2)):
            changed = dict(original, **{field: value})
            mutations.append(changed)
        changed = json.loads(json.dumps(original))
        changed["objects"][NAME]["sha256"] = "f" * 64
        mutations.append(changed)
        changed = json.loads(json.dumps(original))
        changed["objects"][NAME]["size"] = True
        mutations.append(changed)
        for manifest in mutations:
            manifest_path.write_text(json.dumps(manifest))
            with self.assertRaises(ValueError):
                self.prepare()
        manifest_path.write_text(json.dumps(original))
        (self.stage / "outputs.jsonl").write_bytes(self.raw + self.raw.splitlines()[1] + b"\n")
        with self.assertRaises(ValueError):
            self.prepare()

    def test_publication_requires_known_schema_from_shared_parser(self):
        with self.assertRaisesRegex(ValueError, "unsupported"):
            publish.mapping(self.raw.replace(b"2026-03-17", b"future-schema"))

    def test_old_full_staging_producer_remains_supported(self):
        self.stage_outputs(available=False)
        (self.stage / "publication.json").unlink()
        self.assertEqual(self.prepare()["uploaded_objects"], 2)

    def test_remote_sha_check_retries_bounded_and_does_not_trust_sidecars(self):
        attempts = []
        def fetch(_public, records, target, head=False):
            attempts.append(set(records))
            for name in records:
                (target / name).write_bytes(b"corrupt")
        with patch.object(publish, "transfer", side_effect=fetch):
            with self.assertRaisesRegex(ValueError, "FULL_PUBLICATION=1"):
                publish.verify_remote(PUBLIC, {NAME: record(self.data)})
        self.assertEqual(len(attempts), 3)
        attempts.clear()
        def eventual(_public, records, target, head=False):
            attempts.append(set(records))
            for name in records:
                (target / name).write_bytes(b"corrupt" if name == NAME and len(attempts) == 1 else self.data)
        with patch.object(publish, "transfer", side_effect=eventual):
            self.assertEqual(publish.verify_remote(PUBLIC, {NAME: record(self.data), OTHER: record(self.data)}), 2 * len(self.data))
        self.assertEqual(attempts, [{NAME, OTHER}, {NAME}])

    def test_public_transfer_has_bounded_requests_and_no_auth_options(self):
        with patch.object(publish.subprocess, "run") as run:
            publish.transfer(PUBLIC, {NAME: record(self.data)}, self.root)
        args = run.call_args.args[0]
        self.assertEqual(args[args.index("--parallel-max") + 1], str(publish.WORKERS))
        self.assertEqual(args[args.index("--max-time") + 1], "30")
        self.assertEqual(args[args.index("--max-filesize") + 1], str(len(self.data) + 1))
        config = Path(args[args.index("--config") + 1]).read_text()
        self.assertIn(publish.artifact_url(PUBLIC, NAME), config)
        self.assertNotIn("--user", args)
        self.assertNotIn("--aws-sigv4", args)
        self.assertNotIn("LAKE_CACHE_KEY", config)

    def test_failed_inheritance_never_emits_upload_plan(self):
        self.stage_outputs()
        with patch.object(publish, "verify_remote", side_effect=ValueError("missing")):
            with self.assertRaises(ValueError):
                self.prepare()
        self.assertFalse(self.plan.exists())

    def test_endpoints_cannot_inject_config_or_exfiltrate_credentials(self):
        for value in ("http://cache.example", "https://user:pass@cache.example", "https://cache.example?q=x",
                      'https://cache.example/"x', "https://cache.example/\n"):
            with self.assertRaises(ValueError):
                publish.endpoint(value)

    def test_planner_refuses_upload_credentials(self):
        env = dict(os.environ, LAKE_CACHE_KEY="test-only")
        result = subprocess.run([sys.executable, str(ROOT / "scripts/lake_cache_publish.py"), "--help"],
                                env=env, capture_output=True, text=True)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("must never receive upload credentials", result.stderr)

    def test_workflow_boundaries_and_producer_eligibility(self):
        workflow = (ROOT / ".github/workflows/pr-build.yml").read_text()
        stage = workflow.split("- name: Prepare merge-group cache artifact metadata", 1)[1].split("- name:", 1)[0]
        self.assertIn("env.IS_BATCH == 'true'", stage)
        self.assertIn("steps.build.outcome == 'success'", stage)
        self.assertIn("python3 gate/scripts/lake_cache_publish.py stage", stage)
        self.assertIn("ref: ${{ github.workflow_sha }}", workflow)
        publisher = (ROOT / ".github/workflows/publish-lake-cache.yml").read_text()
        planner = publisher.split("- name: Validate staged data", 1)[1].split("- name:", 1)[0]
        upload = publisher.split("- name: Publish the staged Lake cache", 1)[1].split("- name:", 1)[0]
        self.assertNotIn("LAKE_CACHE_KEY", planner)
        self.assertIn("publisher-tools/scripts/lake_cache_publish.py prepare", planner)
        self.assertNotIn("python", upload)
        self.assertNotIn("lake cache", upload)
        self.assertLess(upload.index('"$PLAN/artifacts.curl"'), upload.index('"$PLAN/outputs.jsonl"'))
        self.assertIn("--fail-early", upload)
        tools = publisher.split("- name: Check out workflow-pinned publication planning tools", 1)[1].split("- name:", 1)[0]
        self.assertIn("ref: ${{ github.workflow_sha }}", tools)


@unittest.skipUnless(INTEGRATION, "pass --integration with stock Lake installed")
class StockLakePublication(unittest.TestCase):
    def test_incremental_upload_repair_retry_and_fresh_checkout_restore(self):
        with tempfile.TemporaryDirectory(prefix="lake-publication-test-") as temporary:
            root = Path(temporary)
            objects, puts, failures = {}, [], {}
            class Handler(BaseHTTPRequestHandler):
                def log_message(self, *args):
                    pass
                def do_HEAD(self):
                    self.respond(False)
                def do_GET(self):
                    self.respond(True)
                def respond(self, body):
                    data = objects.get(self.path)
                    if data is None:
                        self.send_error(404)
                        return
                    self.send_response(200)
                    self.send_header("Content-Length", str(len(data)))
                    self.send_header("ETag", '"' + hashlib.md5(data, usedforsecurity=False).hexdigest() + '"')
                    self.end_headers()
                    if body:
                        self.wfile.write(data)
                def do_PUT(self):
                    data = self.rfile.read(int(self.headers["Content-Length"]))
                    if failures.get(self.path, 0):
                        failures[self.path] -= 1
                        self.send_error(500)
                        return
                    objects[self.path] = data
                    puts.append(self.path)
                    self.send_response(200)
                    self.send_header("Content-Length", "0")
                    self.end_headers()
            cert, key = root / "cert.pem", root / "key.pem"
            subprocess.run(["openssl", "req", "-x509", "-newkey", "rsa:2048", "-nodes", "-days", "1",
                            "-keyout", str(key), "-out", str(cert), "-subj", "/CN=localhost",
                            "-addext", "subjectAltName=DNS:localhost"], check=True, capture_output=True)
            server = ThreadingHTTPServer(("localhost", 0), Handler)
            ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            ctx.load_cert_chain(cert, key)
            server.socket = ctx.wrap_socket(server.socket, server_side=True)
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            thread.start()
            self.addCleanup(server.server_close)
            self.addCleanup(server.shutdown)
            public = f"https://localhost:{server.server_port}/artifacts"
            revisions = f"https://localhost:{server.server_port}/revisions"
            toolchain = os.environ.get("ELAN_TOOLCHAIN") or TOOLCHAIN
            env = dict(os.environ, CURL_CA_BUNDLE=str(cert), LAKE_ARTIFACT_CACHE="true",
                       LAKE_RESTORE_ARTIFACTS="true", LAKE_NO_CACHE="true")
            def project(name):
                path = root / name
                path.mkdir()
                (path / "lean-toolchain").write_text(toolchain + "\n")
                (path / "lakefile.toml").write_text(
                    'name = "TauCeti"\nplatformIndependent = true\ndefaultTargets = ["TauCeti"]\n'
                    '[[lean_lib]]\nname = "TauCeti"\nglobs = ["TauCeti.*"]\n')
                (path / "TauCeti").mkdir()
                (path / "TauCeti.lean").write_text("module\n")
                (path / "TauCeti/A.lean").write_text("module\npublic def a : Nat := 42\n")
                (path / "TauCeti/B.lean").write_text("module\npublic def b : Nat := 7\n")
                return path
            def lake(path, *args, expected=0, extra=None):
                result = subprocess.run(["lake", *args], cwd=path,
                                        env=dict(env, LAKE_CACHE_DIR=str(path / ".lake/cache"), **(extra or {})),
                                        capture_output=True, text=True, timeout=120)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
            producer = project("producer")
            lake(producer, "build", "--iofail", "-o", ".lake/outputs.jsonl")
            initial = publish.mapping((producer / ".lake/outputs.jsonl").read_bytes())
            for name in initial:
                objects[f"/artifacts/{publish.REPOSITORY}/{name[:-5]}.art"] = (producer / ".lake/cache/artifacts" / name).read_bytes()
            # Snapshot the downloaded state, then overwrite the live records like Lake's build.
            old_stage = root / "old-stage"
            lake(producer, "cache", "stage", ".lake/outputs.jsonl", str(old_stage))
            consumer = project("consumer")
            lake(consumer, "cache", "unstage", str(old_stage))
            index = root / "snapshot.json"
            index.write_text(json.dumps(reuse.snapshot(consumer)))
            (consumer / "TauCeti/A.lean").write_text("module\npublic def a : Nat := 43\n")
            lake(consumer, "build", "--iofail")
            reuse.reconnect(consumer, json.loads(index.read_text()))
            lake(consumer, "build", "--no-build", "--rehash", "-o", ".lake/outputs.jsonl")
            current = publish.mapping((consumer / ".lake/outputs.jsonl").read_bytes())
            unchanged = initial & current
            self.assertGreater(len(unchanged), 0)
            self.assertGreater(len(current - initial), 0)
            def cycle(number, full=False):
                staging, plan = root / f"stage-{number}", root / f"plan-{number}"
                with patch.dict(os.environ, env), contextlib.redirect_stdout(io.StringIO()):
                    stats = publish.stage(consumer, index, staging, public, full)
                    publish.prepare(staging, plan, toolchain, SHA, public, public, revisions)
                return staging, plan, stats
            staging, plan, stats = cycle(1)
            self.assertEqual(stats["inherited"], len(unchanged))
            # Run the exact workflow upload shell, with dummy credentials to the TLS fixture.
            workflow = (ROOT / ".github/workflows/publish-lake-cache.yml").read_text()
            block = workflow.split("- name: Publish the staged Lake cache", 1)[1].split("- name:", 1)[0]
            shell = block.split("        run: |\n", 1)[1]
            lines = []
            for line in shell.splitlines():
                if line and not line.startswith("          "):
                    break
                lines.append(line[10:])
            shell = "\n".join(lines)
            def upload(plan, expected=0):
                target = root / "lake-publication-plan"
                if target.exists():
                    shutil.rmtree(target)
                # Keep config paths unchanged; workflow uses this path for config lookup.
                shutil.copytree(plan, target)
                upload_env = dict(env, RUNNER_TEMP=str(root), S3_ARTIFACT_ENDPOINT=public,
                                  S3_REVISION_ENDPOINT=revisions, PUBLIC_REVISION_ENDPOINT=revisions,
                                  PUBLIC_ARTIFACT_ENDPOINT=public, LAKE_CACHE_KEY_RAW="test:key",
                                  REVISION=SHA, PUBLICATION_REQUIRED="true", GITHUB_OUTPUT=str(root / "output"))
                result = subprocess.run(["bash", "-c", shell], env=upload_env, capture_output=True, text=True, timeout=120)
                self.assertEqual(result.returncode, expected, result.stdout + result.stderr)
            upload(plan)
            uploaded = set(puts)
            self.assertEqual(len(uploaded), len(current - unchanged) + 1)
            map_path = publish.exact_map_url(revisions, toolchain, SHA).split(f"localhost:{server.server_port}")[1]
            self.assertEqual(objects[map_path], (consumer / ".lake/outputs.jsonl").read_bytes())
            # Interrupted publication: objects already uploaded but no revision map.
            del objects[map_path]
            puts.clear()
            staging, plan, stats = cycle(2)
            changed = sorted(current - unchanged)[0]
            failures[f"/artifacts/{publish.REPOSITORY}/{changed[:-5]}.art"] = 3
            upload(plan, expected=22)
            self.assertNotIn(map_path, objects)
            upload(plan)
            self.assertIn(map_path, puts)
            # Same-size corruption and missing inherited objects both trigger bounded staging repair.
            broken = sorted(unchanged)
            first = f"/artifacts/{publish.REPOSITORY}/{broken[0][:-5]}.art"
            objects[first] = b"x" * len(objects[first])
            if len(broken) > 1:
                del objects[f"/artifacts/{publish.REPOSITORY}/{broken[1][:-5]}.art"]
            staging, plan, stats = cycle(3)
            self.assertGreater(stats["fallback_objects"], 0)
            upload(plan)
            staging, plan, stats = cycle(4, full=True)
            self.assertEqual(stats["inherited"], 0)
            self.assertEqual(stats["staged_bytes"], stats["full_bytes"])
            upload(plan)
            # A fresh checkout reads the COMPLETE map and stock Lake checks its artifact hashes.
            fresh = project("fresh")
            shutil.copyfile(consumer / "TauCeti/A.lean", fresh / "TauCeti/A.lean")
            subprocess.run(["git", "init", "-q", str(fresh)], check=True)
            subprocess.run(["git", "-C", str(fresh), "add", "."], check=True)
            subprocess.run(["git", "-C", str(fresh), "-c", "user.name=Test", "-c", "user.email=test@example.com",
                            "commit", "-qm", "fixture"], check=True)
            head = subprocess.check_output(["git", "-C", str(fresh), "rev-parse", "HEAD"], text=True).strip()
            objects[publish.exact_map_url(revisions, toolchain, head).split(f"localhost:{server.server_port}")[1]] = objects[map_path]
            config = root / "lake.toml"
            config.write_text(f'[[cache.service]]\nname="fixture"\nkind="s3"\nartifactEndpoint="{public}"\nrevisionEndpoint="{revisions}"\n')
            lake(fresh, "cache", "get", "--service", "fixture", "--repo", publish.REPOSITORY,
                 "--max-revs=1", extra={"LAKE_CONFIG": str(config), "LAKE_NO_CACHE": "false"})
            lake(fresh, "build", "--no-build", "--rehash", "-o", ".lake/restored.jsonl")
            self.assertEqual(publish.mapping((fresh / ".lake/restored.jsonl").read_bytes()), current)
            # --no-build rejects a stale map/source combination.
            (fresh / "TauCeti/A.lean").write_text("module\npublic def a : Nat := 44\n")
            lake(fresh, "build", "--no-build", "--rehash", "-o", ".lake/stale.jsonl", expected=3)


if __name__ == "__main__":
    unittest.main()
