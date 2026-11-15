#!/usr/bin/env python3
"""Native Lake publication and the small credential-boundary copy."""

import contextlib
import io
import json
import os
import ssl
import subprocess
import sys
import tempfile
import threading
import unittest
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from pathlib import Path

import lake_cache_publish as publish

INTEGRATION = "--integration" in sys.argv
if INTEGRATION:
    sys.argv.remove("--integration")
TOOLCHAIN = "leanprover/lean4:v4.36.0-rc2"
SHA = "a" * 40
NAME = "0123456789abcdef.ltar"


class PublicationTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.addCleanup(self.temp.cleanup)
        self.root = Path(self.temp.name)
        self.source = self.root / "source"
        self.source.mkdir()
        self.raw = ('"2026-03-17"\n' + json.dumps(["1" * 16, NAME]) + "\n").encode()
        (self.source / "outputs.jsonl").write_bytes(self.raw)
        (self.source / NAME).write_bytes(b"archive")

    def copy(self):
        with contextlib.redirect_stdout(io.StringIO()):
            return publish.stage(self.source, self.root / "copied")

    def test_full_native_stage_has_no_additional_manifest_or_network(self):
        result = self.copy()
        self.assertEqual(set(p.name for p in (self.root / "copied").iterdir()), {"outputs.jsonl", NAME})
        self.assertEqual((self.root / "copied" / NAME).read_bytes(), b"archive")
        self.assertEqual(result["upload_bytes"], result["full_bytes"])
        self.assertEqual(result["inherited"], 0)
        (self.source / NAME).write_bytes(b"changed later")
        self.assertEqual((self.root / "copied" / NAME).read_bytes(), b"archive")

    def test_missing_artifact_never_leaves_a_partial_copy(self):
        (self.source / NAME).unlink()
        with self.assertRaises(ValueError):
            self.copy()
        self.assertFalse((self.root / "copied").exists())

    def test_symlink_and_fifo_rejected_without_reading_them(self):
        for kind in ("symlink", "fifo"):
            with self.subTest(kind=kind):
                target = self.source / NAME
                target.unlink()
                if kind == "symlink":
                    target.symlink_to(self.source / "outputs.jsonl")
                else:
                    os.mkfifo(target)
                with self.assertRaises((ValueError, OSError)):
                    self.copy()
                self.assertFalse((self.root / "copied").exists())

    def test_unsafe_or_partial_maps_and_extra_files_are_rejected(self):
        for data in (b"", b'"2026-03-17"\n', b'"2026-03-17"\n["1111111111111111","../secret"]\n'):
            with self.subTest(data=data):
                (self.source / "outputs.jsonl").write_bytes(data)
                with self.assertRaises((ValueError, UnicodeError)):
                    self.copy()
        (self.source / "outputs.jsonl").write_bytes(self.raw)
        (self.source / "publication.json").write_text("{}")
        with self.assertRaises(ValueError):
            self.copy()

    def test_historical_input_aliases_can_share_one_archive(self):
        (self.source / "outputs.jsonl").write_bytes(self.raw + (json.dumps(["2" * 16, NAME]) + "\n").encode())
        self.assertEqual(self.copy()["objects"], 1)


@unittest.skipUnless(INTEGRATION, "pass --integration with stock Lake installed")
class StockLakePublication(unittest.TestCase):
    def test_native_upload_retry_restore_and_changed_source(self):
        with tempfile.TemporaryDirectory(prefix="native-publication-") as temporary:
            root = Path(temporary)
            objects, puts, fail = {}, [], [True]

            class Handler(BaseHTTPRequestHandler):
                def log_message(self, *args):
                    pass

                def do_GET(self):
                    if self.path not in objects:
                        self.send_error(404)
                        return
                    data = objects[self.path]
                    self.send_response(200)
                    self.send_header("Content-Length", str(len(data)))
                    self.end_headers()
                    self.wfile.write(data)

                def do_PUT(self):
                    data = self.rfile.read(int(self.headers["Content-Length"]))
                    if fail[0] and "/artifacts/" in self.path:
                        self.send_error(403)
                        return
                    objects[self.path] = data
                    puts.append(self.path)
                    self.send_response(200)
                    self.send_header("Content-Length", "0")
                    self.end_headers()

            cert, key = root / "cert.pem", root / "key.pem"
            subprocess.run(
                [
                    "openssl",
                    "req",
                    "-x509",
                    "-newkey",
                    "rsa:2048",
                    "-nodes",
                    "-days",
                    "1",
                    "-keyout",
                    str(key),
                    "-out",
                    str(cert),
                    "-subj",
                    "/CN=localhost",
                    "-addext",
                    "subjectAltName=DNS:localhost",
                ],
                check=True,
                capture_output=True,
            )
            server = ThreadingHTTPServer(("localhost", 0), Handler)
            ctx = ssl.SSLContext(ssl.PROTOCOL_TLS_SERVER)
            ctx.load_cert_chain(cert, key)
            server.socket = ctx.wrap_socket(server.socket, server_side=True)
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            thread.start()
            self.addCleanup(server.server_close)
            self.addCleanup(server.shutdown)
            endpoint = f"https://localhost:{server.server_port}"
            env = {
                **os.environ,
                "CURL_CA_BUNDLE": str(cert),
                "LAKE_ARTIFACT_CACHE": "true",
                "LAKE_RESTORE_ARTIFACTS": "true",
            }
            for key in ("LAKE_NO_CACHE", "LAKE_CONFIG", "LAKE_CACHE_KEY"):
                env.pop(key, None)

            def project(name):
                p = root / name
                p.mkdir()
                (p / "lean-toolchain").write_text(TOOLCHAIN + "\n")
                (p / "lakefile.toml").write_text(
                    'name = "TauCeti"\nplatformIndependent = true\n'
                    'defaultTargets = ["TauCeti"]\n[[lean_lib]]\nname = "TauCeti"\n'
                )
                (p / "TauCeti.lean").write_text("module\npublic def value : Nat := 7\n")
                return p

            def lake(p, *args, ok=True, extra=None):
                result = subprocess.run(
                    ["lake", *args],
                    cwd=p,
                    env={**env, "LAKE_CACHE_DIR": str(p / ".lake/cache"), **(extra or {})},
                    capture_output=True,
                    text=True,
                    timeout=120,
                )
                self.assertEqual(result.returncode == 0, ok, result.stdout + result.stderr)
                return result.stdout + result.stderr

            producer = project("producer")
            lake(producer, "update")
            lake(producer, "build", "--iofail", "--rehash", "-o", ".lake/outputs.jsonl")
            lake(producer, "cache", "stage", ".lake/outputs.jsonl", str(root / "native-stage"))
            with contextlib.redirect_stdout(io.StringIO()):
                publish.stage(root / "native-stage", root / "publisher")
            upload = [
                "cache",
                "put-staged",
                str(root / "publisher"),
                "--rev=" + SHA,
                "--repo=TauCetiProject/TauCeti",
                "--toolchain=" + TOOLCHAIN,
            ]
            credentials = {
                "LAKE_CACHE_KEY": "test-id:test-secret",
                "LAKE_CACHE_ARTIFACT_ENDPOINT": endpoint + "/artifacts",
                "LAKE_CACHE_REVISION_ENDPOINT": endpoint + "/revisions",
            }
            lake(root / "publisher", *upload, ok=False, extra=credentials)
            self.assertFalse(any("/revisions/" in p for p in objects))
            fail[0] = False
            sentinel = root / "executed-candidate-config"
            (root / "publisher/lakefile.lean").write_text(
                'import Lake\n#eval IO.FS.writeFile "' + str(sentinel) + '" "bad"\n'
            )
            lake(root / "publisher", *upload, extra=credentials)
            self.assertFalse(sentinel.exists(), "put-staged must not execute workspace code")
            self.assertIn("/revisions/", puts[-1])
            consumer = project("consumer")
            lake(consumer, "update")
            config = root / "lake.toml"
            config.write_text(
                '[[cache.service]]\nname = "test"\nkind = "s3"\nartifactEndpoint = "' + endpoint + '/artifacts"\n'
                'revisionEndpoint = "' + endpoint + '/revisions"\n'
            )
            fetch = ["cache", "get", "--service=test", "--repo=TauCetiProject/TauCeti", "--rev=" + SHA]
            lake(consumer, *fetch, extra={"LAKE_CONFIG": str(config)})
            restored = lake(consumer, "build", "--iofail", "-o", ".lake/restored.jsonl")
            self.assertIn("Unpacked TauCeti", restored)
            self.assertNotIn("Built TauCeti", restored)
            self.assertEqual(
                publish.mapping((producer / ".lake/outputs.jsonl").read_bytes()),
                publish.mapping((consumer / ".lake/restored.jsonl").read_bytes()),
            )
            (consumer / "TauCeti.lean").write_text("module\npublic def value : Nat := 8\n")
            changed = lake(consumer, "build", "--iofail", "-o", ".lake/changed.jsonl")
            self.assertIn("Built TauCeti", changed)
            artifact = next(p for p in objects if "/artifacts/" in p)
            objects[artifact] = b"corrupt artifact"
            damaged = project("damaged")
            lake(damaged, "update")
            lake(damaged, *fetch, ok=False, extra={"LAKE_CONFIG": str(config)})


if __name__ == "__main__":
    unittest.main()
