"""Ensure every workflow that installs elan installs the same verified binary.

Run with: python3 scripts/test_elan_pin.py

elan chooses the `lake` and `lean` a job runs, so whoever controls the elan a workflow installs
controls what that job executes. That matters most in ci.yml's `publish-lake-cache` job, which
hands LAKE_CACHE_KEY to a `lake` the installer selected, and in pr-build.yml, where elan is
installed in the trusted phase before bwrap confines anything. So every workflow takes elan
from a pinned leanprover/elan release verified by SHA-256, and none of them runs the installer
served at https://elan.lean-lang.org/elan-init.sh, whose contents are whatever that host returns
at the moment of the request.

The pin is deliberately duplicated across workflows rather than shared through a composite
action, for the same reason bwrap's is: pr-build.yml sits on the merge queue's critical path
and runs from the base definition under pull_request_target, so a shared action introduced by a
pull request could not be exercised by that pull request's own build. This test is what stops
the copies drifting.

The checks below match the install as a single ordered block of adjacent lines, over a view of
the file with comment lines removed, and then require that nothing else in the file names the
archive or the installer. Counting the pieces separately would have let a commented-out or
otherwise dead copy of the approved block pay for a live step that installed elan some other
way. Both .yml and .yaml are scanned, since GitHub reads either, and every file in the directory
is scanned rather than a fixed list, so a workflow added later cannot quietly reintroduce the
unpinned install.

What this cannot do is recognise an arbitrary new way to obtain an elan; no textual check can.
It fixes the approved shape and closes the routes that were actually in use.

To bump the pin, change ELAN_VER and ELAN_SHA256 together in every workflow that declares them;
the checksum is that of the release's elan-x86_64-unknown-linux-gnu.tar.gz asset.
"""

import pathlib
import hashlib
import http.server
import io
import os
import subprocess
import tarfile
import tempfile
import threading
import re
import unittest

ROOT = pathlib.Path(__file__).resolve().parent.parent
WORKFLOW_DIR = ROOT / ".github/workflows"

SHA = re.compile(r"^\s*ELAN_SHA256:\s*([0-9a-f]{64})\s*$", re.MULTILINE)
VER = re.compile(r"^\s*ELAN_VER:\s*(v[0-9][0-9A-Za-z.\-]*)\s*$", re.MULTILINE)
# The approved install, as adjacent lines: fetch the pinned release, refuse it unless it hashes
# to the pin, and only then unpack and run the installer it contains. The download must name
# ${ELAN_VER} and the check ${ELAN_SHA256}, or the declared pin would describe a release the
# workflow does not actually fetch, or a checksum it does not actually compare against.
INSTALL = re.compile(
    r'^[ \t]*curl --fail --retry 3 --retry-all-errors --connect-timeout 15 --max-time 60 -sSL -H "Accept: application/octet-stream" \\\n'
    r'[ \t]*"https://github\.com/leanprover/elan/releases/download/\$\{ELAN_VER\}/'
    r'elan-x86_64-unknown-linux-gnu\.tar\.gz\?download=1" -o elan\.tar\.gz\n'
    r'[ \t]*echo "\$\{ELAN_SHA256\}  elan\.tar\.gz" \| sha256sum -c -\n'
    r'[ \t]*tar -xzf elan\.tar\.gz elan-init\n'
    r'[ \t]*\./elan-init -y --default-toolchain none\n'
    r'[ \t]*rm -f elan\.tar\.gz elan-init\n',
    re.MULTILINE,
)
# The names the approved block introduces. Once its matches are removed, no mention of either
# may remain: a second step touching them is installing elan some way this test has not vetted.
NAMES = re.compile(r"elan-init|elan\.tar\.gz")
# Every way of getting an elan that this repository does not choose by checksum. lean-action
# resolves from a floating tag and pipes the second of these to `sh`; naming it in prose is
# fine, so only a `uses:` of it counts.
UNPINNED = (
    ("the installer served at elan.lean-lang.org", re.compile(r"elan\.lean-lang\.org")),
    ("elan's master branch on raw.githubusercontent.com",
     re.compile(r"raw\.githubusercontent\.com/leanprover/elan")),
    ("leanprover/lean-action, which installs elan itself",
     re.compile(r"uses:\s*leanprover/lean-action")),
)


def workflows():
    return sorted(set(WORKFLOW_DIR.glob("*.yml")) | set(WORKFLOW_DIR.glob("*.yaml")))


def code(workflow):
    """The workflow with whole-line comments dropped, so only lines that run are matched."""
    return "".join(line for line in workflow.read_text().splitlines(keepends=True)
                   if not line.lstrip().startswith("#"))


def describe(values):
    return "; ".join(f"{value} in {', '.join(sorted(names))}"
                     for value, names in sorted(values.items()))


class ElanPin(unittest.TestCase):
    def test_workflows_exist(self):
        # A glob that silently matched nothing would make every test below vacuous.
        self.assertTrue(workflows(), f"no workflows found under {WORKFLOW_DIR}")

    def test_every_installing_workflow_pins_the_same_elan(self):
        vers, shas = {}, {}
        for workflow in workflows():
            text = code(workflow)
            for ver in VER.findall(text):
                vers.setdefault(ver, set()).add(workflow.name)
            for sha in SHA.findall(text):
                shas.setdefault(sha, set()).add(workflow.name)
        self.assertTrue(vers, "no workflow pins an elan release")
        self.assertEqual(len(vers), 1, "workflows disagree on the elan version: " + describe(vers))
        self.assertEqual(len(shas), 1, "workflows disagree on the elan checksum: " + describe(shas))

    def test_every_pin_belongs_to_a_verified_install(self):
        # A pin that is declared but never checked is not a pin, and one checksum cannot cover
        # two downloads in the same file, so the three counts must agree step for step.
        for workflow in workflows():
            text = code(workflow)
            pins = len(VER.findall(text))
            if not pins:
                continue
            with self.subTest(workflow=workflow.name):
                self.assertEqual(len(SHA.findall(text)), pins,
                                 f"{workflow.name} declares {pins} elan pin(s) but does not "
                                 "give each of them a checksum")
                self.assertEqual(len(INSTALL.findall(text)), pins,
                                 f"{workflow.name} declares {pins} elan pin(s) but does not "
                                 "download, verify and run each of them as one block")

    def test_nothing_else_touches_the_installer(self):
        for workflow in workflows():
            leftover = NAMES.search(INSTALL.sub("", code(workflow)))
            with self.subTest(workflow=workflow.name):
                self.assertIsNone(
                    leftover,
                    f"{workflow.name} names {leftover.group(0) if leftover else ''} outside the "
                    "verified install block; elan may only come from the pinned, checksummed "
                    "release")

    def test_no_workflow_installs_an_unverified_elan(self):
        for workflow in workflows():
            text = code(workflow)
            for description, pattern in UNPINNED:
                with self.subTest(workflow=workflow.name, source=description):
                    self.assertIsNone(
                        pattern.search(text),
                        f"{workflow.name} takes elan from {description}; install it from a "
                        "pinned leanprover/elan release verified by SHA-256 instead")


class ElanDownload(unittest.TestCase):
    """Exercise the production block against HTTP errors and mismatched bytes."""

    def run_download(self, statuses, good_checksum=True):
        buffer = io.BytesIO()
        script = b"#!/bin/sh\nprintf installed > installed\n"
        with tarfile.open(fileobj=buffer, mode="w:gz") as archive:
            member = tarfile.TarInfo("elan-init")
            member.size = len(script)
            member.mode = 0o755
            archive.addfile(member, io.BytesIO(script))
        payload = buffer.getvalue()
        requests = []

        class Handler(http.server.BaseHTTPRequestHandler):
            def do_GET(self):
                status = statuses[min(len(requests), len(statuses)-1)]
                requests.append(self.path)
                body = payload if status == 200 else b"Gateway timeout"
                self.send_response(status)
                self.send_header("Content-Length", str(len(body)))
                self.end_headers()
                self.wfile.write(body)

            def log_message(self, *args):
                pass

        with http.server.ThreadingHTTPServer(("127.0.0.1", 0), Handler) as server:
            thread = threading.Thread(target=server.serve_forever, daemon=True)
            thread.start()
            try:
                block = INSTALL.search(code(WORKFLOW_DIR / "pr-build.yml")).group()
                block = re.sub(r'https://github.com/leanprover/elan/releases/download/[^" ]+',
                               "http://127.0.0.1:" + str(server.server_port) + "/elan?download=1", block)
                # GitHub run blocks remove the common YAML indentation.
                block = "\n".join(line.lstrip() for line in block.splitlines())
                with tempfile.TemporaryDirectory() as directory:
                    result = subprocess.run(["bash", "-euc", block], cwd=directory, capture_output=True, text=True,
                        env={**os.environ, "ELAN_VER": "v4.2.3", "ELAN_SHA256": hashlib.sha256(payload).hexdigest()
                             if good_checksum else "0" * 64}, timeout=30)
                    installed = (pathlib.Path(directory) / "installed").exists()
            finally:
                server.shutdown()
                thread.join(timeout=5)
        return result, installed, requests

    def test_transient_gateway_error_retries_then_installs_verified_bytes(self):
        result, installed, requests = self.run_download([504, 200])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertTrue(installed)
        self.assertEqual(len(requests), 2)

    def test_http_error_never_runs_the_installer(self):
        result, installed, requests = self.run_download([504])
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(installed)
        self.assertEqual(len(requests), 4)
        self.assertNotIn("FAILED", result.stdout)  # Fails at HTTP, before checksum.

    def test_successful_download_with_wrong_checksum_never_runs_installer(self):
        result, installed, requests = self.run_download([200], good_checksum=False)
        self.assertNotEqual(result.returncode, 0)
        self.assertFalse(installed)
        self.assertEqual(len(requests), 1)
        self.assertIn("FAILED", result.stdout)


if __name__ == "__main__":
    unittest.main()
