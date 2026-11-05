#!/usr/bin/env python3
"""Optional prefill must never replace attestation or native cache validation."""
import hashlib
import io
import json
import os
from pathlib import Path
import shutil
import subprocess
import tarfile
import tempfile
import unittest

import yaml
from dependency_prefill import CONFIG, digest, hydrate

ROOT = Path(__file__).resolve().parents[1]


@unittest.skipUnless(shutil.which("zstd"), "zstd required for archive fixture")
class Hydration(unittest.TestCase):
    def setUp(self):
        temp = tempfile.TemporaryDirectory()
        self.addCleanup(temp.cleanup)
        self.root = Path(temp.name)
        self.project = self.root / "project"
        self.project.mkdir()
        (self.project / ".lake").mkdir()
        self.source = self.root / "source"
        self.source.mkdir()
        package = self.root / "producer/.lake/packages/mathlib"
        package.mkdir(parents=True)
        subprocess.run(["git", "init", "-q", str(package)], check=True)
        subprocess.run(["git", "-C", str(package), "remote", "add", "origin", "https://github.com/leanprover-community/mathlib4"], check=True)
        (package / "source").write_text("trusted fixture")
        subprocess.run(["git", "-C", str(package), "add", "."], check=True)
        subprocess.run(["git", "-C", str(package), "-c", "user.name=Fixture", "-c", "user.email=fixture@example.org", "commit", "-qm", "fixture"], check=True)
        self.rev = subprocess.check_output(["git", "-C", str(package), "rev-parse", "HEAD"], text=True).strip()
        (self.project / "lakefile.toml").write_text('name = "Fixture"\n')
        (self.project / "lean-toolchain").write_text("leanprover/lean4:v4.36.0-rc2\n")
        (self.project / "lake-manifest.json").write_text(json.dumps({"packages": [dict(name="mathlib", rev=self.rev, url="https://github.com/leanprover-community/mathlib4")]}))
        subprocess.run(["tar", "--zstd", "-cf", str(self.source / "packages.tar.zst"), "-C", str(self.root / "producer"), ".lake/packages"], check=True)
        self.metadata = dict(schema=1, platform="Linux-x86_64", uid=os.getuid(), project_path=str(self.project), config_sha256={n:digest(self.project/n) for n in CONFIG})
        self.seal()

    def seal(self):
        p = self.source / "packages.tar.zst"
        self.metadata.update(payload_bytes=p.stat().st_size, payload_sha256=digest(p))
        (self.source / "manifest.json").write_text(json.dumps(self.metadata))

    def assert_clean(self):
        self.assertFalse((self.project / ".lake/packages").exists())
        self.assertEqual(list((self.project / ".lake").iterdir()), [])

    def test_complete_payload_publishes_once_and_preserves_existing_packages(self):
        self.assertTrue(hydrate(self.project, self.source)["hit"])
        self.assertEqual((self.project / ".lake/packages/mathlib/source").read_text(), "trusted fixture")
        self.assertFalse(hydrate(self.project, self.source)["hit"])
        self.assertEqual((self.project / ".lake/packages/mathlib/source").read_text(), "trusted fixture")

    def test_missing_corrupt_and_mismatched_payloads_remain_cold(self):
        for change in ("uid", "config", "path", "digest", "missing"):
            with self.subTest(change=change):
                metadata = dict(self.metadata)
                if change == "uid": metadata["uid"] = os.getuid()+1
                if change == "config": metadata["config_sha256"] = {}
                if change == "path": metadata["project_path"] = "/wrong"
                if change == "digest": metadata["payload_sha256"] = "0"*64
                (self.source / "manifest.json").write_text(json.dumps(metadata))
                if change == "missing": (self.source / "manifest.json").unlink()
                self.assertFalse(hydrate(self.project, self.source)["hit"])
                self.assert_clean()

    def test_escaping_tar_member_cleans_partial_tree(self):
        payload = self.source / "packages.tar.zst"
        raw = io.BytesIO()
        with tarfile.open(fileobj=raw, mode="w") as archive:
            member=tarfile.TarInfo("../../escape")
            member.size=1
            archive.addfile(member, io.BytesIO(b"x"))
        payload.write_bytes(subprocess.check_output(["zstd", "-c"], input=raw.getvalue()))
        self.seal()
        self.assertFalse(hydrate(self.project, self.source)["hit"])
        self.assert_clean()
        self.assertFalse((self.root / "escape").exists())

    def test_wrong_git_revision_remains_cold(self):
        p=self.project / "lake-manifest.json"
        d=json.loads(p.read_text());d["packages"][0]["rev"]="0"*40;p.write_text(json.dumps(d))
        self.metadata["config_sha256"]={n:digest(self.project/n) for n in CONFIG};self.seal()
        self.assertFalse(hydrate(self.project, self.source)["hit"])
        self.assert_clean()


class Workflow(unittest.TestCase):
    def test_hydration_is_after_normalization_attestation_and_sandbox_setup(self):
        steps=yaml.safe_load((ROOT/".github/workflows/pr-build.yml").read_text())["jobs"]["sandboxed-build"]["steps"]
        index=next(i for i,s in enumerate(steps) if s.get("name")=="Hydrate optional trusted local dependency prefill")
        for name in ["Attest integrated Lake configuration before executing Lake", "Install bubblewrap (pinned + checksum) and self-test (fail closed)"]:
            self.assertLess(next(i for i,s in enumerate(steps) if s.get("name")==name), index)
        self.assertLess(index,next(i for i,s in enumerate(steps) if s.get("name")=="Restore Mathlib's compressed download cache from main"))
        fetch=next(s for s in steps if s.get("name", "").startswith("Fetch Mathlib with"))
        self.assertIn("lake exe cache get", fetch["run"])
        self.assertNotIn("prefill",fetch.get("if",""))
        self.assertIn("env.INFRA != '1'",steps[index]["if"])
        self.assertTrue(steps[index]["continue-on-error"])


if __name__=="__main__":unittest.main()
